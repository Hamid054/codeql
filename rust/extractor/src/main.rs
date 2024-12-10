use crate::diagnostics::{emit_extraction_diagnostics, ExtractionStep};
use crate::rust_analyzer::path_to_file_id;
use crate::trap::TrapId;
use anyhow::Context;
use archive::Archiver;
use itertools::Itertools;
use log::{info, warn};
use ra_ap_base_db::{CrateId, SourceDatabase};
use ra_ap_cfg::CfgAtom;
use ra_ap_hir::db::{DefDatabase, HirDatabase};
use ra_ap_hir::{DefMap, ModPath, ModuleDefId, Semantics, TypeRef, Variant};
use ra_ap_hir_def::data::adt::VariantData;
use ra_ap_hir_def::LocalModuleId;
use ra_ap_ide_db::line_index::{LineCol, LineIndex};
use ra_ap_ide_db::RootDatabase;
use ra_ap_project_model::{CargoConfig, ProjectManifest};
use ra_ap_vfs::{Vfs, VfsPath};
use rust_analyzer::{ParseResult, RustAnalyzer};
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::time::Instant;
use std::{
    collections::HashMap,
    path::{Path, PathBuf},
};
use trap::TrapFile;

mod archive;
mod config;
mod diagnostics;
pub mod generated;
mod qltest;
mod rust_analyzer;
mod translate;
pub mod trap;

struct Extractor<'a> {
    archiver: &'a Archiver,
    traps: &'a trap::TrapFileProvider,
    steps: Vec<ExtractionStep>,
}

fn emit_hir_path(path: &ra_ap_hir_def::path::Path) -> Vec<String> {
    path.segments()
        .iter()
        .map(|x| x.name.as_str().to_owned())
        .collect()
}
fn emit_hir_fn(
    trap: &mut TrapFile,
    self_type: Option<&TypeRef>,
    params: &[&TypeRef],
    ret_type: &TypeRef,
    is_async: bool,
    is_const: bool,
    is_unsafe: bool,
) -> trap::Label<generated::FunctionType> {
    let ret_type = emit_hir_typeref(trap, ret_type);

    let self_type = self_type.map(|ty| emit_hir_typeref(trap, ty));
    let params = params.iter().map(|t| emit_hir_typeref(trap, t)).collect();

    trap.emit(generated::FunctionType {
        id: trap::TrapId::Star,
        is_async,
        is_const,
        is_unsafe,
        self_type,
        ret_type,
        params,
        has_varargs: false,
    })
}
fn emit_hir_typeref(trap: &mut TrapFile, ty: &TypeRef) -> trap::Label<generated::Type> {
    match ty {
        TypeRef::Never => trap
            .emit(generated::NeverType {
                id: trap::TrapId::Star,
            })
            .into(),

        TypeRef::Placeholder => trap
            .emit(generated::PlaceholderType {
                id: trap::TrapId::Star,
            })
            .into(),

        TypeRef::Tuple(fields) => {
            let fields = fields
                .iter()
                .map(|field| emit_hir_typeref(trap, field))
                .collect();

            trap.emit(generated::TupleType {
                id: trap::TrapId::Star,
                fields,
            })
            .into()
        }
        TypeRef::RawPtr(type_ref, mutability) => {
            let type_ = emit_hir_typeref(trap, type_ref);

            trap.emit(generated::RawPtrType {
                id: trap::TrapId::Star,
                is_mut: mutability.is_mut(),
                type_,
            })
            .into()
        }
        TypeRef::Reference(type_ref, lifetime_ref, mutability) => {
            let type_ = emit_hir_typeref(trap, type_ref);
            let lifetime = lifetime_ref.as_ref().map(|x|x.name.as_str().to_owned());
            trap.emit(generated::ReferenceType {
                id: trap::TrapId::Star,
                is_mut: mutability.is_mut(),
                type_,
                lifetime,
            })
            .into()
        }
        TypeRef::Array(type_ref, _const_ref) => {
            let type_ = emit_hir_typeref(trap, type_ref);
            // TODO: handle array size constant
            trap.emit(generated::ArrayType {
                id: trap::TrapId::Star,
                type_,
            })
            .into()
        }
        TypeRef::Slice(type_ref) => {
            let type_ = emit_hir_typeref(trap, type_ref);
            trap.emit(generated::SliceType {
                id: trap::TrapId::Star,
                type_,
            })
            .into()
        }
        TypeRef::Fn(params, _, is_unsafe, _symbol) => {
            let (ret_type, params) = params.split_last().unwrap();
            let params: Vec<_> = params.as_ref().iter().map(|x| &x.1).collect();
            emit_hir_fn(
                trap,
                None,
                &params[..],
                &ret_type.1,
                false,
                false,
                *is_unsafe,
            )
            .into()
        }
        TypeRef::Path(path) => {
            let path = emit_hir_path(path);
            trap.emit(generated::PathType {
                id: trap::TrapId::Star,
                path,
            })
            .into()
        }
        TypeRef::ImplTrait(_) | // TODO handle impl
        TypeRef::DynTrait(_) |  // TODO handle dyn
        TypeRef::Macro(_) |
        TypeRef::Error =>  trap.emit(generated::ErrorType { id: trap::TrapId::Star,   })  .into(),
    }
}

fn emit_variant_data(
    trap: &mut TrapFile,
    variant: &VariantData,
) -> Option<trap::Label<generated::VariantData>> {
    match variant {
        VariantData::Record(field_data) | VariantData::Tuple(field_data) => {
            let mut types = Vec::new();
            let mut fields = Vec::new();
            for field in field_data.values() {
                let tp = emit_hir_typeref(trap, &field.type_ref);
                fields.push(field.name.as_str().to_owned());
                types.push(tp);
            }
            Some(trap.emit(generated::VariantData {
                id: trap::TrapId::Star,
                types,
                fields,
                is_record: matches!(variant, VariantData::Record(_)),
            }))
        }
        VariantData::Unit => None,
    }
}
impl<'a> Extractor<'a> {
    pub fn new(archiver: &'a Archiver, traps: &'a trap::TrapFileProvider) -> Self {
        Self {
            archiver,
            traps,
            steps: Vec::new(),
        }
    }

    fn extract(&mut self, rust_analyzer: &rust_analyzer::RustAnalyzer, file: &std::path::Path) {
        self.archiver.archive(file);

        let before_parse = Instant::now();
        let ParseResult {
            ast,
            text,
            errors,
            semantics_info,
        } = rust_analyzer.parse(file);
        self.steps.push(ExtractionStep::parse(before_parse, file));

        let before_extract = Instant::now();
        let line_index = LineIndex::new(text.as_ref());
        let display_path = file.to_string_lossy();
        let mut trap = self.traps.create("source", file);
        let label = trap.emit_file(file);
        let mut translator = translate::Translator::new(
            trap,
            display_path.as_ref(),
            label,
            line_index,
            semantics_info.as_ref().ok(),
        );

        for err in errors {
            translator.emit_parse_error(&ast, &err);
        }
        let no_location = (LineCol { line: 0, col: 0 }, LineCol { line: 0, col: 0 });
        if let Err(reason) = semantics_info {
            let message = format!("semantic analyzer unavailable ({reason})");
            let full_message = format!(
                "{message}: macro expansion, call graph, and type inference will be skipped."
            );
            translator.emit_diagnostic(
                trap::DiagnosticSeverity::Warning,
                "semantics".to_owned(),
                message,
                full_message,
                no_location,
            );
        }
        translator.emit_source_file(ast);
        translator.trap.commit().unwrap_or_else(|err| {
            log::error!(
                "Failed to write trap file for: {}: {}",
                display_path,
                err.to_string()
            )
        });
        self.steps
            .push(ExtractionStep::extract(before_extract, file));
    }

    pub fn extract_with_semantics(
        &mut self,
        file: &Path,
        semantics: &Semantics<'_, RootDatabase>,
        vfs: &Vfs,
    ) {
        self.extract(&RustAnalyzer::new(vfs, semantics), file);
    }

    pub fn extract_without_semantics(&mut self, file: &Path, reason: &str) {
        self.extract(&RustAnalyzer::WithoutSemantics { reason }, file);
    }

    pub fn load_manifest(
        &mut self,
        project: &ProjectManifest,
        config: &CargoConfig,
    ) -> Option<(RootDatabase, Vfs)> {
        let before = Instant::now();
        let ret = RustAnalyzer::load_workspace(project, config);
        self.steps
            .push(ExtractionStep::load_manifest(before, project));
        ret
    }

    pub fn load_source(
        &mut self,
        file: &Path,
        semantics: &Semantics<'_, RootDatabase>,
        vfs: &Vfs,
    ) -> Result<(), String> {
        let before = Instant::now();
        let Some(id) = path_to_file_id(file, vfs) else {
            return Err("not included in files loaded from manifest".to_string());
        };
        if semantics.file_to_module_def(id).is_none() {
            return Err("not included as a module".to_string());
        }
        self.steps.push(ExtractionStep::load_source(before, file));
        Ok(())
    }

    pub fn emit_extraction_diagnostics(
        self,
        start: Instant,
        cfg: &config::Config,
    ) -> anyhow::Result<()> {
        emit_extraction_diagnostics(start, cfg, &self.steps)?;
        let mut trap = self.traps.create("diagnostics", "extraction");
        for step in self.steps {
            let file = trap.emit_file(&step.file);
            let duration_ms = usize::try_from(step.ms).unwrap_or_else(|_e| {
                warn!("extraction step duration overflowed ({step:?})");
                i32::MAX as usize
            });
            trap.emit(generated::ExtractorStep {
                id: TrapId::Star,
                action: format!("{:?}", step.action),
                file,
                duration_ms,
            });
        }
        trap.commit()?;
        Ok(())
    }

    fn extract_crate_graph(&self, db: &RootDatabase, vfs: &Vfs) {
        let crate_graph = db.crate_graph();

        // According to the documentation of `CrateGraph`:
        // Each crate is defined by the `FileId` of its root module, the set of enabled
        // `cfg` flags and the set of dependencies.
        let mut crate_id_map = HashMap::<CrateId, (PathBuf, u64)>::new();
        for krate_id in crate_graph.crates_in_topological_order() {
            let krate = &crate_graph[krate_id];
            let root_module_file: &VfsPath = vfs.file_path(krate.root_file_id);
            if let Some(root_module_file) = root_module_file
                .as_path()
                .map(|p| std::fs::canonicalize(p).unwrap_or(p.into()))
            {
                let mut hasher = std::hash::DefaultHasher::new();
                krate
                    .cfg_options
                    .as_ref()
                    .into_iter()
                    .sorted_by(cmp_flag)
                    .for_each(|x| format!("{x}").hash(&mut hasher));

                krate
                    .dependencies
                    .iter()
                    .flat_map(|d| crate_id_map.get(&d.crate_id))
                    .sorted()
                    .for_each(|x| x.hash(&mut hasher));
                let hash = hasher.finish();
                crate_id_map.insert(krate_id, (root_module_file, hash));
            }
        }
        for krate_id in crate_graph.iter() {
            if let Some((root_module_file, hash)) = crate_id_map.get(&krate_id) {
                let path = root_module_file.join(format!("{hash:0>16x}"));
                let mut trap = self.traps.create("crates", path.as_path());
                if trap.path.exists() {
                    continue;
                }
                let krate = &crate_graph[krate_id];
                let element = generated::Crate {
                    id: trap::TrapId::Key(format!("crate:{}:{hash}", root_module_file.display())),
                    name: krate
                        .display_name
                        .as_ref()
                        .map(|x| x.canonical_name().to_string()),
                    version: krate.version.to_owned(),
                    cfg_options: krate
                        .cfg_options
                        .as_ref()
                        .into_iter()
                        .map(|x| format!("{x}"))
                        .collect(),
                    dependencies: krate
                        .dependencies
                        .iter()
                        .flat_map(|x| crate_id_map.get(&x.crate_id))
                        .map(|(module, hash)| {
                            trap.label(format!("crate:{}:{hash}", module.display()).into())
                        })
                        .collect(),
                };
                let parent = trap.emit(element);

                go(
                    db,
                    db.crate_def_map(krate_id).as_ref(),
                    parent.into(),
                    "crate",
                    DefMap::ROOT,
                    &mut trap,
                );
                trap.commit().unwrap_or_else(|err| {
                    log::error!(
                        "Failed to write trap file for crate: {}: {}",
                        root_module_file.display(),
                        err.to_string()
                    )
                });
            }
            fn go(
                db: &dyn HirDatabase,
                map: &DefMap,
                parent: trap::Label<generated::ModuleContainer>,
                name: &str,
                module: LocalModuleId,
                trap: &mut TrapFile,
            ) {
                let module = &map.modules[module];
                let items = &module.scope;
                let mut values = Vec::new();
                let mut types = Vec::new();

                for (name, item) in items.entries() {
                    let def = item.with_visibility(ra_ap_hir::Visibility::Public);
                    if let Some((value, _, _import)) = def.values {
                        match value {
                            ModuleDefId::FunctionId(function) => {
                                let function = db.function_data(function);
                                let params: Vec<_> =
                                    function.params.iter().map(|x| x.as_ref()).collect();
                                let (self_type, params) = if function.has_self_param() {
                                    (Some(params[0]), &params[1..])
                                } else {
                                    (None, &params[..])
                                };
                                let ret_type = function.ret_type.as_ref();
                                let type_ = emit_hir_fn(
                                    trap,
                                    self_type,
                                    params,
                                    ret_type,
                                    function.is_async(),
                                    function.is_const(),
                                    function.is_unsafe(),
                                )
                                .into();

                                values.push(trap.emit(generated::ValueItem {
                                    id: trap::TrapId::Star,
                                    name: name.as_str().to_owned(),
                                    type_,
                                }));
                            }
                            ModuleDefId::ConstId(konst) => {
                                let konst = db.const_data(konst);
                                let type_ = emit_hir_typeref(trap, &konst.type_ref);
                                values.push(trap.emit(generated::ValueItem {
                                    id: trap::TrapId::Star,
                                    name: name.as_str().to_owned(),
                                    type_,
                                }));
                            }
                            ModuleDefId::StaticId(statik) => {
                                let statik = db.static_data(statik);
                                let type_ = emit_hir_typeref(trap, &statik.type_ref);
                                values.push(trap.emit(generated::ValueItem {
                                    id: trap::TrapId::Star,
                                    name: name.as_str().to_owned(),
                                    type_,
                                }));
                            }
                            ModuleDefId::EnumVariantId(variant_id) => {
                                let variant: Variant = variant_id.into();
                                let tp = variant.parent_enum(db);
                                let mut mod_path = ModPath::from_kind(ra_ap_hir::PathKind::Abs);

                                mod_path.extend(
                                    tp.module(db)
                                        .path_to_root(db)
                                        .iter()
                                        .flat_map(|x| x.name(db)),
                                );
                                mod_path.push_segment(tp.name(db));
                                let ret_type = TypeRef::Path(
                                    ra_ap_hir_def::path::Path::from_known_path_with_no_generic(
                                        mod_path,
                                    ),
                                );
                                //
                                let variant_data = db.enum_variant_data(variant_id);
                                let type_ = match variant_data.variant_data.as_ref() {
                                    ra_ap_hir_def::data::adt::VariantData::Unit => {
                                        Some(emit_hir_typeref(trap, &ret_type))
                                    }
                                    ra_ap_hir_def::data::adt::VariantData::Tuple(arena) => {
                                        let params: Vec<_> =
                                            arena.values().map(|f| f.type_ref.as_ref()).collect();
                                        Some(
                                            emit_hir_fn(
                                                trap,
                                                None,
                                                &params[..],
                                                &ret_type,
                                                false,
                                                false,
                                                false,
                                            )
                                            .into(),
                                        )
                                    }
                                    ra_ap_hir_def::data::adt::VariantData::Record(_) => {
                                        // record enums are not "values"
                                        None
                                    }
                                };
                                if let Some(type_) = type_ {
                                    values.push(trap.emit(generated::ValueItem {
                                        id: trap::TrapId::Star,
                                        name: name.as_str().to_owned(),
                                        type_,
                                    }));
                                }
                            }
                            _ => (),
                        }
                    }
                    if let Some((type_id, _, _import)) = def.types {
                        if let ModuleDefId::AdtId(adt_id) = type_id {
                            match adt_id {
                                ra_ap_hir::AdtId::StructId(struct_id) => {
                                    let data = db.struct_data(struct_id);
                                    let content =
                                        emit_variant_data(trap, data.variant_data.as_ref());
                                    types.push(
                                        trap.emit(generated::StructItem {
                                            id: trap::TrapId::Star,
                                            name: name.as_str().to_owned(),
                                            content,
                                            is_union: false,
                                        })
                                        .into(),
                                    );
                                }
                                ra_ap_hir::AdtId::EnumId(enum_id) => {
                                    let data = db.enum_data(enum_id);
                                    let variants = data
                                        .variants
                                        .iter()
                                        .map(|(enum_id, name)| {
                                            let data = db.enum_variant_data(*enum_id);
                                            let content =
                                                emit_variant_data(trap, data.variant_data.as_ref());
                                            trap.emit(generated::EnumVariant {
                                                id: trap::TrapId::Star,
                                                name: name.as_str().to_owned(),
                                                content,
                                            })
                                        })
                                        .collect();
                                    types.push(
                                        trap.emit(generated::EnumItem {
                                            id: trap::TrapId::Star,
                                            name: name.as_str().to_owned(),
                                            variants,
                                        })
                                        .into(),
                                    );
                                }
                                ra_ap_hir::AdtId::UnionId(union_id) => {
                                    let data = db.union_data(union_id);
                                    let content =
                                        emit_variant_data(trap, data.variant_data.as_ref());
                                    types.push(
                                        trap.emit(generated::StructItem {
                                            id: trap::TrapId::Star,
                                            name: name.as_str().to_owned(),
                                            content,
                                            is_union: true,
                                        })
                                        .into(),
                                    );
                                }
                            }
                        }
                    }
                }
                let label = trap.emit(generated::CrateModule {
                    id: trap::TrapId::Star,
                    name: name.to_owned(),
                    parent,
                    values,
                    types,
                });
                for (name, child) in module
                    .children
                    .iter()
                    .sorted_by(|a, b| Ord::cmp(&a.0, &b.0))
                {
                    go(db, map, label.into(), name.as_str(), *child, trap);
                }
            }
        }
    }
}

fn cmp_flag(a: &&CfgAtom, b: &&CfgAtom) -> Ordering {
    match (a, b) {
        (CfgAtom::Flag(a), CfgAtom::Flag(b)) => a.as_str().cmp(b.as_str()),
        (CfgAtom::Flag(a), CfgAtom::KeyValue { key: b, value: _ }) => {
            a.as_str().cmp(b.as_str()).then(Ordering::Less)
        }
        (CfgAtom::KeyValue { key: a, value: _ }, CfgAtom::Flag(b)) => {
            a.as_str().cmp(b.as_str()).then(Ordering::Greater)
        }
        (CfgAtom::KeyValue { key: a, value: av }, CfgAtom::KeyValue { key: b, value: bv }) => a
            .as_str()
            .cmp(b.as_str())
            .then(av.as_str().cmp(bv.as_str())),
    }
}

fn main() -> anyhow::Result<()> {
    let start = Instant::now();
    let mut cfg = config::Config::extract().context("failed to load configuration")?;
    stderrlog::new()
        .module(module_path!())
        .verbosity(2 + cfg.verbose as usize)
        .init()?;
    if cfg.qltest {
        qltest::prepare(&mut cfg)?;
    }
    info!("{cfg:#?}\n");

    let traps = trap::TrapFileProvider::new(&cfg).context("failed to set up trap files")?;
    let archiver = archive::Archiver {
        root: cfg.source_archive_dir.clone(),
    };
    let mut extractor = Extractor::new(&archiver, &traps);
    let files: Vec<PathBuf> = cfg
        .inputs
        .iter()
        .map(|file| {
            let file = std::path::absolute(file).unwrap_or(file.to_path_buf());
            std::fs::canonicalize(&file).unwrap_or(file)
        })
        .collect();
    let manifests = rust_analyzer::find_project_manifests(&files)?;
    let mut map: HashMap<&Path, (&ProjectManifest, Vec<&Path>)> = manifests
        .iter()
        .map(|x| (x.manifest_path().parent().as_ref(), (x, Vec::new())))
        .collect();

    'outer: for file in &files {
        for ancestor in file.as_path().ancestors() {
            if let Some((_, files)) = map.get_mut(ancestor) {
                files.push(file);
                continue 'outer;
            }
        }
        extractor.extract_without_semantics(file, "no manifest found");
    }
    let cargo_config = cfg.to_cargo_config();
    for (manifest, files) in map.values().filter(|(_, files)| !files.is_empty()) {
        if let Some((ref db, ref vfs)) = extractor.load_manifest(manifest, &cargo_config) {
            extractor.extract_crate_graph(db, vfs);
            let semantics = Semantics::new(db);
            for file in files {
                match extractor.load_source(file, &semantics, vfs) {
                    Ok(()) => extractor.extract_with_semantics(file, &semantics, vfs),
                    Err(reason) => extractor.extract_without_semantics(file, &reason),
                };
            }
        } else {
            for file in files {
                extractor.extract_without_semantics(file, "unable to load manifest");
            }
        }
    }

    extractor.emit_extraction_diagnostics(start, &cfg)
}

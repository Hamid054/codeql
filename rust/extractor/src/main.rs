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

fn emit_hir_path(
    trap: &mut TrapFile,
    path: &ra_ap_hir_def::path::Path,
) -> trap::Label<generated::Path> {
    let part = path.segments().last().map(|segment| {
        let name_ref = trap.emit(generated::NameRef {
            id: trap::TrapId::Star,
            text: Some(segment.name.as_str().to_owned()),
        });
        trap.emit(generated::PathSegment {
            id: trap::TrapId::Star,
            generic_arg_list: None,
            name_ref: Some(name_ref),
            param_list: None,
            path_type: None,
            ret_type: None,
            return_type_syntax: None,
            type_repr: None,
        })
    });
    let qualifier = path
        .mod_path()
        .filter(|p| !p.segments().is_empty())
        .and_then(|_| path.qualifier().as_ref().map(|p| emit_hir_path(trap, p)));
    trap.emit(generated::Path {
        id: trap::TrapId::Star,
        qualifier,
        part,
    })
}
fn emit_hir_fn(
    trap: &mut TrapFile,
    self_type: Option<&TypeRef>,
    params: &[&TypeRef],
    ret_type: &TypeRef,
    is_async: bool,
    is_const: bool,
    is_unsafe: bool,
) -> trap::Label<generated::FnPtrTypeRepr> {
    let ret = emit_hir_typeref(trap, ret_type);

    let ret = trap.emit(generated::RetTypeRepr {
        id: trap::TrapId::Star,
        type_repr: ret,
    });
    let self_param = self_type.map(|ty| {
        let type_repr = emit_hir_typeref(trap, ty);
        trap.emit(generated::SelfParam {
            id: trap::TrapId::Star,
            attrs: vec![],
            type_repr,
            is_mut: false,
            lifetime: None,
            name: None,
        })
    });
    let params = params
        .iter()
        .map(|t| {
            let type_repr = emit_hir_typeref(trap, t);
            trap.emit(generated::Param {
                id: trap::TrapId::Star,
                attrs: vec![],
                type_repr,
                pat: None,
            })
        })
        .collect();
    let params = trap.emit(generated::ParamList {
        id: trap::TrapId::Star,
        params,
        self_param,
    });
    trap.emit(generated::FnPtrTypeRepr {
        id: trap::TrapId::Star,
        abi: None,
        is_async,
        is_const,
        is_unsafe,
        param_list: Some(params),
        ret_type: Some(ret),
    })
}
fn emit_hir_typeref(trap: &mut TrapFile, ty: &TypeRef) -> Option<trap::Label<generated::TypeRepr>> {
    match ty {
        TypeRef::Never => Some(
            trap.emit(generated::NeverTypeRepr {
                id: trap::TrapId::Star,
            })
            .into(),
        ),
        TypeRef::Placeholder => Some(
            trap.emit(generated::InferTypeRepr {
                id: trap::TrapId::Star,
            })
            .into(),
        ),
        TypeRef::Tuple(fields) => {
            let fields = fields
                .iter()
                .flat_map(|field| emit_hir_typeref(trap, field))
                .collect();
            Some(
                trap.emit(generated::TupleTypeRepr {
                    id: trap::TrapId::Star,
                    fields,
                })
                .into(),
            )
        }
        TypeRef::RawPtr(type_ref, mutability) => {
            let type_repr = emit_hir_typeref(trap, type_ref);
            Some(
                trap.emit(generated::PtrTypeRepr {
                    id: trap::TrapId::Star,
                    is_const: mutability.is_shared(),
                    is_mut: mutability.is_mut(),
                    type_repr,
                })
                .into(),
            )
        }
        TypeRef::Reference(type_ref, lifetime_ref, mutability) => {
            let type_repr = emit_hir_typeref(trap, type_ref);
            let lifetime = lifetime_ref.as_ref().map(|x| {
                trap.emit(generated::Lifetime {
                    id: trap::TrapId::Star,
                    text: Some(x.name.as_str().to_owned()),
                })
            });
            Some(
                trap.emit(generated::RefTypeRepr {
                    id: trap::TrapId::Star,
                    is_mut: mutability.is_mut(),
                    type_repr,
                    lifetime,
                })
                .into(),
            )
        }
        TypeRef::Array(type_ref, _const_ref) => {
            let element_type_repr = emit_hir_typeref(trap, type_ref);
            // TODO: handle array size constant
            let const_arg = None;
            Some(
                trap.emit(generated::ArrayTypeRepr {
                    id: trap::TrapId::Star,
                    element_type_repr,
                    const_arg,
                })
                .into(),
            )
        }
        TypeRef::Slice(type_ref) => {
            let type_repr = emit_hir_typeref(trap, type_ref);
            Some(
                trap.emit(generated::SliceTypeRepr {
                    id: trap::TrapId::Star,
                    type_repr,
                })
                .into(),
            )
        }
        TypeRef::Fn(params, _, is_unsafe, _symbol) => {
            let (ret_type, params) = params.split_last().unwrap();
            let params: Vec<_> = params.as_ref().iter().map(|x| &x.1).collect();
            Some(
                emit_hir_fn(
                    trap,
                    None,
                    &params[..],
                    &ret_type.1,
                    false,
                    false,
                    *is_unsafe,
                )
                .into(),
            )
        }
        TypeRef::Path(path) => {
            let path = Some(emit_hir_path(trap, path));

            Some(
                trap.emit(generated::PathTypeRepr {
                    id: trap::TrapId::Star,
                    path,
                })
                .into(),
            )
        }
        TypeRef::ImplTrait(_) => None, // TODO handle impl
        TypeRef::DynTrait(_) => None,  // TODO handle dyn
        TypeRef::Macro(_) => None,
        TypeRef::Error => None,
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
        let mut crate_id_map = HashMap::<CrateId, (&VfsPath, u64)>::new();
        for krate_id in crate_graph.crates_in_topological_order() {
            let krate = &crate_graph[krate_id];
            let root_module_file = vfs.file_path(krate.root_file_id);
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
        for krate_id in crate_graph.iter() {
            let (root_module_file, hash) = crate_id_map.get(&krate_id).unwrap();
            let path: &Path = root_module_file.as_path().unwrap().as_ref();
            let path = path.join(format!("{hash:0>16x}"));
            let mut trap = self.traps.create("crates", path.as_path());
            if trap.path.exists() {
                continue;
            }
            let krate = &crate_graph[krate_id];
            let element = generated::Crate {
                id: trap::TrapId::Key(format!("crate:{root_module_file}:{hash}")),
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
                    .map(|(module, hash)| trap.label(format!("crate:{module}:{hash}").into()))
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
            trap.commit();

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
                                if let Some(type_) = emit_hir_typeref(trap, &konst.type_ref) {
                                    values.push(trap.emit(generated::ValueItem {
                                        id: trap::TrapId::Star,
                                        name: name.as_str().to_owned(),
                                        type_,
                                    }));
                                }
                            }
                            ModuleDefId::StaticId(statik) => {
                                let statik = db.static_data(statik);
                                if let Some(type_) = emit_hir_typeref(trap, &statik.type_ref) {
                                    values.push(trap.emit(generated::ValueItem {
                                        id: trap::TrapId::Star,
                                        name: name.as_str().to_owned(),
                                        type_,
                                    }));
                                }
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
                                        emit_hir_typeref(trap, &ret_type)
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
                    if let Some((_type_id, _, _import)) = def.types {}
                }
                let label = trap.emit(generated::CrateModule {
                    id: trap::TrapId::Star,
                    name: name.to_owned(),
                    parent,
                    values,
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

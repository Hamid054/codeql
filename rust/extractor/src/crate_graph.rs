use ra_ap_base_db::SourceDatabase;
use ra_ap_hir::db::DefDatabase;
use std::hash::Hash;
use std::hash::Hasher;
use std::{cmp::Ordering, collections::HashMap, path::PathBuf};

use itertools::Itertools;
use ra_ap_base_db::CrateId;
use ra_ap_cfg::CfgAtom;
use ra_ap_hir::{db::HirDatabase, DefMap, ModPath, ModuleDefId, TypeRef, Variant};
use ra_ap_hir_def::{
    data::{adt::VariantData, FunctionData},
    AssocItemId, LocalModuleId,
};
use ra_ap_ide_db::RootDatabase;
use ra_ap_vfs::{Vfs, VfsPath};

use crate::{
    generated,
    trap::{self, TrapFile},
};

pub fn extract_crate_graph(trap_provider: &trap::TrapFileProvider, db: &RootDatabase, vfs: &Vfs) {
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
            let mut trap = trap_provider.create("crates", path.as_path());
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
                            let type_ = emit_hir_fn_data(trap, &function).into();
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
                                let content = emit_variant_data(trap, data.variant_data.as_ref());
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
                                let content = emit_variant_data(trap, data.variant_data.as_ref());
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
                    if let ModuleDefId::TraitId(trait_id) = type_id {
                        let data = db.trait_data(trait_id);
                        let mut method_names = Vec::new();
                        let mut method_types = Vec::new();
                        for (name, item) in &data.items {
                            if let AssocItemId::FunctionId(function) = item {
                                method_names.push(name.as_str().to_owned());
                                let function = db.function_data(*function);
                                let method_type = emit_hir_fn_data(trap, &function);
                                method_types.push(method_type);
                            };
                        }

                        types.push(
                            trap.emit(generated::TraitItem {
                                id: trap::TrapId::Star,
                                name: name.as_str().to_owned(),
                                method_names,
                                method_types,
                            })
                            .into(),
                        );
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

fn emit_hir_type_bound(
    trap: &mut TrapFile,
    type_bound: &ra_ap_hir_def::type_ref::TypeBound,
) -> Option<trap::Label<generated::TypeBoundType>> {
    match type_bound {
        ra_ap_hir_def::type_ref::TypeBound::Path(path, _) => Some(
            trap.emit(generated::TraitTypeBound {
                id: trap::TrapId::Star,
                path: emit_hir_path(path),
            })
            .into(),
        ),
        ra_ap_hir_def::type_ref::TypeBound::ForLifetime(names, path) => Some(
            trap.emit(generated::ForLifetimeTypeBound {
                id: trap::TrapId::Star,
                path: emit_hir_path(path),
                names: names.into_iter().map(|x| x.as_str().to_owned()).collect(),
            })
            .into(),
        ),
        ra_ap_hir_def::type_ref::TypeBound::Lifetime(lifetime_ref) => Some(
            trap.emit(generated::LifetimeTypeBound {
                id: trap::TrapId::Star,
                name: lifetime_ref.name.as_str().to_owned(),
            })
            .into(),
        ),
        ra_ap_hir_def::type_ref::TypeBound::Error => None,
    }
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
fn emit_hir_fn_data(
    trap: &mut TrapFile,
    function: &FunctionData,
) -> trap::Label<generated::FunctionType> {
    let params: Vec<_> = function.params.iter().map(|x| x.as_ref()).collect();
    let (self_type, params) = if function.has_self_param() {
        (Some(params[0]), &params[1..])
    } else {
        (None, &params[..])
    };
    let ret_type = function.ret_type.as_ref();
    emit_hir_fn(
        trap,
        self_type,
        params,
        ret_type,
        function.is_async(),
        function.is_const(),
        function.is_unsafe(),
    )
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
            let lifetime = lifetime_ref.as_ref().map(|x| x.name.as_str().to_owned());
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
        TypeRef::ImplTrait(type_bounds) => {
            let type_bounds = type_bounds
                .iter()
                .flat_map(|t| emit_hir_type_bound(trap, t))
                .collect();
            trap.emit(generated::ImplTraitType {
                id: trap::TrapId::Star,
                type_bounds,
            })
            .into()
        }
        TypeRef::DynTrait(type_bounds) => {
            let type_bounds = type_bounds
                .iter()
                .flat_map(|t| emit_hir_type_bound(trap, t))
                .collect();
            trap.emit(generated::DynTraitType {
                id: trap::TrapId::Star,
                type_bounds,
            })
            .into()
        }
        TypeRef::Macro(_) | TypeRef::Error => trap
            .emit(generated::ErrorType {
                id: trap::TrapId::Star,
            })
            .into(),
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

use super::*;

#[derive(serde::Serialize)]
pub(super) struct Material {
    types: Vec<TypeFact>,
    abi: oracle_abi::Material,
    vtables: Vec<VtableFact>,
}

#[derive(serde::Serialize)]
struct VtableFact {
    type_id: u64,
    principal: Option<u64>,
    entries: Vec<VtableEntry>,
}

#[derive(serde::Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum VtableEntry {
    DropInPlace { instance_id: Option<u64> },
    SizeBytes { value: u64 },
    AlignBytes { value: u64 },
    Vacant,
    Method { instance_id: u64 },
    SupertraitVtablePointer { principal: u64 },
}

#[derive(serde::Serialize)]
struct TypeFact {
    type_id: u64,
    layout: pool_layout::Layout,
    booleans: Booleans,
}

#[derive(serde::Serialize)]
struct Booleans {
    is_unsafe_cell: bool,
    has_erasable_regions: bool,
    is_c_void: bool,
    is_simd: bool,
    is_box: bool,
    is_global_box: bool,
    is_dynamic: bool,
    is_too_generic: bool,
    is_monomorphic: bool,
    is_monomorphic_enough: bool,
    is_like_maybe_dangling: bool,
    is_freeze: bool,
    is_unpin: bool,
    is_unsafe_unpin: bool,
    needs_drop: bool,
    opsem_inhabited: bool,
    is_sized: bool,
}

pub(super) fn collect<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &ExportContext<'tcx>,
) -> Result<Material, String> {
    let env = ty::TypingEnv::fully_monomorphized();
    let mut types = Vec::new();
    for (input, id) in context.type_ids.iter() {
        let node = context
            .type_ids
            .definition(*id)
            .ok_or("oracle encountered an unfinished type")?;
        let normalized = *context
            .type_ids
            .key(node.source_layout.normalized_type as usize)
            .ok_or("oracle normalized type is absent")?;
        let layout = tcx
            .layout_of(env.as_query_input(normalized))
            .map_err(|error| {
                format!("oracle layout failed for type {id} ({input:?}): {error:?}")
            })?;
        types.push(TypeFact {
            type_id: *id,
            layout: pool_layout::Layout::new(tcx, layout),
            booleans: Booleans {
                is_unsafe_cell: matches!(input.kind(), ty::Adt(def, _) if def.is_unsafe_cell()),
                has_erasable_regions: input.has_erasable_regions(),
                is_c_void: input.is_c_void(tcx),
                is_simd: input.is_simd(),
                is_box: input.is_box(),
                is_global_box: input.is_box_global(tcx),
                is_dynamic: matches!(input.kind(), ty::Dynamic(..)),
                is_too_generic: matches!(
                    input.kind(),
                    ty::Param(..)
                        | ty::Alias(..)
                        | ty::Bound(..)
                        | ty::Placeholder(..)
                        | ty::Infer(..)
                        | ty::Error(..)
                ),
                is_monomorphic: !input.has_non_region_param() && !input.has_escaping_bound_vars(),
                is_monomorphic_enough: !input.has_param(),
                is_like_maybe_dangling: input.is_like_maybe_dangling(),
                is_freeze: normalized.is_freeze(tcx, env),
                is_unpin: normalized.is_unpin(tcx, env),
                is_unsafe_unpin: normalized.is_unsafe_unpin(tcx, env),
                needs_drop: normalized.needs_drop(tcx, env),
                opsem_inhabited: normalized.is_opsem_inhabited(tcx, env),
                is_sized: normalized.is_sized(tcx, env),
            },
        });
    }
    let mut vtables = Vec::new();
    let mut seen = HashSet::new();
    for (input, predicates) in context.vtable_demands.iter() {
        let input = tcx
            .try_normalize_erasing_regions(env, ty::Unnormalized::new_wip(*input))
            .map_err(|error| format!("oracle vtable normalization failed: {error:?}"))?;
        let principal = predicates
            .principal()
            .map(|principal| {
                tcx.try_normalize_erasing_regions(
                    env,
                    ty::Unnormalized::new_wip(tcx.instantiate_bound_regions_with_erased(principal)),
                )
            })
            .transpose()
            .map_err(|error| format!("oracle vtable principal normalization failed: {error:?}"))?;
        if !seen.insert((input, principal)) {
            continue;
        }
        let principal_id = principal
            .map(|principal| {
                context
                    .predicate_ids
                    .get(&ty::Binder::dummy(ty::ExistentialPredicate::Trait(
                        principal,
                    )))
                    .copied()
                    .ok_or("oracle vtable principal is absent from production material")
            })
            .transpose()?;
        let entries = principal
            .map(|principal| tcx.vtable_entries(principal.with_self_ty(tcx, input)))
            .unwrap_or(TyCtxt::COMMON_VTABLE_ENTRIES);
        let layout = tcx
            .layout_of(env.as_query_input(input))
            .map_err(|error| format!("oracle vtable layout failed: {error:?}"))?;
        let entries = entries
            .iter()
            .map(|entry| {
                Ok(match *entry {
                    ty::VtblEntry::MetadataDropInPlace => VtableEntry::DropInPlace {
                        instance_id: if input.needs_drop(tcx, env) {
                            Some(
                                *context
                                    .instance_ids
                                    .get(&ty::Instance::resolve_drop_glue(tcx, input))
                                    .ok_or("oracle drop instance is absent")?,
                            )
                        } else {
                            None
                        },
                    },
                    ty::VtblEntry::MetadataSize => VtableEntry::SizeBytes {
                        value: layout.size.bytes(),
                    },
                    ty::VtblEntry::MetadataAlign => VtableEntry::AlignBytes {
                        value: layout.align.abi.bytes(),
                    },
                    ty::VtblEntry::Vacant => VtableEntry::Vacant,
                    ty::VtblEntry::Method(instance) => VtableEntry::Method {
                        instance_id: *context
                            .instance_ids
                            .get(&instance)
                            .ok_or("oracle vtable method is absent")?,
                    },
                    ty::VtblEntry::TraitVPtr(reference) => {
                        let principal = tcx
                            .try_normalize_erasing_regions(
                                env,
                                ty::Unnormalized::new_wip(ty::ExistentialTraitRef::erase_self_ty(
                                    tcx, reference,
                                )),
                            )
                            .map_err(|error| {
                                format!("oracle supertrait normalization failed: {error:?}")
                            })?;
                        VtableEntry::SupertraitVtablePointer {
                            principal: *context
                                .predicate_ids
                                .get(&ty::Binder::dummy(ty::ExistentialPredicate::Trait(
                                    principal,
                                )))
                                .ok_or("oracle supertrait principal is absent")?,
                        }
                    }
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        vtables.push(VtableFact {
            type_id: *context
                .type_ids
                .get(&input)
                .ok_or("oracle vtable type is absent")?,
            principal: principal_id,
            entries,
        });
    }
    Ok(Material {
        types,
        abi: oracle_abi::collect(tcx, context)?,
        vtables,
    })
}

pub(super) fn write(path: &Path, input: &Path, facts: Material) -> Result<(), String> {
    #[derive(serde::Serialize)]
    struct Document {
        schema: &'static str,
        rustc_commit: &'static str,
        snapshot_fnv1a64: String,
        snapshot_byte_length: u64,
        #[serde(flatten)]
        facts: Material,
    }
    let (snapshot_fnv1a64, snapshot_byte_length) = snapshot_fingerprint(input)?;
    write_document(
        path,
        &Document {
            schema: "lean-miri-rustc-oracle",
            rustc_commit: EXPECTED_RUSTC_COMMIT,
            snapshot_fnv1a64,
            snapshot_byte_length,
            facts,
        },
    )
}

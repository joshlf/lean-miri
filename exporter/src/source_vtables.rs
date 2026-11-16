use super::*;

#[derive(serde::Serialize)]
pub(super) struct Material {
    no_trait_vptr: bool,
    object_traits: Vec<ObjectTrait>,
    bindings: Vec<Binding>,
}

fn predicate_key<'tcx>(
    tcx: TyCtxt<'tcx>,
    predicates: &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
) -> Result<Vec<ty::ExistentialPredicate<'tcx>>, String> {
    let mut predicates = predicates.without_auto_traits().collect::<Vec<_>>();
    predicates.sort_by(|left, right| left.skip_binder().stable_cmp(tcx, &right.skip_binder()));
    predicates.dedup();
    predicates
        .into_iter()
        .map(|predicate| {
            tcx.try_normalize_erasing_regions(
                ty::TypingEnv::fully_monomorphized(),
                ty::Unnormalized::new_wip(tcx.instantiate_bound_regions_with_erased(predicate)),
            )
            .map_err(|error| {
                format!("vtable constructor predicate normalization failed: {error:?}")
            })
        })
        .collect()
}

#[derive(serde::Serialize)]
struct ObjectTrait {
    principal: u64,
    own_methods: Vec<u64>,
    super_traits: Vec<u64>,
}

#[derive(serde::Serialize)]
struct Method {
    owner: u64,
    definition: u64,
    instance_id: Option<u64>,
}

#[derive(serde::Serialize)]
struct Binding {
    type_id: u64,
    principal: Option<u64>,
    drop_instance: u64,
    methods: Vec<Method>,
}

#[derive(Default)]
pub(super) struct State<'tcx> {
    allocations: usize,
    requests: usize,
    predicates: usize,
    objects: OrderedSet<ty::ExistentialTraitRef<'tcx>>,
    object_cursor: usize,
    pairs: OrderedSet<(ty::Ty<'tcx>, Option<ty::ExistentialTraitRef<'tcx>>)>,
    pair_cursor: usize,
    object_traits: Vec<ObjectTrait>,
    bindings: Vec<Binding>,
    upcast_sites: usize,
    upcast_targets: usize,
    predicate_keys: HashMap<
        &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
        Vec<ty::ExistentialPredicate<'tcx>>,
    >,
}

fn normalized<'tcx>(
    tcx: TyCtxt<'tcx>,
    principal: ty::PolyExistentialTraitRef<'tcx>,
) -> Result<ty::ExistentialTraitRef<'tcx>, String> {
    tcx.try_normalize_erasing_regions(
        ty::TypingEnv::fully_monomorphized(),
        ty::Unnormalized::new_wip(tcx.instantiate_bound_regions_with_erased(principal)),
    )
    .map_err(|error| format!("object trait normalization failed: {error:?}"))
}

fn supertraits<'tcx>(
    tcx: TyCtxt<'tcx>,
    reference: ty::TraitRef<'tcx>,
) -> Result<Vec<ty::ExistentialTraitRef<'tcx>>, String> {
    let mut result = Vec::new();
    for clause in tcx
        .explicit_super_clauses_of(reference.def_id)
        .iter_instantiated_copied(tcx, reference.args)
    {
        let (clause, _) = clause.skip_norm_wip();
        if let ty::ClauseKind::Trait(predicate) = clause.kind().skip_binder() {
            if !matches!(predicate.polarity, ty::ClausePolarity::Positive) {
                return Err("negative object supertrait is not supported".into());
            }
            let reference = tcx
                .instantiate_bound_regions_with_erased(clause.kind().rebind(predicate.trait_ref));
            let principal = ty::ExistentialTraitRef::erase_self_ty(tcx, reference);
            let principal = normalized(tcx, ty::Binder::dummy(principal))?;
            if principal.has_non_region_param() || principal.has_escaping_bound_vars() {
                return Err(format!(
                    "object supertrait retains a type/const parameter: {principal:?}"
                ));
            }
            result.push(principal);
        }
    }
    Ok(result)
}

pub(super) fn discover<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    state: &mut State<'tcx>,
) -> Result<(), String> {
    for index in state.allocations..context.allocation_ids.len() {
        let allocation = *context.allocation_ids.key(index).unwrap();
        if let Some(GlobalAlloc::VTable(input, predicates)) = tcx.try_get_global_alloc(allocation) {
            context.vtable_demands.insert((input, predicates));
        }
    }
    state.allocations = context.allocation_ids.len();
    let sites = context.vtable_upcast_demands.len();
    let targets = context.vtable_demands.len();
    let first_site = if targets == state.upcast_targets { state.upcast_sites } else { 0 };
    for site in first_site..sites {
        let (source, target) = *context.vtable_upcast_demands.get_index(site).unwrap();
        if !state.predicate_keys.contains_key(&source) {
            state
                .predicate_keys
                .insert(source, predicate_key(tcx, source)?);
        }
        let first_target = if site < state.upcast_sites { state.upcast_targets } else { 0 };
        for index in first_target..targets {
            let (concrete, actual) = *context.vtable_demands.get_index(index).unwrap();
            if !state.predicate_keys.contains_key(&actual) {
                state
                    .predicate_keys
                    .insert(actual, predicate_key(tcx, actual)?);
            }
            if state.predicate_keys[&source] == state.predicate_keys[&actual] {
                let (concrete, target) = tcx.erase_and_anonymize_regions((concrete, target));
                type_json(context, tcx, concrete)?;
                for predicate in target {
                    existential_predicate_json(context, tcx, predicate)?;
                }
                context.vtable_demands.insert((concrete, target));
            }
        }
    }
    state.upcast_sites = sites;
    state.upcast_targets = targets;
    for (input, predicates) in context.vtable_demands.suffix(state.requests) {
        let input = tcx
            .try_normalize_erasing_regions(
                ty::TypingEnv::fully_monomorphized(),
                ty::Unnormalized::new_wip(*input),
            )
            .map_err(|error| format!("vtable concrete type normalization failed: {error:?}"))?;
        let principal = predicates
            .principal()
            .map(|principal| normalized(tcx, principal))
            .transpose()?;
        state.pairs.insert((input, principal));
    }
    state.requests = context.vtable_demands.len();
    let declared = context.pending_predicates[state.predicates..]
        .iter()
        .filter_map(|predicate| match predicate.skip_binder() {
            ty::ExistentialPredicate::Trait(principal) => Some(predicate.rebind(principal)),
            _ => None,
        })
        .collect::<Vec<_>>();
    state.predicates = context.pending_predicates.len();
    for principal in declared {
        state.objects.insert(normalized(tcx, principal)?);
    }
    loop {
        while state.pair_cursor < state.pairs.len() {
            let (input, principal) = *state.pairs.get_index(state.pair_cursor).unwrap();
            state.pair_cursor += 1;
            let type_id = type_json(context, tcx, input)?;
            let predicates = if let Some(principal) = principal {
                let predicate = ty::Binder::dummy(ty::ExistentialPredicate::Trait(principal));
                existential_predicate_json(context, tcx, predicate)?;
                tcx.mk_poly_existential_predicates(&[predicate])
            } else {
                tcx.mk_poly_existential_predicates(&[])
            };
            context.vtable_demands.insert((input, predicates));
            type_json(context, tcx, ty::Ty::new_mut_ptr(tcx, input))?;
            type_json(
                context,
                tcx,
                ty::Ty::new_mut_ref(tcx, tcx.lifetimes.re_erased, input),
            )?;
            let drop_instance =
                context.register_vtable_target(ty::Instance::resolve_drop_glue(tcx, input));
            let mut methods = Vec::new();
            let principal_id = if let Some(principal) = principal {
                state.objects.insert(principal);
                let owner = existential_predicate_json(
                    context,
                    tcx,
                    ty::Binder::dummy(ty::ExistentialPredicate::Trait(principal)),
                )?;
                let reference = principal.with_self_ty(tcx, input);
                for &definition in tcx.own_existential_vtable_entries(principal.def_id) {
                    let args =
                        ty::GenericArgs::for_item(tcx, definition, |parameter, _| match parameter
                            .kind
                        {
                            ty::GenericParamDefKind::Lifetime => tcx.lifetimes.re_erased.into(),
                            ty::GenericParamDefKind::Type { .. }
                            | ty::GenericParamDefKind::Const { .. } => {
                                reference.args[parameter.index as usize]
                            }
                        });
                    let args = tcx
                        .try_normalize_erasing_regions(
                            ty::TypingEnv::fully_monomorphized(),
                            ty::Unnormalized::new_wip(args),
                        )
                        .map_err(|error| {
                            format!("vtable method argument normalization failed: {error:?}")
                        })?;
                    let instance_id =
                        if tcx.instantiate_and_check_impossible_clauses((definition, args)) {
                            None
                        } else {
                            Some(context.register_vtable_target(
                                ty::Instance::expect_resolve_for_vtable(
                                    tcx,
                                    ty::TypingEnv::fully_monomorphized(),
                                    definition,
                                    args,
                                    rustc_span::DUMMY_SP,
                                ),
                            ))
                        };
                    methods.push(Method {
                        owner,
                        definition: def_json(context, definition),
                        instance_id,
                    });
                }
                for parent in supertraits(tcx, reference)? {
                    state.pairs.insert((input, Some(parent)));
                }
                Some(owner)
            } else {
                None
            };
            state.bindings.push(Binding {
                type_id,
                principal: principal_id,
                drop_instance,
                methods,
            });
        }
        while state.object_cursor < state.objects.len() {
            let principal = *state.objects.get_index(state.object_cursor).unwrap();
            state.object_cursor += 1;
            let principal_id = existential_predicate_json(
                context,
                tcx,
                ty::Binder::dummy(ty::ExistentialPredicate::Trait(principal)),
            )?;
            let self_type = ty::Ty::new_param(tcx, 0, rustc_span::Symbol::intern("Self"));
            let mut parents = Vec::new();
            for parent in supertraits(tcx, principal.with_self_ty(tcx, self_type))? {
                state.objects.insert(parent);
                parents.push(existential_predicate_json(
                    context,
                    tcx,
                    ty::Binder::dummy(ty::ExistentialPredicate::Trait(parent)),
                )?);
            }
            state.object_traits.push(ObjectTrait {
                principal: principal_id,
                own_methods: tcx
                    .own_existential_vtable_entries(principal.def_id)
                    .iter()
                    .map(|definition| def_json(context, *definition))
                    .collect(),
                super_traits: parents,
            });
        }
        if state.pair_cursor == state.pairs.len() && state.object_cursor == state.objects.len() {
            break;
        }
    }
    Ok(())
}

pub(super) fn finish(tcx: TyCtxt<'_>, state: State<'_>) -> Material {
    Material {
        no_trait_vptr: tcx.sess.opts.unstable_opts.no_trait_vptr,
        object_traits: state.object_traits,
        bindings: state.bindings,
    }
}

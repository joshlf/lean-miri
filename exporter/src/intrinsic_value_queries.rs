//! Concrete type_name intrinsic material.
use super::*;
#[derive(serde::Serialize)]
pub(super) struct TypeName {
    #[serde(flatten)]
    value: pool_constant::Value,
    input_type: u64,
    result_type: u64,
    typing_env: &'static str,
}
pub(super) fn discover_type_names<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    state: &mut TypeNames<'tcx>,
) -> Result<(), String> {
    let mut requested = Vec::new();
    for instance in context.instance_events[state.events..].iter().copied() {
        if tcx.intrinsic(instance.def_id()).is_some()
            && tcx.item_name(instance.def_id()).as_str() == "type_name"
        {
            let input = instance.args.type_at(0);
            if state.completed.insert(input) { requested.push(input); }
        }
    }
    state.events = context.instance_events.len();
    let result_type = ty::Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, tcx.types.str_);
    let facts = requested
            .into_iter()
            .map(|input| {
                let value = if input.has_non_region_param()
                    || input.has_escaping_bound_vars()
                    || input.has_infer()
                    || input.has_placeholders()
                    || input.references_error()
                {
                    unavailable_compiler_fact("type_name requires monomorphic input")?
                } else {
                    let name = rustc_const_eval::util::type_name(tcx, input);
                    let bytes = name.into_bytes();
                    let meta = bytes.len() as u64;
                    let alloc_id = tcx.allocate_bytes_dedup(bytes, CTFE_ALLOC_SALT);
                    compiler_fact(const_value_json(
                        context,
                        tcx,
                        result_type,
                        rustc_middle::mir::ConstValue::Slice { alloc_id, meta },
                    )?)
                };
                Ok::<_, String>(TypeNameFact {
                    value,
                    input_type: type_json(context, tcx, input)?,
                    result_type: type_json(context, tcx, result_type)?,
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
    state.facts.extend(facts);
    Ok(())
}
pub(super) struct TypeNameFact {
    value: pool_constant::Value,
    input_type: u64,
    result_type: u64,
}
#[derive(Default)]
pub(super) struct TypeNames<'tcx> {
    events: usize,
    completed: HashSet<ty::Ty<'tcx>>,
    facts: Vec<TypeNameFact>,
}
pub(super) fn finish_type_names(mut state: TypeNames<'_>) -> Vec<TypeName> {
    state.facts.sort_by_key(|fact| fact.input_type);
    state.facts.into_iter().map(|fact| TypeName {
        value: fact.value,
        input_type: fact.input_type,
        result_type: fact.result_type,
        typing_env: "fully_monomorphized",
    }).collect()
}

//! Concrete function-pointer targets discovered from actual MIR casts.
use super::*;
#[derive(Clone, serde::Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum Target {
    FunctionPointer { input_type: u64, instance_id: Option<u64> },
    ClosureOnce { input_type: u64, instance_id: u64 },
}
#[derive(Default)]
pub(super) struct State {
    inputs: usize,
    boxes: usize,
    pub rows: Vec<Target>,
}
fn instance<'tcx>(
    context: &mut ExportContext<'tcx>,
    value: ty::Instance<'tcx>,
) -> u64 {
    context.fn_pointer_targets.insert(value);
    context.register_instance(value)
}
fn closed(input: ty::Ty<'_>) -> bool {
    !input.has_non_region_param()
        && !input.has_escaping_bound_vars()
        && !input.has_infer()
        && !input.has_placeholders()
        && !input.references_error()
}
pub(super) fn discover<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Result<(), String> {
    let env = ty::TypingEnv::fully_monomorphized();
    let mut state = std::mem::take(&mut context.cast_state);
    let mut records = Vec::new();
    let cast_end = context.fn_pointer_cast_inputs.len();
    let inputs = (state.inputs..cast_end)
        .map(|index| *context.fn_pointer_cast_inputs.get_index(index).unwrap())
        .collect::<Vec<_>>();
    state.inputs = cast_end;
    for input in inputs {
        if !closed(input) {
            export_failure::<()>("cast resolution", "requires normalized monomorphic input")?;
        }
        let normal = tcx
            .try_normalize_erasing_regions(env, ty::Unnormalized::new_wip(input))
            .map_err(|error| format!("cast input normalization failed: {error:?}"))?;
        let result = match *normal.kind() {
            ty::FnDef(def, args) => {
                let args = match args.no_bound_vars() {
                    Some(args) => args,
                    None => {
                        return unavailable_compiler_fact(
                            "source FnDef args.no_bound_vars assertion failed",
                        );
                    }
                };
                let _ = ty::Instance::try_resolve(tcx, env, def, args)
                    .map_err(|error| format!("function-pointer resolution failed: {error:?}"))?;
                let resolution = match ty::Instance::resolve_for_fn_ptr(tcx, env, def, args) {
                    Some(resolved) => {
                        Some(instance(context, resolved))
                    },
                    None => None,
                };
                Target::FunctionPointer {
                    input_type: type_json(context, tcx, input)?,
                    instance_id: resolution,
                }
            }
            ty::Closure(def, args) => {
                let resolved = ty::Instance::resolve_closure(tcx, def, args, ty::ClosureKind::FnOnce);
                let instance_id = instance(context, resolved);
                Target::ClosureOnce {
                    input_type: type_json(context, tcx, input)?,
                    instance_id,
                }
            }
            _ => {
                return export_failure(
                    "cast resolution",
                    "normalization changed function/closure query kind",
                );
            }
        };
        records.push(result);
    }
    let boxes = context.cast_box_requests.suffix(state.boxes).to_vec();
    state.boxes = context.cast_box_requests.len();
    for input in boxes {
        if tcx.lang_items().owned_box().is_some() {
            type_json(context, tcx, ty::Ty::new_box(tcx, input))?;
        } else {
            return export_failure(
                "cast box type",
                "Box constructor requires owned_box lang item",
            );
        }
    }
    state.rows.extend(records);
    context.cast_state = state;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn absent_function_pointer_target_remains_absent() {
        let absent = serde_json::to_value(Target::FunctionPointer { input_type: 3, instance_id: None }).unwrap();
        let present = serde_json::to_value(Target::FunctionPointer { input_type: 3, instance_id: Some(7) }).unwrap();
        assert!(absent["instance_id"].is_null());
        assert_eq!(present["instance_id"], 7);
    }
}

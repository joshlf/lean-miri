use super::{ExportContext, checked_instance_mir, pool_layout};
use rustc_middle::mir::{Operand, TerminatorKind};
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use serde::Serialize;
use std::collections::HashSet;

#[derive(Serialize)]
pub(super) struct FnAbi {
    calling_convention: pool_layout::CanonAbi,
    c_variadic: bool,
    fixed_count: u32,
    can_unwind: bool,
    #[serde(rename = "return")]
    ret: pool_layout::ArgAbi,
    arguments: Vec<pool_layout::ArgAbi>,
}

#[derive(Serialize)]
struct InstanceRow {
    instance_id: u64,
    extra_argument_types: Vec<u64>,
    abi: FnAbi,
}

#[derive(Serialize)]
struct PointerRow {
    type_id: u64,
    extra_argument_types: Vec<u64>,
    abi: FnAbi,
}

#[derive(Serialize)]
struct ExcludedPointer {
    type_id: u64,
    reason: &'static str,
}

#[derive(Serialize)]
pub(super) struct Material {
    abi_layouts: Vec<pool_layout::Layout>,
    instances: Vec<InstanceRow>,
    pointers: Vec<PointerRow>,
    excluded_pointers: Vec<ExcludedPointer>,
}

pub(super) fn collect<'tcx>(tcx: TyCtxt<'tcx>, context: &ExportContext<'tcx>) -> Result<Material, String> {
    let env = ty::TypingEnv::fully_monomorphized();
    let empty = ty::List::empty();
    let mut instances = Vec::new();
    let mut pointers = Vec::new();
    let mut excluded_pointers = Vec::new();
    let mut seen_instances = HashSet::new();
    let mut seen_pointers = HashSet::new();
    for &instance in context.pending_instances.iter().chain(&context.source_abi_demands) {
        if !matches!(instance.def, ty::InstanceKind::LlvmIntrinsic(_)) && seen_instances.insert((instance, empty)) {
            instances.push((instance, empty));
        }
    }
    for &ty in context.type_ids.keys() {
        if matches!(ty.kind(), ty::FnPtr(..)) && ty.fn_sig(tcx).skip_binder().abi() != rustc_abi::ExternAbi::LlvmIntrinsic {
            // Metadata signatures can still refer to enclosing binders. Such
            // types cannot be query operands in normalized concrete MIR.
            if ty.has_escaping_bound_vars() {
                excluded_pointers.push(ExcludedPointer {
                    type_id: context.type_ids[&ty], reason: "escaping_bound_variables",
                });
                continue;
            }
            seen_pointers.insert((ty, empty));
            pointers.push((ty, empty));
        }
    }
    // Vararg requests come from actual monomorphized call operands. The oracle
    // neither creates candidate combinations nor extends the production graph.
    for key in context.bodies.keys() {
        let template = if let Some(promoted) = key.promoted {
            &tcx.promoted_mir(key.instance.def_id())[promoted]
        } else {
            checked_instance_mir(tcx, key.instance.def)?
        };
        let body = key.instance.try_instantiate_mir_and_normalize_erasing_regions(
            tcx, template.typing_env(tcx), ty::EarlyBinder::bind(tcx, template.clone()),
        ).map_err(|error| format!("ABI oracle MIR normalization failed: {error:?}"))?;
        for block in body.basic_blocks.iter() {
            let (function, args) = match &block.terminator().kind {
                TerminatorKind::Call { func, args, .. } | TerminatorKind::TailCall { func, args, .. } => (func, args),
                _ => continue,
            };
            let function_ty = Operand::ty(function, &body, tcx);
            if !matches!(function_ty.kind(), ty::FnDef(..) | ty::FnPtr(..)) { continue; }
            if function_ty.has_escaping_bound_vars() {
                return Err("ABI oracle actual MIR call has escaping bound variables".into());
            }
            let signature = tcx.try_normalize_erasing_regions(env, ty::Unnormalized::new_wip(function_ty.fn_sig(tcx)))
                .map_err(|error| format!("ABI oracle call signature normalization failed: {error:?}"))?;
            let signature = signature.skip_binder();
            if !signature.c_variadic() { continue; }
            let extras = args.get(signature.inputs().len()..).ok_or("ABI oracle call has too few arguments")?;
            let extras = tcx.mk_type_list_from_iter(extras.iter().map(|argument| argument.node.ty(&body, tcx)));
            match *function_ty.kind() {
                ty::FnDef(definition, arguments) => {
                    let instance = ty::Instance::try_resolve(tcx, env, definition, arguments.skip_binder())
                        .map_err(|error| format!("ABI oracle callee resolution failed: {error:?}"))?
                        .ok_or("ABI oracle callee unresolved")?;
                    if seen_instances.insert((instance, extras)) { instances.push((instance, extras)); }
                }
                ty::FnPtr(..) => if seen_pointers.insert((function_ty, extras)) { pointers.push((function_ty, extras)); },
                _ => unreachable!(),
            }
        }
    }
    excluded_pointers.sort_by_key(|row| row.type_id);
    let mut result = Material { abi_layouts: Vec::new(), instances: Vec::new(), pointers: Vec::new(), excluded_pointers };
    for (instance, extra) in instances {
        let instance_id = *context.instance_ids.get(&instance).ok_or("ABI oracle callee outside production instance graph")?;
        let abi = tcx.fn_abi_of_instance_no_deduced_attrs(env.as_query_input((instance, extra)))
            .map_err(|error| format!("ABI oracle instance query failed: {instance:?}: {error:?}"))?;
        let abi = serialize(tcx, context, &mut result.abi_layouts, abi)?;
        let extra_argument_types = type_ids(context, extra)?;
        result.instances.push(InstanceRow { instance_id, extra_argument_types, abi });
    }
    for (ty, extra) in pointers {
        let type_id = *context.type_ids.get(&ty).ok_or("ABI oracle pointer outside production type graph")?;
        let abi = tcx.fn_abi_of_fn_ptr(env.as_query_input((ty.fn_sig(tcx), extra)))
            .map_err(|error| format!("ABI oracle pointer query failed: {ty:?}: {error:?}"))?;
        let abi = serialize(tcx, context, &mut result.abi_layouts, abi)?;
        let extra_argument_types = type_ids(context, extra)?;
        result.pointers.push(PointerRow { type_id, extra_argument_types, abi });
    }
    Ok(result)
}

fn type_ids<'tcx>(context: &ExportContext<'tcx>, types: &[ty::Ty<'tcx>]) -> Result<Vec<u64>, String> {
    types.iter().map(|ty| context.type_ids.get(ty).copied()
        .ok_or_else(|| format!("ABI oracle type outside production graph: {ty:?}"))).collect()
}

fn serialize<'tcx>(tcx: TyCtxt<'tcx>, context: &ExportContext<'tcx>, layouts: &mut Vec<pool_layout::Layout>,
    abi: &rustc_target::callconv::FnAbi<'tcx, ty::Ty<'tcx>>) -> Result<FnAbi, String> {
    let mut argument = |arg: &rustc_target::callconv::ArgAbi<'tcx, ty::Ty<'tcx>>| -> Result<pool_layout::ArgAbi, String> {
        let ty = *context.type_ids.get(&arg.layout.ty)
            .ok_or_else(|| format!("ABI oracle argument outside production type graph: {:?}", arg.layout.ty))?;
        let layout = layouts.len();
        layouts.push(pool_layout::Layout::new(tcx, arg.layout));
        Ok(pool_layout::ArgAbi { ty, layout, mode: pool_layout::PassMode::new(&arg.mode) })
    };
    Ok(FnAbi {
        calling_convention: pool_layout::CanonAbi::new(abi.conv), c_variadic: abi.c_variadic,
        fixed_count: abi.fixed_count, can_unwind: abi.can_unwind,
        ret: argument(&abi.ret)?, arguments: abi.args.iter().map(argument).collect::<Result<_, _>>()?,
    })
}

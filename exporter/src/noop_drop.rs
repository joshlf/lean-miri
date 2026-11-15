//! Raw signature source for the exact rustc DropGlue(_, None) shim family.
//! No instance_mir call or executable MIR is needed by this module.
use rustc_middle::{mir,ty::{self,TyCtxt,TypeVisitableExt}};

pub struct Interface<'tcx> {
    pub argument_count: usize,
    pub spread_argument: Option<mir::Local>,
    pub arguments: Vec<(mir::Local, ty::Ty<'tcx>)>,
    pub return_type: ty::Ty<'tcx>,
}

fn closed_arguments(args: ty::GenericArgsRef<'_>) -> bool {
    !args.has_non_region_param() && !args.has_escaping_bound_vars()
        && !args.has_infer() && !args.has_placeholders() && !args.references_error()
}


pub fn eligible<'tcx>(tcx:TyCtxt<'tcx>,instance:ty::Instance<'tcx>)->bool {
    let ty::InstanceKind::Shim(ty::ShimKind::DropGlue(def,None))=instance.def else {return false};
    if !closed_arguments(instance.args) {return false}
    let signature=tcx.fn_sig(def).instantiate_identity().skip_norm_wip();
    // The exact lang-item signature has one input and region-only binders.
    // A future pinned declaration outside this domain is an explicit residual.
    signature.skip_binder().inputs().len()==1
        && signature.bound_vars().iter().all(|bound|matches!(bound,ty::BoundVariableKind::Region(_)))
}

/// Remaining transfer-catalog material uses only substituted interface types;
/// it must not request or normalize a complete shim MIR body.
pub fn interface<'tcx>(tcx:TyCtxt<'tcx>,instance:ty::Instance<'tcx>)
    ->Result<Interface<'tcx>,String> {
    if !eligible(tcx,instance) {return Err("no-op drop shim interface outside selected source category".into())}
    let signature=tcx.fn_sig(instance.def.def_id()).instantiate(tcx,instance.args).skip_norm_wip();
    let signature=tcx.erase_and_anonymize_regions(tcx.instantiate_bound_regions_with_erased(signature));
    Ok(Interface {
        argument_count:1,spread_argument:None,
        arguments:vec![(mir::Local::from_u32(1),signature.inputs()[0])],
        return_type:signature.output(),
    })
}

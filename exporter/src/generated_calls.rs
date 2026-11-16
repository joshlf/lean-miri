use super::{ExportContext, type_json};
use rustc_middle::ty::{Ty, TyCtxt};

pub(super) fn register_types<'tcx>(context: &mut ExportContext<'tcx>, tcx: TyCtxt<'tcx>,
    inputs: Vec<Ty<'tcx>>, output: Ty<'tcx>) -> Result<(), String> {
    for ty in inputs.into_iter().chain(std::iter::once(output)) {
        type_json(context, tcx, ty)?;
    }
    Ok(())
}

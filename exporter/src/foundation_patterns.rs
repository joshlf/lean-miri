//! Pattern-type constraints are source structure, never erased into base types.
use super::*;
impl<'tcx> Material<'tcx> {
    pub(super) fn pattern_type(&mut self, tcx: TyCtxt<'tcx>, base: ty::Ty<'tcx>, pattern: ty::Pattern<'tcx>) -> Result<Value> {
        let pattern = match *pattern.0 {
            ty::PatternKind::NotNull => json!({"kind":"not_null"}),
            other => return unsupported("source type pattern",other),
        };
        Ok(json!({"kind":"pattern_type","base":self.ty(tcx,base)?,"pattern":pattern}))
    }
}

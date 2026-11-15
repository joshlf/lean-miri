//! Unevaluated scalar const-item source. Reads MIR expressions, never const_eval.
use super::*;

impl<'tcx> Material<'tcx> {
    pub(super) fn constant_definition(&mut self, tcx: TyCtxt<'tcx>, value: mir::UnevaluatedConst<'tcx>) -> Result<Value> {
        if value.promoted.is_some() || !value.args.is_empty() {
            return unsupported("generic or promoted const definition", value);
        }
        if tcx.def_kind(value.def) != rustc_hir::def::DefKind::Const {
            return unsupported("non-free const definition", value.def);
        }
        let definition = self.definition(tcx,value.def);
        if self.definitions[definition].get("const_expression").is_none() {
            self.definitions[definition]["const_expression"] = json!({"pending":true});
            let body = tcx.mir_for_ctfe(value.def);
            crate::ensure_untainted_mir(body)?;
            if body.basic_blocks.len() != 1 || body.arg_count != 0 || body.local_decls.len() != 1 {
                return unsupported("non-expression const body", value.def);
            }
            if !self.required_constants(tcx,body)?.is_empty() {
                return unsupported("nested required constants in const expression", value.def);
            }
            let block = &body.basic_blocks[mir::START_BLOCK];
            if block.is_cleanup || block.statements.len() != 1 ||
                !matches!(block.terminator().kind, mir::TerminatorKind::Return) {
                return unsupported("const expression control flow", value.def);
            }
            let mir::StatementKind::Assign(assignment) = &block.statements[0].kind else {
                return unsupported("const expression statement", value.def);
            };
            if assignment.0.local != mir::RETURN_PLACE || !assignment.0.projection.is_empty() {
                return unsupported("const expression destination", value.def);
            }
            let mir::Rvalue::Use(operand, retag) = &assignment.1 else {
                return unsupported("const expression rvalue", &assignment.1);
            };
            let expression = self.operand(tcx,operand)?;
            self.definitions[definition]["const_expression"] = json!({
                "type":self.ty(tcx,body.return_ty())?,"operand":expression,"retag":retag.yes()});
        }
        Ok(json!({"kind":"unevaluated","definition":definition,"arguments":[]}))
    }
}

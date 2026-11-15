//! Unevaluated scalar const-item source. Reads MIR expressions, never const_eval.
use super::*;
#[path = "foundation_const_aggregate.rs"]
mod aggregate_material;

impl<'tcx> Material<'tcx> {
    pub(super) fn constant_definition(&mut self, tcx: TyCtxt<'tcx>, value: mir::UnevaluatedConst<'tcx>) -> Result<Value> {
        if value.promoted.is_some() || !value.args.is_empty() {
            return unsupported("generic or promoted const definition", value);
        }
        let associated = tcx.def_kind(value.def) == rustc_hir::def::DefKind::AssocConst;
        if tcx.def_kind(value.def) != rustc_hir::def::DefKind::Const && !associated {
            return unsupported("non-constant definition", value.def);
        }
        if associated {
            let parent=tcx.parent(value.def);
            if !matches!(tcx.def_kind(parent),rustc_hir::def::DefKind::Impl {of_trait:false}) || tcx.generics_of(parent).count()!=0 {
                return unsupported("generic or trait-associated constant owner",value.def);
            }
        }
        let definition = self.definition(tcx,value.def);
        if self.definitions[definition].get("const_expression").is_none() {
            self.definitions[definition]["const_expression"] = json!({"pending":true});
            if associated {
                let owner=tcx.parent(value.def);
                self.definitions[definition]["const_owner"] = json!({"kind":"inherent_impl",
                    "definition":self.definition(tcx,owner),"environment":self.environment(tcx,value.def)?});
            }
            // Pinned metadata encoder replaces trivial one-Use MIR with this
            // literal record. This is the encoded declaration, not const_eval;
            // its original trivial reference chain is not retained by rustc.
            if !value.def.is_local() {
                if let Some((literal,ty)) = tcx.trivial_const(value.def) {
                    let mir::ConstValue::Scalar(scalar)=literal else {return unsupported("metadata trivial constant shape",literal)};
                    let scalar=scalar.try_to_scalar_int().map_err(|_|"foundation: metadata trivial pointer constant unsupported")?;
                    self.definitions[definition]["const_expression"] = json!({
                        "kind":"metadata_trivial_literal","type":self.ty(tcx,ty)?,
                        "original_reference_chain":"unavailable_in_pinned_metadata",
                        "literal":{"kind":"constant","type":self.ty(tcx,ty)?,"value":{
                            "kind":"scalar","bits":scalar.to_bits(scalar.size()).to_string(),"size_bytes":scalar.size().bytes()}}});
                    return Ok(json!({"kind":"unevaluated","definition":definition,"arguments":[]}));
                }
            }
            let body = tcx.mir_for_ctfe(value.def);
            crate::ensure_untainted_mir(body)?;
            if body.arg_count != 0 || body.coroutine.is_some() || body.spread_arg.is_some()
                || body.source.promoted.is_some() || body.source.instance != ty::InstanceKind::Item(value.def) {
                return unsupported("non-item const body", value.def);
            }
            let required = self.required_constants(tcx,body)?;
            let simple = body.basic_blocks.len() == 1 && body.local_decls.len() == 1
                && required.is_empty() && !body.basic_blocks[mir::START_BLOCK].is_cleanup
                && body.basic_blocks[mir::START_BLOCK].statements.len() == 1
                && matches!(body.basic_blocks[mir::START_BLOCK].terminator().kind,mir::TerminatorKind::Return);
            if !simple || !matches!(body.basic_blocks[mir::START_BLOCK].statements[0].kind,mir::StatementKind::Assign(ref assignment) if matches!(assignment.1,mir::Rvalue::Use(..))) {
                let material = self.constant_mir_body(tcx,body,required)?;
                self.definitions[definition]["const_expression"] = json!({
                    "kind":if matches!(body.return_ty().kind(),ty::Adt(..)) {"aggregate_mir"} else {"mir"},"type":self.ty(tcx,body.return_ty())?,"mir":material});
                return Ok(json!({"kind":"unevaluated","definition":definition,"arguments":[]}));
            }
            let block = &body.basic_blocks[mir::START_BLOCK];
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
    pub(super) fn constant_mir_body(&mut self, tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>, required: Vec<Value>) -> Result<Value> {
        let locals = body.local_decls.iter().map(|local|self.ty(tcx,local.ty)).collect::<Result<Vec<_>>>()?;
        let blocks = body.basic_blocks.iter().map(|block| {
            if block.is_cleanup { return unsupported("const cleanup block", block); }
            let statements = block.statements.iter().map(|statement| Ok(match &statement.kind {
                mir::StatementKind::Assign(assignment) => json!({"kind":"assign",
                    "place":self.place(tcx,assignment.0)?,"value":self.constant_source_rvalue(tcx,&assignment.1)?}),
                mir::StatementKind::StorageLive(local) => json!({"kind":"storage_live","local":local.as_u32()}),
                mir::StatementKind::StorageDead(local) => json!({"kind":"storage_dead","local":local.as_u32()}),
                mir::StatementKind::Nop => json!({"kind":"nop"}),
                other => return unsupported("const MIR statement",other),
            })).collect::<Result<Vec<_>>>()?;
            let terminator = match &block.terminator().kind {
                mir::TerminatorKind::Return => json!({"kind":"return"}),
                mir::TerminatorKind::Goto {target,..} => json!({"kind":"goto","target":target.as_u32()}),
                mir::TerminatorKind::SwitchInt {discr,targets} => json!({"kind":"switch_int",
                    "operand":self.operand(tcx,discr)?,"targets":targets.iter().map(|(value,target)|json!({"value":value.to_string(),"target":target.as_u32()})).collect::<Vec<_>>(),
                    "otherwise":targets.otherwise().as_u32()}),
                mir::TerminatorKind::Assert {cond,expected,msg,target,unwind} => {
                    if !matches!(unwind,mir::UnwindAction::Continue) { return unsupported("const assert unwind",unwind); }
                    let mir::AssertKind::Overflow(operator,left,right) = &**msg
                        else { return unsupported("const assert message",msg); };
                    json!({"kind":"assert","condition":self.operand(tcx,cond)?,"expected":expected,
                        "target":target.as_u32(),"unwind":"continue","message":{"kind":"overflow",
                            "operator":crate::binop_name(*operator),"left":self.operand(tcx,left)?,"right":self.operand(tcx,right)?}})
                },
                other => return unsupported("const MIR terminator",other),
            };
            Ok(json!({"statements":statements,"terminator":terminator}))
        }).collect::<Result<Vec<_>>>()?;
        Ok(json!({"locals":locals,"required_consts":required,"blocks":blocks}))
    }

}

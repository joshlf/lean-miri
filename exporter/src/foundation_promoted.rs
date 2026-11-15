//! Complete promoted-MIR source tables, not evaluated/promoted allocation data.
//! Nonlocal queries are limited to the source-validated actual start edge.
use super::*;

impl<'tcx> Material<'tcx> {
    fn promoted_rvalue(&mut self, tcx: TyCtxt<'tcx>, value: &mir::Rvalue<'tcx>) -> Result<Value> {
        match value {
            mir::Rvalue::Cast(mir::CastKind::PointerCoercion(
                ty::adjustment::PointerCoercion::ReifyFnPointer(safety),source),operand,target) =>
                Ok(json!({"kind":"cast_reify_function_pointer",
                    "safety":match safety {rustc_hir::Safety::Safe=>"safe",rustc_hir::Safety::Unsafe=>"unsafe"},
                    "source":match source {mir::CoercionSource::AsCast=>"as_cast",mir::CoercionSource::Implicit=>"implicit"},
                    "operand":self.operand(tcx,operand)?,"target":self.ty(tcx,*target)?})),
            _ => self.rvalue(tcx,value),
        }
    }

    pub(super) fn promoted_table(&mut self, tcx: TyCtxt<'tcx>, owner: DefId) -> Result<Value> {
        if tcx.dcx().has_errors().is_some() { return Err("foundation: compiler errors during promoted source capture".into()); }
        let local_owner = super::super::has_local_hir_body(tcx,owner);
        let external_owner = !owner.is_local() &&
            (tcx.lang_items().start_fn() == Some(owner) || start_edge_material::start_internal(tcx)? == Some(owner));
        if (!local_owner && !external_owner) || tcx.def_kind(owner) != rustc_hir::def::DefKind::Fn
            || tcx.is_const_fn(owner) || !tcx.is_mir_available(owner) {
            return unsupported("promoted source table owner",owner);
        }
        let definition = self.definition(tcx,owner);
        let environment = self.environment(tcx,owner)?;
        // Pinned rustc_metadata/rmeta/encoder.rs::encode_mir records
        // promoted_mir alongside encoded MIR unless it is a trivial const.
        // Our non-const Fn guard excludes that exception; is_mir_available
        // supplies optimized MIR for the allowlisted external owners. Missing
        // metadata is never replaced with an empty table.
        let table = tcx.promoted_mir(owner);
        let templates = table.iter_enumerated().map(|(index,body)| {
            super::super::ensure_untainted_mir(body)?;
            if body.source.instance != ty::InstanceKind::Item(owner) || body.source.promoted != Some(index)
                || body.coroutine.is_some() {
                return unsupported("promoted body source identity",body.source);
            }
            if body.source_scopes.iter().any(|s|s.inlined.is_some() || s.inlined_parent_scope.is_some()) {
                return unsupported("promoted inlined source scopes",owner);
            }
            let required_consts = self.required_constants(tcx,body)?;
            let source_metadata = source_material::capture(tcx,body);
            let locals = body.local_decls.iter().map(|l|self.ty(tcx,l.ty)).collect::<Result<Vec<_>>>()?;
            let blocks = body.basic_blocks.iter().map(|block| {
                let statements = block.statements.iter().map(|statement|Ok(match &statement.kind {
                    mir::StatementKind::Assign(p) => json!({"kind":"assign","place":self.place(tcx,p.0)?,"value":self.promoted_rvalue(tcx,&p.1)?}),
                    mir::StatementKind::StorageLive(local) => json!({"kind":"storage_live","local":local.as_u32()}),
                    mir::StatementKind::StorageDead(local) => json!({"kind":"storage_dead","local":local.as_u32()}),
                    mir::StatementKind::Nop => json!({"kind":"nop"}),
                    other => return unsupported("promoted statement",other),
                })).collect::<Result<Vec<_>>>()?;
                let terminator = match &block.terminator().kind {
                    mir::TerminatorKind::Return => json!({"kind":"return"}),
                    mir::TerminatorKind::Goto {target,..} => json!({"kind":"goto","target":target.as_u32()}),
                    mir::TerminatorKind::Unreachable => json!({"kind":"unreachable"}),
                    other => return unsupported("promoted terminator",other),
                };
                Ok(json!({"cleanup":block.is_cleanup,"statements":statements,"terminator":terminator}))
            }).collect::<Result<Vec<_>>>()?;
            Ok(json!({"definition":definition,"promoted_index":index.as_u32(),
                "source_instance":{"kind":"item","definition":definition},"source_promoted":index.as_u32(),
                "argument_count":body.arg_count,"spread_argument":body.spread_arg.map(|l|l.as_u32()),
                "required_consts":required_consts,"source_metadata":source_metadata,"locals":locals,"blocks":blocks}))
        }).collect::<Result<Vec<_>>>()?;
        Ok(json!({"definition":definition,"environment":environment,"promoted_count":table.len(),"templates":templates}))
    }
}

#[cfg(test)]
fn source_document(tcx: TyCtxt<'_>, owner_path: &str) -> Result<Value> {
    let mut candidates = tcx.hir_crate_items(()).definitions().map(|d|d.to_def_id())
        .filter(|d|tcx.def_path_str(*d)==owner_path).collect::<Vec<_>>();
    if candidates.is_empty() {
        if let Some(def) = start_edge_material::start_internal(tcx)? {
            if tcx.def_path_str(def)==owner_path {candidates.push(def);}
        }
    }
    if candidates.len()!=1 {return unsupported("missing/ambiguous promoted source owner",owner_path);}
    let mut material = Material::default();
    let table = material.promoted_table(tcx,candidates[0])?;
    Ok(json!({"schema":"lean-miri-foundation","schema_version":1,
        "rustc_commit":super::super::EXPECTED_RUSTC_COMMIT,
        "target":{"triple":tcx.sess.opts.target_triple.to_string(),"architecture":tcx.sess.target.arch.to_string(),
            "data_layout":tcx.sess.target.data_layout.as_ref(),"runtime_data_layout":super::super::foundation_target::export(tcx)?,
            "pointer_size_bits":tcx.data_layout.pointer_size().bits(),"endian":match tcx.data_layout.endian {
                rustc_abi::Endian::Little=>"little",rustc_abi::Endian::Big=>"big"}},
        "definitions":material.definitions,"types":material.types,"bodies":[],
        "promoted_tables":[table],"source_allocations":material.allocations}))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    #[ignore = "source-only compiler callback requires explicit pinned fixture/arguments/output"]
    fn capture_complete_source_table() {
        struct Capture {owner:String,result:Option<Result<Value>>}
        impl Callbacks for Capture {
            fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
                self.result=Some(source_document(tcx,&self.owner)); Compilation::Stop
            }
        }
        let owner=std::env::var("PROMOTED_SOURCE_OWNER").expect("explicit source owner required");
        let args:Vec<String>=serde_json::from_str(&std::env::var("PROMOTED_SOURCE_ARGS").expect("explicit compiler arguments required")).unwrap();
        let output=std::env::var("PROMOTED_SOURCE_OUTPUT").expect("explicit source material output required");
        let mut capture=Capture {owner,result:None};
        let code=rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut capture));
        assert_eq!(code,std::process::ExitCode::SUCCESS);
        let document=capture.result.expect("analysis callback not reached").expect("unsupported source capture");
        std::fs::write(output,serde_json::to_vec(&document).unwrap()).unwrap();
    }
}

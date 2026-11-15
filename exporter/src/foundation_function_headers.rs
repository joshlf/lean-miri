//! Generic function source headers, independent of executable MIR availability.
//! This retains declared FnSig/binders/environment/attributes, never FnAbi or
//! normalized/monomorphic query answers. The explicit standard helper header is
//! selected from the actual generic start MIR FnDef edge.
use super::*;

impl<'tcx> Material<'tcx> {
    pub(super) fn function_header(&mut self, tcx: TyCtxt<'tcx>, definition: DefId) -> Result<Value> {
        if !matches!(tcx.def_kind(definition),rustc_hir::def::DefKind::Fn) || tcx.is_foreign_item(definition) {
            return unsupported("function header owner",definition);
        }
        let attrs = tcx.codegen_fn_attrs(definition);
        if !attrs.target_features.is_empty() { return unsupported("signature target features",definition); }
        Ok(json!({"definition":self.definition(tcx,definition),
            "environment":self.environment(tcx,definition)?,"signature":self.signature(tcx,definition)?,
            "function_attributes":{
                "never_unwind":attrs.flags.contains(rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags::NEVER_UNWIND),
                "track_caller":ty::InstanceKind::Item(definition).requires_caller_location(tcx),
                "is_foreign":tcx.is_foreign_item(definition),
                "is_drop_glue":tcx.is_lang_item(definition,rustc_attr_ir::LangItem::DropGlue)}}))
    }
}

pub(super) fn capture<'tcx>(tcx: TyCtxt<'tcx>, material: &mut Material<'tcx>, roots: &[String]) -> Result<Vec<Value>> {
    if roots.is_empty() { return Ok(Vec::new()); }
    if roots.len()!=1 || roots[0]!="std::rt::lang_start_internal" {
        return unsupported("function signature source demand",roots);
    }
    let definition = start_edge_material::start_internal(tcx)?
        .ok_or("foundation: actual start-internal signature source edge unavailable")?;
    Ok(vec![material.function_header(tcx,definition)?])
}

//! Generic function source headers, independent of executable MIR availability.
//! This retains declared FnSig/binders/environment/attributes, never FnAbi or
//! normalized/monomorphic query answers. The explicit standard helper header is
//! selected from the actual generic start MIR FnDef edge.
use super::*;

impl<'tcx> Material<'tcx> {
    pub(super) fn function_header(&mut self, tcx: TyCtxt<'tcx>, definition: DefId) -> Result<Value> {
        if tcx.is_foreign_item(definition) { return unsupported("foreign function header owner",definition); }
        let owner = match tcx.def_kind(definition) {
            rustc_hir::def::DefKind::Fn => json!({"kind":"free_function"}),
            rustc_hir::def::DefKind::AssocFn => {
                let parent = tcx.parent(definition);
                if !matches!(tcx.def_kind(parent),rustc_hir::def::DefKind::Impl {of_trait:false}) {
                    return unsupported("non-inherent method source header",definition);
                }
                let self_ty = tcx.type_of(parent).instantiate_identity().skip_normalization();
                json!({"kind":"inherent_method","impl_definition":self.definition(tcx,parent),
                    "self_type":self.ty(tcx,self_ty)?})
            }
            _ => return unsupported("function header owner",definition),
        };
        let attrs = tcx.codegen_fn_attrs(definition);
        if !attrs.target_features.is_empty() { return unsupported("signature target features",definition); }
        Ok(json!({"definition":self.definition(tcx,definition),"owner_declaration":owner,
            "runtime_source":super::super::foundation_runtime_instances::item(tcx,definition),
            "environment":self.environment(tcx,definition)?,"signature":self.signature(tcx,definition)?,
            "function_attributes":{
                "never_unwind":attrs.flags.contains(rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags::NEVER_UNWIND),
                "track_caller":ty::InstanceKind::Item(definition).requires_caller_location(tcx),
                "is_foreign":tcx.is_foreign_item(definition),
                "is_drop_glue":tcx.is_lang_item(definition,rustc_attr_ir::LangItem::DropGlue)}}))
    }
}

/// Headers use the same source-definition graph as executable roots. They do
/// not require MIR availability and never resolve a trait implementation.
pub(super) fn capture_for_roots<'tcx>(tcx: TyCtxt<'tcx>, material: &mut Material<'tcx>,
    roots: &[String], graph: &source_graph_material::Graph) -> Result<Vec<Value>> {
    let mut result = Vec::new();
    let mut seen = Vec::new();
    for root in roots {
        if seen.contains(root) { return unsupported("duplicate function signature source demand",root); }
        seen.push(root.clone());
        result.push(material.function_header(tcx,graph.declaration(tcx,root)?)?);
    }
    Ok(result)
}

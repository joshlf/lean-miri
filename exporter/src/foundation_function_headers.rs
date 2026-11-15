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
            "environment":self.environment(tcx,definition)?,"signature":self.signature(tcx,definition)?,
            "function_attributes":{
                "never_unwind":attrs.flags.contains(rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags::NEVER_UNWIND),
                "track_caller":ty::InstanceKind::Item(definition).requires_caller_location(tcx),
                "is_foreign":tcx.is_foreign_item(definition),
                "is_drop_glue":tcx.is_lang_item(definition,rustc_attr_ir::LangItem::DropGlue)}}))
    }
}

/// Resolve one explicit inherent callee only through the explicitly selected generic
/// closure MIR. This is a source edge, not trait selection or an ABI query.
fn selected_closure_callee(tcx: TyCtxt<'_>, requested: &str, source_roots: &[String]) -> Result<DefId> {
    let closures = closure_material::selected(tcx,source_roots)?;
    let mut methods = Vec::new();
    for closure in closures {
        for definition in closure_callee_material::direct_callees_of(tcx,closure)? {
            if tcx.def_path_str(definition)==requested { methods.push(definition); }
        }
    }
    methods.sort_by_key(|d|tcx.def_path_str(*d)); methods.dedup();
    if methods.len()!=1 { return unsupported("function signature source demand",requested); }
    Ok(methods[0])
}

pub(super) fn capture_for_roots<'tcx>(tcx: TyCtxt<'tcx>, material: &mut Material<'tcx>, roots: &[String], source_roots: &[String]) -> Result<Vec<Value>> {
    let mut result = Vec::new();
    let mut seen = Vec::new();
    for root in roots {
        if seen.contains(root) { return unsupported("duplicate function signature source demand",root); }
        seen.push(root.clone());
        let definition = match root.as_str() {
            "std::rt::lang_start_internal" => start_edge_material::start_internal(tcx)?
                .ok_or("foundation: actual start-internal signature source edge unavailable")?,
            requested => selected_closure_callee(tcx,requested,source_roots)?,
        };
        result.push(material.function_header(tcx,definition)?);
    }
    Ok(result)
}


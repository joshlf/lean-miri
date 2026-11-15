//! One explicit generic-MIR edge from the actual start language item. No
//! monomorphic instance or transitive compiler query closure is enumerated.
use super::*;

pub(super) fn start_internal(tcx: TyCtxt<'_>) -> Result<Option<DefId>> {
    let Some(start) = tcx.lang_items().start_fn() else { return Ok(None); };
    if start.is_local() || tcx.def_path_str(start) != "std::rt::lang_start" {
        return Ok(None);
    }
    if !tcx.is_mir_available(start) { return unsupported("start edge owner MIR unavailable", start); }
    let body = tcx.instance_mir(ty::InstanceKind::Item(start));
    super::super::ensure_untainted_mir(body)?;
    if body.source.instance != ty::InstanceKind::Item(start) || body.source.promoted.is_some() {
        return unsupported("start edge owner source", body.source);
    }
    let mut selected = Vec::new();
    for block in body.basic_blocks.iter() {
        if let mir::TerminatorKind::Call { func: mir::Operand::Constant(operand), .. } = &block.terminator().kind {
            if let ty::FnDef(definition, _) = *operand.const_.ty().kind() {
                if tcx.def_path_str(definition) == "std::rt::lang_start_internal" {
                    if !matches!(tcx.def_kind(definition), rustc_hir::def::DefKind::Fn)
                        || tcx.is_const_fn(definition) || !tcx.is_mir_available(definition) {
                        return unsupported("explicit start internal MIR owner", definition);
                    }
                    selected.push(definition);
                }
            }
        }
    }
    selected.sort_by_key(|definition|tcx.def_path_str(*definition));
    selected.dedup();
    if selected.len() > 1 { return unsupported("ambiguous start internal source edge", selected); }
    Ok(selected.first().copied())
}

/// Only the two direct generic FnDef calls in the selected internal startup
/// template are eligible. This is an explicit source frontier, not recursion.
pub(super) fn internal_callees(tcx: TyCtxt<'_>) -> Result<Vec<DefId>> {
    let Some(internal) = start_internal(tcx)? else { return Ok(Vec::new()); };
    let body = tcx.instance_mir(ty::InstanceKind::Item(internal));
    super::super::ensure_untainted_mir(body)?;
    if body.source.instance != ty::InstanceKind::Item(internal) || body.source.promoted.is_some() {
        return unsupported("internal startup edge owner source",body.source);
    }
    let mut selected = Vec::new();
    for block in body.basic_blocks.iter() {
        if let mir::TerminatorKind::Call { func: mir::Operand::Constant(operand), .. } = &block.terminator().kind {
            if let ty::FnDef(definition, _) = *operand.const_.ty().kind() {
                let path = tcx.def_path_str(definition);
                if path == "std::panic::catch_unwind" || path == "std::result::Result::<T, E>::unwrap_or_else" {
                    if !matches!(tcx.def_kind(definition),rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn)
                        || !tcx.is_mir_available(definition) {
                        return unsupported("explicit internal startup callee MIR owner",definition);
                    }
                    selected.push(definition);
                } else { return unsupported("internal startup callee frontier",definition); }
            } else { return unsupported("internal startup non-FnDef call",operand); }
        } else if matches!(block.terminator().kind,mir::TerminatorKind::Call {..}) {
            return unsupported("internal startup indirect call",block.terminator());
        }
    }
    selected.sort_by_key(|definition|tcx.def_path_str(*definition));
    selected.dedup();
    if selected.len() != 2 { return unsupported("internal startup callee count",selected); }
    Ok(selected)
}

pub(super) fn selected(tcx: TyCtxt<'_>, roots: &[String]) -> Result<Vec<DefId>> {
    let mut selected = Vec::new();
    if roots.iter().any(|name| name == "std::rt::lang_start_internal") {
        selected.extend(start_internal(tcx)?);
    }
    if roots.iter().any(|name|name == "std::panic::catch_unwind" || name == "std::result::Result::<T, E>::unwrap_or_else") {
        selected.extend(internal_callees(tcx)?.into_iter().filter(|definition|roots.contains(&tcx.def_path_str(*definition))));
    }
    Ok(selected)
}

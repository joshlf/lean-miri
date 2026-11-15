//! Explicit finite generic MIR edges from selected closure source roots.
//! No monomorphic instance, trait selection, shim or compiler answer catalog.
use super::*;

/// Read ordinary/inherent FnDef declarations directly named by a closure's
/// generic MIR calls. Trait-associated declarations are intentionally excluded:
/// their source FnDef identity is not an implementation-selection answer.
pub(super) fn direct_callees_of(tcx: TyCtxt<'_>, owner: DefId) -> Result<Vec<DefId>> {
    if tcx.def_kind(owner) != rustc_hir::def::DefKind::Closure || !tcx.is_mir_available(owner) {
        return unsupported("closure callee source owner",owner);
    }
    let body = tcx.instance_mir(ty::InstanceKind::Item(owner));
    super::super::ensure_untainted_mir(body)?;
    if body.source.instance != ty::InstanceKind::Item(owner) || body.source.promoted.is_some()
        || body.coroutine.is_some() || !matches!(body.phase,mir::MirPhase::Runtime(_)) {
        return unsupported("closure callee source identity",body.source);
    }
    let mut result = Vec::new();
    for block in body.basic_blocks.iter() {
        if let mir::TerminatorKind::Call {func:mir::Operand::Constant(operand),..} = &block.terminator().kind {
            if let ty::FnDef(definition,_) = *operand.const_.ty().kind() {
                let eligible = match tcx.def_kind(definition) {
                    rustc_hir::def::DefKind::Fn => true,
                    rustc_hir::def::DefKind::AssocFn => matches!(tcx.def_kind(tcx.parent(definition)),
                        rustc_hir::def::DefKind::Impl {of_trait:false}),
                    _ => false,
                };
                if eligible { result.push(definition); }
            }
        }
    }
    result.sort_by_key(|definition|tcx.def_path_str(*definition));
    result.dedup();
    Ok(result)
}

fn owners(tcx: TyCtxt<'_>, roots: &[String]) -> Result<Vec<DefId>> {
    // External closure roots are selected by their actual source parent, never
    // by a hardcoded closure DefId/path. Local roots use their HIR identities.
    let mut result = closure_material::selected(tcx,roots)?;
    let items = tcx.hir_crate_items(());
    result.extend(items.definitions().chain(items.nested_bodies()).map(|d|d.to_def_id())
        .filter(|d|tcx.def_kind(*d)==rustc_hir::def::DefKind::Closure
            && roots.iter().any(|root|*root==tcx.def_path_str(*d))));
    result.sort_by_key(|definition|tcx.def_path_str(*definition));
    result.dedup();
    Ok(result)
}

/// Admit a body only when its definition occurs on an actual Call FnDef edge
/// from a supplied closure source root. This does not instantiate its arguments.
pub(super) fn is_source_callee(tcx: TyCtxt<'_>, roots: &[String], definition: DefId) -> Result<bool> {
    for owner in owners(tcx,roots)? {
        if direct_callees_of(tcx,owner)?.contains(&definition) { return Ok(true); }
    }
    Ok(false)
}

/// A callee template is captured only by an explicit root demand. Merely
/// exporting a closure does not eagerly export every dependency or suppress an
/// unsupported callee. External promoted metadata requires available ordinary
/// nonconst MIR; never replace an absent table with an empty one.
pub(super) fn selected(tcx: TyCtxt<'_>, roots: &[String]) -> Result<Vec<DefId>> {
    let mut result = Vec::new();
    for owner in owners(tcx,roots)? {
        for definition in direct_callees_of(tcx,owner)? {
            if roots.iter().any(|root|*root==tcx.def_path_str(definition)) {
                if tcx.is_foreign_item(definition) || tcx.is_const_fn(definition) || !tcx.is_mir_available(definition) {
                    return unsupported("selected closure direct callee MIR unavailable",definition);
                }
                result.push(definition);
            }
        }
    }
    result.sort_by_key(|definition|tcx.def_path_str(*definition));
    result.dedup();
    Ok(result)
}

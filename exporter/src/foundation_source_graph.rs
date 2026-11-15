//! Finite definition discovery from uninstantiated MIR syntax. Only requested
//! bodies are traversed; the compiler-selected start is a declaration seed.
//! Calls contribute their source FnDef, never an implementation selection.
use super::*;

pub(super) struct Graph {
    pub selected: Vec<DefId>,
    pub call_declarations: Vec<DefId>,
    declarations: Vec<DefId>,
}
impl Graph {
    pub(super) fn declaration(&self, tcx: TyCtxt<'_>, path: &str) -> Result<DefId> {
        let mut matches = self.declarations.iter().copied()
            .filter(|definition| tcx.def_path_str(*definition) == path);
        let first = matches.next().ok_or_else(|| format!("foundation: missing source definition {path:?}"))?;
        if matches.next().is_some() { return unsupported("ambiguous source definition",path); }
        Ok(first)
    }
    pub(super) fn contains_body(&self, definition: DefId) -> bool {
        self.selected.contains(&definition)
    }
}

fn syntax_edges(tcx: TyCtxt<'_>, owner: DefId) -> Result<(Vec<DefId>,Vec<DefId>)> {
    if !tcx.is_mir_available(owner) { return unsupported("selected source MIR unavailable",owner); }
    let body = tcx.instance_mir(ty::InstanceKind::Item(owner));
    super::super::ensure_untainted_mir(body)?;
    if body.source.instance != ty::InstanceKind::Item(owner) || body.source.promoted.is_some()
        || body.coroutine.is_some() || !matches!(body.phase,mir::MirPhase::Runtime(_)) {
        return unsupported("source graph body identity",body.source);
    }
    let mut result = Vec::new();
    let mut calls = Vec::new();
    for block in body.basic_blocks.iter() {
        if let mir::TerminatorKind::Call {func,..} = &block.terminator().kind {
            if let ty::FnDef(definition,_) = *func.ty(body,tcx).kind() {
                result.push(definition); calls.push(definition);
            }
        }
        for statement in &block.statements {
            if let mir::StatementKind::Assign(assignment) = &statement.kind {
                if let mir::Rvalue::Aggregate(kind,_) = &assignment.1 {
                    if let mir::AggregateKind::Closure(definition,_) = **kind { result.push(definition); }
                }
            }
        }
    }
    result.sort_by_key(|definition|(definition.krate.as_u32(),definition.index.as_u32()));
    result.dedup();
    calls.sort_by_key(|definition|(definition.krate.as_u32(),definition.index.as_u32()));
    calls.dedup();
    Ok((result,calls))
}

pub(super) fn discover(tcx: TyCtxt<'_>, roots: &[String], signatures: &[String]) -> Result<Graph> {
    let items = tcx.hir_crate_items(());
    let mut declarations = items.definitions().chain(items.nested_bodies()).map(|d|d.to_def_id())
        .collect::<Vec<_>>();
    declarations.sort_by_key(|definition|(definition.krate.as_u32(),definition.index.as_u32()));
    declarations.dedup();
    let mut selected = declarations.iter().copied().filter(|definition| {
        tcx.is_mir_available(*definition) && !super::super::is_required_trait_method(tcx,*definition)
            && (roots.is_empty() || roots.contains(&tcx.def_path_str(*definition)))
    }).collect::<Vec<_>>();
    let mut pending = selected.clone();
    // This is language-item semantics, independent of std names. A signature-
    // only demand may inspect this compiler-selected source owner without
    // claiming that its executable body has been supplied.
    if let Some(start) = tcx.lang_items().start_fn() {
        if !declarations.contains(&start) { declarations.push(start); }
        if roots.contains(&tcx.def_path_str(start)) {
            if !selected.contains(&start) { selected.push(start); pending.push(start); }
        } else if roots.iter().chain(signatures).any(|name| !declarations.iter().any(|d|tcx.def_path_str(*d)==*name)) {
            pending.push(start);
        }
    }
    let mut visited = Vec::new();
    let mut call_declarations = Vec::new();
    while let Some(owner) = pending.pop() {
        if visited.contains(&owner) { continue; }
        visited.push(owner);
        let (edges,calls) = syntax_edges(tcx,owner)?;
        if selected.contains(&owner) { call_declarations.extend(calls); }
        for definition in edges {
            if !declarations.contains(&definition) { declarations.push(definition); }
            if roots.contains(&tcx.def_path_str(definition)) && !selected.contains(&definition) {
                if !matches!(tcx.def_kind(definition), rustc_hir::def::DefKind::Fn
                    | rustc_hir::def::DefKind::AssocFn | rustc_hir::def::DefKind::Closure) {
                    return unsupported("requested source body definition kind",definition);
                }
                selected.push(definition);
                pending.push(definition);
            }
        }
    }
    selected.sort_by_key(|definition|tcx.def_path_str(*definition));
    selected.dedup();
    for root in roots {
        if !selected.iter().any(|definition|tcx.def_path_str(*definition)==*root) {
            return Err(format!("foundation: missing MIR root {root:?}"));
        }
    }
    call_declarations.sort_by_key(|definition|(definition.krate.as_u32(),definition.index.as_u32()));
    call_declarations.dedup();
    Ok(Graph {selected,declarations,call_declarations})
}

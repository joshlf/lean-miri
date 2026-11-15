//! Source facts only: no layout, ABI or compiler query answers.
use rustc_middle::{mir, ty::TyCtxt};
use rustc_span::Pos;
use serde_json::{json, Value};

fn span(tcx: TyCtxt<'_>, value: rustc_span::Span) -> Value {
    let map = tcx.sess.source_map();
    let start = map.lookup_char_pos(value.lo());
    let end = map.lookup_char_pos(value.hi());
    json!({"is_dummy":value.is_dummy(),"lo":value.lo().0,"hi":value.hi().0,
        "ctxt":format!("{:?}",value.ctxt()),"file":format!("{:?}",start.file.name),
        "start":{"line":start.line,"column":start.col.to_usize()},
        "end":{"line":end.line,"column":end.col.to_usize()}})
}
fn info(tcx: TyCtxt<'_>, value: mir::SourceInfo) -> Value {
    json!({"span":span(tcx,value.span),"scope":value.scope.as_u32()})
}
pub(super) fn capture(tcx: TyCtxt<'_>, body: &mir::Body<'_>) -> Value {
    // Storage markers remain executable MIR. Whether a local is always live
    // can be derived from their absence, as in pinned interpret/stack.rs.
    json!({"span":span(tcx,body.span),
        "definition_span":span(tcx,tcx.def_span(body.source.def_id())),
        "phase":crate::mir_phase_json(body.phase),
        "injection_phase":body.injection_phase.map(crate::mir_phase_json),
        "locals":body.local_decls.iter().map(|l|json!({"mutable":l.mutability.is_mut(),
            "source_info":info(tcx,l.source_info)})).collect::<Vec<_>>(),
        "scopes":body.source_scopes.iter().map(|s|json!({"span":span(tcx,s.span),
            "parent":s.parent_scope.map(|p|p.as_u32()),
            "inlined_parent":s.inlined_parent_scope.map(|p|p.as_u32())})).collect::<Vec<_>>(),
        "blocks":body.basic_blocks.iter().map(|b|json!({
            "statements":b.statements.iter().map(|s|info(tcx,s.source_info)).collect::<Vec<_>>(),
            "terminator":info(tcx,b.terminator().source_info)})).collect::<Vec<_>>()})
}

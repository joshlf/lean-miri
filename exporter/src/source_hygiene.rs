//! Finite syntax-context declarations used by the source debuginfo walk.
use super::*;

#[derive(serde::Serialize)]
pub(super) struct SyntaxContext {
    pub outer_expansion: Option<u64>,
}
#[derive(serde::Serialize)]
pub(super) struct Expansion {
    pub call_site: u64,
    pub collapse_debuginfo: bool,
}

pub(super) fn context<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    ctxt: rustc_span::SyntaxContext,
) -> u64 {
    if !ctxt.is_root() {
        self::context(context, tcx, rustc_span::SyntaxContext::root());
    }
    let (id, fresh) = context.syntax_contexts.reserve(ctxt);
    if fresh {
        let outer_expansion = if ctxt.is_root() {
            None
        } else {
            let outer = ctxt.outer_expn();
            let (expansion_id, fresh) = context.expansions.reserve(outer);
            if fresh {
                let call_site = outer.expn_data().call_site;
                assert_ne!(ctxt, call_site.ctxt(), "rustc expansion call site has its own syntax context");
                // The declaration field is private in the pinned rustc API.
                // Stopping at the immediate call-site context exposes exactly
                // this expansion's flag, independently of any function body.
                let probe = call_site.with_ctxt(ctxt);
                let collapsed = rustc_span::hygiene::walk_chain_collapsed(probe, call_site);
                let collapse_debuginfo = if collapsed == call_site {
                    true
                } else if collapsed == probe {
                    false
                } else {
                    panic!("one-step rustc debuginfo walk returned neither input nor call site");
                };
                let call_site = span_json(context, tcx, call_site);
                context.expansions.define(expansion_id, Expansion { call_site, collapse_debuginfo });
            }
            Some(expansion_id as u64)
        };
        context.syntax_contexts.define(id, SyntaxContext { outer_expansion });
    }
    id as u64
}

#[derive(serde::Serialize)]
pub(super) struct WalkOracle {
    body_span: u64,
    span: u64,
    collapsed_span: u64,
    byte_position: u32,
    line: usize,
    zero_based_char_column: usize,
    filename: String,
}

pub(super) fn oracle(tcx: TyCtxt<'_>, context: &ExportContext<'_>) -> Result<Vec<WalkOracle>, String> {
    let mut rows = Vec::new();
    let mut seen = HashSet::new();
    let bodies = context.bodies.iter().map(|(_, id)| {
        context.bodies.definition(*id).ok_or("backtrace oracle body is unfinished")
    }).collect::<Result<Vec<_>, _>>()?;
    for body in bodies.into_iter().chain(context.coroutine_coverage.auxiliary_bodies.iter().map(|row| &row.body)) {
        let source_span = |source: &shared_json::Shared<pool_body::SourceInfo>| {
            match source {
                shared_json::Shared::Value(info) => Ok(info.span),
                _ => Err("backtrace oracle received an already frozen body"),
            }
        };
        let mut spans = vec![body.span, body.preamble_def_span];
        for local in &body.locals { spans.push(source_span(&local.source_info)?); }
        for block in &body.basic_blocks {
            for statement in &block.statements { spans.push(source_span(&statement.source_info)?); }
            if let Some(terminator) = &block.terminator { spans.push(source_span(&terminator.source_info)?); }
        }
        let body_span = *context.spans.key(body.span as usize).ok_or("backtrace oracle body span is absent")?;
        for span_id in spans {
            if !seen.insert((body.span, span_id)) { continue; }
            let span = *context.spans.key(span_id as usize).ok_or("backtrace oracle input span is absent")?;
            let collapsed = rustc_span::hygiene::walk_chain_collapsed(span, body_span);
            let collapsed_id = *context.spans.get(&collapsed)
                .ok_or("backtrace oracle result lies outside the call-site span closure")?;
            let position = tcx.sess.source_map().lookup_char_pos(collapsed.lo());
            rows.push(WalkOracle {
                body_span: body.span,
                span: span_id,
                collapsed_span: collapsed_id,
                byte_position: collapsed.lo().0,
                line: position.line,
                zero_based_char_column: position.col.0,
                filename: position.file.name.prefer_remapped_unconditionally().to_string(),
            });
        }
    }
    rows.sort_by_key(|row| (row.body_span, row.span));
    Ok(rows)
}

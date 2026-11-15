//! Finite source for helpers.rs::iter_exported_symbols/lookup_link_section.
//! No static initializer, Instance::mono, allocation or symbol winner is queried.
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_middle::{middle::{codegen_fn_attrs::CodegenFnAttrFlags as F,
    dependency_format::Linkage, exported_symbols::ExportedSymbol}, ty::TyCtxt};
use serde_json::{json, Value};

fn item(tcx: TyCtxt<'_>, definition: DefId) -> Value {
    let attrs = tcx.codegen_fn_attrs(definition);
    let span = tcx.def_span(definition);
    json!({"crate_index":definition.krate.as_u32(),"definition_index":definition.index.as_u32(),
        "definition_kind":format!("{:?}",tcx.def_kind(definition)),
        "used_compiler":attrs.flags.contains(F::USED_COMPILER),
        "used_linker":attrs.flags.contains(F::USED_LINKER),
        "extern_indicator":attrs.contains_extern_indicator(),
        "link_section":attrs.link_section.map(|s|s.as_str().to_owned()),
        "source_span_key":{"lo":span.lo().0,"hi":span.hi().0,
            "ctxt":format!("{:?}",span.ctxt()),
            "parent_local_definition":span.parent().map(|d|d.local_def_index.as_u32())}})
}

pub(super) fn export(tcx: TyCtxt<'_>) -> Value {
    let locals = tcx.hir_crate_items(()).definitions().filter(|d|
        tcx.def_kind(d.to_def_id()).has_codegen_attrs() && !tcx.is_foreign_item(d.to_def_id()))
        .map(|d|item(tcx,d.to_def_id())).collect::<Vec<_>>();
    let formats = tcx.dependency_formats(());
    let dependencies = formats.get(&rustc_structures::CrateType::Executable).map(|format|
        format.iter_enumerated().map(|(krate, linkage)| {
            let exports = if krate == LOCAL_CRATE || *linkage == Linkage::NotLinked { vec![] }
                else { tcx.exported_non_generic_symbols(krate).iter().map(|(symbol,info)|match symbol {
                    ExportedSymbol::NonGeneric(definition) => {
                        let foreign = tcx.is_foreign_item(*definition);
                        json!({"kind":"non_generic","used":info.used,"is_foreign":foreign,
                            "item":if foreign {Value::Null} else {item(tcx,*definition)}})
                    },
                    _ => json!({"kind":"other"}),
                }).collect::<Vec<_>>() };
            json!({"crate_index":krate.as_u32(),"linkage":format!("{linkage:?}"),"exports":exports})
        }).collect::<Vec<_>>());
    json!({"local_crate":LOCAL_CRATE.as_u32(),"local_items":locals,"executable_dependencies":dependencies})
}

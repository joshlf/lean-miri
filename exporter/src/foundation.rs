//! Finite source material, independent of the schema12 monomorphic query cache.
//!
//! This format deliberately has no runtime query answers or successful fallback
//! rows. Unsupported source forms abort export. A consumer must implement their
//! semantics from the material; this format is not executable schema12 input.
#[path = "foundation_signature_binder.rs"]
mod signature_binder_material;
#[path = "foundation_start_edge.rs"]
mod start_edge_material;
#[path = "foundation_promoted.rs"]
mod promoted_material;
#[path = "foundation_termination.rs"]
mod termination_material;
#[path = "foundation_auto_traits.rs"]
mod auto_trait_material;
#[path = "foundation_enum.rs"]
mod enum_material;
#[path = "foundation_generic_parameters.rs"]
mod generic_parameter_material;
#[path = "foundation_generic_environment.rs"]
mod generic_environment_material;
#[path = "foundation_projection_clauses.rs"]
mod projection_clause_material;
#[path = "foundation_patterns.rs"]
mod pattern_material;
#[path = "foundation_fn_vtable.rs"]
mod fn_vtable_material;
#[path = "foundation_closure.rs"]
mod closure_material;
#[path = "foundation_closure_callees.rs"]
mod closure_callee_material;
#[path = "foundation_allocation_identity.rs"]
mod allocation_identity_material;
#[path = "foundation_allocations.rs"]
mod allocation_material;
#[path = "foundation_const_def.rs"]
mod const_definition_material;
#[path = "foundation_const.rs"]
mod const_material;
#[path = "foundation_source.rs"]
mod source_material;
#[path = "foundation_foreign_symbols.rs"]
mod foreign_symbol_material;
#[path = "foundation_link_sections.rs"]
mod link_section_material;
#[path = "foundation_link_initializers.rs"]
mod link_initializer_material;

#[path = "foundation_dynamic.rs"]
mod dynamic_material;
#[path = "foundation_dyn_metadata.rs"]
mod dyn_metadata_material;
#[path = "foundation_function_headers.rs"]
mod function_header_material;
#[path = "foundation_named_type_source.rs"]
mod named_type_material;

use std::collections::HashMap;
use rustc_driver::{Callbacks, Compilation};
use rustc_middle::{mir, ty::{self, TyCtxt}};
use rustc_hir::def_id::DefId;
use serde_json::{Value, json};

type Result<T> = std::result::Result<T, String>;

pub(super) struct FoundationCallbacks {
    pub roots: Vec<String>,
    pub signature_roots: Vec<String>,
    pub rustc_version: String,
    pub rustc_args: Vec<String>,
    pub document: Option<Value>,
    pub error: Option<String>,
}
impl Callbacks for FoundationCallbacks {
    fn after_analysis<'tcx>(&mut self, _: &rustc_interface::interface::Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        match export(tcx, &self.roots, &self.signature_roots, &self.rustc_version, &self.rustc_args) {
            Ok(document) => self.document = Some(document),
            Err(error) => self.error = Some(error),
        }
        Compilation::Stop
    }
}

#[derive(Default)]
struct Material<'tcx> {
    types: Vec<Value>,
    type_ids: HashMap<ty::Ty<'tcx>, usize>,
    definitions: Vec<Value>,
    def_ids: HashMap<DefId, usize>,
    allocations: Vec<Value>,
    allocation_ids: HashMap<rustc_middle::mir::interpret::AllocId, usize>,
}
fn unsupported<T>(kind: &str, value: impl std::fmt::Debug) -> Result<T> {
    Err(format!("foundation: unsupported {kind}: {value:?}"))
}
impl<'tcx> Material<'tcx> {
    fn definition(&mut self, tcx: TyCtxt<'tcx>, def: DefId) -> usize {
        if let Some(id) = self.def_ids.get(&def) { return *id; }
        let id = self.definitions.len();
        self.def_ids.insert(def, id);
        self.definitions.push(json!({"definition_id":id,"crate_index":def.krate.as_u32(),"index":def.index.as_u32(),"path":tcx.def_path_str(def),"kind":match tcx.def_kind(def) {rustc_hir::def::DefKind::Fn=>"fn".to_string(),rustc_hir::def::DefKind::AssocFn=>"assoc_fn".to_string(),rustc_hir::def::DefKind::Const=>"const".to_string(),rustc_hir::def::DefKind::Closure=>"closure".to_string(),other=>format!("{other:?}")}}));
        id
    }
    fn constant(&mut self, tcx: TyCtxt<'tcx>, c: ty::Const<'tcx>) -> Result<Value> {
        Ok(match c.kind() {
            ty::ConstKind::Param(p) => json!({"kind":"param","index":p.index,"name":p.name.as_str()}),
            ty::ConstKind::Value(v) => {
                let leaf = v.valtree.try_to_leaf().ok_or("foundation: non-scalar type constant")?;
                json!({"kind":"value","type":self.ty(tcx,v.ty)?,"bits":leaf.to_bits(leaf.size()).to_string(),"size_bytes":leaf.size().bytes()})
            }
            other => return unsupported("type constant", other),
        })
    }
    fn args(&mut self, tcx: TyCtxt<'tcx>, args: ty::GenericArgsRef<'tcx>) -> Result<Vec<Value>> {
        args.iter().map(|arg| Ok(match arg.kind() {
            ty::GenericArgKind::Type(t) => json!({"kind":"type","type":self.ty(tcx,t)?}),
            ty::GenericArgKind::Const(c) => json!({"kind":"const","value":self.constant(tcx,c)?}),
            ty::GenericArgKind::Lifetime(r) => {
                // Region identities affect validity/proofs; never silently erase.
                if !matches!(r.kind(), ty::ReErased | ty::ReStatic) { return unsupported("region", r); }
                json!({"kind":"region","region":if matches!(r.kind(), ty::ReStatic) {"static"} else {"erased"}})
            }
        })).collect()
    }
    fn ty(&mut self, tcx: TyCtxt<'tcx>, t: ty::Ty<'tcx>) -> Result<usize> {
        if let Some(id) = self.type_ids.get(&t) { return Ok(*id); }
        let id = self.types.len();
        self.type_ids.insert(t,id);
        self.types.push(Value::Null); // Reserve before traversing recursive ADTs.
        let shape = match *t.kind() {
            ty::Bool => json!({"kind":"bool"}),
            ty::Char => json!({"kind":"char"}),
            ty::Int(i) => json!({"kind":"int","name":i.name_str()}),
            ty::Uint(i) => json!({"kind":"uint","name":i.name_str()}),
            ty::Float(i) => json!({"kind":"float","name":i.name_str()}),
            ty::Never => json!({"kind":"never"}),
            ty::Str => json!({"kind":"str"}),
            ty::Param(p) => json!({"kind":"param","index":p.index,"name":p.name.as_str()}),
            ty::Tuple(ts) => json!({"kind":"tuple","elements":ts.iter().map(|t|self.ty(tcx,t)).collect::<Result<Vec<_>>>()?}),
            ty::Array(t,c) => json!({"kind":"array","element":self.ty(tcx,t)?,"length":self.constant(tcx,c)?}),
            ty::Slice(t) => json!({"kind":"slice","element":self.ty(tcx,t)?}),
            ty::RawPtr(t,m) => json!({"kind":"raw_pointer","pointee":self.ty(tcx,t)?,"mutable":m.is_mut()}),
            ty::Ref(r,t,m) => {
                json!({"kind":"reference","pointee":self.ty(tcx,t)?,"mutable":m.is_mut(),"region":self.signature_region(tcx,r)?})
            }
            ty::FnPtr(signature, header) => {
                let signature = signature.with(header);
                if !signature.bound_vars().is_empty() {
                    return unsupported("bound function-pointer signature", signature);
                }
                let signature = signature.skip_binder();
                json!({"kind":"function_pointer","signature":{
                    "bound_variables":[],
                    "inputs":signature.inputs().iter().map(|t|self.ty(tcx,*t)).collect::<Result<Vec<_>>>()?,
                    "output":self.ty(tcx,signature.output())?,
                    "safety":match signature.safety() {rustc_hir::Safety::Safe=>"safe",rustc_hir::Safety::Unsafe=>"unsafe"},
                    "abi":super::extern_abi_json(signature.abi()),
                    "c_variadic":signature.c_variadic(),
                }})
            },
            ty::Dynamic(predicates,region) => self.dynamic_type(tcx,predicates,region)?,
            ty::Pat(base,pattern) => self.pattern_type(tcx,base,pattern)?,
            ty::Closure(d,a) => self.closure_type(tcx,d,a)?,
            ty::FnDef(d,a) => {
                if !a.bound_vars().is_empty() { return unsupported("bound function arguments", a); }
                json!({"kind":"function_definition","definition":self.definition(tcx,d),"arguments":self.args(tcx,a.skip_binder())?})
            },
            // Field templates belong to the definition, not every substitution.
            ty::Adt(d,a) => {
                if d.is_enum() { self.enum_definition(tcx,d)?; }
                let definition = self.definition(tcx,d.did());
                if self.definitions[definition].get("adt").is_none() {
                    self.definitions[definition]["adt"] = json!({"pending":true});
                    let identity = ty::GenericArgs::identity_for_item(tcx,d.did());
                    let environment = self.environment(tcx,d.did())?;
                    let variants = d.variants().iter().map(|v| Ok(json!({"name":v.name.as_str(),"fields":v.fields.iter().map(|f|Ok(json!({"name":f.name.as_str(),"type":self.ty(tcx,f.ty(tcx,identity).skip_normalization())?}))).collect::<Result<Vec<_>>>()?}))).collect::<Result<Vec<_>>>()?;
                    self.definitions[definition]["adt"] = json!({"kind":match d.adt_kind(){ty::AdtKind::Struct=>"struct",ty::AdtKind::Enum=>"enum",ty::AdtKind::Union=>"union"},"environment":environment,"representation":super::repr_options_json(&d.repr()),"variants":variants});
                }
                json!({"kind":"adt","definition":definition,"arguments":self.args(tcx,a)?})
            }
            other => return unsupported("type",other),
        };
        self.types[id] = json!({"type_id":id,"shape":shape});
        Ok(id)
    }
    fn place(&mut self, tcx: TyCtxt<'tcx>, p: mir::Place<'tcx>) -> Result<Value> {
        let projections = p.projection.iter().map(|p| Ok(match p {
            mir::ProjectionElem::Deref => json!({"kind":"deref"}),
            mir::ProjectionElem::Field(f,t) => json!({"kind":"field","index":f.as_u32(),"type":self.ty(tcx,t)?}),
            mir::ProjectionElem::Index(i) => json!({"kind":"index","local":i.as_u32()}),
            other => return unsupported("projection",other),
        })).collect::<Result<Vec<_>>>()?;
        Ok(json!({"local":p.local.as_u32(),"projection":projections}))
    }
    fn operand(&mut self, tcx: TyCtxt<'tcx>, o: &mir::Operand<'tcx>) -> Result<Value> {
        Ok(match o {
            mir::Operand::Copy(p) => json!({"kind":"copy","place":self.place(tcx,*p)?}),
            mir::Operand::Move(p) => json!({"kind":"move","place":self.place(tcx,*p)?}),
            mir::Operand::Constant(c) => {
                let value = match c.const_ {
                    mir::Const::Unevaluated(value,_) => self.constant_definition(tcx,value)?,
                    mir::Const::Ty(_,c) => self.constant(tcx,c)?,
                    mir::Const::Val(mir::ConstValue::ZeroSized,_) => json!({"kind":"zero_sized"}),
                    mir::Const::Val(mir::ConstValue::Scalar(s),_) => {
                        match s.try_to_scalar_int() {
                            Ok(s) => json!({"kind":"scalar","bits":s.to_bits(s.size()).to_string(),"size_bytes":s.size().bytes()}),
                            Err(_) => self.allocation_constant(tcx,mir::ConstValue::Scalar(s))?,
                        }
                    }
                    mir::Const::Val(value @ (mir::ConstValue::Slice {..} | mir::ConstValue::Indirect {..}),_) => self.allocation_constant(tcx,value)?,
                    other => return unsupported("MIR constant",other),
                };
                json!({"kind":"constant","type":self.ty(tcx,c.const_.ty())?,"value":value,"source_span_key":{"lo":c.span.lo().0,"hi":c.span.hi().0,"ctxt":format!("{:?}",c.span.ctxt()),"parent_local_definition":c.span.parent().map(|d|d.local_def_index.as_u32())},"user_type":c.user_ty.map(|i|i.as_u32())})
            }
            other => return unsupported("operand",other),
        })
    }
    fn rvalue(&mut self, tcx: TyCtxt<'tcx>, r: &mir::Rvalue<'tcx>) -> Result<Value> {
        Ok(match r {
            mir::Rvalue::Use(o,retag) => json!({"kind":"use","operand":self.operand(tcx,o)?,"retag":retag.yes()}),
            mir::Rvalue::Ref(region,mir::BorrowKind::Shared,place) => {
                if !matches!(region.kind(),ty::ReErased|ty::ReStatic) { return unsupported("MIR borrow region",region); }
                json!({"kind":"ref","region":if matches!(region.kind(),ty::ReStatic){"static"}else{"erased"},"borrow_kind":"shared","place":self.place(tcx,*place)?})
            },
            mir::Rvalue::Aggregate(kind,operands) => match &**kind {
                mir::AggregateKind::Closure(def,args) => json!({"kind":"aggregate_closure","definition":self.definition(tcx,*def),"arguments":self.args(tcx,args)?,"operands":operands.iter().map(|o|self.operand(tcx,o)).collect::<Result<Vec<_>>>()?}),
                mir::AggregateKind::Tuple => json!({"kind":"aggregate_tuple","operands":operands.iter().map(|o|self.operand(tcx,o)).collect::<Result<Vec<_>>>()?}),
                other => return unsupported("aggregate rvalue",other),
            },
            mir::Rvalue::Cast(mir::CastKind::PointerCoercion(ty::adjustment::PointerCoercion::Unsize,source),operand,target) =>
                json!({"kind":"cast_unsize","source":match source {mir::CoercionSource::AsCast=>"as_cast",mir::CoercionSource::Implicit=>"implicit"},"operand":self.operand(tcx,operand)?,"target":self.ty(tcx,*target)?}),
            mir::Rvalue::BinaryOp(op,p) => json!({"kind":"binary","operator":super::binop_name(*op),"left":self.operand(tcx,&p.0)?,"right":self.operand(tcx,&p.1)?}),
            mir::Rvalue::UnaryOp(op,o) => json!({"kind":"unary","operator":super::unop_name(*op),"operand":self.operand(tcx,o)?}),
            mir::Rvalue::Repeat(o,n) => json!({"kind":"repeat","operand":self.operand(tcx,o)?,"length":self.constant(tcx,*n)?}),
            mir::Rvalue::Discriminant(p) => json!({"kind":"discriminant","place":self.place(tcx,*p)?}),
            other => return unsupported("rvalue",other),
        })
    }
    fn environment(&mut self, tcx: TyCtxt<'tcx>, def: DefId) -> Result<Value> {
        self.generic_environment(tcx,def)
    }
    fn signature(&mut self, tcx: TyCtxt<'tcx>, def: DefId) -> Result<Value> {
        // Source FnSig is finite generic material, not a normalized FnAbi answer.
        // Pinned rustc_ty_utils::abi::FnAbiDesc performs substitution, region
        // erasure and normalization later, when a concrete instance is demanded.
        let signature = tcx.fn_sig(def).instantiate_identity().skip_normalization();
        let bound_variables = self.signature_binders(tcx,signature.bound_vars())?;
        let signature = signature.skip_binder();
        Ok(json!({
            "bound_variables":bound_variables,
            "inputs":signature.inputs().iter().map(|t|self.ty(tcx,*t)).collect::<Result<Vec<_>>>()?,
            "output":self.ty(tcx,signature.output())?,
            "safety":match signature.safety() {rustc_hir::Safety::Safe=>"safe",rustc_hir::Safety::Unsafe=>"unsafe"},
            "abi":super::extern_abi_json(signature.abi()),
            "c_variadic":signature.c_variadic(),
        }))
    }
    fn body(&mut self, tcx: TyCtxt<'tcx>, def: DefId, roots: &[String]) -> Result<Value> {
        let b = tcx.instance_mir(ty::InstanceKind::Item(def));
        super::ensure_untainted_mir(b)?;
        // Pinned queries.rs: retain the complete promoted table, including
        // unused promoteds. metadata/encoder.rs::encode_mir records this table
        // alongside available optimized MIR for ordinary non-const functions.
        // Permit only the explicitly selected actual external start Fn here;
        // do not infer an empty table from a lack of body references.
        let external_start = !def.is_local()
            && tcx.lang_items().start_fn() == Some(def)
            && matches!(tcx.def_kind(def), rustc_hir::def::DefKind::Fn)
            && !tcx.is_const_fn(def)
            && tcx.is_mir_available(def);
        // Other external owners require a checked source Call FnDef edge.
        let external_start_internal = !def.is_local()
            && tcx.def_path_str(def) == "std::rt::lang_start_internal"
            && start_edge_material::start_internal(tcx)? == Some(def);
        let external_internal_callee = !def.is_local()
            && start_edge_material::internal_callees(tcx)?.contains(&def);
        let external_closure_callee = !def.is_local()
            && closure_callee_material::is_source_callee(tcx,roots,def)?
            && !tcx.is_const_fn(def) && tcx.is_mir_available(def);
        if !super::has_local_hir_body(tcx, def) && !external_start && !external_start_internal
            && !external_internal_callee && !external_closure_callee && !termination_material::unit_methods(tcx).contains(&def) {
            return unsupported("non-local promoted table owner", def);
        }
        let promoted_count = tcx.promoted_mir(def).len();
        if promoted_count != 0 { return unsupported("promoted bodies", promoted_count); }
        // Pinned stack.rs evaluates every required constant on frame entry,
        // including constants in unreachable blocks. Preserve the full list.
        let required_consts = self.required_constants(tcx, b)?;
        // The restricted evaluator initializes ordinary argument locals directly;
        // coroutine/resume frames, rust-call spreading, inlined frames and
        // compiler-generated/promoted source identities require more machinery.
        if b.coroutine.is_some() { return unsupported("coroutine body", def); }
        if b.spread_arg.is_some() { return unsupported("spread argument", def); }
        if !matches!(b.phase, mir::MirPhase::Runtime(_)) {
            return unsupported("non-runtime MIR phase", b.phase);
        }
        if b.source.promoted.is_some() || b.source.instance != ty::InstanceKind::Item(def) {
            return unsupported("non-item MIR source", b.source);
        }
        if b.source_scopes.iter().any(|scope| scope.inlined.is_some() || scope.inlined_parent_scope.is_some()) {
            return unsupported("inlined frame metadata", def);
        }
        if !matches!(tcx.def_kind(def), rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn) {
            return unsupported("non-function entry", def);
        }
        if !tcx.codegen_fn_attrs(def).target_features.is_empty() {
            return unsupported("function target features", def);
        }
        let environment = self.environment(tcx,def)?;
        let signature = self.signature(tcx,def)?;
        // Inputs to pinned ty::layout::fn_can_unwind; do not cache its answer.
        let function_attributes = json!({
            "never_unwind":tcx.codegen_fn_attrs(def).flags.contains(rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags::NEVER_UNWIND),
            "track_caller":ty::InstanceKind::Item(def).requires_caller_location(tcx),
            "is_foreign":tcx.is_foreign_item(def),
            "is_drop_glue":tcx.is_lang_item(def,rustc_attr_ir::LangItem::DropGlue),
        });
        let source_metadata = source_material::capture(tcx, b);
        let locals = b.local_decls.iter().map(|l|self.ty(tcx,l.ty)).collect::<Result<Vec<_>>>()?;
        let blocks = b.basic_blocks.iter().map(|bb| {
            let statements = bb.statements.iter().map(|s| Ok(match &s.kind {
                mir::StatementKind::Assign(p) => json!({"kind":"assign","place":self.place(tcx,p.0)?,"value":self.rvalue(tcx,&p.1)?}),
                mir::StatementKind::StorageLive(l) => json!({"kind":"storage_live","local":l.as_u32()}),
                mir::StatementKind::StorageDead(l) => json!({"kind":"storage_dead","local":l.as_u32()}),
                mir::StatementKind::Nop => json!({"kind":"nop"}),
                other => return unsupported("statement",other),
            })).collect::<Result<Vec<_>>>()?;
            let terminator = match &bb.terminator().kind {
                mir::TerminatorKind::Return => json!({"kind":"return"}),
                mir::TerminatorKind::UnwindResume => json!({"kind":"unwind_resume"}),
                mir::TerminatorKind::UnwindTerminate(reason) => json!({"kind":"unwind_terminate","reason":super::unwind_terminate_reason_json(*reason)}),
                mir::TerminatorKind::Goto {target,..} => json!({"kind":"goto","target":target.as_u32()}),
                mir::TerminatorKind::Unreachable => json!({"kind":"unreachable"}),
                mir::TerminatorKind::Drop {place,target,unwind,replace,drop} => json!({
                    "kind":"drop","place":self.place(tcx,*place)?,"target":target.as_u32(),
                    "unwind":super::unwind_json(*unwind),"replace":replace,
                    "async_drop":drop.map(|block|block.as_u32())}),
                mir::TerminatorKind::SwitchInt {discr,targets} => json!({"kind":"switch_int","operand":self.operand(tcx,discr)?,"targets":targets.iter().map(|(v,b)|json!({"value":v.to_string(),"target":b.as_u32()})).collect::<Vec<_>>(),"otherwise":targets.otherwise().as_u32()}),
                mir::TerminatorKind::Call {func,args,destination,target,unwind,call_source,..} => json!({
                    "kind":"call",
                    "function":self.operand(tcx,func)?,
                    "arguments":args.iter().map(|arg|self.operand(tcx,&arg.node)).collect::<Result<Vec<_>>>()?,
                    "destination":self.place(tcx,*destination)?,
                    "target":target.map(|block|block.as_u32()),
                    "unwind":super::unwind_json(*unwind),
                    "call_source":super::call_source_name(*call_source)
                }),
                other => return unsupported("terminator",other),
            };
            Ok(json!({"cleanup":bb.is_cleanup,"statements":statements,"terminator":terminator}))
        }).collect::<Result<Vec<_>>>()?;
        Ok(json!({"definition":self.definition(tcx,def),"argument_count":b.arg_count,"promoted_count":promoted_count,"environment":environment,"signature":signature,"function_attributes":function_attributes,"runtime_source":super::foundation_runtime_instances::item(tcx,def),"required_consts":required_consts,"source_metadata":source_metadata,"locals":locals,"blocks":blocks}))
    }
}
fn export(tcx: TyCtxt<'_>, roots: &[String], signature_roots: &[String], rustc_version: &str, rustc_args: &[String]) -> Result<Value> {
    let mut m = Material::default();
    let items = tcx.hir_crate_items(());
    let mut selected = items.definitions().chain(items.nested_bodies()).map(|d|d.to_def_id()).filter(|d| tcx.is_mir_available(*d) && !super::is_required_trait_method(tcx,*d)).collect::<Vec<_>>();
    // An explicitly named actual start language item can reside in an encoded
    // dependency. Select only that finite generic template; do not enumerate
    // monomorphic instances, callees or compiler query-answer closure.
    if let Some(start) = tcx.lang_items().start_fn() {
        if roots.iter().any(|root| *root == tcx.def_path_str(start)) {
            if !tcx.is_mir_available(start) { return unsupported("selected start MIR unavailable", start); }
            selected.push(start);
        }
    }
    selected.extend(start_edge_material::selected(tcx,roots)?);
    selected.extend(closure_material::selected(tcx,roots)?);
    selected.extend(closure_callee_material::selected(tcx,roots)?);
    selected.sort_by_key(|d|tcx.def_path_str(*d));
    selected.dedup();
    for root in roots {
        if !selected.iter().any(|d|tcx.def_path_str(*d) == *root) { return Err(format!("foundation: missing MIR root {root:?}")); }
    }
    if !roots.is_empty() { selected.retain(|d|roots.contains(&tcx.def_path_str(*d))); }
    let mut bodies = Vec::new();
    let mut closure_templates = Vec::new();
    for def in selected {
        if tcx.def_kind(def) == rustc_hir::def::DefKind::Closure {
            closure_templates.push(m.closure_template(tcx,def)?);
        } else {
            bodies.push(m.body(tcx,def,roots)?);
        }
    }
    let startup_material = super::foundation_startup::capture(tcx, |def|m.definition(tcx,def))?;
    // Finite source selection/configuration only. No lang_start instance or
    // function allocation is resolved or enumerated here.
    let compiler_entry = tcx.entry_fn(()).map(|(definition, kind)| match kind {
        rustc_session::config::EntryFnType::Main { sigpipe } => json!({
            "definition":m.definition(tcx,definition),"kind":"rustc_main","sigpipe":sigpipe}),
    });
    let start_lang_item = tcx.lang_items().start_fn().map(|d|m.definition(tcx,d));
    if tcx.dcx().has_errors().is_some() { return Err("foundation: compiler errors during export".into()); }
    let mut session = super::foundation_session::export(tcx);
    session["root_span"] = source_material::root_span(tcx);
    let source_function_signatures = function_header_material::capture_for_roots(tcx,&mut m,signature_roots,roots)?;
    let has_dynamic = m.types.iter().any(|row| row["shape"]["kind"] == "dynamic");
    let has_fn_pointer = m.types.iter().any(|row| row["shape"]["kind"] == "function_pointer");
    let has_callable_declaration = [tcx.lang_items().fn_trait(),tcx.lang_items().fn_mut_trait(),tcx.lang_items().fn_once_trait()]
        .into_iter().flatten().any(|def| m.def_ids.contains_key(&def));
    let dyn_metadata_source = if has_dynamic { dyn_metadata_material::capture(tcx,&mut m)? } else { Value::Null };
    let fn_vtable_source = if has_dynamic || !closure_templates.is_empty() || has_fn_pointer || has_callable_declaration {
        m.fn_vtable_source(tcx)?
    } else { Value::Null };
    let closure_auto_source = m.closure_auto_source(tcx)?;
    let mut link_sections = link_section_material::export(tcx);
    m.attach_link_initializers(tcx,&mut link_sections)?;
    let termination_source = m.termination_source(tcx)?;
    for body in m.termination_templates(tcx,roots)? {
        if !bodies.iter().any(|existing|existing["definition"]==body["definition"]) {bodies.push(body);}
    }
    let named_type_source = if compiler_entry.is_some() { m.named_type_source(tcx)? } else { Value::Null };
    let producer = super::foundation_producer::capture(tcx, rustc_version, rustc_args)?;
    let frame_metadata = super::foundation_runtime_instances::frames(tcx);
    let foreign_symbol_material = foreign_symbol_material::export(tcx)?;
    let runtime_data_layout = super::foundation_target::export(tcx)?;
    let allocation_identity_source = m.allocation_identity_source(tcx)?;
    Ok(json!({
        "allocation_identity_source":allocation_identity_source,
        "closure_auto_source":closure_auto_source,
        "fn_vtable_source":fn_vtable_source,"schema":"lean-miri-foundation","schema_version":1,
        "rustc_commit":super::EXPECTED_RUSTC_COMMIT,
        "producer":producer,
        "frame_metadata":frame_metadata,
        "startup_material":startup_material,
        "link_section_material":link_sections,"termination_source":termination_source,
        "named_type_source":named_type_source,
        "foreign_symbol_material":foreign_symbol_material,
        "entry_selection":{"compiler_entry":compiler_entry,"start_lang_item":start_lang_item},
        "session":session,
        "compilation":{"panic_strategy":if tcx.sess.panic_strategy().unwinds(){"unwind"}else{"abort"},"panic_in_drop":if tcx.sess.opts.unstable_opts.panic_in_drop.unwinds(){"unwind"}else{"abort"},"opt_level":format!("{:?}",tcx.sess.opts.optimize)},
        "target":{"runtime_data_layout":runtime_data_layout,"triple":tcx.sess.opts.target_triple.to_string(),"architecture":tcx.sess.target.arch.to_string(),"data_layout":tcx.sess.target.data_layout.as_ref(),"pointer_size_bits":tcx.data_layout.pointer_size().bits(),"endian":match tcx.data_layout.endian {rustc_abi::Endian::Little=>"little",rustc_abi::Endian::Big=>"big"}},
        "definitions":m.definitions,"types":m.types,"bodies":bodies,
        "closure_templates":closure_templates,
        "source_allocations":m.allocations,
        "dyn_metadata_source":dyn_metadata_source,
        "source_function_signatures":source_function_signatures,
        "source_signature_roots":signature_roots
    }))
}

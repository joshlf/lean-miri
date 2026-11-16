use super::*;

#[derive(serde::Serialize)]
pub(super) struct Material {
    types: Vec<Type>,
    declarations: Vec<Declaration>,
    adt_declarations: Vec<AdtDeclaration>,
    associated_type_declarations: Vec<AssociatedTypeDeclaration>,
}

#[derive(serde::Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum Type {
    Parameter {
        index: u32,
    },
    Primitive {
        shape_kind: &'static str,
        integer_kind: Option<&'static str>,
        float_kind: Option<&'static str>,
    },
    Adt {
        definition: u64,
        arguments: Vec<Argument>,
    },
    Tuple {
        fields: Vec<u64>,
    },
    Array {
        element: u64,
        length: Argument,
    },
    Slice {
        element: u64,
    },
    Reference {
        pointee: u64,
        mutability: pool_type::Mutability,
    },
    RawPointer {
        pointee: u64,
        mutability: pool_type::Mutability,
    },
    FunctionDefinition {
        definition: u64,
        arguments: Vec<Argument>,
    },
    Closure {
        definition: u64,
        arguments: Vec<Argument>,
    },
    PatternType {
        base: u64,
        pattern: Pattern,
    },
    ProjectionAlias {
        definition: u64,
        arguments: Vec<Argument>,
    },
    Unsupported {
        reason: String,
        shape_kind: Option<&'static str>,
    },
}

#[derive(serde::Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum Pattern {
    Range { start: Argument, end: Argument },
    Or { patterns: Vec<Pattern> },
    NotNull,
}

#[derive(serde::Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum Argument {
    Type { expression: u64 },
    Constant { value: u64 },
    ConstantParameter { index: u32 },
    Lifetime,
    Unsupported { reason: String },
}

#[derive(serde::Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum Clause {
    Trait {
        definition: u64,
        arguments: Vec<Argument>,
    },
    RegionOutlives,
    TypeOutlives {
        r#type: u64,
    },
    Unsupported {
        reason: String,
    },
}

#[derive(serde::Serialize)]
struct Implementation {
    definition: u64,
    parameters: Vec<&'static str>,
    self_type: u64,
    arguments: Vec<Argument>,
    clauses: Vec<Clause>,
    polarity: &'static str,
    is_final: bool,
}

#[derive(serde::Serialize)]
struct Declaration {
    definition: u64,
    role: &'static str,
    is_auto: bool,
    parameters: Vec<&'static str>,
    super_clauses: Vec<Clause>,
    own_vtable_methods: Vec<u64>,
    super_traits: Vec<u64>,
    implementations: Vec<Implementation>,
}

#[derive(serde::Serialize)]
struct AdtDeclaration {
    definition: u64,
    parameters: Vec<&'static str>,
    is_struct: bool,
    tail_type: Option<u64>,
    clauses: Vec<Clause>,
}

#[derive(serde::Serialize)]
struct AssociatedTypeDeclaration {
    definition: u64,
    parameters: Vec<&'static str>,
    bounds: Vec<Clause>,
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
enum Head {
    Adt(rustc_hir::def_id::DefId),
    Function(rustc_hir::def_id::DefId),
    Closure(rustc_hir::def_id::DefId),
    Primitive(&'static str),
    Tuple(usize),
    Array,
    Slice,
    Reference,
    RawPointer,
    FunctionPointer,
    Dynamic,
    Foreign(rustc_hir::def_id::DefId),
    Coroutine,
    CoroutineClosure,
    UnsafeBinder,
    Pattern,
}

impl Head {
    fn of(input: ty::Ty<'_>) -> Option<Self> {
        Some(match *input.kind() {
            ty::Adt(definition, _) => Self::Adt(definition.did()),
            ty::FnDef(definition, _) => Self::Function(definition),
            ty::Closure(definition, _) => Self::Closure(definition),
            ty::Bool => Self::Primitive("bool"),
            ty::Char => Self::Primitive("char"),
            ty::Str => Self::Primitive("str"),
            ty::Never => Self::Primitive("never"),
            ty::Int(integer) => Self::Primitive(integer.name_str()),
            ty::Uint(integer) => Self::Primitive(integer.name_str()),
            ty::Float(float) => Self::Primitive(float.name_str()),
            ty::Tuple(fields) => Self::Tuple(fields.len()),
            ty::Array(..) => Self::Array,
            ty::Slice(..) => Self::Slice,
            ty::Ref(..) => Self::Reference,
            ty::RawPtr(..) => Self::RawPointer,
            ty::FnPtr(..) => Self::FunctionPointer,
            ty::Dynamic(..) => Self::Dynamic,
            ty::Foreign(definition) => Self::Foreign(definition),
            ty::Coroutine(..) => Self::Coroutine,
            ty::CoroutineClosure(..) => Self::CoroutineClosure,
            ty::UnsafeBinder(..) => Self::UnsafeBinder,
            ty::Pat(..) => Self::Pattern,
            _ => return None,
        })
    }
}

#[derive(Default)]
pub(super) struct State<'tcx> {
    types: Pool<ty::Ty<'tcx>, Type>,
    traits: OrderedSet<rustc_hir::def_id::DefId>,
    declarations: Vec<Declaration>,
    cursor: usize,
    adts: OrderedSet<rustc_hir::def_id::DefId>,
    adt_declarations: Vec<AdtDeclaration>,
    adt_cursor: usize,
    heads: HashSet<Head>,
    deferred_impls: Vec<(usize, rustc_hir::def_id::DefId)>,
    type_cursor: usize,
    associated: OrderedSet<rustc_hir::def_id::DefId>,
    associated_type_declarations: Vec<AssociatedTypeDeclaration>,
    associated_cursor: usize,
}

struct Collector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    context: &'a mut ExportContext<'tcx>,
    types: Pool<ty::Ty<'tcx>, Type>,
    traits: OrderedSet<rustc_hir::def_id::DefId>,
    adts: OrderedSet<rustc_hir::def_id::DefId>,
    heads: HashSet<Head>,
    associated: OrderedSet<rustc_hir::def_id::DefId>,
}

impl<'tcx> Collector<'_, 'tcx> {
    fn pattern(&mut self, input: ty::Pattern<'tcx>) -> Result<Pattern, String> {
        Ok(match *input.0 {
            ty::PatternKind::Range { start, end } => Pattern::Range {
                start: self.argument(start.into())?,
                end: self.argument(end.into())?,
            },
            ty::PatternKind::Or(patterns) => Pattern::Or {
                patterns: patterns
                    .iter()
                    .map(|pattern| self.pattern(pattern))
                    .collect::<Result<_, _>>()?,
            },
            ty::PatternKind::NotNull => Pattern::NotNull,
        })
    }

    fn argument(&mut self, input: ty::GenericArg<'tcx>) -> Result<Argument, String> {
        Ok(match input.kind() {
            ty::GenericArgKind::Type(input) => Argument::Type {
                expression: self.ty(input)?,
            },
            ty::GenericArgKind::Lifetime(_) => Argument::Lifetime,
            ty::GenericArgKind::Const(input) => match input.kind() {
                ty::ConstKind::Param(parameter) => Argument::ConstantParameter {
                    index: parameter.index,
                },
                ty::ConstKind::Value(_) => Argument::Constant {
                    value: const_type_json(self.context, self.tcx, input)?,
                },
                _ => Argument::Unsupported {
                    reason: format!("trait declaration constant {input:?}"),
                },
            },
        })
    }

    fn arguments(&mut self, input: ty::GenericArgsRef<'tcx>) -> Result<Vec<Argument>, String> {
        input
            .iter()
            .map(|argument| self.argument(argument))
            .collect()
    }

    fn ty(&mut self, input: ty::Ty<'tcx>) -> Result<u64, String> {
        if let Some(head) = Head::of(input) {
            self.heads.insert(head);
        }
        if let Some(id) = self.types.get(&input) {
            return Ok(*id);
        }
        let node = match *input.kind() {
            ty::Param(parameter) => Type::Parameter {
                index: parameter.index,
            },
            ty::Bool => Type::Primitive {
                shape_kind: "bool",
                integer_kind: None,
                float_kind: None,
            },
            ty::Char => Type::Primitive {
                shape_kind: "char",
                integer_kind: None,
                float_kind: None,
            },
            ty::Str => Type::Primitive {
                shape_kind: "str",
                integer_kind: None,
                float_kind: None,
            },
            ty::Never => Type::Primitive {
                shape_kind: "never",
                integer_kind: None,
                float_kind: None,
            },
            ty::Int(integer) => Type::Primitive {
                shape_kind: "int",
                integer_kind: Some(integer.name_str()),
                float_kind: None,
            },
            ty::Uint(integer) => Type::Primitive {
                shape_kind: "uint",
                integer_kind: Some(integer.name_str()),
                float_kind: None,
            },
            ty::Float(float) => Type::Primitive {
                shape_kind: "float",
                integer_kind: None,
                float_kind: Some(float.name_str()),
            },
            ty::Adt(definition, arguments) => {
                self.adts.insert(definition.did());
                Type::Adt {
                    definition: def_json(self.context, definition.did()),
                    arguments: self.arguments(arguments)?,
                }
            }
            ty::Tuple(fields) => Type::Tuple {
                fields: fields
                    .iter()
                    .map(|field| self.ty(field))
                    .collect::<Result<_, _>>()?,
            },
            ty::Array(element, length) => Type::Array {
                element: self.ty(element)?,
                length: self.argument(length.into())?,
            },
            ty::Slice(element) => Type::Slice {
                element: self.ty(element)?,
            },
            ty::Ref(_, pointee, mutability) => Type::Reference {
                pointee: self.ty(pointee)?,
                mutability: mutability_json(mutability),
            },
            ty::RawPtr(pointee, mutability) => Type::RawPointer {
                pointee: self.ty(pointee)?,
                mutability: mutability_json(mutability),
            },
            ty::FnDef(definition, arguments) => Type::FunctionDefinition {
                definition: def_json(self.context, definition),
                arguments: self.arguments(arguments.skip_binder())?,
            },
            ty::Closure(definition, arguments) => Type::Closure {
                definition: def_json(self.context, definition),
                arguments: self.arguments(arguments)?,
            },
            ty::Pat(base, pattern) => Type::PatternType {
                base: self.ty(base)?,
                pattern: self.pattern(pattern)?,
            },
            ty::Alias(
                _,
                ty::AliasTy {
                    kind: ty::AliasTyKind::Projection { def_id },
                    args,
                    ..
                },
            ) => {
                self.associated.insert(def_id);
                Type::ProjectionAlias {
                    definition: def_json(self.context, def_id),
                    arguments: self.arguments(args)?,
                }
            }
            _ => Type::Unsupported {
                reason: format!("trait declaration type {input:?}"),
                shape_kind: match input.kind() {
                    ty::FnPtr(..) => Some("function_pointer"),
                    ty::Dynamic(..) => Some("dynamic_trait_object"),
                    ty::Foreign(..) => Some("foreign"),
                    ty::Coroutine(..) => Some("coroutine"),
                    ty::CoroutineClosure(..) => Some("coroutine_closure"),
                    ty::UnsafeBinder(..) => Some("unsafe_binder"),
                    _ => None,
                },
            },
        };
        let (id, _) = self.types.reserve(input);
        self.types.define(id, node);
        Ok(id as u64)
    }

    fn clauses(&mut self, definition: rustc_hir::def_id::DefId) -> Result<Vec<Clause>, String> {
        // A trait's generated Self: Trait assumption is not a supertrait obligation.
        let clauses = if matches!(
            self.tcx.def_kind(definition),
            rustc_hir::def::DefKind::Trait
        ) {
            self.tcx.explicit_super_clauses_of(definition).skip_binder()
        } else {
            self.tcx.clauses_of(definition).clauses
        };
        clauses
            .iter()
            .map(|(clause, _)| self.clause(*clause))
            .collect()
    }

    fn clause(&mut self, clause: ty::Clause<'tcx>) -> Result<Clause, String> {
        let bound = clause.kind();
        if bound
            .bound_vars()
            .iter()
            .any(|variable| !matches!(variable, ty::BoundVariableKind::Region(_)))
        {
            return Ok(Clause::Unsupported {
                reason: format!("non-region bound variables: {clause:?}"),
            });
        }
        Ok(match bound.skip_binder() {
            ty::ClauseKind::Trait(predicate)
                if matches!(predicate.polarity, ty::ClausePolarity::Positive) =>
            {
                self.traits.insert(predicate.trait_ref.def_id);
                Clause::Trait {
                    definition: def_json(self.context, predicate.trait_ref.def_id),
                    arguments: self.arguments(predicate.trait_ref.args)?,
                }
            }
            ty::ClauseKind::RegionOutlives(_) => Clause::RegionOutlives,
            ty::ClauseKind::TypeOutlives(predicate) => Clause::TypeOutlives {
                r#type: self.ty(predicate.0)?,
            },
            _ => Clause::Unsupported {
                reason: format!("trait declaration clause {clause:?}"),
            },
        })
    }

    fn parameters(&self, definition: rustc_hir::def_id::DefId) -> Vec<&'static str> {
        ty::GenericArgs::identity_for_item(self.tcx, definition)
            .iter()
            .map(|argument| match argument.kind() {
                ty::GenericArgKind::Type(_) => "type",
                ty::GenericArgKind::Lifetime(_) => "lifetime",
                ty::GenericArgKind::Const(_) => "constant",
            })
            .collect()
    }
}

pub(super) fn discover<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    state: &mut State<'tcx>,
) -> Result<(), String> {
    let new_types = (state.type_cursor..context.type_ids.len())
        .map(|index| *context.type_ids.key(index).unwrap())
        .collect::<Vec<_>>();
    state.type_cursor = context.type_ids.len();
    let dynamic_types = new_types
        .iter()
        .filter_map(|input| match input.kind() {
            ty::Dynamic(predicates, _) => Some((
                *input,
                predicates
                    .principal()
                    .map(|principal| principal.skip_binder().def_id),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();
    for (input, principal) in &dynamic_types {
        if let Some(definition) = tcx.lang_items().get(rustc_attr_ir::LangItem::DynMetadata) {
            let metadata = tcx
                .type_of(definition)
                .instantiate(tcx, &[(*input).into()])
                .skip_norm_wip();
            type_json(context, tcx, metadata)?;
        }
        let mut count = TyCtxt::COMMON_VTABLE_ENTRIES.len() as u64;
        let mut pending = principal.iter().copied().collect::<Vec<_>>();
        let mut seen = HashSet::new();
        while let Some(definition) = pending.pop() {
            if !seen.insert(definition) {
                continue;
            }
            count += tcx.own_existential_vtable_entries(definition).len() as u64;
            for (clause, _) in tcx.explicit_super_clauses_of(definition).skip_binder() {
                if let ty::ClauseKind::Trait(predicate) = clause.kind().skip_binder() {
                    pending.push(predicate.trait_ref.def_id);
                }
            }
        }
        let vtable = ty::Ty::new_imm_ref(
            tcx,
            tcx.lifetimes.re_static,
            ty::Ty::new_array(tcx, tcx.types.usize, count),
        );
        type_json(context, tcx, vtable)?;
    }
    let concrete_adts = new_types
        .iter()
        .filter_map(|input| match input.kind() {
            ty::Adt(definition, _) => Some(definition.did()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let mut heads = std::mem::take(&mut state.heads);
    heads.extend(new_types.iter().filter_map(|input| Head::of(*input)));
    heads.extend([
        Head::Array,
        Head::Slice,
        Head::Reference,
        Head::RawPointer,
        Head::FunctionPointer,
    ]);
    let mut collector = Collector {
        tcx,
        context,
        types: std::mem::take(&mut state.types),
        traits: std::mem::take(&mut state.traits),
        adts: std::mem::take(&mut state.adts),
        heads,
        associated: std::mem::take(&mut state.associated),
    };
    collector.adts.extend(concrete_adts);
    for item in [
        rustc_attr_ir::LangItem::Freeze,
        rustc_attr_ir::LangItem::Unpin,
        rustc_attr_ir::LangItem::UnsafeUnpin,
    ] {
        if let Some(definition) = tcx.lang_items().get(item) {
            collector.traits.insert(definition);
        }
    }
    collector.traits.extend(
        dynamic_types
            .into_iter()
            .filter_map(|(_, principal)| principal),
    );
    let mut declarations = std::mem::take(&mut state.declarations);
    let mut adt_declarations = std::mem::take(&mut state.adt_declarations);
    let mut associated_type_declarations = std::mem::take(&mut state.associated_type_declarations);
    let mut associated_cursor = state.associated_cursor;
    let mut deferred_impls = std::mem::take(&mut state.deferred_impls);
    let mut cursor = state.cursor;
    let mut adt_cursor = state.adt_cursor;
    loop {
        let before_heads = collector.heads.len();
        while cursor < collector.traits.len() {
            let definition = *collector.traits.get_index(cursor).unwrap();
            let trait_index = cursor;
            cursor += 1;
            let mut impls = tcx.all_impls(definition).collect::<Vec<_>>();
            impls.sort_by_key(|definition| (definition.krate.as_u32(), definition.index.as_u32()));
            deferred_impls.extend(
                impls
                    .into_iter()
                    .map(|implementation| (trait_index, implementation)),
            );
            declarations.push(Declaration {
                definition: def_json(collector.context, definition),
                role: if tcx.is_lang_item(definition, rustc_attr_ir::LangItem::Freeze) {
                    "freeze"
                } else if tcx.is_lang_item(definition, rustc_attr_ir::LangItem::Unpin) {
                    "unpin"
                } else if tcx.is_lang_item(definition, rustc_attr_ir::LangItem::UnsafeUnpin) {
                    "unsafe_unpin"
                } else if tcx.is_lang_item(definition, rustc_attr_ir::LangItem::Sized) {
                    "sized"
                } else if tcx.is_lang_item(definition, rustc_attr_ir::LangItem::MetaSized) {
                    "meta_sized"
                } else {
                    "other"
                },
                is_auto: tcx.trait_is_auto(definition),
                parameters: collector.parameters(definition),
                super_clauses: collector.clauses(definition)?,
                own_vtable_methods: tcx
                    .own_existential_vtable_entries(definition)
                    .iter()
                    .map(|method| def_json(collector.context, *method))
                    .collect(),
                super_traits: tcx
                    .explicit_super_clauses_of(definition)
                    .skip_binder()
                    .iter()
                    .filter_map(|(clause, _)| {
                        if let ty::ClauseKind::Trait(predicate) = clause.kind().skip_binder() {
                            collector.traits.insert(predicate.trait_ref.def_id);
                            Some(def_json(collector.context, predicate.trait_ref.def_id))
                        } else {
                            None
                        }
                    })
                    .collect(),
                implementations: Vec::new(),
            });
        }
        for (trait_index, implementation) in std::mem::take(&mut deferred_impls) {
            let header = tcx.impl_trait_header(implementation);
            let reference = header.trait_ref.instantiate_identity().skip_norm_wip();
            if Head::of(reference.self_ty()).is_some_and(|head| !collector.heads.contains(&head)) {
                deferred_impls.push((trait_index, implementation));
                continue;
            }
            declarations[trait_index]
                .implementations
                .push(Implementation {
                    definition: def_json(collector.context, implementation),
                    parameters: collector.parameters(implementation),
                    self_type: collector.ty(reference.self_ty())?,
                    arguments: collector.arguments(reference.args)?,
                    clauses: collector.clauses(implementation)?,
                    polarity: match header.polarity {
                        ty::ImplPolarity::Positive => "positive",
                        ty::ImplPolarity::Negative => "negative",
                    },
                    is_final: tcx.defaultness(implementation).is_final(),
                });
        }
        while adt_cursor < collector.adts.len() {
            let definition = *collector.adts.get_index(adt_cursor).unwrap();
            adt_cursor += 1;
            let adt = tcx.adt_def(definition);
            let tail_type = if adt.is_struct() {
                adt.non_enum_variant()
                    .tail_opt()
                    .map(|field| {
                        collector.ty(tcx
                            .type_of(field.did)
                            .instantiate_identity()
                            .skip_norm_wip())
                    })
                    .transpose()?
            } else {
                None
            };
            adt_declarations.push(AdtDeclaration {
                definition: def_json(collector.context, definition),
                parameters: collector.parameters(definition),
                is_struct: adt.is_struct(),
                tail_type,
                clauses: collector.clauses(definition)?,
            });
        }
        while associated_cursor < collector.associated.len() {
            let definition = *collector.associated.get_index(associated_cursor).unwrap();
            associated_cursor += 1;
            let bounds = tcx
                .explicit_item_bounds(definition)
                .skip_binder()
                .iter()
                .map(|(clause, _)| collector.clause(*clause))
                .collect::<Result<_, _>>()?;
            associated_type_declarations.push(AssociatedTypeDeclaration {
                definition: def_json(collector.context, definition),
                parameters: collector.parameters(definition),
                bounds,
            });
        }
        if cursor == collector.traits.len()
            && adt_cursor == collector.adts.len()
            && associated_cursor == collector.associated.len()
            && before_heads == collector.heads.len()
        {
            break;
        }
    }
    state.types = collector.types;
    state.traits = collector.traits;
    state.cursor = cursor;
    state.declarations = declarations;
    state.adts = collector.adts;
    state.adt_cursor = adt_cursor;
    state.adt_declarations = adt_declarations;
    state.heads = collector.heads;
    state.deferred_impls = deferred_impls;
    state.associated = collector.associated;
    state.associated_cursor = associated_cursor;
    state.associated_type_declarations = associated_type_declarations;
    Ok(())
}

pub(super) fn finish(state: State<'_>) -> Result<Material, String> {
    Ok(Material {
        types: state.types.finish("trait source type")?,
        declarations: state.declarations,
        adt_declarations: state.adt_declarations,
        associated_type_declarations: state.associated_type_declarations,
    })
}

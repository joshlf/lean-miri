// Signature adjustments follow pinned rustc_ty_utils::abi::fn_sig_for_fn_abi;
// layout and pass-mode classification remain Lean computations.
use super::{ExportContext, fn_sig_json_inner, pool_type, type_json};
use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
use rustc_middle::ty::{self, InstanceKind, ShimKind, Ty, TyCtxt};
use std::iter;
use rustc_hir as hir;
use rustc_attr_ir::lang_items::LangItem;
use rustc_span::DUMMY_SP;
use serde::Serialize;

#[derive(Serialize)]
pub(super) struct Policy {
    architecture: String,
    windows: bool,
    darwin: bool,
    simd_types_indirect: bool,
    soft_float: bool,
    max_reliable_alignment: u64,
    box_noalias: bool,
    llvm_writable: bool,
    optimize: bool,
    incremental: bool,
    panic_unwinds: bool,
    panic_in_drop_unwinds: bool,
}

#[derive(Serialize)]
pub(super) struct Definition {
    instance_id: u64,
    signature: pool_type::FunctionSignature,
    caller_location: Option<u64>,
    virtual_call: bool,
    has_definition: bool,
    foreign: bool,
    never_unwind: bool,
    drop_glue: bool,
    no_writable: bool,
    parameter_uses: Vec<u8>,
}

#[derive(Default)]
pub(super) struct State {
    cursor: usize,
    metadata_cursor: usize,
    seen: std::collections::HashSet<u64>,
    definitions: Vec<Definition>,
}

#[derive(Serialize)]
pub(super) struct Material {
    policy: Policy,
    definitions: Vec<Option<Definition>>,
}

pub(super) fn discover<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    state: &mut State,
) -> Result<(), String> {
    while state.cursor < context.pending_instances.len()
        || state.metadata_cursor < context.source_abi_demands.len()
    {
        let instance = if state.cursor < context.pending_instances.len() {
            let instance = context.pending_instances[state.cursor];
            state.cursor += 1;
            instance
        } else {
            let instance = context.source_abi_demands[state.metadata_cursor];
            state.metadata_cursor += 1;
            if context.pending_instances.contains(&instance) { continue; }
            instance
        };
        if matches!(instance.def, ty::InstanceKind::LlvmIntrinsic(_)) {
            continue;
        }
        if !state.seen.insert(context.instance_ids[&instance]) {
            continue;
        }
        let env = ty::TypingEnv::fully_monomorphized();
        let mut signature = if matches!(instance.def, ty::InstanceKind::Shim(ty::ShimKind::ThreadLocal(_))) {
            tcx.mk_fn_sig_safe_rust_abi([], tcx.thread_local_ptr_ty(instance.def_id()))
        } else {
            let ty = instance.ty(tcx, env);
            match *ty.kind() {
                ty::FnDef(definition, args) => tcx.instantiate_bound_regions_with_erased(
                    tcx.fn_sig(definition).instantiate(tcx, args.no_bound_vars().unwrap()).skip_norm_wip(),
                ),
                ty::Closure(definition, args) => {
                    let sig = tcx.instantiate_bound_regions_with_erased(args.as_closure().sig());
                    let receiver = tcx.closure_env_ty(
                        ty::Ty::new_closure(tcx, definition, args),
                        args.as_closure().kind(),
                        tcx.lifetimes.re_erased,
                    );
                    tcx.mk_fn_sig(
                        std::iter::once(receiver).chain(sig.inputs().iter().copied()),
                        sig.output(),
                        sig.fn_sig_kind,
                    )
                }
                ty::CoroutineClosure(def_id, args) => {
                    let coroutine_ty = Ty::new_coroutine_closure(tcx, def_id, args);
                    let sig = args.as_coroutine_closure().coroutine_closure_sig();

                    // When this `CoroutineClosure` comes from a `ConstructCoroutineInClosureShim`,
                    // make sure we respect the `target_kind` in that shim.
                    // FIXME(async_closures): This shouldn't be needed, and we should be populating
                    // a separate def-id for these bodies.
                    let mut coroutine_kind = args.as_coroutine_closure().kind();

                    let env_ty = if let InstanceKind::Shim(ShimKind::ConstructCoroutineInClosure {
                        receiver_by_ref,
                        ..
                    }) = instance.def
                    {
                        coroutine_kind = ty::ClosureKind::FnOnce;

                        // Implementations of `FnMut` and `Fn` for coroutine-closures
                        // still take their receiver by ref.
                        if receiver_by_ref {
                            Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, coroutine_ty)
                        } else {
                            coroutine_ty
                        }
                    } else {
                        tcx.closure_env_ty(coroutine_ty, coroutine_kind, tcx.lifetimes.re_erased)
                    };

                    let sig = tcx.instantiate_bound_regions_with_erased(sig);

                    tcx.mk_fn_sig(
                        iter::once(env_ty).chain([sig.tupled_inputs_ty]),
                        sig.to_coroutine_given_kind_and_upvars(
                            tcx,
                            args.as_coroutine_closure().parent_args(),
                            tcx.coroutine_for_closure(def_id),
                            coroutine_kind,
                            tcx.lifetimes.re_erased,
                            args.as_coroutine_closure().tupled_upvars_ty(),
                            args.as_coroutine_closure().coroutine_captures_by_ref_ty(),
                        ),
                        sig.fn_sig_kind,
                    )
                }
                ty::Coroutine(did, args) => {
                    let coroutine_kind = tcx.coroutine_kind(did).unwrap();
                    let sig = args.as_coroutine().sig();

                    let env_ty = Ty::new_mut_ref(tcx, tcx.lifetimes.re_erased, ty);

                    let pin_did = tcx.require_lang_item(LangItem::Pin, DUMMY_SP);
                    let pin_adt_ref = tcx.adt_def(pin_did);
                    let pin_args = tcx.mk_args(&[env_ty.into()]);
                    let env_ty = match coroutine_kind {
                        hir::CoroutineKind::Desugared(hir::CoroutineDesugaring::Gen, _) => {
                            // Iterator::next doesn't accept a pinned argument,
                            // unlike for all other coroutine kinds.
                            env_ty
                        }
                        hir::CoroutineKind::Desugared(hir::CoroutineDesugaring::Async, _)
                        | hir::CoroutineKind::Desugared(hir::CoroutineDesugaring::AsyncGen, _)
                        | hir::CoroutineKind::Coroutine(_) => Ty::new_adt(tcx, pin_adt_ref, pin_args),
                    };

                    // The `FnSig` and the `ret_ty` here is for a coroutines main
                    // `Coroutine::resume(...) -> CoroutineState` function in case we
                    // have an ordinary coroutine, the `Future::poll(...) -> Poll`
                    // function in case this is a special coroutine backing an async construct
                    // or the `Iterator::next(...) -> Option` function in case this is a
                    // special coroutine backing a gen construct.
                    let (resume_ty, ret_ty) = match coroutine_kind {
                        hir::CoroutineKind::Desugared(hir::CoroutineDesugaring::Async, _) => {
                            // The signature should be `Future::poll(_, &mut Context<'_>) -> Poll<Output>`
                            assert_eq!(sig.yield_ty, tcx.types.unit);

                            let poll_did = tcx.require_lang_item(LangItem::Poll, DUMMY_SP);
                            let poll_adt_ref = tcx.adt_def(poll_did);
                            let poll_args = tcx.mk_args(&[sig.return_ty.into()]);
                            let ret_ty = Ty::new_adt(tcx, poll_adt_ref, poll_args);

                            // We have to replace the `ResumeTy` that is used for type and borrow checking
                            // with `&mut Context<'_>` which is used in codegen.
                            #[cfg(debug_assertions)]
                            {
                                if let ty::Adt(resume_ty_adt, _) = sig.resume_ty.kind() {
                                    let expected_adt =
                                        tcx.adt_def(tcx.require_lang_item(LangItem::ResumeTy, DUMMY_SP));
                                    assert_eq!(*resume_ty_adt, expected_adt);
                                } else {
                                    panic!("expected `ResumeTy`, found `{:?}`", sig.resume_ty);
                                };
                            }
                            let context_mut_ref = Ty::new_task_context(tcx);

                            (Some(context_mut_ref), ret_ty)
                        }
                        hir::CoroutineKind::Desugared(hir::CoroutineDesugaring::Gen, _) => {
                            // The signature should be `Iterator::next(_) -> Option<Yield>`
                            let option_did = tcx.require_lang_item(LangItem::Option, DUMMY_SP);
                            let option_adt_ref = tcx.adt_def(option_did);
                            let option_args = tcx.mk_args(&[sig.yield_ty.into()]);
                            let ret_ty = Ty::new_adt(tcx, option_adt_ref, option_args);

                            assert_eq!(sig.return_ty, tcx.types.unit);
                            assert_eq!(sig.resume_ty, tcx.types.unit);

                            (None, ret_ty)
                        }
                        hir::CoroutineKind::Desugared(hir::CoroutineDesugaring::AsyncGen, _) => {
                            // The signature should be
                            // `AsyncIterator::poll_next(_, &mut Context<'_>) -> Poll<Option<Output>>`
                            assert_eq!(sig.return_ty, tcx.types.unit);

                            // Yield type is already `Poll<Option<yield_ty>>`
                            let ret_ty = sig.yield_ty;

                            // We have to replace the `ResumeTy` that is used for type and borrow checking
                            // with `&mut Context<'_>` which is used in codegen.
                            #[cfg(debug_assertions)]
                            {
                                if let ty::Adt(resume_ty_adt, _) = sig.resume_ty.kind() {
                                    let expected_adt =
                                        tcx.adt_def(tcx.require_lang_item(LangItem::ResumeTy, DUMMY_SP));
                                    assert_eq!(*resume_ty_adt, expected_adt);
                                } else {
                                    panic!("expected `ResumeTy`, found `{:?}`", sig.resume_ty);
                                };
                            }
                            let context_mut_ref = Ty::new_task_context(tcx);

                            (Some(context_mut_ref), ret_ty)
                        }
                        hir::CoroutineKind::Coroutine(_) => {
                            // The signature should be `Coroutine::resume(_, Resume) -> CoroutineState<Yield, Return>`
                            let state_did = tcx.require_lang_item(LangItem::CoroutineState, DUMMY_SP);
                            let state_adt_ref = tcx.adt_def(state_did);
                            let state_args = tcx.mk_args(&[sig.yield_ty.into(), sig.return_ty.into()]);
                            let ret_ty = Ty::new_adt(tcx, state_adt_ref, state_args);

                            (Some(sig.resume_ty), ret_ty)
                        }
                    };

                    if let Some(resume_ty) = resume_ty {
                        tcx.mk_fn_sig_safe_rust_abi([env_ty, resume_ty], ret_ty)
                    } else {
                        // `Iterator::next` doesn't have a `resume` argument.
                        tcx.mk_fn_sig_safe_rust_abi([env_ty], ret_ty)
                    }
                }
                _ => return Err(format!("source ABI unsupported instance type: {ty:?}")),
            }
        };
        if matches!(instance.def, ty::InstanceKind::Shim(ty::ShimKind::VTable(_))) {
            let mut inputs = signature.inputs_and_output.to_vec();
            inputs[0] = ty::Ty::new_mut_ptr(tcx, inputs[0]);
            signature.inputs_and_output = tcx.mk_type_list(&inputs);
        }
        let signature = tcx.try_normalize_erasing_regions(env, ty::Unnormalized::new_wip(signature))
            .map_err(|error| format!("source ABI signature normalization: {error:?}"))?;
        if matches!(instance.def, ty::InstanceKind::Virtual(..)) {
            let receiver = signature.inputs().first().ok_or("virtual instance has no receiver")?;
            type_json(context, tcx, ty::Ty::new_mut_ptr(tcx, *receiver))?;
            type_json(context, tcx, ty::Ty::new_mut_ptr(tcx, tcx.types.unit))?;
        }
        let definition = match instance.def {
            ty::InstanceKind::Item(id) | ty::InstanceKind::Intrinsic(id)
            | ty::InstanceKind::Shim(ty::ShimKind::DropGlue(id, _)) => Some(id),
            _ => None,
        };
        // Defining-crate metadata preserves optimized generic-body usage. The
        // instantiated MIR can change those uses and cannot reconstruct it.
        let parameter_uses = if let ty::InstanceKind::Item(id) = instance.def {
            tcx.deduced_param_attrs(id).iter().map(|attrs| attrs.usage.bits()).collect()
        } else {
            Vec::new()
        };
        state.definitions.push(Definition {
            instance_id: context.instance_ids[&instance],
            signature: fn_sig_json_inner(context, tcx, signature)?,
            caller_location: instance.def.requires_caller_location(tcx)
                .then(|| type_json(context, tcx, tcx.caller_location_ty())).transpose()?,
            virtual_call: matches!(instance.def, ty::InstanceKind::Virtual(..)),
            has_definition: definition.is_some(),
            foreign: definition.is_some_and(|id| tcx.is_foreign_item(id)),
            never_unwind: definition.is_some_and(|id|
                tcx.codegen_fn_attrs(id).flags.contains(CodegenFnAttrFlags::NEVER_UNWIND)),
            drop_glue: definition.is_some_and(|id| tcx.is_lang_item(id, rustc_attr_ir::lang_items::LangItem::DropGlue)),
            no_writable: definition.is_some_and(|id| rustc_attr_ir::find_attr!(tcx, id, RustcNoWritable)),
            parameter_uses,
        });
    }
    Ok(())
}

pub(super) fn finish(tcx: TyCtxt<'_>, state: State) -> Material {
    let target = &tcx.sess.target;
    let count = state.definitions.iter().map(|definition| definition.instance_id as usize + 1).max().unwrap_or(0);
    let mut definitions = std::iter::repeat_with(|| None).take(count).collect::<Vec<_>>();
    for definition in state.definitions {
        let id = definition.instance_id as usize;
        definitions[id] = Some(definition);
    }
    Material {
        policy: Policy {
            architecture: target.arch.to_string(), windows: target.is_like_windows,
            darwin: target.is_like_darwin, simd_types_indirect: target.simd_types_indirect,
            soft_float: target.rustc_abi == Some(rustc_target::spec::RustcAbi::Softfloat),
            max_reliable_alignment: target.max_reliable_alignment().bytes(),
            box_noalias: tcx.sess.opts.unstable_opts.box_noalias,
            llvm_writable: tcx.sess.opts.unstable_opts.llvm_writable,
            optimize: tcx.sess.opts.optimize != rustc_session::config::OptLevel::No,
            incremental: tcx.sess.opts.incremental.is_some(),
            panic_unwinds: tcx.sess.panic_strategy().unwinds(),
            panic_in_drop_unwinds: tcx.sess.opts.unstable_opts.panic_in_drop.unwinds(),
        },
        definitions,
    }
}

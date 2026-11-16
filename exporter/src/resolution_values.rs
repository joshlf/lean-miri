//! Concrete call-resolution evidence retained by semantic MIR bodies.
use serde::Serialize;
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum Callee {
    LlvmIntrinsic { function_type: u64, instance_id: u64 },
    ResolvedInstance {
        function_type: u64,
        instance_id: u64,
        dispatch_slot: Option<usize>,
    },
    VirtualDispatch {
        function_type: u64,
        instance_id: u64,
        dispatch_slot: Option<usize>,
    },
    IndirectFunctionPointer {
        function_type: u64,
        signature: super::pool_type::FunctionSignature,
        extra_argument_types: Vec<u64>,
    },
}

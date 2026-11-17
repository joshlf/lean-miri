//! Test-only observation after guest execution, independent of the input snapshot.
use super::*;
use rustc_middle::mir::interpret::{AllocId, AllocRange, GlobalAlloc};
use std::num::NonZeroU64;

#[derive(serde::Serialize)]
struct Trace {
    schema: &'static str,
    snapshot_frontier: u64,
    post_execution_sentinel: u64,
    allocations: Vec<Memory>,
}
#[derive(serde::Serialize)]
struct Memory {
    source_alloc_id: u64,
    created_during_reference: bool,
    size_bytes: u64,
    align_bytes: u64,
    mutability: &'static str,
    bytes: String,
    initialization_ranges: Vec<allocation_values::InitializationRange>,
    relocations: Vec<Relocation>,
}
#[derive(serde::Serialize)]
struct Relocation {
    storage_offset_bytes: u64,
    target_source_alloc_id: u64,
    target_offset_encoded_bytes: String,
    immutable: bool,
    shared_ref: bool,
}

pub(super) fn enabled() -> Result<bool, String> {
    match env::var("LEAN_MIRI_REFERENCE_ALLOCATION_TRACE") {
        Ok(value) if value == "1" => Ok(true),
        Ok(value) if value == "0" || value.is_empty() => Ok(false),
        Err(env::VarError::NotPresent) => Ok(false),
        _ => Err("LEAN_MIRI_REFERENCE_ALLOCATION_TRACE must be 0 or 1".into()),
    }
}

pub(super) fn write(tcx: TyCtxt<'_>, frontier: u64, output: &std::path::Path) -> Result<(), String> {
    // The sentinel is reserved only after the guest has stopped. It must never
    // enter the execution snapshot or alter the guest's allocation history.
    let sentinel = allocator_world::raw_id(tcx.reserve_alloc_id());
    let mut pending = (frontier + 1..sentinel).collect::<Vec<_>>();
    let mut seen = HashSet::new();
    let mut allocations = Vec::new();
    while let Some(raw) = pending.pop() {
        if !seen.insert(raw) { continue; }
        let id = AllocId(NonZeroU64::new(raw).ok_or("trace encountered allocation ID zero")?);
        let Some(GlobalAlloc::Memory(memory)) = tcx.try_get_global_alloc(id) else { continue; };
        let memory = memory.inner();
        let bytes = memory.inspect_with_uninit_and_ptr_outside_interpreter(0..memory.len());
        let pointer_size = tcx.data_layout.pointer_size().bytes_usize();
        let mut relocations = Vec::new();
        for (offset, provenance) in memory.provenance().ptrs().iter() {
            let (target, immutable, shared_ref) = provenance.into_parts();
            let target = allocator_world::raw_id(target);
            pending.push(target);
            let start = offset.bytes_usize();
            relocations.push(Relocation {
                storage_offset_bytes: offset.bytes(),
                target_source_alloc_id: target,
                target_offset_encoded_bytes: bytes_hex(&bytes[start..start + pointer_size]),
                immutable,
                shared_ref,
            });
        }
        allocations.push(Memory {
            source_alloc_id: raw,
            created_during_reference: raw > frontier,
            size_bytes: memory.size().bytes(),
            align_bytes: memory.align.bytes(),
            mutability: if memory.mutability.is_mut() { "mutable" } else { "immutable" },
            bytes: bytes_hex(bytes),
            initialization_ranges: memory.init_mask()
                .range_as_init_chunks(AllocRange::from(rustc_abi::Size::ZERO..memory.size()))
                .map(|chunk| {
                    let range = chunk.range();
                    allocation_values::InitializationRange {
                        state: if chunk.is_init() { "initialized" } else { "uninitialized" },
                        start_bytes: range.start.bytes(),
                        end_bytes_exclusive: range.end.bytes(),
                    }
                }).collect(),
            relocations,
        });
    }
    allocations.sort_by_key(|row| row.source_alloc_id);
    let trace = Trace {
        schema: "post_execution_raw_ctfe_allocations_v1",
        snapshot_frontier: frontier,
        post_execution_sentinel: sentinel,
        allocations,
    };
    let mut path = output.as_os_str().to_os_string();
    path.push(".miri-allocations.json");
    write_document(std::path::Path::new(&path), &trace)
}

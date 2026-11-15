#!/usr/bin/env python3
"""Hash-pin and check Miri's machine memory-hook ordering boundary.

The full interpreter methods are trait-heavy, so this checks their actual
caller order rather than copying a fake stand-in body. The corresponding Lean
functions update the live BorrowTree extra and expose the same external race,
sync, span, and free operations as callbacks.
"""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path


EXPECTED_MACHINE = "f82134332a85b1ff6561646d4192f55b0894582b"
EXPECTED_TRACKER = "89736bdadf6bf2e71953d5ab5cb1f0fbeb332046"
EXPECTED_TREE_MOD = "086430ad06cd17bb22d77f3baa9a7ec2ae24da6f"
EXPECTED_TREE_RS = "91cc25f2f9b88239225a2a3d32a4fd98262a6fc0"
ORDER = "diagnostic>data-race>tree-borrows>sync>delete-or-free"


def rust_blob_hash(contents: bytes) -> str:
    header = b"blob " + str(len(contents)).encode("ascii") + b"\0"
    return hashlib.sha1(header + contents).hexdigest()


def checked_source(path: Path, expected: str, label: str) -> str:
    contents = path.read_bytes()
    actual = rust_blob_hash(contents)
    if actual != expected:
        raise ValueError(f"pinned {label} blob mismatch: {actual}")
    return contents.decode("utf-8")


def body(source: str, start: str, end: str) -> str:
    first = source.index(start)
    last = source.index(end, first)
    return source[first:last]


def order(label: str, text: str, markers: list[str]) -> None:
    positions = []
    for marker in markers:
        try:
            positions.append(text.index(marker))
        except ValueError as exc:
            raise ValueError(f"{label} lacks source marker {marker!r}") from exc
    if positions != sorted(positions):
        raise ValueError(f"{label} source operations occur out of order")


def main() -> None:
    if len(sys.argv) != 7:
        raise SystemExit(
            "usage: check_machine_memory_order.py MACHINE_RS TRACKER_MOD_RS "
            "TREE_MOD_RS TREE_RS HOOKS_LEAN OUT_RS"
        )
    machine_path, tracker_path, tree_mod_path, tree_path, lean_path, output_path = map(Path, sys.argv[1:])
    machine = checked_source(machine_path, EXPECTED_MACHINE, "machine.rs")
    tracker = checked_source(tracker_path, EXPECTED_TRACKER, "borrow_tracker/mod.rs")
    checked_source(tree_mod_path, EXPECTED_TREE_MOD, "tree_borrows/mod.rs")
    tree = checked_source(tree_path, EXPECTED_TREE_RS, "tree_borrows/tree.rs")
    lean = lean_path.read_text(encoding="utf-8")

    read = body(machine, "    fn before_memory_read(\n", "    fn before_memory_write(\n")
    write = body(machine, "    fn before_memory_write(\n", "    fn before_memory_deallocation(\n")
    dealloc = body(machine, "    fn before_memory_deallocation(\n", "    fn retag_ptr_value(\n")
    order("machine before_memory_read", read, [
        "machine.emit_diagnostic", "match &machine.data_race",
        "borrow_tracker.before_memory_read", "alloc_extra.meta_objs.range", "obj.on_access",
    ])
    order("machine before_memory_write", write, [
        "machine.emit_diagnostic", "match &machine.data_race",
        "borrow_tracker.before_memory_write", "alloc_extra.meta_objs.range",
        "obj.on_access", "alloc_extra.meta_objs.remove_range_if", "obj.opaque()",
    ])
    order("machine before_memory_deallocation", dealloc, [
        "machine.emit_diagnostic", "match &machine.data_race",
        "borrow_tracker.before_memory_deallocation", "alloc_extra.meta_objs.range(AllocRange { start: Size::ZERO, size })",
        "obj.on_access", "allocation_spans.borrow_mut()", "machine.free_alloc_id",
    ])

    order("Lean beforeMemoryRead", body(lean, "def beforeMemoryRead", "/-- Pinned `MiriMachine::before_memory_write"), [
        "hooks.emitDiagnostic", "hooks.dataRaceRead", "commitTreeAccess", "runSyncRange",
    ])
    order("Lean beforeMemoryWrite", body(lean, "def beforeMemoryWrite", "structure DeallocationResult"), [
        "hooks.emitDiagnostic", "hooks.dataRaceWrite", "commitTreeAccess",
        "hooks.syncOnAccess", "hooks.deleteOnWrite", ".remove offset",
    ])
    order("Lean beforeMemoryDeallocation", body(lean, "def beforeMemoryDeallocation", "/-- Adapt the source-ordered Tree Borrows hooks"), [
        "hooks.emitDiagnostic", "hooks.dataRaceDeallocate", "deallocateBorrowRange",
        "hooks.syncOnAccess", "hooks.recordDeallocatedSpan", "hooks.freeAllocId",
    ])

    # The source tracker dispatches Tree Borrows for each operation; the Lean
    # caller uses the matching BorrowTree range/access entry points.
    order("AllocState::before_memory_read", body(
        tracker, "pub fn before_memory_read<'tcx>(", "    pub fn before_memory_write<'tcx>("), [
            "AllocState::TreeBorrows(tb)", "before_memory_access",
        ])
    order("AllocState::before_memory_write", body(
        tracker, "pub fn before_memory_write<'tcx>(", "    pub fn before_memory_deallocation<'tcx>("), [
            "AllocState::TreeBorrows(tb)", "before_memory_access",
        ])
    order("AllocState::before_memory_deallocation", body(
        tracker, "pub fn before_memory_deallocation<'tcx>(", "    pub fn remove_unreachable_tags("), [
            "AllocState::TreeBorrows(tb)", "tb.get_mut().before_memory_deallocation",
        ])
    if "fn perform_access(" not in tree or "pub fn dealloc(" not in tree:
        raise ValueError("pinned Tree Borrows module lacks the expected access entry points")

    output_path.write_text(
        'fn main() { println!("machine-memory-hooks ' + ORDER + '"); }\n',
        encoding="utf-8",
    )
    print("checked machine read/write/deallocation hook order against pinned sources")


if __name__ == "__main__":
    main()

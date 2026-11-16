#!/usr/bin/env python3
"""Check a complete abstract virtual identity without inventing concrete targets."""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_inspection_document as load_mir_document, pool_entry

doc = load_mir_document(sys.argv[1])
scope = doc["selected_scope"]
assert "completeness" not in doc
assert scope["kind"] == "rooted_structural_closure"
assert scope["semantics"] == "structural_export_closure_only"
assert scope["roots"][0]["def_path"] == "call_trait_object"

virtual_targets = [
    item for item in doc["instances"]
    if item.get("kind") == "virtual_dispatch_target"
]
assert virtual_targets, "the source virtual instance identity was dropped"
for target in virtual_targets:
    assert "status" not in target
    assert target["body_status"] == "not_applicable"
    assert "status" not in target["virtual_identity"]
    assert pool_entry(doc, "types", target["virtual_identity"]["function_type"])["shape"]["kind"] == "function_definition"
    assert doc["source_abi"]["definitions"][target["instance_id"]] is not None

def walk(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)

calls = [node for node in walk(doc["bodies"]) if node.get("kind") == "virtual_dispatch"]
assert calls, "the MIR callsite lost its virtual operation"
for call in calls:
    assert isinstance(call.get("dispatch_slot"), int)
    assert "virtual_resolution" not in call
assert doc["source_vtables"]["bindings"] == [], "opaque dyn input invented a concrete vtable target"
assert not any("ValueCell as ValueSource" in row["def_path"] and row["kind"] == "instance_mir"
               for row in doc["instances"]), "unreached implementation body leaked into abstract root"
assert "status" not in scope
assert "unresolved_obligations" not in scope
print("validated abstract virtual identity and signature without invented concrete targets")

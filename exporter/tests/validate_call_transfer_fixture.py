#!/usr/bin/env python3
"""Recover exact MIR transfer edges and pinned covariance expectations.

The paired Lean check evaluates these exact type IDs using the typed source
materials. The fixture is intentionally ABI-compatible but not executed.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_inspection_document as load_mir_document, pool_entry


def require(condition, message):
    if not condition:
        raise SystemExit(message)


document = load_mir_document(sys.argv[1])
types = {item["type_id"]: item for item in document["types"]}
checks = []
require("compiler_covariance_queries" not in document, "producer emitted covariance answer catalog")
require("virtual" not in document["compiler_runtime_queries"], "producer emitted virtual query answer catalog")


def display(type_ref):
    if not isinstance(type_ref, int):
        return ""
    node = types.get(type_ref, {})
    return node.get("display", "")


def type_id(type_ref):
    return type_ref if isinstance(type_ref, int) else None


def relation_ids(source_ref, target_ref):
    return source_ref in types and target_ref in types


def require_false_relation(source_ref, target_ref, label):
    require(source_ref in types and target_ref in types, f"{label}: source material missing")
    checks.append({"source_type": source_ref, "target_type": target_ref,
                   "expected": False, "label": label})


def require_transfer(source_ref, target_ref, label):
    require(source_ref in types and target_ref in types,
            f"{label}: exact source/destination type material is missing")


def body_payload(row):
    return pool_entry(document, "bodies", row["body"])


instance_rows = document["instances"]
all_body_rows = list(document["body_roots"]) + [
    row for row in instance_rows if isinstance(row.get("body"), int)
]


def calls_in(body):
    payload = body_payload(body)
    for block in payload.get("basic_blocks", []):
        terminator = block.get("terminator", {}).get("kind", {})
        if terminator.get("variant") == "Call":
            yield terminator


def operand_type_ref(operand):
    if not isinstance(operand, dict):
        return None
    if operand.get("kind") in ("Copy", "Move"):
        return operand.get("place", {}).get("type")
    constant = operand.get("constant", {})
    return constant.get("type")


def local_type_ref(body, local):
    for item in body_payload(body).get("locals", []):
        if item.get("local") == local:
            return item.get("type")
    return None


def body_by_path(fragment):
    return [row for row in all_body_rows if fragment in row.get("def_path", "")]


# Recover the exact call operand/destination and the candidate's substituted
# MIR locals. Retain those exact IDs rather than selecting expectations
# from unrelated types with similar printed names.
indirect_bodies = body_by_path("indirect_pointer_call")
require(indirect_bodies, "indirect_pointer_call body is absent")
indirect_call = next(
    (
        (body, call)
        for body in indirect_bodies
        for call in calls_in(body)
        if call.get("resolution", {}).get("kind") == "indirect_function_pointer"
        and "*mut u8" in display(call["resolution"].get("function_type"))
        and "*const u8" in display(call["resolution"].get("function_type"))
    ),
    None,
)
require(indirect_call, "typed indirect FnPtr callsite was not exported")
call_body, call = indirect_call
pointer_target_rows = [row for row in instance_rows if row.get("def_path", "").endswith("pointer_target")]
require(pointer_target_rows, "pointer_target candidate instance/body is absent")
pointer_target_body = next(
    (row for row in pointer_target_rows if "body" in row),
    None,
)
require(pointer_target_body, "pointer_target candidate has no substituted MIR body")
argument_source = operand_type_ref(call.get("args", [{}])[0].get("operand"))
argument_target = local_type_ref(pointer_target_body, 1)
return_source = local_type_ref(pointer_target_body, 0)
return_target = call.get("destination", {}).get("type")
require(all(value is not None for value in [argument_source, argument_target, return_source, return_target]),
        "indirect pointer call/candidate transfer types could not be recovered")
require(type_id(argument_source) != type_id(argument_target),
        "indirect FnPtr argument fixture did not preserve its distinct MIR types")
require(type_id(return_source) != type_id(return_target),
        "indirect FnPtr return fixture did not preserve its distinct MIR types")
require_transfer(argument_source, argument_target, "indirect FnPtr argument")
require_false_relation(argument_source, argument_target, "indirect argument pointer mutability")
require_transfer(return_source, return_target, "indirect FnPtr return")
require_false_relation(return_source, return_target, "indirect return pointer mutability")

# Rust's virtual call passes the concrete receiver pointer into the
# instantiated method's receiver local. Find a validated virtual resolution
# for this fixture's trait method, then retain its concrete receiver transfer.
instance_by_id = {item["instance_id"]: item for item in document["instances"]}
fixture_virtual_targets = [instance_by_id[method["instance_id"]]
    for binding in document["source_vtables"]["bindings"] for method in binding["methods"]
    if method["instance_id"] is not None
    and "ConcreteObject as TransferObject" in instance_by_id[method["instance_id"]]["def_path"]
    and instance_by_id[method["instance_id"]]["def_path"].endswith("::get")]
require(
    fixture_virtual_targets,
    "TransferObject::get has no validated concrete virtual target row",
)
virtual_bodies = body_by_path("virtual_call")
require(virtual_bodies, "virtual_call body is absent")
virtual_callsite = next(
    (
        call
        for body in virtual_bodies
        for call in calls_in(body)
        if call.get("resolution", {}).get("kind") == "virtual_dispatch"
    ),
    None,
)
require(virtual_callsite, "trait-object virtual callsite is absent")
virtual_target = fixture_virtual_targets[0]
virtual_target_body = next(
    (row for row in instance_rows
     if row.get("instance_id") == virtual_target.get("instance_id") and "body" in row),
    None,
)
require(virtual_target_body, "validated virtual target has no substituted MIR body")
receiver_source = next(
    (
        item["type_id"]
        for item in types.values()
        if item.get("shape", {}).get("kind") == "raw_pointer"
        and item.get("shape", {}).get("mutability", {}).get("kind") == "mutable"
        and "ConcreteObject"
        in types.get(item.get("shape", {}).get("pointee"), {})
        .get("shape", {}).get("def_path", "")
    ),
    None,
)
receiver_target = local_type_ref(virtual_target_body, 1)
require(receiver_source is not None and receiver_target is not None and relation_ids(receiver_source, receiver_target),
        "exact virtual receiver transfer from *mut ConcreteObject to callee local is absent")
# Receiver ABI compatibility does not make a raw pointer covariant with a
# reference. The typed relation must preserve this negative expectation.
require_false_relation(receiver_source, receiver_target, "virtual receiver")
virtual_argument_source = operand_type_ref(virtual_callsite.get("args", [{}, {}])[1].get("operand"))
virtual_argument_target = local_type_ref(virtual_target_body, 2)
virtual_return_source = local_type_ref(virtual_target_body, 0)
virtual_return_target = virtual_callsite.get("destination", {}).get("type")
require_transfer(virtual_argument_source, virtual_argument_target,
                "virtual call nonreceiver argument")
require_transfer(virtual_return_source, virtual_return_target,
                "virtual call return")

# pthread_create's generated callback call takes the registration data pointer
# and returns through Miri's source *mut () destination. This exact compiler
# relation is distinct from the C registration function's own signature.
pthread_callsite = next(
    (
        call
        for body in body_by_path("call_transfer_root")
        for call in calls_in(body)
        if call.get("resolution", {}).get("kind") == "indirect_function_pointer"
        and len(call.get("args", [])) == 4
    ),
    None,
)
require(pthread_callsite, "indirect pthread_create MIR callsite is absent")
pthread_function_type = display(pthread_callsite["resolution"].get("function_type"))
require("usize" in pthread_function_type and "c_void" in pthread_function_type,
        "four-argument pthread_create FnPtr signature is not the exported callsite")
callback_data_source = operand_type_ref(pthread_callsite["args"][3]["operand"])
callback_operand_type = operand_type_ref(pthread_callsite["args"][2]["operand"])
callback_rows = [row for row in instance_rows if row.get("def_path", "").endswith("thread_start")]
callback_body = next(
    (row for row in callback_rows if "body" in row),
    None,
)
require(callback_body is not None and callback_data_source is not None and callback_operand_type is not None,
        "pthread callback target or registration data operand is absent")
callback_signature = display(callback_operand_type)
require("c_void" in callback_signature and "*mut" in callback_signature,
        "pthread callback operand is not the fixture's mutable c_void callback")
callback_argument_target = local_type_ref(callback_body, 1)
require(
    callback_argument_target is not None
    and type_id(callback_data_source) == type_id(callback_argument_target),
    "pthread registration data operand does not match the callback MIR argument local",
)
callback_return_source = local_type_ref(callback_body, 0)
require(
    callback_return_source is not None
    and type_id(callback_return_source) == type_id(callback_argument_target),
    "thread_start return local does not preserve its callback argument type",
)


def is_mutable_unit_pointer(node):
    shape = node.get("shape", {})
    if shape.get("kind") != "raw_pointer":
        return False
    if shape.get("mutability", {}).get("kind") != "mutable":
        return False
    pointee = types.get(shape.get("pointee"), {})
    return (
        pointee.get("shape", {}).get("kind") == "tuple"
        and pointee.get("shape", {}).get("elements", []) == []
    )


unit_pointer_destination = next(
    (
        item["type_id"]
        for item in types.values()
        if is_mutable_unit_pointer(item)
    ),
    None,
)
require_transfer(callback_return_source, unit_pointer_destination,
                "pthread generated callback return")
require(type_id(callback_return_source) != type_id(unit_pointer_destination),
        "pthread callback return did not exercise *mut c_void to *mut ()")

require_false_relation(callback_return_source, unit_pointer_destination,
                       "pthread generated callback return")

# Confirm the registration call itself is retained as an indirect FnPtr call
# and its exact foreign function identity is in the exported instance graph.
instances = document["instances"]
pthread_instances = [
    item
    for item in instances
    if item.get("def_path", "").endswith("pthread_create")
    or item.get("symbol_name") == "pthread_create"
]
require(pthread_instances, "pthread_create foreign instance/candidate is absent")

Path(sys.argv[2]).write_text(json.dumps({"checks": checks}))

print(
    "validated typed indirect FnPtr pointer transfer, a resolved virtual target, "
    "and pthread_create callback transfer; candidate discovery is not exhaustive"
)

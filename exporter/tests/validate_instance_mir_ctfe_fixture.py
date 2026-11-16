#!/usr/bin/env python3
"""Validate reachable external constructors and rustc-evaluated constants."""
import json
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_inspection_document as load_mir_document, pool_entry


def require(condition, message):
    if not condition:
        raise SystemExit(f"CTFE instance MIR fixture: {message}")


def walk(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def main(path):
    document = load_mir_document(path)
    rows = {row.get("def_path"): row for row in document["instances"]
            if row.get("kind") == "instance_mir"}
    for def_path in ("ctfe_producer_types::Pair", "ctfe_producer_types::Token::Number"):
        require(def_path in rows, f"missing concrete constructor {def_path}")
        row = rows[def_path]
        body = pool_entry(document, "bodies", row["body"])
        require(body["instance_id"] == row["instance_id"], "constructor body identity differs")
        require(body["source_def_id"] == row["def_id"], "constructor source identity differs")
        require(body["basic_blocks"], "constructor body has no blocks")
    for def_path in ("ctfe_producer_types::compile_time_add", "ctfe_producer_types::Opcode::compile_time_xor"):
        require(def_path not in rows, f"CTFE-only function leaked into executable closure: {def_path}")
    constants = pool_entry(document, "bodies", rows["constants"]["body"])
    bits = {node["bits_unsigned"] for node in walk(constants) if "bits_unsigned" in node}
    require({"42", "121"}.issubset(bits), "constant results were not evaluated by rustc")
    require([row["def_path"] for row in document["root_declarations"]] == ["invoke"],
            "generic root declaration was not retained separately")
    pair = pool_entry(document, "bodies", rows["ctfe_producer_types::Pair"]["body"])["basic_blocks"]
    pair_aggregate = [n for n in walk(pair) if n.get("kind") == "Aggregate"]
    require(any(n.get("aggregate_kind", {}).get("def_path") == "ctfe_producer_types::Pair"
                for n in pair_aggregate), "tuple constructor body lacks its Pair ADT aggregate")
    variant_aggregate = [n for n in walk(pool_entry(document, "bodies", rows["ctfe_producer_types::Token::Number"]["body"])["basic_blocks"])
                         if n.get("kind") == "Aggregate"]
    require(any(n.get("aggregate_kind", {}).get("def_path") == "ctfe_producer_types::Token"
                and n.get("aggregate_kind", {}).get("variant_index") == 1
                for n in variant_aggregate), "enum constructor body lacks Token::Number variant 1")

    calls = []
    for caller in ("make_pair", "make_token"):
        caller_row = rows[caller]
        for block in pool_entry(document, "bodies", caller_row["body"])["basic_blocks"]:
            terminator = block.get("terminator", {}).get("kind", {})
            if terminator.get("variant") == "Call":
                calls.append(terminator)
    require(len(calls) == 2, f"expected two constructor call sites, found {len(calls)}")
    for call in calls:
        resolution = call.get("resolution", {})
        require(call.get("call_source", {}).get("kind") == "normal_call",
                f"constructor call is not a normal call: {call.get('call_source')}")
        require(resolution.get("kind") == "indirect_function_pointer"
                and "status" not in resolution,
                f"constructor call resolution changed: {resolution}")
    print("validated concrete external constructors, evaluated constants, and declaration-only generic root")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: validate_instance_mir_ctfe_fixture.py EXPORT.json")
    main(sys.argv[1])

#!/usr/bin/env python3
"""Fresh finite closure-edge source and independent compiler comparison."""
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "scratch/closure-callees-check"
CLOSURE = "std::rt::lang_start::{closure#0}"


def export(path, roots, *, foundation=True, succeeds=True):
    path.unlink(missing_ok=True)
    arguments = ["bash", "tools/export-mir.sh", "--output", str(path)]
    if foundation:
        arguments.append("--foundation")
    for root in roots:
        arguments.extend(["--root", root])
    arguments.extend(["--", str(ROOT / "exporter/fixtures/foundation_closure.rs"), "--crate-name=foundation_closure"])
    result = subprocess.run(arguments, cwd=ROOT, text=True, capture_output=True)
    if succeeds:
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)
        return json.loads(path.read_text())
    if result.returncode == 0 or "missing MIR root" not in result.stderr:
        raise RuntimeError("unselected/unknown source edge was accepted: " + result.stdout + result.stderr)
    if path.exists():
        raise RuntimeError("failed export left executable source output")
    return None


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    subprocess.run(["bash", "tools/build-exporter.sh"], cwd=ROOT, check=True)
    baseline = export(OUT / "baseline.json", [CLOSURE])
    selected = baseline["closure_templates"][0]
    callees = set()
    for block in selected["blocks"]:
        terminal = block["terminator"]
        if terminal["kind"] == "call" and terminal["function"]["kind"] == "constant":
            shape = baseline["types"][terminal["function"]["type"]]["shape"]
            if shape["kind"] == "function_definition":
                definition = baseline["definitions"][shape["definition"]]
                if definition["kind"] == "fn":
                    callees.add(definition["path"])
    if len(callees) != 1:
        raise RuntimeError("control fixture ordinary source edge is not unique")
    callee = next(iter(callees))
    baseline_paths = {baseline["definitions"][body["definition"]]["path"] for body in baseline["bodies"]}
    if callee in baseline_paths:
        raise RuntimeError("closure baseline eagerly captured the ordinary callee")
    export(OUT / "missing-owner.json", [callee], succeeds=False)
    export(OUT / "unknown-edge.json", [CLOSURE, callee + "__absent"], succeeds=False)
    source = export(OUT / "source.json", [CLOSURE, callee])
    source_paths = {source["definitions"][body["definition"]]["path"] for body in source["bodies"]}
    if source_paths != baseline_paths | {callee}:
        raise RuntimeError("explicit generic callee table differs")
    export(OUT / "reference.json", ["main"], foundation=False)
    env = os.environ.copy()
    env["ELAN_HOME"] = str(ROOT / ".elan")
    command = [str(ROOT / ".elan/bin/lake"), "build", "Miri.Frontend.FoundationClosureMIR", "Miri.Frontend.FoundationDirectCalls"]
    subprocess.run(["flock", "/tmp/lean-miri-lake-build.lock", *command], cwd=ROOT, env=env, check=True)
    subprocess.run([str(ROOT / ".elan/bin/lake"), "env", "lean", "--run",
                    "tests/foundation/FoundationClosureCallees.lean", str(OUT / "source.json"), str(OUT / "reference.json")],
                   cwd=ROOT, env=env, check=True)


if __name__ == "__main__":
    main()

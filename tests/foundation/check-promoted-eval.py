#!/usr/bin/env python3
"""Compare a source-only promoted recipe/fixed MIR fragment to real schema12 MIR."""
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]


def run(arguments, env):
    subprocess.run([str(arg) for arg in arguments], cwd=ROOT, env=env, check=True)


def main():
    env = os.environ.copy()
    env["ELAN_HOME"] = str(ROOT / ".elan")
    run([sys.executable, ROOT / "tests/foundation/check-promoted-source.py"], env)
    run(["bash", ROOT / "tools/build-exporter.sh"], env)
    out = ROOT / "scratch/promoted-source-check"
    reference = out / "schema12-reification.json"
    run(["bash", ROOT / "tools/export-mir.sh", "--output", reference, "--root", "concrete_vtable", "--",
         ROOT / "exporter/fixtures/foundation_fn_vtable.rs", "--crate-name=promoted_source"], env)
    lake = ROOT / ".elan/bin/lake"
    run(["flock", "/tmp/lean-miri-lake-build.lock", lake, "build", "Miri.Frontend.FoundationPromotedMIR"], env)
    run([lake, "env", "lean", "--run", ROOT / "tests/foundation/FoundationPromotedEval.lean",
         out / "local-source.json", reference], env)


if __name__ == "__main__":
    main()

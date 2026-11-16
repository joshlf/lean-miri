#!/usr/bin/env python3
"""Compare Lean queries with a rustc oracle tied to the exact exported input."""

import argparse
import json
import os
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("oracle", type=Path)
    parser.add_argument("--skip-build", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    source = args.input.resolve()
    oracle_path = args.oracle.resolve()
    payload = source.read_bytes()
    oracle = json.loads(oracle_path.read_bytes())
    fingerprint = 0xCBF29CE484222325
    for byte in payload:
        fingerprint = ((fingerprint ^ byte) * 0x100000001B3) & ((1 << 64) - 1)
    if oracle.get("schema") != "lean-miri-rustc-oracle":
        parser.error("unexpected compiler oracle schema")
    if (oracle.get("snapshot_byte_length") != len(payload)
            or oracle.get("snapshot_fnv1a64") != f"{fingerprint:016x}"):
        parser.error("compiler oracle belongs to different exported input bytes")
    document = json.loads(payload)
    if oracle.get("rustc_commit") != document["producer"]["rustc_commit"]:
        parser.error("compiler oracle belongs to a different compiler revision")
    env = os.environ.copy()
    env["ELAN_HOME"] = env.get("LEAN_MIRI_ELAN_HOME", str(root / ".elan"))
    env["PATH"] = str(Path(env["ELAN_HOME"]) / "bin") + os.pathsep + env["PATH"]
    env["LEAN_NUM_THREADS"] = "1"
    if not args.skip_build:
        subprocess.run([
            "flock", "--no-fork", "/tmp/lean-miri-lake-build.lock", "lake", "build",
            "Miri.Input.Decoder", "Miri.Input.CompilerProviders",
        ], cwd=root, env=env, check=True)
    for tool in ["CheckSourceLayouts", "CheckSourceTypeQueries", "CheckSourceAbi", "CheckSourceVTables"]:
        subprocess.run([
            "lake", "env", "lean", "-j1", "--run", f"tools/{tool}.lean",
            str(source), str(oracle_path),
        ], cwd=root, env=env, check=True)


if __name__ == "__main__":
    main()

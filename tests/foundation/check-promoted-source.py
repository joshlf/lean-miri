#!/usr/bin/env python3
"""Fresh complete promoted source tables versus an independent pinned-rustc probe."""
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
PIN = "8144389c895da997dbdecaa635e41d6a50be6ffd"
TOOLCHAIN = "miri-exporter-" + PIN[:12]
OUT = ROOT / "scratch" / "promoted-source-check"


def run(args, env):
    process = subprocess.run([str(arg) for arg in args], cwd=ROOT, env=env,
                             text=True, capture_output=True)
    if process.returncode:
        raise RuntimeError(process.stdout + process.stderr)
    return process.stdout


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    toolchain = ROOT / ".rustup" / "toolchains" / TOOLCHAIN
    rustc = toolchain / "bin" / "rustc"
    env = os.environ.copy()
    env.update(RUSTUP_HOME=str(ROOT / ".rustup"), CARGO_HOME=str(ROOT / ".cargo"),
               CARGO_TARGET_DIR=str(ROOT / "exporter" / "target"),
               ELAN_HOME=str(ROOT / ".elan"))
    env["PATH"] = str(ROOT / ".cargo" / "bin") + os.pathsep + env.get("PATH", "")
    env["LD_LIBRARY_PATH"] = str(toolchain / "lib") + os.pathsep + env.get("LD_LIBRARY_PATH", "")
    if "commit-hash: " + PIN not in run([rustc, "-vV"], env):
        raise RuntimeError("independent source probe requires pinned rustc")
    probe = OUT / "probe"
    run([rustc, ROOT / "tests/foundation/PromotedSourceProbe.rs", "-o", probe, "-Cprefer-dynamic"], env)
    flags = ["--crate-name=promoted_source", "--edition=2024", "--sysroot", str(ROOT / "scratch/miri-sysroot"),
             "--cfg=miri", "-Zalways-encode-mir", "-Zextra-const-ub-checks", "-Zmir-preserve-ub",
             "-Zmir-opt-level=0", "-Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums",
             "-Zmir-enable-passes=-ReferencePropagation,-GVN", "-Zdeduplicate-diagnostics=no"]
    paths = []
    for label, owner, fixture, count in [
            ("local", "concrete_vtable", "foundation_fn_vtable.rs", 1),
            ("internal", "std::rt::lang_start_internal", "foundation_closure.rs", 0)]:
        arguments = [str(ROOT / "exporter/fixtures" / fixture)] + flags
        case = env.copy()
        case["PROMOTED_SOURCE_OWNER"] = owner
        reference = OUT / (label + "-reference.json")
        reference.write_text(run([probe] + arguments, case))
        source = OUT / (label + "-source.json")
        source.unlink(missing_ok=True)
        case.update(PROMOTED_SOURCE_ARGS=json.dumps(["rustc"] + arguments),
                    PROMOTED_SOURCE_OUTPUT=str(source))
        run([ROOT / ".cargo/bin/cargo", "+" + TOOLCHAIN, "test", "--release", "--locked", "--offline",
             "--manifest-path", ROOT / "exporter/Cargo.toml",
             "foundation::promoted_material::tests::capture_complete_source_table",
             "--", "--ignored", "--exact"], case)
        actual = json.loads(reference.read_text())
        material = json.loads(source.read_text())
        if actual["count"] != count or material["promoted_tables"][0]["promoted_count"] != count:
            raise RuntimeError("genuine promoted source control changed; investigate pinned source")
        paths.extend([source, reference])
    lake = ROOT / ".elan/bin/lake"
    run(["flock", "/tmp/lean-miri-lake-build.lock", lake, "build", "Miri.Frontend.FoundationPromoted"], env)
    print(run([lake, "env", "lean", "--run", ROOT / "tests/foundation/FoundationPromoted.lean"] + paths, env), end="")


if __name__ == "__main__":
    main()

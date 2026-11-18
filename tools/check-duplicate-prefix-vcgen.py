#!/usr/bin/env python3
"""Check the vcgen client against this library and the pinned PR #12 inputs.

Fetch 7950c01b18013969c360df535b8b888dd6181dff into the local Git repository
before running. The proof sources and MIR are read from that immutable tree.
"""

from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from pathlib import Path
import os
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
REVISION = "7950c01b18013969c360df535b8b888dd6181dff"


def main():
    os.chdir(ROOT)
    scratch = ROOT / "scratch"
    scratch.mkdir(exist_ok=True)
    out = Path(tempfile.mkdtemp(prefix="duplicate-prefix-vcgen.", dir=scratch))
    archive = subprocess.check_output(["git", "archive", REVISION, "examples/duplicate_prefix"])
    subprocess.run(["tar", "-x", "-C", str(out)], input=archive, check=True)
    compatibility = ROOT / "examples/duplicate_prefix/SourceControl.patch"
    subprocess.run(["patch", "--batch", "--fuzz=0", "-p1", "-i", str(compatibility)], cwd=out, check=True)
    src = out / "examples/duplicate_prefix"
    for name in ("VCGen", "ZeroBody"):
        client = ROOT / f"examples/duplicate_prefix/{name}.lean"
        (src / client.name).write_bytes(client.read_bytes())
    artifacts = out / "duplicate_prefix"
    artifacts.mkdir()
    deps = {}
    targets = set()

    def discover(name):
        if name in deps:
            return
        contents = (src / f"{name}.lean").read_text()
        deps[name] = set(re.findall(r"^import duplicate_prefix\.(\w+)", contents, re.M))
        targets.update(re.findall(r"^import (Miri(?:\.[\w.]+)?)", contents, re.M))
        for dep in deps[name]:
            discover(dep)

    discover("ZeroBody")
    env = os.environ.copy()
    env.setdefault("ELAN_HOME", str(ROOT / ".elan"))
    env["PATH"] = str(Path(env["ELAN_HOME"]) / "bin") + os.pathsep + env["PATH"]
    subprocess.run(
        ["flock", "/tmp/lean-miri-lake-build.lock", "lake", "build", *sorted(targets)],
        env=env, check=True,
    )
    base = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], env=env, text=True).strip()
    env["LEAN_PATH"] = str(out) + os.pathsep + base
    env["LEAN_NUM_THREADS"] = "1"
    print(f"Checking {len(deps)} modules in {out}", flush=True)

    def check(name):
        log = out / f"{name}.log"
        with log.open("w") as output:
            result = subprocess.run(
                ["lean", "-j1", f"--root={src.parent}", "-o", str(artifacts / f"{name}.olean"),
                 str(src / f"{name}.lean")],
                env=env, cwd=out, stdout=output, stderr=subprocess.STDOUT,
            )
        if result.returncode:
            raise RuntimeError(f"{name} failed\n{log.read_text()}")
        return name

    with ThreadPoolExecutor(max_workers=4) as pool:
        pending = set(deps)
        running = set()
        checked = set()
        while pending or running:
            for name in sorted(pending):
                if len(running) == 4:
                    break
                if deps[name] <= checked:
                    pending.remove(name)
                    running.add(pool.submit(check, name))
            if not running:
                raise RuntimeError(f"Unresolved Lean imports: {sorted(pending)}")
            ready, running = wait(running, return_when=FIRST_COMPLETED)
            for job in ready:
                name = job.result()
                checked.add(name)
                print(f"{len(checked)}/{len(deps)} {name}", flush=True)
    print((out / "ZeroBody.log").read_text(), end="")


if __name__ == "__main__":
    main()

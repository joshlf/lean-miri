#!/usr/bin/env python3
"""Compare concrete layout algorithms with the pinned compiler and its Rand."""
import fcntl
import os
from pathlib import Path
import subprocess
import tempfile

root = Path(__file__).resolve().parents[2]
env = dict(os.environ, ELAN_HOME=str(root / ".elan"))
lake = root / ".elan/bin/lake"
rustc = root / ".rustup/toolchains/miri-exporter-8eb778d04094/bin/rustc"
version = subprocess.check_output([rustc, "--version", "--verbose"], text=True)
assert "8eb778d04094d3af4b26580cab327e0413eb1e02" in version, version
assert "host: x86_64-unknown-linux-gnu" in version, version
with open("/tmp/lean-miri-lake-build.lock", "w") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    subprocess.run([lake, "build", "Miri.Input.ConcreteEnumLayout", "Miri.Input.ConcreteCoroutineLayout", "Miri.Input.TableCore"], cwd=root, env=env, check=True)
compiler_env = dict(os.environ, LD_LIBRARY_PATH=str(rustc.parents[1] / "lib") + os.pathsep + os.environ.get("LD_LIBRARY_PATH", ""))
with tempfile.TemporaryDirectory(prefix="lean-miri-layout-") as directory:
    for name, lean, scope in [
        ("enum", "ConcreteEnum", "9 enum geometries and niche/tag controls"),
        ("coroutine", "ConcreteCoroutine", "5 coroutine layouts, all offsets and memory orders"),
        ("shuffle", "ConcreteShuffle", "36 shuffled sequences"),
        ("randomized", "ConcreteRandomized", "160 randomized aggregate layouts"),
    ]:
        binary = Path(directory) / name
        subprocess.run([rustc, "--edition=2021", root / f"tests/layout/concrete_{name}_reference.rs", "-o", binary], check=True)
        expected = subprocess.check_output([binary], text=True, env=compiler_env)
        actual = subprocess.check_output([lake, "env", "lean", "--run", f"tests/layout/{lean}.lean"], cwd=root, env=env, text=True)
        assert actual == expected, (name, expected, actual)
        print(f"Concrete layout differential passed ({scope})")

subprocess.run([lake, "env", "lean", "--run", "tests/layout/SourceTypeBoundary.lean"], cwd=root, env=env, check=True)

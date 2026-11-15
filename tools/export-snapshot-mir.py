#!/usr/bin/env python3
"""Run the normal exporter built by build-snapshot-exporter.py, without replacing tools."""
import argparse
import json
import os
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--build-manifest', type=Path, default=root / 'scratch/snapshot-exporter-target/snapshot-build.json')
p.add_argument('arguments', nargs=argparse.REMAINDER)
a = p.parse_args()
manifest = json.loads(a.build_manifest.read_text())
env = os.environ.copy()
env.update(manifest['environment'])
env['MIRI_SYSROOT'] = manifest['target_sysroot']
env.pop('LEAN_MIRI_OBSERVE_CTFE_ROOT', None)
arguments = a.arguments[1:] if a.arguments[:1] == ['--'] else a.arguments
raise SystemExit(subprocess.run([manifest['binary'], *arguments], env=env).returncode)

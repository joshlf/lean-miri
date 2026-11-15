#!/usr/bin/env python3
"""Compare one fresh export with its same-TyCtxt Miri reference and Lean run."""
import argparse
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, help='new directory under scratch/')
    parser.add_argument('--timeout', type=float, default=600)
    args = parser.parse_args()
    output = args.output.resolve()
    if not output.is_relative_to(ROOT / 'scratch') or output.exists():
        parser.error('output must be a new directory under scratch/')
    output.mkdir(parents=True)
    source = ROOT / 'tests/compiler_queries/material-guest.rs'
    document = output / 'guest.json'
    env = os.environ.copy()
    env.update(LEAN_MIRI_PREPARED_ALLOC_ID_WORLD='1', LEAN_MIRI_RUN_PREPARED_MIRI='1')
    with (output / 'export.log').open('x') as log:
        subprocess.run(['bash', 'tools/export-mir.sh', '--output', str(document),
                        '--root', 'miri_start', '--', str(source),
                        '--crate-name=material_guest', '--edition=2024', '-Cpanic=abort',
                        '-Zmir-opt-level=0', '--cfg=miri'], cwd=ROOT,
                       stdout=log, stderr=subprocess.STDOUT, check=True, timeout=args.timeout,
                       env=env)
    original = document.read_bytes()
    reference = json.loads(Path(str(document) + '.miri-reference.json').read_text())
    digest = 0xcbf29ce484222325
    for byte in original:
        digest = ((digest ^ byte) * 0x100000001b3) & ((1 << 64) - 1)
    if not (reference.get('status') == 'completed'
            and reference.get('reference', {}).get('status') == 'completed'
            and reference['reference'].get('config', {}).get('same_tcx') is True
            and reference['reference'].get('outcome') == {'kind': 'exit_zero'}
            and reference.get('snapshot_byte_length') == len(original)
            and reference.get('snapshot_fnv1a64') == f'{digest:016x}'):
        raise SystemExit('same-TyCtxt Miri did not complete with exit zero')
    with (output / 'lean.log').open('x') as log:
        run = subprocess.run([str(ROOT / '.lake/build/bin/native_runner'), str(document),
                              '--ui-source', str(source), '--ui-flags', '[]'],
                             cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
                             timeout=args.timeout, env=env)
    if document.read_bytes() != original:
        raise SystemExit('input changed during Lean execution')
    if run.returncode or 'run: finalized_exit code=0;' not in (output / 'lean.log').read_text():
        raise SystemExit(f'Lean did not complete with exit zero; see {output / "lean.log"}')
    print('PASS fresh guest: same-TyCtxt Miri and Lean finalized exit zero')


if __name__ == '__main__':
    main()

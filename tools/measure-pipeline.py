#!/usr/bin/env python3
"""Compare fresh export-to-execution trials using the same Rust input and CPU."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import signal
import statistics
import subprocess
import time


def digest(path):
    with path.open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def run_phase(command, directory, env, cpu, timeout, log, counters):
    started = time.monotonic_ns()
    with log.open('xb') as output:
        child = subprocess.Popen(command, cwd=directory, env=env, stdout=output,
                                 stderr=subprocess.STDOUT, start_new_session=True)
        before = counters(child.pid, cpu)
        peak = 0
        timed_out = False
        while True:
            snapshot = counters(child.pid, cpu)
            peak = max(peak, snapshot['process_group_rss_bytes'])
            waited, status, usage = os.wait4(child.pid, os.WNOHANG)
            if waited:
                child.returncode = os.waitstatus_to_exitcode(status)
                break
            if time.monotonic_ns() - started > timeout * 1_000_000_000:
                timed_out = True
                os.killpg(child.pid, signal.SIGKILL)
                _, status, usage = os.wait4(child.pid, 0)
                child.returncode = os.waitstatus_to_exitcode(status)
                break
            time.sleep(0.05)
        after = counters(child.pid, cpu)
    steal_before = before['selected_cpu_steal_ticks']
    steal_after = after['selected_cpu_steal_ticks']
    return {
        'command': command, 'log': str(log), 'returncode': child.returncode,
        'timed_out': timed_out,
        'wall_seconds': (time.monotonic_ns() - started) / 1e9,
        'cpu_seconds': usage.ru_utime + usage.ru_stime,
        'max_child_rss_bytes': usage.ru_maxrss * 1024,
        'peak_sampled_process_group_rss_bytes': peak,
        'selected_cpu_steal_ticks_delta': None if steal_before is None or steal_after is None
            else steal_after - steal_before,
        'cgroup_cpu_delta': {
            key: value - before['cgroup_cpu_stat'][key]
            for key, value in after['cgroup_cpu_stat'].items()
            if key in before['cgroup_cpu_stat']},
        'start_counters': before, 'end_counters': after}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--root', action='append', default=[])
    for version in ('baseline', 'candidate'):
        parser.add_argument(f'--{version}-exporter', type=Path, required=True)
        parser.add_argument(f'--{version}-runner', type=Path, required=True)
    parser.add_argument('--rustc-toolchain', type=Path, required=True)
    parser.add_argument('--miri-sysroot', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--cpu', type=int, default=min(os.sched_getaffinity(0)))
    parser.add_argument('--pairs', type=int, default=3)
    parser.add_argument('--timeout', type=float, default=1800)
    parser.add_argument('--expected-terminal', default='run: finalized_exit code=0')
    parser.add_argument('--seed', type=int, default=0)
    parser.add_argument('--profile', action='store_true')
    parser.add_argument('rustc_args', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.cpu not in os.sched_getaffinity(0) or args.pairs < 1 or args.timeout <= 0:
        parser.error('select an available CPU, positive pair count and positive timeout')
    if not 0 <= args.seed < 2**64:
        parser.error('seed must be an unsigned u64')
    source = args.source.resolve()
    directory = Path.cwd().resolve()
    toolchain = args.rustc_toolchain.resolve()
    sysroot = args.miri_sysroot.resolve()
    rustc = toolchain / 'bin/rustc'
    paths = [source, rustc] + [getattr(args, f'{version}_{role}').resolve()
        for version in ('baseline', 'candidate') for role in ('exporter', 'runner')]
    if any(not path.is_file() for path in paths) or not sysroot.is_dir():
        parser.error('source, artifact, rustc or prepared sysroot does not exist')
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=False)
    artifacts = output / 'artifacts'
    artifacts.mkdir()
    frozen = {}
    for version in ('baseline', 'candidate'):
        frozen[version] = {}
        for role in ('exporter', 'runner'):
            original = getattr(args, f'{version}_{role}').resolve()
            target = artifacts / f'{version}-{role}'
            shutil.copy2(original, target)
            frozen[version][role] = {'original': str(original), 'path': str(target),
                                     'sha256': digest(target)}
    collector = Path(__file__).with_name('measure.py')
    spec = importlib.util.spec_from_file_location('pipeline_counters', collector)
    measurement = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(measurement)
    env = os.environ.copy()
    env.update({'LEAN_NUM_THREADS': '1', 'MIRI_SYSROOT': str(sysroot),
                'LEAN_MIRI_PREPARED_ALLOC_ID_WORLD': '1',
                'PATH': str(toolchain / 'bin') + os.pathsep + env.get('PATH', ''),
                'LD_LIBRARY_PATH': str(toolchain / 'lib') + os.pathsep
                    + env.get('LD_LIBRARY_PATH', '')})
    flags = args.rustc_args[1:] if args.rustc_args[:1] == ['--'] else args.rustc_args
    result = {
        'source': str(source), 'source_sha256': digest(source), 'cwd': str(directory),
        'rustc_args': flags, 'roots': args.root, 'cpu': args.cpu,
        'lean_num_threads': 1, 'seed': args.seed, 'profile_requested': args.profile,
        'rustc': subprocess.check_output([str(rustc), '-vV'], env=env, text=True),
        'miri_sysroot': str(sysroot), 'artifacts': frozen,
        'collector_sha256': digest(Path(__file__)),
        'counter_collector_sha256': digest(collector),
        'clock_ticks_per_second': os.sysconf('SC_CLK_TCK'),
        'expected_terminal': args.expected_terminal, 'trials': []}
    for pair in range(args.pairs):
        order = ('baseline', 'candidate') if pair % 2 == 0 else ('candidate', 'baseline')
        for version in order:
            name = f'{pair + 1:02d}-{version}'
            exported = output / 'active.json'
            exported.unlink(missing_ok=True)
            command = ['taskset', '-c', str(args.cpu), frozen[version]['exporter']['path'],
                       '--output', str(exported)]
            for root in args.root:
                command.extend(['--root', root])
            command.extend(['--', str(source), *flags])
            trial = {'pair': pair + 1, 'version': version}
            started = time.monotonic_ns()
            trial['export'] = run_phase(command, directory, env, args.cpu, args.timeout,
                output / f'{name}-export.log', measurement.counters)
            if trial['export']['returncode'] == 0 and exported.is_file():
                trial['input_bytes'] = exported.stat().st_size
                command = ['taskset', '-c', str(args.cpu), frozen[version]['runner']['path'],
                           str(exported), '--seed', str(args.seed)]
                if args.profile:
                    command.append('--profile')
                trial['run'] = run_phase(command, directory, env, args.cpu, args.timeout,
                    output / f'{name}-run.log', measurement.counters)
                trial['total_wall_seconds'] = (time.monotonic_ns() - started) / 1e9
                trial['input_sha256'] = digest(exported)
                lines = (output / f'{name}-run.log').read_text().splitlines()
                terminal = [line for line in lines if line.startswith('run: ')]
                trial['lean_profile_spans'] = []
                for line in lines:
                    span = re.fullmatch(r'(decoder|preparation|prepare|startup|finalization|execution)\.(\S+) took ([0-9.]+)(ms|s)', line)
                    if span:
                        trial['lean_profile_spans'].append({
                            'provider': span[1], 'name': span[2],
                            'seconds': float(span[3]) / (1000 if span[4] == 'ms' else 1)})
                trial['terminal_line'] = terminal[-1] if terminal else None
                trial['terminal_outcome'] = terminal[-1].partition(';')[0].strip() if terminal else None
                trial['accepted'] = trial['run']['returncode'] == 0 and (
                    trial['terminal_outcome'] == args.expected_terminal)
            else:
                trial['accepted'] = False
                trial['total_wall_seconds'] = (time.monotonic_ns() - started) / 1e9
            trial['total_cpu_seconds'] = sum(trial[phase]['cpu_seconds']
                for phase in ('export', 'run') if phase in trial)
            result['trials'].append(trial)
            (output / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
            print(f"{name}: accepted={trial['accepted']} wall={trial['total_wall_seconds']:.3f}s",
                  flush=True)
    result['accepted'] = all(trial['accepted'] for trial in result['trials'])
    result['source_unchanged'] = digest(source) == result['source_sha256']
    result['accepted'] = result['accepted'] and result['source_unchanged']
    if result['accepted']:
        result['summary'] = {}
        for version in ('baseline', 'candidate'):
            summary = {}
            for metric in ('total_wall_seconds', 'total_cpu_seconds'):
                values = [trial[metric] for trial in result['trials'] if trial['version'] == version]
                summary[metric] = {'median': statistics.median(values),
                                   'minimum': min(values), 'maximum': max(values)}
            result['summary'][version] = summary
    (output / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(output / 'results.json')
    return 0 if result['accepted'] else 2


if __name__ == '__main__':
    raise SystemExit(main())

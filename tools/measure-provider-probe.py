#!/usr/bin/env python3
"""Save raw, same-CPU trial data for the live Lean/rustc provider experiment."""
import argparse
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time


def cpu_steal(cpu):
    fields = next(line.split() for line in Path('/proc/stat').read_text().splitlines()
                  if line.startswith(f'cpu{cpu} '))
    return int(fields[8])


def throttle():
    return {k: int(v) for k, v in (line.split() for line in
            Path('/sys/fs/cgroup/cpu.stat').read_text().splitlines())}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('probe')
    parser.add_argument('lean')
    parser.add_argument('script')
    parser.add_argument('fixture')
    parser.add_argument('--trials', type=int, default=5)
    args = parser.parse_args()
    cpu = min(os.sched_getaffinity(0))
    root = Path(__file__).resolve().parents[1]
    out = root / 'scratch/provider-probe'
    out.mkdir(parents=True, exist_ok=True)
    command = ['taskset', '-c', str(cpu), args.probe, args.lean, args.script, args.fixture]
    for index in range(args.trials):
        start_steal, start_throttle = cpu_steal(cpu), throttle()
        start_usage = resource.getrusage(resource.RUSAGE_CHILDREN)
        start = time.monotonic_ns()
        result = subprocess.run(command, capture_output=True, text=True, cwd=root)
        wall = time.monotonic_ns() - start
        end_usage = resource.getrusage(resource.RUSAGE_CHILDREN)
        end_steal, end_throttle = cpu_steal(cpu), throttle()
        if result.returncode:
            sys.stderr.write(result.stderr)
            raise SystemExit(f'probe trial {index + 1} exited {result.returncode}')
        probe = json.loads(result.stdout)
        if probe['query_count'] != 21 or len(probe['lean_roundtrip_ns']) != 21:
            raise SystemExit('unexpected query count')
        record = {
            'trial': index + 1, 'cpu': cpu, 'wall_ns': wall,
            'waited_process_cpu_ns': round(((end_usage.ru_utime + end_usage.ru_stime) -
                (start_usage.ru_utime + start_usage.ru_stime)) * 1e9),
            'selected_cpu_steal_ticks_delta': end_steal - start_steal,
            'cgroup_nr_throttled_delta': end_throttle['nr_throttled'] - start_throttle['nr_throttled'],
            'cgroup_throttled_usec_delta': end_throttle['throttled_usec'] - start_throttle['throttled_usec'],
            'probe': probe,
        }
        (out / f'trial-{index + 1:02d}.json').write_text(json.dumps(record, indent=2) + '\n')
        print(json.dumps({k: record[k] for k in ('trial', 'cpu', 'wall_ns',
            'selected_cpu_steal_ticks_delta', 'cgroup_throttled_usec_delta')}), flush=True)


if __name__ == '__main__':
    main()

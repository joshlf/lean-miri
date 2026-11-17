#!/usr/bin/env python3
"""Record alternating, single-CPU native retag lookup trials as JSON.

Build with `lake build profile_retag_lookup`. This is a microbenchmark, not a
whole-interpreter benchmark. Raw wall/CPU times include process startup; the
native stdout also records the timed lookup loop and a checked-result checksum.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import re
import subprocess
import time


def cpu_stat():
    return {key: int(value) for key, value in
            (line.split() for line in Path('/sys/fs/cgroup/cpu.stat').read_text().splitlines())}


def steal(cpu):
    line = next(line for line in Path('/proc/stat').read_text().splitlines()
                if line.startswith(f'cpu{cpu} '))
    return int(line.split()[8]) / os.sysconf('SC_CLK_TCK')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, default=Path('.lake/build/bin/profile_retag_lookup'))
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cpu', type=int, default=min(os.sched_getaffinity(0)))
    parser.add_argument('--trials', type=int, default=5)
    parser.add_argument('--rows', type=int, nargs='+', default=[16, 128, 1024])
    parser.add_argument('--repetitions', type=int, default=10000)
    args = parser.parse_args()
    binary = args.binary.resolve()
    records = []
    result = {'binary': str(binary), 'binary_sha256': hashlib.sha256(binary.read_bytes()).hexdigest(),
              'cpu': args.cpu, 'lean_num_threads': 1, 'clock_ticks_per_second': os.sysconf('SC_CLK_TCK'),
              'cpu_max': Path('/sys/fs/cgroup/cpu.max').read_text().strip(), 'trials': records}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    for rows in args.rows:
        for trial in range(args.trials):
            modes = ['scan', 'index', 'prepare'] if trial % 2 == 0 else ['prepare', 'index', 'scan']
            for mode in modes:
                command = ['taskset', '-c', str(args.cpu), str(binary), mode, str(rows), str(args.repetitions)]
                before_cpu = resource.getrusage(resource.RUSAGE_CHILDREN)
                before_stat, before_steal = cpu_stat(), steal(args.cpu)
                start = time.perf_counter()
                completed = subprocess.run(command, capture_output=True, text=True,
                                           env={**os.environ, 'LEAN_NUM_THREADS': '1'}, check=True)
                wall = time.perf_counter() - start
                after_cpu = resource.getrusage(resource.RUSAGE_CHILDREN)
                after_stat, after_steal = cpu_stat(), steal(args.cpu)
                match = re.fullmatch(rf'{mode} rows={rows} repetitions={args.repetitions} ns=(\d+) checksum=(\d+)\n',
                                     completed.stdout)
                cycles, remainder = divmod(args.repetitions, rows)
                expected_checksum = cycles * ((rows + 1) // 2) + (remainder + 1) // 2
                if match is None or int(match[2]) != expected_checksum:
                    raise RuntimeError(f'benchmark output/checksum mismatch: {completed.stdout!r}')
                record = {'rows': rows, 'trial': trial, 'mode': mode, 'command': command,
                          'loop_ns': int(match[1]), 'checksum': int(match[2]),
                          'wall_s': wall, 'user_s': after_cpu.ru_utime - before_cpu.ru_utime,
                          'system_s': after_cpu.ru_stime - before_cpu.ru_stime,
                          'same_cpu_steal_s': after_steal - before_steal,
                          'cgroup_delta': {key: after_stat[key] - value for key, value in before_stat.items()},
                          'stdout': completed.stdout, 'stderr': completed.stderr}
                records.append(record)
                args.output.write_text(json.dumps(result, indent=2) + '\n')
                print(completed.stdout.strip(), flush=True)


if __name__ == '__main__':
    main()

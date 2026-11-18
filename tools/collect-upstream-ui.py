#!/usr/bin/env python3
"""Require complete, non-overlapping coverage from all upstream UI shards."""
import argparse
from collections import Counter
import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tests/upstream_ui'))
from suite import LONG_CASES, case_shard, discover, source_fingerprint


def collect(root, expected, shard_count, fingerprint, dedicated_long_shard=False):
    records, errors, shards = [], [], set()
    settings = None
    result_files = sorted(root.rglob('results.jsonl'))
    for path in result_files:
        try:
            provenance = json.loads(path.with_name('provenance.json').read_text())
            index = provenance['shard_index']
            if provenance['project_source_sha256'] != fingerprint:
                errors.append(f'{path}: incompatible project source identity')
            if provenance['shard_count'] != shard_count or not 0 <= index < shard_count or index in shards:
                errors.append(f'{path}: invalid or duplicate shard {index}')
            if provenance.get('dedicated_long_shard', False) != dedicated_long_shard:
                errors.append(f'{path}: incompatible shard assignment')
            shard_settings = {key: provenance.get(key) for key in
                              ('source_lock_sha256', 'timeout', 'export_timeout', 'memory_limit', 'profile')}
            if settings is None:
                settings = shard_settings
            elif settings != shard_settings:
                errors.append(f'{path}: incompatible comparison settings')
            shards.add(index)
            rows = [json.loads(line) for line in path.read_text().splitlines() if line]
            if dedicated_long_shard and any(case_shard(row['id'], shard_count, True) != index for row in rows):
                errors.append(f'{path}: case assigned to the wrong shard')
            records.extend(rows)
            summary = json.loads(path.with_name('summary.json').read_text())
            if summary != dict(Counter(row['status'] for row in rows)):
                errors.append(f'{path}: summary does not match outcomes')
        except (OSError, ValueError, KeyError, TypeError) as error:
            errors.append(f'{path}: incomplete/invalid shard: {error}')
    observed = Counter(row['id'] for row in records)
    missing = sorted(set(expected) - observed.keys())
    unknown = sorted(observed.keys() - set(expected))
    duplicates = sorted(key for key, count in observed.items() if count != 1)
    if missing or unknown or duplicates or len(shards) != shard_count:
        errors.append('inventory/shard coverage is incomplete or overlapping')
    for row in records:
        if row['id'] in expected and row.get('reasons') != expected[row['id']]:
            errors.append(f'{row["id"]}: profile disposition changed')
        if row['id'] in expected and bool(expected[row['id']]) != (row['status'] == 'profile_unsupported'):
            errors.append(f'{row["id"]}: invalid unsupported disposition')
    counts = dict(Counter(row['status'] for row in records))
    if dedicated_long_shard and LONG_CASES - expected.keys():
        errors.append('long-running case list is inconsistent with the pinned inventory')
    complete = not errors
    return {'complete': complete, 'passed': complete and bool(counts.get('passed')) and
            all(row['status'] in ('passed', 'profile_unsupported') for row in records),
            'counts': counts, 'expected_cases': len(expected), 'observed_cases': len(records),
            'shards': sorted(shards), 'missing': missing, 'unknown': unknown,
            'duplicates': duplicates, 'errors': errors,
            'settings': settings,
            'cases': {row['id']: {key: row.get(key) for key in
                                ('status', 'path', 'revision', 'edition', 'flags', 'runtime_flags', 'errors', 'reasons')}
                      for row in records},
            'failures': [{'id': row['id'], 'status': row['status']} for row in records
                         if row['status'] not in ('passed', 'profile_unsupported')]}


def compare_baseline(current, baseline):
    if current.get('complete') is not True:
        return {'available': False, 'reason': 'current inventory is incomplete'}
    if not isinstance(baseline, dict) or baseline.get('complete') is not True or not isinstance(baseline.get('cases'), dict):
        return {'available': False, 'reason': 'no complete baseline summary with case results'}
    settings = current.get('settings')
    if not settings or not settings.get('source_lock_sha256') or settings != baseline.get('settings'):
        return {'available': False, 'reason': 'baseline source pins or execution settings differ'}
    result = {'available': True, 'baseline_commit': baseline.get('commit'),
              'new_failures': [], 'same_failure_status': [],
              'changed_failure_status': [], 'resolved': [], 'not_comparable': []}
    passing = ('passed', 'profile_unsupported')
    for case_id in sorted(current['cases']):
        case = current['cases'][case_id]
        previous = baseline['cases'].get(case_id)
        if not isinstance(previous, dict) or not isinstance(previous.get('status'), str) or any(
            previous.get(key) != value for key, value in case.items()
                                                 if key != 'status'):
            result['not_comparable'].append(case_id)
            continue
        old, new = previous.get('status'), case['status']
        if old in passing and new in passing:
            continue
        column = ('resolved' if new in passing else 'new_failures' if old in passing else
                  'same_failure_status' if old == new else 'changed_failure_status')
        result[column].append({'id': case_id, 'baseline': old, 'current': new})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('artifacts', type=Path)
    parser.add_argument('--shards', type=int, default=32)
    parser.add_argument('--dedicated-long-shard', action='store_true')
    parser.add_argument('--baseline', type=Path, help='previous full-sweep summary, when available')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.dedicated_long_shard and args.shards < 2:
        parser.error('a dedicated long shard requires at least two shards')
    report = collect(args.artifacts, {case.id: case.reasons for case in discover()},
                     args.shards, source_fingerprint(), args.dedicated_long_shard)
    report['commit'] = os.environ.get('GITHUB_SHA')
    baseline = None
    if args.baseline and args.baseline.is_file():
        try:
            baseline = json.loads(args.baseline.read_text())
        except (OSError, ValueError):
            pass
    report['baseline_comparison'] = compare_baseline(report, baseline)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: report[key] for key in ('complete', 'passed', 'counts', 'expected_cases', 'observed_cases')}))
    print(json.dumps(report['baseline_comparison']))
    return int(not report['passed'])


if __name__ == '__main__':
    raise SystemExit(main())

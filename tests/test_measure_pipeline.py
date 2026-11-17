"""Pipeline measurement controls use fake producers/runners, not MIR semantics."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


COLLECTOR = Path(__file__).resolve().parents[1] / 'tools/measure-pipeline.py'


class PipelineMeasurementTests(unittest.TestCase):
    def test_identical_input_order_and_unsuccessful_terminal(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / 'guest.rs'
            source.write_text('fn main() {}\n')
            sysroot = root / 'sysroot'
            sysroot.mkdir()
            toolchain = root / 'toolchain'
            (toolchain / 'bin').mkdir(parents=True)
            rustc = toolchain / 'bin/rustc'
            exporter = root / 'exporter'
            runner = root / 'runner'
            rustc.write_text('#!/bin/sh\necho fake-pinned-rustc\n')
            exporter.write_text(f'#!{sys.executable}\n'
                'import json, os, pathlib, sys\n'
                'args=sys.argv[1:]\n'
                'pathlib.Path(args[args.index("--output")+1]).write_text(json.dumps({\n'
                '"flags":args[args.index("--")+1:],\n'
                '"affinity":sorted(os.sched_getaffinity(0)),\n'
                '"threads":os.environ["LEAN_NUM_THREADS"]}))\n')
            runner.write_text(f'#!{sys.executable}\n'
                'import json, os, pathlib, sys\n'
                'data=json.loads(pathlib.Path(sys.argv[1]).read_text())\n'
                'assert data["affinity"] == sorted(os.sched_getaffinity(0))\n'
                'assert data["threads"] == os.environ["LEAN_NUM_THREADS"] == "1"\n'
                'print("decoder.json_parse took 12.5ms")\n'
                'print("run: finalized_exit code=0; choice_cursor=7; threads=1")\n')
            for path in (rustc, exporter, runner):
                path.chmod(0o700)
            command = [sys.executable, str(COLLECTOR), '--source', str(source),
                '--baseline-exporter', str(exporter), '--candidate-exporter', str(exporter),
                '--baseline-runner', str(runner), '--candidate-runner', str(runner),
                '--rustc-toolchain', str(toolchain), '--miri-sysroot', str(sysroot),
                '--pairs', '2', '--root', 'main', '--output-dir', str(root / 'success'),
                '--', '--crate-name=same_input', '-Cpanic=abort']
            completed = subprocess.run(command, text=True, capture_output=True, timeout=30)
            self.assertEqual(completed.returncode, 0, completed.stderr)
            result = json.loads((root / 'success/results.json').read_text())
            self.assertTrue(result['accepted'])
            self.assertFalse(result['profile_requested'])
            self.assertEqual([trial['version'] for trial in result['trials']],
                             ['baseline', 'candidate', 'candidate', 'baseline'])
            self.assertEqual(len({trial['input_sha256'] for trial in result['trials']}), 1)
            self.assertEqual(result['source_sha256'], hashlib.sha256(source.read_bytes()).hexdigest())
            self.assertEqual(result['rustc_args'], ['--crate-name=same_input', '-Cpanic=abort'])
            for trial in result['trials']:
                self.assertNotIn('--profile', trial['run']['command'])
                self.assertEqual(trial['lean_profile_spans'], [
                    {'provider': 'decoder', 'name': 'json_parse', 'seconds': 0.0125}])
                for phase in ('export', 'run'):
                    self.assertGreaterEqual(trial[phase]['cpu_seconds'], 0)
                    self.assertIn('selected_cpu_steal_ticks_delta', trial[phase])
                    self.assertIn('cgroup_cpu_delta', trial[phase])
            candidate = root / 'candidate-runner'
            candidate.write_text('#!/bin/sh\necho "run: finalized_exit code=0; choice_cursor=9"\n')
            candidate.chmod(0o700)
            command[command.index('--candidate-runner') + 1] = str(candidate)
            command[command.index(str(root / 'success'))] = str(root / 'different-cursors')
            completed = subprocess.run(command, text=True, capture_output=True, timeout=30)
            self.assertEqual(completed.returncode, 0, completed.stderr)
            command[command.index(str(root / 'different-cursors'))] = str(root / 'mismatch')
            command[command.index('--'):command.index('--')] = ['--candidate-expected-cursor', '8']
            completed = subprocess.run(command, text=True, capture_output=True, timeout=30)
            self.assertEqual(completed.returncode, 2, completed.stderr)
            command[command.index('--candidate-expected-cursor') + 1] = '9'
            candidate.write_text(f'#!{sys.executable}\nimport pathlib\np=pathlib.Path({str(root / 'count')!r})\nn=int(p.read_text())+1 if p.exists() else 0\np.write_text(str(n))\nprint("run: finalized_exit code=0; choice_cursor="+str(9+n))\n')
            command[command.index(str(root / 'mismatch'))] = str(root / 'unstable')
            completed = subprocess.run(command, text=True, capture_output=True, timeout=30)
            self.assertEqual(completed.returncode, 2, completed.stderr)
            unstable = json.loads((root / 'unstable/results.json').read_text())
            self.assertFalse(unstable['cursor_stable']['candidate'])
            command[command.index('--candidate-runner') + 1] = str(runner)
            i = command.index('--candidate-expected-cursor')
            del command[i:i+2]
            command[command.index(str(root / 'unstable'))] = str(root / 'success')
            old_hash = result['artifacts']['candidate']['runner']['sha256']
            runner.write_text('#!/bin/sh\necho "run: unsupported missing query"\n')
            self.assertEqual(hashlib.sha256(Path(result['artifacts']['candidate']['runner']['path'])
                .read_bytes()).hexdigest(), old_hash)
            command[command.index(str(root / 'success'))] = str(root / 'unsupported')
            command.insert(command.index('--'), '--profile')
            failed = subprocess.run(command, text=True, capture_output=True, timeout=30)
            self.assertEqual(failed.returncode, 2, failed.stderr)
            result = json.loads((root / 'unsupported/results.json').read_text())
            self.assertFalse(result['accepted'])
            self.assertTrue(result['profile_requested'])
            self.assertTrue(all('--profile' in trial['run']['command'] for trial in result['trials']))
            self.assertNotIn('summary', result)
            self.assertTrue(all(trial['run']['returncode'] == 0 for trial in result['trials']))
            runner.write_text('#!/bin/sh\necho "run: finalized_exit code=0; choice_cursor=7"\n')
            missing_output = root / 'missing-output-exporter'
            missing_output.write_text('#!/bin/sh\nexit 0\n')
            missing_output.chmod(0o700)
            command[command.index('--candidate-exporter') + 1] = str(missing_output)
            command[command.index(str(root / 'unsupported'))] = str(root / 'missing-output')
            failed = subprocess.run(command, text=True, capture_output=True, timeout=30)
            self.assertEqual(failed.returncode, 2, failed.stderr)
            result = json.loads((root / 'missing-output/results.json').read_text())
            self.assertFalse(result['accepted'])
            self.assertTrue(all(trial['accepted'] == (trial['version'] == 'baseline')
                                for trial in result['trials']))
            self.assertTrue(all('run' not in trial for trial in result['trials']
                                if trial['version'] == 'candidate'))


if __name__ == '__main__':
    unittest.main()

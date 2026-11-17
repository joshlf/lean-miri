"""Process-group guard shared by finite fixture entry points (no stored run ledger)."""
import os
from pathlib import Path
import signal
import subprocess
import time


def run(command, *, cwd, env, log, timeout, memory_limit, pass_fds=()):
    memory = Path('/sys/fs/cgroup/memory.current')
    def exceeded():
        return memory_limit is not None and memory.exists() and int(memory.read_text()) > memory_limit
    def details(pid=None):
        current = memory.read_text().strip() if memory.exists() else 'unavailable'
        rss = 'not started' if pid is None else 'unavailable (process exited)'
        if pid is not None:
            try:
                rss = ', '.join(line.strip() for line in Path(f'/proc/{pid}/status').read_text().splitlines()
                                if line.startswith(('VmRSS:', 'VmHWM:')))
            except OSError:
                pass
        return f'cgroup_memory_current={current}; child_rss={rss}'
    if exceeded():
        raise RuntimeError('shared cgroup memory limit exceeded before launch; NOT RUN; ' + details())
    events = Path('/sys/fs/cgroup/memory.events')
    events_before = events.read_text() if events.exists() else None
    started = time.monotonic()
    with log.open('w') as stream:
        process = subprocess.Popen(command, cwd=cwd, env=env, stdout=stream,
                                   stderr=subprocess.STDOUT, start_new_session=True, pass_fds=pass_fds)
        reason = None
        while process.poll() is None:
            if timeout is not None and time.monotonic() - started > timeout:
                reason = 'walltime limit'
            elif exceeded():
                reason = 'shared cgroup memory limit'
            if reason:
                observation = details(process.pid)
                event_counts = events.read_text().strip() if events.exists() else 'unavailable'
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                raise RuntimeError(f'{reason}; FAIL; {observation}; cgroup_events={event_counts!r}; exit={process.returncode}; log={log}')
            time.sleep(0.25)
        if events_before is not None and events.read_text() != events_before:
            raise RuntimeError(f'cgroup memory events changed during execution; inspect resource failure; {details(process.pid)}; cgroup_events_before={events_before!r}; cgroup_events_after={events.read_text()!r}; log={log}')
        return subprocess.CompletedProcess(command, process.returncode)


def source_closure(root):
    """Bind read-only execution to unchanged project sources and built OLeans."""
    import hashlib
    paths = [root / 'Miri.lean', root / 'lakefile.lean', root / 'lean-toolchain',
             *sorted((root / 'Miri').rglob('*.lean')),
             *sorted((root / '.lake/build/lib/lean').rglob('*.olean'))]
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}

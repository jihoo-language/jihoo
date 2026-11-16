#!/usr/bin/env python3
"""Exercise the container proof guard without allocating gigabytes of memory."""
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import textwrap
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
GUARD = ROOT / 'scripts/proof-supervisor.py'
WRAPPER = ROOT / 'scripts/proof-limits.sh'


class ProofLimits(unittest.TestCase):
    def test_inherited_limit_nested_wrapper_and_exit_status(self):
        code = ('import resource, subprocess, sys; '
                'assert resource.getrlimit(resource.RLIMIT_AS) == (64*1024**3,)*2; '
                f'sys.exit(subprocess.call([{str(WRAPPER)!r}, '
                f'{sys.executable!r}, "-c", "raise SystemExit(7)"]))')
        result = subprocess.run([sys.executable, str(GUARD), sys.executable, '-c', code],
                                capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 7, result.stderr)
        self.assertEqual(result.stderr.count('Proof guard: serialized job'), 1)

    def test_tree_memory_limit(self):
        # Smaller test-only threshold: each child fits, their aggregate does not.
        child = ('import os,time; '
                 'children=[os.fork() for _ in range(2)]; '
                 'memory=bytearray(40*1024**2); time.sleep(30)')
        bootstrap = (f'import runpy,sys; module=runpy.run_path({str(GUARD)!r}); '
                     'module["main"].__globals__["LIMIT"]=128*1024**2; '
                     f'sys.argv=[{str(GUARD)!r},{sys.executable!r},"-c",{child!r}]; '
                     'sys.exit(module["main"]())')
        result = subprocess.run([sys.executable, '-c', bootstrap], capture_output=True,
                                text=True, timeout=10)
        self.assertEqual(result.returncode, 137, result.stderr)
        self.assertIn('aggregate RSS', result.stderr)

    def test_signal_cleans_up_detached_descendant(self):
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / 'child'
            code = (f'import os,pathlib,time; child=os.fork(); '
                    f'os.setsid() if child == 0 else None; '
                    f'pathlib.Path({str(marker)!r}).write_text(str(os.getpid())) '
                    'if child == 0 else None; time.sleep(30)')
            job = subprocess.Popen([sys.executable, str(GUARD), sys.executable, '-c', code],
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            try:
                deadline = time.monotonic() + 5
                while not marker.exists() and time.monotonic() < deadline:
                    time.sleep(0.02)
                self.assertTrue(marker.exists(), 'Detached child did not start')
                child = int(marker.read_text())
                job.send_signal(signal.SIGTERM)
                _, errors = job.communicate(timeout=5)
                self.assertEqual(job.returncode, 143, errors)
                self.assertFalse(Path(f'/proc/{child}').exists())
            finally:
                if job.poll() is None:
                    job.kill()
                    job.communicate()

    def test_cleanup_catches_fork_after_snapshot_and_releases_lock(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            lock = root / 'lock'
            worker = textwrap.dedent('''
                import os, pathlib, sys, time
                root = pathlib.Path(sys.argv[1])
                (root / 'ready').write_text(str(os.getpid()))
                while not (root / 'fork').exists():
                    time.sleep(0.001)
                if os.fork() == 0:
                    os.setsid()
                    (root / 'late').write_text(str(os.getpid()))
                time.sleep(30)
            ''')
            bootstrap = textwrap.dedent('''
                import ctypes, pathlib, runpy, subprocess, sys, time
                guard_path, directory, worker = sys.argv[1:]
                root = pathlib.Path(directory)
                guard = runpy.run_path(guard_path)
                assert ctypes.CDLL(None).prctl(36, 1, 0, 0, 0) == 0
                subprocess.Popen([sys.executable, '-c', worker, directory],
                                 start_new_session=True)
                deadline = time.monotonic() + 5
                def wait_for(marker):
                    while not marker.exists() or not marker.read_text():
                        assert time.monotonic() < deadline, str(marker)
                        time.sleep(0.001)
                wait_for(root / 'ready')
                job = subprocess.Popen(['true'], start_new_session=True)
                job.wait()
                original_processes = guard['processes']
                def snapshot_then_fork():
                    table = original_processes()
                    if not (root / 'fork').exists():
                        (root / 'fork').touch()
                        wait_for(root / 'late')
                    return table
                guard['kill_children'].__globals__['processes'] = snapshot_then_fork
                guard['kill_children'](job)
                assert job.returncode == 0
                for marker in ('ready', 'late'):
                    pid = (root / marker).read_text()
                    assert not pathlib.Path('/proc', pid).exists(), pid
            ''')
            job = subprocess.Popen(['flock', '--no-fork', str(lock), sys.executable,
                                    '-c', bootstrap, str(GUARD), directory, worker],
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            try:
                _, errors = job.communicate(timeout=10)
                self.assertEqual(job.returncode, 0, errors)
                unlocked = subprocess.run(['flock', '--nonblock', str(lock), 'true'],
                                          timeout=5)
                self.assertEqual(unlocked.returncode, 0, 'Cleanup retained the job lock')
            finally:
                # The old implementation hangs on the late child. Clean it up
                # even when this regression fails, then let the subreaper exit.
                for marker in ('ready', 'late'):
                    path = root / marker
                    if path.exists() and path.read_text():
                        try:
                            os.kill(int(path.read_text()), signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                if job.poll() is None:
                    try:
                        job.communicate(timeout=5)
                    except subprocess.TimeoutExpired:
                        job.kill()
                        job.communicate(timeout=5)


if __name__ == '__main__':
    unittest.main()

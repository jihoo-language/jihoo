#!/usr/bin/env python3
"""Exercise the container proof guard without allocating gigabytes of memory."""
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
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


if __name__ == '__main__':
    unittest.main()

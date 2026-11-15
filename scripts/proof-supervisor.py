#!/usr/bin/env python3
"""Linux fallback for proof-limits.sh when user systemd is unavailable.

Each child inherits a 64 GiB address-space limit. A subreaper watches aggregate
process-tree RSS and kills the job at 6 GiB. Sampling is not a cgroup hard cap;
the shared flock serializes jobs across checkouts. Lean also keeps its own
4 GiB allocation limit. Exiting or interrupted jobs leave no child processes.
"""
import ctypes
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import time

LIMIT = 6 * 1024**3
ADDRESS_LIMIT = 64 * 1024**3  # Lean's runtime reserves more virtual than resident memory.
PAGE_SIZE = os.sysconf('SC_PAGE_SIZE')


def processes():
    result = {}
    for entry in Path('/proc').iterdir():
        if not entry.name.isdecimal():
            continue
        try:
            fields = (entry / 'stat').read_text().rsplit(')', 1)[1].split()
            result[int(entry.name)] = (int(fields[1]), int(fields[21]) * PAGE_SIZE)
        except (OSError, ValueError, IndexError):
            continue  # A process may exit during the snapshot.
    return result


def inside():
    try:
        supervisor = int(os.environ['JIHOO_PROOF_SUPERVISOR'])
    except (KeyError, ValueError):
        return False
    table = processes()
    current = os.getppid()
    while current in table:
        if current == supervisor:
            return True
        current = table[current][0]
    return False


def descendants(table):
    parents = {os.getpid()}
    while True:
        children = {pid for pid, (parent, _) in table.items() if parent in parents}
        expanded = parents | children
        if expanded == parents:
            return parents - {os.getpid()}
        parents = expanded


def child_limit():
    _, hard = resource.getrlimit(resource.RLIMIT_AS)
    limit = ADDRESS_LIMIT if hard == resource.RLIM_INFINITY else min(ADDRESS_LIMIT, hard)
    resource.setrlimit(resource.RLIMIT_AS, (limit, limit))


def kill_children(job):
    try:
        os.killpg(job.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    # Subreaping also retains descendants that create their own sessions.
    for pid in descendants(processes()):
        try:
            os.kill(pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    job.wait()
    while True:
        try:
            os.waitpid(-1, 0)
        except ChildProcessError:
            return


def main():
    if sys.argv[1:] == ['--inside']:
        return 0 if inside() else 1
    if len(sys.argv) < 2:
        print('usage: proof-supervisor.py COMMAND [ARGUMENT ...]', file=sys.stderr)
        return 2
    # PR_SET_CHILD_SUBREAPER keeps orphaned grandchildren in the watched tree.
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(36, 1, 0, 0, 0) != 0:
        raise OSError(ctypes.get_errno(), 'Cannot enable proof job subreaping')
    stopped = 0

    def stop(signum, _frame):
        nonlocal stopped
        stopped = signum

    for signum in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
        signal.signal(signum, stop)
    environment = dict(os.environ, JIHOO_PROOF_SUPERVISOR=str(os.getpid()))
    print('Proof guard: serialized job, 64 GiB address space per process, '
          '6 GiB sampled tree RSS.', file=sys.stderr)
    try:
        job = subprocess.Popen(sys.argv[1:], env=environment,
                               start_new_session=True, preexec_fn=child_limit)
    except OSError as error:
        print(f'Cannot start proof job: {error}', file=sys.stderr)
        return 127
    peak = 0
    try:
        while job.poll() is None:
            table = processes()
            resident = sum(table[pid][1] for pid in descendants(table))
            peak = max(peak, resident)
            if stopped:
                return 128 + stopped
            if resident >= LIMIT:
                print('Proof job exceeded 6 GiB aggregate RSS; terminating tree.',
                      file=sys.stderr)
                return 137
            time.sleep(0.1)
        return job.returncode if job.returncode >= 0 else 128 - job.returncode
    finally:
        kill_children(job)
        print(f'Proof guard: sampled peak tree RSS {peak / 1024**2:.1f} MiB.',
              file=sys.stderr)


if __name__ == '__main__':
    sys.exit(main())

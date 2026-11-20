#!/usr/bin/env python3
"""Whole mixed-program bytes checked by Loan64 typing and resource projection.

The same checked history includes actual earlier global/family prefixes.
This is regression evidence, not a full native runtime safety theorem.
"""
import argparse
from pathlib import Path
import shlex
import tempfile

from core_certificate_process import ROOT, command
from core_native_unified_correspondence import CASES as MIXED_CASES, run
from core_native_loan_typing_correspondence import CASES as LOAN_CASES, BUFFER, FUNCTION, CONTINUATION
from core_typing_producer import require

DEFAULT_CHECKER = 'lake env lean -M 4096 -j 1 -DwarningAsError=true --run CheckNativeLoanMixedProgram.lean'

CASES = dict(MIXED_CASES)
CASES.update({f'loan-{name}': (source, accepted, accepted)
              for name, (source, accepted) in LOAN_CASES.items()})
CASES.update({
    'specialized-reader-erased-owner-equality': (
        f'(def value I64 (app (lam b {BUFFER} (lend b '
        f'(lam r (Ref {BUFFER}) (app '
        '(lam0 p (Eq (free (deref r) 0) (free b 0)) (int 7)) '
        f'(refl (free b 0)))) {CONTINUATION})) (alloc 2 (int 0))))', True, True),
    'unspecialized-reader-erased-owner-equality': (
        f'(def value (pi b {BUFFER} (pi r (Ref {BUFFER}) I64)) '
        f'(lam b {BUFFER} (lam r (Ref {BUFFER}) (app '
        '(lam0 p (Eq (free (deref r) 0) (free b 0)) (int 7)) '
        '(refl (free b 0))))))', False, False),
    'dynamic-guarded-named-reader': (
        '(def value (pi n U64 (pi i U64 I64)) (lam n U64 (lam i U64 '
        '(app (lam b (Buffer n) (lend b '
        '(lam r (Ref (Buffer n)) (if-lt i n p (index (borrow b) i p) (int 0))) '
        '(lam a I64 (lam x (Buffer n) (free x a))))) (alloc n (int 7))))))', True, True),
    'nested-active-readers': (
        f'(def value I64 (app (lam b {BUFFER} (lend b '
        f'(lam r (Ref {BUFFER}) (lend (alloc 2 (int 7)) '
        f'(lam s (Ref {BUFFER}) (add (index s 0 (decide-lt 0 2)) '
        f'(index (borrow b) 0 (decide-lt 0 2)))) {CONTINUATION})) '
        f'{CONTINUATION})) (alloc 2 (int 0))))', True, True),
    'returned-owner-alias-reborrow': (
        '(def value I64 (app (lam xs (Buffer 1) (lend xs '
        '(lam r (Ref (Buffer 1)) (index r 0 (decide-lt 0 1))) '
        '(lam a I64 (lam y (Buffer 1) (lend y '
        '(lam s (Ref (Buffer 1)) (index (borrow xs) 0 (decide-lt 0 1))) '
        '(lam b I64 (lam z (Buffer 1) (free z b)))))))) '
        '(alloc 1 (int 7))))', True, True),
    'fresh-reader-two-owned-resources': (
        f'(def value U64 (app (lam b {BUFFER} (lend b '
        f'(lam r (Ref {BUFFER}) (alloc 1 (index r 0 (decide-lt 0 2)))) '
        f'(lam a (Buffer 1) (lam x {BUFFER} (free a (free x 7)))))) '
        '(alloc 2 (int 0))))', True, True),
    'loan-explicit-owner-borrow': (
        '(data Bit (zero Bit)) '
        f'(def read (pi b {BUFFER} I64) (lam b {BUFFER} '
        f'(lend b (lam r (Ref {BUFFER}) (index (borrow b) 0 (decide-lt 0 2))) {CONTINUATION}))) '
        '(def value I64 (app read (alloc 2 (int 0))))', True, True),
    'family-between-loan-definitions': (
        f'(def read (pi b {BUFFER} I64) {FUNCTION}) '
        '(data Bit (zero Bit)) (def value I64 (app read (alloc 2 (int 0))))', True, True),
    'loan-function-after-family': (
        '(data Bit (zero Bit)) '
        f'(def read (pi b {BUFFER} I64) {FUNCTION}) '
        '(def value I64 (app read (alloc 2 (int 0))))', True, True),
    'boxed-value-after-loan-function': (
        f'(def read (pi b {BUFFER} I64) {FUNCTION}) '
        '(data Box (box (pi b (Buffer 2) Box))) '
        '(def value Box (box (alloc 2 (int 0))))', True, True),
    'pure-mixed-admission': (
        '(def freed_eq (pi x U64 (Eq (free (alloc 1 (int 0)) x) x)) (lam x U64 (refl x)))\n'
        '(def inherited (pi x U64 (Eq (free (alloc 1 (int 0)) x) x)) freed_eq)\n'
        '(data Bit (Off Bit) (On (pi x U64 Bit)))\n'
        '(def applied (Eq (free (alloc 1 (int 0)) 0) 0) (app inherited 0))\n'
        '(def prior (pi x U64 (pi0 p (Eq x x) (Eq x x))) '
        '(lam x U64 (lam0 p (Eq (free (alloc 1 (int 0)) x) x) (refl x))))\n'
        '(def nested (pi y U64 (Eq y y)) (lam y U64 (app (app prior y) (refl y))))\n'
        '(def scalar I64 (int 7))', True, False),
})


def execute(args, output):
    run(shlex.split(args.compiler), shlex.split(args.checker), output, args.exporter,
        cases=CASES, acknowledgement=b'exact native loan mixed program accepted\n')
    # The raw checker above rejects these bytes. Replay exactly the same bytes
    # through the extension that checks ghost aliases at their stored types.
    payload = (output / 'pure-mixed-admission.snapshot').read_bytes()
    result = command([*shlex.split(args.pure_checker), '64', '128', '--pure'], payload, cwd=ROOT / 'proofs')
    (output / 'pure-mixed-admission.pure-checker.stdout').write_bytes(result.stdout)
    (output / 'pure-mixed-admission.pure-checker.stderr').write_bytes(result.stderr)
    require(result.returncode == 0 and result.stdout == b'exact native pure mixed program accepted\n',
            f'pure mixed admission changed: {(result.stdout + result.stderr)!r}')
    print('native pure mixed correspondence: pure admission accepted the exact native snapshot bytes')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--exporter', type=Path)
    parser.add_argument('--checker', default=DEFAULT_CHECKER)
    parser.add_argument('--pure-checker', default=DEFAULT_CHECKER)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output:
        execute(args, args.output)
    else:
        with tempfile.TemporaryDirectory(prefix='native-loan-mixed-') as directory:
            execute(args, Path(directory))

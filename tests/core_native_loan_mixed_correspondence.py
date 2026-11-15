#!/usr/bin/env python3
"""Whole mixed-program bytes checked by Loan64 typing and resource projection.

The same checked history includes actual earlier global/family prefixes.
This is regression evidence, not a full native runtime safety theorem.
"""
import argparse
from pathlib import Path
import shlex
import tempfile

from core_native_unified_correspondence import CASES as MIXED_CASES, run
from core_native_loan_typing_correspondence import CASES as LOAN_CASES, BUFFER, FUNCTION

CASES = dict(MIXED_CASES)
CASES.update({f'loan-{name}': (source, accepted, accepted)
              for name, (source, accepted) in LOAN_CASES.items()})
CASES.update({
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
})


def execute(args, output):
    run(shlex.split(args.compiler), shlex.split(args.checker), output, args.exporter,
        cases=CASES, acknowledgement=b'exact native loan mixed program accepted\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--exporter', type=Path)
    parser.add_argument('--checker', default='lake env lean -M 4096 -j 1 -DwarningAsError=true --run CheckNativeLoanMixedProgram.lean')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output:
        execute(args, args.output)
    else:
        with tempfile.TemporaryDirectory(prefix='native-loan-mixed-') as directory:
            execute(args, Path(directory))

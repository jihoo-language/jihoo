#!/usr/bin/env python3
"""Exact native programs versus verified sequential loan-aware global typing.

These are regression comparisons, not a native checker refinement theorem.
Runtime quantities, families and heap safety remain separate from this gate.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shlex
import tempfile

from core_certificate_process import ROOT, command, success
from core_native_family_correspondence import Family, Program
from core_native_loan_typing_correspondence import CASES as LOAN_CASES, BUFFER, FUNCTION
from core_typing_producer import require

CASES = dict(LOAN_CASES)
CASES.update({
    'empty': ('', True),
    'global-chain': ('(def first U64 7) (def second U64 first) '
                     '(def third (Eq second 7) (refl 7))', True),
    'global-type-alias': ('(def Scalar (Type 0) U64) '
                          '(def identity (pi x Scalar Scalar) (lam x Scalar x)) '
                          '(def value Scalar (app identity 7))', True),
    'global-proof-alias': ('(def evidence (Eq 7 7) (refl 7)) '
                           '(def value (Eq 7 7) evidence)', True),
    'sequential-loan-call': (f'(def read (pi b {BUFFER} I64) {FUNCTION}) '
                            '(def value I64 (app read (alloc 2 (int 0))))', True),
    'wrong-global-result': ('(def first U64 7) (def second I64 first)', False),
    'false-global-evidence': ('(def first U64 7) '
                              '(def evidence (Eq first 8) (refl first))', False),
})


def run(args):
    output = args.output
    output.mkdir(parents=True, exist_ok=True)
    exporter = args.exporter
    if exporter is None:
        exporter = output / 'core-native-snapshots'
        success(command([*shlex.split(args.compiler), 'build', '-O2', '-I', 'compiler',
                         'tests/core_native_snapshots.jh', '-o', exporter]))
    observations, checks, retained = [], [], {}

    def check(name, payload, accepted, *, fuel=64, declarations=None):
        (output / f'{name}.snapshot').write_bytes(payload)
        result = command([*shlex.split(args.checker), str(fuel)], payload, cwd=ROOT / 'proofs')
        (output / f'{name}.checker.stdout').write_bytes(result.stdout)
        (output / f'{name}.checker.stderr').write_bytes(result.stderr)
        require(result.returncode == (0 if accepted else 1),
                f'{name}: checker outcome changed: {result.stdout!r} {result.stderr!r}')
        if accepted:
            expected = f'exact native loan program typing accepted: {declarations} declarations\n'
            require(result.stdout == expected.encode(), f'{name}: missing exact-byte acknowledgement')
        checks.append({'case': name, 'accepted': accepted, 'fuel': fuel,
                       'sha256': hashlib.sha256(payload).hexdigest()})

    for name, (source, accepted) in CASES.items():
        (output / f'{name}.core').write_text(source + '\n')
        result = command([exporter, 'families'], source.encode())
        (output / f'{name}.native.stderr').write_bytes(result.stderr)
        require(result.returncode == (0 if accepted else 1),
                f'{name}: native outcome changed: {result.stderr!r}')
        observations.append({'case': name, 'native_accepted': accepted})
        if accepted:
            program = Program.read(result.stdout)
            retained[name] = result.stdout
            check(name, result.stdout, True, declarations=len(program.definitions))

    def mutate(name, base, edit):
        program = Program.read(retained[base])
        edit(program)
        check(name, program.encode(), False)

    def self_reference(program):
        index = next(i for i, (tag, _, _) in enumerate(program.nodes) if tag == 1)
        program.nodes[index] = (1, (1,), ())

    def unbound(program):
        index = next(i for i, (tag, _, _) in enumerate(program.nodes) if tag == 0)
        program.nodes[index] = (0, (99,), ())

    mutate('mutation-self-reference', 'sequential-loan-call', self_reference)
    mutate('mutation-forward-reference', 'sequential-loan-call',
           lambda p: p.definitions.reverse())
    mutate('mutation-unbound-variable', 'sequential-loan-call', unbound)
    mutate('mutation-unreachable-malformed', 'sequential-loan-call',
           lambda p: p.nodes.append((17, (), ())))
    mutate('mutation-missing-root', 'sequential-loan-call',
           lambda p: p.definitions.append((0, len(p.nodes) + 1)))
    mutate('mutation-family-table', 'literal',
           lambda p: p.families.append(Family(1, 0, 0, 0, [p.definitions[0][0]])))
    check('mutation-trailing-byte', retained['sequential-loan-call'] + b'\n', False)
    check('typing-fuel-exhausted', retained['sequential-loan-call'], False, fuel=0)
    (output / 'manifest.json').write_text(json.dumps({
        'claim': __doc__,
        'core_sha256': hashlib.sha256((ROOT / 'compiler/core.jh').read_bytes()).hexdigest(),
        'cases': observations, 'checks': checks,
    }, indent=2) + '\n')
    print(f'Native loan program typing: {len(observations)} source fixtures and '
          f'{len(checks)} exact-byte checks passed')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--exporter', type=Path)
    parser.add_argument('--checker', default='lake env lean -M 4096 -j 1 -DwarningAsError=true --run CheckNativeLoanProgram.lean')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output:
        run(args)
    else:
        with tempfile.TemporaryDirectory(prefix='native-loan-program-') as directory:
            args.output = Path(directory)
            run(args)

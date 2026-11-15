#!/usr/bin/env python3
"""Exact native single-declaration bytes versus verified loan-aware typing.

The Lean entry point checks types and active reader permissions. It does not
claim runtime quantities, heap safety or general mixed-program admission.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shlex
import tempfile

from core_certificate_process import ROOT, command, success
from core_native_family_correspondence import Program
from core_typing_producer import require

BUFFER = '(Buffer 2)'
READER = f'(lam r (Ref {BUFFER}) (index r 0 (decide-lt 0 2)))'
CONTINUATION = f'(lam a I64 (lam x {BUFFER} (free x a)))'
FUNCTION = f'(lam b {BUFFER} (lend b {READER} {CONTINUATION}))'
CASES = {
    'literal': ('(def value I64 (int 7))', True),
    'dependent-reader': (f'(def value (pi b {BUFFER} I64) {FUNCTION})', True),
    'generic-allocated-owner': (
        f'(def value I64 (lend (alloc 2 (int 0)) {READER} {CONTINUATION}))', True),
    'closed-dependent-call': (f'(def value I64 (app {FUNCTION} (alloc 2 (int 0))))', True),
    'code-borrow-without-reader': (f'(def value (Ref {BUFFER}) (borrow (alloc 2 (int 0))))', False),
    'reader-reference-escapes': (
        f'(def value (pi b {BUFFER} I64) (lam b {BUFFER} '
        f'(lend b (lam r (Ref {BUFFER}) r) (lam a (Ref {BUFFER}) '
        f'(lam x {BUFFER} (free x (int 0)))))))', False),
    'borrow-after-reader-exit': (
        f'(def value (pi b {BUFFER} I64) (lam b {BUFFER} (lend b {READER} '
        f'(lam a I64 (lam x {BUFFER} (free x '
        '(index (borrow x) 0 (decide-lt 0 2))))))))', False),
    'wrong-reader-domain': (
        f'(def value (pi b {BUFFER} I64) (lam b {BUFFER} '
        f'(lend b (lam r (Ref (Buffer 1)) (int 0)) {CONTINUATION})))', False),
    'nonowned-lender': (f'(def value I64 (lend 0 {READER} {CONTINUATION}))', False),
}


def run(args):
    output = args.output
    output.mkdir(parents=True, exist_ok=True)
    exporter = args.exporter
    if exporter is None:
        exporter = output / 'core-native-snapshots'
        success(command([*shlex.split(args.compiler), 'build', '-O2', '-I', 'compiler',
                         'tests/core_native_snapshots.jh', '-o', exporter]))
    observations, checks, retained = [], [], {}

    def check(name, payload, expected, fuel='64'):
        (output / f'{name}.snapshot').write_bytes(payload)
        result = command([*shlex.split(args.checker), fuel], payload, cwd=args.proofs)
        (output / f'{name}.checker.stdout').write_bytes(result.stdout)
        (output / f'{name}.checker.stderr').write_bytes(result.stderr)
        require(result.returncode == (0 if expected else 1),
                f'{name}: checker outcome changed: {result.stdout!r} {result.stderr!r}')
        if expected:
            require(result.stdout == b'exact native loan typing accepted\n', f'{name}: acknowledgement')
        checks.append({'case': name, 'accepted': expected, 'fuel': int(fuel),
                       'sha256': hashlib.sha256(payload).hexdigest()})

    for name, (source, expected) in CASES.items():
        (output / f'{name}.core').write_text(source + '\n')
        result = command([exporter, 'families'], source.encode())
        (output / f'{name}.native.stderr').write_bytes(result.stderr)
        require(result.returncode == (0 if expected else 1),
                f'{name}: native outcome changed: {result.stderr!r}')
        observations.append({'case': name, 'native_accepted': expected})
        if expected:
            Program.read(result.stdout)
            retained[name] = result.stdout
            check(name, result.stdout, True)

    def mutate(name, base, edit):
        program = Program.read(retained[base])
        edit(program)
        check(name, program.encode(), False)

    def unbound_owner(program):
        index = next(i for i, (tag, _, _) in enumerate(program.nodes) if tag == 34)
        tag, payload, (_, reader, continuation) = program.nodes[index]
        variable = next(i for i, (tag, payload, _) in enumerate(program.nodes)
                        if tag == 0 and payload == (0,))
        program.nodes[index] = (tag, payload, (variable, reader, continuation))

    def erased_reader(program):
        _, _, (_, reader, _) = next(node for node in program.nodes if node[0] == 34)
        tag, _, refs = program.nodes[reader]
        require(tag == 45, 'reader lambda expected')
        program.nodes[reader] = (tag, (1,), refs)

    def unscoped_again(program):
        def append(tag, payload, refs):
            program.nodes.append((tag, tuple(payload), tuple(refs)))
            return len(program.nodes) - 1

        declared, root = program.definitions[0]
        root_tag, root_flags, (domain, lend) = program.nodes[root]
        lend_tag, lend_flags, (owner, reader, continuation) = program.nodes[lend]
        cont_tag, cont_flags, (first, inner) = program.nodes[continuation]
        inner_tag, inner_flags, (again, body) = program.nodes[inner]
        scalar = next(i for i, (tag, _, _) in enumerate(program.nodes) if tag == 4)
        unbound = append(0, (99,), ())
        constant_type = append(45, (0,), (scalar, again))
        hidden_unbound = append(46, (), (constant_type, unbound))
        inner = append(inner_tag, inner_flags, (hidden_unbound, body))
        continuation = append(cont_tag, cont_flags, (first, inner))
        lend = append(lend_tag, lend_flags, (owner, reader, continuation))
        program.definitions[0] = (declared, append(root_tag, root_flags, (domain, lend)))

    mutate('mutation-unbound-owner', 'generic-allocated-owner', unbound_owner)
    mutate('mutation-erased-reader', 'dependent-reader', erased_reader)
    mutate('mutation-erased-annotation-unbound', 'dependent-reader', unscoped_again)
    check('mutation-trailing-byte', retained['dependent-reader'] + b'\n', False)
    check('typing-fuel-exhausted', retained['closed-dependent-call'], False, '0')
    (output / 'manifest.json').write_text(json.dumps({
        'claim': __doc__,
        'core_sha256': hashlib.sha256((ROOT / 'compiler/core.jh').read_bytes()).hexdigest(),
        'cases': observations, 'checks': checks,
    }, indent=2) + '\n')
    print(f'Native loan typing: {len(observations)} source fixtures and {len(checks)} exact-byte checks passed')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='jihoo')
    parser.add_argument('--exporter', type=Path)
    parser.add_argument('--checker', default='lake env lean -M 4096 -j 1 -DwarningAsError=true --run CheckNativeLoanTyping.lean')
    parser.add_argument('--proofs', type=Path, default=ROOT / 'proofs')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output:
        run(args)
    else:
        with tempfile.TemporaryDirectory(prefix='native-loan-typing-') as directory:
            args.output = Path(directory)
            run(args)

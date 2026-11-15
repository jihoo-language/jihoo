#!/usr/bin/env python3
"""Actual native Lend admission versus the full Loan64 source/resource gate.

The strict byte entry admits one closed declaration with no families. It proves
original source scope, full loan-aware typing and recursive quantities. Heap
execution, selected computed-callback contracts and native allocator refinement
remain separate obligations.
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
CONT = f'(lam a I64 (lam x {BUFFER} (free x a)))'
FIRST_READER = f'(lam r (Ref {BUFFER}) (alloc 0 (int -1)))'
FIRST_CONT = f'(lam a (Buffer 0) (lam x {BUFFER} (free a (free x (int 7)))))'

def closed(reader=READER, continuation=CONT):
    return f'(def value I64 (app (lam b {BUFFER} (lend b {reader} {continuation})) (alloc 2 (int 0))))'

CASES = {
    'literal': ('(def value I64 (int 7))', True),
    'dependent-function': (f'(def value (pi b {BUFFER} I64) (lam b {BUFFER} (lend b {READER} {CONT})))', True),
    'closed-dependent-call': (closed(), True),
    'generic-allocated-owner': (f'(def value I64 (lend (alloc 2 (int 0)) {READER} {CONT}))', True),
    'original-owner-alias': (closed(continuation=f'(lam a I64 (lam x {BUFFER} (free b a)))'), True),
    'distinct-owned-reader-result': (closed(FIRST_READER, FIRST_CONT), True),
    'computed-callbacks': (closed(f'(if-lt 0 1 p {READER} {READER})', f'(if-eq 0 0 p {CONT} {CONT})'), True),
    'both-owner-aliases': (closed(continuation=f'(lam a I64 (lam x {BUFFER} (free x (free b a))))'), False),
    'reader-consumes-owner': (closed(f'(lam r (Ref {BUFFER}) (free b (int 0)))'), False),
    'dropped-owned-reader-result': (closed(FIRST_READER, f'(lam a (Buffer 0) (lam x {BUFFER} (free x (int 7))))'), False),
    'duplicated-owned-reader-result': (closed(FIRST_READER, f'(lam a (Buffer 0) (lam x {BUFFER} (free a (free a (free x (int 7))))))'), False),
    'borrow-after-reader-exit': (closed(continuation=f'(lam a I64 (lam x {BUFFER} (free x (index (borrow x) 0 (decide-lt 0 2)))))'), False),
}

def run(args):
    args.output.mkdir(parents=True, exist_ok=True)
    exporter = args.exporter
    if exporter is None:
        exporter = args.output / 'core-native-snapshots'
        success(command([*shlex.split(args.compiler), 'build', '-O2', '-I', 'compiler',
                         'tests/core_native_snapshots.jh', '-o', exporter]))
    observations, checks, retained = [], [], {}

    def check(name, payload, expected, fuel='64', quantity='128'):
        (args.output / f'{name}.snapshot').write_bytes(payload)
        result = command([*shlex.split(args.checker), fuel, quantity], payload, cwd=args.proofs)
        (args.output / f'{name}.checker.stdout').write_bytes(result.stdout)
        (args.output / f'{name}.checker.stderr').write_bytes(result.stderr)
        require(result.returncode == (0 if expected else 1),
                f'{name}: checker outcome changed: {result.stdout!r} {result.stderr!r}')
        if expected:
            require(result.stdout == b'exact native loan quantity accepted\n', f'{name}: acknowledgement')
        checks.append({'case':name, 'accepted':expected, 'typing_fuel':int(fuel),
                       'quantity_fuel':int(quantity), 'sha256':hashlib.sha256(payload).hexdigest()})

    for name, (source, expected) in CASES.items():
        (args.output / f'{name}.core').write_text(source + '\n')
        result = command([exporter, 'families'], source.encode())
        (args.output / f'{name}.native.stderr').write_bytes(result.stderr)
        require(result.returncode == (0 if expected else 1),
                f'{name}: native outcome changed: {result.stderr!r}')
        observations.append({'case':name, 'native_accepted':expected})
        if expected:
            Program.read(result.stdout)
            retained[name] = result.stdout
            check(name, result.stdout, True)

    def mutate(name, edit):
        program = Program.read(retained['dependent-function'])
        edit(program)
        check(name, program.encode(), False)

    def edit_body(program, reader_edit=None, continuation_edit=None):
        def append(tag, payload=(), refs=()):
            program.nodes.append((tag, tuple(payload), tuple(refs)))
            return len(program.nodes)-1
        declared, root = program.definitions[0]
        root_tag, root_flags, (domain, lend) = program.nodes[root]
        lend_tag, lend_flags, (owner, reader, continuation) = program.nodes[lend]
        if reader_edit:
            tag, flags, (ref_domain, body) = program.nodes[reader]
            reader = append(tag, flags, (ref_domain, reader_edit(append)))
        if continuation_edit:
            tag, flags, (first, inner) = program.nodes[continuation]
            inner_tag, inner_flags, (again, body) = program.nodes[inner]
            again, body = continuation_edit(append, again, body)
            inner = append(inner_tag, inner_flags, (again, body))
            continuation = append(tag, flags, (first, inner))
        lend = append(lend_tag, lend_flags, (owner, reader, continuation))
        program.definitions[0] = (declared, append(root_tag, root_flags, (domain, lend)))

    def duplicate(append, again, body):
        returned, original, first = [append(0, (index,)) for index in [0,2,1]]
        return again, append(31, (), (returned, append(31, (), (original, first))))
    mutate('mutation-both-owner-aliases', lambda p: edit_body(p, continuation_edit=duplicate))
    mutate('mutation-reader-consumes-owner', lambda p: edit_body(p,
        reader_edit=lambda add: add(31, (), (add(0,(1,)), add(48,(0,0))))))

    def unscoped(program):
        scalar = next(i for i,(tag,_,_) in enumerate(program.nodes) if tag==4)
        def hidden(append, again, body):
            unbound=append(0,(99,))
            constant=append(45,(1,),(scalar,again))
            return append(46,(),(constant,unbound)),body
        edit_body(program, continuation_edit=hidden)
    mutate('mutation-unscoped-converted-annotation', unscoped)
    check('mutation-trailing-byte', retained['dependent-function']+b'\n', False)
    check('typing-fuel-exhausted', retained['closed-dependent-call'], False, '0')
    check('quantity-fuel-exhausted', retained['closed-dependent-call'], False, quantity='0')
    (args.output/'manifest.json').write_text(json.dumps({
        'claim':__doc__, 'core_sha256':hashlib.sha256((ROOT/'compiler/core.jh').read_bytes()).hexdigest(),
        'exporter_sha256':hashlib.sha256(exporter.read_bytes()).hexdigest(),
        'cases':observations,'checks':checks},indent=2)+'\n')
    print(f'Native loan quantities: {len(observations)} source fixtures and {len(checks)} exact-byte checks passed')

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler',default='jihoo')
    parser.add_argument('--exporter',type=Path)
    parser.add_argument('--checker',default='lake env lean -M 4096 -j 1 -DwarningAsError=true --run CheckNativeLoanQuantity.lean')
    parser.add_argument('--proofs',type=Path,default=ROOT/'proofs')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    if args.output:run(args)
    else:
        with tempfile.TemporaryDirectory(prefix='native-loan-quantity-') as directory:
            args.output=Path(directory)
            run(args)

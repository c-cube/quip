#!/usr/bin/env python

import os, sys, subprocess
from typing import Iterator, Tuple

static_files = [
    ('test-010.quip.gz', 'test-010.smt2'),
]

proof_dirs = [
    'out-proofs-2021-12-27T20:48',
]

def green(s: str) -> str:
    return '\x1b[1;32m' + s + '\x1b[0m'

def red(s: str) -> str:
    return '\x1b[1;31m' + s + '\x1b[0m'

def gen_files(curdir: str) -> Iterator[Tuple[str, str]]:
    "List all pairs (proof,problem) to check"
    for (file, pb) in static_files:
        file = os.path.join(curdir, file)
        pb = os.path.join(curdir, pb)
        yield (file, pb)
    for dir in proof_dirs:
        d = os.listdir(os.path.join(curdir, dir))
        proofs = set(x for x in d if x.endswith('..quip.gz'))
        for proof in proofs:
            proof = os.path.join(curdir, dir, proof)
            pb = proof.rstrip('..quip.gz').replace('proof-', 'pb-')
            if os.path.isfile(pb):
                yield (proof, pb)

def check(file: str, pb: str) -> bool:
    p = subprocess.Popen(['./quip.sh', 'check', file, f'--problem={pb}'], stdout=subprocess.PIPE)
    errcode = p.wait()
    #if p.stdout is not None:
    #    out = p.stdout.read()
    #else:
    #    out = b''
    ok = (errcode == 0)
    print(green('OK') if ok else red('FAIL'))
    return ok

def main() -> None:
    curdir = os.path.dirname(sys.argv[0])
    bad: set[str] = set()
    for (file, pb) in gen_files(curdir):
        print(f'proof={file} problem={pb}… ', end='', flush=False)
        if not check(file=file, pb=pb):
            bad.add(file)

    ok = len(bad) == 0
    if ok:
        print(green('OK'))
    else:
        print(red('FAIL'))
        for f in bad: print(f'bad: {f}')
        sys.exit(1)


if __name__ == '__main__':
    main()

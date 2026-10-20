#!/usr/bin/env python3
"""Does the finder derive the natural rules under ctrl?

NaturalP's ctrl lemma (NaturalP/CtrlBounded) proves each rule under
ctrl from completeness on at most five wires (eight for ctrl₁).  These
are fixed identities: the rule's gates replaced by their controlled
gadgets (`../ctrlcheck.py`, checked against the controlled operator),
on one wire more than the rule.  Rules on at most three wires give
identities on at most four wires; the four-wire rules give five.

    python3 -B ctrltest.py [limit] [--no-r4] [--only N]
"""
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))
import contextlib, io
with contextlib.redirect_stdout(io.StringIO()):
    import ctrlcheck as CC          # prints its own check when imported
import finder as F
from classical3 import CLASSICAL_RULES
from natural3 import TOFFOLI_CNOT, HADAMARD_RULES
from check4 import FOUR

ARITY = {'X': 1, 'CX': 2, 'CXr': 2, 'SW': 2, 'HH': 2, 'CCX': 3}


def gates(text):
    if '=' in text:
        l, r = text.split('=')
        names = l.split() + list(reversed(r.split()))
    else:
        names = text.split()
    out = []
    for x in names:
        if x.startswith('HH') and len(x) == 4:          # HH ab: as swaps around an adjacent HH
            a, b = int(x[2]), int(x[3])
            sw = [('SW', i) for i in range(b - 1, a, -1)]
            out += sw + [('HH', a)] + list(reversed(sw))
            continue
        base = x.rstrip('0123456789')
        i = int(x[len(base):])
        if base == 'CXr':
            out += [('HH', i), ('CX', i), ('HH', i)]
        else:
            out.append((base, i))
    return out


def width(gs):
    return max(i + ARITY[k] for k, i in gs)


def controlled(gs, m):
    out = []
    for k, i in gs:
        w = CC.CTRL(k, i, m)
        if w is None:
            return None
        out += list(w)
    return out


def main():
    r4 = '--no-r4' not in sys.argv
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    limit = int(args[0]) if args else 30_000
    only = int(sys.argv[sys.argv.index('--only') + 1]) if '--only' in sys.argv else None
    texts = CLASSICAL_RULES + [TOFFOLI_CNOT['commutator']] + HADAMARD_RULES + FOUR
    if r4:
        texts = texts + [F.R4_TEXT]
    alph = {}
    tot = ok = 0
    for t in texts:
        gs = gates(t)
        m = width(gs)
        c = controlled(gs, m)
        if c is None:
            m += 1
            c = controlled(gs, m)
        n = max(m + 1, 4)
        if only and n != only:
            continue
        if n not in alph:
            alph[n] = F.Alphabet(n, r4=r4)
        A = alph[n]
        word = tuple(A.adj(f'{k}{i}') for k, i in c)
        assert A.is_identity(word), t
        t0 = time.time()
        res = A.derive(word, limit)
        tot += 1
        ok += res is not None
        print(f'{n} wires, {len(word):3} letters: {"derived" if res else "NOT derived"} '
              f'{round(time.time() - t0, 1)} s   ctrl({t})', flush=True)
    print(ok, 'of', tot, 'derived')


if __name__ == '__main__':
    main()

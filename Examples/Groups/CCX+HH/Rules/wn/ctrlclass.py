#!/usr/bin/env python3
"""The classical rules under ctrl, restated as classical identities.

Each controlled gadget of NaturalP/Ctrl is replaced by the classical
word it equals: X on wire t by the CNOT from wire 0, a CNOT by a
Toffoli with wire 0 as a further control, the swap by the Fredkin gate
CX · CCX · CX, and a Toffoli by Barenco's four Toffolis borrowing a
wire (the first idle one).  Each replacement is an identity on at most
five wires; the controlled rule becomes a classical identity on one or
two wires more than the rule.  Does the finder derive them?

    python3 -B ctrlclass.py [limit]
"""
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))
import finder as F
from classical3 import CLASSICAL_RULES
from natural3 import TOFFOLI_CNOT
from check4 import FOUR

ARITY = {'X': 1, 'CX': 2, 'CXr': 2, 'SW': 2, 'CCX': 3}


def gates(text):
    """(kind, wires) of a rule's relator, wires of the rule itself."""
    if '=' in text:
        l, r = text.split('=')
        names = l.split() + list(reversed(r.split()))
    else:
        names = text.split()
    out = []
    for x in names:
        base = x.rstrip('0123456789')
        i = int(x[len(base):])
        out.append({'X': ('X', (i,)), 'CX': ('CX', (i + 1, i)), 'CXr': ('CX', (i, i + 1)),
                    'SW': ('SW', (i, i + 1)), 'CCX': ('CCX', (i, i + 1, i + 2))}[base])
    return out


def controlled(gs, m):
    """The controlled relator on m + 1 wires (control 0, the rule on
    1 … m), each gate replaced by a classical word; letters as tuples."""
    out = []
    for k, ws in gs:
        w = [x + 1 for x in ws]
        if k == 'X':
            out.append(('CX', 0, w[0]))
        elif k == 'CX':
            c, t = w
            out.append(('CCX', t, min(0, c), max(0, c)))
        elif k == 'SW':
            a, b = w
            out += [('CX', b, a), ('CCX', b, 0, a), ('CX', b, a)]
        else:
            t, c1, c2 = w
            spare = next(x for x in range(1, m + 1) if x not in w)
            t1 = ('CCX', t, 0, spare)
            t2 = ('CCX', spare, c1, c2)
            out += [t1, t2, t1, t2]
    return out


def norm(l):
    if l[0] == 'CCX':
        return ('CCX', l[1], min(l[2], l[3]), max(l[2], l[3]))
    return l


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    limit = int(args[0]) if args else 30_000
    texts = CLASSICAL_RULES + [TOFFOLI_CNOT['commutator']] + FOUR
    alph = {}
    tot = ok = 0
    for t in texts:
        gs = gates(t)
        width = max(max(ws) + 1 for _, ws in gs)
        m = width + (1 if any(k == 'CCX' for k, _ in gs) else 0)
        n = m + 1
        if n not in alph:
            alph[n] = F.Alphabet(n, placed='--adjacent' not in sys.argv)
        A = alph[n]
        word = tuple(A.INDEX[norm(l)] for l in controlled(gs, m))
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

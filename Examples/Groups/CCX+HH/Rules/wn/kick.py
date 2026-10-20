#!/usr/bin/env python3
"""The Toffoli kickbacks on four wires.

A Toffoli conjugating a diagonal monomial on its target kicks back a
CCZ on the other wires: [CCX(t;a,b), CCZ(t,a,b)] = CZ(a,b) is R4, and
with a fourth wire c,

    K_CZ :  [CCX(t;a,b), CZ(t,c)]    = CCZ(a,b,c)
    K_CCZ:  [CCX(t;a,b), CCZ(t,a,c)] = CCZ(a,b,c).

The finder (rules at every placement, R4, short subgroup identities)
does not derive these.  Here: with one of them as a further rule at
every placement, is the other derived?

    python3 -B kick.py CZ|CCZ [limit]
"""
import itertools
import sys
import time
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import finder as F


def z(A, wires):
    """A circuit for the monomial gate on `wires` (2 or 3 of them)."""
    t = wires[-1]
    u = next(x for x in range(4) if x not in wires)
    hh = A.INDEX[('HH', min(t, u), max(t, u))]
    if len(wires) == 2:
        core = A.INDEX[('CX', wires[0], t)]
    else:
        core = A.INDEX[('CCX', t, min(wires[0], wires[1]), max(wires[0], wires[1]))]
    return (hh, core, hh)


def kick(A, kind, t, a, b, c):
    """The kickback relator for the Toffoli (t; a, b) and the fourth wire c."""
    x = A.INDEX[('CCX', t, min(a, b), max(a, b))]
    m = z(A, (t, c)) if kind == 'CZ' else z(A, (t, a, c))
    rhs = z(A, tuple(sorted((a, b, c))))
    # x m x = m rhs, as the relator x m x rev(rhs) rev(m)
    return (x,) + m + (x,) + tuple(reversed(rhs)) + tuple(reversed(m))


def main():
    rule = sys.argv[1]
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 30_000
    other = 'CCZ' if rule == 'CZ' else 'CZ'
    base = F.Alphabet(4, r4=True, placed=True)
    extra = set()
    for kind in [('P', w) for w in range(4)] + [('C',)]:
        extra |= base.short_identities(kind, 2)
    for t, a, b, c in itertools.permutations(range(4)):
        extra.add(kick(base, rule, t, a, b, c))
    A = F.Alphabet(4, r4=True, placed=True, extra=sorted(extra, key=lambda r: (len(r), r)))
    print(len(A.rels), f'relators, K_{rule} a rule; deriving K_{other}', flush=True)
    seen = set()
    ok = tot = 0
    for t, a, b, c in itertools.permutations(range(4)):
        if (t, min(a, b), max(a, b), c) in seen:
            continue
        seen.add((t, min(a, b), max(a, b), c))
        w = kick(A, other, t, a, b, c)
        assert A.is_identity(w)
        t0 = time.time()
        r = A.derive(w, limit)
        tot += 1
        ok += r is not None
        print(f'  K_{other} ({t};{a},{b}) c={c}: {"derived" if r else "NOT derived"} {round(time.time() - t0, 1)} s',
              flush=True)
    print(ok, 'of', tot)


if __name__ == '__main__':
    main()

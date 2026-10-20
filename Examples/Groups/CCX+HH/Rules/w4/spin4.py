#!/usr/bin/env python3
"""Is R4 a consequence of the natural rules on four wires?  A spin test.

    python3 -B spin4.py

On four wires every gate is a rotation of R^16 and lifts to Spin(16)
(`../spin/spin.py`).  Give the lift of each primitive gate g a twist
ζ_g, a fourth root of unity.  A relator r then lifts to
i^(e(r) + Σ_g c_g(r) z_g), where ζ_g = i^(z_g), c_g(r) counts g in r and
i^(e(r)) = ±1 is r's lift with the untwisted gates.  If some twist makes
every rule instance lift to 1, the group the rules present maps to the
twisted spin group, and a relation lifting to anything else is not a
consequence of the rules.  The conditions are linear over ℤ/4."""
import sys
import itertools
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE.parent / 'spin'))
sys.path.insert(0, str(HERE))
import check4 as K
from spin import lift_sign

a, gs = K.a, K.gs


def spin_gate(p):
    """Primitive gate index -> spin.py gate tuple (time order)."""
    name = gs.names[p]
    base = name.rstrip('0123456789')
    i = int(name[len(base):])
    if base == 'X':
        return ('X', i)
    if base == 'CX':
        return ('CX', i + 1, i)
    if base == 'CCX':
        return ('CCX', i + 1, i + 2, i)
    if base == 'HH':
        return ('HH', i, i + 1)
    raise ValueError(name)


def exponent(word):
    """e with lift = i^e, for a primitive word with matrix I."""
    r = lift_sign(4, [spin_gate(p) for p in word])
    if abs(r - 1) < 1e-6:
        return 0
    if abs(r + 1) < 1e-6:
        return 2
    raise ValueError(('not ±1', r))


def equations(relators):
    seen = {}
    for r in relators:
        w = a.primitive(r)
        counts = tuple(sum(1 for p in w if p == g) % 4 for g in range(len(gs.names)))
        key = (counts, w)
        if counts in seen:
            # same counts: the lifts must agree, else no twist works
            e = exponent(w)
            if e != seen[counts][0]:
                return None, (w, seen[counts][1])
            continue
        seen[counts] = (exponent(w), w)
    return [(c, e) for c, (e, _) in seen.items()], None


def solve(eqs, nv):
    """All z in (ℤ/4)^nv with Σ c z + e ≡ 0 for every equation."""
    order = sorted(range(nv), key=lambda v: -sum(1 for c, _ in eqs if c[v]))
    pos = {v: k for k, v in enumerate(order)}
    # an equation is checked once its last variable (in `order`) is set
    last = {}
    for c, e in eqs:
        sup = [pos[v] for v in range(nv) if c[v]]
        k = max(sup) if sup else -1
        last.setdefault(k, []).append((c, e))
    if any(e for c, e in last.get(-1, [])):
        return []
    sols = []
    z = [0] * nv

    def go(k):
        if k == nv:
            sols.append(tuple(z))
            return
        v = order[k]
        for val in range(4):
            z[v] = val
            if all((sum(ci * zi for ci, zi in zip(c, z)) + e) % 4 == 0 for c, e in last.get(k, [])):
                go(k + 1)
        z[v] = 0

    go(0)
    return sols


def main():
    lets = range(len(a.letters))
    rels = a.structural(lets) + K.all_rules() + a.definitions()
    print(len(rels), 'rule instances', flush=True)
    eqs, clash = equations(rels)
    if eqs is None:
        print('two instances with the same counts lift differently:', clash)
        return
    print(len(eqs), 'distinct count vectors', flush=True)
    nv = len(gs.names)
    sols = solve(eqs, nv)
    print(len(sols), 'twists make every rule lift to 1', flush=True)
    if not sols:
        # which rule, together with the involutions, admits no twist?
        inv, _ = equations([(g, g) for g in range(nv)])
        for r in rels:
            eq, _ = equations([r])
            if not solve(inv + eq, nv):
                print('  no twist with the involutions:', a.show(r))
        return
    # R4 with partner wire 0: (CCX(1;2,3) · HH(0,1))^4 = CZ(2,3),
    # CZ(2,3) = HH(0,2) CX(3→2) HH(0,2), HH(0,2) = SW1 HH0 SW1.
    cz = 'SW1 HH0 SW1 CX2 SW1 HH0 SW1'
    lhs = ' '.join(['CCX1 HH0'] * 4)
    r4 = a.word(lhs) + tuple(reversed(a.word(cz)))
    w = a.primitive(r4)
    e = exponent(w)
    c = [sum(1 for p in w if p == g) for g in range(nv)]
    vals = {(e + sum(ci * zi for ci, zi in zip(c, z))) % 4 for z in sols}
    print('R4 lifts to i^k for k in', sorted(vals))
    if vals == {0}:
        print('inconclusive: R4 lifts to 1 under every twist')
    elif 0 not in vals:
        print('R4 is NOT a consequence of the rules on four wires')
    else:
        print('inconclusive: depends on the twist')


if __name__ == '__main__':
    main()

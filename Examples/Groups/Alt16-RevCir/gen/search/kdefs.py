"""Shared definitions for the feasibility search: the cycles Omega_i as words
over placed gates (letters of XCXCCX-4bit/gen/pg_search.py, imported
read-only), checked against gen/common.py."""
import os, sys
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'XCXCCX-4bit', 'gen'))
import common
import pg_search as pg
from pg_search import X, CX, CCX, B1, func, canon, inv, show, parse, relabel

PG_RESULTS = os.path.join(os.path.dirname(pg.__file__), 'pg_results.json')

def state_func(circ):
    """Function on states (tuple of 16) of a circuit of common.py's gates."""
    p = common.circ_perm(circ)            # on Gray positions
    return tuple(common.ENC[p[common.DEC[s]]] for s in range(16))

# K = (T C)^2: T = Toffoli target 1 controls 0,3; C = target 0 controls 1,2
T_ = B1[CCX(0, 3, 1)]
C_ = B1[CCX(1, 2, 0)]
K = (T_ + C_) * 2
assert func(K) == state_func(common.K)

def tof(t, a, b, va=1, vb=1):
    """Toffoli with target t and controls a, b of colours va, vb
    (0 = white: X before and after)."""
    xs = bytes(X(c) for c, v in ((a, va), (b, vb)) if v == 0)
    return xs + B1[CCX(a, b, t)] + xs

def omega(i):
    """Omega_i as 4 coloured Toffolis: the 3-cycle s0 -> s1 -> s2 of the
    states at Gray positions i, i+1, i+2.  With a, b the wires flipped in
    the two steps and c < d the other two: (T C)^2, T flips b where a is
    set as in s1 and d as in s0, C flips a where b is as in s1 and c as in
    s0 -- the image of K under the cube symmetry."""
    s0, s1, s2 = (common.ENC[i + k] for k in range(3))
    a = (s0 ^ s1).bit_length() - 1
    b = (s1 ^ s2).bit_length() - 1
    c, d = [w for w in range(4) if w not in (a, b)]
    bit = common.bit
    best = None
    for (c1, d1) in ((c, d), (d, c)):
        Tg = tof(b, a, d1, bit(s1, a), bit(s0, d1))
        Cg = tof(a, b, c1, bit(s1, b), bit(s0, c1))
        for w in ((Tg + Cg) * 2, (Cg + Tg) * 2):
            if func(w) == state_func(common.omega_circuit(i)):
                if best is None or len(w) < len(best):
                    best = w
    assert best is not None, i
    return best

OM = [omega(i) for i in range(14)]
for i in range(14):
    f = func(OM[i]); s = [common.ENC[i + k] for k in range(3)]
    assert f[s[0]] == s[1] and f[s[1]] == s[2] and f[s[2]] == s[0]

def load_library(names=None):
    """The equations E1..E8 of XCXCCX-4bit (already derived from r1..r7,
    Equations4.agda) as a lemma library."""
    import json
    lib = pg.Library()
    with open(PG_RESULTS) as fh:
        data = json.load(fh)
    for rec in data['targets']:
        if rec.get('found') and (names is None or rec['name'] in names):
            l, r = pg.TARGETS[rec['name']]
            lib.add(rec['name'], l, r, pg.steps_from_json(rec['steps']))
    return lib

if __name__ == '__main__':
    for i in range(14):
        print(i, show(OM[i]))

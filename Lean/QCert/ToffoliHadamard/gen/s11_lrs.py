"""LRS-level derivations for the roundTrip identities (non-permutation letters)."""
from paths import work, data, module
import pickle, time
from lrsc import CSearch7, lrs_relators, D, N, X, K
from lrs import GENS, GI, T1, RS, bidir
from lrs3 import RS2, pair_rule
from model import lev

R = lrs_relators()
C = CSearch7(8, R)

def rot_steps(a, b, ex=2, grows=(1, 2, 100)):
    aa = [GI[g] for g in a]; bb = [GI[g] for g in b]
    for g in grows:
        st = C.query(aa, bb, min(18, max(len(aa), len(bb)) + ex), 4000000, grow=g)
        if st is not None:
            return [('R',) + s for s in st]
    raise RuntimeError(("rot search failed", a, b))

def plain_steps(a, b, S, ex=4):
    rs = RS2(RS, [GI[g] for g in S])
    r = bidir(rs, bytes(GI[g] for g in a), bytes(GI[g] for g in b),
              maxlen=max(len(a), len(b)) + ex, limit=3_000_000)
    if r is None:
        raise RuntimeError(("plain search failed", a, b))
    return [('P', i, k, d) for ((i, k, d), _w) in r]

def replay(w, steps):
    w = list(w)
    for st in steps:
        if st[0] == 'P':
            _, i, k, d = st
            fam, idx, l, r = T1[k]
            src, dst = (l, r) if d else (r, l)
            assert w[i:i + len(src)] == src, (w, st)
            w = w[:i] + dst + w[i + len(src):]
        else:
            _, i, rid, rot, cut, rv = st
            rho = [GENS[x] for x in R.rels[rid]]
            base = rho[::-1] if rv else rho
            rr = base[rot:] + base[:rot]
            u = rr[:cut]; v = rr[cut:][::-1]
            assert w[i:i + len(u)] == u, (w, st)
            w = w[:i] + v + w[i + len(u):]
    return w

def shift(steps, off):
    return [(s[0], s[1] + off) + tuple(s[2:]) for s in steps]

out = {}
def done(nm, a, b, steps):
    assert replay(a, steps) == b, nm
    out[nm] = (a, b, steps)
    print(nm, len(steps), flush=True)

c1a, c1b = [K(4,5,6,7), X(5,7), X(4,6), K(4,5,6,7)], [N(6), N(7)]
c2a, c2b = [K(0,1,2,3), X(1,3), X(0,2), K(0,1,2,3)], [N(2), N(3)]
c1 = plain_steps(c1a, c1b, sorted(set(c1a) | set(c1b)))
c2 = plain_steps(c2a, c2b, sorted(set(c2a) | set(c2b)))
# CZ01
a = D["K12"] + D["CX01"] + D["K12"]
st = rot_steps(a, c1a) + c1
done("CZ01", a, D["CZ01"], st)
# Z1
a = D["K12"] + D["X1"] + D["K12"]
mid = c1a + c2a
st = rot_steps(a, mid) + c1 + shift(c2, 2) + rot_steps(c1b + c2b, D["Z1"])
done("Z1", a, D["Z1"], st)
for nm, a in [("Z0", D["CZ01"] + D["CX01"] + D["CZ01"] + D["CX01"]), ("Z2", D["S02"] + D["Z0"] + D["S02"]),
              ("CZ02", D["S12"] + D["CZ01"] + D["S12"]), ("CZ12", D["S01"] + D["CZ02"] + D["S01"]),
              ("K01", D["S02"] + D["K12"] + D["S02"])]:
    done(nm, a, D[nm], rot_steps(a, D[nm]))
a = [K(4,5,6,7)] + D["X0"] + [K(4,5,6,7)] + D["X0"]
r = bidir(RS, bytes(GI[g] for g in a), bytes(GI[g] for g in D["K12"]), maxlen=len(a) + 2, limit=2_000_000)
done("K12", a, D["K12"], [('P', i, k, d) for ((i, k, d), _w) in r])
pickle.dump(out, open(work("rt_lrs.pkl"), "wb"))
C.p.stdin.close()

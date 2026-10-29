"""Lemma 8.5 (Appendix E.3) and its step, checked numerically.

* lemma85: for every state s with bit t clear, D((-1)_[G^-1(s)] X_[G^-1(s), G^-1(s^2^t)]) is the
  multi-controlled XZ on wire t controlled by the other bits of s, and the sign on G^-1(s^2^t)
  gives the ZX (`mc` of ../mc.py, `ctlOf s t`).
* step85: the five letters of the unfolding (Lean's `Step85`) at every pair of wires and state.
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import mc
import decode as dc

def gInv(n, s):
    acc = 0
    for i in range(n): acc ^= (s >> i)
    return acc
def ctlOf(s, t): return lambda j: None if j == t else (((s >> j) & 1) == 1)
def sgn(k): return 'xz' if k else 'zx'
def M(n, c): return mc.mat(n, c)

bad = 0; tot = 0
for n in [3, 4, 5]:
    for s in range(2 ** n):
        for t in range(n):
            if (s >> t) & 1: continue
            p, q = gInv(n, s), gInv(n, s ^ (1 << t))
            for sign, kind in [(p, 'xz'), (q, 'zx')]:
                d = dc.dec(n, dc.Zx(sign, p, q))
                tot += 1
                if not np.allclose(M(n, d), M(n, mc.mc(n, kind, [t], ctlOf(s, t)))):
                    bad += 1; print('lemma85 FAIL', n, s, t, kind)
            for b in range(n):
                if b == t: continue
                for k1 in [False, True]:
                    for k2 in [False, True]:
                        g = [mc.mc(n, sgn(k1), [b], ctlOf(s, b)),
                             mc.mc(n, sgn(k1), [b], ctlOf(s ^ (1 << t), b)),
                             mc.mc(n, sgn(k2), [t], ctlOf(s ^ (1 << b), t)),
                             mc.mc(n, sgn(not k1), [b], ctlOf(s ^ (1 << t), b)),
                             mc.mc(n, sgn(not k1), [b], ctlOf(s, b))]
                        tot += 1
                        if not np.allclose(M(n, mc.drawn(*g)), M(n, mc.mc(n, sgn(k2), [t], ctlOf(s, t)))):
                            bad += 1; print('step85 FAIL', n, s, t, b, k1, k2)
print('checked', tot, 'bad', bad)

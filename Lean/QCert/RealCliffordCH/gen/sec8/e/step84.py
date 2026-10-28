"""Step84 / Step85 (the induction steps of Lemmas 8.4, 8.5 as stated in Sec8/E/Lemma84.lean)."""
from decode import *
import fast
from mc import mc as MC
def ctlOf(s, t): return lambda j: None if j == t else (bitOf(s, j) == 1)
def boxAt(N, t, s): return MC(N, 'box', [t], ctlOf(s, t))
def zxAt(N, K, t, s): return MC(N, K, [t], ctlOf(s, t))
def eqm(N, l, r): return np.allclose(fast.mat(N, l), fast.mat(N, r), atol=1e-9)
for N in (3, 4, 5):
    ok = bad = 0
    for t in range(N):
        for b in range(N):
            if b == t: continue
            for s in range(2 ** N):
                l = drawn(boxAt(N, b, s), boxAt(N, t, s ^ (1 << b)), boxAt(N, b, s ^ (1 << t)))
                if eqm(N, l, boxAt(N, t, s)): ok += 1
                else: bad += 1
    print('step84', N, ok, bad)

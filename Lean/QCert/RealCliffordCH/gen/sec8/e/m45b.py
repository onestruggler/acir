"""Rule (45): the facts of `E/Core45Facts.lean` and the algebra of `E/Core45Alg.lean`.

Every gate is the circuit of `MC.lean` (`mc.py`'s `mc`), on N = 4, 5, 6 wires: the local
wires 0..3 coloured as in `Core45Facts` (`ctlF s l`: wires `l` idle or special, wire j black
where bit j of s is 1), the wires 4.. white.  Words are in drawn order (first applied first);
the Lean facts are the same equations in monoid order (`drawn [x, y] = y * x`).
Checked: each fact, and the three stages of `alg45` (T = k V, V = P01 X P01, X X = 1).
"""
import sys, os, itertools
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from mc import mat, mc, pp, placeG
import numpy as np

def ctlF_N(s, l):
    def c(j):
        if j in l: return None
        if j >= 4: return False
        return bool((s >> j) & 1)
    return c

def G(N):
    B = lambda t, s, l: mc(N, 'box', [t], ctlF_N(s, l))
    H = lambda b, h, s, l: mc(N, 'hg', [b, h], ctlF_N(s, l))
    P = lambda i, j: placeG(N, pp, [i, j])
    return dict(
        a=H(2, 0, 0, [2, 0]), b=H(0, 1, 0, [0, 1]), w=B(0, 0, [0]), k=B(0, 4, [0]),
        f=H(0, 1, 8, [0, 1]), v=B(0, 0, [2, 0]), e=H(0, 1, 0, [3, 0, 1]), beta=B(0, 2, [0]),
        phi=B(0, 10, [0]), zp=B(0, 2, [3, 0]), z=B(3, 2, [3, 0]), z0=B(3, 2, [3]), z1=B(3, 3, [3]),
        y=B(2, 1, [2]), y0=B(2, 0, [2]), u0=B(2, 2, [2]), u1=B(2, 3, [2]), vp=B(2, 0, [2, 0]),
        p=B(2, 0, [1, 2]), q=B(2, 1, [1, 2]), h0=H(2, 1, 0, [2, 1]), h1=H(2, 1, 1, [2, 1]),
        P01=P(0, 1), P20=P(2, 0), P21=P(2, 1), P12=P(1, 2))

FACTS = [
    *[(f'{g} {g}', '') for g in ['k', 'a', 'b', 'w', 'f', 'y', 'y0', 'u0', 'u1', 'z0', 'z1',
                                  'h0', 'h1', 'P01']],
    ('k b', 'b k'), ('k f', 'f k'), ('k w', 'w k'), ('k a', 'a k'), ('w k', 'v'), ('b f', 'e'),
    ('w f', 'f w'), ('a f', 'f a'), ('f b', 'b f'),
    ('b', 'P01 beta P01'), ('f', 'P01 phi P01'), ('beta phi', 'zp'), ('a', 'P20 y P20'),
    ('P01 P20', 'P21'), ('P20 P01', 'P21'), ('P20 v', 'v P20'), ('v', 'vp'), ('y0 y', 'vp'),
    ('y0 u0', 'p'), ('y u1', 'q'), ('P21 p', 'p P21'), ('P21 q', 'q P21'), ('P12', 'P21'),
    ('h0', 'P21 u0 P21'), ('h1', 'P21 u1 P21'), ('zp', 'z'), ('z0 z1', 'z'),
    ('z1 h0', 'h0 z1'), ('z0 h1', 'h1 z0'), ('h0 h1', 'h1 h0'),
    *[(f'{s} {t}', f'{t} {s}') for s, t in [('y0', 'u0'), ('y0', 'u1'), ('u0', 'u1'), ('y', 'u0'),
      ('y', 'u1'), ('y', 'y0'), ('z0', 'y0'), ('z0', 'u0'), ('z0', 'y'), ('z0', 'u1'),
      ('z1', 'y0'), ('z1', 'u0'), ('z0', 'z1')]],
]

if __name__ == '__main__':
    for N in [4, 5, 6]:
        g = {k: mat(N, v) for k, v in G(N).items()}
        def S(s):
            M = np.eye(2 ** N)
            for t in s.split():
                M = g[t] @ M
            return M
        bad = [(l, r) for l, r in FACTS if not np.allclose(S(l), S(r))]
        T = S('b w a b a'); L = S('a b a w b')
        print(N, 'facts', len(FACTS), 'bad', bad,
              '| (45) decoded', np.allclose(T, L),
              '| T = k V', np.allclose(T, S('e v a e a k')),
              '| V = P01 X P01', np.allclose(S('e v a e a'), S('P01 p z0 h0 z0 h1 q P01')),
              '| X X = 1', np.allclose(S('p z0 h0 z0 h1 q p z0 h0 z0 h1 q'), np.eye(2 ** N)))

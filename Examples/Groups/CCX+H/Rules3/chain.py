"""Segment chains for the Agda derivations.

A line is a list of elements: ('T', tokens) or 'H' (H on wire 0).  The
steps are those of Steps.agda, at element positions:
  ('MG', k, a, b, t)     [T a, T b] -> [T t]            fastCheck (a b) t
  ('HH', k)              [H, H] -> []                    H²
  ('E0', k)              [] -> [T ()]                    refl (inserted at k)
  ('BT', k, p, s, q, t, alpha)  [T p, H, T s, H, T q] -> [T t]
  ('SQ', k, p1, p2, p3, q1, q2, r, t, cfX, cfY)  5 -> 5
  ('FIN', a)             [T a] -> []                     fastCheck a ε
Contraction is deriv.py's, on the segments of the line.
"""
import collections
from syn import M, inv, theta_word
from tree import mat_mul
from deriv import (mm, I8, d, rd, NBW, cf, hconj, is_type1)
import geo


class Line:
    def __init__(self, elems):
        self.el = [('T', tuple(e[1])) if e != 'H' else 'H' for e in elems]
        self.steps = []

    # ---- normalisation: T H T H ... H T, no empty interior handled by HH
    def normalise(self):
        changed = True
        while changed:
            changed = False
            for k in range(len(self.el) - 1):
                a, b = self.el[k], self.el[k + 1]
                if a != 'H' and b != 'H':
                    t = theta_word(mm(a[1], b[1]))
                    self.steps.append(('MG', k, a[1], b[1], t))
                    self.el[k:k + 2] = [('T', t)]
                    changed = True
                    break
                if a == 'H' and b == 'H':
                    self.steps.append(('HH', k))
                    del self.el[k:k + 2]
                    changed = True
                    break
        if not self.el or self.el[0] == 'H':
            self.steps.append(('E0', 0))
            self.el.insert(0, ('T', ()))
        if self.el[-1] == 'H':
            k = len(self.el)
            self.steps.append(('E0', k))
            self.el.append(('T', ()))

    def segs(self):
        return [e[1] for e in self.el if e != 'H']

    def prefix(self, j):   # P_j = s0 H s1 H ... s(j-1) H
        if j == 0:
            return I8
        w = ()
        for e in self.el[:2 * j]:
            w += ('H0',) if e == 'H' else e[1]
        return M(w)

    def run(self):
        self.normalise()
        while len(self.el) > 1:
            segs = self.segs()
            m = len(segs) - 1
            P = [self.prefix(j) for j in range(m + 1)]
            ds = [d(p) for p in P]
            D = max(ds)
            k = ds.index(D)
            assert 1 <= k <= m - 1, (k, m, ds)
            a, x, b = P[k - 1], P[k], P[k + 1]
            pos = 2 * (k - 1)
            if rd(a, b) == 0:
                p, s, q = segs[k - 1], segs[k], segs[k + 1]
                from syn import a_word
                alpha = a_word(M(s))
                t = theta_word(mm(p, hconj(alpha), q))
                self.steps.append(('BT', pos, p, s, q, t, alpha))
                self.el[pos:pos + 5] = [('T', t)]
                continue
            com = []
            for th in NBW:
                y = mat_mul(a, mm(th, ('H0',)))
                if rd(y, b) == 1:
                    com.append((th, y))
            target = [i for i, (th, y) in enumerate(com) if d(y) == D - 2]
            assert target
            xi = [i for i, (th, y) in enumerate(com) if rd(y, x) == 0][0]
            prev = {xi: None}
            q_ = collections.deque([xi])
            goal = None
            while q_:
                u = q_.popleft()
                if u in target:
                    goal = u
                    break
                for v in range(len(com)):
                    if v not in prev and is_type1(com[u][1], com[v][1]):
                        prev[v] = u
                        q_.append(v)
            assert goal is not None
            path = []
            u = goal
            while u is not None:
                path.append(u)
                u = prev[u]
            path.reverse()
            for u in path[1:]:
                self.square(pos, com[u][0])
        if self.el[0][1] != ():
            assert M(self.el[0][1]) == I8
        self.steps.append(('FIN', self.el[0][1]))
        self.el = []
        return self.steps

    def square(self, pos, q1):
        p1, p2, p3 = self.el[pos][1], self.el[pos + 2][1], self.el[pos + 4][1]
        base = mm(p1, ('H0',), p2, ('H0',))
        zq = mm(q1, ('H0',))
        q2 = None
        for th in NBW:
            if rd(mat_mul(zq, mm(th, ('H0',))), base) == 0:
                q2 = th
                break
        assert q2 is not None
        r = theta_word(mat_mul(geo.transpose(mm(q1, ('H0',), q2, ('H0',))), base))
        cfX = cf((), inv(q1) + p1, ())
        cfY = cf(q2, r, inv(p2))
        assert cfX[0] == cfY[0]
        t = theta_word(mm(r, p3))
        self.steps.append(('SQ', pos, p1, p2, p3, q1, q2, r, t, cfX, cfY))
        self.el[pos:pos + 5] = [('T', q1), 'H', ('T', q2), 'H', ('T', t)]


if __name__ == "__main__":
    import sys, time
    from canon_rel import inv_elems
    from decoder import dec, AUX, REL, seg_tokens
    for r in REL['relations'][:int(sys.argv[1]) if len(sys.argv) > 1 else 5]:
        if r['source'] == 'roundtrip':
            continue
        lhs = [e for i in r['auxiliary_left'] for e in dec(AUX[i])]
        rhs = [e for i in r['auxiliary_right'] for e in dec(AUX[i])]
        el = [('T', seg_tokens(e)) if e != 'H' else 'H' for e in lhs + inv_elems(rhs)]
        L = Line(el)
        st = L.run()
        print(r['source'], r['indices'], collections.Counter(s[0] for s in st))

"""Deterministic Schreier-Sims (with sifting) for permutation groups."""
def mul(p, q):          # apply p then q
    return tuple(q[i] for i in p)
def inv(p):
    r = [0]*len(p)
    for i, x in enumerate(p): r[x] = i
    return tuple(r)

class SS:
    def __init__(self, n):
        self.n = n; self.base = []; self.gens = []; self.trans = []
    def _orbit(self, k):
        pt = self.base[k]; T = {pt: tuple(range(self.n))}; fr = [pt]
        while fr:
            nw = []
            for x in fr:
                for g in self.gens[k]:
                    y = g[x]
                    if y not in T:
                        T[y] = mul(T[x], g); nw.append(y)
            fr = nw
        self.trans[k] = T
    def sift(self, g):
        for k, b in enumerate(self.base):
            y = g[b]
            if y not in self.trans[k]:
                return g, k
            g = mul(g, inv(self.trans[k][y]))
        return g, len(self.base)
    def add(self, g):
        idt = tuple(range(self.n))
        h, k = self.sift(g)
        if h == idt: return
        if k == len(self.base):
            pt = next(i for i in range(self.n) if h[i] != i)
            self.base.append(pt); self.gens.append([]); self.trans.append({})
        for j in range(k + 1):
            self.gens[j].append(h)
        for j in range(k, -1, -1):
            old = set(self.trans[j]); self._orbit(j)
            # Schreier generators from new orbit points
            for x, tx in list(self.trans[j].items()):
                for s in self.gens[j]:
                    sg = mul(mul(tx, s), inv(self.trans[j][s[x]]))
                    h2, k2 = self.sift(sg)
                    if h2 != idt:
                        self.add(sg)
    def order(self):
        r = 1
        for T in self.trans: r *= len(T)
        return r

def order(perms):
    S = SS(len(perms[0]))
    for p in perms: S.add(p)
    return S.order()

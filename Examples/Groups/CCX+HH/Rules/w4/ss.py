"""Deterministic Schreier-Sims (Holt's version) for permutations as tuples.
mul(p, q): first p then q, i.e. x -> q[p[x]]."""
def mul(p, q):
    return tuple(q[i] for i in p)
def inv(p):
    r = [0]*len(p)
    for i, j in enumerate(p): r[j] = i
    return tuple(r)

def order(gens, want_chain=False):
    n = len(gens[0]); ident = tuple(range(n))
    S = [g for g in gens if g != ident]
    base = []
    for g in S:
        if all(g[b] == b for b in base):
            base.append(next(x for x in range(n) if g[x] != x))
    def Si(i):
        return [s for s in S if all(s[b] == b for b in base[:i])]
    def transversal(i):
        gs = Si(i); b = base[i]
        T = {b: ident}; fr = [b]
        while fr:
            new = []
            for x in fr:
                for s in gs:
                    y = s[x]
                    if y not in T:
                        T[y] = mul(T[x], s); new.append(y)
            fr = new
        return T, gs
    trans = {}
    def get(i):
        if i not in trans: trans[i] = transversal(i)
        return trans[i]
    def sift(g, start):
        for j in range(start, len(base)):
            T, _ = get(j)
            b = g[base[j]]
            if b not in T: return g, j
            g = mul(g, inv(T[b]))
        return g, len(base)
    i = len(base) - 1
    while i >= 0:
        T, gs = get(i)
        found = False
        for x in list(T):
            for s in gs:
                h = mul(mul(T[x], s), inv(T[s[x]]))
                r, j = sift(h, i + 1)
                if r != ident:
                    S.append(r)
                    if j == len(base):
                        base.append(next(y for y in range(n) if r[y] != y))
                    for k in range(0, j + 1):
                        trans.pop(k, None)
                    # levels i+1..j gained a generator
                    i = j; found = True; break
            if found: break
        if not found:
            i -= 1
        else:
            for k in range(0, i + 1):
                trans.pop(k, None) if k > i else None
    o = 1
    for k in range(len(base)):
        o *= len(get(k)[0])
    return (o, base, S, get) if want_chain else o

from fig6 import *
import pickle, collections
GENS = [('Z',a) for a in range(4)] + [('X',a,b) for a in range(4) for b in range(a+1,4)] + \
       [('H',a,b) for a in range(4) for b in range(a+1,4)]
def g4eqs(proven):
    eqs = []
    for g in GENS: eqs.append((('a', g), (g, g), ()))
    for f, idx, l, r in instances():
        if (f, idx) in proven: eqs.append(((f, idx), tuple(l), tuple(r)))
    return eqs
def occ(w, a):
    n = len(a)
    for p in range(len(w) - n + 1):
        if w[p:p+n] == a: yield p
def gsearch(src, dst, eqs, maxlen, limit=500000):
    src = tuple(src); dst = tuple(dst)
    fa = {src: None}; fb = {dst: None}
    qa = collections.deque([src]); qb = collections.deque([dst]); n = 0
    def nb(w):
        for k, (name, l, r) in enumerate(eqs):
            for d, (a, b) in ((0, (l, r)), (1, (r, l))):
                if len(w) - len(a) + len(b) > maxlen: continue
                if len(a) == 0:
                    for p in range(len(w)+1): yield w[:p] + b + w[p:], (p, k, d)
                else:
                    for p in occ(w, a): yield w[:p] + b + w[p+len(a):], (p, k, d)
    while qa and qb:
        if len(qa) <= len(qb): q, f, g = qa, fa, fb
        else: q, f, g = qb, fb, fa
        for _ in range(len(q)):
            w = q.popleft()
            for v, st in nb(w):
                if v in f: continue
                f[v] = (w, st); n += 1
                if v in g:
                    # path
                    left = []; x = v
                    while fa[x] is not None: p, s = fa[x]; left.append((p, s)); x = p
                    left.reverse()
                    path = [src] + [None]*0
                    words = [src]
                    for p, s in left: pass
                    seq = []
                    x = src
                    for p, s in left:
                        seq.append(('f', p, s))
                    y = v
                    while fb[y] is not None:
                        p, s = fb[y]; seq.append(('b', y, p, s)); y = p
                    return seq
                if n > limit: return None
                q.append(v)
    return None
def explicit(src, seq, eqs):
    """list of (u_len, k, d) rewrites from src: at position p replace a by b"""
    out = []; cur = tuple(src)
    for it in seq:
        if it[0] == 'f':
            _, p, (pos, k, d) = it
            assert p == cur
            name, l, r = eqs[k]; a, b = (l, r) if d == 0 else (r, l)
            assert cur[pos:pos+len(a)] == a
            cur = cur[:pos] + b + cur[pos+len(a):]; out.append((pos, k, d))
        else:
            _, y, p, (pos, k, d) = it
            assert y == cur
            # p --(pos,k,d)--> y ; inverse: at pos replace b by a
            name, l, r = eqs[k]; a, b = (l, r) if d == 0 else (r, l)
            assert cur[pos:pos+len(b)] == b
            cur = cur[:pos] + a + cur[pos+len(b):]; out.append((pos, k, 1-d))
    return out, cur
if __name__ == '__main__':
    proven = pickle.load(open('proven_dec.pkl','rb'))
    eqs = g4eqs(proven)
    res = {}
    for f, idx, l, r in instances():
        if (f, idx) in proven or f == 'd3': continue
        t = time.time()
        seq = gsearch(l, r, eqs, maxlen=max(len(l), len(r)) + 4)
        if seq is None: print(f, idx, 'FAILED', round(time.time()-t,1)); continue
        st, end = explicit(l, seq, eqs)
        assert end == tuple(r)
        res[(f, idx)] = st
        print(f, idx, 'ok', len(st), round(time.time()-t,1), flush=True)
    pickle.dump((eqs, res), open('g4res.pkl','wb'))

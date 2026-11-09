"""EvenRS N: symbols (c,d), 1<=d<=N-2, f(c=False,d)= s_d . s_0 (diagram: s_d first), f(True,d) = s_0 . s_d.
Relations as in EvenRS.agda.  Words are lists of symbols."""
def rs_relations(N):
    R = []
    for c in (False, True):
        for d in range(1, N-1):
            R.append(('order', c, d, [(c,d),(not c,d)], []))
        if N >= 3:
            R.append(('braid0', c, 0, [(not c,1)], [(c,1),(c,1)]))
        for d in range(1, N-2):
            R.append(('braid', c, d, [(c,d),(not c,d+1),(c,d)], [(c,d+1),(not c,d),(c,d+1)]))
        for e in range(2, N-1):
            R.append(('far0', c, e, [(c,e)], [(not c,e)]))
        for d in range(1, N-1):
            for e in range(d+2, N-1):
                R.append(('far', c, (d,e), [(c,d),(not c,e)], [(c,e),(not c,d)]))
    return R
def transp(N, d):
    p = list(range(N)); p[d], p[d+1] = d+1, d; return tuple(p)
def mulN(p, q): return tuple(q[i] for i in p)   # p then q
def fsym(N, s):
    c, d = s
    return mulN(transp(N,d), transp(N,0)) if not c else mulN(transp(N,0), transp(N,d))
def fword(N, w):
    p = tuple(range(N))
    for s in w: p = mulN(p, fsym(N, s))
    return p
if __name__ == '__main__':
    for N in (8, 16):
        R = rs_relations(N)
        bad = [r for r in R if fword(N, r[3]) != fword(N, r[4])]
        print('N=%d relations=%d unsound=%d' % (N, len(R), len(bad)))
        print('  with 7:', sum(1 for r in R if any(d == 7 for (_, d) in r[3] + r[4])))

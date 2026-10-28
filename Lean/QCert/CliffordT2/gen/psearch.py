# Search for table entries with partial normal forms (chain procedure up to the
# first unknown entry) collapsing the search space.
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from collections import deque
from cliffnf import CliffNF, Cert, inv
from deriv import neighbors, apply

def partial_nf(C, w):
    """Normalize w left to right while table entries are known.
    Returns (cert from w to result, result)."""
    parts = [''] * 6
    steps = []
    i = 0
    while i < len(w):
        x = w[i]
        try:
            newparts, st = C.append(parts, 5, x, 0)
        except Exception:
            break
        parts = newparts; steps += st; i += 1
    res = ''.join(parts) + w[i:]
    return Cert(w, res, steps), res

def psearch(C, u, v, moves, limit=200000, maxlen=40):
    R = C.R
    cu, u0 = partial_nf(C, u); cv, v0 = partial_nf(C, v)
    if u0 == v0: return cu.then(cv.rev())
    pu = {u0: None}; pv = {v0: None}
    qu = deque([u0]); qv = deque([v0])
    count = 0; meet = None
    while qu and qv and meet is None and count < limit:
        for (q, P, Q) in ((qu, pu, pv), (qv, pv, pu)):
            for _ in range(len(q)):
                w = q.popleft(); count += 1
                for nw, st in neighbors(w, R.rules, moves, maxlen):
                    c, nw2 = partial_nf(C, nw)
                    if nw2 in P: continue
                    P[nw2] = (w, Cert(w, nw, [st]).then(c))
                    if nw2 in Q: meet = nw2; break
                    q.append(nw2)
                if meet is not None: break
            if meet is not None: break
    if meet is None: return None
    def path(P, w):
        cert = Cert(w, w, [])
        while P[w] is not None:
            prev, c = P[w]
            cert = c.then(cert)
            w = prev
        return cert
    a = cu.then(path(pu, meet))
    b = cv.then(path(pv, meet))
    return a.then(b.rev())

if __name__ == '__main__':
    import pickle, __main__
    __main__.CliffNF = CliffNF; __main__.Cert = Cert
    from paths import WORK
    with open(os.path.join(WORK, 'cliffnf.pkl'), 'rb') as f: C = pickle.load(f)
    from chain import GENS
    missing = [(c, x) for c in range(20) for x in GENS[5] if (5, c, x) not in C.table]
    print(len(missing))
    for (c, x) in [(3, 's'), (6, 'H'), (13, 'Z'), (17, 'h')]:
        lam, c2 = C.semantic_entry(5, c, x)
        lhs, rhs = C.ch.reps[5][c] + x, lam + C.ch.reps[5][c2]
        t = time.time()
        cert = psearch(C, lhs, rhs, C.cliffax, limit=100000)
        print(c, x, lhs, rhs, None if cert is None else len(cert.steps), '%.0fs' % (time.time() - t), flush=True)

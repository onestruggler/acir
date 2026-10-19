"""Word-level contraction: derivations from L1 (backtracks) and L30 (squares).

A loop is segs = [t0, ..., tm]: the word t0 H0 t1 H0 ... H0 tm, ti theta-words.
Steps:
  ('BT', k, alpha)          segs[k] = alpha in A; t(k-1) H0 alpha H0 t(k+1) -> t(k-1) alpha^H t(k+1)
  ('SQ', k, q1, q2, r, cfX, cfY)
                            t(k-1) H0 t(k) H0 -> q1 H0 q2 H0 r  (r joins t(k+1)),
                            through L30 on X = H0 inv(q1) t(k-1) H0 and Y = q2 H0 r H0 inv(t(k))
  ('TH', k, new)            segs[k] -> new (a theta-step: same matrix)
cf = (phi, psi, alpha, beta, omega): a1 H0 a2 H0 a3 = phi CCZ omega with
  a1 = phi psi alpha, alpha^H a2 = CCX0 beta, omega = psi^Z beta^H a3.
"""
import sys, random, collections, time, pickle, os
from syn import M, inv, mono, T, theta_word, a_word, THETA_T, A_T, LETW, LET, letters_tokens
from tree import mat_mul, S
from tree2 import key
import geo

I8 = M(())
CCZ = ('H0', 'CCX0', 'H0')


def mm(*ws):
    m = I8
    for w in ws:
        m = mat_mul(m, M(w))
    return m


def d(g):
    return geo.rel_dist(I8, g)


def rd(g, h):
    return geo.rel_dist(g, h)


# -------- letter images (letters.py)
from letters import HC as HCONJ, ZCH as ZCONJ
LZ = dict(LETW)


def hconj(alpha):
    out = ()
    for t in alpha:
        out += HCONJ[t]
    return out


def ltok(lw):
    out = ()
    for x in lw:
        out += LZ[x]
    return out


def zconj(lw):
    out = ()
    for x in lw:
        out += ZCONJ[x]
    return out


# -------- neighbours (270), j=1 targets (135), commons of (E, E') (30)
def bfs_orbit(start_word, gens_words):
    seen = {key(M(start_word)): ()}
    q = collections.deque([()])
    while q:
        w = q.popleft()
        for g in gens_words:
            w2 = g + w
            k = key(mm(w2, start_word))
            if k not in seen:
                seen[k] = w2
                q.append(w2)
    return seen


CACHE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'deriv_tables.pkl')
if os.path.exists(CACHE):
    NB, PHI, PSI = pickle.load(open(CACHE, 'rb'))
else:
    _t0 = time.time()
    NB = bfs_orbit(('H0',), [(t,) for t in THETA_T])          # key(w H0) -> w
    PHI = bfs_orbit(CCZ, [(t,) for t in THETA_T])             # key(phi CCZ) -> phi
    seen = {key(M(('H0',))): ()}
    q = collections.deque([()])
    while q:
        lw = q.popleft()
        for x in LET:
            lw2 = (x,) + lw
            k = key(mm(ltok(lw2), ('H0',)))
            if k not in seen:
                seen[k] = lw2
                q.append(lw2)
    PSI = seen                                                 # key(psi H0) -> psi (letters)
    pickle.dump((NB, PHI, PSI), open(CACHE, 'wb'))
    print("tables", len(NB), len(PHI), len(PSI), round(time.time() - _t0), flush=True)
NBW = list(NB.values())
assert len(NB) == 270 and len(PHI) == 135 and len(PSI) == 30


def cf(a1, a2, a3):
    """canonical form of a1 H0 a2 H0 a3 (relative position (2,0^6))"""
    m = mm(a1, ('H0',), a2, ('H0',))
    phi = PHI[key(m)]
    c = mm(inv(phi), a1, ('H0',))
    psi = PSI[key(c)]
    alpha = a_word(mm(inv(ltok(psi)), inv(phi), a1))
    beta = a_word(mm(('CCX0',), hconj(alpha), a2))
    omega = zconj(psi) + hconj(beta) + a3
    assert mm(a1) == mm(phi, ltok(psi), alpha)
    assert mm(hconj(alpha), a2) == mm(('CCX0',), beta)
    assert mm(a1, ('H0',), a2, ('H0',), a3) == mm(phi, CCZ, omega)
    return (phi, psi, alpha, beta, omega)


def word_of(segs):
    out = ()
    for i, s in enumerate(segs):
        if i:
            out += ('H0',)
        out += s
    return out


def is_type1(g, h):
    from osnf import exps
    return exps(mat_mul(T(g), h)) == [-2, 0, 0, 0, 0, 0, 0, 2]


class Deriv:
    def __init__(self, segs):
        self.segs = [tuple(s) for s in segs]
        self.steps = []
        assert mm(word_of(self.segs)) == I8

    def prefix(self, k):   # P_k = t0 H0 ... t(k-1) H0
        if k == 0:
            return I8
        return mm(word_of(self.segs[:k]) + ('H0',))

    def norm(self, k):
        new = theta_word(M(self.segs[k]))
        if new != self.segs[k]:
            self.steps.append(('TH', k, new))
            self.segs[k] = new

    def run(self):
        while len(self.segs) > 1:
            m = len(self.segs) - 1
            P = [self.prefix(k) for k in range(m + 1)]
            ds = [d(p) for p in P]
            D = max(ds)
            k = ds.index(D)
            assert 1 <= k <= m - 1, (k, m, ds)
            a, x, b = P[k - 1], P[k], P[k + 1]
            if rd(a, b) == 0:
                alpha = a_word(M(self.segs[k]))
                self.steps.append(('BT', k, alpha))
                merged = self.segs[k - 1] + hconj(alpha) + self.segs[k + 1]
                self.segs[k - 1:k + 2] = [merged]
                self.norm(k - 1)
                continue
            com = []
            for th in NBW:
                y = mat_mul(a, mm(th, ('H0',)))
                if rd(y, b) == 1:
                    com.append((th, y))
            target = [i for i, (th, y) in enumerate(com) if d(y) == D - 2]
            assert target, "stuck"
            xi = [i for i, (th, y) in enumerate(com) if rd(y, x) == 0][0]
            prev = {xi: None}
            q = collections.deque([xi])
            goal = None
            while q:
                u = q.popleft()
                if u in target:
                    goal = u
                    break
                for v in range(len(com)):
                    if v not in prev and is_type1(com[u][1], com[v][1]):
                        prev[v] = u
                        q.append(v)
            assert goal is not None, "commons not j1-connected"
            path = []
            u = goal
            while u is not None:
                path.append(u)
                u = prev[u]
            path.reverse()
            for u in path[1:]:
                self.square(k, com[u][0])
        assert mm(self.segs[0]) == I8
        return self.steps

    def square(self, k, q1):
        p1, p2 = self.segs[k - 1], self.segs[k]
        base = mm(p1, ('H0',), p2, ('H0',))
        zq = mm(q1, ('H0',))
        q2 = None
        for th in NBW:
            if rd(mat_mul(zq, mm(th, ('H0',))), base) == 0:
                q2 = th
                break
        assert q2 is not None
        r = theta_word(mat_mul(T(mm(q1, ('H0',), q2, ('H0',))), base))
        cfX = cf((), inv(q1) + p1, ())
        cfY = cf(q2, r, inv(p2))
        assert cfX[0] == cfY[0]
        assert mm(cfX[4]) == mm(cfY[4])
        self.steps.append(('SQ', k, q1, q2, r, cfX, cfY))
        self.segs[k - 1] = q1
        self.segs[k] = q2
        self.segs[k + 1] = r + self.segs[k + 1]
        self.norm(k + 1)


def random_loop(L, rng):
    segs = [()]
    while len(segs) < L + 1:
        th = rng.choice(NBW)
        segs[-1] = segs[-1] + th
        segs.append(())
    while True:
        P = mm(word_of(segs))
        Dd = d(P)
        if Dd == 0:
            break
        for th in rng.sample(NBW, len(NBW)):
            if d(mat_mul(P, mm(th, ('H0',)))) == Dd - 1:
                segs[-1] = segs[-1] + th
                segs.append(())
                break
    segs[-1] = segs[-1] + theta_word(T(mm(word_of(segs))))
    return segs


if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    L = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    for _ in range(int(sys.argv[3]) if len(sys.argv) > 3 else 3):
        segs = random_loop(L, rng)
        t0 = time.time()
        Dv = Deriv(segs)
        st = Dv.run()
        c = collections.Counter(s[0] for s in st)
        print("loop H-count", len(segs) - 1, "steps", dict(c), round(time.time() - t0, 1), flush=True)

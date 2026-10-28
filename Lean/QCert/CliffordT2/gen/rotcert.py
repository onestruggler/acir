# Pauli-rotation lemmas and normal forms with certificates.
import sys, os, pickle, time
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np
from collections import deque
from ct import MAT, mat, EQN, AX
from cliffnf import CliffNF, Cert, refl, inv, INV
from rot import PAULIS, pmat, ident, conj, conj_inv, commute, ORDER, CW, Rmat, Emat, Fmat
from chain import key

from paths import WORK
STABG = 'wSZhs'

def rw(p): return CW[p] + 'T' + inv(CW[p])

class RotCert:
    def __init__(self, C):
        self.C = C
        R = C.R
        self.R = R
        ix = R.index
        # stabilizer of Z0: minimal words
        self.stab = {}
        start = np.eye(4, dtype=complex)
        self.stab[key(start)] = ''
        q = deque([start])
        while q:
            M = q.popleft(); w = self.stab[key(M)]
            for g in STABG:
                N = M @ MAT[g]
                k = key(N)
                if k not in self.stab:
                    self.stab[k] = w + g; q.append(N)
        print('stab size', len(self.stab))
        # L0: S T -> T S
        self.L0 = R.add('ST', 'TS', 'L0', [(0, ix['c14_0'], False), (1, ix['c14_0'], True)])
        # y T -> T y for stabilizer letters
        self.passT = {'w': (ix['c1_T'], True), 'S': (self.L0, True), 'Z': (ix['c16'], False),
                      'h': (ix['c2_Th'], False), 's': (ix['c2_Ts'], False)}
        self.L4 = {}; self.L5 = {}; self.L6 = {}; self.L7 = {}
        # L2: t -> R(IZ)
        W = 'hZHhZH'
        assert np.allclose(mat(W + 'T'), mat('t' + W))
        c1 = C.cancel(W).rev().ctx('t')                  # t -> t W inv(W)
        c2 = Cert('t' + W + inv(W), W + 'T' + inv(W), [(0, ix['c17'], False)])
        c3 = self.conjT(W, (1, 'IZ'))
        cert = c1.then(c2).then(c3).check(R.rules)
        self.L2 = R.add('t', rw((1, 'IZ')), 'L2', cert.steps)

    def stabword(self, M):
        return self.stab[key(M)]

    def conjT(self, A, p):
        """Certificate A T inv(A) -> R(p), where A Z0 A^dagger = p."""
        C = self.C
        cw = CW[p]
        assert conj(mat(A), (1, 'ZI')) == p
        D = np.linalg.inv(mat(cw)) @ mat(A)
        Dw = self.stabword(D)
        start = A + 'T' + inv(A)
        c1 = C.eq(A, cw + Dw).ctx('', 'T' + inv(A))
        cur = c1
        # move T left through Dw
        word = cw + Dw + 'T' + inv(A)
        pos = len(cw) + len(Dw)   # position of T
        steps = []
        for y in reversed(Dw):
            k, d = self.passT[y]
            steps.append((pos - 1, k, d)); pos -= 1
        cur = cur.then(Cert(word, cw + 'T' + Dw + inv(A), steps))
        c3 = C.eq(Dw + inv(A), inv(cw)).ctx(cw + 'T', '')
        return cur.then(c3).check(self.R.rules)

    # ---- lemma families ----------------------------------------------------
    def l4(self, p, x):
        """R(p) x -> x R(x^dagger p x)."""
        if (p, x) in self.L4: return self.L4[(p, x)]
        C = self.C
        q = conj_inv(MAT[x], p)
        cw = CW[p]
        A = inv(x) + cw
        lhs = rw(p) + x
        c1 = C.cancel(x).rev().ctx('', lhs)                        # -> x inv(x) cw T inv(cw) x
        c2 = C.eq(inv(cw) + x, inv(A)).ctx(x + inv(x) + cw + 'T', '')  # -> x A T inv(A)
        c3 = self.conjT(A, q).ctx(x, '')
        cert = c1.then(c2).then(c3).check(self.R.rules)
        k = self.R.add(lhs, x + rw(q), 'L4_%s_%s_%s' % ('p' if p[0] > 0 else 'm', p[1], x), cert.steps)
        self.L4[(p, x)] = k
        return k

    def eword(self, a):
        return CW[(1, a)] + 'wSSS' + inv(CW[(1, a)])

    def l5(self, a):
        """R(-a) -> E(a) R(a)."""
        if a in self.L5: return self.L5[a]
        C, R = self.C, self.R
        ix = R.index
        p = (1, a); m = (-1, a)
        cw = CW[p]
        X0 = 'HSSH'
        A = cw + X0
        # R(-a) -> A T inv(A)
        c1 = self.conjT(A, m).rev()
        # inv(A) = inv(X0) inv(cw); make it X0 inv(cw)
        c2 = C.eq(inv(X0), X0).ctx(cw + X0 + 'T', inv(cw))
        # X0 T X0 -> w SSS T
        mid = self.x0tx0()
        c3 = mid.ctx(cw, inv(cw))
        # cw wSSS T inv(cw) -> cw wSSS inv(cw) cw T inv(cw)
        c4 = C.eq('', inv(cw) + cw).ctx(cw + 'wSSS', 'T' + inv(cw))
        cert = c1.then(c2).then(c3).then(c4).check(R.rules)
        k = R.add(rw(m), self.eword(a) + rw(p), 'L5_' + a, cert.steps)
        self.L5[a] = k
        return k

    def x0tx0(self):
        """HSSH T HSSH -> wSSST."""
        if hasattr(self, '_x0tx0'): return self._x0tx0
        C, R = self.C, self.R
        ix = R.index
        X0 = 'HSSH'
        w0 = X0 + 'T' + X0
        # insert T^8 = (TT)^4 -> S^4 -> '' at front: '' -> SSSS -> TTTTTTTT
        k5, k14 = ix['c5_0'], ix['c14_0']
        ins = Cert('', 'SSSS', [(0, k5, False)])
        ins = ins.then(Cert('SSSS', 'TT' * 4, [(0, k14, False), (2, k14, False), (4, k14, False), (6, k14, False)]))
        c1 = ins.ctx('', w0)            # w0 -> T^8 w0
        word = 'T' * 7 + 'T' + X0 + 'T' + X0
        # (T X0)^2 -> w at position 7
        c2 = Cert(word, 'T' * 7 + 'w', [(7, ix['c15_0'], True)])
        # T^7 w -> w T^7 : move w left (c1_T backward: 'Tw' -> 'wT')
        steps = [(6 - j, ix['c1_T'], False) for j in range(7)]
        c3 = Cert('T' * 7 + 'w', 'w' + 'T' * 7, steps)
        # T^7 -> T SSS : TT -> S three times at positions 1,2,3
        c4 = Cert('w' + 'T' * 7, 'wTSSS', [(2, k14, True), (3, k14, True), (4, k14, True)])
        # T SSS -> SSS T : 'TS' -> 'ST' is L0 backward
        c5 = Cert('wTSSS', 'wSSST', [(1, self.L0, False), (2, self.L0, False), (3, self.L0, False)])
        cert = c1.then(c2).then(c3).then(c4).then(c5).check(R.rules)
        self._x0tx0 = cert
        return cert

    def fword(self, a):
        return CW[(1, a)] + 'S' + inv(CW[(1, a)])

    def l6(self, a):
        """R(a) R(a) -> F(a)."""
        if a in self.L6: return self.L6[a]
        C, R = self.C, self.R
        p = (1, a); cw = CW[p]
        lhs = rw(p) + rw(p)
        c1 = C.eq(inv(cw) + cw, '').ctx(cw + 'T', 'T' + inv(cw))
        c2 = Cert(cw + 'TT' + inv(cw), cw + 'S' + inv(cw), [(len(cw), R.index['c14_0'], True)])
        cert = c1.then(c2).check(R.rules)
        k = R.add(lhs, self.fword(a), 'L6_' + a, cert.steps)
        self.L6[a] = k
        return k

    def l7(self, a, b):
        """R(a) R(b) -> R(b) R(a), a, b commuting positive Paulis, a != b."""
        if (a, b) in self.L7: return self.L7[(a, b)]
        C, R = self.C, self.R
        p, q = (1, a), (1, b)
        cw = CW[p]
        qq = conj_inv(mat(cw), q)        # cw^dagger q cw, commutes with Z0
        cz = CW[(1, 'IZ')]
        # B in Stab(Z0) with B Z1 B^dagger = qq
        Bw = None
        for kk, w in sorted(self.stab.items(), key=lambda kv: (len(kv[1]), kv[1])):
            if conj(mat(w), (1, 'IZ')) == qq: Bw = w; break
        assert Bw is not None, (a, b, qq)
        A = cw + Bw + cz
        lhs = rw(p) + rw(q)
        c1 = self.conjT(A, q).rev().ctx(rw(p), '')   # -> cw T inv(cw) A T inv(A)
        c2 = C.eq(inv(cw) + cw, '').ctx(cw + 'T', Bw + cz + 'T' + inv(A))
        # cw T Bw (cz T inv(cz)) inv(Bw) inv(cw) ; cz T inv(cz) -> t  is L2 backward
        w2 = cw + 'T' + Bw + cz + 'T' + inv(cz) + inv(Bw) + inv(cw)
        c3 = Cert(w2, cw + 'T' + Bw + 't' + inv(Bw) + inv(cw), [(len(cw) + 1 + len(Bw), self.L2, False)])
        # T passes Bw
        pos = len(cw); steps = []
        for y in Bw:
            k, d = self.passT[y]
            steps.append((pos, k, not d)); pos += 1
        w3 = cw + Bw + 'T' + 't' + inv(Bw) + inv(cw)
        c4 = Cert(cw + 'T' + Bw + 't' + inv(Bw) + inv(cw), w3, steps)
        # T t -> t T : c2_Tt forward
        c5 = Cert(w3, cw + Bw + 'tT' + inv(Bw) + inv(cw), [(pos, R.index['c2_Tt'], True)])
        pos += 1
        steps = []
        for y in inv(Bw):
            k, d = self.passT[y]
            steps.append((pos, k, not d)); pos += 1
        w6 = cw + Bw + 't' + inv(Bw) + 'T' + inv(cw)
        c6 = Cert(cw + Bw + 'tT' + inv(Bw) + inv(cw), w6, steps)
        # t -> cz T inv(cz)
        c7 = Cert(w6, cw + Bw + cz + 'T' + inv(cz) + inv(Bw) + 'T' + inv(cw),
                  [(len(cw) + len(Bw), self.L2, True)])
        # insert inv(cw) cw before the second T
        pre = cw + Bw + cz + 'T' + inv(cz) + inv(Bw)
        c8 = C.eq('', inv(cw) + cw).ctx(pre, 'T' + inv(cw))
        c9 = self.conjT(A, q).ctx('', rw(p))
        cert = c1.then(c2).then(c3).then(c4).then(c5).then(c6).then(c7).then(c8).then(c9).check(R.rules)
        k = R.add(lhs, rw(q) + rw(p), 'L7_%s_%s' % (a, b), cert.steps)
        self.L7[(a, b)] = k
        return k

    # ---- normal forms ------------------------------------------------------
    def normal(self, word):
        """Certificate word -> NF, and the NF."""
        C, R = self.C, self.R
        parts = [''] * 6
        rots = []
        steps = []
        cur = word
        def rotstart(i):
            return len(''.join(parts)) + sum(len(rw(p)) for p in rots[:i])
        def push_letter(x, i):
            """letter x sits right after rotation i-1 (i.e. before rotation i) ; push it into C."""
            nonlocal parts, steps
            for j in reversed(range(i)):
                k = self.l4(rots[j], x)
                steps.append((rotstart(j), k, True))
                rots[j] = conj_inv(MAT[x], rots[j])
            parts, st = C.append(parts, 5, x, 0)
            steps += st
        processed = 0   # length of the processed prefix (NF + rotations)
        for x in word:
            if x in 'wHhSsZ':
                push_letter(x, len(rots))
            elif x == 'T':
                rots.append((1, 'ZI'))
            elif x == 't':
                steps.append((rotstart(len(rots)), self.L2, True))
                rots.append((1, 'IZ'))
        # canonicalization: signs, merges, lexicographic normal form of the trace
        def swap(j):
            """rotations j, j+1 (commuting) exchanged."""
            a, b = rots[j], rots[j + 1]
            steps.append((rotstart(j), self.l7(a[1], b[1]), True))
            rots[j], rots[j + 1] = b, a
        for _round in range(100000):
            neg = [k for k, q in enumerate(rots) if q[0] < 0]
            if neg:
                k = neg[-1]
                a = rots[k][1]
                steps.append((rotstart(k), self.l5(a), True))
                rots[k] = (1, a)
                for y in self.eword(a):
                    push_letter(y, k)
                continue
            done = True
            # merge: equal rotations that can be made adjacent
            for jj in range(len(rots)):
                for ii in range(jj - 1, -1, -1):
                    if rots[ii] == rots[jj]:
                        if all(commute(rots[jj], rots[t]) for t in range(ii + 1, jj)):
                            for t in range(jj - 1, ii, -1):
                                swap(t)
                            a = rots[ii]
                            steps.append((rotstart(ii), self.l6(a[1]), True))
                            del rots[ii:ii + 2]
                            for y in self.fword(a[1]):
                                push_letter(y, ii)
                            done = False
                        break
                    if not commute(rots[ii], rots[jj]):
                        break
                if not done: break
            if not done: continue
            # lexicographic normal form: a letter moves left past commuting larger ones
            for jj in range(len(rots)):
                a = rots[jj]
                ii = jj
                while ii > 0 and commute(rots[ii - 1], a):
                    ii -= 1
                # smallest position ii whose letter is larger than a, among those reachable
                tgt = None
                for t in range(ii, jj):
                    if ORDER[rots[t][1]] > ORDER[a[1]]:
                        tgt = t; break
                if tgt is not None:
                    for t in range(jj - 1, tgt - 1, -1):
                        swap(t)
                    done = False
                    break
            if done: break
        else:
            raise Exception('canonicalization did not terminate')
        nf = ''.join(parts) + ''.join(rw(p) for p in rots)
        cert = Cert(word, nf, steps).check(R.rules)
        return cert, nf, rots

from ct import CX, CXw, Tdg, AX as _AX

def lemma_rules(RC):
    """lemma-rel-A and lemma-rel-B of the authors' code: (rel-A word)^2 = e, (rel-B word)^2 = e."""
    C, R = RC.C, RC.R
    ix = R.index
    out = {}
    if 'LRA' not in ix:
        A = 't' + 'h' + Tdg(1)
        w1 = A + CXw(1) + A + CX(1)
        l18, r18 = [(l, r) for (l, r, n) in _AX if n == 'c18'][0]
        assert w1 == r18
        word = w1 + w1
        c1 = Cert(word, l18 + w1, [(0, ix['c18'], False)])
        c2, nf, _ = RC.normal(l18 + w1)
        assert nf == '', nf
        R.add(word, '', 'LRA', c1.then(c2).check(R.rules).steps)
    if 'LRB' not in ix:
        l19, r19 = [(l, r) for (l, r, n) in _AX if n == 'c19'][0]
        word = l19 + l19
        c1 = Cert(word, r19 + l19, [(0, ix['c19'], True)])
        c2, nf, _ = RC.normal(r19 + l19)
        assert nf == '', nf
        R.add(word, '', 'LRB', c1.then(c2).check(R.rules).steps)
    return R.index['LRA'], R.index['LRB']

def chain_cert(RC, n, start, end, chain, local_rules):
    """Certificate start -> end following the special steps of an Agda chain."""
    from agda_chain import special_steps, expand
    R = RC.R
    kA, kB = lemma_rules(RC)
    total = Cert(start, start, [])
    cur = start
    for (before, pos, ln, by, after, name, fwd) in special_steps(chain, local_rules):
        Wb, Wa = expand(before), expand(after)
        c1, n1, r1 = RC.normal(cur)
        c2, n2, r2 = RC.normal(Wb)
        assert n1 == n2, (n, name, r1, r2)
        total = total.then(c1).then(c2.rev())
        p = len(expand(before[:pos]))
        k = {'rel-C': R.index['c20'], 'lemma-rel-A': kA, 'lemma-rel-B': kB}.get(name)
        if k is None: k = local_rules[name]
        step = Cert(Wb, Wa, [(p, k, fwd)]).check(R.rules)
        total = total.then(step)
        cur = Wa
    c1, n1, r1 = RC.normal(cur)
    c2, n2, r2 = RC.normal(end)
    assert n1 == n2, (n, 'end', r1, r2)
    return total.then(c1).then(c2.rev()).check(R.rules)

def hard_cert(RC, n, l, r):
    from agda_chain import chains, expand
    R = RC.R
    ch = chains(n)
    local_rules = {}
    main = 'eqn%d' % n
    for name, chain in ch.items():
        if name == main: continue
        a, b = expand(chain[0][0]), expand(chain[-1][0])
        rn = 'LE%d_%s' % (n, name.replace('-', '_'))
        if rn not in R.index:
            cert = chain_cert(RC, n, a, b, chain, local_rules)
            R.add(a, b, rn, cert.steps)
        local_rules[name] = R.index[rn]
    return chain_cert(RC, n, l, r, ch[main], local_rules)

if __name__ == '__main__':
    import __main__
    __main__.CliffNF = CliffNF; __main__.Cert = Cert
    with open(os.path.join(WORK, 'cliffnf.pkl'), 'rb') as f:
        C = pickle.load(f)
    RC = RotCert(C)
    t0 = time.time()
    good = {}
    only = [int(a) for a in sys.argv[1:]]
    for n, (l, r) in EQN.items():
        if only and n not in only: continue
        if n in (21, 28, 30, 43, 44, 46):
            try:
                cert = hard_cert(RC, n, l, r)
                good[n] = cert.steps
                print(n, 'ok (hard)', len(cert.steps), flush=True)
            except Exception as e:
                print(n, 'HARD FAILED', repr(e)[:300], flush=True)
            continue
        cl, nl, rl = RC.normal(l)
        cr, nr, rr = RC.normal(r)
        if nl == nr:
            cert = cl.then(cr.rev())
            good[n] = cert.steps
            print(n, 'ok', len(cert.steps), '%.0fs' % (time.time() - t0), flush=True)
        else:
            print(n, 'DIFF', rl, rr, flush=True)
    with open(os.path.join(WORK, 'eqcerts.pkl'), 'wb') as f:
        pickle.dump((C.R.rules, C.R.proofs, C.R.index, good), f)
    print('rules', len(C.R.rules))

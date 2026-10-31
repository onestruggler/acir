"""Face transport: a face action h_F : {0,1} x Gen2 -> Word Gen x {0,1} reading a pair word as
gates on the face q_s = x (the pair (a, b) of the other qubits, a the upper one), the letter CS
flipping the coset; at coset 1 the images are conjugated by the CS of the face.  Hypothesis (b)
of rs_claimB for Rel2 is a finite list of three-qubit identities (`b_list`), each proved from
Figure 2 by the block groups.  `decode_face` identifies a word over the face's decoded letters
with hstar of a pair word, so that a face identity follows from `complete2` (checked by sem2)."""
import numpy as np
from qc import key, eq, MAT2, mat2
from fig2 import rels2
from table import Deriv, invert
from cross import Ctrl, short_word, inv_word
from pc import prove_any

CSL = {(0, 1): 'C01', (1, 2): 'C12', (0, 2): 'C02'}
CZL = {(0, 1): 'CZ01', (1, 2): 'CZ12', (0, 2): 'CZ02'}
GEN2 = ['i', 'Ku', 'Kl', 'Su', 'Sl', 'CS']


class FaceAction:
    def __init__(self, P, CT, s, x):
        self.P, self.CT, self.s, self.x = P, CT, s, x
        a, b = sorted(set(range(3)) - {s})
        self.a, self.b = a, b
        A = P.A
        tag = 'F%d%d' % (s, x)
        self.tag = tag
        self.cs = CSL[(a, b)]
        inv3 = lambda z: (z, z, z)
        self.img = {0: {}, 1: {}}
        Ka = self._letter(tag + 'Ka', CT.word(a, s, x))
        Kb = self._letter(tag + 'Kb', CT.word(b, s, x))
        if x == 1:
            Su, Sl, il = (CSL[tuple(sorted((s, a)))],), (CSL[tuple(sorted((s, b)))],), ('S%d' % s,)
            CS2 = ('CCZ',)
        else:
            Su = ('S%d' % a,) + inv3(CSL[tuple(sorted((s, a)))])
            Sl = ('S%d' % b,) + inv3(CSL[tuple(sorted((s, b)))])
            il = ('i',) + inv3('S%d' % s)
            CS2 = (CZL[(a, b)], 'CCZ')
        Ea = self._letter(tag + 'Ea', (self.cs,) + Ka + inv3(self.cs))
        Eb = self._letter(tag + 'Eb', (self.cs,) + Kb + inv3(self.cs))
        for c in (0, 1):
            self.img[c]['i'] = (il, c)
            self.img[c]['Su'] = (Su, c)
            self.img[c]['Sl'] = (Sl, c)
        self.img[0]['Ku'], self.img[0]['Kl'] = (Ka, 0), (Kb, 0)
        self.img[1]['Ku'], self.img[1]['Kl'] = (Ea, 1), (Eb, 1)
        self.img[0]['CS'] = ((), 1)
        self.img[1]['CS'] = (CS2, 0)
        self.check()

    def _letter(self, name, word):
        A = self.P.A
        if name not in A.mats:
            A.define(name, tuple(word))
        return (name,)

    # the face embedding of a 4x4 matrix
    def embed(self, m2):
        s, x, a, b = self.s, self.x, self.a, self.b
        m = np.eye(8, dtype=complex)
        for p in range(4):
            for q in range(4):
                pu, pl = p >> 1, p & 1
                qu, ql = q >> 1, q & 1
                P3 = [0, 0, 0]; Q3 = [0, 0, 0]
                P3[a], P3[b], P3[s] = pu, pl, x
                Q3[a], Q3[b], Q3[s] = qu, ql, x
                pi = P3[0] * 4 + P3[1] * 2 + P3[2]
                qi = Q3[0] * 4 + Q3[1] * 2 + Q3[2]
                m[pi, qi] = m2[p, q]
        return m

    def check(self):
        A = self.P.A
        CSm = MAT2['CS']
        for c in (0, 1):
            for y in GEN2:
                wd, c2 = self.img[c][y]
                m2 = MAT2[y]
                if c == 1:
                    m2 = CSm @ m2 @ np.linalg.inv(CSm)
                if y == 'CS':
                    # coset bookkeeping: image is the embedding of CS^(c) y CS^(-c2)
                    m2 = np.linalg.matrix_power(CSm, c) @ MAT2['CS'] @ np.linalg.matrix_power(np.linalg.inv(CSm), c2)
                assert eq(A.matw(wd), self.embed(m2)), (self.tag, c, y)

    def hstar(self, c, w):
        out = ()
        for y in w:
            u, c = self.img[c][y]
            out += u
        return out, c

    def b_list(self):
        out = []
        for nm, l, r in rels2():
            for c in (0, 1):
                u, cu = self.hstar(c, l)
                v, cv = self.hstar(c, r)
                assert cu == cv
                out.append((nm, c, u, v))
        return out

    def prove_b(self, verbose=True):
        res = []
        for nm, c, u, v in self.b_list():
            e = prove_any(self.P, u, v)
            res.append((nm, c, u, v, e))
        return res


def main():
    import pickle, sys, time
    sys.setrecursionlimit(1000000)
    from pc import PC, define_phase_c
    t = time.time()
    W, pushes, cancels = pickle.load(open('w3L.pkl', 'rb'))
    P = PC(W)
    P.pushes, P.cancels = pushes, cancels
    define_phase_c(P)
    CT = Ctrl(P)
    print('loaded %.1fs' % (time.time() - t), flush=True)
    for s, x in [(2, 1), (2, 0), (0, 0)]:
        F = FaceAction(P, CT, s, x)
        ok = bad = 0
        for nm, c, u, v in F.b_list():
            try:
                prove_any(P, u, v)
                ok += 1
            except (ValueError, AssertionError) as ex:
                bad += 1
                print('  ', F.tag, nm, c, ' '.join(u), '=', ' '.join(v), flush=True)
        print(F.tag, 'ok', ok, 'bad', bad, '%.1fs' % (time.time() - t), flush=True)


if __name__ == '__main__':
    main()

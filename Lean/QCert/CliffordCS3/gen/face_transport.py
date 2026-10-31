"""Proof-producing transport of two-qubit equalities to a controlled face.

The extra table justification records the complete finite check of the coset
action, and the two pair words whose equality is to be checked by Lean.
"""
import numpy as np
from ft import FaceAction
from pc import prove_any
from cross import letterwise
from table import Deriv, invert
from ctv import word_of
import b2two


class FaceProof(FaceAction):
    pair_group = None

    def __init__(self, P, CT, s, x):
        super().__init__(P, CT, s, x)
        self.b_proofs = []
        self.preimages = {}
        for nm, c, u, v in self.b_list():
            if nm == 'comm_Ku_Kl':
                e = self.comm_k(c, u, v)
            else:
                e = prove_any(P, u, v)
            self.b_proofs.append(e)

    def comm_k(self, c, u, v):
        P, T = self.P, self.P.T
        if c == 0:
            Du, Dv = Deriv(T, u), Deriv(T, v)
            for D in (Du, Dv):
                D.step(1, P.A.defs[D.w[1]], True)
                D.step(0, P.A.defs[D.w[0]], True)
            a = P.A.defs[u[0]]
            da = T.eqs[a][1]
            db = T.eqs[P.A.defs[u[1]]][1]
            e = letterwise(P, da, db)
            return T.derived(u, v, Du.steps + [(0, e, True)] + invert(Dv.steps))
        a = self.img[0]['Ku'][0][0]
        b = self.img[0]['Kl'][0][0]
        e0 = self.comm_k(0, (a, b), (b, a))
        cancel = prove_any(P, (self.cs,) * 4, ())
        def expand_pair(w):
            D = Deriv(T, w)
            D.step(1, P.A.defs[w[1]], True)
            D.step(0, P.A.defs[w[0]], True)
            D.step(2, cancel, True)
            return D
        Du, Dv = expand_pair(u), expand_pair(v)
        return T.derived(u, v, Du.steps + [(1, e0, True)] + invert(Dv.steps))

    def preimage(self, z):
        if z in self.preimages:
            return self.preimages[z]
        P = self.P
        if FaceProof.pair_group is None:
            FaceProof.pair_group = b2two.build()
        W2 = FaceProof.pair_group
        inds = []
        for p in range(4):
            bits = [0, 0, 0]
            bits[self.a], bits[self.b], bits[self.s] = p >> 1, p & 1, self.x
            inds.append(4 * bits[0] + 2 * bits[1] + bits[2])
        m = P.A.mats[z][np.ix_(inds, inds)]
        assert np.allclose(self.embed(m), P.A.mats[z]), (self.tag, z, 'outside face')
        for G in W2.groups:
            wd = word_of(G, m)
            if wd is None:
                continue
            w2 = W2.A.expand(wd)
            decoded, c = self.hstar(0, w2)
            assert c == 0, (self.tag, z, 'odd determinant')
            e = prove_any(P, (z,), decoded)
            self.preimages[z] = (w2, decoded, e)
            return self.preimages[z]
        raise ValueError(('no pair preimage', self.tag, z))

    def prove(self, u, v):
        P, T = self.P, self.P.T
        def expand(word):
            D = Deriv(T, word)
            w2, i = (), 0
            for z in word:
                wz, dz, e = self.preimage(z)
                if e is not None:
                    D.step(i, e, True)
                i += len(dz)
                w2 += wz
            assert self.hstar(0, w2) == (D.w, 0)
            return D, w2
        Du, wu = expand(tuple(u))
        Dv, wv = expand(tuple(v))
        e = T._add(Du.w, Dv.w, ('face', self.s, self.x, wu, wv, tuple(self.b_proofs)), None)
        return T.derived(tuple(u), tuple(v), Du.steps + [(0, e, True)] + invert(Dv.steps))

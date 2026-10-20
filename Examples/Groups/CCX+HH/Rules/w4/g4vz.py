#!/usr/bin/env python3
"""A finder for the four-wire group over the signed permutations V_Z.

The partial proof-producing enumeration of `../wn/finder.py`, but over
V_Z instead of AGL(4, 2): its cosets are the lattices g·ℤ¹⁶.  The
subgroup's generators (macros) are the 34 classical letters and the
14 non-constant monomial gates (Z_t, CZ_ab, CCZ_abc as HH · X-gate ·
HH); a label is kept canonical by its signed permutation: the monomials
of the algebraic normal form of its signs (−I as Z0 X0 Z0 X0), then the
A16 tower's canonical word of its permutation (`canonA16.py`).  A norm
step is an instance of completeness for V_Z.

    from g4vz import VZFinder
"""
import itertools
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'wn'))
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))
import labelled as LB
import proofs as PR
import finder as F
import canonA16 as CA
from diag4 import MONOS, mono_word

N, D = 4, 16


class VZFinder:
    def __init__(self, extra=(), kick=True, coarse=2):
        A0 = F.Alphabet(N, r4=True, placed=True)
        ex = set(tuple(r) for r in extra)
        if coarse:
            for kind in [('P', w) for w in range(N)] + [('C',)]:
                ex |= A0.short_identities(kind, coarse)
        if kick:
            import kick as KK
            for t, a, b, c in itertools.permutations(range(N)):
                ex.add(KK.kick(A0, 'CCZ', t, a, b, c))
        self.A = A = F.Alphabet(N, r4=True, placed=True, extra=sorted(ex, key=lambda r: (len(r), r)))
        nl = len(A.LETTERS)
        self.cls = [g for g, l in enumerate(A.LETTERS) if l[0] != 'HH']
        # macros: classical letters, and the non-constant monomials
        self.macros = {g: (g,) for g in self.cls}
        self.mono_id = {}
        for k, m in enumerate(MONOS):
            if m:
                self.mono_id[m] = nl + k
                self.macros[nl + k] = mono_word(A, m)
        self.cache = {}

    # -----------------------------------------------------------------
    def signed(self, word):
        """(signs d[y] in {1, -1} by row, permutation p) of a word whose
        matrix is a signed permutation, or None."""
        M = self.A.matrix(word)
        p, d = [0] * D, [1] * D
        for i, (s, w) in enumerate(M):
            if s != 0:
                return None
            nz = [y for y in range(D) if w[y]]
            if len(nz) != 1 or abs(w[nz[0]]) != 1:
                return None
            y = nz[0]
            p[i] = y
            d[y] = w[y]
        return tuple(d), tuple(p)

    def anf(self, d):
        """The monomials (sorted tuples of wires) of f with (-1)^f = d."""
        f = [1 if x == -1 else 0 for x in d]
        a = list(f)
        for t in range(N):
            for x in range(D):
                if x >> t & 1:
                    a[x] ^= a[x ^ (1 << t)]
        return [tuple(t for t in range(N) if x >> t & 1) for x in range(D) if a[x]]

    def canon_label(self, d, p):
        lab = []
        for m in self.anf(d):
            if m == ():
                z0 = self.mono_id[(0,)]
                x0 = self.A.IX['X0']
                lab += [z0, x0, z0, x0]
            else:
                assert len(m) <= 3, m
                lab.append(self.mono_id[m])
        lab += list(CA.canon(p))
        return tuple(lab)

    def normal(self, lab, dec):
        key = tuple(lab)
        if key not in self.cache:
            sp = self.signed(dec(lab))
            assert sp is not None, 'a label left V_Z'
            self.cache[key] = self.canon_label(*sp)
        return self.cache[key]

    # -----------------------------------------------------------------
    def derive(self, target, limit, verbose=False):
        vz = self

        class PTC(LB.LabelledTC):
            def join(tc, left, right):
                lab = tuple(left) + tuple(right)
                nf = vz.normal(lab, tc.dec)
                if nf == lab:
                    return lab, []
                f = tc._add(tc.dec(lab), tc.dec(nf), [(0, ('norm', (lab, nf)), True)])
                return nf, [(0, ('fact', f), True)]

        axioms = [PR.Axiom(f'r{j}', r, ()) for j, r in enumerate(self.A.rels)]
        seeds = [tuple(target[:i]) for i in range(1, len(target) + 1)]
        tc = PTC(len(self.A.LETTERS), axioms, self.macros, seed=seeds, limit=limit)
        try:
            tc.run()
            closed = True
        except OverflowError:
            closed = False
        i, f, lab, st = tc.walk(0, tuple(target))
        ok = i == len(target) and tc.root(f) == 0 and lab == ()
        if verbose:
            print(f'  {"closed" if closed else "stopped"} at {len(tc.rep)} cosets; '
                  f'trace {i}/{len(target)} ends at {tc.root(f)} label {lab}', flush=True)
        return (tc, tc._add(tuple(target), (), st)) if ok else None


if __name__ == '__main__':
    import time
    V = VZFinder()
    A = V.A
    print(len(A.rels), 'relators', flush=True)
    # smoke test: a V_Z identity and an R4
    tests = {
        'CX0>1 commutes with CZ23': 'CX0>1 HH03 CX2>3 HH03 CX0>1 HH03 CX2>3 HH03',
        'R4': 'CCX0;12 HH03 CCX0;12 HH03 CCX0;12 HH03 CCX0;12 HH03 HH02 CX1>2 HH02',
    }
    for name, t in tests.items():
        w = A.word(t)
        assert A.is_identity(w)
        t0 = time.time()
        r = V.derive(w, 20000, verbose=True)
        print(name, 'derived' if r else 'NOT derived', round(time.time() - t0, 1), 's', flush=True)

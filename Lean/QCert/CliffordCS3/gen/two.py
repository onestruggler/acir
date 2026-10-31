"""Two-qubit derivations (the fragment (a)-(c) of Figure 2 on a pair u, l).

The proof table over an extended alphabet (`ext.Alpha`): the base letters i, Ku, Kl, Su, Sl,
CS, the axioms (a)-(c) with the commutations, and defined letters (CZ = CS CS, X_u, X_l, the
decodings of the macro letters).  Coset tables with proofs (`ctv.CTV`) for the finite groups

  A_u = <i, Ku, Su, Sl, CS>, A_l = <i, Kl, Su, Sl, CS>          over D  = <i, Su, Sl, CS>,
  C2  = <i, Ku, Kl, Su, Sl, CZ> (the Clifford group)              over DC = <i, Su, Sl, CZ>,
  M2  = <i, Su, Sl, CS, Xu, Xl, T0, T1, T2> (monomial matrices)  over D,
  AlX = <i, Su, Sl, CS, Kl, Xu>, AuX = <i, Su, Sl, CS, Ku, Xl>   over D,

each proved from the axioms (A_u, A_l) or from equations proved in the groups before it.
"""
import numpy as np
from collections import deque
from qc import MAT2, key, eq
from fig2 import rels2
from table import Deriv
from ext import Alpha
from ctv import Abelian, Inverses, CTV

BASE = ['i', 'Ku', 'Kl', 'Su', 'Sl', 'CS']


class Two:
    def __init__(self, decodings, verbose=False):
        self.verbose = verbose
        A = self.A = Alpha({a: MAT2[a] for a in BASE})
        T = self.T = A.T
        self.ax = {}
        for nm, l, r in rels2():
            self.ax[nm] = T.axiom(l, r, nm)
        A.define('CZ', ('CS', 'CS'))
        A.define('Xu', ('Ku', 'Su', 'Su', 'Ku', 'i'))
        A.define('Xl', ('Kl', 'Sl', 'Sl', 'Kl', 'i'))
        for nm, w in decodings.items():
            A.define(nm, w)
        A.define('CXb', ('Ku', 'CS', 'CS', 'Ku', 'i'))
        if 'T2' in decodings:
            A.define('SW', ('T2', 'CXb', 'T2'))
        self.groups = []
        self._inverses()

    # ------------------------------------------------------------------ inverses
    def _inverses(self):
        T, ax = self.T, self.ax
        inv = {'i': ('i',) * 3, 'Ku': ('Ku', 'i'), 'Kl': ('Kl', 'i'), 'Su': ('Su',) * 3,
               'Sl': ('Sl',) * 3, 'CS': ('CS',) * 3}
        right, left = {}, {}
        right['i'] = left['i'] = (ax['c1'], True)
        for q in 'ul':
            right['S' + q] = left['S' + q] = (ax['c3' + q], True)
        right['CS'] = left['CS'] = (ax['c5'], True)
        for q in 'ul':
            K = 'K' + q
            e = T.derived((K, K, 'i'), (), [(0, ax['c2' + q], True), (0, ax['c1'], True)])
            right[K] = (e, True)
            e2 = T.derived((K, 'i', K), (), [(1, ax['comm_i_' + K], True), (0, e, True)])
            left[K] = (e2, True)
        self.inv = Inverses(inv, right, left)

    def add_inverse(self, x, invw, eright, eleft):
        self.inv.inv[x] = tuple(invw)
        self.inv.right[x] = (eright, True)
        self.inv.left[x] = (eleft, True)

    # ------------------------------------------------------------------ diagonal groups
    def comm_eq(self, a, b):
        """(eid, d) rewriting 'a b' into 'b a' (a, b commuting letters of the diagonal groups)."""
        T, ax = self.T, self.ax
        for nm in ['comm_i_%s' % b, 'comm_i_%s' % a, 'comm_Su_Sl', 'c6', 'c7']:
            if nm in ax:
                l, r, _ = T.eqs[ax[nm]]
                if l == (a, b) and r == (b, a):
                    return (ax[nm], True)
                if r == (a, b) and l == (b, a):
                    return (ax[nm], False)
        if 'CZ' in (a, b):
            x = b if a == 'CZ' else a
            dz = self.A.defs['CZ']
            if a == 'CZ':
                cs_x = self.comm_eq('CS', x)
                D = Deriv(T, ('CZ', x))
                D.step(0, dz, True)
                D.step(1, *cs_x)
                D.step(0, *cs_x)
                D.step(1, dz, False)
                return (T.derived(('CZ', x), (x, 'CZ'), D.steps), True)
            xcs = self.comm_eq(x, 'CS')
            D = Deriv(T, (x, 'CZ'))
            D.step(1, dz, True)
            D.step(0, *xcs)
            D.step(1, *xcs)
            D.step(0, dz, False)
            return (T.derived((x, 'CZ'), ('CZ', x), D.steps), True)
        raise KeyError((a, b))

    def abelian(self, letters, orders):
        comm = {}
        for i, a in enumerate(letters):
            for b in letters[:i]:
                comm[(a, b)] = self.comm_eq(a, b)
        power = {}
        for a, o in zip(letters, orders):
            assert self.inv.inv[a] == (a,) * (o - 1), a
            power[a] = self.inv.right[a]
        return Abelian(letters, orders, self.A.mats, comm, power)

    # ------------------------------------------------------------------ proving
    def expand_word(self, w):
        D = Deriv(self.T, w)
        self.A.unfold(D, 0, len(D.w))
        return D

    def contract_cz(self, D):
        """Rewrite every adjacent 'CS CS' of D.w into CZ (left to right)."""
        dz = self.A.defs['CZ']
        i = 0
        while i + 1 < len(D.w):
            if D.w[i] == 'CS' and D.w[i + 1] == 'CS':
                D.step(i, dz, False)
            i += 1
        return D

    def prove_with(self, G, u, v, prep):
        """u = v in the group G after rewriting both sides by `prep` (a function of a Deriv)."""
        Du = Deriv(self.T, u)
        prep(Du)
        Dv = Deriv(self.T, v)
        prep(Dv)
        if Du.w == Dv.w:
            steps = Du.steps + [(p, k, not d) for (p, k, d) in reversed(Dv.steps)]
            return self.T.derived(u, v, steps)
        if not set(Du.w) | set(Dv.w) <= set(G.letters):
            return None
        e = G.prove(Du.w, Dv.w)
        steps = Du.steps + [(0, e, True)] + [(p, k, not d) for (p, k, d) in reversed(Dv.steps)]
        return self.T.derived(u, v, steps)

    def prove(self, u, v):
        """u = v by one of the groups, with the letters as they are, expanded, or expanded
        with CS CS contracted to CZ."""
        u, v = tuple(u), tuple(v)
        if u == v:
            return None
        unfold = lambda D: self.A.unfold(D, 0, len(D.w))
        cz = lambda D: (self.A.unfold(D, 0, len(D.w)), self.contract_cz(D))
        for G in self.groups:
            for prep in (lambda D: None, unfold, cz):
                e = self.prove_with(G, u, v, prep)
                if e is not None:
                    return e
        raise ValueError('no group proves %s = %s' % (u, v))

    def add_group(self, name, letters, H, relators):
        G = CTV(self.T, letters, self.A.mats, H, self.inv, relators, verbose=self.verbose, name=name)
        ok = G.deduce_all()
        if self.verbose:
            print(' ', name, 'complete' if ok else 'INCOMPLETE', 'eqs', len(self.T.eqs), flush=True)
        assert ok, name
        self.groups.append(G)
        setattr(self, name, G)
        return G


def min_rules(letters, mats, n=4):
    """The minimal complete rewriting system of the shortlex normal forms of a finite group."""
    e = np.eye(n, dtype=complex)
    nf = {key(e): ()}
    elem = {(): e}
    dq = deque([()])
    while dq:
        w = dq.popleft()
        m = elem[w]
        for a in letters:
            p = m @ mats[a]
            k = key(p)
            if k not in nf:
                nf[k] = w + (a,)
                elem[w + (a,)] = p
                dq.append(w + (a,))
    isnf = set(nf.values())
    rules = []
    for w in isnf:
        for a in letters:
            v = w + (a,)
            if v in isnf:
                continue
            if all(v[i:] in isnf for i in range(1, len(v))):
                rules.append((v, nf[key(elem[w] @ mats[a])]))
    return rules, len(nf)


def build(decodings, verbose=False):
    W = Two(decodings, verbose)
    T = W.T
    # CZ, Xu, Xl inverses: CZ CZ = e, X X = e
    for x in ['CZ', 'Xu', 'Xl']:
        D = W.expand_word((x, x))
        if x == 'CZ':
            D.step(0, W.ax['c5'], True)
        e = None
        W.inv.inv[x] = (x,)
    D0 = W.abelian(['i', 'Su', 'Sl', 'CS'], [4, 4, 4, 4])
    rels = lambda L: [W.ax[nm] for nm, l, r in rels2() if set(l) | set(r) <= set(L)]
    Lu = ['i', 'Su', 'Sl', 'CS', 'Ku']
    Ll = ['i', 'Su', 'Sl', 'CS', 'Kl']
    W.add_group('Au', Lu, D0, rels(Lu))
    W.add_group('Al', Ll, D0, rels(Ll))
    # involutions CZ, Xu, Xl: x x = e, proved in A_u / A_l after expansion
    for x in ['CZ', 'Xu', 'Xl']:
        e = W.prove((x, x), ())
        W.add_inverse(x, (x,), e, e)
    DC = W.abelian(['i', 'Su', 'Sl', 'CZ'], [4, 4, 4, 2])
    rel = []
    for G, L in [(W.Au, ['i', 'Su', 'Sl', 'CZ', 'Ku']), (W.Al, ['i', 'Su', 'Sl', 'CZ', 'Kl'])]:
        R, order = min_rules(L, W.A.mats)
        for u, v in R:
            rel.append(W.prove(u, v))
    for a, b in [('Ku', 'Kl'), ('Ku', 'Sl'), ('Su', 'Kl')]:
        rel.append(W.ax['comm_%s_%s' % (a, b)])
    W.add_group('C2', ['i', 'Su', 'Sl', 'CZ', 'Ku', 'Kl'], DC, rel)
    return W


if __name__ == '__main__':
    import time
    t = time.time()
    W = build({}, True)
    print('time %.1f' % (time.time() - t), 'steps', sum(W.T.size(i) for i in range(len(W.T.eqs))))


def seg_normalize(W, G, D):
    """Rewrite every maximal segment of D.w over the letters of G into G's normal form."""
    L = set(G.letters)
    i = 0
    while i < len(D.w):
        if D.w[i] not in L:
            i += 1
            continue
        j = i
        while j < len(D.w) and D.w[j] in L:
            j += 1
        seg = D.w[i:j]
        D2 = Deriv(W.T, seg)
        G.normalize_word(seg, D2, 0)
        D.steps_at(D2.steps, i)
        i += len(D2.w)
    return D


def prove_frames(W, u, v):
    """u = v after normalizing the monomial segments (M2) and unfolding all letters but Xu, Xl."""
    u, v = tuple(u), tuple(v)
    M2L = set(W.M2.letters)
    def prep_keep(D):
        i = 0
        while i < len(D.w):
            a = D.w[i]
            if a in W.A.defs and a not in M2L:
                D.step(i, W.A.defs[a], True)
            else:
                i += 1
        seg_normalize(W, W.M2, D)
        i = 0
        while i < len(D.w):
            a = D.w[i]
            if a in W.A.defs and a not in ('Xu', 'Xl'):
                W.A.unfold(D, i, i + 1)
            else:
                i += 1
    for G in W.groups:
        e = W.prove_with(G, u, v, prep_keep)
        if e is not None:
            return e
    raise ValueError('frames: no group proves %s = %s' % (u, v))


def prove_any(W, u, v):
    u, v = tuple(u), tuple(v)
    if u == v:
        return None
    try:
        return W.prove(u, v)
    except ValueError:
        return prove_frames(W, u, v)


def rewrite(W, D, i, j, target):
    """Replace D.w[i:j] by target, by an equation proved with `prove_any`."""
    seg = D.w[i:j]
    e = prove_any(W, seg, tuple(target))
    if e is not None:
        D.step(i, e, True)


def chain(W, u, v, moves):
    """A derivation of u = v by segment rewrites `moves` [(i, j, target)], ending at v."""
    D = Deriv(W.T, u)
    for i, j, target in moves:
        rewrite(W, D, i, j, target)
    assert D.w == tuple(v), (D.w, v)
    return W.T.derived(u, v, D.steps)

"""Three-qubit derivations from Figure 2 (`Rel`), with two-qubit steps for free.

The proof table over an extended alphabet (`ext.Alpha` over the nine generators): the axioms of
Figure 2, defined letters (Section 2.1 and 4.1 abbreviations, the decodings of the macro letters),
and *semantic steps*: an equation between two words on the pair of qubits (0, 1) or (1, 2) with the
same matrix, which completeness on a pair (`QCert.CliffordCS3.Two.complete2`) derives.  Words on the
pair (0, 2) are handled by conjugation with SWAP12 (`sem02`).

Coset tables with proofs (`ctv.CTV`) for finite subgroups, over abelian diagonal subgroups
(`Abelian`), over two-qubit subgroups normalised by one semantic step (`PairGroup`), or over
subgroups already tabled (`Nested`).
"""
import itertools
import numpy as np
from collections import deque
from qc import MAT3, key, eq, kron, I2
from fig2 import rels3
from table import Deriv, invert
from ext import Alpha
from ctv import Abelian, Inverses, CTV, word_of

BASE = ['i', 'K0', 'K1', 'K2', 'S0', 'S1', 'S2', 'C01', 'C12']
# the qubits a base letter acts on
BSUP = {'i': set(), 'K0': {0}, 'K1': {1}, 'K2': {2}, 'S0': {0}, 'S1': {1}, 'S2': {2},
        'C01': {0, 1}, 'C12': {1, 2}}
# base letters on a pair, as letters of Gen2 (u the upper qubit)
PAIR = {0: {'i': 'i', 'K0': 'Ku', 'K1': 'Kl', 'S0': 'Su', 'S1': 'Sl', 'C01': 'CS'},
        1: {'i': 'i', 'K1': 'Ku', 'K2': 'Kl', 'S1': 'Su', 'S2': 'Sl', 'C12': 'CS'}}

DEFS = [
    ('X0', 'K0 S0 S0 K0 i'), ('X1', 'K1 S1 S1 K1 i'), ('X2', 'K2 S2 S2 K2 i'),
    ('Z0', 'S0 S0'), ('Z1', 'S1 S1'), ('Z2', 'S2 S2'),
    ('CZ01', 'C01 C01'), ('CZ12', 'C12 C12'),
    ('CX01', 'K1 C01 C01 K1 i'), ('CX10', 'K0 C01 C01 K0 i'),
    ('CX12', 'K2 C12 C12 K2 i'), ('CX21', 'K1 C12 C12 K1 i'),
    ('SW01', 'CX01 CX10 CX01'), ('SW12', 'CX12 CX21 CX12'),
    ('C02', 'SW12 C01 SW12'), ('CZ02', 'C02 C02'),
    ('CX20', 'K0 CZ02 K0 i'), ('CX02', 'K2 CZ02 K2 i'),
    ('CCZ', 'C02 CX01 C12 C12 C12 CX01 C12'),
    ('CCX0', 'K0 CCZ K0 i'), ('CCX1', 'K1 CCZ K1 i'), ('CCX2', 'K2 CCZ K2 i'),
]


class Three:
    def __init__(self, verbose=False):
        self.verbose = verbose
        A = self.A = Alpha({a: MAT3[a] for a in BASE})
        T = self.T = A.T
        self.ax = {}
        for nm, l, r in rels3():
            self.ax[nm] = T.axiom(l, r, nm)
        for nm, w in DEFS:
            A.define(nm, tuple(w.split()))
        self.groups = []
        self._inverses()

    # ---------------------------------------------------------------- letters
    def sup(self, a):
        s = set()
        for b in self.A.exp[a]:
            s |= BSUP[b]
        return s

    def pair_of(self, w):
        """The pair (0 or 1) a word acts on, if its expansion is on one of them."""
        e = self.A.expand(w)
        letters = set(e)
        for j in (0, 1):
            if letters <= set(PAIR[j]):
                return j
        return None

    # ---------------------------------------------------------------- inverses
    def _inverses(self):
        T, ax = self.T, self.ax
        inv = {'i': ('i',) * 3}
        right, left = {'i': (ax['c1'], True)}, {'i': (ax['c1'], True)}
        for q in range(3):
            S = 'S%d' % q
            inv[S] = (S,) * 3
            right[S] = left[S] = (ax['c3_%d' % q], True)
        for j, c in enumerate(['C01', 'C12']):
            inv[c] = (c,) * 3
            right[c] = left[c] = (ax['c5_%d' % j], True)
        for q in range(3):
            K = 'K%d' % q
            inv[K] = (K, 'i')
            e = T.derived((K, K, 'i'), (), [(0, ax['c2_%d' % q], True), (0, ax['c1'], True)])
            right[K] = (e, True)
            e2 = T.derived((K, 'i', K), (), [(1, ax['comm_i_' + K], True), (0, e, True)])
            left[K] = (e2, True)
        self.inv = Inverses(inv, right, left)

    def add_inverse(self, x, invw, eright, eleft):
        self.inv.inv[x] = tuple(invw)
        self.inv.right[x] = (eright, True)
        self.inv.left[x] = (eleft, True)

    def involution(self, x):
        """Register x as an involution (x x = e proved by `prove`)."""
        e = self.prove((x, x), ())
        self.add_inverse(x, (x,), e, e)
        return e

    # ---------------------------------------------------------------- semantic steps
    def sem(self, u, v):
        """u = v for words on one pair with the same matrix (a semantic step)."""
        u, v = tuple(u), tuple(v)
        j = self.pair_of(u + v)
        assert j is not None, ('not on a pair', u, v)
        return self.T.sem(u, v, ('pair', j))

    def prove(self, u, v):
        """u = v: a semantic step if on a pair, else in one of the tabled groups."""
        u, v = tuple(u), tuple(v)
        if u == v:
            return None
        if self.pair_of(u + v) is not None:
            return self.sem(u, v)
        for G in self.groups:
            e = self.prove_in(G, u, v)
            if e is not None:
                return e
        raise ValueError('no proof of %s = %s' % (' '.join(u), ' '.join(v)))

    def prove_in(self, G, u, v):
        """u = v in G (after unfolding letters not in G one level at a time)."""
        L = set(G.letters)
        Du = Deriv(self.T, u)
        self._fold_into(Du, L)
        Dv = Deriv(self.T, v)
        self._fold_into(Dv, L)
        if Du.w == Dv.w:
            return self.T.derived(u, v, Du.steps + invert(Dv.steps))
        if not set(Du.w) | set(Dv.w) <= L:
            return None
        e = G.prove(Du.w, Dv.w)
        return self.T.derived(u, v, Du.steps + [(0, e, True)] + invert(Dv.steps))

    def _fold_into(self, D, L):
        i = 0
        while i < len(D.w):
            a = D.w[i]
            if a not in L and a in self.A.defs:
                D.step(i, self.A.defs[a], True)
            else:
                i += 1

    # ---------------------------------------------------------------- groups
    def add_group(self, name, letters, H, relators, phases=None):
        G = CTV(self.T, letters, self.A.mats, H, self.inv, relators, verbose=self.verbose,
                name=name, phases=phases)
        ok = G.deduce_all()
        if self.verbose:
            print(' ', name, 'complete' if ok else 'INCOMPLETE (%d missing)' % len(G.missing()),
                  'eqs', len(self.T.eqs), flush=True)
        if ok:
            self.groups.append(G)
            setattr(self, name, G)
        return G, ok


class PairGroup:
    """A finite group of words on one pair: elements by BFS, the canonical word of an element,
    normalisation of a segment by one semantic step."""

    def __init__(self, W, letters, limit=10**6):
        self.W = W
        self.letters = list(letters)
        mats = W.A.mats
        n = 8
        e = np.eye(n, dtype=complex)
        self.can = {key(e): ()}
        dq = deque([((), e)])
        while dq:
            w, m = dq.popleft()
            for a in self.letters:
                p = m @ mats[a]
                k = key(p)
                if k not in self.can:
                    self.can[k] = w + (a,)
                    dq.append((w + (a,), p))
                    if len(self.can) > limit:
                        raise ValueError('pair group too big')
        self.identity = key(e)
        self.elist = None

    def exps(self, m):
        k = key(m)
        return k if k in self.can else None

    def word(self, k):
        return self.can[k]

    def normalize(self, D, s, e):
        seg = D.w[s:e]
        k = key(self.W.A.matw(seg))
        c = self.can[k]
        if seg != c:
            eid = self.W.sem(seg, c)
            D.step(s, eid, True)
        return s + len(c)


class Nested:
    """A tabled group (complete `CTV`) as the subgroup of a coset table."""

    def __init__(self, G):
        self.G = G
        self.letters = G.letters
        self.identity = key(np.eye(8, dtype=complex))
        self.elist = None
        self.memo = {}

    def exps(self, m):
        k = key(m)
        if k in self.memo:
            return k if self.memo[k] is not None else None
        w = word_of(self.G, m)
        self.memo[k] = w
        return k if w is not None else None

    def word(self, k):
        return self.memo[k]

    def normalize(self, D, s, e):
        seg = D.w[s:e]
        D2 = Deriv(self.G.T, seg)
        self.G.normalize_word(seg, D2, 0)
        D.steps_at(D2.steps, s)
        return s + len(D2.w)


def comm_axiom(W, a, b):
    """(eid, d) rewriting 'a b' into 'b a' for base letters with an axiom saying so."""
    T = W.T
    for nm, e in W.ax.items():
        l, r, _ = T.eqs[e]
        if l == (a, b) and r == (b, a):
            return (e, True)
        if l == (b, a) and r == (a, b):
            return (e, False)
    return None


def struct_comm(W, a, b):
    """a b = b a for letters whose expansions commute letter by letter (by axioms, or semantic
    steps for letters on one pair)."""
    T, A = W.T, W.A
    ua, ub = A.expand((a,)), A.expand((b,))
    D = Deriv(T, (a, b))
    A.unfold(D, 0, 2)
    # bubble: move the letters of b (now at the end) to the front
    na, nb = len(ua), len(ub)
    for j in range(nb):
        for i in range(na - 1, -1, -1):
            pos = i + j
            x, y = D.w[pos], D.w[pos + 1]
            st = comm_axiom(W, x, y)
            if st is None:
                st = (W.sem((x, y), (y, x)), True)
            D.step(pos, *st)
    # fold back
    target = ub + ua
    assert D.w == target
    Db = Deriv(T, (b, a))
    A.unfold(Db, 0, 2)
    assert Db.w == target
    return T.derived((a, b), (b, a), D.steps + invert(Db.steps))


def d2(W):
    """The diagonal group D2 = <i, S0, S1, S2, C01, C12> (relations: axioms)."""
    L = ['i', 'S0', 'S1', 'S2', 'C01', 'C12']
    comm = {}
    for i, a in enumerate(L):
        for b in L[:i]:
            st = comm_axiom(W, a, b)
            if st is None:
                st = (W.sem((a, b), (b, a)), True)
            comm[(a, b)] = st
    power = {a: W.inv.right[a] for a in L}
    return Abelian(L, [4] * 6, W.A.mats, comm, power)


def folded(W, eid, lhs, rhs):
    """The equation eid restated over the extended letters lhs = rhs (whose expansions are its
    sides)."""
    T, A = W.T, W.A
    l, r, _ = T.eqs[eid]
    D = Deriv(T, lhs)
    A.unfold(D, 0, len(D.w))
    assert D.w == l, (D.w, l)
    D.step(0, eid, True)
    Dr = Deriv(T, rhs)
    A.unfold(Dr, 0, len(Dr.w))
    assert Dr.w == r
    return T.derived(lhs, rhs, D.steps + invert(Dr.steps))


def w(s):
    return tuple(s.split())


def fig2_folded(W):
    """C12-C15 over the letters CX, CS."""
    out = {}
    out['c12'] = W.ax['c12']
    out['c13'] = folded(W, W.ax['c13'], w('CX10 CX01 C12 CX01 CX10'), w('CX12 CX21 C01 CX21 CX12'))
    out['c14'] = folded(W, W.ax['c14'], w('C12 CX01 C12 C12 C12 CX01'), w('C01 CX21 C01 C01 C01 CX21'))
    out['c15'] = folded(W, W.ax['c15'], w('CX10 CX01 C12 C12 CX01 CX10'), w('CX01 C12 C12 CX01 C12 C12'))
    return out


def local_rels(W, L, pair_letters):
    """Relators: the minimal rewriting systems of the pair groups (semantic steps) and the
    commutations of letters on disjoint qubits."""
    from two import min_rules
    rel = []
    for Lp in pair_letters:
        R, n = min_rules(Lp, W.A.mats, n=8)
        rel += [W.sem(u, v) for u, v in R]
    for a, b in itertools.combinations(L, 2):
        if W.sup(a) and W.sup(b) and not (W.sup(a) & W.sup(b)):
            rel.append(struct_comm(W, a, b))
    return rel


def compact_rels(W, letters):
    """A compact presentation of the pair group on `letters` (one pair), each relation a
    semantic step."""
    from compact import compact
    R, o = compact(letters, W.A.mats)
    return [W.sem(u, v) for u, v in R]


def struct_rels(W, L):
    out = []
    for a, b in itertools.combinations(L, 2):
        if W.sup(a) and W.sup(b) and not (W.sup(a) & W.sup(b)):
            out.append(struct_comm(W, a, b))
    return out


def square_rel(W, eid, lsplit, rsplit):
    """From l = r with l = a x b, r = c y d (x, y single letters) derive a x x b' ... (unused)."""
    raise NotImplementedError

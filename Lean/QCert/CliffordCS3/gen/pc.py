"""Phase C: the three-qubit identities of the coset action for U8 (two cosets), from Figure 2.

Engines (all producing derivations in the proof table `W.T`):
* semantic steps on a pair, the tabled groups of `groups3` (C3, KB1, FS);
* B1 = KB1 + C02 and L1 = B1 x| <X0, X2, CX20, CX02> (the q1-target block group with the block
  permutations), coset tables with proofs over the tables below them;
* relabelling: u = v from sigma(u) = sigma(v), conjugating by a swap SW and pushing it through
  the letters (`push`: SW x SW = sigma(x)); L0 and L2 are L1 relabelled.
"""
import pickle
import sys
import itertools
import numpy as np
from collections import deque
sys.setrecursionlimit(1000000)
from three import Three, PairGroup, Nested, struct_comm, w
from table import Deriv, invert
from ctv import CTV, word_of
from qc import key, eq

LETTERS = ['i', 'K0', 'K1', 'K2', 'S0', 'S1', 'S2', 'C01', 'C12', 'C02', 'X0', 'X1', 'X2',
           'Z0', 'Z1', 'Z2', 'CZ01', 'CZ12', 'CZ02', 'CX01', 'CX10', 'CX12', 'CX21', 'CX02',
           'CX20', 'SW01', 'SW12', 'SW02', 'CCZ', 'CCX0', 'CCX1', 'CCX2']


def qmap(perm):
    """The letter map of a permutation of the qubits (perm[q] = image of q)."""
    out = {}
    for a in LETTERS:
        if a == 'i' or a == 'CCZ':
            out[a] = a
            continue
        if a.startswith('CCX'):
            out[a] = 'CCX%d' % perm[int(a[3])]
            continue
        for pre in ('CX', 'CZ', 'SW', 'C'):
            if a.startswith(pre) and len(a) == len(pre) + 2 and a[len(pre):].isdigit():
                p, q = perm[int(a[-2])], perm[int(a[-1])]
                if pre in ('CZ', 'SW', 'C'):
                    p, q = min(p, q), max(p, q)
                out[a] = '%s%d%d' % (pre, p, q)
                break
        else:
            out[a] = a[0] + str(perm[int(a[1])])
    return out


SIG = {'SW01': qmap({0: 1, 1: 0, 2: 2}), 'SW12': qmap({0: 0, 1: 2, 2: 1})}


def load(path='w3.pkl'):
    with open(path, 'rb') as f:
        return pickle.load(f)


class PC:
    def __init__(self, W, verbose=True):
        self.W = W
        self.T = W.T
        self.A = W.A
        self.verbose = verbose
        if 'SW02' not in self.A.mats:
            self.A.define('SW02', ('CX02', 'CX20', 'CX02'))
        self.pushes = {}
        self.cancels = {}
        self.sig = dict(SIG)

    def log(self, *a):
        if self.verbose:
            print(*a, flush=True)

    # ------------------------------------------------------------------ basic proofs
    def cancel(self, sw):
        if sw not in self.cancels:
            self.cancels[sw] = self.W.sem((sw, sw), ())
        return self.cancels[sw]

    def sigma(self, sw, u):
        return tuple(self.sig[sw][x] for x in u)

    def try_prove(self, u, v, groups=None):
        """u = v by a semantic step or in a tabled group; None if no engine applies."""
        W = self.W
        u, v = tuple(u), tuple(v)
        if u == v:
            return 'id'
        if W.pair_of(u + v) is not None:
            return W.sem(u, v)
        if len(u) == 2 and v == (u[1], u[0]) and not (W.sup(u[0]) & W.sup(u[1])):
            return struct_comm(W, u[0], u[1])
        for G in (groups if groups is not None else W.groups):
            e = W.prove_in(G, u, v)
            if e is not None:
                return e
        return None

    def push(self, sw, x):
        """SW x SW = sigma(x)."""
        k = (sw, x)
        if k in self.pushes:
            return self.pushes[k]
        W, T, A = self.W, self.T, self.A
        sx = self.sig[sw][x]
        u, v = (sw, x, sw), (sx,)
        e = None
        if W.pair_of(u + v) is not None:
            e = W.sem(u, v)
        elif not (W.sup(sw) & W.sup(x)):
            assert sx == x, (sw, x)
            c = struct_comm(W, sw, x)
            e = T.derived(u, v, [(0, c, True), (1, self.cancel(sw), True)])
        elif x in A.defs:
            d = T.eqs[A.defs[x]][1]
            D = Deriv(T, u)
            D.step(1, A.defs[x], True)
            for j in range(len(d) - 1, 0, -1):
                D.step(1 + j, self.cancel(sw), False)
            for j in range(len(d)):
                D.step(j, self.push(sw, d[j]), True)
            Dr = Deriv(T, v)
            A.unfold(D, 0, len(D.w))
            A.unfold(Dr, 0, 1)
            if D.w == Dr.w:
                e = T.derived(u, v, D.steps + invert(Dr.steps))
        if e is None:
            e = self.try_prove(u, v)
            assert e is not None and e != 'id', ('no push', sw, x)
        self.pushes[k] = e
        return e

    def to_conj(self, sw, word):
        """A derivation from word to SW sigma(word) SW."""
        T = self.T
        c = self.cancel(sw)
        D = Deriv(T, word)
        D.step(0, c, False)
        if not word:
            return D
        D.step(len(D.w), c, False)
        k = len(word)
        for j in range(k - 1, 0, -1):
            D.step(2 + j, c, False)
        for j in range(k):
            D.step(1 + j, self.push(sw, word[j]), True)
        assert D.w == (sw,) + self.sigma(sw, word) + (sw,)
        return D

    def relabel(self, sw, u, v, prove_fn):
        """u = v from a proof of sigma(u) = sigma(v)."""
        u, v = tuple(u), tuple(v)
        su, sv = self.sigma(sw, u), self.sigma(sw, v)
        es = prove_fn(su, sv)
        if es is None:
            return None
        Du, Dv = self.to_conj(sw, u), self.to_conj(sw, v)
        steps = Du.steps + ([] if es == 'id' else [(1, es, True)]) + invert(Dv.steps)
        return self.T.derived(u, v, steps)

    def prove(self, u, v, deep=True):
        """u = v: directly, or relabelled by one or two swaps."""
        u, v = tuple(u), tuple(v)
        e = self.try_prove(u, v)
        if e is not None:
            return None if e == 'id' else e
        if deep:
            for sw in ('SW01', 'SW12'):
                if all(x in self.sig[sw] for x in u + v):
                    e = self.relabel(sw, u, v, lambda a, b: self.try_prove(a, b))
                    if e is not None:
                        return e
            for s1, s2 in (('SW01', 'SW12'), ('SW12', 'SW01')):
                if all(x in self.sig[s1] for x in u + v):
                    e = self.relabel(s1, u, v, lambda a, b: self.relabel(
                        s2, a, b, lambda c, d: self.try_prove(c, d)))
                    if e is not None:
                        return e
        raise ValueError('no proof of %s = %s' % (' '.join(u), ' '.join(v)))

    def path(self, words):
        """words[0] = words[-1]: each step proves only the part where consecutive words differ."""
        T = self.T
        steps = []
        cur = tuple(words[0])
        for b in words[1:]:
            b = tuple(b)
            p = 0
            while p < len(cur) and p < len(b) and cur[p] == b[p]:
                p += 1
            s = 0
            while s < len(cur) - p and s < len(b) - p and cur[-1 - s] == b[-1 - s]:
                s += 1
            mc, mb = cur[p:len(cur) - s], b[p:len(b) - s]
            e = self.prove(mc, mb)
            if e is not None:
                steps.append((p, e, True))
            cur = b
        return T.derived(tuple(words[0]), cur, steps)

    def chain(self, words):
        """words[0] = words[-1] through the intermediate words, each step by `prove`."""
        steps = []
        for a, b in zip(words, words[1:]):
            e = self.prove(a, b)
            if e is not None:
                steps.append((0, e, True))
        return self.T.derived(tuple(words[0]), tuple(words[-1]), steps)

    # ------------------------------------------------------------------ groups
    def short_word(self, letters, m, maxlen=8):
        """A shortest word over `letters` with matrix m (BFS)."""
        mats = self.A.mats
        target = key(m)
        e = np.eye(8, dtype=complex)
        if key(e) == target:
            return ()
        seen = {key(e)}
        dq = deque([((), e)])
        while dq:
            wd, mm = dq.popleft()
            if len(wd) >= maxlen:
                continue
            for a in letters:
                p = mm @ mats[a]
                k = key(p)
                if k == target:
                    return wd + (a,)
                if k not in seen:
                    seen.add(k)
                    dq.append((wd + (a,), p))
        return None

    def conj_rels(self, new, old, G, extra=('CCZ',)):
        """Relators y x = w y for y in new, x in old, w a word over old (a short word over old
        and `extra`, rewritten into G's normal form if it uses `extra`)."""
        mats = self.A.mats
        rels = []
        for y in new:
            yi = np.linalg.inv(mats[y])
            for x in old:
                m = mats[y] @ mats[x] @ yi
                wd = self.short_word(list(old) + list(extra), m)
                assert wd is not None, (y, x)
                if set(wd) <= set(old):
                    rels.append(self.prove((y, x), wd + (y,)))
                else:
                    nf = word_of(G, m)
                    rels.append(self.path([(y, x), wd + (y,), nf + (y,)]))
        return rels

    def build_B1(self):
        W = self.W
        KB1 = W.KB1
        old = list(KB1.letters)
        rels = []
        for x in old:
            rels.append(self.prove(('C02', x), (x, 'C02')))
        e4 = self.prove(('C02',) * 4, ())
        rels.append(e4)
        self.W.add_inverse('C02', ('C02',) * 3, e4, e4)
        cz = word_of(KB1, self.A.mats['CZ02'])
        rels.append(self.chain([('C02', 'C02'), w('CX01 CZ12 CX01 CZ12'), cz]))
        G, ok = W.add_group('B1', old + ['C02'], Nested(KB1), rels)
        assert ok
        return G

    def build_L1(self):
        W = self.W
        from compact import compact
        B1 = W.B1
        old = list(B1.letters)
        new = ['X0', 'X2', 'CX20', 'CX02']
        for y in new:
            if y not in W.inv.inv:
                e = self.prove((y, y), ())
                W.add_inverse(y, (y,), e, e)
        rels = self.conj_rels(new, old, B1)
        R, o = compact(new, self.A.mats)
        self.log('  AGL relations', len(R), 'order', o)
        for u, v in R:
            rels.append(self.prove(u, v))
        G, ok = W.add_group('L1', old + new, Nested(B1), rels)
        assert ok
        return G


def main():
    import time
    t = time.time()
    W = load()
    P = PC(W)
    W.verbose = True
    P.build_B1()
    print('B1 %.1fs' % (time.time() - t), flush=True)
    P.build_L1()
    print('L1 %.1fs' % (time.time() - t), 'eqs', len(W.T.eqs), flush=True)
    with open('w3L.pkl', 'wb') as f:
        pickle.dump((W, P.pushes, P.cancels), f, protocol=pickle.HIGHEST_PROTOCOL)
    print('saved %.1fs' % (time.time() - t), flush=True)


if __name__ == '__main__':
    main()


# ---------------------------------------------------------------------- Phase C letters
def unfold_to(P, word, allowed):
    """A derivation unfolding the letters of `word` not in `allowed` (until all are)."""
    D = Deriv(P.T, word)
    i = 0
    while i < len(D.w):
        a = D.w[i]
        if a not in allowed and a in P.A.defs:
            D.step(i, P.A.defs[a], True)
        else:
            assert a in allowed, ('cannot unfold', a)
            i += 1
    return D


def prove_rel(P, sw, u, v, inner=None):
    """u = v by relabelling with sw after unfolding to letters sw acts on."""
    u, v = tuple(u), tuple(v)
    allowed = set(P.sig[sw])
    Du, Dv = unfold_to(P, u, allowed), unfold_to(P, v, allowed)
    if inner is None:
        inner = lambda a, b: P.try_prove(a, b)
    e = P.relabel(sw, Du.w, Dv.w, inner)
    if e is None:
        return None
    return P.T.derived(u, v, Du.steps + [(0, e, True)] + invert(Dv.steps))


def prove_any(P, u, v):
    """u = v directly, or in L0 (relabelled by SW01) or L2 (by SW12)."""
    u, v = tuple(u), tuple(v)
    if u == v:
        return None
    if (u, v) in P.T.index:
        return P.T.index[u, v]
    if (v, u) in P.T.index:
        return P.T.derived(u, v, [(0, P.T.index[v, u], False)])
    e = P.try_prove(u, v)
    if e is not None:
        return None if e == 'id' else e
    for sw in ('SW01', 'SW12'):
        e = prove_rel(P, sw, u, v)
        if e is not None:
            return e
    raise ValueError('no proof of %s = %s' % (' '.join(u), ' '.join(v)))


def define_phase_c(P):
    """The decodings of the macro letters (b2q1) on W's alphabet."""
    import b2q1
    W, A = P.W, P.A
    Z, Zi, K, tok = b2q1.matrices()
    for d, s in b2q1.TOK.items():
        A.define('T%d' % d, tuple(s.split()))
        assert eq(A.mats['T%d' % d], tok[d]), d
    A.define('T6J', ('CCX1', 'C02', 'CCZ'))
    assert eq(A.mats['T6J'], Z @ tok[6] @ Zi)
    ki = word_of(W.KB1, K @ Zi)
    A.define('KI', tuple(ki))
    A.define('KJ', ('KI', 'KI', 'C02'))
    assert eq(A.mats['KJ'], Z @ K)

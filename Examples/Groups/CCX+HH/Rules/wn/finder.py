#!/usr/bin/env python3
"""A derivation finder for the natural rules on N wires.

The letters are the placed gates on N wires: X t, CX c>t, CCX t;ab,
SW ab, HH ab.  The relators are the natural rules (`../classical3.py`,
the Toffoli-CNOT commutator and the HH rules of `../natural3.py`, the
four-wire rules of `../w4/check4.py`) at every adjacent placement, every
letter an involution, the commutations of disjoint adjacent letters, the
reversed CNOT as HH · CX · HH, and the other letters defined as swap
conjugates of adjacent ones; optionally R4 at every adjacent placement.

A target relator is traced by a partial proof-producing coset
enumeration over the affine group, as `../w4/g4partial.py` does on four
wires, but the labels are kept canonical by Gaussian elimination rather
than by a table of AGL(N, 2) (which has 3.2·10⁸ elements on five
wires).  A norm step between two affine words with one permutation is
an instance of affine completeness, which holds at every width
(`../../NaturalP/AffineComplete`).

    from finder import Alphabet
    A = Alphabet(5, r4=True)
    A.derive(A.word('...'), limit)
"""
import itertools
import sys
from collections import deque
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE.parent / 'w4'))
import labelled as LB
import proofs as PR
from classical3 import CLASSICAL_RULES
from natural3 import TOFFOLI_CNOT, HADAMARD_RULES
from check4 import FOUR

R4_TEXT = 'CCX0 HH03 CCX0 HH03 CCX0 HH03 CCX0 HH03 HH02 CXr1 HH02'


class Alphabet:
    def __init__(self, n, r4=False, extra=()):
        self.N = n
        self.D = 1 << n
        L = [('X', t) for t in range(n)]
        L += [('CX', c, t) for c in range(n) for t in range(n) if c != t]
        L += [('CCX', t, a, b) for t in range(n) for a in range(n) for b in range(a + 1, n)
              if t not in (a, b)]
        L += [('SW', a, b) for a in range(n) for b in range(a + 1, n)]
        L += [('HH', a, b) for a in range(n) for b in range(a + 1, n)]
        self.LETTERS = L
        self.NAMES = [self._name(l) for l in L]
        self.IX = {nm: k for k, nm in enumerate(self.NAMES)}
        self.INDEX = {l: k for k, l in enumerate(L)}
        self.WIRES = [set(l[1:]) for l in L]
        self.HH = {k for k, l in enumerate(L) if l[0] == 'HH'}
        self.PERMS = [None if l[0] == 'HH' else self._perm(l) for l in L]
        self.AFF = [k for k, l in enumerate(L) if l[0] in ('X', 'CX', 'SW')]
        self.rels = self._relators(r4) + [tuple(r) for r in extra]
        bad = [r for r in self.rels if not self.is_identity(r)]
        assert not bad, [' '.join(self.NAMES[g] for g in r) for r in bad[:3]]

    # -----------------------------------------------------------------
    @staticmethod
    def _name(l):
        if l[0] == 'X':
            return f'X{l[1]}'
        if l[0] == 'CX':
            return f'CX{l[1]}>{l[2]}'
        if l[0] == 'CCX':
            return f'CCX{l[1]};{l[2]}{l[3]}'
        return f'{l[0]}{l[1]}{l[2]}'

    def _perm(self, l):
        def f(x):
            k = l[0]
            if k == 'X':
                return x ^ (1 << l[1])
            if k == 'CX':
                return x ^ (1 << l[2]) if x >> l[1] & 1 else x
            if k == 'CCX':
                return x ^ (1 << l[1]) if x >> l[2] & 1 and x >> l[3] & 1 else x
            a, b = l[1], l[2]
            ba, bb = x >> a & 1, x >> b & 1
            return x ^ ((1 << a) | (1 << b)) if ba != bb else x
        return tuple(f(x) for x in range(self.D))

    def word(self, text):
        return tuple(self.IX[x] for x in text.split())

    def adj(self, name):
        """An adjacent-alphabet name (X0, CX0, CXr0, SW0, CCX0, HH0)."""
        base = name.rstrip('0123456789')
        i = int(name[len(base):])
        l = {'X': ('X', i), 'CX': ('CX', i + 1, i), 'CXr': ('CX', i, i + 1),
             'SW': ('SW', i, i + 1), 'CCX': ('CCX', i, i + 1, i + 2),
             'HH': ('HH', i, i + 1)}[base]
        if max(l[1:]) >= self.N:
            raise KeyError
        return self.INDEX[l]

    def _shift(self, names, s):
        out = []
        for x in names:
            if x.startswith('HH') and len(x) == 4:        # HH ab, two wires
                a, b = int(x[2]) + s, int(x[3]) + s
                if b >= self.N:
                    raise KeyError
                out.append(self.INDEX[('HH', a, b)])
                continue
            base = x.rstrip('0123456789')
            out.append(self.adj(f'{base}{int(x[len(base):]) + s}'))
        return tuple(out)

    def instances(self, text):
        if '=' in text:
            l, r = text.split('=')
            names = l.split() + list(reversed(r.split()))
        else:
            names = text.split()
        out = []
        for s in range(self.N):
            try:
                out.append(self._shift(names, s))
            except KeyError:
                break
        return out

    def _definitions(self):
        """Every non-adjacent letter as w · b · rev(w), b adjacent and w a
        word in the adjacent swaps: the shortest such."""
        n = self.N
        prim = set()
        for b, k in (('X', n), ('CX', n - 1), ('CXr', n - 1), ('SW', n - 1), ('CCX', n - 2), ('HH', n - 1)):
            for i in range(k):
                prim.add(self.adj(f'{b}{i}'))
        sws = [self.INDEX[('SW', i, i + 1)] for i in range(n - 1)]

        def relabel(g, pi):
            l = self.LETTERS[g]
            k = l[0]
            if k == 'X':
                return self.INDEX[('X', pi[l[1]])]
            if k == 'CX':
                return self.INDEX[('CX', pi[l[1]], pi[l[2]])]
            if k == 'CCX':
                a, b = sorted((pi[l[2]], pi[l[3]]))
                return self.INDEX[('CCX', pi[l[1]], a, b)]
            a, b = sorted((pi[l[1]], pi[l[2]]))
            return self.INDEX[(k, a, b)]

        out = {}
        # breadth first over swap words w; the letter w b rev(w) is b
        # relabelled by the wire permutation of w
        seen = {tuple(range(n)): ()}
        q = deque([tuple(range(n))])
        while q and len(out) < len(self.LETTERS) - len(prim):
            pi = q.popleft()
            w = seen[pi]
            for b in sorted(prim):
                g = relabel(b, pi)
                if g not in prim and g not in out:
                    out[g] = w + (b,) + tuple(reversed(w))
            for s in sws:
                a = self.LETTERS[s][1]
                # w' = s w: the relabelling first applies pi, then s
                pi2 = tuple(a + 1 if x == a else a if x == a + 1 else x for x in pi)
                if pi2 not in seen:
                    seen[pi2] = (s,) + w
                    q.append(pi2)
        assert len(out) == len(self.LETTERS) - len(prim), 'undefined letters'
        return prim, out

    def _relators(self, r4):
        rels = set()
        texts = CLASSICAL_RULES + [TOFFOLI_CNOT['commutator']] + FOUR + HADAMARD_RULES
        if r4:
            texts = texts + [R4_TEXT]
        for t in texts:
            rels |= set(self.instances(t))
        for i in range(self.N - 1):
            rels.add((self.adj(f'CXr{i}'), self.adj(f'HH{i}'), self.adj(f'CX{i}'), self.adj(f'HH{i}')))
        for g in range(len(self.LETTERS)):
            rels.add((g, g))
        prim, defs = self._definitions()
        prim = sorted(prim)
        for i, g in enumerate(prim):
            for h in prim[i + 1:]:
                if not self.WIRES[g] & self.WIRES[h]:
                    rels.add((g, h, g, h))
        for g, w in defs.items():
            rels.add((g,) + w)
        self.defs = defs
        return sorted(rels, key=lambda r: (len(r), r))

    # -----------------------------------------------------------------
    # exact semantics: columns (scale, entries), the scale a power of √2
    def act(self, g, col):
        s, w = col
        l = self.LETTERS[g]
        if l[0] == 'HH':
            for t in l[1:]:
                out = list(w)
                for x in range(self.D):
                    if not x >> t & 1:
                        y = x | 1 << t
                        out[x], out[y] = w[x] + w[y], w[x] - w[y]
                w = out
                s += 1
            while s >= 2 and all(v % 2 == 0 for v in w):
                s -= 2
                w = [v // 2 for v in w]
            return s, tuple(w)
        p = self.PERMS[g]
        out = [0] * self.D
        for x in range(self.D):
            out[p[x]] = w[x]
        return s, tuple(out)

    def matrix(self, word):
        cols = []
        for i in range(self.D):
            c = (0, tuple(1 if j == i else 0 for j in range(self.D)))
            for g in reversed(word):
                c = self.act(g, c)
            cols.append(c)
        return tuple(cols)

    def is_identity(self, word):
        return self.matrix(word) == self.matrix(())

    # -----------------------------------------------------------------
    # affine words: their permutation, and a canonical word for it
    def ev(self, word):
        p = tuple(range(self.D))
        for g in reversed(word):
            q = self.PERMS[g]
            p = tuple(q[x] for x in p)
        return p

    def canon(self, p):
        """A word of affine letters with permutation p (x ↦ A x ⊕ b), by
        reducing p to the identity with letters on the left."""
        n = self.N
        letters = []

        def left(g):
            nonlocal p
            q = self.PERMS[g]
            p = tuple(q[x] for x in p)
            letters.append(g)

        b = p[0]
        for t in range(n):
            if b >> t & 1:
                left(self.INDEX[('X', t)])
        for i in range(n):
            col = p[1 << i]
            if not col >> i & 1:
                r = next(r for r in range(i + 1, n) if col >> r & 1)
                left(self.INDEX[('SW', min(i, r), max(i, r))])
            col = p[1 << i]
            for j in range(n):
                if j != i and col >> j & 1:
                    left(self.INDEX[('CX', i, j)])
        assert p == tuple(range(self.D))
        # p0 = l1 ... lk, each letter an involution
        return tuple(letters)

    # -----------------------------------------------------------------
    def derive(self, target, limit, verbose=False):
        A = self
        cache = {}

        def nf(lab):
            p = A.ev(lab)
            if p not in cache:
                cache[p] = A.canon(p)
            return cache[p]

        class PTC(LB.LabelledTC):
            def join(tc, left, right):
                lab = tuple(left) + tuple(right)
                c = nf(lab)
                if c == lab:
                    return lab, []
                f = tc._add(tc.dec(lab), tc.dec(c), [(0, ('norm', (lab, c)), True)])
                return c, [(0, ('fact', f), True)]

        axioms = [PR.Axiom(f'r{j}', r, ()) for j, r in enumerate(self.rels)]
        macros = {g: (g,) for g in self.AFF}
        seeds = [tuple(target[:i]) for i in range(1, len(target) + 1)]
        tc = PTC(len(self.LETTERS), axioms, macros, seed=seeds, limit=limit)
        try:
            tc.run()
            closed = True
        except OverflowError:
            closed = False
        i, f, lab, st = tc.walk(0, tuple(target))
        ok = i == len(target) and tc.root(f) == 0 and lab == ()
        if verbose:
            print(f'  {"closed" if closed else "stopped"} at {len(tc.rep)} cosets; '
                  f'trace {i}/{len(target)} ends at {tc.root(f)}', flush=True)
        if not ok:
            return None
        top = tc._add(tuple(target), (), st)
        return tc, top

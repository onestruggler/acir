"""B1: the derivations over the macro alphabet (`Macro/Basic.lean`) for U_n, and their Lean
emission.

* the tokens' Coxeter relations are completed by Knuth–Bendix (the shortlex rewriting system
  of S_n), every rule derived from the axioms;
* the transport table: for every token t_d and generator g (by its indices),
  t_d enc(g) t_d = enc(t_d g), by S_n normal forms and the atom passing the tokens of its
  stabiliser;
* the families of relations are carried from standard instances by paths (`pathTo`) or are
  conjugations by palindromic paths (`okPal`), checked in Lean by `decide`.
"""
from collections import deque
from macro import Macro, macro_axioms
from table import Table, Deriv, invert
from kb import KB


def pos_path(M, p, q):
    """The palindromic path of the transposition (p q) in Gray positions."""
    i, j = sorted((M.gray.index(p), M.gray.index(q)))
    up = list(range(i, j))
    return up + list(reversed(up[:-1]))


def path_word(P):
    """pathW P = T d_m ... T d_1."""
    return [('t', d) for d in reversed(P)]


class B1:
    def __init__(self, M, std, verbose=False):
        self.M = M
        self.std = std
        n = M.n
        self.xp = {}
        for p in range(n):
            for q in range(n):
                if p != q:
                    self.xp[(p, q)] = pos_path(M, p, q)
        # the X encodings are the palindromic paths
        M.xwords = {pq: path_word(P) for pq, P in self.xp.items()}
        T = self.T = Table(lambda w: M.mmat(list(w)))
        self.ax = []
        self.axid = {}
        for nm, l, r in macro_axioms(M, std):
            e = T.axiom(l, r, nm)
            self.ax.append((nm, tuple(l), tuple(r)))
            self.axid[nm] = e
        toks = [('t', d) for d in range(M.nt)]
        self.kb = KB(T, toks)
        for nm, l, r in self.ax:
            if all(x in toks for x in l + r):
                self.kb.add_equation(self.axid[nm])
        assert self.kb.complete()
        self.allAG = [('i', p) for p in range(n)] + \
                     [('x', p, q) for p in range(n) for q in range(n) if p != q] + \
                     [('k', p, q) for p in range(n) for q in range(n) if p != q]
        self.adj = {}
        for d in range(M.nt):
            for g in self.allAG:
                self.adj[(d, g)] = self.adj_cert(d, g)
        if verbose:
            print(' B1 n=%d: kb rules %d, adj %d, eqs %d' % (n, len(self.kb.rules), len(self.adj), len(T.eqs)))

    # ---------------------------------------------------------------- encodings
    def enc(self, g):
        M = self.M
        if g[0] == 'i':
            return M.F(g[1])
        if g[0] == 'x':
            return list(M.xwords[(g[1], g[2])])
        return M.E(g[1], g[2])

    def act(self, d, g):
        p = self.M.tperm(d)
        return (g[0],) + tuple(p[x] for x in g[1:])

    def stab_word(self, perm, fixed):
        """A token word of `perm` (fixing the points `fixed`) in the tokens fixing them."""
        M = self.M
        toks = [d for d in range(M.nt) if all(M.tperm(d)[x] == x for x in fixed)]
        start = tuple(range(M.n))
        seen = {start: ()}
        dq = deque([start])
        while dq:
            p = dq.popleft()
            if p == perm:
                return [('t', d) for d in seen[p]]
            for d in toks:
                q = M.tperm(d)
                p2 = tuple(q[x] for x in p)
                if p2 not in seen:
                    seen[p2] = (d,) + seen[p]
                    dq.append(p2)
        raise ValueError('not in the stabiliser')

    def tok_eq(self, D, off, u, v):
        """Rewrite the token word u at offset off of D into the token word v (same permutation)."""
        nu, su = self.kb.reduce(u)
        nv, sv = self.kb.reduce(v)
        assert nu == nv
        D.steps_at(su, off)
        D.steps_at(invert(sv), off)

    def adj_cert(self, d, g):
        M, T = self.M, self.T
        t = ('t', d)
        u = [t] + self.enc(g) + [t]
        g2 = self.act(d, g)
        v = self.enc(g2)
        D = Deriv(T, u)
        if g[0] == 'x':
            self.tok_eq(D, 0, u, v)
            return T.derived(u, v, D.steps)
        if g[0] == 'i':
            f, f2, A, fixed = M.vF(g[1]), M.vF(g2[1]), 'Z', [M.z]
        else:
            f, f2, A, fixed = M.vE(g[1], g[2]), M.vE(g2[1], g2[2]), 'K', [M.a, M.z]
        Aw = [t] + f
        pa = M.perm_of(Aw)
        p2 = M.perm_of(f2)
        inv2 = [0] * M.n
        for x in range(M.n):
            inv2[p2[x]] = x
        s = tuple(inv2[pa[x]] for x in range(M.n))
        sw = self.stab_word(s, fixed)
        # prefix t f -> f2 sw
        self.tok_eq(D, 0, Aw, f2 + sw)
        k = len(f2) + len(sw)
        assert D.w[k] == A
        # suffix f^R t -> sw^R f2^R
        self.tok_eq(D, k + 1, list(reversed(Aw)), list(reversed(sw)) + list(reversed(f2)))
        # commute A left through sw
        nm = 'Zc' if A == 'Z' else 'Kc'
        for i in range(len(sw) - 1, -1, -1):
            pos = len(f2) + i
            tok = D.w[pos]
            assert D.w[pos + 1] == A
            D.step(pos, self.axid['%s%d' % (nm, tok[1])], False)
        # cancel sw sw^R
        c = len(f2) + 1 + len(sw)
        for i in range(len(sw)):
            pos = c - 1 - i
            tok = D.w[pos]
            assert D.w[pos + 1] == tok
            D.step(pos, self.axid['sq%d' % tok[1]], True)
        assert D.w == tuple(v), (D.w, v)
        return T.derived(u, v, D.steps)

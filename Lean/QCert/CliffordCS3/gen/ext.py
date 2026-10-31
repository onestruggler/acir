"""Extended alphabets: letters that abbreviate words of the base alphabet.

`Alpha` holds the base letters with their matrices and the defined letters with their
expansions; the proof table works over all letters (matrices through the expansions) and a
defined letter's definition is the axiom ('def', name) `x = expansion`, which disappears when
equations are expanded to the base alphabet (`expand_eq`, `expand_steps`)."""
import numpy as np
from table import Table, Deriv


class Alpha:
    def __init__(self, base_mats):
        self.base = list(base_mats)
        self.mats = dict(base_mats)
        self.exp = {a: (a,) for a in self.base}
        self.n = next(iter(base_mats.values())).shape[0]
        self.T = Table(self.matw)
        self.defs = {}

    def matw(self, w):
        r = np.eye(self.n, dtype=complex)
        for a in w:
            r = r @ self.mats[a]
        return r

    def expand(self, w):
        out = []
        for a in w:
            out += self.exp[a]
        return tuple(out)

    def define(self, name, word):
        word = tuple(word)
        assert name not in self.mats
        self.exp[name] = self.expand(word)
        self.mats[name] = self.matw(word)
        self.defs[name] = self.T._add((name,), word, ('def', name), 'def_' + name)
        return self.defs[name]

    def unfold(self, D, start, end):
        """Rewrite the segment D.w[start:end] into base letters; returns its new end."""
        i = start
        while i < end:
            a = D.w[i]
            if a in self.defs:
                l, r, _ = self.T.eqs[self.defs[a]]
                D.step(i, self.defs[a], True)
                end += len(r) - 1
            else:
                i += 1
        return end

    def expand_steps(self, w, steps):
        """The steps of a derivation over the extended alphabet, on the expanded words
        (definition steps dropped)."""
        T = self.T
        out = []
        w = tuple(w)
        for (p, k, d) in steps:
            if T.eqs[k][2][0] != 'def':
                out.append((len(self.expand(w[:p])), k, d))
            w = T.apply(w, (p, k, d))
        return out

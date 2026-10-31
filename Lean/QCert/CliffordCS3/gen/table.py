"""A proof table: equations between words (tuples of letter names), each an axiom, a
semantic step, or derived from earlier equations by rewriting steps (pos, eq_id, d): at
position pos replace the left side of equation eq_id by its right side (d = True) or the
right side by the left side (d = False).  Every equation is checked on matrices when added.
"""
import numpy as np
from qc import eq


class Table:
    def __init__(self, matfn):
        self.matfn = matfn
        self.eqs = []          # (lhs, rhs, just)
        self.byname = {}
        self.index = {}        # (lhs, rhs) -> id

    def _add(self, lhs, rhs, just, name):
        lhs, rhs = tuple(lhs), tuple(rhs)
        k = (lhs, rhs)
        if k in self.index and name is None:
            return self.index[k]
        assert eq(self.matfn(lhs), self.matfn(rhs)), ('unsound', name, lhs, rhs)
        self.eqs.append((lhs, rhs, just))
        i = len(self.eqs) - 1
        self.index.setdefault(k, i)
        if name is not None:
            self.byname[name] = i
        return i

    def axiom(self, lhs, rhs, name):
        return self._add(lhs, rhs, ('ax', name), name)

    def sem(self, lhs, rhs, tag, name=None):
        return self._add(lhs, rhs, ('sem', tag), name)

    def apply(self, w, step):
        p, k, d = step
        l, r, _ = self.eqs[k]
        a, b = (l, r) if d else (r, l)
        assert w[p:p + len(a)] == a, ('bad step', step, w, a)
        return w[:p] + b + w[p + len(a):]

    def replay(self, w, steps):
        w = tuple(w)
        for s in steps:
            w = self.apply(w, s)
        return w

    def derived(self, lhs, rhs, steps, name=None):
        lhs, rhs = tuple(lhs), tuple(rhs)
        end = self.replay(lhs, steps)
        assert end == rhs, ('bad derivation', name, end, rhs)
        if len(steps) == 1:
            p, k, d = steps[0]
            l, r, _ = self.eqs[k]
            if p == 0 and len(lhs) == len(l if d else r):
                # the equation itself (or its reverse)
                if d and name is None:
                    return k
        return self._add(lhs, rhs, ('der', list(steps)), name)

    def size(self, i):
        j = self.eqs[i][2]
        return len(j[1]) if j[0] == 'der' else 0


def invert(steps):
    return [(p, k, not d) for (p, k, d) in reversed(steps)]


def shift(steps, off):
    return [(p + off, k, d) for (p, k, d) in steps]


class Deriv:
    """A word being rewritten, recording the steps."""

    def __init__(self, T, w):
        self.T = T
        self.w = tuple(w)
        self.steps = []

    def step(self, p, k, d=True):
        self.w = self.T.apply(self.w, (p, k, d))
        self.steps.append((p, k, d))

    def steps_at(self, steps, off):
        for (p, k, d) in steps:
            self.step(p + off, k, d)

    def rsteps_at(self, steps, off):
        """Apply the inverse of `steps` (recorded on a word starting at offset `off`)."""
        for (p, k, d) in reversed(steps):
            self.step(p + off, k, not d)

    def eq(self, name=None):
        return None

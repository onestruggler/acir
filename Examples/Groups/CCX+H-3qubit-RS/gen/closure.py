"""Rewrite rules from relators: every rotation and split of l rev(r)."""
from search import Lib


def rev(w):
    return tuple(reversed(w))


class RLib(Lib):
    """A library whose moves are the rotations of its lemmas' relators.

    rules: (p, q) -> (name, k, m) with p = take m (rot k R), q = rev (drop m (rot k R)),
    R = lhs ++ rev rhs of the lemma `name`.
    """

    def __init__(self, invols):
        super().__init__()
        self.invols = set(invols)
        self.rules = {}

    def add(self, name, lhs, rhs, check=True, rotate=True, slack=2):
        super().add(name, lhs, rhs, check)
        if rotate:
            self.add_rotations(name, slack)

    def add_rotations(self, name, slack=2):
        lhs, rhs = self.lemmas[name]
        R = lhs + rev(rhs)
        if not set(R) <= self.invols:
            return
        n = len(R)
        for k in range(n):
            Rk = R[k:] + R[:k]
            for m in range(1, n + 1):
                p, q = Rk[:m], rev(Rk[m:])
                if len(q) > len(p) + slack:
                    continue
                if (p, q) in self.rules or p == q:
                    continue
                self.rules[(p, q)] = (name, k, m)
                self.by_first.setdefault(p[0], []).append((('rot', name, k, m), 1, p, q))

    def describe(self, step):
        return step


def apply_step(lib, w, step):
    i, name, o = step
    if isinstance(name, tuple):
        p, q = next((pq for pq, v in lib.rules.items() if ('rot',) + v == name), (None, None))
        if p is None:
            raise KeyError(name)
    else:
        l, r = lib.lemmas[name]
        p, q = (l, r) if o == 1 else (r, l)
    if o == -1 and isinstance(name, tuple):
        p, q = q, p
    assert w[i:i + len(p)] == p, (w, i, name, o)
    return w[:i] + q + w[i + len(p):]


def replay(lib, u, steps):
    w = tuple(u)
    for st in steps:
        w = apply_step(lib, w, st)
    return w

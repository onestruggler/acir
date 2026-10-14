#!/usr/bin/env python3
"""Coset enumeration that proves its own table.

Every generator is an involution.  Cosets of the trivial subgroup are
numbered as they are defined; coset c has a representative word rep[c]
(the letters along which it was defined), which never changes.  Every
table entry c·y = d comes with a *fact*, a derivation of

    rep[c] ++ [y]  ⟶  rep[d]

as a list of rewrite steps on letter lists.  A step (pos, eq, fwd)
replaces the occurrence of one side of an equation at position pos by
the other (lhs by rhs when fwd).  The equations are the axioms, the
involutions y y = ε, and earlier facts; a coincidence is a fact
rep[b] ⟶ rep[a].  This is exactly what Natural/Engine.agda's `derive`
checks (with sym⁼ for the backward steps), so the facts can be emitted
as Agda.  `replay` checks every fact here first.

The strategy is HLT, as in core.py.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass
class Fact:
    lhs: tuple
    rhs: tuple
    steps: list          # (pos, (kind, key), fwd); kind in ax, inv, fact


@dataclass
class Axiom:
    name: str            # the Agda Eqn
    lhs: tuple
    rhs: tuple


class ProofTC:
    def __init__(self, ngens: int, axioms: list, limit=200_000):
        self.ngens = ngens
        self.axioms = axioms
        self.facts: list = []
        self.rep: list = []
        self.table: list = []        # entries (d, fact) or None; d may be dead
        self.parent: list = []       # (a, fact rep[b] -> rep[a]) or None
        self.limit = limit
        self.relators = []
        for k, ax in enumerate(axioms):
            rel = tuple(ax.lhs) + tuple(reversed(ax.rhs))
            steps = [(0, ("ax", k), True)]
            r = list(ax.rhs)
            for j in range(len(r) - 1, -1, -1):
                steps.append((j, ("inv", r[j]), True))   # r ++ rev r -> ε, middle out
            self.relators.append((rel, self._add(rel, (), steps)))

    def _add(self, lhs, rhs, steps):
        self.facts.append(Fact(tuple(lhs), tuple(rhs), steps))
        return len(self.facts) - 1

    # ---------------------------------------------------------------
    def _new(self, c, y):
        if len(self.rep) >= self.limit:
            raise OverflowError
        d = len(self.rep)
        self.rep.append(self.rep[c] + (y,))
        self.table.append([None] * self.ngens)
        self.parent.append(None)
        fwd = self._add(self.rep[c] + (y,), self.rep[d], [])
        back = self._add(self.rep[d] + (y,), self.rep[c], [(len(self.rep[c]), ("inv", y), True)])
        self.table[c][y] = (d, fwd)
        self.table[d][y] = (c, back)

    def find(self, c):
        """(root, steps rewriting a prefix rep[c] into rep[root])."""
        steps = []
        while self.parent[c] is not None:
            a, f = self.parent[c]
            steps.append((0, ("fact", f), True))
            c = a
        return c, steps

    def entry(self, c, y):
        e = self.table[c][y]
        if e is None:
            return None
        d, f = e
        root, more = self.find(d)
        return root, [(0, ("fact", f), True)] + more

    def path(self, c, word):
        """Follow word from c: (letters followed, coset, steps rewriting a
        prefix rep[c] ++ word[:i] into rep[coset])."""
        steps, cur = [], c
        for i, y in enumerate(word):
            e = self.entry(cur, y)
            if e is None:
                return i, cur, steps
            cur, s = e
            steps = steps + s
        return len(word), cur, steps

    @staticmethod
    def reverse(steps):
        return [(pos, key, not fwd) for (pos, key, fwd) in reversed(steps)]

    # ---------------------------------------------------------------
    def relator_proof(self, e, rel, relfact, i, j):
        """Steps rewriting rep[f] ++ rel[i:j] into rep[b], where f = e·rel[:i]
        (forward) and b is reached from e along rev(rel[j:])."""
        _, _, fwd = self.path(e, rel[:i])
        steps = self.reverse(fwd)                     # rep[f] -> rep[e] rel[:i]
        base = len(self.rep[e])
        pos = base + j
        for y in rel[j:]:
            steps.append((pos, ("inv", y), False))     # insert y y
            pos += 1
        steps.append((base, ("fact", relfact), True))  # rel -> ε
        _, _, back = self.path(e, tuple(reversed(rel[j:])))
        return steps + back

    def merge(self, a, b, f):
        """Coincidence of a and b, given a fact f: rep[b] -> rep[a]."""
        queue = [(a, b, f)]
        while queue:
            a, b, f = queue.pop()
            ra, sa = self.find(a)
            rb, sb = self.find(b)
            if ra == rb:
                continue
            steps = self.reverse(sb) + [(0, ("fact", f), True)] + sa   # rep[rb] -> rep[ra]
            if ra > rb:
                ra, rb = rb, ra
                steps = self.reverse(steps)                             # rep[rb] -> rep[ra]
            link = self._add(self.rep[rb], self.rep[ra], steps)
            self.parent[rb] = (ra, link)
            for y in range(self.ngens):
                e = self.table[rb][y]
                if e is None:
                    continue
                self.table[rb][y] = None
                d, fd = e
                f1 = self._add(self.rep[ra] + (y,), self.rep[d],
                               [(0, ("fact", link), False), (0, ("fact", fd), True)])
                cur = self.table[ra][y]
                if cur is None:
                    self.table[ra][y] = (d, f1)
                else:
                    d2, f2 = cur
                    queue.append((d2, d, self._add(self.rep[d], self.rep[d2],
                                  [(0, ("fact", f1), False), (0, ("fact", f2), True)])))

    def scan(self, e, rel, relfact):
        n = len(rel)
        while True:
            e, _ = self.find(e)
            i, f, _ = self.path(e, rel)
            if i == n:
                if f != e:
                    self.merge(e, f, self._add(self.rep[f], self.rep[e],
                                               self.relator_proof(e, rel, relfact, n, n)))
                return
            j, b = n, e
            while j > i:
                ent = self.entry(b, rel[j - 1])
                if ent is None:
                    break
                b, j = ent[0], j - 1
            if j == i:
                if f != b:
                    self.merge(b, f, self._add(self.rep[f], self.rep[b],
                                               self.relator_proof(e, rel, relfact, i, i)))
                return
            if j == i + 1:
                y = rel[i]
                fact = self._add(self.rep[f] + (y,), self.rep[b],
                                 self.relator_proof(e, rel, relfact, i, i + 1))
                back = self._add(self.rep[b] + (y,), self.rep[f],
                                 [(0, ("fact", fact), False), (len(self.rep[f]), ("inv", y), True)])
                if self.table[f][y] is None:
                    self.table[f][y] = (b, fact)
                if self.table[b][y] is None:
                    self.table[b][y] = (f, back)
                else:
                    d2, f2 = self.table[b][y]
                    self.merge(d2, f, self._add(self.rep[f], self.rep[d2],
                                                [(0, ("fact", back), False), (0, ("fact", f2), True)]))
                return
            self._new(f, rel[i])

    def run(self):
        self.rep.append(())
        self.table.append([None] * self.ngens)
        self.parent.append(None)
        c = 0
        while c < len(self.rep):
            if self.parent[c] is None:
                for rel, rf in self.relators:
                    self.scan(c, rel, rf)
                    if self.parent[c] is not None:
                        break
                if self.parent[c] is None:
                    for y in range(self.ngens):
                        if self.table[c][y] is None:
                            self._new(c, y)
            c += 1
        return [c for c in range(len(self.rep)) if self.parent[c] is None]

    # ---------------------------------------------------------------
    def final(self, c, y):
        """For live c: (live d, fact id of rep[c] ++ [y] -> rep[d])."""
        d, steps = self.entry(c, y)
        return d, self._add(self.rep[c] + (y,), self.rep[d], steps)


# -------------------------------------------------------------------
# Independent replay of every fact, as Natural/Engine.agda will run it

def equation(tc: ProofTC, key):
    kind, k = key
    if kind == "ax":
        return tc.axioms[k].lhs, tc.axioms[k].rhs
    if kind == "inv":
        return (k, k), ()
    return tc.facts[k].lhs, tc.facts[k].rhs


def replay(tc: ProofTC, fact: Fact) -> bool:
    xs = list(fact.lhs)
    for pos, key, fwd in fact.steps:
        l, r = equation(tc, key)
        if not fwd:
            l, r = r, l
        if tuple(xs[pos:pos + len(l)]) != tuple(l):
            return False
        xs = xs[:pos] + list(r) + xs[pos + len(l):]
    return tuple(xs) == tuple(fact.rhs)

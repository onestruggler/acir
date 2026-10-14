#!/usr/bin/env python3
"""Exact semantics and coset enumeration for searching circuit relations.

Gates of the CCX+HH gate set (X, CX, CCX, HH = H tensor H) act on
2^n basis levels, wire 0 the least significant bit.  Their matrices
have entries in Z[1/2]; a group element at a small width is represented
by the permutation it induces on a finite invariant set of vectors (the
orbit of 4 e_i), which is faithful because the orbit spans the space.

Every generator is an involution, so the coset enumerator below works
with self-inverse generators only: a relator is a word, and a coset
table column is its own inverse.

This is a research tool.  It decides completeness of a candidate rule
set at a fixed small width by coset enumeration; it is not a proof.
"""

from __future__ import annotations

from itertools import combinations
from pathlib import Path


# ---------------------------------------------------------------------
# Gates as vector maps

def flip(v, target, controls=()):
    out = list(v)
    for i, entry in enumerate(v):
        if all(i >> c & 1 for c in controls):
            out[i ^ (1 << target)] = entry
    return tuple(out)


def hh(v, a, b):
    """H tensor H on wires a and b, the other wires spectators."""
    n = len(v).bit_length() - 1
    mask = (1 << a) | (1 << b)
    out = list(v)
    for base in range(len(v)):
        if base & mask:
            continue
        idx = [base | ((r & 1) << a) | ((r >> 1) << b) for r in range(4)]
        for r, i in enumerate(idx):
            num = sum((-1) ** ((r & c).bit_count()) * v[j] for c, j in enumerate(idx))
            if num % 2:
                raise ValueError("non-integral image: enlarge the scale")
            out[i] = num // 2
    return tuple(out)


class GateSet:
    """Adjacent gates of a width: names and vector actions.

    `X i` on wire i, `CX i` target i control i+1, `CCX i` target i
    controls i+1 and i+2, `HH i` on wires i and i+1, as in the
    repository's Circuit.Base placements.
    """

    def __init__(self, n: int):
        self.n = n
        self.names: list[str] = []
        self.actions = []
        self.wires: list[tuple[int, ...]] = []
        for i in range(n):
            self._add(f"X{i}", (i,), lambda v, i=i: flip(v, i))
        for i in range(n - 1):
            self._add(f"CX{i}", (i, i + 1), lambda v, i=i: flip(v, i, (i + 1,)))
        for i in range(n - 2):
            self._add(f"CCX{i}", (i, i + 1, i + 2),
                      lambda v, i=i: flip(v, i, (i + 1, i + 2)))
        for i in range(n - 1):
            self._add(f"HH{i}", (i, i + 1), lambda v, i=i: hh(v, i, i + 1))
        self.index = {name: k for k, name in enumerate(self.names)}

    def _add(self, name, wires, action):
        self.names.append(name)
        self.wires.append(wires)
        self.actions.append(action)

    def word(self, text: str) -> tuple[int, ...]:
        return tuple(self.index[t] for t in text.split())

    def show(self, word) -> str:
        return " ".join(self.names[g] for g in word) if word else "ε"


class PermRep:
    """The gates of a GateSet as permutations of an invariant orbit."""

    def __init__(self, gs: GateSet, scale: int = 4):
        self.gs = gs
        dim = 1 << gs.n
        start = [tuple(scale if j == i else 0 for j in range(dim)) for i in range(dim)]
        index = {v: k for k, v in enumerate(start)}
        points = list(start)
        frontier = list(start)
        while frontier:
            new = []
            for v in frontier:
                for act in gs.actions:
                    w = act(v)
                    if w not in index:
                        index[w] = len(points)
                        points.append(w)
                        new.append(w)
            frontier = new
        self.points = points
        self.index = index
        self.gens = [tuple(index[act(v)] for v in points) for act in gs.actions]
        self.identity = tuple(range(len(points)))

    def evaluate(self, word) -> tuple[int, ...]:
        # A word denotes the product in written order: the matrix of
        # w = g1 g2 ... gk is G1 G2 ... Gk, so gk acts first.
        p = self.identity
        for g in reversed(word):
            gp = self.gens[g]
            p = tuple(gp[x] for x in p)
        return p

    def is_identity(self, word) -> bool:
        return self.evaluate(word) == self.identity


# ---------------------------------------------------------------------
# Coset enumeration with self-inverse generators (HLT + coincidences)

class Enumeration:
    def __init__(self, ngens, relators, subgroup, limit=2_000_000):
        self.ngens = ngens
        self.relators = [tuple(r) for r in relators if r]
        self.subgroup = [tuple(w) for w in subgroup if w]
        self.limit = limit
        self.table: list[list[int]] = []
        self.parent: list[int] = []
        self.alive = 0

    def _new(self) -> int:
        if len(self.table) >= self.limit:
            raise OverflowError
        c = len(self.table)
        self.table.append([-1] * self.ngens)
        self.parent.append(c)
        self.alive += 1
        return c

    def _find(self, c):
        while self.parent[c] != c:
            self.parent[c] = self.parent[self.parent[c]]
            c = self.parent[c]
        return c

    def _set(self, c, g, d):
        self.table[c][g] = d
        self.table[d][g] = c

    def _coincidence(self, a, b):
        queue = [(a, b)]
        while queue:
            a, b = queue.pop()
            a, b = self._find(a), self._find(b)
            if a == b:
                continue
            if a > b:
                a, b = b, a
            self.parent[b] = a
            self.alive -= 1
            row = self.table[b]
            for g in range(self.ngens):
                d = row[g]
                if d < 0:
                    continue
                row[g] = -1
                d = self._find(d)
                if self.table[d][g] == b:
                    self.table[d][g] = -1
                e = self.table[a][g]
                if e >= 0:
                    queue.append((self._find(e), d))
                else:
                    da = self.table[d][g]
                    if da >= 0 and self._find(da) != a:
                        queue.append((self._find(da), a))
                        continue
                    self._set(a, g, d)

    def _scan_fill(self, c, word):
        # Trace word from c forwards and backwards, defining cosets to
        # close the gap; deduce or record a coincidence when it closes.
        n = len(word)
        while True:
            c = self._find(c)
            f, i = c, 0
            while i < n and self.table[f][word[i]] >= 0:
                f = self._find(self.table[f][word[i]])
                i += 1
            if i == n:
                if f != c:
                    self._coincidence(f, c)
                return
            b, j = c, n - 1
            while j >= i and self.table[b][word[j]] >= 0:
                b = self._find(self.table[b][word[j]])
                j -= 1
            if j < i:
                self._coincidence(f, b)
                return
            if j == i:
                self._set(f, word[i], b)
                return
            d = self._new()
            self._set(f, word[i], d)

    def run(self) -> int:
        start = self._new()
        for w in self.subgroup:
            self._scan_fill(start, w)
        c = 0
        while c < len(self.table):
            if self._find(c) == c:
                for r in self.relators:
                    self._scan_fill(c, r)
                    if self._find(c) != c:
                        break
                if self._find(c) == c:
                    for g in range(self.ngens):
                        if self.table[c][g] < 0:
                            d = self._new()
                            self._set(c, g, d)
            c += 1
        return self.alive


def index(ngens, relators, subgroup=(), limit=2_000_000):
    """Index of the subgroup in the presented group, or None past the limit."""
    try:
        return Enumeration(ngens, relators, subgroup, limit).run()
    except OverflowError:
        return None


# ---------------------------------------------------------------------
# Structural rules of Circuit.Base at a fixed width

def structural(gs: GateSet):
    """Involutions and commutation of gates on disjoint wires."""
    rels = [(g, g) for g in range(len(gs.names))]
    for a, b in combinations(range(len(gs.names)), 2):
        if not set(gs.wires[a]) & set(gs.wires[b]):
            rels.append((a, b, a, b))
    return rels


def placements(gs: GateSet, rule: str):
    """Every placement of a rule stated on the bottom wires (cong↑)."""
    toks = [split_name(t) for t in rule.split()]
    span = max(i + arity(base) for base, i in toks)
    return [tuple(gs.index[f"{base}{i + s}"] for base, i in toks)
            for s in range(gs.n - span + 1)]


def shifts(gs: GateSet, rules: list[str]):
    """Every placement of every rule."""
    return [w for r in rules for w in placements(gs, r)]


def split_name(token: str):
    k = len(token)
    while k > 0 and token[k - 1].isdigit():
        k -= 1
    return token[:k], int(token[k:])


def arity(base: str) -> int:
    return {"X": 1, "CX": 2, "CCX": 3, "HH": 2}[base]


# ---------------------------------------------------------------------
# The same enumeration in C (tc.c), for millions of cosets

def index_c(ngens, relators, subgroup=(), limit=20_000_000):
    """Index via the compiled `tc`, or None past the limit."""
    import subprocess
    exe = Path(__file__).resolve().parent / "tc"
    lines = [f"{ngens} {limit}", str(len(relators))]
    lines += [" ".join(map(str, (len(r),) + tuple(r))) for r in relators]
    lines += [str(len(subgroup))]
    lines += [" ".join(map(str, (len(w),) + tuple(w))) for w in subgroup]
    out = subprocess.run([str(exe)], input="\n".join(lines) + "\n",
                         capture_output=True, text=True, check=True).stdout.strip()
    return None if out == "overflow" else int(out)

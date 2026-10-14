#!/usr/bin/env python3
"""The CCX+H gate set (X, CX, CCX and the single Hadamard H), exactly.

Entries are in Z[1/√2]; a number a + b√2 is a pair of Fractions.  As in
core.py, a group element at a small width is the permutation it induces
on the orbit of the basis vectors, which is finite on one and two wires
(on three the group is infinite).  Gate names: `X i`, `CX i` (target i,
control i+1), `CCX i`, `H i`.
"""

from __future__ import annotations

from fractions import Fraction

import core as C


def _add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def _sub(x, y):
    return (x[0] - y[0], x[1] - y[1])


def _over_root2(x):
    # (a + b√2) / √2 = b + (a / 2)√2
    return (x[1], x[0] / 2)


def hadamard(v, wire):
    out = list(v)
    for i in range(len(v)):
        if i >> wire & 1:
            continue
        j = i | (1 << wire)
        out[i] = _over_root2(_add(v[i], v[j]))
        out[j] = _over_root2(_sub(v[i], v[j]))
    return tuple(out)


class GateSetH:
    def __init__(self, n: int):
        self.n = n
        self.names, self.actions, self.wires = [], [], []
        for i in range(n):
            self._add(f"X{i}", (i,), lambda v, i=i: C.flip(v, i))
        for i in range(n - 1):
            self._add(f"CX{i}", (i, i + 1), lambda v, i=i: C.flip(v, i, (i + 1,)))
        for i in range(n - 2):
            self._add(f"CCX{i}", (i, i + 1, i + 2), lambda v, i=i: C.flip(v, i, (i + 1, i + 2)))
        for i in range(n):
            self._add(f"H{i}", (i,), lambda v, i=i: hadamard(v, i))
        self.index = {name: k for k, name in enumerate(self.names)}

    def _add(self, name, wires, action):
        self.names.append(name)
        self.wires.append(wires)
        self.actions.append(action)

    def word(self, text):
        return tuple(self.index[t] for t in text.split())

    def show(self, word):
        return " ".join(self.names[g] for g in word) if word else "ε"


class PermRepH(C.PermRep):
    def __init__(self, gs: GateSetH):
        self.gs = gs
        dim = 1 << gs.n
        one, zero = (Fraction(1), Fraction(0)), (Fraction(0), Fraction(0))
        start = [tuple(one if j == i else zero for j in range(dim)) for i in range(dim)]
        index = {v: k for k, v in enumerate(start)}
        points, frontier = list(start), list(start)
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
            if len(points) > 200000:
                raise OverflowError("orbit too large: the group is probably infinite")
        self.points, self.index = points, index
        self.gens = [tuple(index[act(v)] for v in points) for act in gs.actions]
        self.identity = tuple(range(len(points)))

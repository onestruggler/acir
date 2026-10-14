#!/usr/bin/env python3
"""Sanity checks for core.py: known group orders by coset enumeration."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import core as C


def coxeter_sym(k):
    """S_{k+1} on k involutive generators: its order is (k+1)!."""
    rels = []
    for i in range(k):
        for j in range(i + 1, k):
            rels.append((i, j) * (3 if j == i + 1 else 2))
    return rels


def schreier_relators(rep: C.PermRep):
    """A complete presentation: one relator per Cayley-graph edge."""
    word = {rep.identity: ()}
    frontier = [rep.identity]
    while frontier:
        new = []
        for p in frontier:
            for g in range(len(rep.gens)):
                q = tuple(rep.gens[g][x] for x in p)  # g applied after p
                if q not in word:
                    word[q] = (g,) + word[p]
                    new.append(q)
        frontier = new
    rels = []
    for p, w in word.items():
        for g in range(len(rep.gens)):
            q = tuple(rep.gens[g][x] for x in p)
            rels.append((g,) + w + tuple(reversed(word[q])))
    return len(word), rels


def main():
    import math
    for k in (2, 3, 5, 7):
        got = C.index(k, coxeter_sym(k))
        assert got == math.factorial(k + 1), (k, got)
    for n, order in ((1, 2), (2, 384)):
        gs = C.GateSet(n)
        rep = C.PermRep(gs)
        size, rels = schreier_relators(rep)
        assert size == order, (n, size)
        assert all(rep.is_identity(r) for r in rels)
        got = C.index(len(gs.names), rels)
        assert got == order, (n, got)
        print(f"width {n}: group order {size}, {len(rep.points)} orbit points")
    print("core self-test passed")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Derive a classical relator on four wires from the tower's level-0
relators, locally.

For a relator δ, find a small alphabet A containing δ's letters whose
relators (those of tower4.relators_tower() with every letter in A)
present the group A generates: coset enumeration over the trivial
subgroup closes at that group's order.  Then a proof-producing
enumeration (`../labelled.py`) of that group traces δ from the identity
coset, which is a derivation of δ ⟶ ε from level-0 relators.

    python3 -B local4.py 'CCX0;23 CCX1;23 CCX0;23 CCX1;23'
"""
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))
import core as C
import labelled as LB
import proofs as PR
import ss
import tower4 as T

MAXORDER = 60_000
BASE = None


def base():
    global BASE
    if BASE is None:
        BASE = T.relators_tower()
    return BASE


def order(lets):
    return ss.order([T.PERMS[g] for g in lets]) if lets else 1


def presented(lets):
    """Do the relators among lets present the group they generate?"""
    n = order(lets)
    if n > MAXORDER:
        return False
    pos = {g: i for i, g in enumerate(lets)}
    own = [tuple(pos[g] for g in r) for r in base() if all(g in pos for g in r)]
    return C.index_c(len(lets), own, [], max(20_000, 20 * n)) == n


def gain(A, g):
    """How many relators adding g to A brings in."""
    S = set(A) | {g}
    return sum(1 for r in base() if g in r and all(x in S for x in r))


def alphabet(delta, steps=8):
    """A small presented alphabet containing δ's letters, or None: add
    letters one at a time, each the one bringing in the most relators
    (among those keeping the group small), with a short beam."""
    start = sorted(set(delta))
    beam = [start]
    seen = {tuple(start)}
    for _ in range(steps + 1):
        for A in beam:
            if presented(A):
                return A
        nxt = []
        for A in beam:
            scored = []
            for g in range(len(T.LETTERS)):
                if g in A:
                    continue
                B = sorted(A + [g])
                if tuple(B) in seen:
                    continue
                k = gain(A, g)
                if k == 0 or order(B) > MAXORDER:
                    continue
                scored.append((-k, order(B), B))
            scored.sort()
            for _, _, B in scored[:3]:
                seen.add(tuple(B))
                nxt.append(B)
        beam = sorted(nxt, key=lambda B: (order(B), len(B)))[:6]
        if not beam:
            return None
    return None


def derive(delta):
    """(alphabet, tc, fact) with fact: δ (local letters) ⟶ ε, or None."""
    A = alphabet(delta)
    if A is None:
        return None
    loc = {g: i for i, g in enumerate(A)}
    rels = [r for r in base() if all(g in loc for g in r)]
    axioms = [PR.Axiom(f'b{T.relators_tower().index(r)}', tuple(loc[g] for g in r), ()) for r in rels]
    tc = LB.LabelledTC(len(A), axioms, {}, limit=4 * MAXORDER)
    live = tc.run()
    assert len(live) == order(A)
    word = tuple(loc[g] for g in delta)
    i, c, lab, st = tc.walk(0, word)
    assert i == len(word) and tc.root(c) == 0 and lab == ()
    f = tc._add(word, (), st)
    return A, tc, f


if __name__ == '__main__':
    delta = tuple(T.INDEX_N[x] for x in sys.argv[1].split())
    res = derive(delta)
    if res is None:
        print('no small presented alphabet')
    else:
        A, tc, f = res
        print('alphabet', [T.NAME[g] for g in A], 'order', order(A), 'facts', len(tc.facts))

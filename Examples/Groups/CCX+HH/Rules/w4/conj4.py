#!/usr/bin/env python3
"""The conjugation calculus of the four-wire classical tower: the rules
at every placement of their wires, derived from level 0.

Level 0 (tower4.relators_tower) has the rules at adjacent placements
only, and the other letters as swap conjugates of adjacent ones.  Here
every letter is written as W · b₀ · rev W, W a word in the adjacent
swaps and b₀ one base letter of its kind (X0, CX1>0, CX0>1, SW01,
CCX0;12).  Two such conjugates of b₀ are equal when the swap words
differ by an element of b₀'s stabiliser in S4; that element is a word
in adjacent swaps commuting with b₀ (by a level-0 relator), and the
difference is an identity in S4, derived by a proof-producing
enumeration of the 24 permutations of the wires.

`Facts` keeps derivations as in `../proofs.py` (lhs, rhs, steps over
the global letters); `conj_fact(word, word2)` derives word ⟶ word2 for
two conjugates; `placed()` lists every placed rule instance (and every
swap naturality), each with a derivation from level 0.

    python3 -B conj4.py          # derive and replay them all
"""
import sys
import itertools
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))
import labelled as LB
import proofs as PR
import tower4 as T

N = T.N
SWAP = [T.INDEX[('SW', i, i + 1)] for i in range(N - 1)]       # adjacent swaps
REL0 = T.relators_tower()
RIX = {r: j for j, r in enumerate(REL0)}
DEFS = T.definitions()


class Facts:
    """Derivations over the global letters, steps (pos, kind, fwd) with
    kind ('ax', j) a level-0 relator, ('inv', g) or ('fact', f)."""

    def __init__(self):
        self.facts = []

    def add(self, lhs, rhs, steps):
        self.facts.append(PR.Fact(tuple(lhs), tuple(rhs), list(steps)))
        return len(self.facts) - 1

    @staticmethod
    def cancel(pos, word):
        return [(pos + j, ('inv', word[j]), True) for j in range(len(word) - 1, -1, -1)]

    @staticmethod
    def reverse(steps):
        return [(p, k, not f) for (p, k, f) in reversed(steps)]

    def insert(self, pos, word):
        return self.reverse(self.cancel(pos, word))

    def replay(self, f):
        fact = self.facts[f]
        xs = list(fact.lhs)
        for pos, (kind, key), fwd in fact.steps:
            if kind == 'ax':
                l, r = REL0[key], ()
            elif kind == 'inv':
                l, r = (key, key), ()
            else:
                l, r = self.facts[key].lhs, self.facts[key].rhs
            if not fwd:
                l, r = r, l
            if tuple(xs[pos:pos + len(l)]) != tuple(l):
                return False
            xs = xs[:pos] + list(r) + xs[pos + len(l):]
        return tuple(xs) == tuple(fact.rhs)


F = Facts()


def rel_fact(r):
    """A fact r ⟶ ε for a level-0 relator (or a rotation/reverse of one)."""
    r = tuple(r)
    if r in RIX:
        return F.add(r, (), [(0, ('ax', RIX[r]), True)])
    raise KeyError(r)


def eq_fact(lhs, rhs):
    """lhs ⟶ rhs from the level-0 relator lhs · rev(rhs)."""
    rel = tuple(lhs) + tuple(reversed(rhs))
    j = RIX[rel]
    # lhs -> lhs rhs rev(rhs) ... : lhs -> lhs · (rev rhs · rhs) -> (lhs · rev rhs) · rhs -> rhs
    steps = F.insert(len(lhs), tuple(reversed(rhs)))
    steps += [(0, ('ax', j), True)]
    return F.add(lhs, rhs, steps)


# ---------------------------------------------------------------------
# S4: words in the adjacent swaps

def wperm(word):
    """The permutation of the wires a swap word induces on placements:
    a gate on wires ws is carried to wires p[ws] by W · g · rev W."""
    p = list(range(N))
    for s in reversed(word):
        a, b = T.LETTERS[s][1], T.LETTERS[s][2]
        p = [b if x == a else a if x == b else x for x in p]
    return tuple(p)


S4_TC = None


def s4():
    global S4_TC
    if S4_TC is None:
        loc = {g: i for i, g in enumerate(SWAP)}
        rels = [r for r in REL0 if all(g in loc for g in r)]
        axioms = [PR.Axiom(f'b{RIX[r]}', tuple(loc[g] for g in r), ()) for r in rels]
        tc = LB.LabelledTC(len(SWAP), axioms, {}, limit=10_000)
        live = tc.run()
        assert len(live) == 24, len(live)
        S4_TC = tc
    return S4_TC


def import_fact(tc, f, memo={}):
    """Copy a fact of the S4 enumeration (local letters) into F."""
    if f in memo:
        return memo[f]
    fact = tc.facts[f]
    steps = []
    for pos, (kind, key), fwd in fact.steps:
        if kind == 'ax':
            steps.append((pos, ('ax', int(tc.axioms[key].name[1:])), fwd))
        elif kind == 'inv':
            steps.append((pos, ('inv', SWAP[key]), fwd))
        else:
            steps.append((pos, ('fact', import_fact(tc, key)), fwd))
    g = F.add(tuple(SWAP[y] for y in fact.lhs), tuple(SWAP[y] for y in fact.rhs), steps)
    memo[f] = g
    return g


def s4_identity(word):
    """A fact word ⟶ ε for a swap word that is the identity on wires."""
    tc = s4()
    loc = {g: i for i, g in enumerate(SWAP)}
    w = tuple(loc[g] for g in word)
    i, c, lab, st = tc.walk(0, w)
    assert i == len(w) and tc.root(c) == 0 and lab == ()
    f = tc._add(w, (), st)
    return import_fact(tc, f)


# ---------------------------------------------------------------------
# Letters as conjugates of base letters

BASE = {'X': T.INDEX[('X', 0)], 'CX': T.INDEX[('CX', 1, 0)], 'CXr': T.INDEX[('CX', 0, 1)],
        'SW': T.INDEX[('SW', 0, 1)], 'CCX': T.INDEX[('CCX', 0, 1, 2)]}


def kind(g):
    l = T.LETTERS[g]
    if l[0] == 'CX':
        return 'CX' if l[1] > l[2] else 'CXr'
    return l[0]


def placement(g):
    """The wires of a letter, as an ordered tuple matching BASE's."""
    l = T.LETTERS[g]
    if l[0] == 'X':
        return (l[1],)
    if l[0] == 'CX':
        return (l[1], l[2])             # control, target
    if l[0] == 'SW':
        return (l[1], l[2])
    return (l[1], l[2], l[3])           # target, controls


def stabiliser_words(b):
    """Adjacent swaps that commute with the base letter b (as relators)."""
    return {'X': [SWAP[1], SWAP[2]], 'CX': [SWAP[2]], 'CXr': [SWAP[2]],
            'SW': [SWAP[0], SWAP[2]], 'CCX': [SWAP[1]]}[b]


def same_letter(k, ws1, ws2):
    if k == 'SW' or k == 'CCX':
        if k == 'SW':
            return set(ws1) == set(ws2)
        return ws1[0] == ws2[0] and set(ws1[1:]) == set(ws2[1:])
    return ws1 == ws2


def conj_word(g):
    """A swap word W with g = W · base · rev W (as permutations), shortest."""
    k = kind(g)
    target = placement(g)
    base = placement(BASE[k])
    for n in range(0, 7):
        for W in itertools.product(SWAP, repeat=n):
            p = wperm(W)
            if same_letter(k, tuple(p[x] for x in base), target):
                return W
    raise ValueError(g)


CONJ = {}


def letter_fact(g):
    """A fact g ⟶ W · base · rev W (W = conj_word(g))."""
    if g in CONJ:
        return CONJ[g]
    k = kind(g)
    b = BASE[k]
    W = conj_word(g)
    target = W + (b,) + tuple(reversed(W))
    if g == b:
        f = F.add((g,), (g,), [])
    else:
        # g ⟶ def(g) or a chain of naturality relators: search via the
        # S4 calculus on the expanded word
        f = expand_to_base(g, W)
    CONJ[g] = (W, f)
    return CONJ[g]


def expand_to_base(g, W):
    """g ⟶ W b rev W by: g = its definition (if not adjacent) then each
    adjacent primitive in it rewritten by naturality towards the base."""
    raise NotImplementedError


if __name__ == '__main__':
    tc = s4()
    print('S4 presented by the swap relators: 24 cosets,', len(tc.facts), 'facts')
    for g in range(len(T.LETTERS)):
        W = conj_word(g)
        print(T.NAME[g], '=', ' '.join(T.NAME[s] for s in W), T.NAME[BASE[kind(g)]], '…')

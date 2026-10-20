#!/usr/bin/env python3
"""A lemma library for the V_Z finder: every short four-wire relation.

The relators w₁ · rev(w₂) with words of at most `half` letters (all 40
placed letters, exact matrices), spanning four wires, freely reduced and
not a plain commutation of disjoint letters (as `g4derive.py`), at every
placement of the wires.  Each is a consequence of the rules with K_CCZ
(the finder derives them: `g4derive.py`, `diag4.py --kick`), so in a
proof it is a lemma with its own derivation.

    python3 -B lemmas4.py [half]        writes lemmas4.pkl
    load() -> the relators
"""
import itertools
import pickle
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'wn'))
import finder as F

PKL = HERE / 'lemmas4.pkl'


def relabel(A, g, pi):
    l = A.LETTERS[g]
    k = l[0]
    if k == 'X':
        return A.INDEX[('X', pi[l[1]])]
    if k == 'CX':
        return A.INDEX[('CX', pi[l[1]], pi[l[2]])]
    if k == 'CCX':
        a, b = sorted((pi[l[2]], pi[l[3]]))
        return A.INDEX[('CCX', pi[l[1]], a, b)]
    a, b = sorted((pi[l[1]], pi[l[2]]))
    return A.INDEX[(k, a, b)]


def build(half):
    A = F.Alphabet(4)
    letters = range(len(A.LETTERS))
    buckets = {}
    layer = [()]
    for _ in range(half):
        nxt = []
        for w in layer:
            for g in letters:
                if not w or w[-1] != g:
                    nxt.append(w + (g,))
        for w in nxt:
            buckets.setdefault(A.matrix(w), []).append(w)
        layer = nxt
    out = set()
    for ws in buckets.values():
        ws.sort(key=len)
        for b in ws[1:]:
            r = ws[0] + tuple(reversed(b))
            if set().union(*(A.WIRES[g] for g in r)) != {0, 1, 2, 3}:
                continue
            if len(r) == 4 and r[0] == r[2] and r[1] == r[3] and not (A.WIRES[r[0]] & A.WIRES[r[1]]):
                continue
            if any(r[i] == r[i + 1] for i in range(len(r) - 1)):
                continue
            for pi in itertools.permutations(range(4)):
                out.add(tuple(relabel(A, g, pi) for g in r))
    return sorted(out, key=lambda r: (len(r), r))


def load():
    return pickle.load(open(PKL, 'rb'))


if __name__ == '__main__':
    half = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    rels = build(half)
    pickle.dump(rels, open(PKL, 'wb'))
    print(len(rels), 'lemmas (all placements)')

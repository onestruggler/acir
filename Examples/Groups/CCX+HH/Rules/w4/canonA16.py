#!/usr/bin/env python3
"""Canonical classical words on four wires, from the A16 tower.

The tower's levels (pipe16.a16_spec) give every permutation of A16 a
canonical word: the representatives of its cosets, level by level.
`python3 -B canonA16.py` builds the tower once and pickles what the
canonical word needs (canonA16.pkl); `load()` reads it back and
`canon(p)` returns the word (letter indices of tower4.LETTERS) of the
permutation p (a tuple of 16 levels, as tower4/pipe16 compose them)."""
import pickle
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))

PKL = HERE / 'canonA16.pkl'
D = 16
ID = tuple(range(D))


def mul(a, b):
    return tuple(a[x] for x in b)


def inv(a):
    r = [0] * D
    for i, j in enumerate(a):
        r[j] = i
    return tuple(r)


def build():
    import pipe16 as P16
    rels = P16.named_relators([('a', HERE / 'aff4extra.txt'), ('e', HERE / 'tower16extra.txt')])
    levels = P16.build(P16.a16_spec(), rels)      # bottom first
    data = []
    for lev in reversed(levels):                  # top first
        data.append({'reps': lev.reps, 'repsp': lev.repsp,
                     'kind': getattr(lev, 'up_kind', None), 'k': lev.k})
    pickle.dump(data, open(PKL, 'wb'))
    print('saved', len(data), 'levels')


DATA = None


def load():
    global DATA
    if DATA is None:
        DATA = pickle.load(open(PKL, 'rb'))
    return DATA


def member(kind, h):
    if kind is None:
        return h == ID
    if kind[0] == 'point':
        return h[kind[1]] == kind[1]
    if kind[0] == 'pair':
        return {h[kind[1]], h[kind[2]]} == {kind[1], kind[2]}
    col = kind[1]
    return all(col[h[x]] == col[x] for x in range(D))


def canon(g):
    """The canonical word of g: from the top level down, the
    representative of g's coset over the next level, then the canonical
    word of what is left (which lies in the next level)."""
    data = load()
    word = ()
    for i, lev in enumerate(data):
        hit = None
        for c, r in enumerate(lev['repsp']):
            h = mul(g, inv(r))
            if member(KINDS[i], h):
                hit = (c, h)
                break
        assert hit is not None, i
        c, h = hit
        word = word + lev['reps'][c] if False else word
        word = lev['reps'][c] + word
        g = h
    assert g == ID
    return word


def _kinds():
    import tower16 as T16
    return T16.kinds() + [None]


KINDS = None
if __name__ == '__main__':
    build()
else:
    import tower16 as _T16
    KINDS = _T16.kinds() + [None]

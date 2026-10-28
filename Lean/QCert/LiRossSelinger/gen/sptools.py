"""Derivations between words over N, X (signed permutations), by incremental
normalisation to canonical words, each append found by a small BFS."""
import sys
from alg import ident, word_apply
from bfs import Engine, apply_steps
from sp import sp_word

SPF = ['r1a', 'r1b', 'r2a', 'r2b', 'r2d', 'r3a', 'r3b', 'r3c']
_eng = {}
_memo = {}

def eng(m):
    if m not in _eng:
        _eng[m] = Engine(m, fams=SPF, rev=True)
    return _eng[m]

def canon(w, m):
    return sp_word(word_apply(list(w), ident(m)))

def append_step(c, g, m):
    """Steps from c + (g,) to canon(c + (g,)), c canonical."""
    key = (m, c, g)
    if key in _memo:
        return _memo[key]
    src = c + (g,)
    tgt = canon(src, m)
    E = eng(m)
    st = None
    for extra in (1, 2, 3, 4):
        st = E.search(src, tgt, depth=14, maxlen=max(len(src), len(tgt)) + extra,
                      ins_letters=set(src) | set(tgt), limit=400_000)
        if st is not None:
            break
    if st is None:
        raise RuntimeError(('append failed', m, c, g, tgt))
    _memo[key] = st
    return st

def to_canon(w, m, off=0):
    """Steps (at offset off) turning the sp word w into its canonical word."""
    steps = []
    c = ()
    for j, g in enumerate(w):
        # current word: c + w[j:]; normalise c + (g,)
        st = append_step(c, g, m)
        steps += [(f, ps, d, p + off) for (f, ps, d, p) in st]
        c = canon(c + (g,), m)
    return steps, c

def invert(steps):
    return [(f, ps, not d, pos) for (f, ps, d, pos) in reversed(steps)]

def sp_derive(w, w2, m, off=0):
    """Steps from w to w2 (same signed permutation), at offset off."""
    s1, c1 = to_canon(w, m, off)
    s2, c2 = to_canon(w2, m, off)
    assert c1 == c2
    return s1 + invert(s2)

def is_sp(w):
    return all(g[0] in ('n', 'x') for g in w)

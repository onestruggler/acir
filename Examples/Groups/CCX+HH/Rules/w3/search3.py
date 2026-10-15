"""Derivation search on three wires: natural three-wire rules, with any
segment acting on two wires (and possibly X on the third) rewritten
freely, as completeness on two wires allows.

Words are tuples of letter names.  A segment of type A uses only
X0 X1 X2 CX0 HH0 (gates on wires 0,1 plus X on wire 2); type B only
X0 X1 X2 CX1 HH1.  Each maximal segment is replaced by a canonical word
of its element (shortest, then lexicographic).
"""
import sys, itertools
from collections import deque
sys.path.insert(0, '..')
from e8 import ACT, E, LETTERS

def perm(word):
    """Action on the 8 basis vectors at scale 2, as a tuple of vectors."""
    return tuple(act_word(word, e) for e in E)

def act_word(word, v):
    for g in reversed(word):
        v = ACT[g](v)
    return v

A = ('X0', 'X1', 'X2', 'CX0', 'HH0')
B = ('X0', 'X1', 'X2', 'CX1', 'HH1')

def shortest_words(letters):
    start = ()
    key = perm(start)
    best = {key: start}
    fr = [start]
    while fr:
        nw = []
        for w in fr:
            for g in letters:
                w2 = w + (g,)
                k = perm(w2)
                if k not in best:
                    best[k] = w2
                    nw.append(w2)
        fr = nw
    return best

CANON_A = shortest_words(A)
CANON_B = shortest_words(B)
print('A elements', len(CANON_A), 'B elements', len(CANON_B), file=sys.stderr)

def canon(word):
    out = []
    i = 0
    n = len(word)
    while i < n:
        g = word[i]
        if g == 'CCX0':
            out.append(g); i += 1; continue
        # choose the type that extends furthest
        def run(T):
            j = i
            while j < n and word[j] in T:
                j += 1
            return j
        ja, jb = run(A), run(B)
        if ja >= jb:
            seg = word[i:ja]; out.extend(CANON_A[perm(seg)]); i = ja
        else:
            seg = word[i:jb]; out.extend(CANON_B[perm(seg)]); i = jb
    return tuple(out)

def macro(s):
    out = []
    for t in s.split():
        if t.startswith('XC'):
            i = t[2]; out += [f'HH{i}', f'CX{i}', f'HH{i}']
        elif t.startswith('Ex'):
            i = t[2]; out += [f'CX{i}', f'HH{i}', f'CX{i}', f'HH{i}', f'CX{i}']
        elif t == 'C':
            out.append('CCX0')
        else:
            out.append(t)
    return tuple(out)

RULES3 = [
    ("braid", "Ex0 Ex1 Ex0", "Ex1 Ex0 Ex1"),
    ("CX-up", "Ex0 Ex1 CX0 Ex1 Ex0", "CX1"),
    ("CCX-sym", "Ex1 C Ex1", "C"),
    ("CCX-neg", "X1 C X1", "C Ex1 CX0 Ex1"),
    ("CCX-XC", "C XC0 C XC0", "Ex0 C Ex0 C"),
    ("HH-swap0", "Ex0 HH1 Ex0", "HH0 HH1"),
    ("HH-swap1", "Ex1 HH0 Ex1", "HH0 HH1"),
    ("CCX-HH", "C XC0 HH0 XC0", "XC0 HH0 XC0 C"),
]
RULES = []
for name, l, r in RULES3:
    L, R = macro(l), macro(r)
    assert perm(L) == perm(R), name
    RULES.append((name, L, R))
    RULES.append((name + '⁻', R, L))
    # relators as cyclic rotations too: L R^-1 = ε, so any rotation
    rel = L + tuple(reversed(R))
    for k in range(1, len(rel)):
        rot = rel[k:] + rel[:k]
        # rot = ε  i.e. prefix = inverse of suffix
    # (kept simple: only forward/backward rewrites)

def neighbours(w):
    out = []
    for name, L, R in RULES:
        m = len(L)
        for i in range(len(w) - m + 1):
            if w[i:i + m] == L:
                out.append((canon(w[:i] + R + w[i + m:]), (name, i)))
    # also insert a rule's relator: since every letter is an involution,
    # L = R gives L R^-1 = ε; insert it anywhere (bounded use)
    return out

def search(u, v, maxlen=40, maxnodes=200000):
    u, v = canon(u), canon(v)
    if u == v:
        return []
    fu = {u: None}; fv = {v: None}
    qu, qv = deque([u]), deque([v])
    while qu and qv and len(fu) + len(fv) < maxnodes:
        for (q, f, other) in ((qu, fu, fv), (qv, fv, fu)):
            for _ in range(len(q)):
                w = q.popleft()
                for w2, step in neighbours(w):
                    if len(w2) > maxlen or w2 in f:
                        continue
                    f[w2] = (w, step)
                    if w2 in other:
                        return ('found', len(fu), len(fv))
                    q.append(w2)
    return ('fail', len(fu), len(fv))

if __name__ == '__main__':
    tests = [
        ('C X0 = X0 C', 'C X0', 'X0 C'),
        ('C CX0 = CX0 C', 'C CX0', 'CX0 C'),
        ('C HH0 X1 HH0 = .. (Z1)', 'C HH0 X1 HH0', 'HH0 X1 HH0 C'),
        ('X2 C X2 C commutes w X1 C X1 C', 'X2 C X2 X1 C X1', 'X1 C X1 X2 C X2'),
    ]
    for name, l, r in tests:
        L, R = macro(l), macro(r)
        print(name, 'semantic', perm(L) == perm(R), search(L, R), flush=True)

#!/usr/bin/env python3
"""Exact synthesis of short NaturalP circuits for a target operator.

Gates of NaturalP on w wires, wire 0 least significant: X i, CX i (target
i, control i+1), HH i (wires i, i+1), SW i (swap of i, i+1), CCX i
(target i, controls i+1, i+2).  A word g1 ... gk denotes G1 ... Gk (gk
acts first), as in Natural and NaturalP; every gate is an involution.

Meet in the middle on the action on two probe vectors with large integer
entries (scaled so that halvings stay integral): A T p = V p, A and V
built by prepending gates, gives T = rev(A) V.  A hit is then checked on
every basis vector, exactly.
"""
import random, sys

def gates(w):
    G = [('X', i) for i in range(w)]
    for i in range(w - 1):
        G += [('CX', i), ('HH', i), ('SW', i)]
    G += [('CCX', i) for i in range(w - 2)]
    return G

def apply_gate(g, v, w):
    kind, i = g
    N = 1 << w
    out = list(v)
    if kind == 'X':
        for x in range(N):
            out[x ^ (1 << i)] = v[x]
    elif kind == 'CX':
        for x in range(N):
            out[x ^ (1 << i) if x >> (i + 1) & 1 else x] = v[x]
    elif kind == 'CCX':
        for x in range(N):
            out[x ^ (1 << i) if (x >> (i + 1) & 1) and (x >> (i + 2) & 1) else x] = v[x]
    elif kind == 'SW':
        for x in range(N):
            a, b = x >> i & 1, x >> (i + 1) & 1
            out[x & ~(3 << i) | (b << i) | (a << (i + 1))] = v[x]
    elif kind == 'HH':
        for base in range(N):
            if base & (3 << i):
                continue
            idx = [base | (r << i) for r in range(4)]
            for r in range(4):
                s = sum((-1) ** bin(r & c).count('1') * v[idx[c]] for c in range(4))
                assert s % 2 == 0
                out[idx[r]] = s // 2
    return tuple(out)

def apply_word(word, v, w):
    for g in reversed(word):
        v = apply_gate(g, v, w)
    return v

def frontier_search(start_vecs, w, depth, tag):
    G = gates(w)
    key0 = tuple(start_vecs)
    seen = {key0: ()}
    frontier = [(key0, ())]
    for d in range(depth):
        nxt = []
        for vecs, word in frontier:
            for g in G:
                if word and word[0] == g:
                    continue
                nv = tuple(apply_gate(g, v, w) for v in vecs)
                if nv not in seen:
                    seen[nv] = (g,) + word
                    nxt.append((nv, (g,) + word))
        frontier = nxt
        print(f'  {tag} depth {d + 1}: {len(seen)}', file=sys.stderr, flush=True)
    return seen

def synth(T, w, L1, L2, seed=0, scale=1 << 24):
    """T: function on basis-index -> column vector (exact Fractions or ints
    times 1/scale0).  We pass T as a function acting on integer vectors."""
    rnd = random.Random(seed)
    N = 1 << w
    probes = [tuple(rnd.randrange(-10**6, 10**6) * scale for _ in range(N)) for _ in range(2)]
    left = frontier_search([T(p) for p in probes], w, L1, 'A')     # A T p
    right = frontier_search(probes, w, L2, 'V')                    # V p
    for key, V in right.items():
        if key in left:
            A = left[key]
            word = tuple(reversed(A)) + V
            # exact check on basis vectors (scaled)
            ok = all(apply_word(word, e, w) == T(e)
                     for e in (tuple(scale * int(i == j) for i in range(N)) for j in range(N)))
            if ok:
                return word
    return None

def show(word):
    return ' '.join(f'{k}{i}' for k, i in word)

# ---------------------------------------------------------------------
# Targets: controlled operators, control wire c, the gate word on other
# wires, borrowed wires idle.

def controlled(word, w, c):
    def T(v):
        N = 1 << w
        inner = apply_word(word, v, w)
        return tuple(inner[x] if x >> c & 1 else v[x] for x in range(N))
    return T

if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'CHHa'
    L1, L2 = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (5, 5)
    if which == 'CHHa':        # control 0, HH on wires 1 2, wire 3 borrowed
        w, T = 4, controlled([('HH', 1)], 4, 0)
    elif which == 'CHHb':      # control 0, wire 1 borrowed, HH on 2 3
        w, T = 4, controlled([('HH', 2)], 4, 0)
    elif which == 'C3Xa':      # control 0, CCX on wires 1 2 3 (target 1), wire 4 borrowed
        w, T = 5, controlled([('CCX', 1)], 5, 0)
    elif which == 'C3Xb':      # control 0, wire 1 borrowed, CCX on 2 3 4
        w, T = 5, controlled([('CCX', 2)], 5, 0)
    elif which == 'Fredkin':   # control 0, swap of 1 2
        w, T = 3, controlled([('SW', 1)], 3, 0)
    elif which == 'CCXc':      # control 0, CX on 1 2 (target 1, control 2)
        w, T = 3, controlled([('CX', 1)], 3, 0)
    elif which == 'XC':        # control 0, X on 1
        w, T = 2, controlled([('X', 1)], 2, 0)
    else:
        raise SystemExit('unknown target')
    word = synth(T, w, L1, L2)
    print(which, len(word) if word else None, show(word) if word else '')

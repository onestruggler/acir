#!/usr/bin/env python3
"""Clément decoding of every four-state Schreier generator, n >= 4.

The source is the scaled two-level presentation (Tables 1 and 2).  The
four representatives are 1, M_0, X_01, M_0 X_01.  A Schreier edge is
rep(c) g inverse(rep(c.g)).  This script constructs a circuit over
X, CX, CCX and H for each such edge, without adding wires.

The generic auxiliary subgroup presentation and the four IH formulas
are Agda theorems in this directory.  The physical constructions here
have exact executable checks; their symbolic-width Agda verification
is a separate obligation.  No numerical approximation is used.
"""

from __future__ import annotations

import argparse
from functools import lru_cache
import importlib.util
from itertools import combinations
from pathlib import Path
import random


_path = Path(__file__).resolve().parents[2] / 'CCX+HH' / 'GeneralN' / 'construct.py'
_spec = importlib.util.spec_from_file_location('dyadic_construct', _path)
dyadic = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(dyadic)
Matrix, canonical = dyadic.Matrix, dyadic.canonical
identity, append_gate = dyadic.identity, dyadic.append_gate

# States are (determinant parity, rational spinor-2 parity).
STATES = ((0, 0), (1, 0), (1, 1), (0, 1))
REPS = {STATES[0]: (), STATES[1]: (('M', (0,)),),
        STATES[2]: (('X', (0, 1)),),
        STATES[3]: (('M', (0,)), ('X', (0, 1)))}


def step(state, letter):
    d, s = state
    name, _ = letter
    if name == 'IH':
        return d, s ^ d
    x, y = {'M': (1, 0), 'X': (1, 1), 'K': (0, 1)}[name]
    return d ^ x, s ^ y


def edge_word(state, letter):
    return REPS[state] + (letter,) + tuple(reversed(REPS[step(state, letter)]))


def source_alphabet(n):
    size = 1 << n
    yield from (('M', (a,)) for a in range(size))
    yield from (('X', ab) for ab in combinations(range(size), 2))
    yield from (('K', abcd) for abcd in combinations(range(size), 4))
    yield 'IH', ()


def signed_data(n, word):
    """Return (negative output indices, column permutation) for an M/X word."""
    p, signs = list(range(1 << n)), [1] * (1 << n)
    for name, indices in reversed(word):
        if name == 'M':
            a, = indices
            signs = [-s if y == a else s for y, s in zip(p, signs)]
        else:
            assert name == 'X'
            a, b = indices
            p = [b if y == a else a if y == b else y for y in p]
    negatives = tuple(sorted(y for y, s in zip(p, signs) if s == -1))
    assert len(negatives) % 2 == 0, 'odd number of signs'
    assert sum(p[i] > p[j] for i in range(len(p))
               for j in range(i + 1, len(p))) % 2 == 0, 'odd permutation'
    return negatives, tuple(p)


@lru_cache(maxsize=None)
def signed_permutation(n, word):
    negatives, p = signed_data(n, word)
    signs = sum((dyadic.sign_pair(n, a, b)
                 for a, b in zip(negatives[::2], negatives[1::2])), ())
    return signs + dyadic.permutation_word(n, p)


def k_factors(n, state, indices):
    """L K_A R = T S^-1 (M_a X_bc K_A) S, with T,S even signed.

    T=L X_bc M_a R.  Set S=Z R, where Z has the M/X parities
    of R and is supported outside A.  Thus Z commutes with the mixed
    atom, and the displayed identity follows by cancellations alone.
    """
    a, b, c, _ = indices
    letter = 'K', indices
    left, right = REPS[state], tuple(reversed(REPS[step(state, letter)]))
    t = left + (('X', (b, c)), ('M', (a,))) + right
    e, f = tuple(i for i in range(1 << n) if i not in indices)[:2]
    z = ((('M', (e,)),) if sum(g[0] == 'M' for g in right) % 2 else ())
    z += ((('X', (e, f)),) if sum(g[0] == 'X' for g in right) % 2 else ())
    s = z + right
    signed_data(n, t)
    signed_data(n, s)
    return t, s


def plan(n, state, letter):
    """A short exact source-word expansion of the circuit construction."""
    name, indices = letter
    if name in ('M', 'X'):
        return edge_word(state, letter)
    if name == 'IH':
        return (() if state == (0, 0) else (('M', (0,)), ('M', (1,)))) + (letter,)
    t, s = k_factors(n, state, indices)
    a, b, c, _ = indices
    mixed = (('M', (a,)), ('X', (b, c)), letter)
    return t + tuple(reversed(s)) + mixed + s


def expand_hh(word):
    return tuple(g for name, wires in word
                 for g in ((('H', (wires[0],)), ('H', (wires[1],)))
                           if name == 'HH' else ((name, wires),)))


def decode_edge(n, state, letter, adjacent=False):
    """Actual fixed-width circuit, using only X,CX,CCX,H."""
    assert n >= 4 and state in STATES
    name, indices = letter
    if name in ('M', 'X'):
        word = signed_permutation(n, edge_word(state, letter))
    elif name == 'IH':
        word = (() if state == (0, 0) else dyadic.sign_pair(n, 0, 1))
        if adjacent:
            word = dyadic.to_adjacent(n, word)
        return expand_hh(word) + (('H', (0,)),)
    else:
        assert name == 'K'
        t, s = k_factors(n, state, indices)
        ts, ss = signed_permutation(n, t), signed_permutation(n, s)
        word = ts + dyadic.inverse(ss) + dyadic.mixed(n, indices) + ss
    if adjacent:
        word = dyadic.to_adjacent(n, word)
    return expand_hh(word)


def append_source(value, letter, n):
    """Independent exact source matrices, by right column operations."""
    name, indices = letter
    if name == 'IH':
        return append_gate(value, ('H', (0,)), n)
    size, entries = 1 << n, list(value.entries)
    if name == 'M':
        a, = indices
        for r in range(size):
            entries[r * size + a] *= -1
        return canonical(value.exponent, tuple(entries))
    if name == 'X':
        a, b = indices
        for r in range(size):
            i, j = r * size + a, r * size + b
            entries[i], entries[j] = entries[j], entries[i]
        return canonical(value.exponent, tuple(entries))
    assert name == 'K' and tuple(sorted(set(indices))) == indices and len(indices) == 4
    out = [2 * x for x in entries]
    for r in range(size):
        old = [entries[r * size + c] for c in indices]
        for j, c in enumerate(indices):
            out[r * size + c] = sum((-1 if (i & j).bit_count() % 2 else 1) * x
                                    for i, x in enumerate(old))
    return canonical(value.exponent + 2, tuple(out))


def source_matrix(n, word):
    value = identity(n)
    for g in word:
        value = append_source(value, g, n)
    return value


def audit(n, samples, exhaustive=True):
    assert n >= 4
    alphabet = tuple(source_alphabet(n))
    edges = [(c, g) for c in STATES for g in alphabet]
    rng = random.Random(41089)
    plans = edges if exhaustive else rng.sample(edges, min(1000, len(edges)))
    for state, letter in plans:
        if letter[0] in ('M', 'X'):
            signed_data(n, edge_word(state, letter))
        assert source_matrix(n, plan(n, state, letter)) == source_matrix(n, edge_word(state, letter)), (state, letter)
    print(f'PASS {len(plans)} exact Schreier plans at n={n}', flush=True)
    chosen = [(c, ('IH', ())) for c in STATES]
    for kind in ('M', 'X', 'K'):
        pool = [(c, g) for c, g in edges if g[0] == kind]
        chosen += rng.sample(pool, min(samples, len(pool)))
    for state, letter in chosen:
        expected = source_matrix(n, edge_word(state, letter))
        word = decode_edge(n, state, letter)
        assert dyadic.matrix(n, word) == expected, (state, letter, 'physical')
        adjacent = decode_edge(n, state, letter, adjacent=True)
        assert dyadic.matrix(n, adjacent) == expected, (state, letter, 'adjacent')
        for name, wires in adjacent:
            assert name in ('X', 'CX', 'CCX', 'H')
            assert name not in ('CX', 'CCX') or wires == tuple(range(wires[-1] + 1, wires[-1] + len(wires))) + (wires[-1],)
        print(f'PASS {state} {letter}: {len(word)} gates, {len(adjacent)} adjacent gates', flush=True)
    print(f'PASS {len(chosen)} physical edge circuits; all {1 << n} basis states included.', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--wires', type=int, default=4)
    parser.add_argument('--samples', type=int, default=4,
                        help='physical circuits checked per dyadic generator family')
    parser.add_argument('--sample-plans', action='store_true',
                        help='check 1000 plans instead of every source edge')
    args = parser.parse_args()
    audit(args.wires, args.samples, not args.sample_plans)

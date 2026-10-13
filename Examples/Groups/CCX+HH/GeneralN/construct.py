#!/usr/bin/env python3
"""Fixed-width, ancilla-free constructions for the dyadic charge kernel.

Only X, CX, CCX and HH are used.  Temporary work bits have arbitrary
input values and are restored on every computational basis state.  No
wire is added.  Words have matrix-product order.  A gate is (name,wires),
with controls before target for CX/CCX.  Public constructors initially
allow arbitrary distinct wire placements; to_adjacent expands these to
the shifted adjacent primitives of Circuit.Base.

This executable construction is independently checked with exact
arithmetic.  The accompanying Agda modules prove the physical primitive
constructions at symbolic width; the Python and Agda output words are
not asserted to be literally identical.  The identities used come from
auxiliary Table 1 and elementary reversible Boolean algebra.
"""

from __future__ import annotations

import argparse
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from exact_matrices import Matrix, canonical, identity, append_gate, evaluate


def gate(kind, *wires):
    return ((kind, tuple(wires)),)


def inverse(word):
    # Every primitive gate is an involution.
    return tuple(reversed(word))


@lru_cache(maxsize=None)
def mcx(n, controls, target):
    """C^k X with k<=n-2, using one arbitrary, restored work bit.

    For k>=3, A toggles a spare bit by the first two controls and B
    toggles the target by that spare bit and the remaining controls.
    A B A B toggles the target by the AND of all k original controls.
    B has k-1 controls, giving structural recursion on k.
    """
    controls = tuple(controls)
    assert len(set(controls + (target,))) == len(controls) + 1
    assert all(0 <= i < n for i in controls + (target,))
    assert len(controls) <= n - 2
    if not controls:
        return gate('X', target)
    if len(controls) == 1:
        return gate('CX', controls[0], target)
    if len(controls) == 2:
        return gate('CCX', *controls, target)
    spare = next(i for i in range(n) if i not in controls and i != target)
    a = gate('CCX', controls[0], controls[1], spare)
    b = mcx(n, (spare,) + controls[2:], target)
    return a + b + a + b


def zero_controlled_x(n, controls, target):
    negate = tuple(('X', (c,)) for c in controls)
    return negate + mcx(n, tuple(controls), target) + inverse(negate)


def rank(vectors):
    pivots = {}
    for vector in vectors:
        while vector:
            p = vector.bit_length() - 1
            if p in pivots:
                vector ^= pivots[p]
            else:
                pivots[p] = vector
                break
    return len(pivots)


def complete_basis(n, fixed):
    """Complete specified independent columns to an invertible matrix."""
    columns = [None] * n
    for i, v in fixed.items():
        columns[i] = v
    chosen = [v for v in columns if v is not None]
    assert rank(chosen) == len(chosen)
    for i in range(n):
        if columns[i] is None:
            v = next(1 << j for j in range(n)
                     if rank(chosen + [1 << j]) == len(chosen) + 1)
            columns[i] = v
            chosen.append(v)
    return tuple(columns)


def linear_word(n, columns):
    """Gaussian row reduction, with the inverse row operations as a word."""
    assert len(columns) == n and rank(columns) == n
    rows = [sum(((columns[c] >> r) & 1) << c for c in range(n)) for r in range(n)]
    word = ()
    for c in range(n):
        pivot = next(r for r in range(c, n) if rows[r] & (1 << c))
        if pivot != c:
            rows[c], rows[pivot] = rows[pivot], rows[c]
            word += gate('CX', c, pivot) + gate('CX', pivot, c) + gate('CX', c, pivot)
        for r in range(n):
            if r != c and rows[r] & (1 << c):
                rows[r] ^= rows[c]
                word += gate('CX', c, r)
    assert rows == [1 << i for i in range(n)]
    return word


def affine_word(n, columns, offset):
    return tuple(('X', (i,)) for i in range(n) if offset & (1 << i)) + linear_word(n, columns)


@lru_cache(maxsize=None)
def three_cycle(n, a, b, c):
    """The single basis-state cycle (a b c), fixing every other state."""
    assert n >= 4 and len({a, b, c}) == 3
    assert all(0 <= i < (1 << n) for i in (a, b, c))
    # A=(0 1)(4 5), B=(0 2)(8 10); their supports intersect only at 0.
    aw = zero_controlled_x(n, tuple(i for i in range(n) if i not in (0, 2)), 0)
    bw = zero_controlled_x(n, tuple(i for i in range(n) if i not in (1, 3)), 1)
    base = aw + bw + aw + bw
    columns = complete_basis(n, {0: a ^ b, 1: a ^ c})
    route = affine_word(n, columns, a)
    return route + base + inverse(route)


def double_exchange(n, a, b, c, d):
    """X_[a,b] X_[c,d]; pairs may share a point or coincide."""
    assert a != b and c != d
    if {a, b} == {c, d}:
        return ()
    if len({a, b, c, d}) == 4:
        # (a b)(c d) = (a c b)(a c d), in written product order.
        return three_cycle(n, a, c, b) + three_cycle(n, a, c, d)

    def swap(i, x, y):
        return y if i == x else x if i == y else i
    start = min(a, b, c, d)
    nxt = lambda i: swap(swap(i, c, d), a, b)
    return three_cycle(n, start, nxt(start), nxt(nxt(start)))


def permutation_word(n, permutation):
    """Synthesize any even permutation, fixing no unlisted workspace."""
    assert n >= 4 and sorted(permutation) == list(range(1 << n))
    visited, transpositions = set(), []
    for start in range(1 << n):
        if start in visited:
            continue
        cycle, current = [], start
        while current not in visited:
            visited.add(current)
            cycle.append(current)
            current = permutation[current]
        transpositions.extend((cycle[0], x) for x in reversed(cycle[1:]))
    assert len(transpositions) % 2 == 0, 'Odd permutations are outside the circuit image at n>=4'
    word = ()
    for i in range(0, len(transpositions), 2):
        word += double_exchange(n, *transpositions[i], *transpositions[i + 1])
    return word


def even_extension(n, sources, targets):
    """Complete a partial bijection to an even permutation.

    Two unused source points are enough to correct its parity without
    changing any requested image.  They are basis states, not ancillas.
    """
    assert len(set(sources)) == len(sources) == len(targets) == len(set(targets))
    size = 1 << n
    free_sources = [i for i in range(size) if i not in sources]
    free_targets = [i for i in range(size) if i not in targets]
    assert len(free_sources) >= 2
    result = [-1] * size
    for a, b in zip(tuple(sources) + tuple(free_sources), tuple(targets) + tuple(free_targets)):
        result[a] = b
    parity = sum(result[i] > result[j] for i in range(size) for j in range(i + 1, size)) % 2
    if parity:
        a, b = free_sources[:2]
        result[a], result[b] = result[b], result[a]
    return tuple(result)


@lru_cache(maxsize=None)
def sign_pair(n, a, b):
    """M_[a] M_[b], using HH to conjugate one double transposition."""
    assert n >= 4 and 0 <= a < (1 << n) and 0 <= b < (1 << n)
    if a == b:
        return ()
    controls = tuple(range(2, n))
    q = gate('HH', 0, 1)
    # Negative controls isolate the sign pair on basis vectors 1 and 3.
    base = q + zero_controlled_x(n, controls, 0) + q
    columns = complete_basis(n, {1: a ^ b})
    route = affine_word(n, columns, a ^ columns[0])
    return route + base + inverse(route)


@lru_cache(maxsize=None)
def disjoint_k_pair(n, qa, qb):
    assert n >= 4 and len(qa) == len(qb) == 4 and len(set(qa + qb)) == 8
    assert tuple(sorted(qa)) == qa and tuple(sorted(qb)) == qb
    s = sign_pair(n, 0, 4)
    q = gate('HH', 0, 1)
    p = double_exchange(n, 1, 2, 5, 6)
    # Table1 r4b in the two disjoint blocks; all other HH blocks cancel.
    base = s + q + s + q + s + p
    permutation = even_extension(n, tuple(range(8)), qa + qb)
    route = permutation_word(n, permutation)
    return route + base + inverse(route)


@lru_cache(maxsize=None)
def k_pair(n, qa, qb):
    """K_qa K_qb, including overlapping quadruples, for n>=4."""
    assert n >= 4 and tuple(sorted(set(qa))) == qa and tuple(sorted(set(qb))) == qb
    assert len(qa) == len(qb) == 4
    if qa == qb:
        return ()
    if not set(qa) & set(qb):
        return disjoint_k_pair(n, qa, qb)
    spare = tuple(i for i in range(1 << n) if i not in qa and i not in qb)[:4]
    assert len(spare) == 4
    return disjoint_k_pair(n, qa, spare) + disjoint_k_pair(n, spare, qb)


@lru_cache(maxsize=None)
def mixed(n, qa):
    """M_a X_[b,c] K_[a,b,c,d], a<b<c<d, the mixed charge-zero atom."""
    assert n >= 4 and len(qa) == 4 and tuple(sorted(set(qa))) == qa
    a, b, c, d = qa
    outside = [i for i in range(1 << n) if i not in qa]
    e, *rest = outside
    qb = tuple(rest[:4])
    q = disjoint_k_pair(n, qa, qb)
    s = sign_pair(n, a, e)
    # r4b: M_a X_bc K_A = K_A M_a K_A M_a.  The spare sign and
    # spare K commute with the relevant block and cancel from Q S Q S.
    return q + s + q + s


def adjacent_swap(p):
    c = gate('CX', p + 1, p)
    h = gate('HH', p, p + 1)
    return c + h + c + h + c


@lru_cache(maxsize=None)
def placed_primitive(n, kind, wires):
    if kind == 'X':
        return gate(kind, *wires)
    if kind == 'CX' and wires[0] == wires[1] + 1:
        return gate(kind, *wires)
    if kind == 'CCX' and set(wires[:-1]) == {wires[-1] + 1, wires[-1] + 2}:
        return gate('CCX', wires[-1] + 1, wires[-1] + 2, wires[-1])
    if kind == 'HH' and abs(wires[0] - wires[1]) == 1:
        return gate('HH', *sorted(wires))
    logical = (wires[-1],) + wires[:-1] if kind in ('CX', 'CCX') else wires
    labels, swaps = list(range(n)), []
    for slot, wanted in enumerate(logical):
        current = labels.index(wanted)
        while current > slot:
            p = current - 1
            labels[p], labels[p + 1] = labels[p + 1], labels[p]
            swaps.append(p)
            current -= 1
    route = tuple(g for p in swaps for g in adjacent_swap(p))
    base = {'CX': gate('CX', 1, 0), 'CCX': gate('CCX', 1, 2, 0), 'HH': gate('HH', 0, 1)}[kind]
    return route + base + inverse(route)


def to_adjacent(n, word):
    return tuple(g for kind, wires in word for g in placed_primitive(n, kind, wires))


def matrix(n, word):
    value = identity(n)
    for g in word:
        value = append_gate(value, g, n)
    return value


def expected(n, kind, indices):
    size = 1 << n
    entries = list(identity(n).entries)
    if kind == 'M':
        a, = indices
        entries[a * size + a] = -1
        return Matrix(0, tuple(entries))
    if kind == 'X':
        a, b = indices
        entries[a * size + a] = entries[b * size + b] = 0
        entries[a * size + b] = entries[b * size + a] = 1
        return Matrix(0, tuple(entries))
    entries = [2 * x for x in entries]
    for r, a in enumerate(indices):
        for c, b in enumerate(indices):
            entries[a * size + b] = -1 if (r & c).bit_count() % 2 else 1
    return Matrix(2, tuple(entries))


def multiply(n, a, b):
    size = 1 << n
    return canonical(a.exponent + b.exponent, tuple(
        sum(a.entries[r * size + k] * b.entries[k * size + c] for k in range(size))
        for r in range(size) for c in range(size)))


def audit(n):
    assert n >= 4
    size = 1 << n
    checks = 0

    def verify(label, word, target, adjacent=False):
        nonlocal checks
        assert matrix(n, word) == target, label
        if adjacent:
            expanded = to_adjacent(n, word)
            assert matrix(n, expanded) == target, ('adjacent', label)
        checks += 1
        print(f'PASS n={n} {label}: {len(word)} gates' +
              (f', {len(to_adjacent(n, word))} adjacent gates' if adjacent else ''))

    controls = tuple(range(n - 2))
    word = mcx(n, controls, n - 2)
    target = identity(n)
    # append_gate implements arbitrary controlled X for this exact check.
    target = append_gate(target, ('MCX', controls + (n - 2,)), n)
    verify('borrowed-bit MCX', word, target, True)
    for a, b, c in ((0, 1, 2), (1, 5, size - 1), (0, size - 2, size - 1)):
        target = multiply(n, expected(n, 'X', (a, c)), expected(n, 'X', (a, b)))
        verify(f'cycle({a},{b},{c})', three_cycle(n, a, b, c), target, a == 0)
    for a, b, c, d in ((0, 1, 2, 3), (1, size - 1, 5, 7), (0, 1, 1, 2)):
        target = multiply(n, expected(n, 'X', (a, b)), expected(n, 'X', (c, d)))
        verify(f'XX({a},{b};{c},{d})', double_exchange(n, a, b, c, d), target)
    for a, b in ((0, 1), (0, size - 1), (5, 7)):
        target = multiply(n, expected(n, 'M', (a,)), expected(n, 'M', (b,)))
        verify(f'MM({a},{b})', sign_pair(n, a, b), target, a == 0)
    for qa, qb in (((0, 1, 2, 3), (4, 5, 6, 7)),
                   ((1, 3, 5, 7), (0, 2, 4, 6)),
                   ((0, 1, 2, 3), (3, 4, 5, 6))):
        target = multiply(n, expected(n, 'K', qa), expected(n, 'K', qb))
        verify(f'KK{qa}{qb}', k_pair(n, qa, qb), target, qa == (1, 3, 5, 7))
    for qa in ((0, 1, 2, 3), (2, 5, 7, size - 1)):
        a, b, c, d = qa
        target = multiply(n, expected(n, 'M', (a,)),
                          multiply(n, expected(n, 'X', (b, c)), expected(n, 'K', qa)))
        verify(f'MXK{qa}', mixed(n, qa), target)
    print(f'PASS: {checks} fixed-width identities at n={n}; every matrix includes all {size} basis states.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--wires', type=int, default=4, choices=range(4, 9))
    args = parser.parse_args()
    audit(args.wires)

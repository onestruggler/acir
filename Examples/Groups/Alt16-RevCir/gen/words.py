"""Find the data of Syntactics.agda: the cycles as circuits and the gates
as words in the cycles.

Run: python3 words.py

1. Each cycle of three consecutive positions is a conjugate of K, the cycle
   of the positions 9, 10, 11, by NOT gates and swaps (the automorphisms of
   the 4-cube); the search lists the shortest conjugators.
2. Each of the six base gates (X, CX, CCX on the bottom wires and the three
   swaps) is a product of permutations of a few consecutive positions; a
   breadth-first search in the group that the cycles of those positions
   generate gives a shortest word for each factor.  For the swap of the
   wires 2 and 3, whose factors move twelve positions, a word is found that
   removes two inversions with every letter; a cycle changes the number of
   inversions by at most two, so no word is shorter.
"""
from collections import deque

from common import (N, GATES, K, IDENT, BASE, compose, omega, omega_inv,
                    word_perm, circ_perm, from_cycles, inversions)


# ----------------------------------------------------------------------
# The cycles as conjugates of K

def conjugators():
    auts = ['X0', 'X1', 'X2', 'X3', 'Ex0', 'Ex1', 'Ex2']
    words = {IDENT: []}
    queue = deque([IDENT])
    while queue:
        p = queue.popleft()
        for g in auts:
            q = compose(p, GATES[g])
            if q not in words:
                words[q] = words[p] + [g]
                queue.append(q)
    assert len(words) == 384
    for i in range(N - 2):
        cands = [w for w in words.values()
                 if circ_perm(w + K + w[::-1]) == omega(i)]
        cands.sort(key=lambda w: (len(w), w))
        print('  Omega %-2d = c K c^-1 for c =' % i,
              ' | '.join(' '.join(c) or '(empty)' for c in cands))


# ----------------------------------------------------------------------
# Shortest words in a window of consecutive positions

def shortest(target, lo, hi):
    """A shortest word over omega_lo .. omega_(hi-2) for target."""
    letters = [(i, omega(i)) for i in range(lo, hi - 1)]
    back = {IDENT: None}
    queue = deque([IDENT])
    while queue:
        p = queue.popleft()
        if p == target:
            word = []
            while back[p] is not None:
                i, p = back[p]
                word.append(i)
            return word[::-1]
        for i, g in letters:
            q = compose(p, g)
            if q not in back:
                back[q] = (i, p)
                queue.append(q)
    return None


def geodesic(target):
    """A word with one letter for every two inversions of target, found by
    peeling letters off its end; None if there is none."""
    dead = set()

    def go(p):
        if p == IDENT:
            return []
        if p in dead:
            return None
        c = inversions(p)
        for i in range(N - 2):
            q = compose(p, omega_inv(i))
            if inversions(q) == c - 2:
                r = go(q)
                if r is not None:
                    return r + [i]
        dead.add(p)
        return None
    return go(target)


def base_words():
    pieces = {
        'X0': [([(0, 1), (2, 3)], 0, 3), ([(4, 5), (6, 7)], 4, 7),
               ([(8, 9), (10, 11)], 8, 11), ([(12, 13), (14, 15)], 12, 15)],
        'CX0': [([(2, 3), (4, 5)], 2, 5), ([(10, 11), (12, 13)], 10, 13)],
        'CCX0': [([(4, 5), (10, 11)], 4, 11)],
        'Ex0': [([(1, 3), (4, 6)], 1, 6), ([(9, 11), (12, 14)], 9, 14)],
        'Ex1': [([(2, 6), (3, 7)], 2, 7), ([(8, 12), (9, 13)], 8, 13)],
    }
    found = {}
    for name, parts in pieces.items():
        word = []
        for cycles, lo, hi in parts:
            word += shortest(from_cycles(cycles), lo, hi)
        assert word_perm(word) == GATES[name]
        found[name] = word
    found['Ex2'] = geodesic(GATES['Ex2'])
    assert word_perm(found['Ex2']) == GATES['Ex2']
    assert 2 * len(found['Ex2']) == inversions(GATES['Ex2'])
    return found


if __name__ == '__main__':
    print('the cycles as conjugates of K:')
    conjugators()
    print('the base gates as words in the cycles:')
    found = base_words()
    for name, word in found.items():
        mark = '' if word == BASE[name] else '   (common.py has %s)' % BASE[name]
        print('  %-5s %2d letters:' % (name, len(word)), word, mark)

"""Lafont's 105 instances between the cycles, up to the symmetries of the
4-cube (NOT gates and swaps of wires).

Each instance is a relation between two or three cycles of three
consecutive states.  Conjugating by an automorphism of the cube (a word in
X and Ex) carries cycles of corners to cycles of corners, so instances in
one orbit follow from one another once the automorphisms are known to act
as they should.  This counts the orbits.

Run: python3 shapes.py
"""
from itertools import permutations, product

from common import ENC, bit


def automorphisms():
    for perm in permutations(range(4)):
        for mask in range(16):
            def h(s, perm=perm, mask=mask):
                t = 0
                for k in range(4):
                    t |= bit(s, k) << perm[k]
                return t ^ mask
            yield h


AUTS = list(automorphisms())


def corner(i):
    return (ENC[i], ENC[i + 1], ENC[i + 2])


def canon(corners):
    """The least image of a tuple of corners under the automorphisms."""
    return min(tuple(tuple(h(s) for s in c) for c in corners) for h in AUTS)


def main():
    kinds = {
        'order': [(i,) for i in range(14)],
        'near': [(i, i + 1) for i in range(13)],
        'far': [(i, i + 2, i + 1) for i in range(12)],
        'apart': [(i, j) for i in range(14) for j in range(i + 3, 14)],
    }
    total = 0
    for name, insts in kinds.items():
        orbits = {}
        for inst in insts:
            orbits.setdefault(canon([corner(i) for i in inst]), []).append(inst)
        total += len(orbits)
        print('%-6s %3d instances, %2d shapes' % (name, len(insts), len(orbits)))
        for reps in orbits.values():
            print('    ', reps[0], 'x%d' % len(reps))
    print('shapes in all:', total)


if __name__ == '__main__':
    main()

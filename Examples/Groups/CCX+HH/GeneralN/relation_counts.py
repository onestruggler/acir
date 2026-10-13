#!/usr/bin/env python3
"""Count the unsimplified Clément relation families without expanding them.

Counts identify axiom shapes and legal level-index tuples.  Proof witnesses
for distinctness are not counted separately.  Both orientations of the
source commutation schemas are retained, as in the Agda source relation.
These counts measure the present construction, not a minimal presentation.
"""

import argparse
from math import comb


def choose(n, k):
    return comb(n, k) if n >= k else 0


def table1(n):
    # Group the exact Table 1 constructors by the number of distinct levels.
    return (n + 4 * choose(n, 2) + 5 * choose(n, 3)
            + 10 * choose(n, 4) + 9 * choose(n, 5)
            + 16 * choose(n, 6) + 71 * choose(n, 8))


def counts(wires):
    assert wires >= 4
    levels = 2 ** wires
    source_generators = levels + choose(levels, 2) + choose(levels, 4)
    source_relations = table1(levels)
    # Four states, one roundtrip per formal Schreier edge, then one
    # physical circuit recovery equation per adjacent gate generator.
    hh = 4 * (source_relations + source_generators) + 4 * wires - 4
    # Table 2 adds IH and N+2 relations; H has one more physical generator.
    h = 4 * (source_relations + levels + 2 + source_generators + 1) + 4 * wires - 3
    return levels, source_generators, source_relations, hh, h


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--wires', type=int, default=4)
    args = parser.parse_args()
    if args.wires < 4:
        parser.error('the four-state translation applies at widths at least four')
    assert [table1(n) for n in (2, 4, 8)] == [6, 58, 2123]
    levels, generators, relations, hh, h = counts(args.wires)
    print(f'Width {args.wires}; {levels:,} basis levels')
    print(f'Table 1: {generators:,} generators and {relations:,} indexed equations')
    print(f'CCX+HH: {hh:,} circuit equations before removing redundancies')
    print(f'CCX+H:  {h:,} circuit equations before removing redundancies')


if __name__ == '__main__':
    main()

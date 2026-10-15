"""Search all the level-0 lemmas, in rounds, and write derivations.json.

The C++ search (fbfs) must be compiled first: g++ -O2 -std=c++17 -o fbfs fbfs.cpp.
Lemmas already in derivations.json are replayed, not searched again.
"""
import sys
from targets import *
from rounds import Pool

pool = Pool(R0, TK)
pool.fast = 20
for (n, u, v) in boot:
    assert pool.try_one(n, u, v, (2, 4, 6, 8, 10), 2_000_000, verbose=False), n
pool.start_rotating()
assert not pool.rounds(A + table)
print('stage2 replayed', flush=True)
left = pool.rounds(comm + Tf + t3 + orders + mid + reach,
                   budgets=((2, 4), 100_000), more=(((2, 4, 6), 1_000_000), ((2, 4, 6, 8), 4_000_000)))
print('left', [t[0] for t in left], flush=True)
pool.write()

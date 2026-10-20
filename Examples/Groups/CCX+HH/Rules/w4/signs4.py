#!/usr/bin/env python3
"""The sign relations for completeness of the signed permutations V_Z on
four wires, by the finder of ../wn/finder.py (rules at every placement,
with R4).

V_Z is the even signs E (2¹⁵) times A₁₆.  As a semidirect product it is
presented by A₁₆, one sign pair s = M_0 M_1 and: s² = ε; s commutes
with the setwise stabiliser of {0, 1} (the 24 letters fixing 0 and 1,
and X0); the triangle M_0 M_1 · M_1 M_2 = M_0 M_2; and two sign pairs
on disjoint levels commute.  Here every sign pair M_a M_b is s
conjugated by a classical word sending 0, 1 to a, b, the shortest one
found by breadth-first search.

    python3 -B signs4.py [limit]
"""
import sys
import time
from collections import deque
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'wn'))
import finder as F

S = 'X1 X2 X3 HH03 CCX3;12 HH03 X1 X2 X3'


def routes(A):
    """For each ordered pair (a, b), a shortest classical word whose
    permutation sends 0 to a and 1 to b."""
    cls = [g for g, l in enumerate(A.LETTERS) if l[0] != 'HH']
    best = {(0, 1): ()}
    q = deque([((0, 1), ())])
    seen = {(0, 1)}
    while q and len(best) < A.D * (A.D - 1):
        (a, b), w = q.popleft()
        for g in cls:
            p = A.PERMS[g]
            nab = (p[a], p[b])
            if nab not in seen:
                seen.add(nab)
                best[nab] = (g,) + w        # g after w
                q.append((nab, (g,) + w))
    return best


def sign_pair(A, R, a, b):
    s = A.word(S)
    w = R[(a, b)]
    return w + s + tuple(reversed(w))


def main():
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 30_000
    A = F.Alphabet(4, r4=True, placed=True)
    R = routes(A)
    s = A.word(S)
    targets = {
        's squared': s + s,
        'triangle M0M1 M1M2 = M0M2': sign_pair(A, R, 0, 1) + sign_pair(A, R, 1, 2) + sign_pair(A, R, 0, 2),
        'triangle M0M1 M1M3 = M0M3': sign_pair(A, R, 0, 1) + sign_pair(A, R, 1, 3) + sign_pair(A, R, 0, 3),
        'disjoint M0M1, M2M3 commute': (sign_pair(A, R, 0, 1) + sign_pair(A, R, 2, 3)) * 2,
        'disjoint M0M1, M4M8 commute': (sign_pair(A, R, 0, 1) + sign_pair(A, R, 4, 8)) * 2,
    }
    for name, t in targets.items():
        assert A.is_identity(t), name
        t0 = time.time()
        res = A.derive(t, limit)
        print(f'{len(t):3} letters: {"derived" if res else "NOT derived"} {round(time.time() - t0, 1)} s   {name}',
              flush=True)


if __name__ == '__main__':
    main()

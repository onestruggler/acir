"""Numerical check of the (339) frame plan (N >= 6)."""
import sys, itertools
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from mc import *

def col(d, lo, N, f):  # controls dict d plus colOn lo N f
    return lambda j: d[j] if j in d else (bool(f(j)) if lo <= j < N else None)

N = 6
ok = True
for c1, c2, c3 in itertools.product([False, True], repeat=3):
  for xs in itertools.product([False, True], repeat=N - 4):
    for ys in itertools.product([False, True], repeat=N - 4):
      x = lambda j: xs[j - 4]; y = lambda j: ys[j - 4]
      A = mc(N, 'box', [0], col({1: c2, 2: True, 3: c1}, 4, N, x))
      B = mc(N, 'hg', [1, 3], col({0: c3, 2: False}, 4, N, y))
      E = mc(N, 'box', [0], col({1: c3, 2: False, 3: True}, 4, N, y))
      P = drawn(ppAt(N, 1, 3), swAt(N, 0))
      Pr = drawn(swAt(N, 0), ppAt(N, 1, 3))
      # (a) B = P' E P (drawn: P first, then E, then P')
      if not eq(N, B, drawn(P, E, Pr)) and not eq(N, B, drawn(Pr, E, P)):
          print('(a) fails', c1, c2, c3, xs, ys); ok = False
      # commutation of A and B
      if not eq(N, drawn(A, B), drawn(B, A)): print('AB fails'); ok = False
      # (d) E_rem conj = box[1](0:c3, 2:o, bulk) idle 3
      Erem = mc(N, 'box', [0], col({1: c3, 2: False}, 4, N, y))
      R1 = mc(N, 'box', [1], col({0: c3, 2: False}, 4, N, y))
      if not (eq(N, drawn(P, Erem, Pr), R1) or eq(N, drawn(Pr, Erem, P), R1)):
          print('(d) fails'); ok = False
print('which orientation:', eq(N, B, drawn(swAt(N,0), ppAt(N,1,3), E, ppAt(N,1,3), swAt(N,0))) if False else '')
print('ok' if ok else 'FAIL')

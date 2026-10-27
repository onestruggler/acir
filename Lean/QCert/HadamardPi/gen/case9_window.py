# The square of Main Case 9 in dimension 9 that no word on the four odd entries closes:
# all states reachable from t below s, by words on the window {0,1,3,5}; q is not among them.
import itertools
from collections import deque
from zr import *
col = [(1, 3), (1, 0), (0, -3), (1, 3), (2, 0), (5, 0), (-2, 1), (-4, 2), (-2, -2)]
k = 7
assert norm_ok(col, k)
W = [0, 1, 3, 5]
L = [('H', i, j) for i, j in itertools.combinations(W, 2)] + [('X', i, j) for i, j in itertools.combinations(W, 2)] + [('Z', i) for i in W]
def ok_state(c): return sum(1 for e in c if odd(e)) < 4
t = tuple(act(('H', 0, 3), col)); r = act(('H', 0, 1), col)
print("r", r, "odd", [i for i in range(9) if odd(r[i])], [cls(r[i]) for i in range(9)])
q = tuple(act(('H', 0, 3), r))
seen = {t}; dq = deque([t])
while dq:
    S = dq.popleft()
    for l in L:
        S2 = act(l, list(S))
        if S2 is None: continue
        S2 = tuple(S2)
        if S2 in seen or not ok_state(S2): continue
        seen.add(S2); dq.append(S2)
print(len(seen), q in seen)

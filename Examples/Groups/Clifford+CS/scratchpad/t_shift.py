# The shortest K-free words w over the letters on the pairs (c, c+1) and
# (c+1, c+2) with w k_c = k_{c+1} w (matrices, written order).
import sys, itertools
sys.argv = ['thyb', '8']
import thyb as T
c = 2
lets = {'p0': T.p(c), "q0": T.pq(c), 'l0': T.l(c), 'h0': T.h(c),
        'p1': T.p(c + 1), 'q1': T.pq(c + 1), 'l1': T.l(c + 1), 'h1': T.h(c + 1)}
K0, K1 = T.k(c), T.k(c + 1)
found = []
for n in range(1, 5):
    for w in itertools.product(lets, repeat=n):
        W = T.word(*[lets[x] for x in w])
        if T.close(T.mul(W, K0), T.mul(K1, W)): found.append(w)
    if found: break
print(found[:20])
# also: words with k_{c+1} w = w k_c (the other orientation)
found2 = []
for n in range(1, 5):
    for w in itertools.product(lets, repeat=n):
        W = T.word(*[lets[x] for x in w])
        if T.close(T.mul(K1, W), T.mul(W, K0)): found2.append(w)
    if found2: break
print(found2[:5])

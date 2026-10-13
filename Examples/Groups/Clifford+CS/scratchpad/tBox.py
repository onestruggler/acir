# The box recursion for the iZ-box: is Lambda^3(iZ) = W . B . V . B
# with W a 3-wire gate and B the smaller box re-placed, as Clement's
# Definition 2.4?  Everything is a phased permutation: represent an
# operator as (perm, phase) with phase in Z/4 (units i^k), compose
# exactly, and search placements and W-candidates at width 4.
from itertools import permutations, product

n = 4
N = 2 ** n

class Mono:
    __slots__ = ('p', 'f')
    def __init__(self, p, f):
        self.p = tuple(p); self.f = tuple(f)   # column x -> i^f[x] |p[x]>
    def __mul__(self, o):                      # self . o  (o acts first)
        return Mono([self.p[o.p[x]] for x in range(N)],
                    [(o.f[x] + self.f[o.p[x]]) % 4 for x in range(N)])
    def inv(self):
        q = [0] * N; g = [0] * N
        for x in range(N):
            q[self.p[x]] = x; g[self.p[x]] = (-self.f[x]) % 4
        return Mono(q, g)
    def __eq__(self, o): return self.p == o.p and self.f == o.f
    def __hash__(self): return hash((self.p, self.f))

I = Mono(range(N), [0] * N)

def ctrl_gate(t, controls, kind):
    # kind 'iZ': on the block controls-all-1: i^(1-2 x_t) ; 'A' = iZX:
    # flip x_t with phase i(-1)^(1 - x_t after flip)... column action:
    # A|b> = i (-1)^(1-b) |1-b>  i.e. phase i^(1 + 2(1-b)).
    p = list(range(N)); f = [0] * N
    for x in range(N):
        if all((x >> c) & 1 for c in controls):
            b = (x >> t) & 1
            if kind == 'iZ':
                f[x] = (1 + 2 * b) % 4          # i, -i
            elif kind == 'A':                    # iZX
                p[x] = x ^ (1 << t)
                f[x] = (1 + 2 * (1 - b)) % 4     # |b> -> i(-1)^(1-b)|1-b>
            elif kind == 'X':
                p[x] = x ^ (1 << t)
            elif kind == 'Z':
                f[x] = (2 * b) % 4
            elif kind == 'ZX':                   # X then Z
                p[x] = x ^ (1 << t)
                f[x] = (2 * (1 - b)) % 4
            elif kind == 'iXZ':                  # Z then X, times i
                p[x] = x ^ (1 << t)
                f[x] = (1 + 2 * b) % 4
    return Mono(p, f)

target = ctrl_gate(0, (1, 2, 3), 'iZ')          # Lambda^3(iZ)

# B: the smaller box CC(iZ) with target wire tb and controls cb
# W: a 3-wire doubly controlled letter of kind kw, target tw controls cw
found = []
wires = range(n)
for kw in ('A', 'iXZ', 'ZX', 'X'):
    for tw in wires:
        for cw in permutations([w for w in wires if w != tw], 2):
            if cw[0] > cw[1]: continue
            W = ctrl_gate(tw, cw, kw)
            Wi = W.inv()
            for tb in wires:
                for cb in permutations([w for w in wires if w != tb], 2):
                    if cb[0] > cb[1]: continue
                    B = ctrl_gate(tb, cb, 'iZ')
                    for w1, w2 in ((W, Wi), (Wi, W), (W, W)):
                        if w1 * B * w2 * B == target:
                            found.append((kw, tw, cw, tb, cb,
                                          'W,Wi' if w2 is Wi and w1 is W else
                                          ('Wi,W' if w1 is Wi else 'W,W')))
for f in found[:12]:
    print(f)
print(len(found), 'solutions')

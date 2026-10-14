"""The two-level presentation of Uₙ(ℤ[½,i]) (Examples.Groups.Clifford+CS-
TwoLevel, Bian and Selinger) in dimensions 2 and 4, decoded into CliffCS₂
on one and two wires: its generators ω... i_[a] (i at index a), X_[a,b]
and K_[a,b] = ω̄ H on the indices a, b, and the instances of its
relations (1)–(19) with distinct indices, in the order written (their
matrices being symmetric).  Index a of dimension 4 is 2 x₀ + x₁, wire 0
the high bit.

On one wire: i_[1] = S, i_[0] = ω² S†, X_[0,1] = X, K_[0,1] = ω⁷ H.
On two: i_[a] is CS with its controls negated where a has a 0; X_[a,b]
a CNOT, the swap, or X ⊗ X around the swap; K_[a,b] a controlled K
(CS K CS K CS S† ω², on the target) with its control negated, or
conjugated by a CNOT when a and b differ in both bits."""
import itertools

# dimension 2
D1 = {('i', 0): 'w w Sd0', ('i', 1): 'S0', ('X', 0, 1): 'X0', ('K', 0, 1): 'wd H0'}


def CK(c, t):
    """Controlled K, control c, target t (adjacent), in time order."""
    cs = 'CS%d%d' % (max(c, t), min(c, t))
    k = 'wd H%d' % t
    return ' '.join([cs, k, cs, k, cs, 'Sd%d' % c, 'w w'])


D2 = {('i', 3): 'CS10', ('i', 2): 'X1 CS10 X1', ('i', 1): 'X0 CS10 X0',
      ('i', 0): 'X0 X1 CS10 X1 X0',
      ('X', 2, 3): 'CX01', ('X', 0, 1): 'X0 CX01 X0', ('X', 1, 3): 'CX10',
      ('X', 0, 2): 'X1 CX10 X1', ('X', 1, 2): 'SW01', ('X', 0, 3): 'X0 X1 SW01',
      ('K', 2, 3): CK(0, 1), ('K', 0, 1): 'X0 %s X0' % CK(0, 1), ('K', 1, 3): CK(1, 0),
      ('K', 0, 2): 'X1 %s X1' % CK(1, 0), ('K', 1, 2): 'CX01 %s CX01' % CK(1, 0),
      ('K', 0, 3): 'CX10 X0 %s X0 CX10' % CK(0, 1)}


def gens(n):
    out = [('i', a) for a in range(n)]
    for a, b in itertools.combinations(range(n), 2):
        out += [('X', a, b), ('K', a, b)]
    return out


def i(j): return [('i', j)]
def X(j, k): return [('X', j, k)]
def K(j, k): return [('K', j, k)]


def relations(n):
    """(name, lhs, rhs) for every instance with distinct indices, a < b
    wherever X_[a,b] or K_[a,b] occurs, as in Syntactics."""
    R = range(n)
    out = []
    for j in R:
        out.append(('order-i-%d' % j, i(j) * 4, []))
    for j, k in itertools.combinations(R, 2):
        out.append(('order-X-%d%d' % (j, k), X(j, k) * 2, []))
        out.append(('order-K-%d%d' % (j, k), K(j, k) * 8, []))
    for j, k in itertools.permutations(R, 2):
        out.append(('comm-ii-%d%d' % (j, k), i(j) + i(k), i(k) + i(j)))
    for j in R:
        for k, l in itertools.combinations(R, 2):
            if j not in (k, l):
                out.append(('comm-iX-%d%d%d' % (j, k, l), i(j) + X(k, l), X(k, l) + i(j)))
                out.append(('comm-iK-%d%d%d' % (j, k, l), i(j) + K(k, l), K(k, l) + i(j)))
    for (j, k), (l, m) in itertools.product(itertools.combinations(R, 2), repeat=2):
        if len({j, k, l, m}) == 4:
            out.append(('comm-XX-%d%d%d%d' % (j, k, l, m), X(j, k) + X(l, m), X(l, m) + X(j, k)))
            out.append(('comm-XK-%d%d%d%d' % (j, k, l, m), X(j, k) + K(l, m), K(l, m) + X(j, k)))
            out.append(('comm-KK-%d%d%d%d' % (j, k, l, m), K(j, k) + K(l, m), K(l, m) + K(j, k)))
    for j, k in itertools.combinations(R, 2):
        out.append(('swap-iX-%d%d' % (j, k), i(k) + X(j, k), X(j, k) + i(j)))
    for j, k, l in itertools.combinations(R, 3):
        out.append(('swap-XX-%d%d%d' % (j, k, l), X(k, l) + X(j, k), X(j, k) + X(j, l)))
        out.append(('swap-XX′-%d%d%d' % (j, k, l), X(j, l) + X(k, l), X(k, l) + X(j, k)))
        out.append(('swap-KX-%d%d%d' % (j, k, l), K(k, l) + X(j, k), X(j, k) + K(j, l)))
        out.append(('swap-KX′-%d%d%d' % (j, k, l), K(j, l) + X(k, l), X(k, l) + K(j, k)))
    for j, k in itertools.combinations(R, 2):
        out.append(('rel-13-%d%d' % (j, k), K(j, k) + i(k) * 2, X(j, k) + K(j, k)))
        out.append(('rel-14-%d%d' % (j, k), K(j, k) + i(k) * 3, i(k) + K(j, k) + i(k) + K(j, k)))
        out.append(('rel-15-%d%d' % (j, k), K(j, k) + i(j) + i(k), i(j) + i(k) + K(j, k)))
        out.append(('rel-16-%d%d' % (j, k), K(j, k) * 2 + i(j) + i(k), []))
    for j, k, l, m in itertools.permutations(R, 4):
        if j < k and l < m and j < l and k < m and k != l:
            out.append(('rel-17-%d%d%d%d' % (j, k, l, m),
                        K(j, k) + K(l, m) + K(j, l) + K(k, m),
                        K(j, l) + K(k, m) + K(j, k) + K(l, m)))
    return out


def decode(table, word):
    return ' '.join(table[g] for g in word)


if __name__ == '__main__':
    import sys
    sys.stdout.reconfigure(encoding='utf-8')
    import cmath
    import cscliff
    from circ import parse, unitary
    W = cmath.exp(1j * cmath.pi / 4)
    cg = (1 - 1j) / 2

    def two_level(g, n):
        M = [[1 + 0j if r == c else 0j for c in range(n)] for r in range(n)]
        if g[0] == 'i':
            M[g[1]][g[1]] = 1j
        elif g[0] == 'X':
            a, b = g[1], g[2]
            M[a][a] = M[b][b] = 0
            M[a][b] = M[b][a] = 1
        else:
            a, b = g[1], g[2]
            M[a][a], M[a][b], M[b][a], M[b][b] = cg, cg, cg, -cg
        return M

    def index(x, w):
        # circ numbers wire k as bit k; the two-level index has wire 0 high
        return sum(((x >> k) & 1) << (w - 1 - k) for k in range(w))

    for n, w, table in [(2, 1, D1), (4, 2, D2)]:
        for g in gens(n):
            U = unitary(parse(table[g]), w)
            T = two_level(g, n)
            ok = all(abs(U[x][y] - T[index(x, w)][index(y, w)]) < 1e-9
                     for x in range(n) for y in range(n))
            print(n, g, ok)
        rs = relations(n)
        print(n, len(rs), 'instances')

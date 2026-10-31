"""Figure 2 of Bian–Selinger as lists of equations (name, lhs, rhs) over letter names, in the
order of `Syntax.lean`'s constructors, checked on matrices.

`rels3()`: the relations on three qubits (`Rel`); `rels2()`: the fragment (a)-(c) and the
commutations on a pair of qubits u, l (`Two.Rel2`)."""
from qc import mat3, mat2, eq


def X3(q): return ['K%d' % q, 'S%d' % q, 'S%d' % q, 'K%d' % q, 'i']
def CX3(cs, t): return ['K%d' % t, cs, cs, 'K%d' % t, 'i']


CX01 = CX3('C01', 1)
CX10 = CX3('C01', 0)
CX12 = CX3('C12', 2)
CX21 = CX3('C12', 1)


def rels3():
    R = []
    R.append(('c1', ['i'] * 4, []))
    for q in range(3):
        R.append(('c2_%d' % q, ['K%d' % q] * 2, ['i'] * 3))
    for q in range(3):
        R.append(('c3_%d' % q, ['S%d' % q] * 4, []))
    for q in range(3):
        R.append(('c4_%d' % q, ['S%d' % q, 'K%d' % q] * 3, ['i'] * 3))
    css = ['C01', 'C12']
    for j in range(2):
        R.append(('c5_%d' % j, [css[j]] * 4, []))
    for j in range(2):
        u = j
        R.append(('c6_%d' % j, ['S%d' % u, css[j]], [css[j], 'S%d' % u]))
    for j in range(2):
        l = j + 1
        R.append(('c7_%d' % j, ['S%d' % l, css[j]], [css[j], 'S%d' % l]))
    for j in range(2):
        u, l = j, j + 1
        R.append(('c8_%d' % j, X3(u) + [css[j]], [css[j]] * 3 + X3(u) + ['S%d' % l]))
    for j in range(2):
        u, l = j, j + 1
        R.append(('c9_%d' % j, X3(l) + [css[j]], [css[j]] * 3 + X3(l) + ['S%d' % u]))
    for j in range(2):
        q = j
        S, K, c = 'S%d' % q, 'K%d' % q, css[j]
        R.append(('c10_%d' % j, [S, K, c, K, c], [c, K, c, K, S]))
    for j in range(2):
        q = j + 1
        S, K, c = 'S%d' % q, 'K%d' % q, css[j]
        R.append(('c11_%d' % j, [S, K, c, K, c], [c, K, c, K, S]))
    R.append(('c12', ['C12', 'C01'], ['C01', 'C12']))
    R.append(('c13', CX10 + CX01 + ['C12'] + CX01 + CX10, CX12 + CX21 + ['C01'] + CX21 + CX12))
    R.append(('c14', ['C12'] + CX01 + ['C12'] * 3 + CX01, ['C01'] + CX21 + ['C01'] * 3 + CX21))
    R.append(('c15', CX10 + CX01 + ['C12'] * 2 + CX01 + CX10, CX01 + ['C12'] * 2 + CX01 + ['C12'] * 2))
    R.append(('c16', 'C12 K1 C12 K1 C01 K1 C01'.split(), 'C01 K1 C01 K1 C12 K1 C12'.split()))
    R.append(('c17', 'C12 K1 C12 C12 C12 K1 C01 K1 C12'.split(),
              'C01 K1 C01 C01 C01 K1 C12 K1 C01'.split()))
    gens = ['i', 'K0', 'K1', 'K2', 'S0', 'S1', 'S2', 'C01', 'C12']
    for A in gens[1:]:
        R.append(('comm_i_' + A, ['i', A], [A, 'i']))
    loc = {('K', 0): 'K0', ('K', 1): 'K1', ('K', 2): 'K2', ('S', 0): 'S0', ('S', 1): 'S1', ('S', 2): 'S2'}
    for A in 'KS':
        for B in 'KS':
            for q in range(3):
                for r in range(q + 1, 3):
                    R.append(('comm_loc_%s%s%d%d' % (A, B, q, r), [loc[(A, q)], loc[(B, r)]],
                              [loc[(B, r)], loc[(A, q)]]))
    for A in 'KS':
        R.append(('comm_0_12_' + A, [loc[(A, 0)], 'C12'], ['C12', loc[(A, 0)]]))
    for A in 'KS':
        R.append(('comm_2_01_' + A, [loc[(A, 2)], 'C01'], ['C01', loc[(A, 2)]]))
    for nm, l, r in R:
        assert eq(mat3(l), mat3(r)), nm
    return R


def X2(q): return ['K' + q, 'S' + q, 'S' + q, 'K' + q, 'i']


def rels2():
    R = []
    R.append(('c1', ['i'] * 4, []))
    for q in 'ul':
        R.append(('c2' + q, ['K' + q] * 2, ['i'] * 3))
    for q in 'ul':
        R.append(('c3' + q, ['S' + q] * 4, []))
    for q in 'ul':
        R.append(('c4' + q, ['S' + q, 'K' + q] * 3, ['i'] * 3))
    R.append(('c5', ['CS'] * 4, []))
    R.append(('c6', ['Su', 'CS'], ['CS', 'Su']))
    R.append(('c7', ['Sl', 'CS'], ['CS', 'Sl']))
    R.append(('c8', X2('u') + ['CS'], ['CS'] * 3 + X2('u') + ['Sl']))
    R.append(('c9', X2('l') + ['CS'], ['CS'] * 3 + X2('l') + ['Su']))
    R.append(('c10', 'Su Ku CS Ku CS'.split(), 'CS Ku CS Ku Su'.split()))
    R.append(('c11', 'Sl Kl CS Kl CS'.split(), 'CS Kl CS Kl Sl'.split()))
    for A in ['Ku', 'Kl', 'Su', 'Sl', 'CS']:
        R.append(('comm_i_' + A, ['i', A], [A, 'i']))
    for a in ['Ku', 'Su']:
        for b in ['Kl', 'Sl']:
            R.append(('comm_%s_%s' % (a, b), [a, b], [b, a]))
    for nm, l, r in R:
        assert eq(mat2(l), mat2(r)), nm
    return R


if __name__ == '__main__':
    print(len(rels3()), len(rels2()))

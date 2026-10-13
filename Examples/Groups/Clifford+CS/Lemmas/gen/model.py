"""The two-qubit model behind Lemmas.TwoWire and Lemmas.TwoWireMacro:
the alphabets, their numeric semantics, the decoding of the two-level
generators, the 118 instances of the two-level relations on four
indices, and the equations each stage of the pipeline proves.

Conventions are those of Examples/Groups/Clifford+CS: wire 0 is the most
significant bit of a basis index, a word denotes the product of its
letters' matrices in the order written, K = (1+i)⁻¹ [[1,1],[1,-1]].

Alphabets:
  base   I s k t l C   the scalar i, S and K on wire 0, S and K on wire 1, CS
  tier C I s k t l z   the same with z = CS² (CZ) in place of CS
  macro  I s t C x y a b p q k l
         x = X, y = X on wire 1, a = CX₀₁ (control 0), b = CX₁₀,
         p = CK₀₁ = K_[2,3], q = CK₁₀ = K_[1,3], k l = K on wire 0, 1
"""
import itertools
import re

import numpy as np

# ----------------------------------------------------------------------
# Base letters and their matrices

cg = 1 / (1 + 1j)
S1q = np.diag([1, 1j])
K1q = cg * np.array([[1, 1], [1, -1]])
I2 = np.eye(2)

BASE = 'IsktlC'
MATRIX = {
    'I': 1j * np.eye(4),
    's': np.kron(S1q, I2), 'k': np.kron(K1q, I2),
    't': np.kron(I2, S1q), 'l': np.kron(I2, K1q),
    'C': np.diag([1, 1, 1, 1j]),
}


def sem(w):
    """The matrix of a base word."""
    A = np.eye(4, dtype=complex)
    for a in w:
        A = A @ MATRIX[a]
    return A


MIRROR = str.maketrans('sktl', 'tlsk')


def mirror(w):
    """Exchange the wires (the rules are symmetric under it)."""
    return w.translate(MIRROR)


# The rules of Syntactics on two wires, wire 1's scalar read as the scalar.
def base_axioms():
    return [
        ('order-I', 'IIII', ''),
        ('order-S0', 'ssss', ''), ('order-K0', 'kk', 'III'), ('order-SK0', 'sksksk', 'III'),
        ('order-S1', 'tttt', ''), ('order-K1', 'll', 'III'), ('order-SK1', 'tltltl', 'III'),
        ('comm-IS0', 'sI', 'Is'), ('comm-IK0', 'kI', 'Ik'),
        ('comm-IS1', 'tI', 'It'), ('comm-IK1', 'lI', 'Il'), ('comm-IC', 'CI', 'IC'),
        ('comm-ts', 'ts', 'st'), ('comm-lk', 'lk', 'kl'), ('comm-tk', 'tk', 'kt'), ('comm-ls', 'ls', 'sl'),
        ('order-CS', 'CCCC', ''), ('comm-CS-S0', 'Cs', 'sC'), ('comm-CS-S1', 'Ct', 'tC'),
        ('X-CS0', 'ksskIC', 'CCCksskIt'), ('X-CS1', 'lttlIC', 'CCClttlIs'),
        ('CS-K0', 'CkCks', 'skCkC'), ('CS-K1', 'ClClt', 'tlClC'),
    ]


# ----------------------------------------------------------------------
# Tier C: the two-qubit Clifford group, z = CZ

CLIFF = 'Isktlz'


def cliff_expand(w):
    return w.replace('z', 'CC')


def cliff_axioms():
    """Selinger's C1–C11, read with H = ω K and CZ = CS²."""
    return [
        ('order-I', 'IIII', ''),
        ('order-S0', 'ssss', ''), ('order-K0', 'kk', 'III'), ('order-SK0', 'sksksk', 'III'),
        ('order-S1', 'tttt', ''), ('order-K1', 'll', 'III'), ('order-SK1', 'tltltl', 'III'),
        ('comm-IS0', 'sI', 'Is'), ('comm-IK0', 'kI', 'Ik'),
        ('comm-IS1', 'tI', 'It'), ('comm-IK1', 'lI', 'Il'), ('comm-Iz', 'zI', 'Iz'),
        ('comm-ts', 'ts', 'st'), ('comm-lk', 'lk', 'kl'), ('comm-tk', 'tk', 'kt'), ('comm-ls', 'ls', 'sl'),
        ('z2', 'zz', ''), ('z-s', 'zs', 'sz'), ('z-t', 'zt', 'tz'),
        ('C8', 'zlttl', 'lttlssz'), ('C9', 'zkssk', 'ksskttz'),
        ('C10', 'zlz', 'tltszlt'), ('C11', 'zkz', 'skstzks'),
    ]


def to_cliff(w):
    """A base word in tier-C letters (C C ↦ z), or None if a C is unpaired."""
    out = []
    for m in re.finditer(r'C+|[^C]', w):
        g = m.group(0)
        if g[0] == 'C':
            if len(g) % 2:
                return None
            out.append('z' * (len(g) // 2))
        else:
            out.append(g)
    return ''.join(out)


# ----------------------------------------------------------------------
# Macro letters, and the decoding

X0, X1 = 'ksskI', 'lttlI'
CX01, CX10 = 'lCClI', 'kCCkI'
CK01, CK10 = 'ClClCsssI', 'CkCkCtttI'

MACRO = 'IstCxyabpqkl'
EXP = {'I': 'I', 's': 's', 't': 't', 'C': 'C', 'x': X0, 'y': X1, 'a': CX01, 'b': CX10,
       'p': CK01, 'q': CK10, 'k': 'k', 'l': 'l'}


def expand(w):
    return ''.join(EXP[c] for c in w)


def msem(w):
    return sem(expand(w))


# TwoQubit.d, letter for letter.
D = {
    ('i', 3): 'C', ('i', 2): 'yCy', ('i', 1): 'xCx', ('i', 0): 'xyCxy',
    ('X', 2, 3): 'a', ('X', 0, 1): 'xax', ('X', 1, 3): 'b', ('X', 0, 2): 'yby',
    ('X', 1, 2): 'aba', ('X', 0, 3): 'abaxy',
    ('K', 2, 3): 'p', ('K', 0, 1): 'xpx', ('K', 1, 3): 'q', ('K', 0, 2): 'yqy',
    ('K', 1, 2): 'aqa', ('K', 0, 3): 'bxpxb',
}


def i(a): return D[('i', a)]
def X(a, b): return D[('X', min(a, b), max(a, b))]
def K(a, b): return D[('K', a, b)]


def relations():
    """(name, lhs, rhs): every instance of Bian and Selinger's Figure 1
    on four indices, decoded, in the words of the relations."""
    R = []
    idx = range(4)
    for j in idx:
        R.append(('order-i %d' % j, i(j) * 4, ''))
    for j, k in itertools.combinations(idx, 2):
        R.append(('order-X %d%d' % (j, k), X(j, k) * 2, ''))
        R.append(('order-K %d%d' % (j, k), K(j, k) * 8, ''))
        R.append(('swap-iX %d%d' % (j, k), i(k) + X(j, k), X(j, k) + i(j)))
        R.append(('rel-13 %d%d' % (j, k), K(j, k) + i(k) * 2, X(j, k) + K(j, k)))
        R.append(('rel-14 %d%d' % (j, k), K(j, k) + i(k) * 3, i(k) + K(j, k) + i(k) + K(j, k)))
        R.append(('rel-15 %d%d' % (j, k), K(j, k) + i(j) + i(k), i(j) + i(k) + K(j, k)))
        R.append(('rel-16 %d%d' % (j, k), K(j, k) * 2 + i(j) + i(k), ''))
    for j, k in itertools.permutations(idx, 2):
        R.append(('comm-ii %d%d' % (j, k), i(j) + i(k), i(k) + i(j)))
    for j in idx:
        for k, l in itertools.combinations(idx, 2):
            if j not in (k, l):
                R.append(('comm-iX %d%d%d' % (j, k, l), i(j) + X(k, l), X(k, l) + i(j)))
                R.append(('comm-iK %d%d%d' % (j, k, l), i(j) + K(k, l), K(k, l) + i(j)))
    for (j, k), (l, m) in itertools.permutations(list(itertools.combinations(idx, 2)), 2):
        if len({j, k, l, m}) == 4:
            R.append(('comm-XX %d%d%d%d' % (j, k, l, m), X(j, k) + X(l, m), X(l, m) + X(j, k)))
            R.append(('comm-XK %d%d%d%d' % (j, k, l, m), X(j, k) + K(l, m), K(l, m) + X(j, k)))
            R.append(('comm-KK %d%d%d%d' % (j, k, l, m), K(j, k) + K(l, m), K(l, m) + K(j, k)))
    for j, k, l in itertools.combinations(idx, 3):
        R.append(('swap-XX %d%d%d' % (j, k, l), X(k, l) + X(j, k), X(j, k) + X(j, l)))
        R.append(("swap-XX' %d%d%d" % (j, k, l), X(j, l) + X(k, l), X(k, l) + X(j, k)))
        R.append(('swap-KX %d%d%d' % (j, k, l), K(k, l) + X(j, k), X(j, k) + K(j, l)))
        R.append(("swap-KX' %d%d%d" % (j, k, l), K(j, l) + X(k, l), X(k, l) + K(j, k)))
    for j, k, l, m in itertools.permutations(idx, 4):
        if j < k and l < m and j < l and k < m and k != l:
            R.append(('rel-17 %d%d%d%d' % (j, k, l, m),
                      K(j, k) + K(l, m) + K(j, l) + K(k, m), K(j, l) + K(k, m) + K(j, k) + K(l, m)))
    return R


def lemma74():
    """The decoded encodings of the generators (TwoQubit.e)."""
    return [('d∘e I', 'I', i(0) + i(1) + i(2) + i(3)),
            ('d∘e S', 's', i(2) + i(3)),
            ('d∘e S↑', 't', i(1) + i(3)),
            ('d∘e K', 'k', K(0, 2) + K(1, 3)),
            ('d∘e K↑', 'l', K(0, 1) + K(2, 3))]


def macro_axioms():
    """The equations between macro letters that tier 2 starts from."""
    A = []
    # the monomial group
    A += [('m-I4', 'IIII', ''), ('m-s4', 'ssss', ''), ('m-t4', 'tttt', ''), ('m-C4', 'CCCC', ''),
          ('m-x2', 'xx', ''), ('m-y2', 'yy', ''), ('m-a2', 'aa', ''), ('m-b2', 'bb', '')]
    for u, v in itertools.combinations('IstC', 2):
        A.append(('m-%s%s' % (u, v), v + u, u + v))
    for u in 'xyab':
        A.append(('m-I%s' % u, u + 'I', 'I' + u))
    A += [('m-xy', 'yx', 'xy'),
          ('m-xs', 'xsx', 'Isss'), ('m-xt', 'xt', 'tx'), ('m-xC', 'xCx', 'CCCt'),
          ('m-ys', 'ys', 'sy'), ('m-yt', 'yty', 'Ittt'), ('m-yC', 'yCy', 'CCCs'),
          ('m-as', 'as', 'sa'), ('m-at', 'ata', 'stCC'), ('m-aC', 'aCa', 'CCCs'),
          ('m-bt', 'bt', 'tb'), ('m-bs', 'bsb', 'stCC'), ('m-bC', 'bCb', 'CCCt'),
          ('m-ax', 'axa', 'xy'), ('m-ay', 'ay', 'ya'), ('m-by', 'byb', 'xy'), ('m-bx', 'bx', 'xb'),
          ('m-ab', 'aba', 'bab')]
    # the controlled K gates
    A += [('p-13', 'pCC', 'ap'), ('p-14', 'pCCC', 'CpCp'), ('p-15', 'ps', 'sp'), ('p-16', 'pps', ''),
          ('q-13', 'qCC', 'bq'), ('q-14', 'qCCC', 'CqCq'), ('q-15', 'qt', 'tq'), ('q-16', 'qqt', ''),
          ('p-I', 'pI', 'Ip'), ('q-I', 'qI', 'Iq'),
          ('p-y', 'ypy', 'ssCCpCC'), ('p-a', 'apa', 'ssCCpCC'),
          ('q-x', 'xqx', 'ttCCqCC'), ('q-b', 'bqb', 'ttCCqCC'),
          ('pq-sw', 'abapaba', 'q'),
          ('p-xpx', 'xpxp', 'pxpx'), ('q-yqy', 'yqyq', 'qyqy'),
          ('p-i1', 'pCCCt', 'CCCtp'), ('q-i2', 'qCCCs', 'CCCsq'),
          ('p-b', 'bpb', 'abqba'), ('sw-pq', 'paba', 'abaq'),
          ('K1', 'xpxp', 'l'), ('K0', 'yqyq', 'k'), ('k-l', 'lk', 'kl'),
          ('k2', 'kk', 'III'), ('l2', 'll', 'III'), ('sk3', 'sksksk', 'III'), ('tl3', 'tltltl', 'III'),
          ('k-I', 'kI', 'Ik'), ('l-I', 'lI', 'Il'), ('k-t', 'tk', 'kt'), ('l-s', 'ls', 'sl'),
          ('x-def', 'x', 'ksskI'), ('y-def', 'y', 'lttlI'),
          ('sw-x', 'abax', 'yaba'), ('sw-y', 'abay', 'xaba'), ('sw-C', 'abaC', 'Caba'),
          ('K03-sym', 'bxpxb', 'ayqya'),
          ('aqa-C', 'Caqa', 'aqaC'), ('aka', 'aka', 'balab'),
          ('q-i0', 'qxyCxy', 'xyCxyq')]
    return A


# Derived over the macro letters (tier 2a), not on the gates.
DERIVED = ['p-b', 'sw-pq', 'sw-C', 'K03-sym', 'q-i0']


def t2a_axioms():
    keep = {'pq-sw', 'p-a', 'p-y', 'q-x', 'q-b', 'p-15', 'q-15', 'p-I', 'q-I', 'p-i1', 'q-i2'}
    return [a for a in macro_axioms() if a[0] not in DERIVED and (a[0].startswith('m-') or a[0] in keep)]


def split_macro_axioms():
    """The macro axioms proved on the gates: (Clifford ones in tier-C
    letters, the others in base letters)."""
    cl, ncl = [], []
    for (n, l, r) in macro_axioms():
        if n in DERIVED:
            continue
        L, R = expand(l), expand(r)
        cL, cR = to_cliff(L), to_cliff(R)
        if cL is not None and cR is not None:
            cl.append((n, cL, cR))
        else:
            ncl.append((n, L, R))
    return cl, ncl


# ----------------------------------------------------------------------
# The stages: (letters, axioms, targets)

def tc_targets():
    """The Clifford macro axioms, and their mirror images (mir-…), which
    a mirrored stage-1 run may use."""
    T = list(split_macro_axioms()[0])
    seen = {(l, r) for (_, l, r) in T}
    for (n, l, r) in split_macro_axioms()[0]:
        ml, mr = mirror(l), mirror(r)
        if (ml, mr) not in seen and (mr, ml) not in seen:
            T.append(('mir-' + n, ml, mr))
            seen.add((ml, mr))
    return T


def stage(name):
    if name == 's0':     # tier C's axioms, on the gates
        return BASE, base_axioms(), [(n, cliff_expand(l), cliff_expand(r)) for (n, l, r) in cliff_axioms()]
    if name == 'tc':     # the Clifford facts
        return CLIFF, cliff_axioms(), tc_targets()
    if name == 's1':     # the rest, on the gates, with the Clifford facts
        extra = [(n, cliff_expand(l), cliff_expand(r)) for (n, l, r) in tc_targets()]
        return BASE, base_axioms() + extra, split_macro_axioms()[1]
    if name == 't2a':    # the derived macro axioms
        return MACRO, t2a_axioms(), [a for a in macro_axioms() if a[0] in DERIVED]
    if name == 't2':     # the decoded relations
        return MACRO, macro_axioms(), relations() + lemma74()
    raise KeyError(name)


def check():
    """Every equation of every stage holds."""
    for st in ('s0', 'tc', 's1', 't2a', 't2'):
        letters, axioms, targets = stage(st)
        ex = {'s0': lambda w: w, 'tc': cliff_expand, 's1': lambda w: w,
              't2a': expand, 't2': expand}[st]
        for (n, l, r) in axioms + targets:
            assert np.allclose(sem(ex(l)), sem(ex(r))), (st, n)
    print('all equations hold')


if __name__ == '__main__':
    check()

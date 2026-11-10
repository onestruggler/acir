"""The data behind Examples/Groups/Alt16-RevCir: states, gates, cycles.

Conventions (those of Syntactics.agda).  A state of the four wires is an
integer whose bit k is the bit of wire k.  The sixteen states are numbered
along the reflected Gray code, position i being the state i xor (i >> 1).  A
permutation is a tuple p with p[i] the image of position i, and words are in
diagram order: the first letter acts first.  Lafont's cycle omega_i sends
i to i + 1, i + 1 to i + 2 and i + 2 to i.
"""

N = 16


def gray(i):
    return i ^ (i >> 1)


ENC = [gray(i) for i in range(N)]            # position -> state
DEC = {s: i for i, s in enumerate(ENC)}      # state -> position


def bit(s, k):
    return (s >> k) & 1


# The gates as functions on states: X on wire k; CX with control k + 1 and
# target k; Ex swapping the wires k, k + 1; CCX with controls k + 1, k + 2
# and target k.

def x_gate(k):
    return lambda s: s ^ (1 << k)


def cx_gate(k):
    return lambda s: s ^ (bit(s, k + 1) << k)


def ex_gate(k):
    def f(s):
        a, b = bit(s, k), bit(s, k + 1)
        return s & ~(3 << k) | (b << k) | (a << (k + 1))
    return f


def ccx_gate(k):
    return lambda s: s ^ ((bit(s, k + 1) & bit(s, k + 2)) << k)


def perm_of(f):
    """The permutation of positions that a function on states carries out."""
    return tuple(DEC[f(ENC[i])] for i in range(N))


GATES = {}
for _k in range(4):
    GATES['X%d' % _k] = perm_of(x_gate(_k))
for _k in range(3):
    GATES['CX%d' % _k] = perm_of(cx_gate(_k))
for _k in range(3):
    GATES['Ex%d' % _k] = perm_of(ex_gate(_k))
for _k in range(2):
    GATES['CCX%d' % _k] = perm_of(ccx_gate(_k))

IDENT = tuple(range(N))


def compose(p, q):
    """p followed by q."""
    return tuple(q[x] for x in p)


def omega(i):
    p = list(range(N))
    p[i], p[i + 1], p[i + 2] = i + 1, i + 2, i
    return tuple(p)


def omega_inv(i):
    p = list(range(N))
    p[i], p[i + 1], p[i + 2] = i + 2, i, i + 1
    return tuple(p)


def word_perm(word):
    """The permutation of a word in the cycles (a list of indices)."""
    p = IDENT
    for i in word:
        p = compose(p, omega(i))
    return p


def circ_perm(circ):
    """The permutation of a circuit (a list of gate names)."""
    p = IDENT
    for g in circ:
        p = compose(p, GATES[g])
    return p


def from_cycles(cycles):
    p = list(range(N))
    for c in cycles:
        for k in range(len(c)):
            p[c[k]] = c[(k + 1) % len(c)]
    return tuple(p)


def cycles_of(p):
    seen, out = set(), []
    for i in range(len(p)):
        if i in seen or p[i] == i:
            continue
        c, j = [], i
        while j not in seen:
            seen.add(j)
            c.append(j)
            j = p[j]
        out.append(tuple(c))
    return out


def inversions(p):
    return sum(1 for i in range(N) for j in range(i + 1, N) if p[i] > p[j])


# ----------------------------------------------------------------------
# The data of Syntactics.agda

# K = (Ex0 Ex2 CCX0)^4, the cycle of the positions 9, 10, 11.
K = ['Ex0', 'Ex2', 'CCX0'] * 4

# K on the face of the wires a, b: K between these swaps.
FACE = {
    (1, 0): [],
    (0, 1): ['Ex0'],
    (2, 0): ['Ex1'],
    (0, 2): ['Ex1', 'Ex0'],
    (3, 0): ['Ex2', 'Ex1'],
    (0, 3): ['Ex2', 'Ex1', 'Ex0'],
}


def k_face(a, b):
    s = FACE[(a, b)]
    return s + K + s[::-1]


def corner(i):
    """The wires a, b that change from state i to i + 1 and from i + 1 to
    i + 2, and the wires on which state i differs from the first state of
    K_ab (wire a clear, the others set)."""
    a = (ENC[i] ^ ENC[i + 1]).bit_length() - 1
    b = (ENC[i + 1] ^ ENC[i + 2]).bit_length() - 1
    first = 0b1111 & ~(1 << a)
    mask = ENC[i] ^ first
    return a, b, [k for k in range(4) if bit(mask, k)]


def omega_circuit(i):
    a, b, wires = corner(i)
    nots = ['X%d' % k for k in wires]
    return nots + k_face(a, b) + nots[::-1]


# The six base gates as words in the cycles (found by words.py).
BASE = {
    'X0': [1, 0, 5, 4, 9, 8, 13, 12],
    'CX0': [3, 2, 11, 10],
    'CCX0': [5, 4, 7, 6, 9, 8],
    'Ex0': [1, 3, 2, 4, 9, 11, 10, 12],
    'Ex1': [2, 3, 4, 2, 5, 3, 8, 9, 10, 8, 11, 9],
    'Ex2': [6, 7, 8, 9, 10, 11, 12, 13, 4, 5, 6, 7, 8, 9, 10, 11,
            6, 7, 8, 9, 4, 5, 6, 7],
}


def phi():
    """Every generator as a word in the cycles: the base words, and the
    other six through the swaps (Translation.agda's φ)."""
    f = dict(BASE)
    f['X1'] = f['Ex0'] + f['X0'] + f['Ex0']
    f['X2'] = f['Ex1'] + f['X1'] + f['Ex1']
    f['X3'] = f['Ex2'] + f['X2'] + f['Ex2']
    f['CX1'] = f['Ex0'] + f['Ex1'] + f['CX0'] + f['Ex1'] + f['Ex0']
    f['CX2'] = f['Ex1'] + f['Ex2'] + f['CX1'] + f['Ex2'] + f['Ex1']
    f['CCX1'] = (f['Ex0'] + f['Ex1'] + f['Ex2'] + f['CCX0']
                 + f['Ex2'] + f['Ex1'] + f['Ex0'])
    return f

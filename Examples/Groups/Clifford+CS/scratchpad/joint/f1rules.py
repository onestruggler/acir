# The rules of the four-wire theory (Syntactics._SRel,_===_) as generator
# words in derivn letters, and their controlled versions lambda1 (control
# wire 4) at every placement in the domain 0 .. 3: the items of (F1).
#
# Generators: ('iI',), ('S', v), ('K', v), ('CS', v, v+1).  A word at
# offset o is the rule's word with every wire shifted by o (the rule's
# `↑ᵒ`).  The shortcuts are Syntactics' definitions, letter for letter.
import derivn
from derivn import norm1

IS = [('iI',)]


def S(v): return [('S', v)]
def K(v): return [('K', v)]
def CS(v): return [norm1(('CS', v, v + 1))]
def X(v): return K(v) + S(v) + S(v) + K(v) + IS
def Z(v): return S(v) + S(v)
def CX01(o): return K(o + 1) + CS(o) + CS(o) + K(o + 1) + IS     # control o, target o+1
def CX10(o): return K(o) + CS(o) + CS(o) + K(o) + IS             # control o+1, target o
def Swap(o): return CX01(o) + CX10(o) + CX01(o)
def CX12(o): return CX01(o + 1)
def CX21(o): return CX10(o + 1)
def CS02(o): return Swap(o + 1) + CS(o) + Swap(o + 1)
def CCZ(o): return CS(o + 1) + CX01(o) + CS(o + 1) * 3 + CX01(o) + CS02(o)
def Toff(o): return K(o) + CCZ(o) + K(o) + IS
def CCZ013(o): return Swap(o + 2) + CCZ(o) + Swap(o + 2)
def CK(o): return CS(o) + K(o + 1) + CS(o) + K(o + 1) + CS(o) + S(o) * 3 + IS


# (name, arity, lhs(o), rhs(o))
RULES = [
    ('order-I', 0, lambda o: IS * 4, lambda o: []),
    ('order-S', 1, lambda o: S(o) * 4, lambda o: []),
    ('order-K', 1, lambda o: K(o) * 2, lambda o: IS * 3),
    ('order-SK', 1, lambda o: (S(o) + K(o)) * 3, lambda o: IS * 3),
    ('order-CS', 2, lambda o: CS(o) * 4, lambda o: []),
    ('comm-CS-S0', 2, lambda o: CS(o) + S(o), lambda o: S(o) + CS(o)),
    ('comm-CS-S1', 2, lambda o: CS(o) + S(o + 1), lambda o: S(o + 1) + CS(o)),
    ('X-CS0', 2, lambda o: X(o) + CS(o), lambda o: CS(o) * 3 + X(o) + S(o + 1)),
    ('X-CS1', 2, lambda o: X(o + 1) + CS(o), lambda o: CS(o) * 3 + X(o + 1) + S(o)),
    ('CS-K0', 2, lambda o: CS(o) + K(o) + CS(o) + K(o) + S(o),
                 lambda o: S(o) + K(o) + CS(o) + K(o) + CS(o)),
    ('CS-K1', 2, lambda o: CS(o) + K(o + 1) + CS(o) + K(o + 1) + S(o + 1),
                 lambda o: S(o + 1) + K(o + 1) + CS(o) + K(o + 1) + CS(o)),
    ('comm-CSu-CS', 3, lambda o: CS(o + 1) + CS(o), lambda o: CS(o) + CS(o + 1)),
    ('rel-266', 3, lambda o: CX10(o) + CX01(o) + CS(o + 1) + CX01(o) + CX10(o),
                   lambda o: CX12(o) + CX21(o) + CS(o) + CX21(o) + CX12(o)),
    ('rel-267', 3, lambda o: CX10(o) + CX01(o) + CS(o + 1) * 2 + CX01(o) + CX10(o),
                   lambda o: CX01(o) + CS(o + 1) * 2 + CX01(o) + CS(o + 1) * 2),
    ('rel-268', 3, lambda o: CS(o + 1) + CX01(o) + CS(o + 1) * 3 + CX01(o),
                   lambda o: CS(o) + CX21(o) + CS(o) * 3 + CX21(o)),
    ('rel-269', 3, lambda o: CS(o + 1) + K(o + 1) + CS(o + 1) + K(o + 1) + CS(o) + K(o + 1) + CS(o),
                   lambda o: CS(o) + K(o + 1) + CS(o) + K(o + 1) + CS(o + 1) + K(o + 1) + CS(o + 1)),
    ('rel-272', 3, lambda o: CS(o + 1) + K(o + 1) + CS(o + 1) * 3 + K(o + 1) + CS(o) + K(o + 1) + CS(o + 1),
                   lambda o: CS(o) + K(o + 1) + CS(o) * 3 + K(o + 1) + CS(o + 1) + K(o + 1) + CS(o)),
    ('cx-ccz', 4, lambda o: CX10(o + 2) + CCZ(o) + CX10(o + 2),
                  lambda o: CCZ(o) + Swap(o + 2) + CCZ(o) + Swap(o + 2)),
    ('toff-ccz', 4, lambda o: Toff(o) + CCZ013(o) + Toff(o),
                    lambda o: CCZ013(o) + CCZ(o + 1)),
    ('ck-tct', 4, lambda o: X(o) + CK(o) + X(o) + Toff(o + 1) + CS(o) + Toff(o + 1),
                  lambda o: Toff(o + 1) + CS(o) + Toff(o + 1) + X(o) + CK(o) + X(o)),
]

SIGMA = {0: ('SBOX', 2, 0, (4, 1), 3), 1: ('SBOX', 0, 1, (4, 2), 3), 2: ('SBOX', 0, 2, (4, 3), 1)}


def lam1_letter(g):
    k = g[0]
    if k == 'iI':
        return [('S', 4)]
    if k == 'S':
        return [norm1(('CS', g[1], 4))]
    if k == 'K':
        return [('CK', 4, g[1])]
    if k == 'CS':
        return [SIGMA[g[1]]]
    raise ValueError(g)


def lam1(word):
    return [x for g in word for x in lam1_letter(g)]


def items():
    """every (name, offset, lhs, rhs): the rule at that offset, controlled."""
    out = []
    for name, ar, l, r in RULES:
        for o in range(0, 4 - max(ar, 1) + 1) if ar > 0 else [0]:
            out.append((f'{name}@{o}', l(o), r(o)))
    return out


if __name__ == '__main__':
    # sanity: every rule is sound on four wires (derivn's semantics at
    # width 5, wire 4 idle), and the controlled versions too
    n_win = 0
    for name, l, r in items():
        assert derivn.fp(l) == derivn.fp(r), ('unsound rule', name)
        L1, R1 = lam1(l), lam1(r)
        assert derivn.fp(L1) == derivn.fp(R1), ('unsound controlled rule', name)
        w = len(derivn.supp(L1 + R1))
        nb = sum(1 for g in L1 + R1 if g[0] == 'SBOX')
        if w <= 4:
            n_win += 1
        print(f'{name:16} wires {w}  S-boxes {nb:3}  letters {len(L1)}+{len(R1)}')
    print(len(items()), 'items,', n_win, 'single windows')

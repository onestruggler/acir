# The CS-parity invariant: the number of CS gates mod 2, in the Agda
# spellings (CX_01 = K^ CS CS K^ i, Swap = CX CX CX, X = K S S K i,
# Z = S S, CZ = CS CS, CK_10 = CS K CS K CS S^3 i, CCZ = CS^ CX CS^3 CX
# (Swap^ CS Swap^), Toff = K CCZ K i), is balanced by every rule of
# Syntactics (at width 3 it is the determinant), while true 4-wire
# identities can break it.
from itertools import product, combinations, permutations
from prover2 import apply, fp, FP_ID, P, I, GINV, DIM
# CS counts of the macros
cs = {'S': 0, 'Sd': 0, 'K': 0, 'Kd': 0, 'iI': 0, 'iIi': 0, 'X': 0, 'Z': 0, 'CS': 1, 'CSd': 3, 'CZ': 2,
      'CX': 2, 'SWAP': 6, 'CK': 3, 'CKd': 3}
def cscount(word): return sum(cs[g[0]] for g in word)
# Bian-Selinger's rules on three wires, as macro words (operator order), checked semantically too
def CXw(c, t): return [('CX', c, t)]
rules = {
 'order-I': ([('iI',)] * 4, []),
 'order-S': ([('S', 0)] * 4, []),
 'order-K': ([('K', 0)] * 2, [('iI',)] * 3),
 'order-SK': ([('S', 0), ('K', 0)] * 3, [('iI',)] * 3),
 'order-CS': ([('CS', 0, 1)] * 4, []),
 'comm-CS-S0': ([('CS', 0, 1), ('S', 0)], [('S', 0), ('CS', 0, 1)]),
 'X-CS0': ([('X', 0), ('CS', 0, 1)], [('CS', 0, 1)] * 3 + [('X', 0), ('S', 1)]),
 'CS-K0': ([('CS', 0, 1), ('K', 0), ('CS', 0, 1), ('K', 0), ('S', 0)], [('S', 0), ('K', 0), ('CS', 0, 1), ('K', 0), ('CS', 0, 1)]),
 'rel-266': (CXw(1, 0) + CXw(0, 1) + [('CS', 1, 2)] + CXw(0, 1) + CXw(1, 0), CXw(1, 2) + CXw(2, 1) + [('CS', 0, 1)] + CXw(2, 1) + CXw(1, 2)),
 'rel-267': (CXw(1, 0) + CXw(0, 1) + [('CS', 1, 2)] * 2 + CXw(0, 1) + CXw(1, 0), CXw(0, 1) + [('CS', 1, 2)] * 2 + CXw(0, 1) + [('CS', 1, 2)] * 2),
 'rel-268': ([('CS', 1, 2)] + CXw(0, 1) + [('CS', 1, 2)] * 3 + CXw(0, 1), [('CS', 0, 1)] + CXw(2, 1) + [('CS', 0, 1)] * 3 + CXw(2, 1)),
 'rel-269': ([('CS', 1, 2), ('K', 1), ('CS', 1, 2), ('K', 1), ('CS', 0, 1), ('K', 1), ('CS', 0, 1)], [('CS', 0, 1), ('K', 1), ('CS', 0, 1), ('K', 1), ('CS', 1, 2), ('K', 1), ('CS', 1, 2)]),
 'rel-272': ([('CS', 1, 2), ('K', 1)] + [('CS', 1, 2)] * 3 + [('K', 1), ('CS', 0, 1), ('K', 1), ('CS', 1, 2)], [('CS', 0, 1), ('K', 1)] + [('CS', 0, 1)] * 3 + [('K', 1), ('CS', 1, 2), ('K', 1), ('CS', 0, 1)]),
}
allok = True
for name, (l, r) in rules.items():
    sem = fp(l) == fp(r); par = (cscount(l) - cscount(r)) % 2
    print(f'{name:12s} semantically {"ok " if sem else "BAD"}  CS parity difference {par}')
    allok &= sem and par == 0
print('all rules balanced:', allok)
# the Toffoli and CCZ as macro words
def CCZ(a, b, c):   # Barenco with target c? use the Agda spelling on (0,1,2) relabelled: CS12 CX01 CS12^3 CX01 CS02, CS02 = Swap12 CS01 Swap12
    return [('CS', b, c), ('CX', a, b), ('CSd', b, c), ('CX', a, b), ('SWAP', b, c), ('CS', a, b), ('SWAP', b, c)]
def Toff(t, b, c): return [('K', t)] + CCZ(t, b, c) + [('K', t), ('iI',)]
# the control-XOR identities
lhs = [('CX', 3, 1)] + Toff(0, 1, 2) + [('CX', 3, 1)]; rhs = Toff(0, 1, 2) + Toff(0, 3, 2)
print('Sigma1 (CX_31 Toff(0;1,2) CX_31 = Toff(0;1,2) Toff(0;3,2)): true', fp(lhs) == fp(rhs), ' CS counts', cscount(lhs), cscount(rhs))
lhs = [('CX', 3, 1)] + CCZ(0, 1, 2) + [('CX', 3, 1)]; rhs = CCZ(0, 1, 2) + CCZ(0, 3, 2)
print('Delta  (CX_31 CCZ_012 CX_31 = CCZ_012 CCZ_032): true', fp(lhs) == fp(rhs), ' CS counts', cscount(lhs), cscount(rhs))
# the shortest true 4-wire identities with odd CS parity, over macro words of length <= 3
atoms = []
for w in range(4): atoms += [('S', w), ('K', w), ('X', w)]
for a, b in permutations(range(4), 2): atoms += [('CX', a, b)]
for a, b in combinations(range(4), 2): atoms += [('CS', a, b), ('SWAP', a, b)]
for t in range(4):
    for b, c in combinations([w for w in range(4) if w != t], 2):
        atoms += [('CCZ', t, b, c), ('TOFF', t, b, c)]
def expand(w):
    out = []
    for g in w:
        if g[0] == 'CCZ': out += CCZ(*g[1:])
        elif g[0] == 'TOFF': out += Toff(*g[1:])
        else: out.append(g)
    return out
seen = {}
for L in range(1, 4):
    for w in product(atoms, repeat=L):
        w = list(w); e = expand(w)
        k = fp(e)
        seen.setdefault(k, []).append((cscount(e) % 2, w))
odd = []
for k, ws in seen.items():
    pars = {p for p, _ in ws}
    if len(pars) == 2:
        w0 = min((w for p, w in ws if p == 0), key=len); w1 = min((w for p, w in ws if p == 1), key=len)
        odd.append((len(w0) + len(w1), w0, w1))
odd.sort(key=lambda t: (t[0], str(t)))
print('shortest true identities with odd CS parity (macro length <= 3):', len(odd))
for t in odd[:12]: print('  ', t[1], ' = ', t[2])

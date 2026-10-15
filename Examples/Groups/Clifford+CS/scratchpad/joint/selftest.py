# Consistency of the semantics: macros against their generator words,
# boxes against their unfoldings.   python3 selftest.py
import itertools
import cs, derivn
from derivn import N, norm1, unfold1, flatten, show

S = cs.Sem(N)
W = range(N)
gates = []
for w in W:
    for k in ('S', 'Sd', 'K', 'Kd', 'X', 'Z'): gates.append((k, w))
gates += [('iI',), ('iIi',)]
for a, b in itertools.permutations(W, 2):
    gates += [('CX', a, b), ('CK', a, b), ('CKd', a, b)]
    if a < b: gates += [('CS', a, b), ('CSd', a, b), ('CZ', a, b), ('SWAP', a, b)]
for s in itertools.combinations(W, 3):
    gates.append(('CCZ',) + s)
    for t in s:
        c = [x for x in s if x != t]; gates.append(('TOFF', t, c[0], c[1]))
bad = [g for g in gates if S.fp([g]) != S.fp(cs.to_generators([g]))]
print(len(gates), 'macros,', len(bad), 'bad', bad[:5])

boxes = []
for k in range(2, 5):
    for ws in itertools.permutations(W, k + 1):
        boxes += [('BOX',) + ws, ('BOXd',) + ws]
for ws in itertools.permutations(W, 5):
    u, x, c1, c2, A = ws
    boxes += [('SBOX', u, x, (c1, c2), A), ('SBOXd', u, x, (c1, c2), A)]
bad = [g for g in boxes if S.fp([g]) != S.fp(flatten([g]))]
print(len(boxes), 'boxes,', len(bad), 'bad', [show([g]) for g in bad[:5]])
bad = [g for g in boxes if S.fp([g]) != S.fp(cs.to_generators(flatten([g])))]
print(len(boxes), 'boxes against generators,', len(bad), 'bad')

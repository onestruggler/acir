"""Is H(x)H conjugate to Z on one wire in the two-wire group?"""
from synth import gates, apply_gate, apply_word
w = 2
N = 4
S = 2
basis = [tuple(S * int(i == j) for i in range(N)) for j in range(N)]
def mat(word):
    return tuple(apply_word(word, e, w) for e in basis)
G = [g for g in gates(2)]
# BFS the group
elems = {mat(()): ()}
fr = [()]
while fr:
    nw = []
    for word in fr:
        for g in G:
            w2 = (g,) + word
            M = mat(w2)
            if M not in elems:
                elems[M] = w2; nw.append(w2)
    fr = nw
print('group order', len(elems))
K = mat((('HH', 0),))
for name, Zw in [('Z0', (('HH', 0), ('X', 0), ('HH', 0))), ('Z1', (('HH', 0), ('X', 1), ('HH', 0)))]:
    Z = mat(Zw)
    found = None
    for M, Ww in elems.items():
        # W Z W^-1 == K  <=>  W Z rev(W) == K
        if mat(Ww + Zw + tuple(reversed(Ww))) == K:
            found = Ww; break
    print(name, 'conjugate to HH via', found)

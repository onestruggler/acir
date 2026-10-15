"""Find W in the three-wire group with W (Z on wire a) W^-1 = HH on (a,b),
wire 2 the borrowed one (a = 0, b = 1)."""
import sys
from synth import gates, apply_gate, apply_word
w = 3; N = 8; S = 4
basis = [tuple(S * int(i == j) for i in range(N)) for j in range(N)]
def mat(word): return tuple(apply_word(word, e, w) for e in basis)
G = gates(3)
Zw = (('HH', 0), ('X', 0), ('HH', 0))    # Z on wire 0 (partner wire 1)
K = mat((('HH', 0),))
Z = mat(Zw)
# BFS on elements; test W Z W^-1 = K  <=>  W Z = K W
elems = {mat(()): ()}
fr = [()]
depth = int(sys.argv[1]) if len(sys.argv) > 1 else 7
for d in range(depth):
    nw = []
    for word in fr:
        for g in G:
            w2 = (g,) + word
            M = mat(w2)
            if M not in elems:
                elems[M] = w2; nw.append(w2)
                if mat(w2 + Zw) == mat((('HH', 0),) + w2):
                    print('found', ' '.join(f'{k}{i}' for k, i in w2)); sys.exit(0)
    fr = nw
    print('depth', d + 1, len(elems), flush=True)
print('none')

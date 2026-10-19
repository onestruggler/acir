"""Is S = <X0, X1, CX0, HH0, CCX0> presented by the two-wire rules and
the Toffoli rules that stay on the wires 0, 1 (CCX², CCX-XC, CCX-HH)?

Enumerates the cosets of the two-wire group P2 = <X0, X1, CX0, HH0> in
the group those rules present, with the letters of S only, and compares
with |S| / |P2|.

    python3 -B sub01.py
"""
import sys
sys.path.insert(0, '..')
import core as C
import natproof as NP
from derive3 import gs, rep, L, ev

LET = ['X0', 'X1', 'CX0', 'HH0', 'CCX0']
idx = {n: k for k, n in enumerate(LET)}
gl = [L[n] for n in LET]

def order(gens):
    seen = {rep.identity}; fr = [rep.identity]
    while fr:
        nw = []
        for p in fr:
            for g in gens:
                q = tuple(p[i] for i in g)
                if q not in seen:
                    seen.add(q); nw.append(q)
        fr = nw
    return len(seen)

gperm = [rep.gens[g] for g in gl]
S = order(gperm)
P2 = order(gperm[:4])
print('|S| =', S, '|P2| =', P2, 'index', S // P2)

# relators in S's letters: the natural rules whose letters are in S
rels = []
for a in NP.axioms(gs):
    word = tuple(a.lhs) + tuple(reversed(a.rhs))
    if all(x in gl for x in word):
        rels.append(tuple(idx[gs.names[x]] for x in word))
print('relators kept', len(rels))
sub = [(0,), (1,), (2,), (3,)]
r = C.index(len(LET), rels, sub, limit=2_000_000)
print('index from the rules', r)

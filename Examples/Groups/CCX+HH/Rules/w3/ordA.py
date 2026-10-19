import sys
sys.path.insert(0, '..')
from derive3 import gs, rep, L
def order(names):
    gens = [rep.gens[L[n]] for n in names]
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
a = order(['X0','X1','X2','CX0','CX1','HH0','HH1'])
print('|A| =', a, 'index', 696729600 // a)

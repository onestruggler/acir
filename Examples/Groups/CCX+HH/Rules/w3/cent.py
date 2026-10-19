import sys
sys.path.insert(0, '..')
from derive3 import gs, rep, L, ev, CAN_LOW, canon_table
# 2-wire group on wires {0,1} inside Gen 3
G2 = CAN_LOW
cx0 = ev((L['CX0'],)); ccx = ev((L['CCX0'],))
def mul(p, q):   # matrix product P Q as evaluate does: word p++q
    # evaluate(word) = permutation; evaluate(w1+w2): apply w2 first then w1
    return tuple(p[i] for i in q)
def comm(a, b): return mul(a, b) == mul(b, a)
cent = [k for k in G2 if comm(k, ccx)]
print('2-wire elements commuting with CCX0:', len(cent))
T = ev(tuple(L[t] for t in 'HH0 CX0 HH0 HH0 HH0 CX0 HH0'.split()))  # XC HH XC = HH CX HH HH HH CX HH
T = ev(tuple(L[t] for t in ['HH0','CX0','HH0','HH0','HH0','CX0','HH0']))
def gen(gs_):
    seen = {rep.identity}; fr = [rep.identity]
    while fr:
        nw = []
        for p in fr:
            for g in gs_:
                q = mul(p, g)
                if q not in seen: seen.add(q); nw.append(q)
        fr = nw
    return seen
print('order of <T>:', len(gen([T])))
x0 = ev((L['X0'],))
print('X0 commutes with CCX0:', comm(x0, ccx), 'CX0:', comm(cx0, ccx))
# words of length <= 3 in {0,1} letters commuting with CCX0 that the rules give directly:
known = [T]
print('<T, conj by ...>')
sub = gen([T, ev((L['CX0'],)), x0])
print('|<T, CX0, X0>| =', len(sub), ' centraliser size', len(cent))

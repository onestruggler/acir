from chains import *
import itertools
D = {
 ('Z',0): drawn(X1, X0, 'C', X1, X0), ('Z',1): czw, ('Z',2): czw0, ('Z',3): 'C',
 ('X',0,1): cnw, ('X',0,2): cn10w, ('X',0,3): drawn('S', X0, X1), ('X',1,2): 'S', ('X',1,3): cn10, ('X',2,3): cn,
 ('H',0,1): chw, ('H',0,2): ch10w, ('H',0,3): drawn(cn10, chw, cn10), ('H',1,2): drawn(cn, ch10, cn),
 ('H',1,3): ch10, ('H',2,3): 'K',
}
def Zg(a): return [('Z',a)]
def Xg(a,b): return [('X',a,b)]
def Hg(a,b): return [('H',a,b)]
def dw(gs): return ''.join(D[g] for g in gs)
R4 = range(4)
def instances():
    out = []
    for a in R4:
        for b in R4:
            if a != b: out.append(('b1',(a,b), Zg(a)+Zg(b), Zg(b)+Zg(a)))
    for a,b,c in itertools.product(R4,R4,R4):
        if b < c and a != b and a != c:
            out.append(('b2',(a,b,c), Zg(a)+Xg(b,c), Xg(b,c)+Zg(a)))
            out.append(('b4',(a,b,c), Zg(a)+Hg(b,c), Hg(b,c)+Zg(a)))
    for a,b,c,d in itertools.product(R4,R4,R4,R4):
        if a < b and c < d and len({a,b,c,d}) == 4:
            out.append(('b3',(a,b,c,d), Xg(a,b)+Xg(c,d), Xg(c,d)+Xg(a,b)))
            out.append(('b5',(a,b,c,d), Xg(a,b)+Hg(c,d), Hg(c,d)+Xg(a,b)))
            out.append(('b6',(a,b,c,d), Hg(a,b)+Hg(c,d), Hg(c,d)+Hg(a,b)))
    for a,b in itertools.product(R4,R4):
        if a < b:
            out.append(('c1',(a,b), Zg(a)+Xg(a,b), Xg(a,b)+Zg(b)))
            out.append(('d1',(a,b), Zg(a)+Zg(b)+Hg(a,b), Hg(a,b)+Zg(a)+Zg(b)))
            out.append(('d2',(a,b), Zg(b)+Hg(a,b), Hg(a,b)+Xg(a,b)))
    for a,b,c in itertools.product(R4,R4,R4):
        if a < b < c:
            out.append(('c2',(a,b,c), Xg(b,c)+Xg(a,b), Xg(a,b)+Xg(a,c)))
            out.append(('c3',(a,b,c), Xg(a,c)+Xg(b,c), Xg(b,c)+Xg(a,b)))
            out.append(('c4',(a,b,c), Hg(b,c)+Xg(a,b), Xg(a,b)+Hg(a,c)))
            out.append(('c5',(a,b,c), Hg(a,c)+Xg(b,c), Xg(b,c)+Hg(a,b)))
    for a,b,c,d in itertools.product(R4,R4,R4,R4):
        if a < b and c < d and a < c and b < d and b != c and len({a,b,c,d})==4:
            out.append(('d3',(a,b,c,d), (Hg(c,d)+Hg(a,c)+Hg(b,d))*4, Hg(a,b)+Hg(c,d)))
    return out
if __name__ == '__main__':
    import numpy as np
    from dec import gm, lvl
    insts = instances()
    for f, idx, l, r in insts:
        M = np.eye(4)
        for g in l: M = M @ gm(g)
        assert np.allclose(sem(dw(l)), M), (f, idx)
        assert eq(dw(l), dw(r)), (f, idx)
    from collections import Counter
    print(len(insts), Counter(f for f,_,_,_ in insts))

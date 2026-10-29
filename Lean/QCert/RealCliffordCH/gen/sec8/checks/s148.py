import sys, time
sys.path.insert(0, r'D:\work2\acir\Lean\QCert\RealCliffordCH\gen\sec8')
import eng3, bfs3, letters as LT
C=lambda j:('C',j); S=lambda j:('S',j); H=lambda j:('H',j); K=lambda j:('K',j); Z=lambda j:('Z',j)
table = [
 ([C(1),C(0)],[C(0),C(1)]),       # e12
 ([C(1),K(0)],[K(0),C(1)]),       # e13
 ([C(1),S(0),S(1)],[S(0),S(1),C(0)]), # f3
 ([K(1),S(0),S(1)],[S(0),S(1),K(0)]), # f4
]
u=[S(0),C(1),S(0),C(0)]
v=[H(1),C(1),H(1),C(0),H(1),C(1),H(1)]
eng=eng3.Engine(2, table)
print(LT.eq(3,u,v))
for ml in [10,12,14,16]:
    t=time.time()
    s=bfs3.Search(eng, maxlen=ml)
    r=s.search(u,v,depth=8,limit=2000000)
    print(ml, time.time()-t, r)
    if r: break

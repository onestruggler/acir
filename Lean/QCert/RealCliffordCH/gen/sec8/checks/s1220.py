import sys, time
sys.path.insert(0, r'D:\work2\acir\Lean\QCert\RealCliffordCH\gen\sec8')
import eng3, bfs3, letters as LT
C=lambda j:('C',j); S=lambda j:('S',j)
table = [([C(1),C(0)],[C(0),C(1)]), ([C(1),S(0),S(1)],[S(0),S(1),C(0)])]
u=[C(1),S(0),C(1),S(0)]; v=[S(0),C(1),S(0),C(1)]
eng=eng3.Engine(2, table)
print(LT.eq(3,u,v))
s=bfs3.Search(eng, maxlen=10)
r=s.search(u,v,depth=8,limit=500000)
print(r)

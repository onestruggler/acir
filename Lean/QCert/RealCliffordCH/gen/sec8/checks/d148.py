import sys
sys.path.insert(0, r'D:\work2\acir\Lean\QCert\RealCliffordCH\gen\sec8')
import eng3, letters as LT
H=lambda j:('H',j); Z=lambda j:('Z',j); C=lambda j:('C',j); K=lambda j:('K',j); S=lambda j:('S',j)
c20=[S(0),C(1),S(0)]
W=[K(0)]+c20+[K(0)]+c20
V=c20+[K(0)]+c20+[K(0)]
X2=[H(2),Z(2),H(2)]
R=[K(0),S(0),Z(1),S(0),K(0),S(0),Z(1),S(0)]
Rp=[S(0),Z(1),S(0),K(0),S(0),Z(1),S(0),K(0)]
x10=[H(0),C(0),H(0)]
names=['e148a','d128','d117','d118','d136','d138','d143','e15','d123','czc']
table=[
 ([C(0)]+c20, c20+[C(0)]),          #0 148a
 (c20+W, W+[C(1)]+c20),             #1 128
 (W+V, []),                         #2 117
 (V+W, []),                         #3 118
 (X2+W+X2+W, R),                    #4 136
 (V+X2+V+X2, Rp),                   #5 138
 ([C(1)]+X2+V+X2, X2+V+X2+[C(1)]),  #6 143
 (W+W, [C(1)]),                     #7 e15
 ([Z(0)]+V, W+[Z(0)]),              #8 123
 ([C(1),S(0),C(1),S(0)], [S(0),C(1),S(0),C(1)]), #9 czc
]
eng=eng3.Engine(2, table)
for k,(l,r) in enumerate(table):
    assert LT.eq(3,l,r), names[k]
class B:
    def __init__(s,w): s.cur=list(w); s.steps=[]
    def step(s,st):
        n=eng.apply_step(s.cur,st)
        assert n is not None, (st, s.cur)
        s.cur=n; s.steps.append(st)
    def find(s,sub,start=0):
        for i in range(start,len(s.cur)-len(sub)+1):
            if s.cur[i:i+len(sub)]==sub: return i
        raise ValueError(sub)
    def rw(s,k,i,d=False): s.step(('rw',i,k,d))
    def sem(s,i,n,r): s.step(('sem',i,n,list(r)))
    def sw(s,i): s.step(('sw',i))
TR=x10+c20+x10
TL=[C(1)]+c20
b=B(TR)
b.sem(0,3,R+[C(0)])
i=len(R)+1+3; b.sem(i,3,R+[C(0)])
i=b.find([C(0)]+c20); b.rw(0,i)
i=b.find([C(0)]+R+[C(0)]); b.sem(i,len(R)+2,Rp)
# cur: R c20 Rp
b.rw(4,0,True)                       # R -> X2 W X2 W
i=b.find(Rp); b.rw(5,i,True)         # Rp -> V X2 V X2
# cur: X2 W X2 W c20 V X2 V X2
def wcv(b, i):
    """[W, c20, V] at i -> [c20, C1]"""
    b.sem(i+len(W),0,[C(1),C(1)])
    b.rw(9,i+len(W)+1)               # C1 c20 -> c20 C1
    b.rw(1,i,True)                   # W C1 c20 -> c20 W
    j=i+3+len(W)                     # position of C1 after W
    assert b.cur[j]==C(1)
    b.rw(7,j,True)                   # C1 -> W W
    b.rw(7,i+3)                      # W W -> C1
    assert b.cur[i+3:i+4]==[C(1)]
    b.rw(2,i+4)                      # W V -> []
wcv(b, 3+len(W)+3)
# cur: X2 W X2 c20 C1 X2 V X2
i=b.find([C(1)]+X2+V+X2); b.rw(6,i)
# cur: X2 W X2 c20 X2 V X2 C1
# X2 c20 X2 -> c20 Z0, at position 3+len(W)
i=3+len(W)
assert b.cur[i:i+9]==X2+c20+X2
b.sw(i+2); b.sw(i+1); b.sw(i)
b.sw(i+5); b.sw(i+6); b.sw(i+7)
b.sem(i+1,7,[C(1),Z(1)])
b.sem(i+2,2,[S(0),Z(0)])
# cur: X2 W c20 Z0 V C1
j=3+len(W)
assert b.cur[3:j]==W and b.cur[j:j+3]==c20 and b.cur[j+3]==Z(0)
b.rw(3,j+3,True)       # insert V W before Z0
# cur: X2 W c20 V W Z0 V C1
wcv(b,3)
# cur: X2 c20 C1 W Z0 V C1
k=3+3+1
assert b.cur[k:k+len(W)]==W
b.rw(8,k+len(W),False)  # Z0 V -> W Z0
b.rw(7,k)               # W W -> C1
b.sem(k-1,2,[])         # C1 C1 -> []
# cur: X2 c20 Z0 C1
print(b.cur)
# X2 c20 Z0 X2: need X2 after Z0; currently C1 at end. Original had X2 V X2 C1 ... check
b.sw(2); b.sw(1); b.sw(0)
b.sw(6); b.sw(7); b.sw(8)
b.sw(5); b.sw(6); b.sw(7)
b.sem(1,7,[C(1),Z(1)])
b.sem(2,3,[S(0)])
b.rw(9,0,True)
print(b.cur==TL, len(b.steps))
# sub-lemma czc run (from bfs3)
czc_steps=[('sem', 0, 0, [('S', 0), ('S', 0)]), ('sem', 6, 0, [('S', 1), ('S', 1)]), ('rw', 4, 1, False), ('sem', 3, 2, []), ('sem', 2, 2, [('S', 1), ('C', 1)]), ('rw', 3, 0, False), ('rw', 1, 1, True), ('sem', 4, 2, [('S', 1), ('C', 1)]), ('sem', 3, 2, [])]
e2=eng3.Engine(2,[([C(1),C(0)],[C(0),C(1)]), ([C(1),S(0),S(1)],[S(0),S(1),C(0)])])
w,bad=e2.run([C(1),S(0),C(1),S(0)],czc_steps); print(w==[S(0),C(1),S(0),C(1)])
def lw(w): return '['+', '.join('L.%s %d'%(k,j) for k,j in w)+']'
def lst(st):
    if st[0]=='rw': return '.rw %d %d %s'%(st[1],st[2],'true' if st[3] else 'false')
    if st[0]=='sw': return '.sw %d'%st[1]
    return '.sem %d %d %s'%(st[1],st[2],lw(st[3]))
print('TR', lw(TR)); print('TL', lw(TL))
for k,(l,r) in enumerate(table): print(names[k], lw(l), '=>', lw(r))
print('[' + ', '.join(lst(s) for s in b.steps) + ']')
print('czc [' + ', '.join(lst(s) for s in czc_steps) + ']')

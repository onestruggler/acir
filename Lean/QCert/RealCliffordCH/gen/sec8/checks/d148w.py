import sys
sys.path.insert(0, r'D:\work2\acir\Lean\QCert\RealCliffordCH\gen\sec8\w4')
sys.path.insert(0, r'D:\work2\acir\Lean\QCert\RealCliffordCH\gen\sec8')
import tok
def s(k,j): return ('s',k,j)
def p(m,w,ps): return ('p',m,tuple(tuple(x) for x in w),tuple(ps))
def tau(j,q): return j+1 if q==j else (j if q==j+1 else q)
def toP(l):
    k,j=l
    if k in 'HZ': return p(1,[(k,0)],[j])
    return p(2,[(k,0)],[j,j+1])
def rl1(j,t):
    if t[0]=='s': t=toP((t[1],t[2]))
    if t[0]=='p': return ('p',t[1],t[2],tuple(tau(j,x) for x in t[3]))
    raise
def rlS(sig,t):
    for j in sig: t=rl1(j,t)
    return t
TR=[('H',0),('C',0),('H',0),('S',0),('C',1),('S',0),('H',0),('C',0),('H',0)]
TL=[('C',1),('S',0),('C',1),('S',0)]
TRp=[rlS([1,0],s(*l)) for l in TR]
TLp=[rlS([1,0],s(*l)) for l in TL]
print('TRp',TRp); print('TLp',TLp)
print(tok.weq(3,TRp,TLp))
l148b=[s('S',0),s('C',1),s('S',0),s('C',0)]
r148b=[s('H',1),s('C',1),s('H',1),s('C',0),s('H',1),s('C',1),s('H',1)]
print(tok.weq(3,l148b,TLp), tok.weq(3,r148b,TRp))
T=[(TRp,TLp)]
e=tok.Engine(2,T)
c02=p(2,[('C',0)],[0,2]); c20=p(2,[('C',0)],[2,0]); c12=p(2,[('C',0)],[1,2]); c10=p(2,[('C',0)],[1,0])
s12=p(2,[('S',0)],[1,2]); h1=p(1,[('H',0)],[1])
steps=[
 ('sem',1,1,[c12],0),            # C1 -> p C0 [1,2]
 ('swp',0,0,c12,c02,False),      # [S0, c12, S0] -> c02
 ('sem',0,1,[c20],1),            # c02 -> c20
 ('sem',1,1,[c10],2),            # C0 -> p C0 [1,0]
 ('swp',1,1,c20,c10,True),       # c10 -> [S1, c20, S1]
 ('sem',1,1,[s12],0), ('sem',3,1,[s12],0),
 ('rw',0,0,True),                # TLp -> TRp
]
cur,bad=e.run(l148b,steps); print(bad, cur==TRp)
# from TRp to r148b: H0 relabelled -> h1 ; C0 -> c12 ; S0 C1 S0 -> s12 c20 s12
steps2=[]
cur=list(TRp)
def ap(st):
    global cur
    n=e.apply_step(cur,st); assert n is not None,(st,cur); cur=n; steps2.append(st)
# convert each h1 to letter H1 and c12 to letter C1, middle [s12,c20,s12] to C0
for i,t in enumerate(list(cur)):
    pass
i=0
while i < len(cur):
    t=cur[i]
    if t==h1: ap(('sem',i,1,[s('H',1)],0)); i+=1
    elif t==c12: ap(('sem',i,1,[s('C',1)],0)); i+=1
    elif t==s12 and cur[i+1]==c20 and cur[i+2]==s12:
        ap(('sem',i,1,[s('S',1)],0)); ap(('sem',i+2,1,[s('S',1)],0))
        ap(('swp',i,1,c20,c10,False)); ap(('sem',i,1,[s('C',0)],2)); i+=1
    else: raise Exception(t)
print(cur==r148b)
allsteps=steps+steps2
cur,bad=e.run(l148b,allsteps); print('total',bad,cur==r148b)
def lt(t):
    if t[0]=='s': return 't%s %d'%(t[1],t[2])
    return 'tp %d [%s] [%s]'%(t[1],', '.join('L.%s %d'%x for x in t[2]),', '.join(map(str,t[3])))
def lst(st):
    if st[0]=='rw': return '.rw %d %d %s'%(st[1],st[2],'true' if st[3] else 'false')
    if st[0]=='sem': return '.sem %d %d [%s] %d'%(st[1],st[2],', '.join(lt(x) for x in st[3]),st[4])
    if st[0]=='swp': return '.swp %d %d (%s) (%s) %s'%(st[1],st[2],lt(st[3]),lt(st[4]),'true' if st[5] else 'false')
print('TRp:', '['+', '.join(lt(x) for x in TRp)+']')
print('TLp:', '['+', '.join(lt(x) for x in TLp)+']')
print('['+', '.join(lst(x) for x in allsteps)+']')

"""Generate BoxCommLow.lean; run from the Lean project directory."""
import sys,itertools,pickle
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import gen2,proj,sym,tok,solve2
def direct_known(P,u,v):
 at,a,b=solve2.trim(u,v);S=P.solver([])
 for name,(l,r,pf) in list(P.ctx.eqs.items()):
  for left,right,rev in [(l,r,False),(r,l,True)]:
   if len(a)!=len(left) or len(b)!=len(right):continue
   pre=[];post=[];ok=True
   for i,(x,y) in enumerate(zip(a,left)):
    st=S.respell(x,y)
    if st is None:ok=False;break
    pre+=solve2.shift(st,i)
   if not ok:continue
   for i,(x,y) in enumerate(zip(right,b)):
    st=S.respell(x,y)
    if st is None:ok=False;break
    post+=solve2.shift(st,i)
   if not ok:continue
   k=P.ctx.entry(l,r,pf,dep=name)
   return solve2.shift(pre+[('rw',0,k,rev)]+post,at)
 raise solve2.Fail('no exact equation')

P=proj.Project(4,lambda k,n:n+sym.KIND_AR[k]<=4,'(havail4b ih)')
for mod in ['A','B1','B2','B3','B4','HgMerge','Expansion','CommuteLate']:
 for n,(l,r) in gen2.read_known(Path(gen2.LEAN_DIR)/(mod+'.lean')).items():P.known(n,l,r)
def save():
 pass
def chain(name,ws,names=[]):
 steps=[]
 for i,(u,v) in enumerate(zip(ws,ws[1:])):
  found=False
  try: st=direct_known(P,u,v);found=True
  except solve2.Fail: pass
  if not found:
   for ns in [[],names]:
    S=P.solver(ns);S.start(100)
    try: st=S.solve(u,v);found=True;break
    except solve2.Fail:pass
  if not found:raise RuntimeError((name,i,u,v))
  steps+=st
 e=P.emit(name,ws[0],ws[-1],steps);save();return e
def box(t,cols):return tok.G('box',[t],[(w,cols[i]) for i,w in enumerate(x for x in range(4) if x!=t)])
def cz(ws,cols):
 xx=[]
 for i,c in enumerate(cols):
  if not c:xx += [('H',i),('Z',i),('H',i)]
 return ('p',2,tuple(xx+[('C',0)]+list(reversed(xx))),tuple(ws))
def flips(name,wires):
 ns=[name]
 for w in wires:
  for old in list(ns):
   new=old+'f'+str(w)
   if new not in P.ctx.eqs:P.derive_flip(old,w,new)
   ns.append(new)
 return ns
T=(True,True,True);A=box(0,T)
exp=list(P.ctx.eqs['150'][1])
for x,y in itertools.product((False,True),repeat=2):
 C=cz([1,2],[x,y]);name='ControlCZ'+str(int(x))+str(int(y))
 e=chain(name,[[C,A],[C]+exp,exp+[C],[A,C]],['150'])
 flips(name,[1,2,3])
save()
for base in ['166','170a','156']:
 flips(base,[1,2,3])
for vs in sorted(itertools.product((False,True),repeat=3),key=lambda v:v.count(False)):
 B=box(0,vs);name='Box335Base'+''.join('T' if v else 'F' for v in vs)
 if vs==T:chain(name,[[A,B],[B,A]]);continue
 w=next(i+1 for i,c in enumerate(vs) if not c)
 prev=list(vs);prev[w-1]=True;D=box(0,prev)
 rem=[i for i in [1,2,3] if i!=w];C=cz(rem,[vs[i-1] for i in rem])
 ns=['166','170a']+[n for n in P.ctx.eqs if n.startswith(('166f','170af','Box335Base','ControlCZ'))]
 chain(name,[[A,B],[D,D,A,B],[D,A,D,B],[D,A,C],[D,C,A],[D,D,B,A],[B,A]],ns)
for name in [n for n in P.ctx.eqs if n.startswith('Box335Base')]:flips(name,[1,2,3])
save()
print('ALL SAME BORROW DONE',flush=True)
for vs in [(True,False,True),(True,True,False),(True,False,False)]:
 B=box(1,vs);name='Box336Base'+''.join('T' if v else 'F' for v in vs)
 chain(name,[[A,B],[B,A]],['179','180'])
B=box(1,T);D=box(1,[True,False,True]);C=cz([0,3],[True,True])
chain('Box336BaseTTT',[[A,B],[D,D,A,B],[D,A,D,B],[D,A,C],[D,C,A],[D,D,B,A],[B,A]],
 ['166','170a','159']+[n for n in P.ctx.eqs if n.startswith(('166f','170af','Box336Base'))])
for name in [n for n in P.ctx.eqs if n.startswith('Box336Base')]:flips(name,[0,1,2,3])
save()
print('ALL DIFFERENT BORROW DONE',flush=True)
header='''/-
Copyright (c) 2026 QCert contributors. All rights reserved.

Four-wire base cases of (335) and (336). Control-CZ commutation follows
from (150); complementary boxes merge by (170). The different-borrow
cases use (179), (180), and the same merge. Every run is kernel checked.
-/
import QCert.RealCliffordCH.Sec8.D.W4.CommuteLate

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace QCert.RealCliffordCH.Sec8.D.W4Low
open Circuit WE WS
open Eng (L)
open W4
'''
Path('QCert/RealCliffordCH/Sec8/D/W4/BoxCommLow.lean').write_text(header+'\n'.join(gen2.lean_run(e,4,4) for e in P.out)+'\nend QCert.RealCliffordCH.Sec8.D.W4Low\n',encoding='utf-8')

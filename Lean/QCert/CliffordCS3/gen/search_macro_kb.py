#!/usr/bin/env python3
"""Proof-producing search with named circuit abbreviations and local identities."""
from pathlib import Path
import sys,importlib.util,itertools,json,pickle,time,heapq,random
from base_rules import equations
from three_words import K,S,X,CX,SW,CS,ccZ,ccX,atom,inverse
import pair_normalize as pn
ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('cskb',ROOT.parents[1]/'Minimality/gen/cskb.py')
kbmod=importlib.util.module_from_spec(spec);sys.modules['cskb']=kbmod;spec.loader.exec_module(kbmod)
NAMES=['i','K0','K1','K2','S0','S1','S2','CS01','CS12']
EXP=[(i,) for i in range(9)]
def named(name,word):
 NAMES.append(name);EXP.append(tuple(word));return len(NAMES)-1
KI=[named('k'+str(q),inverse(K(q))) for q in range(3)]
SI=[named('s'+str(q),inverse(S(q))) for q in range(3)]
CSI=[named('cs'+str(q)+str(q+1),inverse(CS(q,q+1))) for q in range(2)]
XX=[named('X'+str(q),X(q)) for q in range(3)]
CC={(c,t):named('CX'+str(c)+str(t),CX(c,t)) for c,t in [(0,1),(1,0),(1,2),(2,1)]}
SS=[named('SW'+str(q)+str(q+1),SW(q,q+1)) for q in range(2)]
CS02=named('CS02',CS(0,2))
CS02I=named('cs02',CS(0,2,3))
Q=named('Q',ccZ())
TT=[named('CCX'+str(q),ccX(q)) for q in range(3)]
AA=named('A',atom())
def expanded(w):return tuple(x for t in w for x in EXP[t])
def symbolic_definitions():
 defs=[(tuple(EXP[i]),(i,)) for i in range(9,len(EXP))]
 # Additional spellings using existing abbreviations.
 for q in range(3):defs.append(((1+q,4+q,4+q,1+q,0),(XX[q],)))
 for (c,t),i in CC.items():defs.append(((1+t,7+min(c,t),7+min(c,t),1+t,0),(i,)))
 for q in range(2):defs.append(((CC[q,q+1],CC[q+1,q],CC[q,q+1]),(SS[q],)))
 defs.extend([((SS[0],8,SS[0]),(CS02,)),((SS[0],8,8,8,SS[0]),(CS02I,)),
              ((CS02I,CC[0,1],8,CC[0,1],CSI[1]),(Q,))])
 for q in range(3):defs.append(((1+q,Q,KI[q]),(TT[q],)))
 defs.append(((1,7,KI[0],CS02I,1,CSI[0],KI[0],CS02),(AA,)))
 return defs
def local_equations():
 eqs=[];seen={};pairletters=[]
 for j,mapping in enumerate(pn.PAIRS):
  inv={g:k for k,g in enumerate(mapping)}
  letters=[i for i,w in enumerate(EXP) if all(g in inv for g in w) and i<Q]
  small={i:tuple(inv[g] for g in EXP[i]) for i in letters}
  seen={pn.identity():()}
  for n in range(1,4):
   for w in itertools.product(letters,repeat=n):
    key=pn.evaluate(tuple(g for i in w for g in small[i]))
    if key not in seen:seen[key]=w
    elif w!=seen[key]:
     old=seen[key]
     if (len(w),w)<(len(old),old):seen[key]=w;w,old=old,w
     eqs.append((j,w,old))
 return eqs
def main(seed,seconds):
 out=Path('/tmp/acir-cs3-macro-kb');out.mkdir(exist_ok=True)
 start=time.time()
 defs=symbolic_definitions()
 base=[('ax'+i,a,b) for i,a,b in equations()]
 meta=[{'type':'ax','id':int(i),'lhs':a,'rhs':b} for i,a,b in equations()]
 for i,(a,b) in enumerate(defs):
  assert expanded(a)==expanded(b)
  base.append(('def'+str(i),a,b));meta.append({'type':'def','lhs':a,'rhs':b})
 eqfile=out/'locals.pickle'
 if eqfile.exists():
  with eqfile.open('rb') as f:locals_=pickle.load(f)
 else:
  locals_=local_equations()
  with eqfile.open('wb') as f:pickle.dump(locals_,f)
 for i,(j,a,b) in enumerate(locals_):
  base.append(('pair'+str(i),a,b));meta.append({'type':'pair','pair':j,'lhs':a,'rhs':b})
 order=list(range(len(EXP)))
 if seed:random.Random(seed).shuffle(order)
 kb=kbmod.KB(order,base)
 # Prefilter critical overlaps that would produce large equations.
 overlap=kb.overlaps
 def bounded(a,b):
  A,B=kb.rules[a],kb.rules[b]
  if not(A[3]and B[3]):return
  la,lb=A[0],B[0]
  for k in range(1,min(len(la),len(lb))):
   if la[-k:]==lb[:k]:
    u1=A[1]+lb[k:];u2=la[:-k]+B[1]
    if max(len(u1),len(u2))<=12:kb.push(u1,u2,[(0,a,True),(len(la)-k,b,False)])
 kb.overlaps=bounded
 # Admit every given equation before scheduling critical pairs. Otherwise
 # the short critical pairs can indefinitely starve the long circuit
 # definitions and the essential three-wire axioms C13--C17.
 kb.pending=[]
 kb.overlaps=lambda a,b:None
 for name,a,b in base:kb.process(kb.enc(a),kb.enc(b),('base',name))
 kb.overlaps=bounded
 live=list(kb.index.values())
 for a in live:
  for b in live:bounded(a,b)
 raw=json.loads((ROOT/'coset_obligations.json').read_text())
 goals=[(g,kb.enc(g['lhs']),kb.enc(g['rhs']))for g in raw]
 solved={};steps=0;last=start
 def save():
  nonlocal last
  for g,l,r in goals:
   if g['name'] not in solved:
    a,sa=kb.reduce(l);b,sb=kb.reduce(r)
    if a==b:solved[g['name']]=sa+kb.invert(sb)
  for q in range(3):
   name='tokeninv'+str(q);l=kb.enc((TT[q],TT[q]))
   a,sa=kb.reduce(l)
   if not a:solved[name]=sa
  print(seed,steps,len(kb.index),len(kb.pending),'solved',list(solved),'secs',round(time.time()-start),flush=True)
  with(out/f'run{seed}.pickle').open('wb')as f:pickle.dump({'letters':kb.letters,'rules':kb.rules,'solved':solved,'base':meta,'names':NAMES,'expansions':EXP},f)
  last=time.time()
 print('START',seed,'abbreviations',len(EXP),'base',len(base),flush=True)
 while kb.pending and time.time()-start<seconds:
  m,_,u,v,proof=heapq.heappop(kb.pending)
  kb.process(u,v,proof);steps+=1
  if time.time()-last>25:save()
  if len(kb.index)>15000 or len(kb.pending)>4000000:break
 save()
if __name__=='__main__':main(int(sys.argv[1]),int(sys.argv[2])if len(sys.argv)>2 else 600)


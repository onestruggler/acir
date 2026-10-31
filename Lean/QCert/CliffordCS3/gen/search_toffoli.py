#!/usr/bin/env python3
"""Five-generator certificate search for the Toffoli permutation identities."""
from pathlib import Path
import sys,heapq,pickle,time,importlib.util,random,os
from base_rules import equations
from three_words import ccZ,ccX
from pair_normalize import left,identity
ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('cskb',ROOT.parents[1]/'Minimality/gen/cskb.py')
mod=importlib.util.module_from_spec(spec);sys.modules['cskb']=mod;spec.loader.exec_module(mod)
GLOBALS=(0,1,2,7,8)
def local(depth,conv):
 seen={identity():()};front=[identity()];rules=[]
 for _ in range(depth):
  nxt=[]
  for key in front:
   w=seen[key]
   for g,c in conv.items():
    z=left(c,key);nw=(g,)+w
    if z not in seen:seen[z]=nw;nxt.append(z)
    elif seen[z]!=nw:rules.append((nw,seen[z]))
  front=nxt
 return rules
def run(seed,seconds):
 start=time.monotonic();last=start
 out=Path('/tmp/acir-cs3-toffoli-seeded');out.mkdir(exist_ok=True)
 cache=out/'localbase.pickle'
 if cache.exists():
  with cache.open('rb')as f:base=pickle.load(f)
 else:
  base=[]
  for j,depth,conv in [(0,9,{0:0,1:1,2:2,3:5}),(1,10,{0:0,2:1,4:5})]:
   for a,b in local(depth,conv):base.append(('pair'+str(j)+'_'+str(len(base)),a,b))
  for name,a,b in equations():
   if all(x in GLOBALS for x in a+b):
    base.append(('ax'+name,tuple(GLOBALS.index(x)for x in a),tuple(GLOBALS.index(x)for x in b)))
  with cache.open('wb')as f:pickle.dump(base,f)
 order=list(range(5));random.Random(seed).shuffle(order)
 kb=mod.KB(order,base)
 kb.pending=[]
 original_overlaps=kb.overlaps
 kb.overlaps=lambda a,b:None
 for name,l,r in base:kb.process(kb.enc(l),kb.enc(r),('base',name))
 kb.overlaps=original_overlaps
 live=list(kb.index.values())
 for a in live:
  for b in live:kb.overlaps(a,b)
 Q=tuple(GLOBALS.index(x)for x in ccZ())
 T=[tuple(GLOBALS.index(x)for x in ccX(q))for q in [0,1]]
 targets=[('Qsquare',Q*2,()),('T0square',T[0]*2,()),('T1square',T[1]*2,()),
          ('braid01',T[0]+T[1]+T[0],T[1]+T[0]+T[1]),
          ('Qphase',Q+(4,),(4,)+Q),
          ('T0phase',T[0]+(4,),(4,)+T[0])]
 goals=[(n,kb.enc(l),kb.enc(r))for n,l,r in targets]
 steps=0;solved={}
 def save():
  nonlocal last
  for n,l,r in goals:
   nl,sl=kb.reduce(l);nr,sr=kb.reduce(r)
   if nl==nr:solved[n]=sl+kb.invert(sr)
  print(seed,'steps',steps,'rules',len(kb.index),'pending',len(kb.pending),'solved',list(solved),'secs',int(time.monotonic()-start),flush=True)
  state={'letters':order,'globals':GLOBALS,'base':base,'rules':kb.rules,'solved':solved,'targets':targets}
  with(out/f'toffoli{seed}.pickle').open('wb')as f:pickle.dump(state,f)
  last=time.monotonic()
 print('START',seed,'base',len(base),flush=True)
 while kb.pending and time.monotonic()-start<seconds:
  m,_,u,v,p=heapq.heappop(kb.pending)
  if m>30:continue
  kb.process(u,v,p);steps+=1
  if time.monotonic()-last>20:
   save()
   if len(solved)==len(goals):break
  if len(kb.pending)>int(os.environ.get('CS3_KB_PENDING','16000000')) or len(kb.index)>50000:break
 save()
if __name__=='__main__':run(int(sys.argv[1]),int(sys.argv[2])if len(sys.argv)>2 else 600)


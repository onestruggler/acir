#!/usr/bin/env python3
"""Five-letter cross-target identities, seeded with proved local certificates."""
from pathlib import Path
import pickle,json,sys,heapq,time,random,importlib.util,re
from three_words import ccZ,ccX,CX,atom
BASE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('cskb',BASE.parents[1]/'Minimality/gen/cskb.py')
mod=importlib.util.module_from_spec(spec);sys.modules['cskb']=mod;spec.loader.exec_module(mod)
GLOBALS=(0,1,2,7,8)

def get_base():
 with Path('/tmp/acir-cs3-toffoli-seeded/localbase.pickle').open('rb') as f:base=pickle.load(f)
 for module,seed in [('AtomCube',5),('AtomRelations',12),('AtomNegative',12)]:
  d=json.loads((BASE/'data'/f'{module}-seed{seed}.json').read_text())
  amap=(0,2,3,4)
  def trans(w):return tuple(amap[d['letters'][i]] for i in w)
  for rid,rule in d['rules'].items():base.append((module+'.r'+rid,trans(rule[0]),trans(rule[1])))
  for name,proof in d['solved'].items():
   l,r=next((l,r) for n,l,r in d['targets'] if n==name)
   base.append((module+'.'+name+'Rule',tuple(amap[i] for i in l),tuple(amap[i] for i in r)))
 def g(w):return tuple(GLOBALS.index(x) for x in w)
 Q=g(ccZ());A=g(atom());P=(4,)
 base += [('Qsquare',Q+Q,()),('PcommQ',P+Q,Q+P),('Acube',A*3,P*2)]
 return base

def run(seed,seconds=300):
 out=Path('/tmp/acir-cs3-cross');out.mkdir(exist_ok=True)
 cache=out/'base.pickle'
 if cache.exists():
  with cache.open('rb') as f:base=pickle.load(f)
 else:
  base=get_base()
  with cache.open('wb') as f:pickle.dump(base,f)
 order=list(range(5));random.Random(seed).shuffle(order);kb=mod.KB(order,base)
 start=time.monotonic();last=start;steps=0;solved={}
 kb.pending=[];overlaps=kb.overlaps;kb.overlaps=lambda a,b:None
 for n,l,r in base:kb.process(kb.enc(l),kb.enc(r),('base',n))
 kb.overlaps=overlaps;live=list(kb.index.values())
 for a in live:
  for b in live:kb.overlaps(a,b)
 def g(w):return tuple(GLOBALS.index(x) for x in w)
 A=(2,3,0,2,4,4,4,2,3,3,3,0,2,4)
 B=g(CX(1,0)+ccX(0));T0=g(ccX(0));T1=g(ccX(1))
 targets=[('cross_comm',A+B,B+A),('braid',T0+T1+T0,T1+T0+T1)]
 print('START',seed,'base',len(base),'live',len(live),'queue',len(kb.pending),flush=True)
 goals=[(n,kb.enc(l),kb.enc(r)) for n,l,r in targets]
 def save():
  nonlocal last
  for n,l,r in goals:
   nl,sl=kb.reduce(l);nr,sr=kb.reduce(r)
   if nl==nr:solved[n]=sl+kb.invert(sr)
  print(seed,'steps',steps,'rules',len(kb.index),'queue',len(kb.pending),'solved',list(solved),'secs',int(time.monotonic()-start),flush=True)
  with(out/f'cross{seed}.pickle').open('wb')as f:pickle.dump({'letters':order,'base':base,'rules':kb.rules,'solved':solved,'targets':targets},f)
  last=time.monotonic()
 save()
 while kb.pending and time.monotonic()-start<seconds and len(solved)<len(goals):
  m,_,u,v,p=heapq.heappop(kb.pending)
  if m>30:continue
  kb.process(u,v,p);steps+=1
  if time.monotonic()-last>20:
   save()
   if len(kb.pending)>8000000 or len(kb.index)>20000:break
 save()

if __name__=='__main__':run(int(sys.argv[1]))

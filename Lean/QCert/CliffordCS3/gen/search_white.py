#!/usr/bin/env python3
"""Controlled Clifford certificates with the target phase available."""
from pathlib import Path
import sys,pickle,heapq,time,random,importlib.util,json,os
from pair_normalize import left,identity
BASE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('cskb',BASE.parents[1]/'Minimality/gen/cskb.py')
mod=importlib.util.module_from_spec(spec);sys.modules['cskb']=mod;spec.loader.exec_module(mod)

def local(depth):
 conv={0:0,1:2,2:5,4:4};seen={identity():()};front=[identity()];rules=[]
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

def base_rules():
 out=[]
 for directory,module,seed in [('/tmp/acir-cs3-atom-extra','AtomRelations',12),('/tmp/acir-cs3-atom-neg','AtomNegative',12),('/tmp/acir-cs3-atom-signneg','SignNegative',6)]:
  with Path(directory+f'/atom{seed}.pickle').open('rb') as f:s=pickle.load(f)
  import re
  code=(BASE.parent/f'Three/Cert/{module}.lean').read_text()
  for rid in map(int,re.findall(r'^def r(\d+) : Rule',code,re.M)):
   l,r=s['rules'][rid][:2]
   out.append((module+'.r'+str(rid),tuple(s['letters'][x] for x in l),tuple(s['letters'][x] for x in r)))
 for k,(l,r) in enumerate(local(9)):
  out.append(('paira'+str(k),l,r))
  out.append(('pairb'+str(k),tuple(3 if g==2 else g for g in l),tuple(3 if g==2 else g for g in r)))
 return out

def run(seed,seconds=300):
 out=Path(os.environ.get('CS3_WHITE_OUT','/tmp/acir-cs3-atom-white'));out.mkdir(exist_ok=True)
 cached=out/'base.pickle'
 if cached.exists():
  with cached.open('rb') as f:base=pickle.load(f)
 else:
  base=base_rules()
  with cached.open('wb') as f:pickle.dump(base,f)
 order=list(range(5));random.Random(seed).shuffle(order);kb=mod.KB(order,base)
 kb.pending=[]
 overlaps=kb.overlaps
 kb.overlaps=lambda a,b:None
 for name,l,r in base:kb.process(kb.enc(l),kb.enc(r),('base',name))
 kb.overlaps=overlaps
 live=list(kb.index.values())
 for a in live:
  for b in live:kb.overlaps(a,b)
 A=(1,2,0,1,3,3,3,1,2,2,2,0,1,3);CX=(1,2,2,1,0);R=CX+(3,)+CX+(3,3,3)
 NW=(1,4,4,2,2,3,3)+R+(0,1)
 TR=(1,)+R+(0,1)
 ZW=(4,4,2,2,3,3)+R
 targets=[('sign_white',ZW+TR,TR+ZW)] if os.environ.get('CS3_WHITE_GOAL')=='sign' else [('comm_white',A+NW,NW+A)]
 goals=[(n,kb.enc(l),kb.enc(r)) for n,l,r in targets]
 start=time.monotonic();last=start;steps=0;solved={}
 while kb.pending and time.monotonic()-start<seconds:
  m,_,u,v,p=heapq.heappop(kb.pending)
  if m>28:continue
  kb.process(u,v,p);steps+=1
  if time.monotonic()-last>15:
   for n,l,r in goals:
    nl,sl=kb.reduce(l);nr,sr=kb.reduce(r)
    if nl==nr:solved[n]=sl+kb.invert(sr)
   print(seed,'steps',steps,'rules',len(kb.index),'pending',len(kb.pending),'solved',list(solved),'seconds',int(time.monotonic()-start),flush=True)
   last=time.monotonic()
   if solved or len(kb.pending)>12000000 or len(kb.index)>24000:break
 for n,l,r in goals:
  nl,sl=kb.reduce(l);nr,sr=kb.reduce(r)
  if nl==nr:solved[n]=sl+kb.invert(sr)
 state={'letters':order,'base':base,'rules':kb.rules,'solved':solved,'targets':targets}
 with (out/f'white{seed}.pickle').open('wb') as f:pickle.dump(state,f)
 print('FINAL',seed,list(solved),flush=True)

if __name__=='__main__':run(int(sys.argv[1]))

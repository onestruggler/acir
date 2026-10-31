#!/usr/bin/env python3
"""Completion with a named controlled sign and previously proved equations.

This search records derivations; matrix equality is used only for local
two-qubit base identities already certified by Two.complete2.
"""
from pathlib import Path
import sys,heapq,pickle,time,importlib.util,random
from base_rules import equations
from three_words import ccZ,ccX,CX,SW,CS
ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('cskb',ROOT.parents[1]/'Minimality/gen/cskb.py')
mod=importlib.util.module_from_spec(spec);sys.modules['cskb']=mod;spec.loader.exec_module(mod)
GLOBALS=(0,1,2,7,8)
def run(seed,seconds):
 out=Path('/tmp/acir-cs3-monomial-named');out.mkdir(exist_ok=True)
 with Path('/tmp/acir-cs3-toffoli-seeded/localbase.pickle').open('rb')as f:base=pickle.load(f)
 def conv(w):return tuple(GLOBALS.index(g)for g in w)
 Q=5;A=6;X=7;C=8;S=9
 defs=[('aDef',conv(CX(0,1)),(A,)),('xDef',conv(CX(1,0)),(X,)),
       ('swapDef',(A,X,A),(S,)),
       ('cDef',(S,4,S),(C,)),('qDef',(C,C,C,A,4,A,4,4,4),(Q,))]
 base+=defs
 base += [
  ('aSquare',(A,A),()),('xSquare',(X,X),()),('axBraid',(A,X,A),(X,A,X)),
  ('bX',(4,X),(X,4)),('cConj',(C,),(X,A,4,A,X)),
  ('cSquare',(C,C),(A,4,4,A,4,4)),('qSquare',(Q,Q),()),
  ('qB',(Q,4),(4,Q)),('cB',(C,4),(4,C)),('cD',(C,3),(3,C)),
  ('qD',(Q,3),(3,Q)),('qSwap',(S,Q,S),(Q,)),
  ('qX',(X,Q,X),(Q,4,4)),
  ('tX',(1,Q,0,1,X),(X,1,Q,0,1))]
 order=list(range(10));random.Random(seed).shuffle(order)
 kb=mod.KB(order,base);kb.pending=[]
 old=kb.overlaps;kb.overlaps=lambda a,b:None
 for name,l,r in base:kb.process(kb.enc(l),kb.enc(r),('base',name))
 kb.overlaps=old
 for a in list(kb.index.values()):
  for b in list(kb.index.values()):kb.overlaps(a,b)
 t0=(1,Q,0,1);t1=(2,Q,0,2)
 targets=[('braid',t0+t1+t0,t1+t0+t1),('six',(Q,1,2)*6,(0,0)),
          ('aConjToffoli',(A,)+t0+(A,),t1+t0+t1)]
 goals=[(n,kb.enc(l),kb.enc(r))for n,l,r in targets]
 start=time.time();last=start;steps=0;solved={}
 def save():
  nonlocal last
  for n,l,r in goals:
   nl,sl=kb.reduce(l);nr,sr=kb.reduce(r)
   if nl==nr:solved[n]=sl+kb.invert(sr)
  print(seed,'steps',steps,'rules',len(kb.index),'pending',len(kb.pending),'solved',list(solved),'secs',int(time.time()-start),flush=True)
  with(out/f'run{seed}.pickle').open('wb')as f:pickle.dump({'letters':order,'globals':GLOBALS,'base':base,'rules':kb.rules,'solved':solved,'targets':targets},f)
  last=time.time()
 print('START',seed,len(base),flush=True)
 while kb.pending and time.time()-start<seconds:
  m,_,u,v,p=heapq.heappop(kb.pending)
  if m>26:continue
  kb.process(u,v,p);steps+=1
  if time.time()-last>30:
   save()
   if solved:break
  if len(kb.pending)>4000000 or len(kb.index)>18000:break
 save()
if __name__=='__main__':run(int(sys.argv[1]),int(sys.argv[2]) if len(sys.argv)>2 else 300)


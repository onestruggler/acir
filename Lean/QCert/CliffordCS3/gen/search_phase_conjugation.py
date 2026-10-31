#!/usr/bin/env python3
"""Find four-letter phase-conjugation certificates for a controlled exchange."""
import heapq, pickle, random, sys, time, json
from pathlib import Path
import search_white as sw
import search_atom as sa

OUT = Path('/tmp/acir-cs3-phase-conjugation')
OUT.mkdir(exist_ok=True)

def run(seed, seconds=180):
    base=[]
    for module,seed0 in [('AtomRelations',12),('AtomNegative',12),('SignNegative',6)]:
        s=json.loads((sw.BASE/'data'/f'{module}-seed{seed0}.json').read_text())
        for rid,(l,r,_,_) in s['rules'].items():
            base.append((module+'.r'+rid,tuple(s['letters'][x] for x in l),tuple(s['letters'][x] for x in r)))
    for n,l,r in sa.local_rules():
        base.append((n+'a',l,r))
        base.append((n+'b',tuple(3 if x==2 else x for x in l),tuple(3 if x==2 else x for x in r)))
    order=list(range(4)); random.Random(seed).shuffle(order)
    kb=sw.mod.KB(order,base); kb.pending=[]
    overlaps=kb.overlaps; kb.overlaps=lambda a,b:None
    for name,l,r in base:kb.process(kb.enc(l),kb.enc(r),('base',name))
    kb.overlaps=overlaps
    live=list(kb.index.values())
    for a in live:
        for b in live:kb.overlaps(a,b)
    CX=(1,2,2,1,0);R=CX+(3,)+CX+(3,3,3)
    TR=(1,)+R+(0,1)
    targets=[('d_conj',(2,)+TR+(2,2,2),TR+R),('b_conj',(3,)+TR+(3,3,3),TR+R)]
    goals=[(n,kb.enc(l),kb.enc(r)) for n,l,r in targets]
    start=time.monotonic();last=start;steps=0;solved={}
    while kb.pending and time.monotonic()-start<seconds:
        m,_,u,v,p=heapq.heappop(kb.pending)
        if m>26:continue
        kb.process(u,v,p);steps+=1
        if time.monotonic()-last>10:
            for n,l,r in goals:
                nl,sl=kb.reduce(l);nr,sr=kb.reduce(r)
                if nl==nr:solved[n]=sl+kb.invert(sr)
            print(seed,steps,len(kb.index),len(kb.pending),list(solved),int(time.monotonic()-start),flush=True)
            last=time.monotonic()
            if len(solved)==2 or len(kb.pending)>3500000 or len(kb.index)>12000:break
    for n,l,r in goals:
        nl,sl=kb.reduce(l);nr,sr=kb.reduce(r)
        if nl==nr:solved[n]=sl+kb.invert(sr)
    state={'letters':order,'base':base,'rules':kb.rules,'solved':solved,'targets':targets}
    with (OUT/f'phase{seed}.pickle').open('wb') as f:pickle.dump(state,f)
    print('FINAL',seed,list(solved),flush=True)

if __name__=='__main__':run(int(sys.argv[1]))

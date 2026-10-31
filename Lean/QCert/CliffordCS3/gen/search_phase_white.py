#!/usr/bin/env python3
"""Search the phase commutation on a white controlled branch."""
import heapq, pickle, random, sys, time
from pathlib import Path
import search_white as sw

OUT = Path('/tmp/acir-cs3-phase-white')
OUT.mkdir(exist_ok=True)

def run(seed, seconds=240):
    with Path('/tmp/acir-cs3-atom-white/base.pickle').open('rb') as f:
        base=pickle.load(f)
    order=list(range(5)); random.Random(seed).shuffle(order)
    kb=sw.mod.KB(order,base); kb.pending=[]
    overlaps=kb.overlaps; kb.overlaps=lambda a,b:None
    for name,l,r in base:kb.process(kb.enc(l),kb.enc(r),('base',name))
    kb.overlaps=overlaps
    live=list(kb.index.values())
    for a in live:
        for b in live:kb.overlaps(a,b)
    CX=(1,2,2,1,0);R=CX+(3,)+CX+(3,3,3)
    TR=(1,)+R+(0,1)
    W=(3,3,3,4)
    targets=[('phase_white',W+TR,TR+W)]
    goals=[(n,kb.enc(l),kb.enc(r)) for n,l,r in targets]
    start=time.monotonic();last=start;steps=0;solved={}
    while kb.pending and time.monotonic()-start<seconds:
        m,_,u,v,p=heapq.heappop(kb.pending)
        if m>28:continue
        kb.process(u,v,p);steps+=1
        if time.monotonic()-last>10:
            for n,l,r in goals:
                nl,sl=kb.reduce(l);nr,sr=kb.reduce(r)
                if nl==nr:solved[n]=sl+kb.invert(sr)
            print(seed,steps,len(kb.index),len(kb.pending),list(solved),int(time.monotonic()-start),flush=True)
            last=time.monotonic()
            if solved or len(kb.pending)>5000000 or len(kb.index)>15000:break
    for n,l,r in goals:
        nl,sl=kb.reduce(l);nr,sr=kb.reduce(r)
        if nl==nr:solved[n]=sl+kb.invert(sr)
    state={'letters':order,'base':base,'rules':kb.rules,'solved':solved,'targets':targets}
    with (OUT/f'phase{seed}.pickle').open('wb') as f:pickle.dump(state,f)
    print('FINAL',seed,list(solved),flush=True)

if __name__=='__main__':run(int(sys.argv[1]))

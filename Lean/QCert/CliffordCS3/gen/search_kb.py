#!/usr/bin/env python3
"""Independent proof-producing completion runs for the coset equations.

All initial equations are Figure 2, in Replay.baseRules order. A successful
search exports a DAG of rewrites over those equations for Lean replay.
"""
import sys, importlib.util, heapq, time, json, pickle, random
from pathlib import Path
from base_rules import equations
BASE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('cskb',BASE.parents[1]/'Minimality/gen/cskb.py')
mod=importlib.util.module_from_spec(spec);sys.modules['cskb']=mod;spec.loader.exec_module(mod)
def run(seed,seconds=600):
    orders=[list(range(9)),[0,4,5,6,7,8,1,2,3],[0,7,8,4,5,6,1,2,3],
            [0,1,2,3,8,7,6,5,4],[0,3,2,1,6,5,4,8,7]]
    if seed<len(orders):order=orders[seed]
    else:
        order=list(range(1,9));random.Random(seed).shuffle(order);order=[0]+order
    kb=mod.KB(order,equations())
    goals=json.loads((BASE/'coset_obligations.json').read_text())
    goalwords=[(g,kb.enc(g['lhs']),kb.enc(g['rhs'])) for g in goals]
    solved={};start=time.time();last=start;steps=0;maxlen=24
    out=Path('/tmp/acir-cs3-kb');out.mkdir(exist_ok=True)
    def checkpoint():
        nonlocal last
        for g,l,r in goalwords:
            if g['name'] not in solved:
                nl,sl=kb.reduce(l);nr,sr=kb.reduce(r)
                if nl==nr:solved[g['name']]=sl+kb.invert(sr)
        print(seed,'steps',steps,'rules',len(kb.index),'total',len(kb.rules),'queue',len(kb.pending),
              'solved',len(solved),list(solved),'secs',round(time.time()-start),flush=True)
        state={'letters':kb.letters,'rules':kb.rules,'solved':solved}
        with (out/f'run{seed}.pickle').open('wb') as f:pickle.dump(state,f)
        (out/f'run{seed}.json').write_text(json.dumps({'solved':list(solved),'steps':steps,'rules':len(kb.index)}))
        last=time.time()
    while kb.pending and time.time()-start<seconds:
        m,_,u,v,proof=heapq.heappop(kb.pending)
        if m>maxlen:continue
        kb.process(u,v,proof);steps+=1
        if time.time()-last>20:checkpoint()
        if len(kb.index)>6000 or len(kb.pending)>1500000:break
    checkpoint()
if __name__=='__main__':run(int(sys.argv[1]),int(sys.argv[2]) if len(sys.argv)>2 else 600)


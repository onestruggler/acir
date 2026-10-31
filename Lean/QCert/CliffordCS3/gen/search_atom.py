#!/usr/bin/env python3
"""Small-alphabet completion for the controlled-commutator identity."""
import sys,heapq,pickle,time,importlib.util,json,random,os
from pathlib import Path
from pair_normalize import left,identity
BASE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('cskb',BASE.parents[1]/'Minimality/gen/cskb.py')
mod=importlib.util.module_from_spec(spec);sys.modules['cskb']=mod;spec.loader.exec_module(mod)

def word(*xs):return sum((tuple(x) for x in xs),())

def local_rules(depth=9):
    # Abstract0=i,1=K1,2=CS01,3=CS12. Local evaluation treatsK aslowerqubit.
    seen={identity():()};front=[identity()];rules=[]
    conv={0:0,1:2,2:5}
    for d in range(depth):
        nxt=[]
        for key in front:
            w=seen[key]
            for g in range(3):
                z=left(conv[g],key);nw=(g,)+w
                if z not in seen:seen[z]=nw;nxt.append(z)
                elif seen[z]!=nw:
                    old=seen[z]
                    rules.append((f'pair{len(rules)}',nw,old))
        front=nxt
    return rules

def run(seed,seconds=240):
    start=time.monotonic();last=start
    out=Path(os.environ.get('CS3_ATOM_OUT','/tmp/acir-cs3-atom'));out.mkdir(exist_ok=True)
    rules=local_rules()
    br=[]
    for name,l,r in rules:
        br.append((name+'a',l,r));br.append((name+'b',tuple(3 if g==2 else g for g in l),tuple(3 if g==2 else g for g in r)))
    br += [('c12',(3,2),(2,3)),
           ('c16',(3,1,3,1,2,1,2),(2,1,2,1,3,1,3)),
           ('c17',(3,1,3,3,3,1,2,1,3),(2,1,2,2,2,1,3,1,2))]
    order=[0,1,2,3];random.Random(seed).shuffle(order)
    kb=mod.KB(order,br)
    A=(1,2,0,1,3,3,3,1,2,2,2,0,1,3)
    CX=(1,2,2,1,0)
    P2=CX+(3,3)+CX+(3,3)
    R=CX+(3,)+CX+(3,3,3)
    NA=(1,3,3)+R+(0,1)
    NB=(1,2,2)+R+(0,1)
    TR=(1,)+R+(0,1)
    targets=[('cube',A*3,P2),('conjugate_sign',A+R,(1,)+R+(0,1)+A),
             ('triangle',(R+A)*3,P2),('comm_negA',A+NA,NA+A),('comm_negB',A+NB,NB+A),
             ('sign_negA',(3,3)+R+TR,TR+(3,3)+R),('sign_negB',(2,2)+R+TR,TR+(2,2)+R)]
    goals=[(n,kb.enc(l),kb.enc(r)) for n,l,r in targets]
    steps=0;solved={}
    while kb.pending and time.monotonic()-start<seconds:
        m,_,u,v,p=heapq.heappop(kb.pending)
        if m>26:continue
        kb.process(u,v,p);steps+=1
        if time.monotonic()-last>15:
            for n,l,r in goals:
                nl,sl=kb.reduce(l);nr,sr=kb.reduce(r)
                if nl==nr:solved[n]=sl+kb.invert(sr)
            print(seed,'steps',steps,'rules',len(kb.index),'pending',len(kb.pending),'solved',list(solved),'seconds',int(time.monotonic()-start),flush=True)
            last=time.monotonic()
            if len(solved)==len(goals) or len(kb.pending)>3500000 or len(kb.index)>10000:break
    for n,l,r in goals:
        nl,sl=kb.reduce(l);nr,sr=kb.reduce(r)
        if nl==nr:solved[n]=sl+kb.invert(sr)
        print('NORMALS',seed,n,list(nl),list(nr),flush=True)
    state={'letters':order,'base':br,'rules':kb.rules,'solved':solved,'targets':targets}
    with (out/f'atom{seed}.pickle').open('wb') as f:pickle.dump(state,f)
    print('FINAL',seed,'solved',list(solved),'secs',int(time.monotonic()-start),flush=True)

if __name__=='__main__':run(int(sys.argv[1]),int(sys.argv[2]) if len(sys.argv)>2 else 240)

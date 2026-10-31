#!/usr/bin/env python3
"""Finite group of the residual one-qubit Clifford atoms, with proof search.

The five input identities must be instantiated by independently proved
three-qubit equations. No matrix equality is treated as a base axiom.
"""
from pathlib import Path
import sys,importlib.util,pickle,json
BASE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('cskb',BASE.parents[1]/'Minimality/gen/cskb.py')
mod=importlib.util.module_from_spec(spec);sys.modules['cskb']=mod;spec.loader.exec_module(mod)


def act(c,g):
    # Alphabet0=P,1=Q,2=A,3=T. The final base equation definesT.
    T=(3,)
    if g=='T':return ((0,)+T+(1,) if c else T),c
    if g=='Z':return ((1,) if c else ()),not c
    if g=='K':return ((2,2,0) if c else (2,)),not c
    raise ValueError(g)


def run(c,w):
    out=()
    for g in w:
        v,c=act(c,g);out+=v
    return out,c


def main():
    base=[('p4',(0,)*4,()),('q2',(1,1),()),('a3',(2,2,2),(0,0)),
          ('pA',(0,2),(2,0)),('pQ',(0,1),(1,0)),('triangle',(1,2)*3,(0,0,0)),
          ('tdef',(3,),(2,1)+(2,)*5)]
    eqs={'T2':('TT',''),'Z4':('ZZZZ',''),'K8':('K'*8,''),'phase':('ZTZT','TZTZ'),
         'KZ2':('KZZ','TK'),'KZ3':('KZZZ','ZKZK'),'KP':('KTZTZ','TZTZK'),
         'K2P':('KKTZTZ','')}
    targets=[]
    for n,(l,r) in eqs.items():
        for c in [False,True]:
            a,ca=run(c,l);b,cb=run(c,r);assert ca==cb
            targets.append((n+str(int(c)),a,b))
    kb=mod.KB([0,1,2,3],base)
    kb.run(targets=[(l,r) for _,l,r in targets],maxrules=3000,report=500)
    solved={n:kb.proof_of(l,r) for n,l,r in targets}
    print('RESULTS',{n:None if p is None else len(p) for n,p in solved.items()})
    state={'letters':kb.letters,'base':base,'rules':kb.rules,'solved':solved,'targets':targets}
    with Path('/tmp/acir-cs3-local-block.pickle').open('wb') as f:pickle.dump(state,f)


if __name__=='__main__':main()

#!/usr/bin/env python3
"""Exact, non-proof audit of every finite obligation of the two-coset action."""
from pathlib import Path
import re,json
from three_words import *


def macro_axioms():
    s=(Path(__file__).resolve().parents[1]/'Macro8.lean').read_text()
    start=s.index('  ax := ')+len('  ax := ')
    i=start;depth=0
    while i<len(s):
        if s[i]=='[':depth+=1
        elif s[i]==']':
            depth-=1
            if depth==0:break
        i+=1
    s=s[start:i+1]
    result=[]
    for l,r in re.findall(r'\(\[([^]]*)\],\s*\[([^]]*)\]\)',s):
        def word(t):
            return [int(d) if d else (7 if z else 8) for d,z,k in re.findall(r'\.T\s+(\d+)|(\.Z)|(\.K)',t)]
        result.append((word(l),word(r)))
    return result


def action(c,g):
    if g<7:
        t=transposition(GRAY[g],GRAY[g+1])
        return ([8]+t+ccZ() if c and g==6 else t),c
    if g==7:return (ccZ() if c else []),not c
    return (atom()*2+[8] if c else atom()),not c


def run(c,w):
    result=[]
    for g in w:
        step,c=action(c,g);result+=step
    return result,c


def cases():
    for i,(l,r) in enumerate(macro_axioms()):
        for c in [False,True]:
            a,ca=run(c,l);b,cb=run(c,r)
            yield f'b{i:02d}_{int(c)}',a,b,ca==cb


if __name__=='__main__':
    allcases=[]
    for name,l,r,state in cases():
        matrix=eval_word(l)==eval_word(r)
        print(name,len(l),len(r),'OK' if state and matrix else 'FAIL')
        assert state and matrix,name
        allcases.append({'name':name,'lhs':l,'rhs':r})
    path=Path(__file__).resolve().parent/'coset_obligations.json'
    path.write_text(json.dumps(allcases))
    print('Checked',len(allcases),'finite equations; wrote',path)

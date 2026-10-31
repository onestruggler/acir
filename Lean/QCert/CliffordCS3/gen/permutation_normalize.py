"""Proof-producing Coxeter normalization, including the natural gate routes.

Every step is an involution, distant commutation, or adjacent braid.
The evaluator only checks the produced certificate; it supplies no proof.
"""
from pathlib import Path
import json, sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'ToffoliHadamard/gen'))
from model import LET, IDX, xAdj

def cx_rules():
    out = []
    for i in range(7):out.append(((i,i),(),f'inv{i}'))
    for i in range(7):
        for j in range(i+2,7):out.append(((i,j),(j,i),f'far{i}{j}'))
    for i in range(6):out.append(((i,i+1,i),(i+1,i,i+1),f'braid{i}'))
    return out

COX = cx_rules()
RULES = {name:i for i,(_,_,name) in enumerate(COX)}

def normalize(raw):
    w = list(raw)
    steps = []
    def rewrite(pos, name, reverse=False):
        rid = RULES[name]
        a,b,_ = COX[rid]
        if reverse:a,b=b,a
        assert tuple(w[pos:pos+len(a)]) == a, (w,pos,name,reverse)
        w[pos:pos+len(a)] = b
        steps.append((pos,rid,reverse))
    def commute(pos):
        a,b=w[pos:pos+2]
        assert abs(a-b)>1
        rewrite(pos, f'far{min(a,b)}{max(a,b)}',a>b)
    def insert(start,end,m):
        # The canonical prefix w[start:end] is followed by the added letter.
        g=w[end]
        assert g<=m
        if m not in w[start:end]:
            if g != m:insert(start,end,m-1)
            return
        s=w.index(m,start,end)
        k=w[end-1]
        assert w[s:end] == list(range(m,k-1,-1))
        if g < k-1:
            for p in range(end-1,s-1,-1):commute(p)
            insert(start,s,m-1)
        elif g == k-1:
            return
        elif g == k:
            rewrite(end-1,f'inv{k}')
        else:
            # Bring the new s_g next to s_(g-1), braid, and move s_(g-1) out.
            for p in range(end-1,s+m-g+1,-1):commute(p)
            p=s+m-g
            rewrite(p,f'braid{g-1}',True)
            for p in range(s+m-g-1,s-1,-1):commute(p)
            insert(start,s,m-1)
    n=0
    for g in raw:
        # Start from the canonical prefix plus the untouched original suffix.
        before=len(w)
        insert(0,n,6)
        n += 1 + len(w)-before
    assert n==len(w)
    return tuple(w),steps

routes = json.loads((ROOT/'ToffoliHadamard/gen/data/routes.json').read_text())['routes']
routes = {x:p for x,p in routes}
def natural(g):
    out=[]
    for kind,v in routes[g]:
        if kind=='L':out.extend(natural(v))
        else:
            assert v[0]=='T', (g,v)
            out.append(v[1])
    return out

TOKENS = [ ['X1','CCX12','X1'],
    ['X0','X1','CCX01','X1','X0'],
    ['X1','X2','CCX12','X2','X1'],
    ['X2','CCX02','X2'], ['X2','CCX12','X2'],
    ['X0','CCX01','X0'], ['CCX12']]
def token(d):return sum((natural(g) for g in TOKENS[d]), [])

def permutation(w):
    a=list(range(8))
    for i in w:a[i],a[i+1]=a[i+1],a[i]
    return tuple(a)

if __name__=='__main__':
    import random
    for _ in range(1000):
        w=[random.randrange(7) for _ in range(random.randrange(100))]
        n,steps=normalize(w)
        assert permutation(w)==permutation(n)
    print('Coxeter normalization checked on 1000 random words')
    for i in range(7):
        n,st=normalize(token(i))
        print(i,len(token(i)),n,len(st))

#!/usr/bin/env python3
"""Certificate-producing local simplification via proved two-qubit completeness.

The output records windows with equal exact matrices. Lean's pairRule
rechecks each such equality and obtains its derivation from complete2.
"""
from pathlib import Path
import pickle,collections,time,json,sys

ROOT=Path(__file__).resolve().parent
CACHE=Path('/tmp/acir-cs3-pair-normalforms.pickle')
PAIRS=((0,1,2,4,5,7),(0,2,3,5,6,8))
SUPPORT=(0,4,2,1,4,2,1,6,3)


def identity():
    return tuple(v for i in range(4) for j in range(4) for v in (int(i==j),0))+(0,)


def left(g,key):
    ex=key[-1];a=key[:-1]
    if g in (1,2):
        bit=3-g;out=list(a)
        for i in range(4):
            if i&bit:continue
            for j in range(4):
                k=8*i+2*j;l=8*(i|bit)+2*j
                x,y=a[k:k+2];u,v=a[l:l+2]
                out[k:k+2]=(x+u+y+v,y+v-x-u)
                out[l:l+2]=(x-u+y-v,y-v-x+u)
        ex+=1
        while ex and all(v%2==0 for v in out):out=[v//2 for v in out];ex-=1
    else:
        out=list(a)
        for i in range(4):
            phase=g==0 or (g==3 and bool(i&2)) or (g==4 and bool(i&1)) or (g==5 and i==3)
            if phase:
                for j in range(4):
                    k=8*i+2*j;x,y=a[k:k+2];out[k:k+2]=(-y,x)
    return tuple(out)+(ex,)


def evaluate(word):
    result=identity()
    for g in reversed(word):result=left(g,result)
    return result


def make_cache(depth=8):
    seen={identity():()};front=[identity()];start=time.time()
    for d in range(depth):
        nxt=[]
        for key in front:
            w=seen[key]
            for g in range(6):
                q=left(g,key);nw=(g,)+w
                if q not in seen:seen[q]=nw;nxt.append(q)
                elif len(seen[q])==len(nw) and nw<seen[q]:seen[q]=nw
        front=nxt
        print('depth',d+1,'new',len(nxt),'total',len(seen),'seconds',round(time.time()-start,1),flush=True)
    with CACHE.open('wb') as f:pickle.dump(seen,f,protocol=5)
    return seen


_cache=None
def cache():
    global _cache
    if _cache is None:
        with CACHE.open('rb') as f:_cache=pickle.load(f)
    return _cache


def canonical(word):return cache().get(evaluate(tuple(word)))


def normalize(word,limit=200000):
    w=tuple(word);steps=[]
    for _ in range(limit):
        changed=False
        # Merge commuting disjoint gates, including the scalar, in a stable order.
        for p in range(len(w)-1):
            a,b=w[p:p+2]
            if a>b and (not SUPPORT[a]&SUPPORT[b] or (a>=4 and b>=4)):
                w=w[:p]+(b,a)+w[p+2:];steps.append(('comm',a,b,p));changed=True;break
        if changed:continue
        for j,mapping in enumerate(PAIRS):
            inv={g:k for k,g in enumerate(mapping)}
            p=0
            while p<len(w):
                if w[p] not in inv:p+=1;continue
                end=p
                while end<len(w) and w[end] in inv:end+=1
                run=w[p:end]
                # Prefer a complete maximal run, then bounded subwindows.
                candidates=[(p,end)]
                candidates += [(a,min(end,a+size)) for size in range(min(12,end-p),1,-1)
                               for a in range(p,end-size+1)]
                for a,b in candidates:
                    old=w[a:b];small=tuple(inv[g] for g in old)
                    nf=canonical(small)
                    if nf is None:continue
                    new=tuple(mapping[g] for g in nf)
                    if (len(new),new)<(len(old),old):
                        steps.append(('pair',j,list(small),list(nf),a))
                        w=w[:a]+new+w[b:];changed=True;break
                if changed:break
                p=end
            if changed:break
        if not changed:return w,steps
    raise RuntimeError('normalization limit exceeded')


def normalize_case(case):
    a,sa=normalize(case['lhs']);b,sb=normalize(case['rhs'])
    return {**case,'left_nf':a,'right_nf':b,'left_steps':sa,'right_steps':sb,'solved':a==b}


if __name__=='__main__':
    if len(sys.argv)>1 and sys.argv[1]=='cache':make_cache(int(sys.argv[2]) if len(sys.argv)>2 else 8)
    else:
        cases=json.loads((ROOT/'coset_obligations.json').read_text())
        if len(sys.argv)>1:cases=[c for c in cases if c['name'] in sys.argv[1:]]
        for c in cases:
            r=normalize_case(c)
            (ROOT/(c['name']+'.normal.json')).write_text(json.dumps(r))
            print(c['name'],r['solved'],len(r['left_nf']),len(r['right_nf']),
                  len(r['left_steps']),len(r['right_steps']),flush=True)

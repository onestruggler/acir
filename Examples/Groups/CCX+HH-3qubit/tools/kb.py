"""Search for derivations; retain every rewriting certificate.

This is an untrusted search tool, not part of the trusted Agda kernel.
It never treats equal matrices as a circuit derivation.
"""
import generate as g
import heapq, json, time
import sys
from collections import deque
from pathlib import Path

rank={x:i for i,x in enumerate(g.GATES)}
def key(w): return len(w),tuple(rank[x] for x in w)
rules=[]; pending=[]; seen=set(); serial=0; certificates=[]; byhead={}
PERM='--permutation' in sys.argv
FULL='--full' in sys.argv
LIMIT=int(sys.argv[sys.argv.index('--seconds')+1]) if '--seconds' in sys.argv else 480

def normalize(w):
    w=tuple(w); path=[]
    for _ in range(20000):
        found=False
        for pos in range(len(w)):
            for i in byhead.get(w[pos],[]):
                l,r=rules[i]
                if w[pos:pos+len(l)]==l:
                    path.append((i,pos)); w=w[:pos]+r+w[pos+len(l):]
                    found=True; break
            if found: break
        if not found: return w,path
    raise RuntimeError('normalization bound')

def queue(l,r,cert):
    global serial
    if l==r: return
    k=(l,r) if key(l)>key(r) else (r,l)
    if k in seen: return
    seen.add(k); serial+=1
    heapq.heappush(pending,(max(len(l),len(r)),len(l)+len(r),serial,l,r,cert))

def add(l,r,cert):
    if key(l)<key(r): l,r=r,l; cert={'sym':cert}
    idx=len(rules); rules.append((l,r)); certificates.append(cert)
    byhead.setdefault(l[0],[]).append(idx)
    for j,(u,v) in enumerate(rules):
        for i,k in ((idx,j),(j,idx)) if idx!=j else ((idx,j),):
            a,b=rules[i]; c,d=rules[k]
            for offset in range(-len(c)+1,len(a)):
                start=min(0,offset); end=max(len(a),offset+len(c))
                if end-start>30: continue
                word=[None]*(end-start)
                for p,x in enumerate(a): word[p-start]=x
                valid=True
                for p,x in enumerate(c):
                    q=p+offset-start
                    if word[q] is not None and word[q]!=x: valid=False;break
                    word[q]=x
                if not valid: continue
                word=tuple(word); pa=-start;pc=offset-start
                lhs=word[:pa]+b+word[pa+len(a):]
                rhs=word[:pc]+d+word[pc+len(c):]
                queue(lhs,rhs,{'overlap':[list(word),i,pa,k,pc]})

if PERM:
    dataset=json.loads((Path(__file__).parent/'tietze-parsed.json').read_text())
    for name,(l,r,_) in dataset['raw'].items():
        if all(x.startswith(('X','CX','CCX','SWAP')) for x in l+r):
            queue(tuple(l),tuple(r),{'tietze':name})
    for name,(l,r) in dataset['base'].items():
        if all(x.startswith(('X','CX','CCX','SWAP')) for x in l+r):
            n=dataset['matches'][name]
            queue(tuple(l),tuple(r),{'axiom':n} if n else {'pauli':True})
else:
    for n,(l,r) in (list(g.RELATIONS.items()) if FULL else list(g.RELATIONS.items())[:46]):
        queue(tuple(g.expand(l)),tuple(g.expand(r)),{'axiom':n})
    if FULL:
        dataset=json.loads((Path(__file__).parent/'tietze-parsed.json').read_text())
        for name,(l,r,_) in dataset['raw'].items():
            queue(tuple(l),tuple(r),{'tietze':name})

ts=[tuple(g.expand('t'+str(i)+str(i+1))) for i in range(7)]
goals={}
for i in range(7): goals[f'invol{i}']=(ts[i]+ts[i],())
for i in range(7):
    for j in range(i+2,7): goals[f'comm{i}{j}']=(ts[i]+ts[j],ts[j]+ts[i])
for i in range(6): goals[f'braid{i}']=(ts[i]+ts[i+1]+ts[i],ts[i+1]+ts[i]+ts[i+1])
if FULL:goals={'K-definition':(('K12',),('NK','X0','NK','X0'))}

start=time.monotonic(); last=start; solved={}
while pending and len(rules)<6000 and time.monotonic()-start<LIMIT:
    _,_,_,l,r,cert=heapq.heappop(pending)
    nl,pl=normalize(l);nr,pr=normalize(r)
    if nl!=nr:
        if len(nl)>30 or len(nr)>30: continue
        add(nl,nr,{'reduce':[list(l),list(r),cert,pl,pr]})
    if time.monotonic()-last>5:
        for name,(a,b) in goals.items():
            if name in solved: continue
            na,pa=normalize(a);nb,pb=normalize(b)
            if na==nb: solved[name]=[pa,pb]
        print('rules',len(rules),'pending',len(pending),'goals',len(solved),'/',len(goals),flush=True)
        last=time.monotonic()
        if len(solved)==len(goals): break
out={'rules':[[list(l),list(r)] for l,r in rules], 'certificates':certificates,
     'goals':{k:[list(a),list(b)] for k,(a,b) in goals.items()},'solved':solved}
(Path(__file__).parent/('glue-certificates.json' if FULL else 'permutation-certificates.json' if PERM else 'kb-certificates.json')).write_text(json.dumps(out))
print('Finished:',len(solved),'of',len(goals),'goals',flush=True)

#!/usr/bin/env python3
"""Proof-producing normal forms for the amalgam of the two adjacent-pair groups.

Only equations on an adjacent pair are used. Each normalization step
records a two-qubit matrix equality, to be replayed through pairRule.
This is a search aid, not an assumption about three-qubit completeness.
"""
from pathlib import Path
import functools,collections,pickle
import pair_normalize as pn
from three_words import inverse
HGEN=(0,2,5)
def product(a,b):
    x=a[:-1];y=b[:-1];out=[];e=a[-1]+b[-1]
    for i in range(4):
      for j in range(4):
        re=im=0
        for k in range(4):
          ar,ai=x[8*i+2*k:8*i+2*k+2];br,bi=y[8*k+2*j:8*k+2*j+2]
          re+=ar*br-ai*bi;im+=ar*bi+ai*br
        out.extend((re,im))
    while e and all(v%2==0 for v in out):out=[v//2 for v in out];e-=1
    return tuple(out)+(e,)
@functools.lru_cache(maxsize=300000)
def evaluate(j,w):
    inv={g:k for k,g in enumerate(pn.PAIRS[j])}
    return pn.evaluate(tuple(inv[g]for g in w))
class Normalizer:
 def __init__(self):
    I=pn.identity();seen={I:()};queue=collections.deque([I])
    while queue:
      key=queue.popleft();w=seen[key]
      for g in HGEN:
        nw=(g,)+w;nkey=evaluate(0,nw)
        if nkey not in seen:seen[nkey]=nw;queue.append(nkey)
    self.hwords=list(seen.values())
    self.hmats=[[evaluate(j,w)for w in self.hwords]for j in range(2)]
    self.hlookup=[{k:i for i,k in enumerate(row)}for row in self.hmats]
    self.hinvs=[self.hlookup[0][evaluate(0,tuple(inverse(w)))]for w in self.hwords]
    self.reps=[{},{}];self.decomp=[{},{}];self.normalcache={}
    self.hcols=[[[[(k,key[8*k+2*j],key[8*k+2*j+1])for k in range(4)if key[8*k+2*j]or key[8*k+2*j+1]]for j in range(4)]for key in row]for row in self.hmats]
 def mulH(self,j,g,h):
    x=g[:-1];out=[];e=g[-1]+self.hmats[j][h][-1]
    for i in range(4):
      for col in self.hcols[j][h]:
        re=im=0
        for k,br,bi in col:
          ar,ai=x[8*i+2*k:8*i+2*k+2];re+=ar*br-ai*bi;im+=ar*bi+ai*br
        out.extend((re,im))
    while e and all(v%2==0 for v in out):out=[v//2 for v in out];e-=1
    return tuple(out)+(e,)
 def split(self,j,key,w):
    if key in self.hlookup[j]:return None,self.hlookup[j][key]
    if key in self.decomp[j]:return self.decomp[j][key]
    choices=[self.mulH(j,key,h)for h in range(len(self.hwords))]
    hi=min(range(len(choices)),key=lambda h:(choices[h][-1],choices[h][:-1]))
    rep=choices[hi];tail=self.hinvs[hi]
    if rep not in self.reps[j]:
      nf=pn.cache().get(rep)
      rw=tuple(pn.PAIRS[j][g]for g in nf)if nf is not None else w+self.hwords[hi]
      self.reps[j][rep]=rw
    self.decomp[j][key]=(rep,tail)
    return rep,tail
 def normalized(self,w):
    w=tuple(w)
    if w in self.normalcache:return self.normalcache[w]
    chunks=[];i=0
    while i<len(w):
      k=i
      while k<len(w)and w[k]in HGEN:k+=1
      j=0 if k==len(w)or w[k]in pn.PAIRS[0]else 1
      end=i
      while end<len(w)and w[end]in pn.PAIRS[j]:end+=1
      chunks.append((j,w[i:end]));i=end
    stack=[];tail=0;steps=[]
    for j,chunk in chunks:
      left=()
      if stack and stack[-1][0]==j:
        _,key=stack.pop();left=self.reps[j][key]
      pos=sum(len(self.reps[k][key])for k,key in stack)
      old=left+self.hwords[tail]+chunk
      key=evaluate(j,old);rep,tail=self.split(j,key,old)
      new=(()if rep is None else self.reps[j][rep])+self.hwords[tail]
      if old!=new:
        inv={g:k for k,g in enumerate(pn.PAIRS[j])}
        steps.append(('pair',j,tuple(inv[g]for g in old),tuple(inv[g]for g in new),pos))
      if rep is not None:stack.append((j,rep))
    key=tuple(stack)+(tail,)
    out=tuple(g for j,k in stack for g in self.reps[j][k])+self.hwords[tail]
    # Independently replay substitutions to check positions.
    replay=w
    for _,j,old,new,pos in steps:
      a=tuple(pn.PAIRS[j][g]for g in old);b=tuple(pn.PAIRS[j][g]for g in new)
      assert replay[pos:pos+len(a)]==a
      assert pn.evaluate(old)==pn.evaluate(new)
      replay=replay[:pos]+b+replay[pos+len(a):]
    assert replay==out
    self.normalcache[w]=(key,out,steps)
    return key,out,steps
if __name__=='__main__':
 import json,time
 start=time.monotonic();N=Normalizer();print('INTERSECTION_SIZE',len(N.hwords),flush=True)
 cases=json.loads((Path(__file__).parent/'coset_obligations.json').read_text())
 for c in cases:
  a,aw,sa=N.normalized(c['lhs']);b,bw,sb=N.normalized(c['rhs'])
  print(c['name'],a==b,'blocks',len(a)-1,len(b)-1,'wordlen',len(aw),len(bw),flush=True)
 print('SECONDS',round(time.monotonic()-start,1))
 with Path('/tmp/acir-cs3-amalgam.pickle').open('wb')as f:pickle.dump(N,f)


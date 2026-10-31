#!/usr/bin/env python3
"""Cyclic relation search in the adjacent-pair amalgam normal forms."""
from pathlib import Path
import sys,pickle,time,json,heapq
from amalgam_normalize import Normalizer
from search_amalgam import initial_rules
from three_words import inverse
ROOT=Path(__file__).parent
def prepare(N):
 out=[];seen=set()
 for rid,(name,l,r)in enumerate(initial_rules()):
  word=tuple(l)+tuple(inverse(r))
  key,w,_=N.normalized(word);factors=key[:-1]
  chunks=[N.reps[j][m]for j,m in factors]
  for rot in range(len(chunks)):
   pre=tuple(g for a in chunks[:rot]for g in a)
   post=tuple(g for a in chunks[rot:]for g in a)+N.hwords[key[-1]]
   rk,rw,_=N.normalized(post+pre)
   rc=[N.reps[j][m]for j,m in rk[:-1]]
   for cut in range(1,len(rc)):
    a=tuple(g for s in rc[:cut]for g in s)
    b=tuple(inverse(tuple(g for s in rc[cut:]for g in s)+N.hwords[rk[-1]]))
    ak,aw,_=N.normalized(a);bk,bw,_=N.normalized(b)
    if len(ak)<3 or len(bk)>len(ak)+2 or(ak,bk)in seen:continue
    seen.add((ak,bk));out.append((rid,rot,cut,ak,bk,aw,bw))
 return out
def search(name,seconds=180):
 N=Normalizer();rules=prepare(N);cases=json.loads((ROOT/'coset_obligations.json').read_text())
 case=next(c for c in cases if c['name']==name)
 word=tuple(case['lhs'])+tuple(inverse(case['rhs']))
 key,w,st=N.normalized(word);start=key;words={key:w};seen={key:None}
 queue=[(len(key),0,key)];serial=0;expanded=0;t0=time.monotonic();last=t0;best=len(key);found=None
 print('START',name,'blocks',len(key)-1,'rules',len(rules),flush=True)
 while queue and time.monotonic()-t0<seconds and len(seen)<100000:
  _,_,key=heapq.heappop(queue);expanded+=1
  factors=key[:-1];tail=key[-1];w=words[key]
  fw=[N.reps[j][m]for j,m in factors];pref=[0]
  for s in fw:pref.append(pref[-1]+len(s))
  # Cyclic conjugation preserves being the identity.
  neighbors=[]
  for rot in range(1,len(fw)):
   nwraw=w[pref[rot]:]+w[:pref[rot]]
   nk,nw,nst=N.normalized(nwraw)
   if len(nk)<=len(key)and nk not in seen:neighbors.append((nk,nw,('rotate',rot,nst)))
  for rindex,(_,_,_,lk,rk,lw,rw)in enumerate(rules):
   lf=lk[:-1];L=len(lf)
   for pos in range(len(factors)-L+1):
    if factors[pos][0]!=lf[0][0]or factors[pos+L-1][0]!=lf[-1][0]:continue
    if factors[pos+1:pos+L-1]!=lf[1:-1]:continue
    first=N.reps[lf[0][0]][lf[0][1]]
    lastword=N.reps[lf[-1][0]][lf[-1][1]]+N.hwords[lk[-1]]
    pre=fw[pos]+tuple(inverse(first));post=tuple(inverse(lastword))+fw[pos+L-1]
    raw=w[:pref[pos]]+pre+rw+post+w[pref[pos+L]:]
    nk,nw,nst=N.normalized(raw)
    if nk in seen or len(nk)>len(start)+2:continue
    neighbors.append((nk,nw,('rule',rindex,pos,pre,post,nst)))
  for nk,nw,step in neighbors:
   if nk in seen:continue
   seen[nk]=(key,step);words[nk]=nw
   if nk==(0,):found=nk;break
   serial+=1;heapq.heappush(queue,(len(nk),serial,nk));best=min(best,len(nk))
  if found is not None:break
  if time.monotonic()-last>15:
   print(name,'nodes',len(seen),'expanded',expanded,'best',best-1,'seconds',int(time.monotonic()-t0),flush=True);last=time.monotonic()
 if found is not None:
  trace=[];k=found
  while seen[k]is not None:
   prev,step=seen[k];trace.append((k,step));k=prev
  out=Path('/tmp/acir-cs3-cyclic');out.mkdir(exist_ok=True)
  with(out/(name+'.pickle')).open('wb')as f:pickle.dump({'case':case,'initial':st,'trace':trace[::-1],'normalizer':N,'rules':rules,'words':words},f)
 print('SOLVED'if found is not None else'FAILED',name,'nodes',len(seen),'expanded',expanded,'best',best-1,'secs',round(time.monotonic()-t0),flush=True)
if __name__=='__main__':search(sys.argv[1],int(sys.argv[2])if len(sys.argv)>2 else 180)


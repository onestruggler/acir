#!/usr/bin/env python3
"""Search cross-pair identities modulo the shared one-qubit subgroup.

The edges apply proved relations, with boundary factorizations certified on
two wires. Normal forms compare exact pair matrices, never entire 3-wire
matrices as an axiom.
"""
from pathlib import Path
import json,sys,heapq,time,pickle,random
from amalgam_normalize import Normalizer
from base_rules import equations
from three_words import inverse,ccZ,ccX,atom,CS,transposition,GRAY
ROOT=Path(__file__).parent
def initial_rules():
 r=[('ax'+i,tuple(l),tuple(v))for i,l,v in equations()[24:30]]
 r+=[('Qsquare',tuple(ccZ()*2),()),('Acube',tuple(atom()*3),tuple(CS(1,2)*2)),
     ('P_Q_comm',tuple(CS(1,2)+ccZ()),tuple(ccZ()+CS(1,2)))]
 return r
def search(name,variant,seconds=180):
 N=Normalizer();raw=initial_rules();rules=[]
 for rid,(n,l,r)in enumerate(raw):
  a,aw,ast=N.normalized(l);b,bw,bst=N.normalized(r)
  for rev in [False,True]:
   rules.append((rid,rev,b if rev else a,a if rev else b,bw if rev else aw,aw if rev else bw))
 cases=json.loads((ROOT/'coset_obligations.json').read_text())
 case=next(c for c in cases if c['name']==name)
 startkey,startword,startsteps=N.normalized(case['lhs']);goal,goalword,goalsteps=N.normalized(case['rhs'])
 start=time.monotonic();last=start
 # State is represented by its normal form, with concrete words kept for replay.
 seen={startkey:None};words={startkey:startword};queue=[];serial=0;count=0
 def score(k):
  p=0
  while p<min(len(k)-1,len(goal)-1)and k[p]==goal[p]:p+=1
  q=0
  while q<min(len(k)-1-p,len(goal)-1-p)and k[-2-q]==goal[-2-q]:q+=1
  return len(k)+len(goal)-2*p-2*q
 heapq.heappush(queue,(score(startkey),serial,startkey))
 maxblocks=max(len(startkey),len(goal))+4;best=score(startkey);found=False
 print('START',name,variant,'blocks',len(startkey)-1,len(goal)-1,flush=True)
 while queue and time.monotonic()-start<seconds and len(seen)<12000:
  _,_,key=heapq.heappop(queue);count+=1
  factors=key[:-1];tail=key[-1];w=words[key]
  fw=[N.reps[j][m]for j,m in factors];prefix=[0]
  for x in fw:prefix.append(prefix[-1]+len(x))
  for rid,rev,left,right,lword,rword in rules:
   lf=left[:-1];lt=left[-1];L=len(lf)
   if L<2:continue
   for pos in range(len(factors)-L+1):
    if factors[pos][0]!=lf[0][0]or factors[pos+L-1][0]!=lf[-1][0]:continue
    if factors[pos+1:pos+L-1]!=lf[1:-1]:continue
    first=N.reps[lf[0][0]][lf[0][1]]
    lastword=N.reps[lf[-1][0]][lf[-1][1]]+N.hwords[lt]
    pre=fw[pos]+tuple(inverse(first))
    post=tuple(inverse(lastword))+fw[pos+L-1]
    newraw=w[:prefix[pos]]+pre+rword+post+w[prefix[pos+L]:]
    nk,nw,nst=N.normalized(newraw)
    if nk in seen or len(nk)>maxblocks:continue
    seen[nk]=(key,rid,rev,pos,pre,post,nst);words[nk]=nw
    if nk==goal:found=True;key=nk;break
    serial+=1;priority=score(nk)+(variant%3)*len(nk)//4
    heapq.heappush(queue,(priority,serial,nk))
    best=min(best,score(nk))
   if found:break
  if found:break
  if time.monotonic()-last>15:
   print(name,variant,'nodes',len(seen),'expanded',count,'best',best,'secs',int(time.monotonic()-start),flush=True);last=time.monotonic()
 if found:
  trace=[];k=goal
  while seen[k]is not None:
   entry=seen[k];trace.append((k,entry));k=entry[0]
  result={'case':case,'variant':variant,'initial':startsteps,'final':goalsteps,'trace':trace[::-1],'words':words,'raw_rules':raw,'normalizer':N}
  out=Path('/tmp/acir-cs3-amalgam-results');out.mkdir(exist_ok=True)
  with(out/f'{name}-{variant}.pickle').open('wb')as f:pickle.dump(result,f)
 print('SOLVED'if found else'FAILED',name,variant,'nodes',len(seen),'expanded',count,'best',best,'secs',int(time.monotonic()-start),flush=True)
if __name__=='__main__':search(sys.argv[1],int(sys.argv[2])if len(sys.argv)>2 else 0)


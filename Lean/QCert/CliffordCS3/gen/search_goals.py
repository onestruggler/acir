#!/usr/bin/env python3
"""Goal-directed proof search modulo checked two-qubit simplification.

Each edge is a supplied derived rule followed by a sequence of checked pair
equations. The JSON witness retains all steps for subsequent Lean replay.
"""
import sys,json,heapq,time,pickle,functools,random,difflib
from pathlib import Path
import pair_normalize as pn
from three_words import *
from base_rules import equations
ROOT=Path(__file__).resolve().parent
pn.canonical=functools.lru_cache(maxsize=300000)(pn.canonical)
@functools.lru_cache(maxsize=120000)
def norm(w):
 a,st=pn.normalize(w,limit=200000)
 return tuple(a),st
def bases():
 b=[('ax'+i,tuple(a),tuple(c))for i,a,c in equations()]
 b.append(('Qsquare',tuple(ccZ()*2),()))
 for q in range(3):b.append(('ccXsquare'+str(q),tuple(ccX(q)*2),()))
 for d,(a,c)in enumerate(zip(GRAY,GRAY[1:])):b.append(('tokenSquare'+str(d),tuple(transposition(a,c)*2),()))
 b.append(('P_Q_comm',tuple(CS(1,2)+ccZ()),tuple(ccZ()+CS(1,2))))
 b.append(('P_CS02_comm',tuple(CS(1,2)+CS(0,2)),tuple(CS(0,2)+CS(1,2))))
 b.append(('P_T6_comm',tuple(CS(1,2)+ccX(0)),tuple(ccX(0)+CS(1,2))))
 b.append(('Acube',tuple(atom()*3),tuple(CS(1,2)*2)))
 return b
def prep():
 file=Path('/tmp/acir-cs3-goal-rules.pickle')
 if file.exists():
  with file.open('rb')as f:return pickle.load(f)
 rules=[]
 for name,l,r in bases():
  a,sa=norm(l);b,sb=norm(r)
  if a!=b:rules.append({'name':name,'lhs':a,'rhs':b,'source_lhs':l,'source_rhs':r,'source_left_steps':sa,'source_right_steps':sb})
 with file.open('wb')as f:pickle.dump(rules,f)
 return rules
def score(a,b):
 # distance against the fixed target; use multiset and shared-end estimates.
 p=0
 while p<min(len(a),len(b)) and a[p]==b[p]:p+=1
 q=0
 while q<min(len(a)-p,len(b)-p)and a[-q-1]==b[-q-1]:q+=1
 return len(a)+len(b)-2*p-2*q
def search(name,seconds=180,variant=0):
 start=time.monotonic();rules=prep();goals=json.loads((ROOT/'coset_obligations.json').read_text())
 goal=next(g for g in goals if g['name']==name)
 l,ls=norm(tuple(goal['lhs']));r,rs=norm(tuple(goal['rhs']))
 print('START',name,'variant',variant,'normal_lengths',len(l),len(r),'rules',len(rules),flush=True)
 if l==r:return {'goal':goal,'left_initial':ls,'right_initial':rs,'join':l,'left_path':[],'right_path':[],'rules':rules}
 pq=[[(score(l,r),0,l)],[(score(r,l),0,r)]];seen=[{l:None},{r:None}];targets=[r,l]
 serial=0;expanded=0;last=start;maxlen=max(len(l),len(r))+20;join=None
 while all(pq)and time.monotonic()-start<seconds and sum(map(len,seen))<50000:
  side=expanded%2
  _,_,w=heapq.heappop(pq[side]);expanded+=1
  neighbors=[]
  for rid,rho in enumerate(rules):
   for reverse in [False,True]:
    a,b=(rho['rhs'],rho['lhs'])if reverse else(rho['lhs'],rho['rhs'])
    if not a or len(b)-len(a)+len(w)>maxlen:continue
    for i in range(len(w)-len(a)+1):
     if w[i:i+len(a)]!=a:continue
     raw=w[:i]+b+w[i+len(a):]
     neighbors.append((rid,reverse,i,raw))
  random.Random(variant+expanded).shuffle(neighbors)
  for rid,rev,i,raw in neighbors:
   nw,st=norm(raw)
   if nw in seen[side]:continue
   seen[side][nw]=(w,rid,rev,i,st)
   if nw in seen[1-side]:join=nw;break
   serial+=1
   priority=score(nw,targets[side])+(variant%3)*len(nw)//3
   heapq.heappush(pq[side],(priority,serial,nw))
  if join is not None:break
  if time.monotonic()-last>20:
   print(name,'expanded',expanded,'nodes',sum(map(len,seen)),'queue',list(map(len,pq)),'sec',round(time.monotonic()-start),flush=True);last=time.monotonic()
 if join is None:
  print('FAIL',name,'expanded',expanded,'nodes',sum(map(len,seen)),'sec',round(time.monotonic()-start),flush=True);return None
 def path(side):
  w=join;result=[]
  while seen[side][w]is not None:
   prev,rid,rev,i,st=seen[side][w];result.append((rid,rev,i,st));w=prev
  return result[::-1]
 print('SOLVED',name,'expanded',expanded,'sec',round(time.monotonic()-start),flush=True)
 return {'goal':goal,'left_initial':ls,'right_initial':rs,'join':join,'left_path':path(0),'right_path':path(1),'rules':rules}
if __name__=='__main__':
 name=sys.argv[1];variant=int(sys.argv[2])if len(sys.argv)>2 else 0
 result=search(name,300,variant)
 if result:
  out=Path('/tmp/acir-cs3-goal-results');out.mkdir(exist_ok=True)
  with(out/(name+'-'+str(variant)+'.pickle')).open('wb')as f:pickle.dump(result,f)


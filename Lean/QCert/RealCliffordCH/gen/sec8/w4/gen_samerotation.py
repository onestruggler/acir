"""Generate all 64 cases of (241) from one differing control and merging.

Usage: gen_samerotation.py D3.json OUT.lean
Every emitted derivation must be checked by Lean.
"""
import sys,json
from pathlib import Path
import gen_b,gen2,proj,solve2,tok,sym
P=proj.Project(4,lambda k,n:n+sym.KIND_AR[k]<=4,'(havail4b ih)')
for mod in ['A','B1','B2','B3','Expansion','CommuteLate','Opposite','HgLate','MergeZX','FullRotation']:
 for n,(l,r) in gen2.read_known(Path(gen2.LEAN_DIR)/(mod+'.lean')).items(): P.known(n,l,r)
for name in ['232','233']:P.ctx.ensure(name+'f2')
r=tok.G('zx',[0],[(1,True),(2,True),(3,True)])
full=tok.G('zx',[0],[(1,True),(2,False),(3,True)])
B=tok.G('box',[2],[(0,True),(1,True),(3,True)]);H=tok.P(2,[('K',0)],[0,2])
factors=[H,B,H,B]
S=P.solver(['DefZX3','BoxReversef1','BoxReverseBackf1','232f2','233f2']);S.start(100)
exp=S.solve([r],factors);steps=solve2.shift(exp,1);state=full
for i,f in enumerate(factors):
 nxt=next(s for s in [full,proj.tinv(full)] if S.c.same([state,f],[f,s])); S.start(100)
 steps+=solve2.shift(S.solve([state,f],[f,nxt]),i);state=nxt
assert state==full
steps+=S.reverse_steps([r],exp)
P.emit('241One',[r,full],[full,r],S.reverse_steps([full,r],steps))
# Coloured cancellation and the merge of two opposite control colours.
merge=['223'];cancel=['208']
for names in (merge,cancel):
 for wire in ((1,2,3) if names is merge else (0,1,2,3)):
  for base in list(names):
   name=base+'f'+str(wire);P.ctx.ensure(name);names.append(name)

def other(name,A,B,C,R,known):
 iB=proj.tinv(B)
 P.prove(name,[[A,C],[iB,B,A,C],[iB,A,B,C],[iB,A,R],
              [iB,R,A],[iB,B,C,A],[C,A]],budget=100,names=cancel+merge+known)
A=r
B=full;C=tok.G('zx',[0],[(1,False),(2,False),(3,True)])
R=tok.G('zx',[0],[(2,False),(3,True)])
other('241Two',A,B,C,R,['241One','239FF','239FT','239TF','239TT'])
B=tok.G('zx',[0],[(1,True),(2,False),(3,False)])
P.prove('241TwoOther',[[A,B],[B,A]],budget=100,names=['241Two'])
C=tok.G('zx',[0],[(1,False),(2,False),(3,False)])
R=tok.G('zx',[0],[(2,False),(3,False)])
other('241Three',A,B,C,R,['241TwoOther','239FF','239FT','239TF','239TT'])
def inv_first(name,new):
 a,b=P.ctx.eqs[name][0]; ai=proj.tinv(a)
 S=P.solver([name,'166']+cancel); S.start(100)
 steps=solve2.shift(P.pair(S,a),2)
 steps+=solve2.shift(S.solve([b,a],[a,b]),1)
 steps+=P.unpair(S,ai,a)
 P.emit(new,[ai,b],[b,ai],steps)

def inv_second(name,new):
 a,b=P.ctx.eqs[name][0]; bi=proj.tinv(b)
 S=P.solver([name,'166']+cancel);S.start(100)
 steps=P.pair(S,bi)
 steps+=solve2.shift(S.solve([b,a],[a,b]),1)
 steps+=solve2.shift(P.unpair(S,b,bi),2)
 P.emit(new,[a,bi],[bi,a],steps)

bases=['241One','241Two','241TwoOther','241Three']
for b in list(bases):
 inv_first(b,b+'Inv1');inv_second(b,b+'Inv2');inv_second(b+'Inv1',b+'Inv12')
 bases.extend([b+'Inv1',b+'Inv2',b+'Inv12'])
variants=list(bases)
for wire in (1,3):
 for b in list(variants):
  new=b+'F'+str(wire);P.derive_flip(b,wire,new);variants.append(new)
import itertools,re,model
from gen_small import dec
p, output = sys.argv[1:]
d=json.load(open(p));num=241
params=model.params([dec(g) for st in (d['statements'][str(num)][0],d['statements'][str(num)][-1]) for g in st['gates']])
exports=[]
for vs in itertools.product((False,True),repeat=len(params)):
 env=dict(zip(params,vs));suffix=''.join('T' if v else 'F' for v in vs);name=str(num)+suffix
 l,r,_,_=gen_b.chain_seq(d,num,env)
 keys=tuple(map(P.ctx.key,l))
 hit=next(n for n in variants if keys in [tuple(map(P.ctx.key,P.ctx.eqs[n][0])),tuple(map(P.ctx.key,P.ctx.eqs[n][1]))])
 P.prove(name,[l,r],budget=30,names=[hit])
 ep=gen_b.lean_endpoint(P,d,num,env,suffix)
 args=' '.join('true' if v else 'false' for v in vs)
 for side in 'lr':ep=re.sub(r'\b'+side+str(num)+r'\b',f'({side}{num} {args})',ep)
 exports.append(ep)
out=gen_b.HEADER.replace('gen/sec8/w4/gen_b.py','gen/sec8/w4/gen_samerotation.py').replace('{title}','full rotations').replace('{imports}','import QCert.RealCliffordCH.Sec8.D.W4.FullRotation')
out+='\n'.join(gen2.lean_run(e,4,4) for e in P.out)+'\n'+'\n'.join(exports)+'\nend QCert.RealCliffordCH.Sec8.D.W4\n'
Path(output).write_text(out,encoding='utf-8')

"""Generate all 64 cases of (240) from commuting and reversing factors.

Usage: gen_fullrotation.py D3.json OUT.lean
Every emitted derivation must be checked by Lean.
"""
import sys,json
from pathlib import Path
import gen_b,gen2,proj,solve2,tok,sym
P=proj.Project(4,lambda k,n:n+sym.KIND_AR[k]<=4,'(havail4b ih)')
for mod in ['A','B1','B2','B3','Expansion','CommuteLate','Opposite','HgLate','MergeZX']:
 for n,(l,r) in gen2.read_known(Path(gen2.LEAN_DIR)/(mod+'.lean')).items(): P.known(n,l,r)
r=tok.G('zx',[0],[(1,True),(2,True),(3,True)])
ri=proj.tinv(r); b=tok.G('box',[1],[(0,True),(2,True),(3,True)]); h=tok.S('K',0)
P.define(r,'DefZX3'); P.define(ri,'DefXZ3')
P.prove('BoxReverse',[[b,r],[b,h,b,h,b],[ri,b]],budget=30,names=['DefZX3','DefXZ3'])
P.prove('BoxReverseBack',[[b,ri],[b,ri,b,b],[b,b,r,b],[r,b]],budget=30,names=['BoxReverse','166'])
P.ctx.ensure('BoxReversef1'); P.ctx.ensure('BoxReverseBackf1')
full=tok.G('zx',[1],[(0,True),(2,False),(3,True)])
partial=r
B=tok.G('box',[2],[(0,True),(1,True),(3,True)]); H=tok.P(2,[('K',0)],[0,2])
factors=[H,B,H,B]
S=P.solver(['DefZX3','BoxReversef1','BoxReverseBackf1','234f2','235f2']);S.start(100)
exp=S.solve([partial],factors);steps=solve2.shift(exp,1);state=full
for i,f in enumerate(factors):
 nxt=next(s for s in [full,proj.tinv(full)] if S.c.same([state,f],[f,s])); S.start(100)
 print('passing',i,flush=True); steps+=solve2.shift(S.solve([state,f],[f,nxt]),i);state=nxt
assert state==full
steps+=S.reverse_steps([partial],exp)
P.emit('240Base',[full,partial],[partial,full],steps)

# A second colour on wire 3 follows from the partial rotation (216)
# and the already proved same-colour commutation, by cancellation.
C=tok.G('zx',[0],[(1,True),(2,True),(3,False)])
R=tok.G('zx',[0],[(1,True),(2,True)])
A=full; B=partial; iB=proj.tinv(B)
P.prove('240Other',[[A,C],[iB,B,A,C],[iB,A,B,C],[iB,A,R],
                     [iB,R,A],[iB,B,C,A],[C,A]],
        budget=100,names=['208','223','240Base','216'])
# The control-coloured versions of X R = R^-1 X.
base='238'
for w in (1,2,3):
 P.ctx.ensure(base+'f'+str(w)); base+='f'+str(w)

def inv_first(name,new):
 a,b=P.ctx.eqs[name][0]; ai=proj.tinv(a)
 S=P.solver([name,'166']); S.start(100)
 steps=solve2.shift(P.pair(S,a),2)
 steps+=solve2.shift(S.solve([b,a],[a,b]),1)
 steps+=P.unpair(S,ai,a)
 P.emit(new,[ai,b],[b,ai],steps)

def inv_second(name,new):
 a,b=P.ctx.eqs[name][0]; bi=proj.tinv(b)
 S=P.solver([name,'166']);S.start(100)
 steps=P.pair(S,bi)
 steps+=solve2.shift(S.solve([b,a],[a,b]),1)
 steps+=solve2.shift(P.unpair(S,b,bi),2)
 P.emit(new,[a,bi],[bi,a],steps)

bases=['240Base','240Other']
for b in list(bases):
 inv_first(b,b+'Inv1');inv_second(b,b+'Inv2');inv_second(b+'Inv1',b+'Inv12')
 bases.extend([b+'Inv1',b+'Inv2',b+'Inv12'])
variants=list(bases)
for wire in (0,1,3):
 for b in list(variants):
  new=b+'F'+str(wire);P.derive_flip(b,wire,new);variants.append(new)
import itertools,re,model
from gen_small import dec
p, output = sys.argv[1:]
d=json.load(open(p));num=240
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
out=gen_b.HEADER.replace('gen/sec8/w4/gen_b.py','gen/sec8/w4/gen_fullrotation.py').replace('{title}','full rotations').replace('{imports}','import QCert.RealCliffordCH.Sec8.D.W4.HgLate')
out+='\n'.join(gen2.lean_run(e,4,4) for e in P.out)+'\n'+'\n'.join(exports)+'\nend QCert.RealCliffordCH.Sec8.D.W4\n'
Path(output).write_text(out,encoding='utf-8')

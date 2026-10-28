"""Generate all cases of (247)--(248) by conjugating white-controlled CZ.

Usage: gen_whitecz.py D3.json OUT.lean
Every emitted certificate is checked by Lean.
"""
import sys,json,itertools,re
from pathlib import Path
import gen_b,gen2,proj,solve2,sym,tok,model
from gen_small import dec
P=proj.Project(4,lambda k,n:n+sym.KIND_AR[k]<=4,'(havail4b ih)')
for mod in ['A','B1','B2','B3','Inverse','HgMerge','Expansion','MergeZX','CommuteLate','Opposite','HgLate','FullRotation','SameRotation']:
 for n,(l,r) in gen2.read_known(Path(gen2.LEAN_DIR)/(mod+'.lean')).items():P.known(n,l,r)
# Extend (234) to a white control on the target of the controlled H.
H=P.ctx.eqs['234'][0][0];B=P.ctx.eqs['234'][0][1]
C=tok.G('zx',[1],[(0,False),(2,True),(3,True)])
R=tok.G('zx',[1],[(2,True),(3,True)]);iB=proj.tinv(B)
P.prove('234White',[[H,C],[iB,B,H,C],[iB,H,B,C],[iB,H,R],
                     [iB,R,H],[iB,B,C,H],[C,H]],
        budget=100,names=['208','223','234','230'])
S=P.solver(['234White','166']+[n for n in P.ctx.eqs if n.startswith('208')]);S.start(100)
Ci=proj.tinv(C)
steps=P.pair(S,Ci)+solve2.shift(S.solve([C,H],[H,C]),1)+solve2.shift(P.unpair(S,C,Ci),2)
P.emit('235White',[H,Ci],[Ci,H],steps)
names=[]
for base,ws in [('229F',(1,3)),('229T',(1,3)),('232',(1,3)),('233',(1,3)),
                ('234',(3,)),('235',(3,)),('234White',(3,)),('235White',(3,))]:
 ns=[base]
 for wire in ws:
  for n in list(ns):
   nm=n+'f'+str(wire);P.ctx.ensure(nm);ns.append(nm)
 names+=ns
p, output = sys.argv[1:]
d=json.load(open(p));exports=[]
for num in [247,248]:
 st=d['statements'][str(num)]
 ps=model.params([dec(g) for s in (st[0],st[-1]) for g in s['gates']])
 for vs in itertools.product((False,True),repeat=len(ps)):
  env=dict(zip(ps,vs));suffix=''.join('T' if v else 'F' for v in vs);name=str(num)+suffix
  l=gen2.diag_tokens(4,st[0],env);r=gen2.diag_tokens(4,st[-1],env)
  pp,rot,_,cz=l
  ch=tok.P(2,[('H',1),('Z',1),('H',1),('K',0),('H',1),('Z',1),('H',1)],[1,2])
  phase=tok.P(1,[('H',0),('Z',0),('H',0),('Z',0),('H',0),('Z',0),('H',0)],[2])
  factors=[ch] if env['gamma'] else [ch,phase]
  words=[l,[pp,rot,pp,cz,pp,pp],[pp,rot]+factors+[pp],
         [pp]+factors+[rot,pp],[pp,pp,cz,pp,rot,pp],r]
  P.prove(name,words,budget=100,names=names)
  ep=gen_b.lean_endpoint(P,d,num,env,suffix);args=' '.join(str(v).lower() for v in vs)
  for side in 'lr':ep=re.sub(r'\b'+side+str(num)+r'\b',f'({side}{num} {args})',ep)
  exports.append(ep)
 out=gen_b.HEADER.replace('gen/sec8/w4/gen_b.py','gen/sec8/w4/gen_whitecz.py').replace('{title}','conjugated rotations and white CZ').replace('{imports}','import QCert.RealCliffordCH.Sec8.D.W4.SameRotation')
 out+='\n'.join(gen2.lean_run(e,4,4) for e in P.out)+'\n'+'\n'.join(exports)+'\nend QCert.RealCliffordCH.Sec8.D.W4\n'
 Path(output).write_text(out,encoding='utf-8')

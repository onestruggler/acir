"""Generate (227) and both colour cases of (228).

Usage: gen_conjrotation.py D3.json OUT.lean
Each branch uses its own diagram chain from the paper.
"""
import sys,json
from pathlib import Path
import gen_b,gen2,proj,sym
P=proj.Project(4,lambda k,n:n+sym.KIND_AR[k]<=4,'(havail4b ih)')
for mod in ['A','B1','B2','B3','B4','Inverse','HgMerge','Expansion','MergeZX','Late','CommuteLate','Opposite','HgLate','FullRotation','SameRotation']:
 for n,(l,r) in gen2.read_known(Path(gen2.LEAN_DIR)/(mod+'.lean')).items():P.known(n,l,r)
pp,zx=P.ctx.eqs['174'][0];xz=P.ctx.eqs['174'][1][0]
P.prove('PPReverseBack',[[pp,xz],[pp,xz,pp,pp],[pp,pp,zx,pp],[zx,pp]],budget=30,names=['174'])
P.ctx.ensure('207f3')
P.ctx.ensure('219f2')
p, output = sys.argv[1:]
d=json.load(open(p));l,r,seq,_=gen_b.chain_seq(d,227)
names=['HgDeff3','HgDef','219','219f2','221','221i','222','223','224','174','PPReverseBack','220','220i']
for name in names:
 if name in P.ctx.virt:P.ctx.ensure(name)
names=[n for n in names if n in P.ctx.eqs]
print(names,flush=True)
S=P.solver(names);steps=[]
for i in range(len(seq)-1):
 print('step',i,flush=True);S.start(100)
 steps+=S.solve(seq[i],seq[i+1])
P.emit('227',l,r,steps)

P.ctx.ensure('156f2');P.ctx.ensure('156f3');P.ctx.ensure('210f2f1')
hb,hw=P.ctx.eqs['171a'][0];hp=P.ctx.eqs['171a'][1][0]
ch=gen_b.tok.P(2,[('K',0)],[1,3])
P.prove('HgWhiteSplit',[[hw],[hb,hb,hw],[hb,hp],[hb,ch]],budget=60,names=['167','171a'])
P.ctx.ensure('HgWhiteSplitf3')
exports=[gen_b.lean_endpoint(P,d,227)]
import re
for beta,ci in [(True,0),(False,1)]:
 env={'beta':beta};suffix='T' if beta else 'F';name='228'+suffix
 seq=[gen2.diag_tokens(4,D,env) for D in d['proofs']['228'][ci]['diags']]
 l=gen2.diag_tokens(4,d['statements']['228'][0],env);r=gen2.diag_tokens(4,d['statements']['228'][-1],env)
 seq=[l]+seq+[r]
 S=P.solver();steps=[]
 for i in range(len(seq)-1):
  print(name,'step',i,flush=True);S.start(150);steps+=S.solve(seq[i],seq[i+1])
 P.emit(name,l,r,steps)
 ep=gen_b.lean_endpoint(P,d,228,env,suffix)
 for side in 'lr':ep=re.sub(r'\b'+side+'228'+r'\b',f'({side}228 {str(beta).lower()})',ep)
 exports.append(ep)
 out=gen_b.HEADER.replace('gen/sec8/w4/gen_b.py','gen/sec8/w4/gen_conjrotation.py').replace('{title}','conjugated Hadamard and rotation').replace('{imports}','import QCert.RealCliffordCH.Sec8.D.W4.SameRotation')
 out+='\n'.join(gen2.lean_run(e,4,4) for e in P.out)+'\n'+'\n'.join(exports)+'\nend QCert.RealCliffordCH.Sec8.D.W4\n'
 Path(output).write_text(out,encoding='utf-8')

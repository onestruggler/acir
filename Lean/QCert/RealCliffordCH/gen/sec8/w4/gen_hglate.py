"""Generate the paper chains (203) and (219).

Usage: gen_hglate.py D3.json OUT.lean
Step 18 of (203) reuses the reverse of step 4 inside two cancelling PP gates.
All generated derivations are checked by Lean.
"""
import sys,json
from pathlib import Path
import gen_b,gen2,proj,sym,solve2,tok
p, output = sys.argv[1:]
d=json.load(open(p)); P=proj.Project(4,lambda k,n:n+sym.KIND_AR[k]<=4,'(havail4b ih)')
for mod in ['A','B1','B2','B3','B4','Inverse','HgMerge','Expansion','MergeZX','Late','CommuteLate','Opposite']:
 for n,(l,r) in gen2.read_known(Path(gen2.LEAN_DIR)/(mod+'.lean')).items(): P.known(n,l,r)
for n in [203,219]:
 print('start',n,flush=True)
 l,r,seq,_=gen_b.chain_seq(d,n)
 try:
  if n==203:
   steps=[]; S=P.solver(); saved4=None
   for i in range(len(seq)-1):
    print('solving',n,i,flush=True)
    S.start(150)
    if i==4:
     off,u,v=solve2.trim(seq[i],seq[i+1])
     local=S.solve(u,v); saved4=(u,v,local)
     sub=solve2.shift(local,off)
    elif i==18:
     off,u,v=solve2.trim(seq[i],seq[i+1]); a,b,pf=saved4; pp=b[0]
     ins=S.solve([], [pp,pp])
     local=ins+solve2.shift(S.reverse_steps(a,pf),1)
     assert S.verify(u,v,local)[0]
     sub=solve2.shift(local,off)
    else: sub=S.solve(seq[i],seq[i+1])
    assert S.verify(seq[i],seq[i+1],sub)[0]
    steps+=sub
   P.emit(str(n),l,r,steps)
  else: gen_b.prove_eq(P,d,n,budget=150)
 except Exception as e: print(type(e).__name__,str(e)[:300],flush=True)
 out=gen_b.HEADER.replace('gen/sec8/w4/gen_b.py','gen/sec8/w4/gen_hglate.py').replace('{title}','remaining commutations').replace('{imports}','import QCert.RealCliffordCH.Sec8.D.W4.Opposite')
 out+='\n'.join(gen2.lean_run(e,4,4) for e in P.out)
 if n==219 and '219' in P.ctx.eqs: out+='\n'+gen_b.lean_endpoint(P,d,219)
 out+='\nend QCert.RealCliffordCH.Sec8.D.W4\n'
 Path(output).write_text(out,encoding='utf-8')

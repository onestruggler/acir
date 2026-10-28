"""Generate N13/Low.lean; run after gen_boxcomm_low.py from the Lean project."""
import sys,itertools,pickle
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import proj,tok,gen2
eqs={n:(l,r,'W4Low.t'+n+' ih') for n,(l,r) in gen2.read_known(Path(gen2.LEAN_DIR)/'BoxCommLow.lean').items()}
P=proj.Project(4,lambda k,n:True,'(W4.havail4b ih)')
for n,(l,r,pf) in eqs.items():P.known(n,l,r,pf)
head='''/- Small-width cases of the general commutation equations. -/
import QCert.RealCliffordCH.Sec8.D.W4.BoxCommLow
import QCert.RealCliffordCH.Sec8.D.N13.Three
import QCert.RealCliffordCH.Sec8.D.N13.E336x
import QCert.RealCliffordCH.Sec8.D.N13.E340
import Mathlib.Tactic.IntervalCases

namespace QCert.RealCliffordCH.Sec8.D.N13
open Circuit Net
set_option maxRecDepth 20000
'''
out=[head]
def ctl(cs):return 'SE.ctl '+str(N)+' ['+', '.join(f'({w}, {c})' for w,c in cs)+'] false'
for N,num in [(4,335),(4,336),(3,335),(3,336),(3,340)]:
 vs=list('abcdef'[:(6 if N==4 else (2 if num==340 else 4))]);n=len(vs)
 if num==340:
  A=f'mc {N} .hg [0, 1] ({ctl([(2,vs[0])])})';B=f'mc {N} .hg [0, 1] ({ctl([(2,vs[1])])})'
 else:
  m=N-1;A=f'mc {N} .box [0] ({ctl(list(zip(range(1,N),vs[:m])))})'
  bw=[w for w in range(N) if w!=(0 if num==335 else 1)]
  B=f'mc {N} .box [{0 if num==335 else 1}] ({ctl(list(zip(bw,vs[m:])))})'
 out.append(f'theorem core{num}_{N} (ih : IH {N}) ('+ ' '.join(vs)+f' : Bool) :\n    Comm {N} ({A}) ({B}) := by\n  '+' <;> '.join('cases '+v for v in vs)+'\n')
 for vals in itertools.product((False,True),repeat=n):
  if N==3: hit=f'Low3.tLow3_{num}'+''.join('T' if v else 'F' for v in vals)
  else:
   a=tok.G('box',[0],list(zip(range(1,N),vals[:3])))
   b=tok.G('box',[0 if num==335 else 1],list(zip([w for w in range(N) if w!=(0 if num==335 else 1)],vals[3:])))
   keys=lambda w:tuple(map(P.ctx.key,w))
   hit='W4Low.t'+next(k for k,(l,r,pf) in eqs.items() if k.startswith(f'Box{num}Base') and keys(l)==keys([a,b]) and keys(r)==keys([b,a]))
  out.append(f'  · exact {hit} ih\n')
for N in [3,4]:
 for num in [335,336,340] if N==3 else [335,336]:
  if num==335:
   spec='.box';tgA='[0]';tgB='[0]';ca=f'colOn 1 {N} x';cb=f'colOn 1 {N} y';vA=[f'x {i}' for i in range(1,N)];vB=[f'y {i}' for i in range(1,N)];wsA=wsB=list(range(1,N));extra=''
  elif num==336:
   spec='.box';tgA='[0]';tgB='[1]';ca=f'ctlOr (ctlAt 1 c₁) (colOn 2 {N} x)';cb=f'ctlOr (ctlAt 0 c₂) (colOn 2 {N} y)';vA=['c₁']+[f'x {i}' for i in range(2,N)];vB=['c₂']+[f'y {i}' for i in range(2,N)];wsA=[1]+list(range(2,N));wsB=[0]+list(range(2,N));extra=' (c₁ c₂ : Bool)'
  else:
   spec='.hg';tgA=tgB='[0, 1]';ca=f'colOn 2 {N} x';cb=f'colOn 2 {N} y';vA=['x 2'];vB=['y 2'];wsA=wsB=[2];extra=''
  out.append(f'\ntheorem comm{num}_{N} (ih : IH {N}) (x y : ℕ → Bool){extra} :\n    Comm {N} (mc {N} {spec} {tgA} ({ca})) (mc {N} {spec} {tgB} ({cb})) := by\n')
  for label,tg,c,vs,ws in [('hx',tgA,ca,vA,wsA),('hy',tgB,cb,vB,wsB)]:
   out.append(f'  have {label} : mc {N} {spec} {tg} ({c}) = mc {N} {spec} {tg} ({ctl(list(zip(ws,vs)))}) := by\n    apply Net.mc_congr\n    intro i hi\n    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]\n')
  out.append('  rw [hx, hy]\n  exact core'+str(num)+'_'+str(N)+' ih '+' '.join('('+v+')' for v in vA+vB)+'\n')
out.append('''
theorem comm340_4 (ih : IH 4) (x y : ℕ → Bool) :
    Comm 4 (mc 4 .hg [0, 1] (colOn 2 4 x)) (mc 4 .hg [0, 1] (colOn 2 4 y)) := by
  have h := Comm.conj (comm335_4 ih (hgCol x) (hgCol y)) (pp_inv 1 ih)
    (u := (pp : Circ 4)) (v := pp)
  refine Comm.congr ((hg_box 0 x).trans ?_).symm ((hg_box 0 y).trans ?_).symm h <;>
    simp only [mul_assoc] <;> exact Derivable.refl _

end QCert.RealCliffordCH.Sec8.D.N13
''')
Path('QCert/RealCliffordCH/Sec8/D/N13/Low.lean').write_text(''.join(out),encoding='utf-8')

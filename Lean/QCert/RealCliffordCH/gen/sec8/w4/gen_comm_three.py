"""Generate N13/Three.lean; run from the Lean project directory."""
import sys,itertools
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import gen2,proj,sym,tok,solve2
P=proj.Project(3,lambda k,n:False,'havailNone')
P.known('e12',*[gen2.read_known('QCert/RealCliffordCH/Sec8/D/W3/Tokens.lean')['e12'][i] for i in [0,1]],proof='W3T.te12 ih')
for num in [335,336,340]:
 for vs in itertools.product((False,True),repeat=2 if num==340 else 4):
  if num==340:
   a,b=vs;A=tok.G('hg',[0,1],[(2,a)]);B=tok.G('hg',[0,1],[(2,b)])
  else:
   a,b,c,d=vs;A=tok.G('box',[0],[(1,a),(2,b)]);B=tok.G('box',[0 if num==335 else 1],[(1 if num==335 else 0,c),(2,d)])
  name='Low3_'+str(num)+''.join('T' if v else 'F' for v in vs)
  if num!=336:
   P.prove(name,[[A,B],[B,A]],names=['e12'],budget=300)
  else:
   S=P.solver(['e12']);S.start(100)
   sa,ra=S.unfold(A);sb,rb=S.unfold(B)
   def parts(ws,cs):
    u,v=ws;x,y=cs;out=[('p',2,(('C',0),),tuple(ws))]
    if not y:out.append(('s','Z',u))
    if not x:out.append(('s','Z',v))
    if not x and not y:out.append(('p',1,(('H',0),('Z',0))*4,(u,)))
    return out
   da=parts([1,2],[a,b]);db=parts([0,2],[c,d])
   S.start(100);pa=sa+S.solve(ra,da)
   S.start(100);pb=sb+S.solve(rb,db)
   S.start(300);mid=S.solve(da+db,db+da)
   steps=pa+solve2.shift(pb,len(da))+mid+S.reverse_steps([B],pb)+solve2.shift(S.reverse_steps([A],pa),1)
   P.emit(name,[A,B],[B,A],steps)
header='''/- Three-wire base cases of (335), (336), and (340). -/
import QCert.RealCliffordCH.Sec8.D.W3.Tokens

namespace QCert.RealCliffordCH.Sec8.D.Low3
open Circuit WE WS
open Eng (L)
abbrev tH (j : Nat) : Tk := Tk.s (L.H j)
abbrev tZ (j : Nat) : Tk := Tk.s (L.Z j)
abbrev tC (j : Nat) : Tk := Tk.s (L.C j)
abbrev tK (j : Nat) : Tk := Tk.s (L.K j)
abbrev tS (j : Nat) : Tk := Tk.s (L.S j)
abbrev tg (Kd : Kind) (tg : List Nat) (cs : List (Nat × Bool)) : Tk := Tk.g Kd tg cs
abbrev tp (m : Nat) (w : List L) (ps : List Nat) : Tk := Tk.p m w ps
private theorem havailNone : ∀ (K : Kind) (k : Nat), false = true → Net.CanonSym K k := by
  intro K k h
  cases h
'''
Path('QCert/RealCliffordCH/Sec8/D/N13/Three.lean').write_text(header+'\n'.join(gen2.lean_run(e,3,3) for e in P.out)+'\nend QCert.RealCliffordCH.Sec8.D.Low3\n',encoding='utf-8')

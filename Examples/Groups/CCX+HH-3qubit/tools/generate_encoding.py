"""Generate the primitive encoding and a syntactic decoding retraction."""
import generate as g
import generate_frames as f
import generate_base_frames as base
ROOT=g.ROOT;P=g.PREFIX
s=f.imports('PrimitiveFrames')
s+=f'import {P}.GatePermutations as GP\nimport {P}.FrameAliases.Ak4567 as A4567\n\n'
def pe(name,a,b):
    global s
    assert f.perm(a)==f.perm(b)
    s+=f'{name} : {f.cp(a)} ≈ {f.cp(b)}\n{name} = checked ({f.pw(a)}) ({f.pw(b)})\n  (λ {{ '
    s+=' ; '.join(f.finpat(i)+' → Eq.refl' for i in range(8))+' ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })\n\n'
    return name
s+='open import Data.Fin.Base using (zero ; suc)\n\n'
for x,pairs in [('X0',[(0,4),(1,5),(2,6),(3,7)]),('CX01',[(4,6),(5,7)]),('CCX12',[(3,7)])]:
    q=tuple(j for ab in pairs for j in f.transposition(*ab))
    ep=pe('perm'+x,base.classical(x),q)
    target=' • '.join('X'+str(a)+str(b) for a,b in pairs)
    s+=f'back{x} : {target} ≈ {x}\nback{x} = sym (trans GP.gate{x} (by-assoc-and {ep} Eq.refl Eq.refl))\n\n'

N=base.classical('X0 X1 X2');R=base.classical('X2 X1 X0')
pe('neg-neg',N+N,());pe('rev-rev',R+R,())
for label,raw,q,proof in [
    ('neg','X0 • X1 • X2',N,'cong GP.gateX0 (cong GP.gateX1 GP.gateX2)'),
    ('rev','X2 • X1 • X0',R,'cong GP.gateX2 (cong GP.gateX1 GP.gateX0)')]:
    s+=f'''{label}-convert : ({raw}) • ({raw}) ≈ {f.cp(q+q)}
{label}-convert = by-assoc-and (cong ({proof}) ({proof})) Eq.refl Eq.refl
{label}-invol : ({raw}) • ({raw}) ≈ ε
{label}-invol = trans {label}-convert {label}-{label}

'''
s+='''ccz-neg : X0 • X1 • X2 • m0 • X2 • X1 • X0 ≈ CCZ
ccz-neg = by-assoc-and (cong neg-invol (cong (refl {w = CCZ}) rev-invol)) Eq.refl Eq.refl

'''
# Move the permutation N past M0 and cancel its inverse. The stabilizer
# fixes 0, hence it is a product of the generators commuting with m0.
a=();b=f.afr(('M',7));st=f.decomposition(f.comp(f.inv(f.perm(b)),f.perm(N)),1)
pe('frame-left',N,b+st);pe('frame-right',st,tuple(reversed(b))+N);pe('neg-rev',N+R,())
comm='trans left-unit (sym right-unit)'
if st:
    comm=f'axiom r{84+st[-1]:03d}'
    for j in reversed(st[:-1]):comm=f'commute-product (axiom r{84+j:03d}) ({comm})'
s+=f'comm-frame : {f.cp(st)} • m0 ≈ m0 • {f.cp(st)}\ncomm-frame = {comm}\n\n'
s+=f'''frame-step0 : {f.cp(N)} • M0 ≈ {f.cp(b)} • {f.cp(st)} • m0
frame-step0 = by-assoc-and (under ε m0 frame-left) Eq.refl Eq.refl

frame-step1 : {f.cp(b)} • {f.cp(st)} • m0 ≈ {f.cp(b)} • m0 • {f.cp(st)}
frame-step1 = cong refl comm-frame

frame-step2 : {f.cp(b)} • m0 • {f.cp(st)} ≈ M7 • {f.cp(N)}
frame-step2 = by-assoc-and (under ({f.cp(b)} • m0) ε frame-right) Eq.refl Eq.refl

move-neg : {f.cp(N)} • M0 ≈ M7 • {f.cp(N)}
move-neg = trans frame-step0 (trans frame-step1 frame-step2)

frame-neg : X0 • X1 • X2 • m0 • X2 • X1 • X0 ≈ M7
frame-neg = trans converted (forget-frame (by-assoc-and move-neg Eq.refl Eq.refl)
  (by-assoc-and neg-rev Eq.refl Eq.refl))
  where
  converted : X0 • X1 • X2 • m0 • X2 • X1 • X0 ≈ {f.cp(N)} • M0 • {f.cp(R)}
  converted = by-assoc-and
    (cong (cong GP.gateX0 (cong GP.gateX1 GP.gateX2))
      (cong (refl {{w = m0}}) (cong GP.gateX2 (cong GP.gateX1 GP.gateX0)))) Eq.refl Eq.refl

backCCZ : M7 ≈ CCZ
backCCZ = trans (sym frame-neg) ccz-neg

backNK : K0123 ≈ NK
backNK = by-assoc Eq.refl

backK4567 : K4567 ≈ X0 • NK • X0
backK4567 = sym A4567.proved
'''
(ROOT/'PrimitiveFrames.agda').write_text(s,encoding='utf-8')

s=g.header('Repaired.Encoding')
s+=f'''open import Data.Fin.Base using (zero ; suc)
open import Data.Nat.Base using (s≤s ; z≤n)
import Relation.Binary.PropositionalEquality as Eq
open import {P}.Repaired.Syntactics
open import {P}.Core using (CGen ; cX0 ; cCX01 ; cCCX12 ; cK12 ; cCCZ ; cNK ; cH2 ; embed ; core ; gen-expand)
import {P}.Core as Core
import {P}.PrimitiveFrames as PF
import {P}.FrameWords as F
import {P}.Normalization as N
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as L
open import Presentation.Base _===_ hiding (_===_ ; _≈_)
open import Presentation.Properties _===_ using (by-assoc ; by-assoc-and)

'''
def bound(a):
    r='z≤n'
    for _ in range(a+1):r='(s≤s '+r+')'
    return r
for a,b in [(0,4),(1,5),(2,6),(3,7),(4,6),(5,7)]:
    s+=f'x{a}{b} : Word (T.Gen 8)\nx{a}{b} = T.X {f.finpat(a)} {f.finpat(b)} {bound(a)}\n'
for a,b,c,d in [(0,1,2,3),(4,5,6,7)]:
    s+=f'k{a}{b}{c}{d} : Word (T.Gen 8)\nk{a}{b}{c}{d} = T.K '+' '.join(f.finpat(i) for i in [a,b,c,d])+' '+' '.join(bound(i) for i in [a,b,c])+'\n'
s+=f'm7 : Word (T.Gen 8)\nm7 = T.M {f.finpat(7)}\n\n'
s+='''encode : CGen → Word (L.Genᴸ 8)
encode cX0 = L.⌊ x04 • x15 • x26 • x37 ⌋ʷ
encode cCX01 = L.⌊ x46 • x57 ⌋ʷ
encode cCCX12 = L.⌊ x37 ⌋ʷ
encode cK12 = L.⌊ k0123 • k4567 ⌋ʷ
encode cCCZ = L.⌊ m7 ⌋ʷ
encode cNK = L.⌊ k0123 ⌋ʷ
encode cH2 = L.H

decode : L.Genᴸ 8 → Word Gen
decode (L.⌊ g ⌋) = F.decode g
decode L.IH = H2

primitive-back : ∀ g → (decode ʷ) (encode g) ≈ [ embed g ]ʷ
primitive-back cX0 = lift PF.backX0
primitive-back cCX01 = lift PF.backCX01
primitive-back cCCX12 = lift PF.backCCX12
primitive-back cK12 = trans
  (cong (lift PF.backNK) (lift PF.backK4567))
  (sym (axiom K-definition))
primitive-back cCCZ = lift PF.backCCZ
primitive-back cNK = lift PF.backNK
primitive-back cH2 = refl

core-back : ∀ w → (decode ʷ) ((encode ʷ) w) ≈ Core.⌞ w ⌟
core-back [ g ]ʷ = primitive-back g
core-back ε = refl
core-back (w • v) = cong (core-back w) (core-back v)

e : Gen → Word (L.Genᴸ 8)
e g = (encode ʷ) (core g)

gen-back : ∀ g → (decode ʷ) (e g) ≈ [ g ]ʷ
gen-back g = trans (core-back (core g)) (sym (lift (gen-expand g)))

-- The encoding followed by decoding is the identity modulo the
-- repaired circuit relations, proved without using matrix equality.
word-back : ∀ w → (decode ʷ) ((e ʷ) w) ≈ w
word-back [ g ]ʷ = gen-back g
word-back ε = refl
word-back (w • v) = cong (word-back w) (word-back v)

encodeᴰ : N.DGen → Word (T.Gen 8)
encodeᴰ N.dX0 = x04 • x15 • x26 • x37
encodeᴰ N.dCX01 = x46 • x57
encodeᴰ N.dCCX12 = x37
encodeᴰ N.dK12 = k0123 • k4567
encodeᴰ N.dCCZ = m7
encodeᴰ N.dNK = k0123

dyadic-encoding : ∀ w → (e ʷ) (N.dyadic w) Eq.≡ L.⌊ (encodeᴰ ʷ) w ⌋ʷ
dyadic-encoding [ N.dX0 ]ʷ = Eq.refl
dyadic-encoding [ N.dCX01 ]ʷ = Eq.refl
dyadic-encoding [ N.dCCX12 ]ʷ = Eq.refl
dyadic-encoding [ N.dK12 ]ʷ = Eq.refl
dyadic-encoding [ N.dCCZ ]ʷ = Eq.refl
dyadic-encoding [ N.dNK ]ʷ = Eq.refl
dyadic-encoding ε = Eq.refl
dyadic-encoding (w • v) = Eq.cong₂ _•_ (dyadic-encoding w) (dyadic-encoding v)

dyadic-decoding : ∀ w → (decode ʷ) L.⌊ w ⌋ʷ Eq.≡ (F.decode ʷ) w
dyadic-decoding [ g ]ʷ = Eq.refl
dyadic-decoding ε = Eq.refl
dyadic-decoding (w • v) = Eq.cong₂ _•_ (dyadic-decoding w) (dyadic-decoding v)
'''
s=s.replace('k0123','tk0123').replace('k4567','tk4567')
(ROOT/'Repaired'/'Encoding.agda').write_text(s,encoding='utf-8')
print('Generated the encoding and syntactic retraction')

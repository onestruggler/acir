"""Transfer the repository's S8 completeness to the circuit words."""
import generate as g
P=g.PREFIX
s=g.header('Permutation')
s+='''open import Data.Nat.Base using (ℕ ; zero ; suc ; _≤_ ; s≤s)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin) renaming (zero to fzero ; suc to fsuc)
import Relation.Binary.PropositionalEquality as Eq
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB
import Presentation.Properties as PP
import Examples.Groups.Symmetric.Syntactics as S
import Examples.Groups.Symmetric.SubPresentation.Semantics as SS
import Examples.Groups.Symmetric.SubPresentation.SubPres as SP
'''
s+=f'open import {P}.Syntactics\n'
for i in range(7):s+=f'import {P}.PermProofs.invol{i} as I{i}\n'
for i in range(6):s+=f'import {P}.PermProofs.braid{i} as B{i}\n'
for i in range(7):
    for j in range(i+2,7):s+=f'import {P}.PermProofs.comm{i}{j} as C{i}{j}\n'
s+='\n'
s+='adjacent : ℕ → Word Gen\n'
for i in range(7):s+=f'adjacent {i} = t{i}{i+1}\n'
s+='adjacent _ = ε\n\n'
s+='decode : ∀ {n} → ℕ → S.Gen n → Word Gen\n'
s+='decode k (S.gate₀ ())\ndecode k (S.gate₂ S.σ-gate) = adjacent k\ndecode k (g S.↥) = decode (suc k) g\n\n'
s+='decode-shift : ∀ {n} k (w : Word (S.Gen n)) →\n  ((decode k) ʷ) (w S.↑) Eq.≡ ((decode (suc k)) ʷ) w\n'
s+='decode-shift k [ x ]ʷ = Eq.refl\ndecode-shift k ε = Eq.refl\ndecode-shift k (w • v) = Eq.cong₂ _•_ (decode-shift k w) (decode-shift k v)\n\n'
s+='open PB _===_ hiding (_===_ ; _≈_)\nopen PP _===_ using (by-assoc-and)\n\n'
s+='involution : ∀ k → adjacent k • adjacent k ≈ ε\n'
for i in range(7):s+=f'involution {i} = by-assoc-and I{i}.proved Eq.refl Eq.refl\n'
s+='involution (suc (suc (suc (suc (suc (suc (suc k))))))) = left-unit\n\n'
s+='braid : ∀ {m} k → k Data.Nat.Base.+ suc (suc (suc m)) ≤ 8 → adjacent k • adjacent (suc k) • adjacent k ≈ adjacent (suc k) • adjacent k • adjacent (suc k)\n'
for i in range(6):s+=f'braid {i} bound = by-assoc-and B{i}.proved Eq.refl Eq.refl\n'
s+='braid {m} (suc (suc (suc (suc (suc (suc k)))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s p)))))) = ⊥-elim (impossible k p)\n  where\n  impossible : ∀ k → k Data.Nat.Base.+ suc (suc (suc m)) ≤ 2 → ⊥\n  impossible zero (s≤s (s≤s ()))\n  impossible (suc zero) (s≤s (s≤s ()))\n  impossible (suc (suc zero)) (s≤s (s≤s ()))\n  impossible (suc (suc (suc k))) (s≤s (s≤s ()))\n\n'
s+='apart : ∀ k l → adjacent k • adjacent (suc (suc (k Data.Nat.Base.+ l))) ≈ adjacent (suc (suc (k Data.Nat.Base.+ l))) • adjacent k\n'
# generate k,l branches with both valid k and target k+2+l<=6
for i in range(5):
    for l in range(5-i):
        j=i+2+l
        s+=f'apart {i} {l} = by-assoc-and C{i}{j}.proved Eq.refl Eq.refl\n'
    n=5-i; pat='suc ('*(n-1)+'suc l'+')'*(n-1) if n>1 else 'suc l'
    s+=f'apart {i} ({pat}) = trans right-unit (sym left-unit)\n'
s+='apart 5 l = trans right-unit (sym left-unit)\napart 6 l = trans right-unit (sym left-unit)\napart (suc (suc (suc (suc (suc (suc (suc k))))))) l = refl\n\n'
s+='comm-decode : ∀ {n} k (g : S.Gen n) → adjacent k • decode (suc (suc k)) g ≈ decode (suc (suc k)) g • adjacent k\n'
# Generic comm shifted needs plus depth explicit lemma instead recursion shift k which changes first fixed.
s+='''
private
  comm-at : ∀ {n} k l (g : S.Gen n) →
    adjacent k • decode (suc (suc (k Data.Nat.Base.+ l))) g ≈
    decode (suc (suc (k Data.Nat.Base.+ l))) g • adjacent k
  comm-at k l (S.gate₀ ())
  comm-at k l (S.gate₂ S.σ-gate) = apart k l
  comm-at k l (g S.↥) = Eq.subst
    (λ z → adjacent k • decode (suc (suc z)) g ≈ decode (suc (suc z)) g • adjacent k)
    (Data.Nat.Properties.+-suc k l) (comm-at k (suc l) g)
'''
s+='comm-decode k g = Eq.subst\n  (λ z → adjacent k • decode (suc (suc z)) g ≈ decode (suc (suc z)) g • adjacent k)\n  (Data.Nat.Properties.+-identityʳ k) (comm-at k 0 g)\n\n'
s+='''
axiom-decode : ∀ {n w v} k → k Data.Nat.Base.+ n ≤ 8 → S._VRel,_===_ n w v →
  ((decode k) ʷ) w ≈ ((decode k) ʷ) v
axiom-decode k bound (S.srel S.order) = involution k
axiom-decode k bound (S.srel S.yang-baxter) = braid k bound
axiom-decode k bound (S.cong↑ {n} {w} {v} e) =
  Eq.subst₂ _≈_ (Eq.sym (decode-shift k w)) (Eq.sym (decode-shift k v))
    (axiom-decode (suc k)
      (Eq.subst (_≤ 8) (Data.Nat.Properties.+-suc k n) bound) e)
axiom-decode k bound (S.comm₁ () g)
axiom-decode k bound (S.comm₂ S.σ-gate g) = sym (comm-decode k g)
axiom-decode k bound (S.ω↑=ω ())

decode-cong : ∀ {n w v} k → k Data.Nat.Base.+ n ≤ 8 → PB._≈_ (S._VRel,_===_ n) w v →
  ((decode k) ʷ) w ≈ ((decode k) ʷ) v
decode-cong {n} k bound = PP.StarCongruence.fʷ-cong
  (S._VRel,_===_ n) _===_ (decode k) (axiom-decode k bound)

-- Matrix-product order on circuits and the endofunction reading on
-- S8 have opposite conventions. Equality is preserved by either
-- convention, so this still proves every true permutation equation.
permutation-complete : (w v : Word (S.Gen 8)) →
  (∀ i → SS.⟦ w ⟧ i Eq.≡ SS.⟦ v ⟧ i) →
  ((decode 0) ʷ) w ≈ ((decode 0) ʷ) v
permutation-complete w v eq = decode-cong {n = 8} {w = w} {v = v}
  0 Data.Nat.Properties.≤-refl (SP.completeness 8 {x = w} {y = v} eq)
'''
s=s.replace('import Relation.Binary.PropositionalEquality as Eq','import Data.Nat.Base\nimport Data.Nat.Properties\nimport Relation.Binary.PropositionalEquality as Eq')
(g.ROOT/'Permutation.agda').write_text(s,encoding='utf-8')

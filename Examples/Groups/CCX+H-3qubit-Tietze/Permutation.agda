{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Permutation where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _≤_ ; s≤s)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin) renaming (zero to fzero ; suc to fsuc)
import Data.Nat.Base
import Data.Nat.Properties
import Relation.Binary.PropositionalEquality as Eq
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB
import Presentation.Properties as PP
import Examples.Groups.Symmetric.Syntactics as S
import Examples.Groups.Symmetric.SubPresentation.Semantics as SS
import Examples.Groups.Symmetric.SubPresentation.SubPres as SP
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B021 using (module braid0 ; module braid1)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B022 using (module braid2)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B023 using (module braid3 ; module braid4 ; module braid5 ; module comm02)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B024 using (module comm03 ; module comm04 ; module comm05 ; module comm06 ; module comm13 ; module comm14)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B025 using (module comm15 ; module comm16 ; module comm24 ; module comm25 ; module comm26 ; module comm35 ; module comm36 ; module comm46 ; module invol0 ; module invol1 ; module invol2)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B026 using (module invol3 ; module invol4 ; module invol5 ; module invol6)

adjacent : ℕ → Word Gen
adjacent 0 = t01
adjacent 1 = t12
adjacent 2 = t23
adjacent 3 = t34
adjacent 4 = t45
adjacent 5 = t56
adjacent 6 = t67
adjacent _ = ε

decode : ∀ {n} → ℕ → S.Gen n → Word Gen
decode k (S.gate₀ ())
decode k (S.gate₂ S.σ-gate) = adjacent k
decode k (g S.↥) = decode (suc k) g

decode-shift : ∀ {n} k (w : Word (S.Gen n)) →
  ((decode k) ʷ) (w S.↑) Eq.≡ ((decode (suc k)) ʷ) w
decode-shift k [ x ]ʷ = Eq.refl
decode-shift k ε = Eq.refl
decode-shift k (w • v) = Eq.cong₂ _•_ (decode-shift k w) (decode-shift k v)

open PB _===_ hiding (_===_ ; _≈_)
open PP _===_ using (by-assoc-and)

involution : ∀ k → adjacent k • adjacent k ≈ ε
involution 0 = by-assoc-and invol0.proved Eq.refl Eq.refl
involution 1 = by-assoc-and invol1.proved Eq.refl Eq.refl
involution 2 = by-assoc-and invol2.proved Eq.refl Eq.refl
involution 3 = by-assoc-and invol3.proved Eq.refl Eq.refl
involution 4 = by-assoc-and invol4.proved Eq.refl Eq.refl
involution 5 = by-assoc-and invol5.proved Eq.refl Eq.refl
involution 6 = by-assoc-and invol6.proved Eq.refl Eq.refl
involution (suc (suc (suc (suc (suc (suc (suc k))))))) = left-unit

braid : ∀ {m} k → k Data.Nat.Base.+ suc (suc (suc m)) ≤ 8 → adjacent k • adjacent (suc k) • adjacent k ≈ adjacent (suc k) • adjacent k • adjacent (suc k)
braid 0 bound = by-assoc-and braid0.proved Eq.refl Eq.refl
braid 1 bound = by-assoc-and braid1.proved Eq.refl Eq.refl
braid 2 bound = by-assoc-and braid2.proved Eq.refl Eq.refl
braid 3 bound = by-assoc-and braid3.proved Eq.refl Eq.refl
braid 4 bound = by-assoc-and braid4.proved Eq.refl Eq.refl
braid 5 bound = by-assoc-and braid5.proved Eq.refl Eq.refl
braid {m} (suc (suc (suc (suc (suc (suc k)))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s p)))))) = ⊥-elim (impossible k p)
  where
  impossible : ∀ k → k Data.Nat.Base.+ suc (suc (suc m)) ≤ 2 → ⊥
  impossible zero (s≤s (s≤s ()))
  impossible (suc zero) (s≤s (s≤s ()))
  impossible (suc (suc zero)) (s≤s (s≤s ()))
  impossible (suc (suc (suc k))) (s≤s (s≤s ()))

apart : ∀ k l → adjacent k • adjacent (suc (suc (k Data.Nat.Base.+ l))) ≈ adjacent (suc (suc (k Data.Nat.Base.+ l))) • adjacent k
apart 0 0 = by-assoc-and comm02.proved Eq.refl Eq.refl
apart 0 1 = by-assoc-and comm03.proved Eq.refl Eq.refl
apart 0 2 = by-assoc-and comm04.proved Eq.refl Eq.refl
apart 0 3 = by-assoc-and comm05.proved Eq.refl Eq.refl
apart 0 4 = by-assoc-and comm06.proved Eq.refl Eq.refl
apart 0 (suc (suc (suc (suc (suc l))))) = trans right-unit (sym left-unit)
apart 1 0 = by-assoc-and comm13.proved Eq.refl Eq.refl
apart 1 1 = by-assoc-and comm14.proved Eq.refl Eq.refl
apart 1 2 = by-assoc-and comm15.proved Eq.refl Eq.refl
apart 1 3 = by-assoc-and comm16.proved Eq.refl Eq.refl
apart 1 (suc (suc (suc (suc l)))) = trans right-unit (sym left-unit)
apart 2 0 = by-assoc-and comm24.proved Eq.refl Eq.refl
apart 2 1 = by-assoc-and comm25.proved Eq.refl Eq.refl
apart 2 2 = by-assoc-and comm26.proved Eq.refl Eq.refl
apart 2 (suc (suc (suc l))) = trans right-unit (sym left-unit)
apart 3 0 = by-assoc-and comm35.proved Eq.refl Eq.refl
apart 3 1 = by-assoc-and comm36.proved Eq.refl Eq.refl
apart 3 (suc (suc l)) = trans right-unit (sym left-unit)
apart 4 0 = by-assoc-and comm46.proved Eq.refl Eq.refl
apart 4 (suc l) = trans right-unit (sym left-unit)
apart 5 l = trans right-unit (sym left-unit)
apart 6 l = trans right-unit (sym left-unit)
apart (suc (suc (suc (suc (suc (suc (suc k))))))) l = refl

comm-decode : ∀ {n} k (g : S.Gen n) → adjacent k • decode (suc (suc k)) g ≈ decode (suc (suc k)) g • adjacent k

private
  comm-at : ∀ {n} k l (g : S.Gen n) →
    adjacent k • decode (suc (suc (k Data.Nat.Base.+ l))) g ≈
    decode (suc (suc (k Data.Nat.Base.+ l))) g • adjacent k
  comm-at k l (S.gate₀ ())
  comm-at k l (S.gate₂ S.σ-gate) = apart k l
  comm-at k l (g S.↥) = Eq.subst
    (λ z → adjacent k • decode (suc (suc z)) g ≈ decode (suc (suc z)) g • adjacent k)
    (Data.Nat.Properties.+-suc k l) (comm-at k (suc l) g)
comm-decode k g = Eq.subst
  (λ z → adjacent k • decode (suc (suc z)) g ≈ decode (suc (suc z)) g • adjacent k)
  (Data.Nat.Properties.+-identityʳ k) (comm-at k 0 g)


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

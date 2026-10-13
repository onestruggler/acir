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
import Examples.Groups.CCX+HH-3qubit.PermProofs.invol0 as I0
import Examples.Groups.CCX+HH-3qubit.PermProofs.invol1 as I1
import Examples.Groups.CCX+HH-3qubit.PermProofs.invol2 as I2
import Examples.Groups.CCX+HH-3qubit.PermProofs.invol3 as I3
import Examples.Groups.CCX+HH-3qubit.PermProofs.invol4 as I4
import Examples.Groups.CCX+HH-3qubit.PermProofs.invol5 as I5
import Examples.Groups.CCX+HH-3qubit.PermProofs.invol6 as I6
import Examples.Groups.CCX+HH-3qubit.PermProofs.braid0 as B0
import Examples.Groups.CCX+HH-3qubit.PermProofs.braid1 as B1
import Examples.Groups.CCX+HH-3qubit.PermProofs.braid2 as B2
import Examples.Groups.CCX+HH-3qubit.PermProofs.braid3 as B3
import Examples.Groups.CCX+HH-3qubit.PermProofs.braid4 as B4
import Examples.Groups.CCX+HH-3qubit.PermProofs.braid5 as B5
import Examples.Groups.CCX+HH-3qubit.PermProofs.comm02 as C02
import Examples.Groups.CCX+HH-3qubit.PermProofs.comm03 as C03
import Examples.Groups.CCX+HH-3qubit.PermProofs.comm04 as C04
import Examples.Groups.CCX+HH-3qubit.PermProofs.comm05 as C05
import Examples.Groups.CCX+HH-3qubit.PermProofs.comm06 as C06
import Examples.Groups.CCX+HH-3qubit.PermProofs.comm13 as C13
import Examples.Groups.CCX+HH-3qubit.PermProofs.comm14 as C14
import Examples.Groups.CCX+HH-3qubit.PermProofs.comm15 as C15
import Examples.Groups.CCX+HH-3qubit.PermProofs.comm16 as C16
import Examples.Groups.CCX+HH-3qubit.PermProofs.comm24 as C24
import Examples.Groups.CCX+HH-3qubit.PermProofs.comm25 as C25
import Examples.Groups.CCX+HH-3qubit.PermProofs.comm26 as C26
import Examples.Groups.CCX+HH-3qubit.PermProofs.comm35 as C35
import Examples.Groups.CCX+HH-3qubit.PermProofs.comm36 as C36
import Examples.Groups.CCX+HH-3qubit.PermProofs.comm46 as C46

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
involution 0 = by-assoc-and I0.proved Eq.refl Eq.refl
involution 1 = by-assoc-and I1.proved Eq.refl Eq.refl
involution 2 = by-assoc-and I2.proved Eq.refl Eq.refl
involution 3 = by-assoc-and I3.proved Eq.refl Eq.refl
involution 4 = by-assoc-and I4.proved Eq.refl Eq.refl
involution 5 = by-assoc-and I5.proved Eq.refl Eq.refl
involution 6 = by-assoc-and I6.proved Eq.refl Eq.refl
involution (suc (suc (suc (suc (suc (suc (suc k))))))) = left-unit

braid : ∀ {m} k → k Data.Nat.Base.+ suc (suc (suc m)) ≤ 8 → adjacent k • adjacent (suc k) • adjacent k ≈ adjacent (suc k) • adjacent k • adjacent (suc k)
braid 0 bound = by-assoc-and B0.proved Eq.refl Eq.refl
braid 1 bound = by-assoc-and B1.proved Eq.refl Eq.refl
braid 2 bound = by-assoc-and B2.proved Eq.refl Eq.refl
braid 3 bound = by-assoc-and B3.proved Eq.refl Eq.refl
braid 4 bound = by-assoc-and B4.proved Eq.refl Eq.refl
braid 5 bound = by-assoc-and B5.proved Eq.refl Eq.refl
braid {m} (suc (suc (suc (suc (suc (suc k)))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s p)))))) = ⊥-elim (impossible k p)
  where
  impossible : ∀ k → k Data.Nat.Base.+ suc (suc (suc m)) ≤ 2 → ⊥
  impossible zero (s≤s (s≤s ()))
  impossible (suc zero) (s≤s (s≤s ()))
  impossible (suc (suc zero)) (s≤s (s≤s ()))
  impossible (suc (suc (suc k))) (s≤s (s≤s ()))

apart : ∀ k l → adjacent k • adjacent (suc (suc (k Data.Nat.Base.+ l))) ≈ adjacent (suc (suc (k Data.Nat.Base.+ l))) • adjacent k
apart 0 0 = by-assoc-and C02.proved Eq.refl Eq.refl
apart 0 1 = by-assoc-and C03.proved Eq.refl Eq.refl
apart 0 2 = by-assoc-and C04.proved Eq.refl Eq.refl
apart 0 3 = by-assoc-and C05.proved Eq.refl Eq.refl
apart 0 4 = by-assoc-and C06.proved Eq.refl Eq.refl
apart 0 (suc (suc (suc (suc (suc l))))) = trans right-unit (sym left-unit)
apart 1 0 = by-assoc-and C13.proved Eq.refl Eq.refl
apart 1 1 = by-assoc-and C14.proved Eq.refl Eq.refl
apart 1 2 = by-assoc-and C15.proved Eq.refl Eq.refl
apart 1 3 = by-assoc-and C16.proved Eq.refl Eq.refl
apart 1 (suc (suc (suc (suc l)))) = trans right-unit (sym left-unit)
apart 2 0 = by-assoc-and C24.proved Eq.refl Eq.refl
apart 2 1 = by-assoc-and C25.proved Eq.refl Eq.refl
apart 2 2 = by-assoc-and C26.proved Eq.refl Eq.refl
apart 2 (suc (suc (suc l))) = trans right-unit (sym left-unit)
apart 3 0 = by-assoc-and C35.proved Eq.refl Eq.refl
apart 3 1 = by-assoc-and C36.proved Eq.refl Eq.refl
apart 3 (suc (suc l)) = trans right-unit (sym left-unit)
apart 4 0 = by-assoc-and C46.proved Eq.refl Eq.refl
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

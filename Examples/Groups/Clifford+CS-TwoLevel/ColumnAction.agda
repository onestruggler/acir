------------------------------------------------------------------------
-- Presentations of groups
--
-- The generators acting on a scaled column w / γᵏ, through its
-- numerator w ∈ ℤ[i]ⁿ: i_[a] and X_[a,b] keep the exponent, K_[a,b]
-- raises it by one.  This turns every column computation of the
-- synthesis algorithm and of the Main Lemma into arithmetic in ℤ[i].
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-TwoLevel.ColumnAction where

open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality

open import Quantum.Synthesis.Ring
  using (SemiRingDyadic ; RingDyadic ; AdjointDyadic ; SemiRingCplx ; RingCplx ; AdjointCplx)

open import Examples.Groups.Clifford+CS-TwoLevel.Ring
open import Examples.Groups.Clifford+CS-TwoLevel.Scale
open import Examples.Groups.Clifford+CS-TwoLevel.Lde using (scV ; scV-!)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (dec-elim)
open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The actions on numerators

iᶻ : Fin n → Vec Z n → Vec Z n
iᶻ a w = set₁ a (ⅈᶻ ZR.* (w ! a)) w

Xᶻ : Fin n → Fin n → Vec Z n → Vec Z n
Xᶻ a b w = set₂ a b (w ! b) (w ! a) w

-- K at scale k + 1: the other entries are multiplied by γ.
Kᶻ : Fin n → Fin n → Vec Z n → Vec Z n
Kᶻ a b w = set₂ a b (w ! a ZR.+ w ! b) (w ! a ZR.- w ! b) (Vec.map (γᶻ ZR.*_) w)

------------------------------------------------------------------------
-- The generators on scaled vectors

private
  sc-ⅈ : ∀ k z → ⅈ DR.* sc k z ≡ sc k (ⅈᶻ ZR.* z)
  sc-ⅈ k z = sym (sc-* k ⅈᶻ z)

  sc-K+ : ∀ k u v → γ⁻ DR.* (sc k u DR.+ sc k v) ≡ sc (suc k) (u ZR.+ v)
  sc-K+ k u v = trans (cong (γ⁻ DR.*_) (sym (sc-+ k u v))) (γ⁻-sc k (u ZR.+ v))

  sc-K- : ∀ k u v → γ⁻ DR.* (sc k u DR.- sc k v) ≡ sc (suc k) (u ZR.- v)
  sc-K- k u v =
    trans (cong (λ z → γ⁻ DR.* (sc k u DR.+ z)) (sym (sc-neg k v)))
          (trans (cong (γ⁻ DR.*_) (sym (sc-+ k u (ZR.- v)))) (γ⁻-sc k (u ZR.- v)))

-- (The case analyses are by dec-elim rather than with-abstraction,
-- which would normalise the goals, arithmetic over 𝔻[i] included.)

actV-i : (a : Fin n) (k : ℕ) (w : Vec Z n) → actV (i-gen a) (scV k w) ≡ scV k (iᶻ a w)
actV-i a k w = vec-ext λ x → dec-elim (x FinP.≟ a)
  (λ { refl → begin
    actV (i-gen x) (scV k w) ! x                   ≡⟨ actV-ia x (scV k w) ⟩
    ⅈ DR.* (scV k w ! x)                           ≡⟨ cong (ⅈ DR.*_) (scV-! k w x) ⟩
    ⅈ DR.* sc k (w ! x)                            ≡⟨ sc-ⅈ k (w ! x) ⟩
    sc k (ⅈᶻ ZR.* (w ! x))                         ≡⟨ cong (sc k) (sym (set₁-a x (ⅈᶻ ZR.* (w ! x)) w)) ⟩
    sc k (iᶻ x w ! x)                              ≡⟨ sym (scV-! k (iᶻ x w) x) ⟩
    scV k (iᶻ x w) ! x                             ∎ })
  (λ x≢a → begin
    actV (i-gen a) (scV k w) ! x                   ≡⟨ actV-i≢ a (scV k w) x≢a ⟩
    scV k w ! x                                    ≡⟨ scV-! k w x ⟩
    sc k (w ! x)                                   ≡⟨ cong (sc k) (sym (set₁-≢ a (ⅈᶻ ZR.* (w ! a)) w x≢a)) ⟩
    sc k (iᶻ a w ! x)                              ≡⟨ sym (scV-! k (iᶻ a w) x) ⟩
    scV k (iᶻ a w) ! x                             ∎)
  where open ≡-Reasoning

actV-X : (a b : Fin n) .(p : a < b) (k : ℕ) (w : Vec Z n) → actV (X-gen a b p) (scV k w) ≡ scV k (Xᶻ a b w)
actV-X a b p k w = vec-ext λ x → dec-elim (x FinP.≟ a)
  (λ { refl → begin
    actV (X-gen x b p) v ! x                ≡⟨ actV-Xa p v ⟩
    v ! b                                   ≡⟨ scV-! k w b ⟩
    sc k (w ! b)                            ≡⟨ cong (sc k) (sym (set₂-a x b (w ! b) (w ! x) w)) ⟩
    sc k (Xᶻ x b w ! x)                     ≡⟨ sym (scV-! k (Xᶻ x b w) x) ⟩
    scV k (Xᶻ x b w) ! x                    ∎ })
  (λ x≢a → dec-elim (x FinP.≟ b)
    (λ { refl → begin
      actV (X-gen a x p) v ! x              ≡⟨ actV-Xb p v ⟩
      v ! a                                 ≡⟨ scV-! k w a ⟩
      sc k (w ! a)                          ≡⟨ cong (sc k) (sym (set₂-b a x (w ! x) (w ! a) w a≢b)) ⟩
      sc k (Xᶻ a x w ! x)                   ≡⟨ sym (scV-! k (Xᶻ a x w) x) ⟩
      scV k (Xᶻ a x w) ! x                  ∎ })
    (λ x≢b → begin
      actV (X-gen a b p) v ! x              ≡⟨ actV-X≢ p v x≢a x≢b ⟩
      v ! x                                 ≡⟨ scV-! k w x ⟩
      sc k (w ! x)                          ≡⟨ cong (sc k) (sym (set₂-≢ a b (w ! b) (w ! a) w x≢a x≢b)) ⟩
      sc k (Xᶻ a b w ! x)                   ≡⟨ sym (scV-! k (Xᶻ a b w) x) ⟩
      scV k (Xᶻ a b w) ! x                  ∎))
  where
  open ≡-Reasoning
  a≢b = <⇒≢ p
  v = scV k w

actV-K : (a b : Fin n) .(p : a < b) (k : ℕ) (w : Vec Z n) → actV (K-gen a b p) (scV k w) ≡ scV (suc k) (Kᶻ a b w)
actV-K a b p k w = vec-ext λ x → dec-elim (x FinP.≟ a)
  (λ { refl → begin
    actV (K-gen x b p) v ! x
      ≡⟨ actV-Ka p v ⟩
    γ⁻ DR.* (v ! x DR.+ v ! b)                           ≡⟨ cong₂ (λ s t → γ⁻ DR.* (s DR.+ t)) (scV-! k w x) (scV-! k w b) ⟩
    γ⁻ DR.* (sc k (w ! x) DR.+ sc k (w ! b))             ≡⟨ sc-K+ k (w ! x) (w ! b) ⟩
    sc (suc k) (w ! x ZR.+ w ! b)                        ≡⟨ cong (sc (suc k)) (sym (set₂-a x b (w ! x ZR.+ w ! b) (w ! x ZR.- w ! b) (γw w))) ⟩
    sc (suc k) (Kᶻ x b w ! x)                            ≡⟨ sym (scV-! (suc k) (Kᶻ x b w) x) ⟩
    scV (suc k) (Kᶻ x b w) ! x                           ∎ })
  (λ x≢a → dec-elim (x FinP.≟ b)
    (λ { refl → begin
      actV (K-gen a x p) v ! x
        ≡⟨ actV-Kb p v ⟩
      γ⁻ DR.* (v ! a DR.- v ! x)                         ≡⟨ cong₂ (λ s t → γ⁻ DR.* (s DR.- t)) (scV-! k w a) (scV-! k w x) ⟩
      γ⁻ DR.* (sc k (w ! a) DR.- sc k (w ! x))           ≡⟨ sc-K- k (w ! a) (w ! x) ⟩
      sc (suc k) (w ! a ZR.- w ! x)                      ≡⟨ cong (sc (suc k)) (sym (set₂-b a x (w ! a ZR.+ w ! x) (w ! a ZR.- w ! x) (γw w) a≢b)) ⟩
      sc (suc k) (Kᶻ a x w ! x)                          ≡⟨ sym (scV-! (suc k) (Kᶻ a x w) x) ⟩
      scV (suc k) (Kᶻ a x w) ! x                         ∎ })
    (λ x≢b → begin
      actV (K-gen a b p) v ! x
        ≡⟨ actV-K≢ p v x≢a x≢b ⟩
      v ! x                                              ≡⟨ scV-! k w x ⟩
      sc k (w ! x)                                       ≡⟨ sym (sc-γ k (w ! x)) ⟩
      sc (suc k) (γᶻ ZR.* (w ! x))                       ≡⟨ cong (sc (suc k)) (sym (VecP.lookup-map x (γᶻ ZR.*_) w)) ⟩
      sc (suc k) (γw w ! x)                              ≡⟨ cong (sc (suc k)) (sym (set₂-≢ a b (w ! a ZR.+ w ! b) (w ! a ZR.- w ! b) (γw w) x≢a x≢b)) ⟩
      sc (suc k) (Kᶻ a b w ! x)                          ≡⟨ sym (scV-! (suc k) (Kᶻ a b w) x) ⟩
      scV (suc k) (Kᶻ a b w) ! x                         ∎))
  where
  open ≡-Reasoning
  a≢b = <⇒≢ p
  v = scV k w
  γw : Vec Z n → Vec Z n
  γw = Vec.map (γᶻ ZR.*_)

------------------------------------------------------------------------
-- Presentations of groups
--
-- The generators acting on a scaled column w / δᵏ, through its
-- numerator w ∈ ℤ[ω]ⁿ: ω_[a] and X_[a,b] keep the exponent, H_[a,b]
-- raises it by two (1/√2 = λω / δ²).  This turns every column
-- computation of the synthesis algorithm and of the Main Lemma into
-- arithmetic in ℤ[ω].
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit-TwoLevel.ColumnAction where

open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality

open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Scale
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Residue using (δ²ᶻ)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Lde using (scV ; scV-!)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (dec-elim)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The actions on numerators

ωᵛ : Fin n → Vec Z n → Vec Z n
ωᵛ a w = set₁ a (ωᶻ ZR.* (w ! a)) w

Xᶻ : Fin n → Fin n → Vec Z n → Vec Z n
Xᶻ a b w = set₂ a b (w ! b) (w ! a) w

-- H at scale k + 2: the other entries are multiplied by δ².
Hᶻ : Fin n → Fin n → Vec Z n → Vec Z n
Hᶻ a b w = set₂ a b (λωᶻ ZR.* (w ! a ZR.+ w ! b)) (λωᶻ ZR.* (w ! a ZR.- w ! b)) (Vec.map (δ²ᶻ ZR.*_) w)

------------------------------------------------------------------------
-- The generators on scaled vectors

-- Two more factors δ.
sc-δ² : ∀ k w → sc (suc (suc k)) (δ²ᶻ ZR.* w) ≡ sc k w
sc-δ² k w = sc-δ^ 2 k w

private
  sc-H+ : ∀ k u v → √½ DR.* (sc k u DR.+ sc k v) ≡ sc (suc (suc k)) (λωᶻ ZR.* (u ZR.+ v))
  sc-H+ k u v = trans (cong (√½ DR.*_) (sym (sc-+ k u v))) (sc-√½ k (u ZR.+ v))

  sc-H- : ∀ k u v → √½ DR.* (sc k u DR.- sc k v) ≡ sc (suc (suc k)) (λωᶻ ZR.* (u ZR.- v))
  sc-H- k u v =
    trans (cong (λ z → √½ DR.* (sc k u DR.+ z)) (sym (sc-neg k v)))
          (trans (cong (√½ DR.*_) (sym (sc-+ k u (ZR.- v)))) (sc-√½ k (u ZR.- v)))

-- (The case analyses are by dec-elim rather than with-abstraction,
-- which would normalise the goals.)

actV-ω : (a : Fin n) (k : ℕ) (w : Vec Z n) → actV (ω-gen a) (scV k w) ≡ scV k (ωᵛ a w)
actV-ω a k w = vec-ext λ x → dec-elim (x FinP.≟ a)
  (λ { refl → begin
    actV (ω-gen x) (scV k w) ! x                   ≡⟨ actV-ia x (scV k w) ⟩
    ωᴰ DR.* (scV k w ! x)                          ≡⟨ cong (ωᴰ DR.*_) (scV-! k w x) ⟩
    ωᴰ DR.* sc k (w ! x)                           ≡⟨ sc-ω k (w ! x) ⟩
    sc k (ωᶻ ZR.* (w ! x))                         ≡⟨ cong (sc k) (sym (set₁-a x (ωᶻ ZR.* (w ! x)) w)) ⟩
    sc k (ωᵛ x w ! x)                              ≡⟨ sym (scV-! k (ωᵛ x w) x) ⟩
    scV k (ωᵛ x w) ! x                             ∎ })
  (λ x≢a → begin
    actV (ω-gen a) (scV k w) ! x                   ≡⟨ actV-i≢ a (scV k w) x≢a ⟩
    scV k w ! x                                    ≡⟨ scV-! k w x ⟩
    sc k (w ! x)                                   ≡⟨ cong (sc k) (sym (set₁-≢ a (ωᶻ ZR.* (w ! a)) w x≢a)) ⟩
    sc k (ωᵛ a w ! x)                              ≡⟨ sym (scV-! k (ωᵛ a w) x) ⟩
    scV k (ωᵛ a w) ! x                             ∎)
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

actV-H : (a b : Fin n) .(p : a < b) (k : ℕ) (w : Vec Z n) →
         actV (H-gen a b p) (scV k w) ≡ scV (suc (suc k)) (Hᶻ a b w)
actV-H a b p k w = vec-ext λ x → dec-elim (x FinP.≟ a)
  (λ { refl → begin
    actV (H-gen x b p) v ! x
      ≡⟨ actV-Ka p v ⟩
    √½ DR.* (v ! x DR.+ v ! b)                          ≡⟨ cong₂ (λ s t → √½ DR.* (s DR.+ t)) (scV-! k w x) (scV-! k w b) ⟩
    √½ DR.* (sc k (w ! x) DR.+ sc k (w ! b))            ≡⟨ sc-H+ k (w ! x) (w ! b) ⟩
    sc k2 (λωᶻ ZR.* (w ! x ZR.+ w ! b))                 ≡⟨ cong (sc k2) (sym (set₂-a x b (λωᶻ ZR.* (w ! x ZR.+ w ! b))
                                                                              (λωᶻ ZR.* (w ! x ZR.- w ! b)) (δw w))) ⟩
    sc k2 (Hᶻ x b w ! x)                                ≡⟨ sym (scV-! k2 (Hᶻ x b w) x) ⟩
    scV k2 (Hᶻ x b w) ! x                               ∎ })
  (λ x≢a → dec-elim (x FinP.≟ b)
    (λ { refl → begin
      actV (H-gen a x p) v ! x
        ≡⟨ actV-Kb p v ⟩
      √½ DR.* (v ! a DR.- v ! x)                        ≡⟨ cong₂ (λ s t → √½ DR.* (s DR.- t)) (scV-! k w a) (scV-! k w x) ⟩
      √½ DR.* (sc k (w ! a) DR.- sc k (w ! x))          ≡⟨ sc-H- k (w ! a) (w ! x) ⟩
      sc k2 (λωᶻ ZR.* (w ! a ZR.- w ! x))               ≡⟨ cong (sc k2) (sym (set₂-b a x (λωᶻ ZR.* (w ! a ZR.+ w ! x))
                                                                                (λωᶻ ZR.* (w ! a ZR.- w ! x)) (δw w) a≢b)) ⟩
      sc k2 (Hᶻ a x w ! x)                              ≡⟨ sym (scV-! k2 (Hᶻ a x w) x) ⟩
      scV k2 (Hᶻ a x w) ! x                             ∎ })
    (λ x≢b → begin
      actV (H-gen a b p) v ! x
        ≡⟨ actV-K≢ p v x≢a x≢b ⟩
      v ! x                                             ≡⟨ scV-! k w x ⟩
      sc k (w ! x)                                      ≡⟨ sym (sc-δ² k (w ! x)) ⟩
      sc k2 (δ²ᶻ ZR.* (w ! x))                          ≡⟨ cong (sc k2) (sym (VecP.lookup-map x (δ²ᶻ ZR.*_) w)) ⟩
      sc k2 (δw w ! x)                                  ≡⟨ cong (sc k2) (sym (set₂-≢ a b (λωᶻ ZR.* (w ! a ZR.+ w ! b))
                                                                                (λωᶻ ZR.* (w ! a ZR.- w ! b)) (δw w) x≢a x≢b)) ⟩
      sc k2 (Hᶻ a b w ! x)                              ≡⟨ sym (scV-! k2 (Hᶻ a b w) x) ⟩
      scV k2 (Hᶻ a b w) ! x                             ∎))
  where
  open ≡-Reasoning
  a≢b = <⇒≢ p
  v = scV k w
  k2 = suc (suc k)
  δw : Vec Z n → Vec Z n
  δw = Vec.map (δ²ᶻ ZR.*_)

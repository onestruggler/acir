------------------------------------------------------------------------
-- Presentations of groups
--
-- The generators acting on a scaled column w / √2ᵏ, through its
-- numerator w ∈ ℤ[√2]ⁿ: Z_[a] and X_[a,b] keep the exponent, H_[a,b]
-- raises it by one (its scalar is 1/√2), multiplying the other
-- entries by √2.  This turns every column computation of the
-- synthesis algorithm and of the Main Lemma into arithmetic in ℤ[√2].
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel.ColumnAction where

open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FinP
open import Data.Integer.Base using (+_ ; -[1+_])
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality

open import Quantum.Synthesis.Ring using (RootTwo)

open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Scale
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (scV ; scV-!)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (dec-elim)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics hiding (Z)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The actions on numerators

Zᶻ : Fin n → Vec Z n → Vec Z n
Zᶻ a w = set₁ a (ZR.- (w ! a)) w

Xᶻ : Fin n → Fin n → Vec Z n → Vec Z n
Xᶻ a b w = set₂ a b (w ! b) (w ! a) w

-- H at scale k + 1: the other entries are multiplied by √2.
Hᶻ : Fin n → Fin n → Vec Z n → Vec Z n
Hᶻ a b w = set₂ a b (w ! a ZR.+ w ! b) (w ! a ZR.- w ! b) (Vec.map (√2ᶻ ZR.*_) w)

------------------------------------------------------------------------
-- The generators on scaled vectors

private
  -1ᶻ : Z
  -1ᶻ = RootTwo -[1+ 0 ] (+ 0)

  -1ᴰ≡ : -1ᴰ ≡ emb -1ᶻ
  -1ᴰ≡ = refl

  -1*≡ : ∀ w → -1ᶻ ZR.* w ≡ ZR.- w
  -1*≡ w = ZS.solve 1 (λ w → ZS.con -[1+ 0 ] ZS.:* w ZS.:= ZS.:- w) refl w

  sc-Z : ∀ k u → -1ᴰ DR.* sc k u ≡ sc k (ZR.- u)
  sc-Z k u = trans (sym (sc-* k -1ᶻ u)) (cong (sc k) (-1*≡ u))

  sc-H+ : ∀ k u v → √½ DR.* (sc k u DR.+ sc k v) ≡ sc (suc k) (u ZR.+ v)
  sc-H+ k u v = trans (cong (√½ DR.*_) (sym (sc-+ k u v))) (√½-sc k (u ZR.+ v))

  sc-H- : ∀ k u v → √½ DR.* (sc k u DR.- sc k v) ≡ sc (suc k) (u ZR.- v)
  sc-H- k u v =
    trans (cong (λ z → √½ DR.* (sc k u DR.+ z)) (sym (sc-neg k v)))
          (trans (cong (√½ DR.*_) (sym (sc-+ k u (ZR.- v)))) (√½-sc k (u ZR.- v)))

-- (The case analyses are by dec-elim rather than with-abstraction,
-- which would normalise the goals.)

actV-Z : (a : Fin n) (k : ℕ) (w : Vec Z n) → actV (Z-gen a) (scV k w) ≡ scV k (Zᶻ a w)
actV-Z a k w = vec-ext λ x → dec-elim (x FinP.≟ a)
  (λ { refl → begin
    actV (Z-gen x) (scV k w) ! x                   ≡⟨ actV-ia x (scV k w) ⟩
    -1ᴰ DR.* (scV k w ! x)                         ≡⟨ cong (-1ᴰ DR.*_) (scV-! k w x) ⟩
    -1ᴰ DR.* sc k (w ! x)                          ≡⟨ sc-Z k (w ! x) ⟩
    sc k (ZR.- (w ! x))                            ≡⟨ cong (sc k) (sym (set₁-a x (ZR.- (w ! x)) w)) ⟩
    sc k (Zᶻ x w ! x)                              ≡⟨ sym (scV-! k (Zᶻ x w) x) ⟩
    scV k (Zᶻ x w) ! x                             ∎ })
  (λ x≢a → begin
    actV (Z-gen a) (scV k w) ! x                   ≡⟨ actV-i≢ a (scV k w) x≢a ⟩
    scV k w ! x                                    ≡⟨ scV-! k w x ⟩
    sc k (w ! x)                                   ≡⟨ cong (sc k) (sym (set₁-≢ a (ZR.- (w ! a)) w x≢a)) ⟩
    sc k (Zᶻ a w ! x)                              ≡⟨ sym (scV-! k (Zᶻ a w) x) ⟩
    scV k (Zᶻ a w) ! x                             ∎)
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
         actV (H-gen a b p) (scV k w) ≡ scV (suc k) (Hᶻ a b w)
actV-H a b p k w = vec-ext λ x → dec-elim (x FinP.≟ a)
  (λ { refl → begin
    actV (H-gen x b p) v ! x
      ≡⟨ actV-Ka p v ⟩
    √½ DR.* (v ! x DR.+ v ! b)                          ≡⟨ cong₂ (λ s t → √½ DR.* (s DR.+ t)) (scV-! k w x) (scV-! k w b) ⟩
    √½ DR.* (sc k (w ! x) DR.+ sc k (w ! b))            ≡⟨ sc-H+ k (w ! x) (w ! b) ⟩
    sc k1 (w ! x ZR.+ w ! b)                            ≡⟨ cong (sc k1) (sym (set₂-a x b (w ! x ZR.+ w ! b)
                                                                              (w ! x ZR.- w ! b) (δw w))) ⟩
    sc k1 (Hᶻ x b w ! x)                                ≡⟨ sym (scV-! k1 (Hᶻ x b w) x) ⟩
    scV k1 (Hᶻ x b w) ! x                               ∎ })
  (λ x≢a → dec-elim (x FinP.≟ b)
    (λ { refl → begin
      actV (H-gen a x p) v ! x
        ≡⟨ actV-Kb p v ⟩
      √½ DR.* (v ! a DR.- v ! x)                        ≡⟨ cong₂ (λ s t → √½ DR.* (s DR.- t)) (scV-! k w a) (scV-! k w x) ⟩
      √½ DR.* (sc k (w ! a) DR.- sc k (w ! x))          ≡⟨ sc-H- k (w ! a) (w ! x) ⟩
      sc k1 (w ! a ZR.- w ! x)                          ≡⟨ cong (sc k1) (sym (set₂-b a x (w ! a ZR.+ w ! x)
                                                                                (w ! a ZR.- w ! x) (δw w) a≢b)) ⟩
      sc k1 (Hᶻ a x w ! x)                              ≡⟨ sym (scV-! k1 (Hᶻ a x w) x) ⟩
      scV k1 (Hᶻ a x w) ! x                             ∎ })
    (λ x≢b → begin
      actV (H-gen a b p) v ! x
        ≡⟨ actV-K≢ p v x≢a x≢b ⟩
      v ! x                                             ≡⟨ scV-! k w x ⟩
      sc k (w ! x)                                      ≡⟨ sym (sc-δ k (w ! x)) ⟩
      sc k1 (√2ᶻ ZR.* (w ! x))                          ≡⟨ cong (sc k1) (sym (VecP.lookup-map x (√2ᶻ ZR.*_) w)) ⟩
      sc k1 (δw w ! x)                                  ≡⟨ cong (sc k1) (sym (set₂-≢ a b (w ! a ZR.+ w ! b)
                                                                                (w ! a ZR.- w ! b) (δw w) x≢a x≢b)) ⟩
      sc k1 (Hᶻ a b w ! x)                              ≡⟨ sym (scV-! k1 (Hᶻ a b w) x) ⟩
      scV k1 (Hᶻ a b w) ! x                             ∎))
  where
  open ≡-Reasoning
  a≢b = <⇒≢ p
  v = scV k w
  k1 = suc k
  δw : Vec Z n → Vec Z n
  δw = Vec.map (√2ᶻ ZR.*_)

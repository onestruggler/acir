------------------------------------------------------------------------
-- Presentations of groups
--
-- The tensor matrices coincide with the previously checked direct
-- basis-entry matrices on one, two and three wires.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.GeneralN.SmallPhysicalSemantics where

open import Relation.Binary.PropositionalEquality
open import Quantum.Synthesis.Matrix using (_·*·_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+H.Syntactics
import Examples.Groups.CCX+H.Semantics as Direct
import Examples.Groups.CCX+H.GeneralN.PhysicalSemantics as Tensor
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R
open R using (RingD)

opaque
  unfolding R._+ᴰ_ R._*ᴰ_ R.-ᴰ_

  gate₁-correct : ∀ (g : Gen 1) → Tensor.gate-matrix g ≡ Direct.gate-matrix g
  gate₁-correct (gate₀ ())
  gate₁-correct (gate₁ X-gate) = refl
  gate₁-correct (gate₁ H-gate) = refl
  gate₁-correct (gate₀ () ↥)

  gate₂-correct : ∀ (g : Gen 2) → Tensor.gate-matrix g ≡ Direct.gate-matrix g
  gate₂-correct (gate₀ ())
  gate₂-correct (gate₁ X-gate) = refl
  gate₂-correct (gate₁ H-gate) = refl
  gate₂-correct (gate₂ CX-gate) = refl
  gate₂-correct (gate₀ () ↥)
  gate₂-correct (gate₁ X-gate ↥) = refl
  gate₂-correct (gate₁ H-gate ↥) = refl
  gate₂-correct ((gate₀ () ↥) ↥)

  gate₃-correct : ∀ (g : Gen 3) → Tensor.gate-matrix g ≡ Direct.gate-matrix g
  gate₃-correct (gate₀ ())
  gate₃-correct (gate₁ X-gate) = refl
  gate₃-correct (gate₁ H-gate) = refl
  gate₃-correct (gate₂ CX-gate) = refl
  gate₃-correct (gate₃ CCX-gate) = refl
  gate₃-correct (gate₀ () ↥)
  gate₃-correct (gate₁ X-gate ↥) = refl
  gate₃-correct (gate₁ H-gate ↥) = refl
  gate₃-correct (gate₂ CX-gate ↥) = refl
  gate₃-correct ((gate₀ () ↥) ↥)
  gate₃-correct ((gate₁ X-gate ↥) ↥) = refl
  gate₃-correct ((gate₁ H-gate ↥) ↥) = refl
  gate₃-correct (((gate₀ () ↥) ↥) ↥)

  zero-identity : ∀ (w : Circuit 0) → Tensor.interpret w ≡ Tensor.interpret {0} ε
  zero-identity [ gate₀ () ]ʷ
  zero-identity ε = refl
  zero-identity (u • v) = trans (cong₂ _·*·_ (zero-identity u) (zero-identity v)) refl

one : ∀ (w : Circuit 1) → Tensor.interpret w ≡ Direct.interpret w
one [ g ]ʷ = gate₁-correct g
one ε = refl
one (u • v) = cong₂ _·*·_ (one u) (one v)

two : ∀ (w : Circuit 2) → Tensor.interpret w ≡ Direct.interpret w
two [ g ]ʷ = gate₂-correct g
two ε = refl
two (u • v) = cong₂ _·*·_ (two u) (two v)

three : ∀ (w : Circuit 3) → Tensor.interpret w ≡ Direct.interpret w
three [ g ]ʷ = gate₃-correct g
three ε = refl
three (u • v) = cong₂ _·*·_ (three u) (three v)

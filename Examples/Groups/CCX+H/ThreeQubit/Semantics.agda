------------------------------------------------------------------------
-- Presentations of groups
--
-- Independent, direct matrices for the three-wire circuit gates.
--
-- X/CX/CCX permute computational basis states by their Boolean action.
-- H has entry (-1)^(r_p c_p)/sqrt(2) when all other bits agree, and
-- zero otherwise.  Nine exact checks identify these matrices with
-- the auxiliary encoding; homomorphism extends this to every circuit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.ThreeQubit.Semantics where

open import Quantum.Synthesis.Matrix using (_·*·_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; trans ; cong₂)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Examples.Groups.CCX+H.Syntactics
open import Examples.Groups.CCX+H.Encoding using (encode)
open import Examples.Groups.CCX+H.Semantics public
  using (gate-matrix ; interpret)
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as S
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R
open R using (RingD)

private
  module M = S.Dim 4

opaque
  unfolding S.actV S.set₁ S.set₂ R._+ᴰ_ R._*ᴰ_ R.-ᴰ_

  gate-correct : ∀ (g : Gen 3) → M.⟦ encode [ g ]ʷ ⟧ᴸ ≡ gate-matrix g
  gate-correct (gate₀ ())
  gate-correct (gate₁ X-gate) = refl
  gate-correct (gate₁ H-gate) = refl
  gate-correct (gate₂ CX-gate) = refl
  gate-correct (gate₃ CCX-gate) = refl
  gate-correct (gate₀ () ↥)
  gate-correct (gate₁ X-gate ↥) = refl
  gate-correct (gate₁ H-gate ↥) = refl
  gate-correct (gate₂ CX-gate ↥) = refl
  gate-correct ((gate₀ () ↥) ↥)
  gate-correct ((gate₁ X-gate ↥) ↥) = refl
  gate-correct ((gate₁ H-gate ↥) ↥) = refl
  gate-correct (((gate₀ () ↥) ↥) ↥)

bridge : ∀ (w : Circuit 3) → M.⟦ encode w ⟧ᴸ ≡ interpret w
bridge [ g ]ʷ = gate-correct g
bridge ε = refl
bridge (w • v) =
  trans (M.⟦•⟧ᴸ (encode w) (encode v))
    (cong₂ _·*·_ (bridge w) (bridge v))

------------------------------------------------------------------------
-- Presentations of groups
--
-- The explicit two-wire encoding agrees with direct gate matrices.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.TwoQubit.Semantics where

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

private module M = S.Dim 2

opaque
  unfolding S.actV S.set₁ S.set₂ R._+ᴰ_ R._*ᴰ_ R.-ᴰ_

  gate-correct : ∀ (g : Gen 2) → M.⟦ encode [ g ]ʷ ⟧ᴸ ≡ gate-matrix g
  gate-correct (gate₀ ())
  gate-correct (gate₁ X-gate) = refl
  gate-correct (gate₁ H-gate) = refl
  gate-correct (gate₂ CX-gate) = refl
  gate-correct (gate₀ () ↥)
  gate-correct (gate₁ X-gate ↥) = refl
  gate-correct (gate₁ H-gate ↥) = refl
  gate-correct ((gate₀ () ↥) ↥)

bridge : ∀ (w : Circuit 2) → M.⟦ encode w ⟧ᴸ ≡ interpret w
bridge [ g ]ʷ = gate-correct g
bridge ε = refl
bridge (w • v) =
  trans (M.⟦•⟧ᴸ (encode w) (encode v))
    (cong₂ _·*·_ (bridge w) (bridge v))

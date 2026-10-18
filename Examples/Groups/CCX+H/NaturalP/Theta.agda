------------------------------------------------------------------------
-- Presentations of groups
--
-- From CCX+HH circuits to CCX+H circuits: HH is H on both of its wires.
--
-- θ reads CCX+HH.NaturalP's gates in CCX+H.NaturalP: HH as `HHw`,
-- H • H ↑, and every other gate as itself.  It commutes with shifting
-- (`θ-↑`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.NaturalP.Theta where

open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂)
open import Word.Base using ([_]ʷ ; ε ; _•_)

import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
open import Examples.Groups.CCX+H.NaturalP.Syntactics

private
  variable
    n : ℕ

θg : P.Gen n → Circuit n
θg (P.gate₀ ())
θg (P.gate₁ P.X-gate)   = X
θg (P.gate₂ P.CX-gate)  = CX
θg (P.gate₂ P.HH-gate)  = HHw
θg (P.gate₂ P.SW-gate)  = σ
θg (P.gate₃ P.CCX-gate) = CCX
θg (g P.↥)              = θg g ↑

θ : P.Circuit n → Circuit n
θ [ g ]ʷ  = θg g
θ ε       = ε
θ (u • v) = θ u • θ v

θ-↑ : (w : P.Circuit n) → θ (w P.↑) ≡ θ w ↑
θ-↑ [ g ]ʷ  = refl
θ-↑ ε       = refl
θ-↑ (u • v) = cong₂ _•_ (θ-↑ u) (θ-↑ v)

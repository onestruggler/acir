------------------------------------------------------------------------
-- Presentations of groups
--
-- Two placed rotations commute when their colourings differ off both
-- targets (Clément, Appendix E.5, (351) and (352) with x ≠ y placed)
--
-- A rotation `rot β` is rigid on wire 0 (Canon32.rot-rigid), so its
-- placement by a network depends only on where the network sends its
-- target (Placed.frame₁).  Two placed rotations with the same target t
-- and a witness j — a wire off the target where their colourings
-- differ — are conjugated by a network bringing t, j to the wires 0, 1
-- (Placed.bring₂): they become the canonical rotation in two colourings,
-- black on wire 0 and relatively white on wire 1, which is C351g.  With
-- different targets t, t′ the network brings t, t′, j to 0, 1, 2
-- (bring₃), and the second rotation is the canonical one under the swap
-- of the wires 0 1: C352g.  The colourings are only ever read at those
-- wires, through the network (`swW-lookup`).  The argument is
-- RotAnywhereGen's, at any width; this is its instance from five wires
-- on.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.RotAnywhere
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)

open import Notations using (₁₊ ; ₂₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (RotComm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon32 complete₂ complete₃ using (rot-rigid ; C351g ; C352g)
import Examples.Groups.Real-Clifford+CH.GeneralN.RotAnywhereGen as Gen

rot-comm : ∀ k → Below (₁₊ (₄₊ k)) → RotComm (₂₊ k)
rot-comm k below = Gen.rot-comm (λ β v → rot-rigid k below β v) (C351g k below) (C352g k below)

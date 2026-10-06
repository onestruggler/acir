------------------------------------------------------------------------
-- Presentations of groups
--
-- Two crossed rotations braid, in every colour and placed anywhere
-- (Clément, Appendix E.5, (358) as rule (24) uses it)
--
-- Two placed rotations P, Q with targets t ≠ t′, whose colourings agree
-- off the two targets, where P's type is decided by Q's colour on P's
-- target and Q's by P's colour on Q's target (as for two consecutive
-- Gray-code steps), satisfy P • Q • P ≈ Q • P • Q (`braid`).  A network
-- bringing t, t′ to the wires 0, 1 (Placed.bring₂) makes them the
-- canonical rotations on wires 0 and 1, and the colourings, relative to
-- each other, differ only on those two wires (a three-factor `col-rel`).
-- What is left is `C24 γ δ`, the canonical braid in the four colourings
-- of the wires 0 1.  A white control on B's target is X there, which
-- turns B over ((356)); white on A's target is X on wire 0 around (358),
-- which turns A over.  So all four are (358).  The argument is
-- BraidFrom's, at any width; this is its instance from five wires on.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.BraidAnywhere
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)

open import Notations using (₁₊ ; ₂₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.GeneralN.BraidCol using (Braid)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon32 complete₂ complete₃ using (rot-rigid)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX356 complete₂ complete₃ using (eq356)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon358 complete₂ complete₃ using (eq358)
import Examples.Groups.Real-Clifford+CH.GeneralN.BraidFrom as Gen

braid : ∀ k → Below (₁₊ (₄₊ k)) → Braid (₂₊ k)
braid k below = Gen.braid (λ β v → rot-rigid k below β v) (eq356 k below) (eq358 k below)

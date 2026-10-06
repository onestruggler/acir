------------------------------------------------------------------------
-- Presentations of groups
--
-- A placed rotation passes a placed box on another target, inverted
-- (Clément, Appendix E.5; the pair step of rule (31))
--
-- A rotation on the wire t and a box on the wire t′ ≠ t, coloured alike
-- off those two wires, are conjugated by a network bringing t, t′ to
-- the wires 0, 1 (Placed.bring₂).  The rotation becomes the canonical
-- one and the box B, the box on wire 1, in a colouring relative to the
-- rotation's that is black off the wires 0 1 — which is Canon31's pair
-- step K1: the rotation passes the box and comes out inverted.  The
-- argument is PairFrom's, at any width; this is its instance from five
-- wires on.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.RotPair
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ ; s≤s)

open import Notations using (₁₊ ; ₂₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (PairStep)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceFrames public using (reflect′ ; col-rel′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon32 complete₂ complete₃ using (rot-rigid)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon31 complete₂ complete₃ using (K1)
import Examples.Groups.Real-Clifford+CH.GeneralN.PairFrom as Gen

pair-step : ∀ k → Below (₁₊ (₄₊ k)) → PairStep (₂₊ k)
pair-step k below = Gen.pair-step (Canon.swaps canon) (λ β v → rot-rigid k below β v) (K1 k below)
  where
  completes : Completes (₁₊ k)
  completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))
  canon : Canon (₂₊ k)
  canon = canonN k completes

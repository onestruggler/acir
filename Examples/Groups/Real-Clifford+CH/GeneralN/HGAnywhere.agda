------------------------------------------------------------------------
-- Presentations of groups
--
-- A placed rotation against the gadget, in every position (Clément,
-- Appendix E.5, rule (38))
--
-- `hgrot` proves HGRotCol.HGRot at width 5 + k.  The gadget is the H
-- gate HG in the colouring black on the wires 0 1 and white above
-- (Box338Eq's S-ΛH).  A network σ on the wires 2 … passes HG
-- (Canon38.HG-rigid), so conjugating by it keeps the gadget in place and
-- brings the separating wire j to wire 2 and, when the rotation's target
-- t is above wire 1, t to wire 3 (Placed.bring₁ / bring₂ one wire up
-- twice).  In that frame the rotation is the canonical one on wire 0,
-- 1 or 3 (the last placed by the transposition of the wires 0 3), and
-- only the relative colouring counts (RotPair.col-rel′): black on its
-- target, white on wire 2 and, for a target on wire 3, white there.
-- That is Canon38's C38₀, C38₁ or C38₂.  The argument is HGFrom's,
-- at any width from four; this is its instance from five wires on.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.HGAnywhere
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)

open import Notations using (₁₊ ; ₂₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.GeneralN.HGRotCol using (HGRot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338Eq complete₂ complete₃ using (module XY)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon32 complete₂ complete₃ using (rot-rigid)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon38 complete₂ complete₃
  using (HG ; HG-rigid ; C38₀ ; C38₁ ; C38₂)
import Examples.Groups.Real-Clifford+CH.GeneralN.HGFrom as Gen

hgrot : ∀ k → Below (₁₊ (₄₊ k)) → HGRot (₂₊ k)
hgrot k below = Gen.hgrot (λ β v → rot-rigid k below β v) (HG k below) (HG-rigid k below) (mid _ _ S-ΛH)
                          (C38₀ k below) (C38₁ k below) (C38₂ k below)
  where
  open Tools ((₁₊ (₄₊ k)) VRel,_===_)
  open XY k below using (S-ΛH)

------------------------------------------------------------------------
-- Presentations of groups
--
-- The kit of the Hadamard-free decoding at width 5 + k (Clément,
-- Appendix E.5)
--
-- From completeness at every smaller width: the box at the canonical
-- position and its merges (CanonN, Lemma87All), the top merges —
-- RotMerge's below the full width and (354) on the top wire (`tmN`) —
-- the rotation's rigidity (Canon32), and the fragment of Figure 8
-- decoded (Free).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.KitN
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (true ; false)
open import Data.Nat using (ℕ ; _<_ ; s≤s)
open import Data.Nat.Properties using (≤-pred ; m≤n⇒m<n∨m≡n)
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₁₊ ; ₂₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (TopMerge)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87All complete₂ complete₃ using (mergesₙ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon32 complete₂ complete₃ using (rot-rigid)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotMerge complete₂ complete₃ using (top-merge ; rmerge-top)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Free complete₂ complete₃ using (d-ax)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Kit using (Kit)

-- The top merges below the full width are RotMerge's, the last one is
-- (354) on the top wire.
tmN : ∀ k → Below (₁₊ (₄₊ k)) → ∀ β K → K < ₄₊ k → TopMerge β K
tmN k below β K K< with m≤n⇒m<n∨m≡n (≤-pred K<)
tmN k below β     K K< | inj₁ K<′      = top-merge k below β K K<′
tmN k below true  K K< | inj₂ Eq.refl  = rmerge-top k below true
tmN k below false K K< | inj₂ Eq.refl  = rmerge-top k below false

kitN : ∀ k → Below (₁₊ (₄₊ k)) → Kit (₂₊ k)
kitN k below = record
  { complete₂ = complete₂
  ; canon     = canonN k completes
  ; merges    = mergesₙ k completes
  ; tm        = tmN k below
  ; rig       = λ β v → rot-rigid k below β v
  ; d-ax      = d-ax k below
  }
  where
  completes : Completes (₁₊ k)
  completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

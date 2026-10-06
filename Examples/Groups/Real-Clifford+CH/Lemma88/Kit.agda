------------------------------------------------------------------------
-- Presentations of groups
--
-- What the decoding of the Hadamard-free letters needs at a width
-- (Clément, Appendix E.5, rules (36) and (37))
--
-- The decoded Lemma 8.5 (Letter85), the encoded swap decoded (DecSwap)
-- and rules (36) and (37) (Rule3637) are proved at every width 3 + m
-- from a few facts about that width, collected here: completeness on
-- two qubits; the box at the canonical position (`canon`) and its
-- merges (`merges`, as Lemma 8.7 takes them); the rotation merged on
-- the top wire at every width up to 3 + m (`tm`, (354)); the rotation
-- rigid on wire 0 (`rig`); and the decoding of every rule of the
-- Hadamard-free fragment of Figure 8 (`d-ax`), which gives Corollary
-- A.5 decoded (FreeGen).  KitN supplies them from five wires on; on
-- three and four wires they come from Lemmas D.2 and D.5.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Lemma88.Kit where

open import Data.Nat using (ℕ ; suc ; _≤_ ; _<_)
open import Word.Base using (Word ; _•_ ; _ʷ)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8Free using (_PF,_===_)
open import Examples.Groups.Real-Clifford+CH.Decoding using (d)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (Rigid)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot ; TopMerge)

-- The merges Lemma 8.7 needs, up to width 2 + B (Lemma87Three's).
Merges : ℕ → Set
Merges B = ∀ K → 1 ≤ K → K ≤ B → ∀ c → 1 ≤ c → c ≤ suc K →
           (₂₊ K) ⊢ (Xat c • Λ□ (suc K) • Xat c) • Λ□ (suc K) ≈ placeAt c (Λ□ K)

record Kit (m : ℕ) : Set where
  field
    complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v
    canon     : Canon m
    merges    : Merges (₁₊ m)
    tm        : ∀ β K → K < ₂₊ m → TopMerge β K
    rig       : ∀ β → Rigid 1 (rot {m} β)
    d-ax      : ∀ {u t : Word (GenP (₃₊ m))} → m PF, u === t → (₃₊ m) ⊢ (d ʷ) u ≈ (d ʷ) t

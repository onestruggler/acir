------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding's gadgets at every width, and the affine decoding
--
-- The gadget on 4 + m wires is λ⁰ of the one a width down, starting
-- from a four-wire gadget G₄ (`gad`).  It commutes with every CX whose
-- control is off wire 0 at every width (`indep`), given that G₄ does on
-- four wires, the paper's (F6) on five, and from six wires on the
-- symmetry of the two top controls of the gadget (Stable.Gadget.step,
-- step′).  So the affine decoding — the gadget carried from the basis
-- states 0, e₀ to p, q by the affine circuit α p q — is equivariant
-- under every affine circuit at every width (`Dec.eqvʷ`, from
-- Affine.Decoding).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; zero ; suc)
open import Notations using (₄₊)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ ; λ⁰ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Calc using (F4ᵗ ; F5ᵗ)
import Examples.Groups.Clifford+CS.Stable.Gadget as Gadget

module Examples.Groups.Clifford+CS.Stable.GadgetAll
  (c4 : Complete 4) (f4 : ∀ m → F4ᵗ m) (f5 : ∀ m → F5ᵗ m)
  (tr : ∀ m {u v : Circuit (₄₊ m)} → (₄₊ m) ⊢ᵧ u ≈ v → (suc (₄₊ m)) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v)
  where

open import Examples.Groups.Clifford+CS.Stable.Rules using (_YVRel,_===_ ; embed)
import Examples.Groups.Clifford+CS.Affine.Decoding as Decoding

module Gd (m : ℕ) = Gadget m c4 (f4 m) (f5 m) (tr m)

module _
  (G₄ : Circuit 4)
  (ind₄ : Gd.Indep₀ 0 G₄)
  (f6 : Gd.TopTarget 0 G₄)
  where

  -- The gadget on 4 + m wires.
  gad : ∀ m → Circuit (₄₊ m)
  gad zero    = G₄
  gad (suc m) = λ⁰ʷ (gad m)

  module _ (sym : ∀ m → Gd.SwapSym (suc m) (gad (suc m))) where

    -- Its independence of the affine circuit, at every width.
    indep : ∀ m → Gd.Indep₀ m (gad m)
    indep zero          = ind₄
    indep (suc zero)    = Gd.step 0 G₄ ind₄ f6
    indep (suc (suc m)) = Gd.step′ (suc m) (gad (suc m)) (indep (suc m)) (sym m)

    -- The affine decoding of the gadget, and its equivariance.
    module Dec (m : ℕ) =
      Decoding.Gate m c4 ((₄₊ m) YVRel,_===_) embed (gad m) (indep m)

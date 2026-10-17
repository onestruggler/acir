------------------------------------------------------------------------
-- Presentations of groups
--
-- The statements about the decoding's gadget, apart from the inputs
--
-- Stable.Gadget proves its lemmas from the λ-calculus at one width, but
-- states them without it: G commutes with every CX whose control is off
-- wire 0 (`Indep₀`, and `Indep₁` one wire up), λ⁰ G with every CX from a
-- domain wire onto the top (`TopTarget`), and λ⁰ G does not see the
-- order of the two top wires (`SwapSym`).  Kept here, the statements are
-- the same terms whatever the inputs, so the chain can state them before
-- it has the inputs (Stable.Inputs).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)

module Examples.Groups.Clifford+CS.Stable.GadgetDefs (m : ℕ) (c4 : Complete 4) where

open import Data.Fin using (Fin ; inject₁ ; fromℕ) renaming (suc to sF)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Word.Base using (_•_)

open import Notations using (₃₊ ; ₄₊)

open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Lambda using (λ⁰ʷ ; Swᵗ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)

import Examples.Groups.Clifford+CS.Affine.Theory (₃₊ m) as A₀
import Examples.Groups.Clifford+CS.Affine.Theory (₄₊ m) as A₁
import Examples.Groups.Clifford+CS.Affine.Circuits m c4 as C₀
import Examples.Groups.Clifford+CS.Affine.Circuits (suc m) c4 as C₁

private
  W D : ℕ
  W = suc (₄₊ m)
  D = ₄₊ m

  tp : Fin W
  tp = fromℕ (₄₊ m)

-- G commutes with every CX whose control is off wire 0.
Indep₀ : Circuit D → Set
Indep₀ G = ∀ (u : Fin (₃₊ m)) (v : A₀.Wire) .(p : sF u ≢ v) →
           D ⊢ᵧ C₀.⟪ A₀.tL (sF u) v p ⟫ • G ≈ G • C₀.⟪ A₀.tL (sF u) v p ⟫

Indep₁ : Circuit W → Set
Indep₁ G = ∀ (u : Fin (₄₊ m)) (v : A₁.Wire) .(p : sF u ≢ v) →
           W ⊢ᵧ C₁.⟪ A₁.tL (sF u) v p ⟫ • G ≈ G • C₁.⟪ A₁.tL (sF u) v p ⟫

-- λ⁰ G commutes with every CX from a domain wire off wire 0 onto the top.
TopTarget : Circuit D → Set
TopTarget G = ∀ (u : Fin (₃₊ m)) .(p : sF (inject₁ u) ≢ tp) →
              W ⊢ᵧ C₁.⟪ A₁.tL (sF (inject₁ u)) tp p ⟫ • λ⁰ʷ G ≈ λ⁰ʷ G • C₁.⟪ A₁.tL (sF (inject₁ u)) tp p ⟫

-- λ⁰ G does not see the order of its two controls, when G is itself λ⁰
-- of a circuit.
SwapSym : Circuit D → Set
SwapSym G = W ⊢ᵧ Swᵗ (₃₊ m) • λ⁰ʷ G • Swᵗ (₃₊ m) ≈ λ⁰ʷ G

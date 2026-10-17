------------------------------------------------------------------------
-- Presentations of groups
--
-- The hyperplane step of Lemma 8.8 by semantics
--
-- Stable.Hyper.hyper carries an equation between decoded words one
-- width up from the moved-down equation.  In the induction on the width
-- that equation needs no check of its own: the white control is
-- injective on operators (`ctrl⁰-inj`, its block where the top wire
-- reads 0), so when the two decoded words on 5 + m wires have the same
-- semantics, so have the moved-down words on 4 + m wires — each is the
-- other's λ⁰ conjugated by the affine word, a derivation (D-top, D-eqv)
-- and hence sound — and completeness on 4 + m wires, the hypothesis of
-- the induction, equates them (`hyper-sem`).  This is Five.DWD's
-- argument at every width: Lemma 8.8 for decoded words comes down to
-- the decoding's semantics.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
open import Notations using (₄₊)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Inputs using (Inputs)
import Examples.Groups.Clifford+CS.Stable.GadgetDefs as GadgetDefs
import Examples.Groups.Clifford+CS.Stable.GadgetAll as GadgetAll

module Examples.Groups.Clifford+CS.Stable.HyperSem
  (c4 : Complete 4) (I : Inputs)
  (K : Set) (G₄ : K → Circuit 4)
  (ind₄ : ∀ κ → GadgetDefs.Indep₀ 0 c4 (G₄ κ))
  (f6 : ∀ κ → Inputs.Bnd I 0 → GadgetDefs.TopTarget 0 c4 (G₄ κ))
  (ssym : ∀ κ m → Inputs.Bnd I (suc m) →
          GadgetDefs.SwapSym (suc m) c4 (GadgetAll.gad c4 I (G₄ κ) (ind₄ κ) (f6 κ) (suc m)))
  where

open import Algebra.Bundles using (Monoid)
open import Data.Bool using (false)
open import Data.List using (List)
open import Data.Product using (_,_)
open import Data.Vec using ([] ; _∷_ ; _∷ʳ_)
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; _•_)

open import Notations using (₀ ; ₁₊)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_ ; up)
open import Examples.Groups.Clifford+CS.Semantics.Control using (blk ; ctrl⁰)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Lambda using (λ⁰ʷ)
open import Examples.Groups.Clifford+CS.Lambda.Semantics using (⟦•⟧ ; λ⁰-sem)
open import Examples.Groups.Clifford+CS.Stable.Soundness using (soundᵧ)
open import Examples.Groups.Clifford+CS.Stable.HypFrom using (Completeᵧ)
import Examples.Groups.Clifford+CS.Affine.Theory as Theory
import Examples.Groups.Clifford+CS.Affine.Circuits as Circuits
open import Examples.Groups.Clifford+CS.Stable.Hyper c4 I K G₄ ind₄ f6 ssym

------------------------------------------------------------------------
-- The white control is injective

private
  blk-lo : ∀ {n} (P M : Op n) (x y : Bits n) → blk P M (x ∷ʳ false) (y ∷ʳ false) ≡ P x y
  blk-lo {₀}    P M []      []      = Eq.refl
  blk-lo {₁₊ n} P M (a ∷ x) (b ∷ y) = blk-lo {n} (λ u v → P (a ∷ u) (b ∷ v)) (λ u v → M (a ∷ u) (b ∷ v)) x y

ctrl⁰-inj : ∀ {n} {s t : Scaled n} → ctrl⁰ s ~ ctrl⁰ t → s ~ t
ctrl⁰-inj {s = l , M} {l′ , M′} e x y =
  Eq.trans (Eq.cong (γ^ l′ *_) (Eq.sym (blk-lo M (scal (γ^ l)) x y)))
    (Eq.trans (e (x ∷ʳ false) (y ∷ʳ false)) (Eq.cong (γ^ l *_) (blk-lo M′ (scal (γ^ l′)) x y)))

------------------------------------------------------------------------
-- The step

open Inputs I using (Bnd)

module _ (m : ℕ) (b : Bnd m) (c : Completeᵧ (₄₊ m)) where
  private
    W : ℕ
    W = suc (₄₊ m)

    module A₁ = Theory (₄₊ m)
    module C₁ = Circuits (suc m) c4
    module R = SetoidR (Monoid.setoid (Scaled-monoid W))

    -- λ⁰ of the moved-down word is the conjugate of the decoded word.
    conj : ∀ (τ : Word A₁.Lt) (ℓ : List (Lit (suc m))) (k : List (Lit m)) → Ne ℓ → ren m τ ℓ ≡ up m k →
           W ⊢ᵧ λ⁰ʷ (D m k) ≈ C₁.⟪ τ ⟫ʷ • D (suc m) ℓ • C₁.⟪ A₁.rev τ ⟫ʷ
    conj τ ℓ k n e =
      PB.trans (PB.sym (D-top m b k))
        (PB.trans (Eq.subst (λ x → W ⊢ᵧ D (suc m) (up m k) ≈ D (suc m) x) (Eq.sym e) PB.refl)
                  (PB.sym (D-eqv m b τ ℓ n)))

    -- The semantics of a conjugate.
    ⟦conj⟧ : ∀ (a u b : Circuit W) → ⟦ a • u • b ⟧ ~ (⟦ a ⟧ ∙ (⟦ u ⟧ ∙ ⟦ b ⟧))
    ⟦conj⟧ a u b = begin
      ⟦ a • u • b ⟧                    ≈⟨ ⟦•⟧ a (u • b) ⟩
      ⟦ a ⟧ ∙ ⟦ u • b ⟧                ≈⟨ ∙-cong {s = ⟦ a ⟧} {⟦ a ⟧} {⟦ u • b ⟧} {⟦ u ⟧ ∙ ⟦ b ⟧} (~-refl ⟦ a ⟧) (⟦•⟧ u b) ⟩
      ⟦ a ⟧ ∙ (⟦ u ⟧ ∙ ⟦ b ⟧)          ∎
      where open R

  -- Two decoded words on 5 + m wires with the same semantics, whose
  -- states an affine word moves into the hyperplane where the top bit is
  -- 0, are equal, given completeness on 4 + m wires.
  hyper-sem : ∀ (τ : Word A₁.Lt) (ℓ₁ ℓ₂ : List (Lit (suc m))) (k₁ k₂ : List (Lit m)) →
              Ne ℓ₁ → Ne ℓ₂ → ren m τ ℓ₁ ≡ up m k₁ → ren m τ ℓ₂ ≡ up m k₂ →
              ⟦ D (suc m) ℓ₁ ⟧ ~ ⟦ D (suc m) ℓ₂ ⟧ → W ⊢ᵧ D (suc m) ℓ₁ ≈ D (suc m) ℓ₂
  hyper-sem τ ℓ₁ ℓ₂ k₁ k₂ n₁ n₂ e₁ e₂ s =
    hyper m b τ ℓ₁ ℓ₂ k₁ k₂ n₁ n₂ e₁ e₂ (c (ctrl⁰-inj {s = ⟦ D m k₁ ⟧} {⟦ D m k₂ ⟧} chain))
    where
    t t′ : Circuit W
    t  = C₁.⟪ τ ⟫ʷ
    t′ = C₁.⟪ A₁.rev τ ⟫ʷ
    X₁ X₂ : Circuit (₄₊ m)
    X₁ = D m k₁
    X₂ = D m k₂
    open R
    chain : ctrl⁰ ⟦ X₁ ⟧ ~ ctrl⁰ ⟦ X₂ ⟧
    chain = begin
      ctrl⁰ ⟦ X₁ ⟧                                 ≈⟨ ~-sym {s = ⟦ λ⁰ʷ X₁ ⟧} {ctrl⁰ ⟦ X₁ ⟧} (λ⁰-sem X₁) ⟩
      ⟦ λ⁰ʷ X₁ ⟧                                   ≈⟨ soundᵧ (conj τ ℓ₁ k₁ n₁ e₁) ⟩
      ⟦ t • D (suc m) ℓ₁ • t′ ⟧                    ≈⟨ ⟦conj⟧ t (D (suc m) ℓ₁) t′ ⟩
      ⟦ t ⟧ ∙ (⟦ D (suc m) ℓ₁ ⟧ ∙ ⟦ t′ ⟧)          ≈⟨ ∙-cong {s = ⟦ t ⟧} {⟦ t ⟧} {⟦ D (suc m) ℓ₁ ⟧ ∙ ⟦ t′ ⟧} {⟦ D (suc m) ℓ₂ ⟧ ∙ ⟦ t′ ⟧}
                                                         (~-refl ⟦ t ⟧)
                                                         (∙-cong {s = ⟦ D (suc m) ℓ₁ ⟧} {⟦ D (suc m) ℓ₂ ⟧} {⟦ t′ ⟧} {⟦ t′ ⟧} s (~-refl ⟦ t′ ⟧)) ⟩
      ⟦ t ⟧ ∙ (⟦ D (suc m) ℓ₂ ⟧ ∙ ⟦ t′ ⟧)          ≈⟨ ~-sym {s = ⟦ t • D (suc m) ℓ₂ • t′ ⟧} {⟦ t ⟧ ∙ (⟦ D (suc m) ℓ₂ ⟧ ∙ ⟦ t′ ⟧)}
                                                         (⟦conj⟧ t (D (suc m) ℓ₂) t′) ⟩
      ⟦ t • D (suc m) ℓ₂ • t′ ⟧                    ≈⟨ ~-sym {s = ⟦ λ⁰ʷ X₂ ⟧} {⟦ t • D (suc m) ℓ₂ • t′ ⟧} (soundᵧ (conj τ ℓ₂ k₂ n₂ e₂)) ⟩
      ⟦ λ⁰ʷ X₂ ⟧                                   ≈⟨ λ⁰-sem X₂ ⟩
      ctrl⁰ ⟦ X₂ ⟧                                 ∎

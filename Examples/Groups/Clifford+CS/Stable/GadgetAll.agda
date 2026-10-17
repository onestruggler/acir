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
-- Affine.Decoding); and at two states whose top bit is 0 the decoding
-- is λ⁰ of the decoding one width down (`d-top`, from Affine.Widen and
-- CalcW.conj⁰), the paper's hyperplane lemma for the top wire.
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

open import Data.Bool using (Bool)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)
open import Notations using (₃₊)
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.MultiControlled using (top)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_YVRel,_===_ ; embed)
import Examples.Groups.Clifford+CS.Affine.Theory as Theory
import Examples.Groups.Clifford+CS.Affine.Alpha as Alpha
import Examples.Groups.Clifford+CS.Affine.Circuits as Circuits
import Examples.Groups.Clifford+CS.Affine.Widen as Widen
import Examples.Groups.Clifford+CS.Affine.Decoding as Decoding
import Examples.Groups.Clifford+CS.Stable.CalcW as CalcW

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

    ----------------------------------------------------------------------
    -- The hyperplane lemma for the top wire

    module _ (m : ℕ) where
      private
        module A₀ = Theory (₃₊ m)
        module A₁ = Theory (₄₊ m)
        module Al₀ = Alpha (₃₊ m)
        module Al₁ = Alpha (₄₊ m)
        module C₀ = Circuits m c4
        module C₁ = Circuits (suc m) c4
        module Wd = Widen m c4
        module CW = CalcW m (f4 m) (f5 m) (tr m)
        open Tools ((suc (₄₊ m)) YVRel,_===_)

        ≡→≈ : ∀ {a b : Circuit (suc (₄₊ m))} → a ≡ b → (suc (₄₊ m)) ⊢ᵧ a ≈ b
        ≡→≈ Eq.refl = refl

      -- At two states whose top bit is 0 the decoding is λ⁰ of the
      -- decoding one width down.
      d-top : ∀ (p q : Vec Bool (₄₊ m)) →
              (suc (₄₊ m)) ⊢ᵧ Dec.d (suc m) (p Wd.⁺) (q Wd.⁺) ≈ λ⁰ʷ (Dec.d m p q)
      d-top p q = begin
        C₁.⟪ Al₁.α (p Wd.⁺) (q Wd.⁺) ⟫ʷ • λ⁰ʷ G • C₁.⟪ A₁.rev (Al₁.α (p Wd.⁺) (q Wd.⁺)) ⟫ʷ
          ≈⟨ ≡→≈ (Eq.cong (λ a → C₁.⟪ a ⟫ʷ • λ⁰ʷ G • C₁.⟪ A₁.rev a ⟫ʷ) (Wd.α-⁺ p q)) ⟩
        C₁.⟪ Wd.ι* a ⟫ʷ • λ⁰ʷ G • C₁.⟪ A₁.rev (Wd.ι* a) ⟫ʷ
          ≈⟨ ≡→≈ (Eq.cong (λ b → C₁.⟪ Wd.ι* a ⟫ʷ • λ⁰ʷ G • C₁.⟪ b ⟫ʷ) (Eq.sym (Wd.ι*-rev a))) ⟩
        C₁.⟪ Wd.ι* a ⟫ʷ • λ⁰ʷ G • C₁.⟪ Wd.ι* (A₀.rev a) ⟫ʷ
          ≈⟨ cong (embed (Wd.ι*-top a)) (back _ (embed (Wd.ι*-top (A₀.rev a)))) ⟩
        top C₀.⟪ a ⟫ʷ • λ⁰ʷ G • top C₀.⟪ A₀.rev a ⟫ʷ
          ≈⟨ CW.conj⁰ C₀.⟪ a ⟫ʷ C₀.⟪ A₀.rev a ⟫ʷ G (embed (C₀.⟪⟫-cong (A₀.rev-inv a))) ⟩
        λ⁰ʷ (C₀.⟪ a ⟫ʷ • G • C₀.⟪ A₀.rev a ⟫ʷ) ∎
        where
        G = gad m
        a = Al₀.α p q

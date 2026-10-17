------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding's gadgets at every width, and the affine decoding
--
-- The gadget on 4 + m wires is λ⁰ of the one a width down, starting
-- from a four-wire gadget G₄ (`gad`).  It commutes with every CX whose
-- control is off wire 0 at every width (`indepS`), given that G₄ does
-- on four wires, the paper's (F6) on five, and from six wires on the
-- symmetry of the two top controls of the gadget (Stable.Gadget.step,
-- step′).  So the affine decoding — the gadget carried from the basis
-- states 0, e₀ to p, q by the affine circuit α p q (`dg`) — is
-- equivariant under every affine circuit at every width (`DecS.eqvʷ`,
-- from Affine.Decoding); and at two states whose top bit is 0 the
-- decoding is λ⁰ of the decoding one width down (`d-top`, from
-- Affine.Widen and CalcW.conj⁰), the paper's hyperplane lemma for the
-- top wire.  The λ-calculus is given under the bound of Stable.Inputs:
-- the gadgets and their decodings take none, and a lemma at index m
-- takes `Bnd m`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; zero ; suc)
open import Notations using (₄₊)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ ; λ⁰ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Inputs using (Inputs)
import Examples.Groups.Clifford+CS.Stable.Gadget as Gadget
import Examples.Groups.Clifford+CS.Stable.GadgetDefs as GadgetDefs

module Examples.Groups.Clifford+CS.Stable.GadgetAll (c4 : Complete 4) (I : Inputs) where

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

open Inputs I

module Gd (m : ℕ) (b : Bnd m) = Gadget m c4 (f4 m b) (f5 m) (tr m b)
module GD (m : ℕ) = GadgetDefs m c4

module _
  (G₄ : Circuit 4)
  (ind₄ : GD.Indep₀ 0 G₄)
  (f6 : Bnd 0 → GD.TopTarget 0 G₄)
  where

  -- The gadget on 4 + m wires.
  gad : ∀ m → Circuit (₄₊ m)
  gad zero    = G₄
  gad (suc m) = λ⁰ʷ (gad m)

  -- Its affine decoding on two states.
  dg : ∀ m → Vec Bool (₄₊ m) → Vec Bool (₄₊ m) → Circuit (₄₊ m)
  dg m p q = Circuits.⟪_⟫ʷ m c4 (Alpha.α (₃₊ m) p q) • gad m • Circuits.⟪_⟫ʷ m c4 (Theory.rev (₃₊ m) (Alpha.α (₃₊ m) p q))

  ----------------------------------------------------------------------
  -- The hyperplane lemma for the top wire

  module _ (m : ℕ) (b : Bnd m) where
    private
      module A₀ = Theory (₃₊ m)
      module A₁ = Theory (₄₊ m)
      module Al₀ = Alpha (₃₊ m)
      module Al₁ = Alpha (₄₊ m)
      module C₀ = Circuits m c4
      module C₁ = Circuits (suc m) c4
      module Wd = Widen m c4
      module CW = CalcW m (f4 m b) (f5 m) (tr m b)
      open Tools ((suc (₄₊ m)) YVRel,_===_)

      ≡→≈ : ∀ {a b : Circuit (suc (₄₊ m))} → a ≡ b → (suc (₄₊ m)) ⊢ᵧ a ≈ b
      ≡→≈ Eq.refl = refl

    -- At two states whose top bit is 0 the decoding is λ⁰ of the
    -- decoding one width down.
    d-top : ∀ (p q : Vec Bool (₄₊ m)) →
            (suc (₄₊ m)) ⊢ᵧ dg (suc m) (p Wd.⁺) (q Wd.⁺) ≈ λ⁰ʷ (dg m p q)
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

  ----------------------------------------------------------------------
  -- Independence, and the equivariance of the decoding

  module _ (sym : ∀ m → Bnd (suc m) → GD.SwapSym (suc m) (gad (suc m))) where

    -- The gadget on 5 + m wires commutes with every CX whose control is
    -- off wire 0, given the inputs at index m.
    indepS : ∀ m → Bnd m → GD.Indep₀ (suc m) (gad (suc m))
    indepS zero    b = Gd.step 0 b G₄ ind₄ (f6 b)
    indepS (suc m) b = Gd.step′ (suc m) b (gad (suc m)) (indepS m (down b)) (sym m b)

    -- The affine decoding on 4 wires and on 5 + m, and its equivariance.
    module Dec0 = Decoding.Gate 0 c4 (4 YVRel,_===_) embed G₄ ind₄
    module DecS (m : ℕ) (b : Bnd m) =
      Decoding.Gate (suc m) c4 ((₄₊ (suc m)) YVRel,_===_) embed (gad (suc m)) (indepS m b)

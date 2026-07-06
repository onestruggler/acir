------------------------------------------------------------------------
-- Presentations of groups
--
-- Normal-form properties for sugar products of group presentations:
-- every extra generator m is definable, via the desugaring axiom
-- [ m ]ʷ ≈ [ f m ]ᵣ, so normal forms transport from Δ to Γ ⋄ Δ ⋄ SugarRel f
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Word.Base

module Presentation.Construct.Properties.SugarProduct
  {M A : Set}
  (Γ : WRel M)
  (Δ : WRel A)
  (f : M → Word A)
  where

open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Function using (_∘_)
open import Function.Definitions using (Congruent ; Injective)
import Function.Construct.Composition as FCC
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR

import Presentation.Base as PB
import Presentation.Properties as PP
open import Normalization.Base using (NormalFormWithoutInverse ; NormalForm)
open import Presentation.Reidemeister-Schreier
open import Presentation.Construct.Base

open PB Γ renaming (_===_ to _===₁_) using ()
open PB Δ renaming (_≈_ to _≈₂_) using ()
open PP Δ renaming (word-setoid to word-setoid₂) using ()

open PB (Γ ⋄ Δ ⋄ SugarRel f) using (_===_ ; _≈_)
open PP (Γ ⋄ Δ ⋄ SugarRel f) renaming (word-setoid to ws) using ()

open _≈_

module _
  (f-wd-ax : ∀ {w v} → w ===₁ v → ((f *) w) ≈₂ ((f *) v))
  where

  X = M ⊎ A

  -- Desugar one generator: an extra generator m becomes f m, a plain
  -- generator stays itself.
  to-right : X → Word A
  to-right (inj₁ x) = f x
  to-right (inj₂ y) = [ y ]ʷ

  -- Every generator is congruent to its desugaring.
  to-right-right : ∀ x → [ x ]ʷ ≈ [ to-right x ]ᵣ
  to-right-right (inj₁ x) = axiom (mid desugar)
  to-right-right (inj₂ y) = refl

  -- Every word is congruent to its desugaring.
  to-right*-right : ∀ w → w ≈ [ (to-right *) w ]ᵣ
  to-right*-right [ x ]ʷ = to-right-right x
  to-right*-right ε = _≈_.refl
  to-right*-right (w • w₁) with to-right*-right w | to-right*-right w₁
  to-right*-right (w • w₁) | ih1 | ih2 = _≈_.cong ih1 ih2

  -- Desugaring is the identity on right-embedded words.
  lemma-to-right-r : ∀ w → (to-right *) [ w ]ᵣ ≡ w
  lemma-to-right-r [ x ]ʷ = Eq.refl
  lemma-to-right-r ε = Eq.refl
  lemma-to-right-r (w • w₁) rewrite lemma-to-right-r w | lemma-to-right-r w₁  = Eq.refl

  -- Desugaring a left-embedded word is embedding via f.
  lemma-to-right-l : ∀ w → (to-right *) [ w ]ₗ ≡ (f *) w
  lemma-to-right-l [ x ]ʷ = Eq.refl
  lemma-to-right-l ε = Eq.refl
  lemma-to-right-l (w • w₁) rewrite lemma-to-right-l w | lemma-to-right-l w₁ = Eq.refl

  -- Desugaring respects the axioms of the sugar product.
  to-right-wd :  ∀ {w v} → w === v → (to-right *) w ≈₂ (to-right *) v
  to-right-wd {w} {v} (left {u} {v₁} x) = begin
    (to-right *) [ u ]ₗ ≡⟨ lemma-to-right-l u ⟩
    (f *) u ≈⟨ f-wd-ax x ⟩
    (f *) v₁ ≡⟨ Eq.sym (lemma-to-right-l v₁) ⟩
    (to-right *) [ v₁ ]ₗ ∎
    where
    open SR word-setoid₂
  to-right-wd {w} {v} (right {u} {v₁} x) rewrite lemma-to-right-r u | lemma-to-right-r v₁ = _≈₂_.axiom x
  to-right-wd {w} {v} (mid (desugar {m})) rewrite lemma-to-right-r (f m) = _≈₂_.refl

  -- Desugaring is a congruence for the full congruence closure.
  to-right*-cong = Star-Congruence.lemma-f*-cong (Γ ⋄ Δ ⋄ SugarRel f) Δ to-right to-right-wd

  private module LR = LeftRightCongruence Γ Δ (SugarRel f)

  -- Desugaring is injective: right-embedding is a congruence and
  -- inverts it up to ≈.
  to-right*-inj : Injective _≈_ _≈₂_ (to-right *)
  to-right*-inj {x} {y} eq = begin
    x ≈⟨ to-right*-right x ⟩
    [ (to-right *) x ]ᵣ ≈⟨ LR.rights eq ⟩
    [ (to-right *) y ]ᵣ ≈⟨ sym (to-right*-right y) ⟩
    y ∎
    where
    open SR ws

  -- A normal form for Δ transports to the sugar product: normalise
  -- the desugaring.
  nfp : NormalFormWithoutInverse Δ → NormalFormWithoutInverse (Γ ⋄ Δ ⋄ SugarRel f)
  nfp p = record { NF = NF ; nf = nf ∘ (to-right *) ; nf-cong = nf'-cong ; nf-injective = nf'-inj }
    where
    open NormalFormWithoutInverse p

    nf' = nf ∘ (to-right *)

    nf'-cong : Congruent _≈_ _≡_ nf'
    nf'-cong = FCC.congruent _≈_ _≈₂_ _≡_ to-right*-cong nf-cong

    nf'-inj : Injective _≈_ _≡_ nf'
    nf'-inj = FCC.injective _≈_ _≈₂_ _≡_ to-right*-inj nf-injective

  -- Like nfp, but also transporting the section: realise the normal
  -- form in Δ and right-embed it.
  nfp' : NormalForm Δ → NormalForm (Γ ⋄ Δ ⋄ SugarRel f)
  nfp' p = record
             { NF = NF ; nf = nf' ; nf-cong = nf'-cong ; inv-nf = inv-nf' ; inv-nf∘nf=id = inv-nf'∘nf'=id }
    where
    open NormalForm p

    nf' = nf ∘ (to-right *)

    inv-nf' : NF → Word X
    inv-nf' = [_]ᵣ ∘ inv-nf

    nf'-cong : Congruent _≈_ _≡_ nf'
    nf'-cong = FCC.congruent _≈_ _≈₂_ _≡_ to-right*-cong nf-cong

    inv-nf'∘nf'=id : {w : Word (M ⊎ A)} → inv-nf' (nf' w) ≈ w
    inv-nf'∘nf'=id {w} = begin
      inv-nf' (nf' w) ≈⟨ refl ⟩
      ([_]ᵣ ∘ inv-nf ∘ nf ∘ (to-right *)) (w) ≈⟨ LR.rights inv-nf∘nf=id ⟩
      ([_]ᵣ ∘ (to-right *)) (w) ≈⟨ sym (to-right*-right w) ⟩
      w ∎
      where
      open SR ws

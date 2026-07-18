------------------------------------------------------------------------
-- Presentations of groups
--
-- Normal-form properties for sugar products of group presentations:
-- every extra generator m is definable, via the desugaring axiom
-- [ m ]ʷ ≈ [ f m ]ᵣ, so normal forms transport from Δ to Γ ⋄ Δ ⋄ SugarRel f
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

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
open import Normalization.NormalForm.Propositional using (NormalFormInjective ; NormalForm)
import Normalization.NormalForm.Setoid as SNF
open import Normalization.Reidemeister-Schreier
open import Presentation.Construct.Base

open PB Γ renaming (_===_ to _===₁_) using ()
open PB Δ renaming (_≈_ to _≈₂_) using ()
open PP Δ renaming (word-setoid to word-setoid₂) using ()

open PB (Γ ⋄ Δ ⋄ SugarRel f) using (_===_ ; _≈_)
open PP (Γ ⋄ Δ ⋄ SugarRel f) renaming (word-setoid to ws) using ()

open _≈_

module _
  (f-wd-ax : ∀ {w v} → w ===₁ v → ((f ʷ) w) ≈₂ ((f ʷ) v))
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
  to-rightʷ-right : ∀ w → w ≈ [ (to-right ʷ) w ]ᵣ
  to-rightʷ-right [ x ]ʷ = to-right-right x
  to-rightʷ-right ε = _≈_.refl
  to-rightʷ-right (w • w₁) with to-rightʷ-right w | to-rightʷ-right w₁
  to-rightʷ-right (w • w₁) | ih1 | ih2 = _≈_.cong ih1 ih2

  -- Desugaring is the identity on right-embedded words.
  lemma-to-right-r : ∀ w → (to-right ʷ) [ w ]ᵣ ≡ w
  lemma-to-right-r [ x ]ʷ = Eq.refl
  lemma-to-right-r ε = Eq.refl
  lemma-to-right-r (w • w₁) rewrite lemma-to-right-r w | lemma-to-right-r w₁  = Eq.refl

  -- Desugaring a left-embedded word is embedding via f.
  lemma-to-right-l : ∀ w → (to-right ʷ) [ w ]ₗ ≡ (f ʷ) w
  lemma-to-right-l [ x ]ʷ = Eq.refl
  lemma-to-right-l ε = Eq.refl
  lemma-to-right-l (w • w₁) rewrite lemma-to-right-l w | lemma-to-right-l w₁ = Eq.refl

  -- Desugaring respects the axioms of the sugar product.
  to-right-wd :  ∀ {w v} → w === v → (to-right ʷ) w ≈₂ (to-right ʷ) v
  to-right-wd {w} {v} (left {u} {v₁} x) = begin
    (to-right ʷ) [ u ]ₗ ≡⟨ lemma-to-right-l u ⟩
    (f ʷ) u ≈⟨ f-wd-ax x ⟩
    (f ʷ) v₁ ≡⟨ Eq.sym (lemma-to-right-l v₁) ⟩
    (to-right ʷ) [ v₁ ]ₗ ∎
    where
    open SR word-setoid₂
  to-right-wd {w} {v} (right {u} {v₁} x) rewrite lemma-to-right-r u | lemma-to-right-r v₁ = _≈₂_.axiom x
  to-right-wd {w} {v} (mid (desugar {m})) rewrite lemma-to-right-r (f m) = _≈₂_.refl

  -- Desugaring respects the full monoid congruence _≈_.
  to-rightʷ-cong = PP.StarCongruence.fʷ-cong (Γ ⋄ Δ ⋄ SugarRel f) Δ to-right to-right-wd

  private module LR = LeftRightCongruence Γ Δ (SugarRel f)

  -- Desugaring is injective: right-embedding is a congruence and
  -- inverts it up to ≈.
  to-rightʷ-inj : Injective _≈_ _≈₂_ (to-right ʷ)
  to-rightʷ-inj {x} {y} eq = begin
    x ≈⟨ to-rightʷ-right x ⟩
    [ (to-right ʷ) x ]ᵣ ≈⟨ LR.rights eq ⟩
    [ (to-right ʷ) y ]ᵣ ≈⟨ sym (to-rightʷ-right y) ⟩
    y ∎
    where
    open SR ws

  -- A normal form for Δ transports to the sugar product: normalise
  -- the desugaring.
  nfp : ∀ {NF} → NormalFormInjective Δ NF → NormalFormInjective (Γ ⋄ Δ ⋄ SugarRel f) NF
  nfp p = record
    { injection = record { to = nf ∘ (to-right ʷ) ; cong = nf'-cong ; injective = nf'-inj } }
    where
    open SNF.NormalFormInjective p

    nf' = nf ∘ (to-right ʷ)

    nf'-cong : Congruent _≈_ _≡_ nf'
    nf'-cong = FCC.congruent _≈_ _≈₂_ _≡_ to-rightʷ-cong nf-cong

    nf'-inj : Injective _≈_ _≡_ nf'
    nf'-inj = FCC.injective _≈_ _≈₂_ _≡_ to-rightʷ-inj nf-injective

  -- Like nfp, but also transporting the section: realise the normal
  -- form in Δ and right-embed it.
  nfp' : ∀ {NF} → NormalForm Δ NF → NormalForm (Γ ⋄ Δ ⋄ SugarRel f) NF
  nfp' {NF} p = record
    { rightInverse = record
        { to        = nf'
        ; from      = inv-nf'
        ; to-cong   = nf'-cong
        ; from-cong = λ { Eq.refl → refl }
        ; inverseʳ  = λ { Eq.refl → inv-nf'∘nf'=id }
        }
    }
    where
    open SNF.NormalForm p

    nf' = nf ∘ (to-right ʷ)

    inv-nf' : NF → Word X
    inv-nf' = [_]ᵣ ∘ inv-nf

    nf'-cong : Congruent _≈_ _≡_ nf'
    nf'-cong = FCC.congruent _≈_ _≈₂_ _≡_ to-rightʷ-cong nf-cong

    inv-nf'∘nf'=id : {w : Word (M ⊎ A)} → inv-nf' (nf' w) ≈ w
    inv-nf'∘nf'=id {w} = begin
      inv-nf' (nf' w) ≈⟨ refl ⟩
      ([_]ᵣ ∘ inv-nf ∘ nf ∘ (to-right ʷ)) (w) ≈⟨ LR.rights inv-nf∘nf=id ⟩
      ([_]ᵣ ∘ (to-right ʷ)) (w) ≈⟨ sym (to-rightʷ-right w) ⟩
      w ∎
      where
      open SR ws

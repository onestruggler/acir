{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base using (WRel ; Word)
open import Level using (0ℓ ; _⊔_)
open import Relation.Binary using (Setoid)

module Normalization.NormalForm.Uniqueness
  {X : Set}
  (Γ : WRel X)
  (NF : Setoid 0ℓ 0ℓ)
  {c d} (Sem : Setoid c d)
  (⟦_⟧ : Word X → Setoid.Carrier Sem)
  where

import Relation.Binary.Reasoning.Setoid as SR

open import Presentation.Base Γ
open import Function.Definitions using (Congruent ; Injective)

open import Normalization.NormalForm.Setoid Γ NF using (NormalForm)

private
  variable
    w v : Word X

open Setoid NF public using ()
  renaming (Carrier to |NF| ; _≈_ to _≈ₙ_ ; refl to reflₙ ; sym to symₙ ; trans to transₙ)
open Setoid Sem using ()
  renaming (Carrier to Cₛ ; _≈_ to _≈₂_ ; sym to sym₂)

-- A normal form with inverse whose section is separated by the
-- semantics ⟦_⟧: normal forms with equal denotations are equal.
record UniqueNormalForm (inv-nf : |NF| -> Word X) : Set (c ⊔ d) where
  field
    unique : ∀ {u v : |NF|} → ⟦ inv-nf u ⟧ ≈₂ ⟦ inv-nf v ⟧ → u ≈ₙ v


-- Soundness together with a unique normal form gives adequacy.
by-normalization : {normalForm : NormalForm} → let open NormalForm normalForm in
                   UniqueNormalForm inv-nf  → Congruent _≈_ _≈₂_ ⟦_⟧ → Injective _≈_ _≈₂_ ⟦_⟧
by-normalization {normalForm} uni sound {x} {y} eq = nf-injective (unique claim)
  where
  open NormalForm normalForm
  open UniqueNormalForm uni
  claim : ⟦ inv-nf (nf x) ⟧ ≈₂ ⟦ inv-nf (nf y) ⟧
  claim = begin
    ⟦ inv-nf (nf x) ⟧ ≈⟨ sound inv-nf∘nf=id ⟩
    ⟦ x ⟧             ≈⟨ eq ⟩
    ⟦ y ⟧             ≈⟨ sym₂ (sound inv-nf∘nf=id) ⟩
    ⟦ inv-nf (nf y) ⟧ ∎
    where open SR Sem


-- Conversely, completeness (semantic injectivity of ⟦_⟧) together
-- with an exact section (nf ∘ inv-nf ≗ id) makes a normal form
-- unique for ⟦_⟧.
module _ (normalForm : NormalForm) where
  open NormalForm normalForm

  by-completeness : (∀ {u} → nf (inv-nf u) ≈ₙ u) →
                    Injective _≈_ _≈₂_ ⟦_⟧ →
                    UniqueNormalForm inv-nf
  by-completeness nf∘inv-nf=id complete = record
    { unique = λ eq →
        transₙ (symₙ nf∘inv-nf=id)
          (transₙ (nf-cong (complete eq)) nf∘inv-nf=id) }



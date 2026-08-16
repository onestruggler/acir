------------------------------------------------------------------------
-- Presentations of groups
--
-- Setoid-valued normal forms for a presented monoid, into a fixed
-- codomain setoid NF.
--
-- Like Normalization.NormalForm.Propositional, but the codomain NF is a
-- Setoid and the normal-form map is a setoid morphism nf : word-setoid
-- ⟶ₛ NF, so its congruence is bundled into the map (no separate nf-cong
-- field).  The witnesses are, on the nose, the stdlib Function.Bundles:
--   NormalFormInjective  =  Injection   word-setoid NF
--   BijectiveNormalForm       =  Bijection   word-setoid NF
--   NormalForm                =  RightInverse word-setoid NF   (nf = to)
-- WeakNormalForm is the exception: its anf stays a plain function (no
-- congruence), only injective.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base using (WRel ; Word)
open import Level using (0ℓ ; _⊔_)
open import Relation.Binary using (Setoid)

module Normalization.NormalForm.Setoid
  {X : Set} (Γ : WRel X) (NF : Setoid 0ℓ 0ℓ) where

open import Data.Empty using (⊥-elim)
open import Data.Product using (∃ ; _,_ ; proj₁ ; proj₂)
open import Function using (_∘_)
open import Function.Bundles using (Injection ; Bijection ; RightInverse ; _⟶ₛ_)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary.Decidable using (yes ; no ; via-injection)
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base using (ε)
open import Presentation.Base Γ
open import Presentation.Core Γ using (word-setoid)
open import Function.Definitions using (Congruent ; Injective)

private
  variable
    w v : Word X

open Setoid NF public using ()
  renaming (Carrier to |NF| ; _≈_ to _≈ₙ_ ; refl to reflₙ ; sym to symₙ ; trans to transₙ)

------------------------------------------------------------------------
-- Normal-form witnesses

-- A normal-form map is a setoid injection out of the word setoid: a
-- morphism nfₛ = injection.function : word-setoid ⟶ₛ NF (which bundles
-- the congruence) that is injective, so  w ≈ v  ⇔  nf w ≈ nf v.
record NormalFormInjective : Set where
  field
    injection : Injection word-setoid NF

  open Injection injection public
    using ()
    renaming (to to nf ; cong to nf-cong ; injective to nf-injective
             ; function to nfₛ)

  -- Prove w ≈ v by comparing normal forms.
  by-equal-nf : nf w ≈ₙ nf v → w ≈ v
  by-equal-nf = nf-injective

  -- Decidable equality of normal forms decides the word problem.
  ≈-dec : Decidable _≈ₙ_ → Decidable _≈_
  ≈-dec = via-injection injection


-- Like NormalFormInjective, but the normal-form map comes with a
-- section inv-nf realising every normal form as a word; this is exactly
-- a RightInverse (inv-nf ∘ nf ≗ id), and injectivity is then derivable.
record NormalForm : Set where
  field
    rightInverse : RightInverse word-setoid NF

  open RightInverse rightInverse public
    using (inverseʳ)
    renaming (to to nf ; from to inv-nf ; to-cong to nf-cong
             ; from-cong to inv-nf-cong)

  -- The normal-form map bundled as a setoid morphism.
  nfₛ : word-setoid ⟶ₛ NF
  nfₛ = record { to = nf ; cong = nf-cong }

  -- inv-nf ∘ nf ≗ id.
  inv-nf∘nf=id : inv-nf (nf w) ≈ w
  inv-nf∘nf=id = inverseʳ reflₙ

  -- Rewrite a word to its canonical representative.
  normalize : Word X → Word X
  normalize = inv-nf ∘ nf

  -- Normalizing does not change the normal form.
  nf-normalize : ∀ x → nf (normalize x) ≈ₙ nf x
  nf-normalize x = nf-cong inv-nf∘nf=id

  -- Normalization is idempotent.
  normalize-idempotent : ∀ x → normalize (normalize x) ≈ normalize x
  normalize-idempotent x = inv-nf-cong (nf-normalize x)

  nf-injective : nf w ≈ₙ nf v → w ≈ v
  nf-injective x = trans (sym inv-nf∘nf=id) (trans (inv-nf-cong x) inv-nf∘nf=id)

  normalFormInjective : NormalFormInjective
  normalFormInjective = record
    { injection = record { to = nf ; cong = nf-cong ; injective = nf-injective } }

  open NormalFormInjective normalFormInjective public
    using (by-equal-nf)


-- Like NormalFormInjective, but also surjective: this is exactly a
-- Bijection.  The surjection's section gives inv-nf, hence a NormalForm.
record BijectiveNormalForm : Set where
  field
    bijection : Bijection word-setoid NF

  open Bijection bijection public
    using (surjective)
    renaming (to to nf ; cong to nf-cong ; injective to nf-injective)

  nfₛ : word-setoid ⟶ₛ NF
  nfₛ = record { to = nf ; cong = nf-cong }

  inv-nf : |NF| → Word X
  inv-nf y = proj₁ (surjective y)

  inv-nf∘nf=id : inv-nf (nf w) ≈ w
  inv-nf∘nf=id {w} = nf-injective (proj₂ (surjective (nf w)) refl)

  inv-nf-cong : ∀ {a b} → a ≈ₙ b → inv-nf a ≈ inv-nf b
  inv-nf-cong {a} {b} eq = nf-injective
    (transₙ (proj₂ (surjective a) refl) (transₙ eq (symₙ (proj₂ (surjective b) refl))))

  normalForm : NormalForm
  normalForm = record
    { rightInverse = record
        { to        = nf
        ; from      = inv-nf
        ; to-cong   = nf-cong
        ; from-cong = inv-nf-cong
        ; inverseʳ  = λ {x} {y} eq →
            nf-injective (transₙ (proj₂ (surjective y) refl) eq)
        }
    }


------------------------------------------------------------------------
-- Fixing the section at the identity
--
-- A coset construction usually wants the identity coset's representative
-- to be the empty word ON THE NOSE, and a normal form built by iterating
-- levels cannot oblige: one level's inverse is a concatenation whatever
-- its arguments, so it differs from ε in head constructor.
--
-- It does not have to.  A Bijection's section is not part of its data —
-- inv-nf y is proj₁ (surjective y) — so it may be changed at any single
-- index without touching the map, its congruence or its injectivity.  At
-- the index nf ε the empty word discharges the surjectivity obligation
--
--     ∃ w. ∀ z. z ≈ w → nf z ≈ₙ u
--
-- by nf-cong alone, so it can simply be put there.  What that costs is
-- the ability to SEE that index, hence the decidability hypothesis.
--
-- The decision never has to reduce: a client gets ε-section-rep from the
-- fact that the two arguments are equal, not by computing with them, so
-- this works at a variable width where nf ε is stuck.

module _ (nfp : BijectiveNormalForm) (_≟_ : Decidable _≈ₙ_) where

  open BijectiveNormalForm nfp

  private
    surj-ε : (u : |NF|) → ∃ λ w → ∀ {z} → z ≈ w → nf z ≈ₙ u
    surj-ε u with u ≟ nf ε
    ... | yes u≈ε = ε , λ z≈ → transₙ (nf-cong z≈) (symₙ u≈ε)
    ... | no  _   = inv-nf u , proj₂ (surjective u)

  -- The same normal form, with ε as the identity's representative.
  ε-section : BijectiveNormalForm
  ε-section = record
    { bijection = record
      { to        = nf
      ; cong      = nf-cong
      ; bijective = nf-injective , surj-ε
      }
    }

  ε-section-rep : BijectiveNormalForm.inv-nf ε-section (nf ε) ≡ ε
  ε-section-rep with nf ε ≟ nf ε
  ... | yes _   = Eq.refl
  ... | no  ≢ε  = ⊥-elim (≢ε reflₙ)


-- A weaker witness: an invariant into NF that is merely injective — the
-- map anf is a plain function (no congruence required).
record WeakNormalForm : Set where
  field
    anf           : Word X → |NF|
    anf-injective : anf w ≈ₙ anf v → w ≈ v

  -- Prove w ≈ v by comparing invariants.
  by-equal-anf : anf w ≈ₙ anf v → w ≈ v
  by-equal-anf = anf-injective


------------------------------------------------------------------------
-- Unique normal form and completeness by normalization
--
-- Both live in Normalization.NormalForm.Uniqueness, which states
-- uniqueness against the SECTION inv-nf rather than against a whole
-- NormalForm record: uniqueness is a property of the section, and
-- indexing it by the record made every client that already had the
-- record carry it twice.  This module used to hold a second copy.



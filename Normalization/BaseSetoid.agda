------------------------------------------------------------------------
-- Presentations of groups
--
-- Setoid-valued normal forms for a presented monoid.
--
-- Like Normalization.Base, but the codomain NF is a Setoid and the
-- normal-form map is a setoid morphism nf : word-setoid ⟶ₛ NF, so its
-- congruence is bundled into the map (no separate nf-cong field).  The
-- witnesses are, on the nose, the stdlib Function.Bundles:
--   NormalFormWithoutInverse  =  Injection   word-setoid NF
--   BijectiveNormalForm       =  Bijection   word-setoid NF
--   NormalForm                =  RightInverse word-setoid NF   (nf = to)
-- WeakNormalForm is the exception: its anf stays a plain function (no
-- congruence), only injective.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base using (WRel ; Word)

module Normalization.BaseSetoid {X : Set} (Γ : WRel X) where

open import Data.Product using (proj₁ ; proj₂)
open import Function using (_∘_)
open import Function.Bundles using (Injection ; Bijection ; RightInverse ; _⟶ₛ_)
open import Level using (0ℓ ; _⊔_) renaming (suc to lsuc)
open import Relation.Binary using (Setoid)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary.Decidable using (via-injection)
import Relation.Binary.Reasoning.Setoid as SR

open import Presentation.Base Γ
import Presentation.Definitions

private
  variable
    w v : Word X

  -- The setoid of words modulo ≈ (a local copy of
  -- Presentation.Properties.word-setoid).
  word-setoid : Setoid 0ℓ 0ℓ
  word-setoid = record
    { Carrier       = Word X
    ; _≈_           = _≈_
    ; isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
    }

------------------------------------------------------------------------
-- Normal-form witnesses

-- A normal-form map is a setoid injection out of the word setoid: a
-- morphism nfₛ = injection.function : word-setoid ⟶ₛ NF (which bundles
-- the congruence) that is injective, so  w ≈ v  ⇔  nf w ≈ nf v.
record NormalFormWithoutInverse : Set₁ where
  field
    NF        : Setoid 0ℓ 0ℓ
    injection : Injection word-setoid NF

  open Setoid NF public using () renaming (_≈_ to _≈ₙ_)
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


-- Like NormalFormWithoutInverse, but the normal-form map comes with a
-- section inv-nf realising every normal form as a word; this is exactly
-- a RightInverse (inv-nf ∘ nf ≗ id), and injectivity is then derivable.
record NormalForm : Set₁ where
  field
    NF           : Setoid 0ℓ 0ℓ
    rightInverse : RightInverse word-setoid NF

  open Setoid NF public using () renaming (_≈_ to _≈ₙ_ ; refl to reflₙ)
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

  hasNormalFormWithoutInverse : NormalFormWithoutInverse
  hasNormalFormWithoutInverse = record
    { NF = NF
    ; injection = record { to = nf ; cong = nf-cong ; injective = nf-injective }
    }

  open NormalFormWithoutInverse hasNormalFormWithoutInverse public
    using (by-equal-nf)


-- Like NormalFormWithoutInverse, but also surjective: this is exactly a
-- Bijection.  The surjection's section gives inv-nf, hence a NormalForm.
record BijectiveNormalForm : Set₁ where
  field
    NF        : Setoid 0ℓ 0ℓ
    bijection : Bijection word-setoid NF

  open Setoid NF public using ()
    renaming (_≈_ to _≈ₙ_ ; sym to symₙ ; trans to transₙ)
  open Bijection bijection public
    using (surjective)
    renaming (to to nf ; cong to nf-cong ; injective to nf-injective)

  nfₛ : word-setoid ⟶ₛ NF
  nfₛ = record { to = nf ; cong = nf-cong }

  inv-nf : Setoid.Carrier NF → Word X
  inv-nf y = proj₁ (surjective y)

  inv-nf∘nf=id : inv-nf (nf w) ≈ w
  inv-nf∘nf=id {w} = nf-injective (proj₂ (surjective (nf w)) refl)

  inv-nf-cong : ∀ {a b} → a ≈ₙ b → inv-nf a ≈ inv-nf b
  inv-nf-cong {a} {b} eq = nf-injective
    (transₙ (proj₂ (surjective a) refl) (transₙ eq (symₙ (proj₂ (surjective b) refl))))

  hasNormalForm : NormalForm
  hasNormalForm = record
    { NF = NF
    ; rightInverse = record
        { to        = nf
        ; from      = inv-nf
        ; to-cong   = nf-cong
        ; from-cong = inv-nf-cong
        ; inverseʳ  = λ {x} {y} eq →
            nf-injective (transₙ (proj₂ (surjective y) refl) eq)
        }
    }


-- A weaker witness: an invariant into a setoid that is merely injective
-- — the map anf is a plain function (no congruence required).
record WeakNormalForm : Set₁ where
  field
    ANF : Setoid 0ℓ 0ℓ
  open Setoid ANF public using () renaming (Carrier to |ANF| ; _≈_ to _≈ₐ_)
  field
    anf           : Word X → |ANF|
    anf-injective : anf w ≈ₐ anf v → w ≈ v

  -- Prove w ≈ v by comparing invariants.
  by-equal-anf : anf w ≈ₐ anf v → w ≈ v
  by-equal-anf = anf-injective


------------------------------------------------------------------------
-- Unique normal form and completeness by normalization
--
-- The syntactic setoid is the setoid of words of Γ modulo ≈; ⟦_⟧ is a
-- semantics into some setoid Sem.

module _ {c d} (Sem : Setoid c d)
  (let open Setoid Sem using () renaming (Carrier to Cₛ ; _≈_ to _≈₂_ ; sym to sym₂))
  (⟦_⟧ : Word X → Cₛ)
  where

  open Presentation.Definitions.SubPresentation word-setoid Sem

  -- A normal form with inverse whose section is separated by the
  -- semantics ⟦_⟧: normal forms with equal denotations are equal.
  record UniqueNormalForm : Set (lsuc 0ℓ ⊔ c ⊔ d) where
    field
      normalForm : NormalForm
    open NormalForm normalForm public
    field
      unique : ∀ {u v : Setoid.Carrier NF} → ⟦ inv-nf u ⟧ ≈₂ ⟦ inv-nf v ⟧ → u ≈ₙ v

  -- Soundness together with a unique normal form gives completeness.
  by-normalization : UniqueNormalForm → Soundness ⟦_⟧ → Completeness ⟦_⟧
  by-normalization uni sound {x} {y} eq = nf-injective (unique claim)
    where
    open UniqueNormalForm uni
    claim : ⟦ inv-nf (nf x) ⟧ ≈₂ ⟦ inv-nf (nf y) ⟧
    claim = begin
      ⟦ inv-nf (nf x) ⟧ ≈⟨ sound inv-nf∘nf=id ⟩
      ⟦ x ⟧             ≈⟨ eq ⟩
      ⟦ y ⟧             ≈⟨ sym₂ (sound inv-nf∘nf=id) ⟩
      ⟦ inv-nf (nf y) ⟧ ∎
      where open SR Sem

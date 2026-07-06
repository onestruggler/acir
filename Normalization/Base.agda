------------------------------------------------------------------------
-- Presentations of groups
--
-- Normal forms for a presented monoid: canonical-representative
-- functions, their sections, and completeness by normalization
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Word.Base using (WRel ; Word)

module Normalization.Base {X : Set} (Γ : WRel X) where

open import Data.Product using (∃ ; _,_ ; proj₁)
open import Function using (_∘_)
open import Function.Bundles using (Injection)
open import Level using (0ℓ ; _⊔_) renaming (suc to lsuc)
open import Relation.Binary using (Setoid)
open import Relation.Binary.Definitions using (DecidableEquality ; Decidable)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; setoid)
open import Relation.Nullary.Decidable using (via-injection)
import Relation.Binary.Reasoning.Setoid as SR

open import Presentation.Base Γ
import Presentation.Semantics

private
  variable
    w v : Word X

  -- The setoid of words modulo ≈.  (Duplicates
  -- Presentation.Properties.word-setoid, which cannot be imported here
  -- because Presentation.Properties re-exports this module.)
  word-setoid : Setoid 0ℓ 0ℓ
  word-setoid = record
    { Carrier       = Word X
    ; _≈_           = _≈_
    ; isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
    }

------------------------------------------------------------------------
-- Normal-form witnesses

-- A normal-form function: a map nf into a set of canonical
-- representatives that is invariant under ≈ (nf-cong) and complete for
-- it (nf-injective), so that  w ≈ v  ⇔  nf w ≡ nf v.
record NormalFormWithoutInverse : Set₁ where
  field
    NF           : Set
    nf           : Word X → NF
    nf-cong      : w ≈ v → nf w ≡ nf v
    nf-injective : nf w ≡ nf v → w ≈ v

  -- Prove w ≈ v by comparing normal forms (typically by refl).
  by-equal-nf : nf w ≡ nf v → w ≈ v
  by-equal-nf = nf-injective

  -- nf is an injection out of the setoid of words.
  nf-injection : Injection word-setoid (setoid NF)
  nf-injection = record { to = nf ; cong = nf-cong ; injective = nf-injective }

  -- Decidable equality of normal forms decides the word problem.
  ≈-dec : DecidableEquality NF → Decidable _≈_
  ≈-dec deceq = via-injection nf-injection deceq


-- Like NormalFormWithoutInverse, but the normal-form function comes
-- with a section inv-nf realising every normal form as a word;
-- injectivity of nf is then derivable.
record NormalForm : Set₁ where
  field
    NF           : Set
    nf           : Word X → NF
    nf-cong      : w ≈ v → nf w ≡ nf v
    inv-nf       : NF → Word X
    inv-nf∘nf=id : inv-nf (nf w) ≈ w

  -- Rewrite a word to its canonical representative.
  normalize : Word X → Word X
  normalize = inv-nf ∘ nf

  -- Normalizing does not change the normal form.
  nf-normalize : ∀ x → nf (normalize x) ≡ nf x
  nf-normalize x = nf-cong inv-nf∘nf=id

  -- Normalization is idempotent.
  normalize-idempotent : ∀ x → normalize (normalize x) ≡ normalize x
  normalize-idempotent x = Eq.cong inv-nf (nf-normalize x)

  nf-injective : nf w ≡ nf v → w ≈ v
  nf-injective x =
    trans (sym inv-nf∘nf=id) (trans (refl' (Eq.cong inv-nf x)) inv-nf∘nf=id)

  hasNormalFormWithoutInverse : NormalFormWithoutInverse
  hasNormalFormWithoutInverse = record
    { NF = NF ; nf = nf ; nf-cong = nf-cong ; nf-injective = nf-injective }

  open NormalFormWithoutInverse hasNormalFormWithoutInverse public
    using (by-equal-nf)


-- Like NormalFormWithoutInverse, but also surjective: every normal
-- form is realised by some word.  This determines a section, and hence
-- a NormalForm.
record BijectiveNormalForm : Set₁ where
  field
    NF            : Set
    nf            : Word X → NF
    nf-cong       : w ≈ v → nf w ≡ nf v
    nf-injective  : nf w ≡ nf v → w ≈ v
    nf-surjective : ∀ y → ∃ λ w → ∀ {v} → v ≈ w → nf v ≡ y

  inv-nf : NF → Word X
  inv-nf y = nf-surjective y .proj₁

  inv-nf∘nf=id : ∀ {w} → inv-nf (nf w) ≈ w
  inv-nf∘nf=id {w} with nf-surjective (nf w)
  ... | w' , hyp = nf-injective (hyp refl)

  hasNormalForm : NormalForm
  hasNormalForm = record
    { NF = NF ; nf = nf ; nf-cong = nf-cong
    ; inv-nf = inv-nf ; inv-nf∘nf=id = inv-nf∘nf=id
    }


-- A weaker witness: an invariant that is merely injective — no
-- canonicity of the chosen values is required.
record WeakNormalForm : Set₁ where
  field
    ANF           : Set
    anf           : Word X → ANF
    anf-injective : anf w ≡ anf v → w ≈ v

  -- Prove w ≈ v by comparing invariants.
  by-equal-anf : anf w ≡ anf v → w ≈ v
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

  open Presentation.Semantics word-setoid Sem

  -- A normal form with inverse whose section is separated by the
  -- semantics ⟦_⟧: normal forms with equal denotations are equal.
  record UniqueNormalForm : Set (lsuc 0ℓ ⊔ c ⊔ d) where
    field
      normalForm : NormalForm
    open NormalForm normalForm public
    field
      unique : ∀ {u v : NF} → ⟦ inv-nf u ⟧ ≈₂ ⟦ inv-nf v ⟧ → u ≡ v

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

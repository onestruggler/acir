------------------------------------------------------------------------
-- The Agda standard library
--
-- ℕ-indexed families of groups, and embeddings of each level of such a
-- family into the next.
--
-- Typical instances are families indexed by a rank or a width: the
-- symmetric group on n points, or the symplectic group of rank n.  In
-- those examples the embedding of level n into level 1+n adjoins a
-- fixed point (respectively a spectator coordinate).
--
-- An embedding is a levelwise MONOmorphism: injectivity is part of the
-- data, since an arbitrary homomorphism between levels need not be
-- injective and nothing downstream is true without it.  For families
-- where injectivity is not evident, the two standard criteria -- a
-- trivial kernel, or a retraction -- are provided as builders.
--
-- (Staged in ForStdlib for upstreaming into Algebra.Construct.Indexed.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module ForStdlib.Algebra.IndexedGroups where

open import Algebra.Bundles using (Group)
open import Algebra.Bundles.Raw using (RawGroup)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
import Algebra.Properties.Group as GroupProperties
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Function.Definitions using (Injective)
open import Level using (Level; _⊔_) renaming (suc to ℓsuc)
open import Relation.Binary.Core using (Rel)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

private
  variable
    c ℓ : Level

------------------------------------------------------------------------
-- Indexed groups

-- A family of groups indexed by a natural number -- a rank, a width,
-- a number of points.  Level n's carrier and equality are named with
-- the index implicit, so that statements about several levels at once
-- stay readable.

record IndexedGroup (c ℓ : Level) : Set (ℓsuc (c ⊔ ℓ)) where
  field
    group : ℕ → Group c ℓ

  Carrier : ℕ → Set c
  Carrier n = Group.Carrier (group n)

  infix 4 _≈_
  _≈_ : ∀ {n} → Rel (Carrier n) ℓ
  _≈_ {n} = Group._≈_ (group n)

  rawGroup : ℕ → RawGroup c ℓ
  rawGroup n = Group.rawGroup (group n)

------------------------------------------------------------------------
-- Embeddings

-- An embedding of each level into the next: an injective group
-- homomorphism from level n to level 1+n.

record Embedding (IG : IndexedGroup c ℓ) : Set (c ⊔ ℓ) where
  open IndexedGroup IG
  field
    emb : ∀ {n} → Carrier n → Carrier (suc n)
    isGroupMonomorphism : ∀ n → GroupMorphisms.IsGroupMonomorphism
                                  (rawGroup n) (rawGroup (suc n)) (emb {n})

  -- The monomorphism at level n: injective, isGroupHomomorphism, and
  -- (through the latter) homo, ⁻¹-homo, ε-homo, ⟦⟧-cong.
  module Mono (n : ℕ) =
    GroupMorphisms.IsGroupMonomorphism (isGroupMonomorphism n)

  isGroupHomomorphism : ∀ n → GroupMorphisms.IsGroupHomomorphism
                                (rawGroup n) (rawGroup (suc n)) (emb {n})
  isGroupHomomorphism = Mono.isGroupHomomorphism

  -- Injectivity of one step, with the width implicit.
  emb-injective : ∀ {n} → Injective (_≈_ {n}) (_≈_ {suc n}) emb
  emb-injective {n} = Mono.injective n

  -- The k-fold embedding of level n into level k + n.  The index is
  -- written k + n, rather than n + k, so that the recursive call is
  -- accepted without a coercion.
  emb^ : ∀ {n} (k : ℕ) → Carrier n → Carrier (k + n)
  emb^ zero    x = x
  emb^ (suc k) x = emb (emb^ k x)

  -- It is injective too: peel off one embedding at a time.
  emb^-injective : ∀ {n} (k : ℕ) → Injective (_≈_ {n}) (_≈_ {k + n}) (emb^ k)
  emb^-injective zero    eq = eq
  emb^-injective (suc k) eq = emb^-injective k (emb-injective eq)

------------------------------------------------------------------------
-- Building an embedding

-- Two standard routes to the injectivity an Embedding requires, for
-- families where it is not evident.  Both take the levelwise
-- homomorphism and return the whole Embedding.

module _ {IG : IndexedGroup c ℓ} where
  open IndexedGroup IG

  -- Criterion 1: a group homomorphism with trivial kernel is
  -- injective.  From emb x ≈ emb y one gets emb (x ∙ y ⁻¹) ≈ ε, so
  -- x ∙ y ⁻¹ ≈ ε, so x ≈ y.
  fromTrivialKernel :
    (emb : ∀ {n} → Carrier n → Carrier (suc n)) →
    (∀ n → GroupMorphisms.IsGroupHomomorphism
             (rawGroup n) (rawGroup (suc n)) (emb {n})) →
    (∀ {n} {x : Carrier n} →
       emb x ≈ Group.ε (group (suc n)) → x ≈ Group.ε (group n)) →
    Embedding IG
  fromTrivialKernel emb isHomo kernel-trivial = record
    { emb                 = emb
    ; isGroupMonomorphism = λ n → record
      { isGroupHomomorphism = isHomo n
      ; injective           = injective n
      }
    }
    where
    injective : ∀ n → Injective (_≈_ {n}) (_≈_ {suc n}) emb
    injective n {x} {y} eq =
      A.trans (inverseˡ-unique x (y A.⁻¹) (kernel-trivial emb-x∙y⁻¹))
              (⁻¹-involutive y)
      where
      module A = Group (group n)
      module B = Group (group (suc n))
      module H = GroupMorphisms.IsGroupHomomorphism (isHomo n)
      open GroupProperties (group n) using (inverseˡ-unique; ⁻¹-involutive)

      emb-x∙y⁻¹ : emb (x A.∙ (y A.⁻¹)) B.≈ B.ε
      emb-x∙y⁻¹ = begin
        emb (x A.∙ (y A.⁻¹))       ≈⟨ H.homo x (y A.⁻¹) ⟩
        emb x B.∙ emb (y A.⁻¹)     ≈⟨ B.∙-congˡ (H.⁻¹-homo y) ⟩
        emb x B.∙ (emb y B.⁻¹)     ≈⟨ B.∙-congʳ eq ⟩
        emb y B.∙ (emb y B.⁻¹)     ≈⟨ B.inverseʳ (emb y) ⟩
        B.ε                        ∎
        where open ≈-Reasoning B.setoid

  -- Criterion 2: an embedding with a retraction -- a congruent left
  -- inverse, not required to be a homomorphism -- is injective.
  fromRetraction :
    (emb : ∀ {n} → Carrier n → Carrier (suc n)) →
    (∀ n → GroupMorphisms.IsGroupHomomorphism
             (rawGroup n) (rawGroup (suc n)) (emb {n})) →
    (retract : ∀ {n} → Carrier (suc n) → Carrier n) →
    (∀ {n} {x y : Carrier (suc n)} → x ≈ y → retract x ≈ retract y) →
    (∀ {n} (x : Carrier n) → retract (emb x) ≈ x) →
    Embedding IG
  fromRetraction emb isHomo retract retract-cong retract-emb = record
    { emb                 = emb
    ; isGroupMonomorphism = λ n → record
      { isGroupHomomorphism = isHomo n
      ; injective           = injective n
      }
    }
    where
    injective : ∀ n → Injective (_≈_ {n}) (_≈_ {suc n}) emb
    injective n {x} {y} eq = begin
      x                ≈⟨ A.sym (retract-emb x) ⟩
      retract (emb x)  ≈⟨ retract-cong eq ⟩
      retract (emb y)  ≈⟨ retract-emb y ⟩
      y                ∎
      where
      module A = Group (group n)
      open ≈-Reasoning A.setoid

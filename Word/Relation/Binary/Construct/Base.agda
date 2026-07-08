------------------------------------------------------------------------
-- Presentations of groups
--
-- Shared glue for building relations on words: the embeddings [_]ₗ / [_]ᵣ
-- of a coproduct alphabet, the join _⋄_⋄_ and union _∪_ of relations, the
-- empty relation, the n-fold sum of alphabets, and the lemmas lifting a
-- monoid congruence along the embeddings.  Each individual construction
-- (direct product, semi-direct product, …) lives in its own module and
-- builds on this one.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Word.Relation.Binary.Construct.Base where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ ; zero)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)

open import Notations
import Word.Relation.Binary.MonoidCongruence as PB
open import Word.Base

------------------------------------------------------------------------
-- Embeddings

-- Embed a word over A as a word over A ⊎ B.
[_]ₗ : ∀ {A B} → Word A → Word (A ⊎ B)
[_]ₗ {A} {B} = wmap inj₁

-- Embed a word over B as a word over A ⊎ B.
[_]ᵣ : ∀ {A B} → Word B → Word (A ⊎ B)
[_]ᵣ {A} {B} = wmap inj₂

------------------------------------------------------------------------
-- Relation combinators

infix 5 _⋄_⋄_
infixr 5 _∪_

-- Join a relation on Word A, a relation on Word B, and a mixed
-- relation on Word (A ⊎ B) into one relation on Word (A ⊎ B).  The
-- mixed component Γ₃ is what distinguishes the various products.
data _⋄_⋄_ {A B} (Γ₁ : WRel A) (Γ₂ : WRel B) (Γ₃ : WRel (A ⊎ B))
    : WRel (A ⊎ B) where
  left  : ∀ {u v} → Γ₁ u v → (Γ₁ ⋄ Γ₂ ⋄ Γ₃) [ u ]ₗ [ v ]ₗ
  right : ∀ {u v} → Γ₂ u v → (Γ₁ ⋄ Γ₂ ⋄ Γ₃) [ u ]ᵣ [ v ]ᵣ
  mid   : ∀ {u v} → Γ₃ u v → (Γ₁ ⋄ Γ₂ ⋄ Γ₃) u v

-- Union of two relations over the same generating set.
data _∪_ {A} (Γ₁ Γ₂ : WRel A) : WRel A where
  left  : ∀ {u v} → Γ₁ u v → (Γ₁ ∪ Γ₂) u v
  right : ∀ {u v} → Γ₂ u v → (Γ₁ ∪ Γ₂) u v

------------------------------------------------------------------------
-- The empty relation and the n-fold sum of alphabets

-- The empty relation: no axioms.
data EmptyRel {A} : WRel A where

-- n-fold sum of generating sets.
infix 4 _⊎^_
_⊎^_ : Set → ℕ → Set
_⊎^_ A zero = ⊥
_⊎^_ A (₁₊ zero) = A
_⊎^_ A (₂₊ n) = A ⊎ (A ⊎^ (₁₊ n))

------------------------------------------------------------------------
-- Congruence lifting

-- Equalities in the component presentations lift to equalities in
-- the join Γ ⋄ Δ ⋄ Λ, along the embeddings [_]ₗ and [_]ᵣ.
module LeftRightCongruence
  {A B : Set}
  (Γ : WRel A)
  (Δ : WRel B)
  (Λ : WRel (A ⊎ B))
  where

  open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_)
  open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_)
  open PB {A ⊎ B} (Γ ⋄ Δ ⋄ Λ) renaming (_===_ to _===₃_ ; _≈_ to _≈₃_)

  -- [_]ₗ maps the congruence of Γ into the congruence of the join.
  lefts :  ∀ {u v} → u ≈₁ v → [ u ]ₗ ≈₃ [ v ]ₗ
  lefts {u} {v} refl = _≈₃_.refl
  lefts {u} {v} (sym h) = _≈₃_.sym (lefts h)
  lefts {u} {v} (trans h h₁) = _≈₃_.trans (lefts h) (lefts h₁)
  lefts {u} {v} (cong h h₁) = _≈₃_.cong (lefts h) (lefts h₁)
  lefts {u} {v} assoc = _≈₃_.assoc
  lefts {u} {v} left-unit = _≈₃_.left-unit
  lefts {u} {v} right-unit = _≈₃_.right-unit
  lefts {u} {v} (axiom x) = _≈₃_.axiom (left x)

  -- [_]ᵣ maps the congruence of Δ into the congruence of the join.
  rights :  ∀ {u v} → u ≈₂ v → [ u ]ᵣ ≈₃ [ v ]ᵣ
  rights {u} {v} refl = _≈₃_.refl
  rights {u} {v} (sym h) = _≈₃_.sym (rights h)
  rights {u} {v} (trans h h₁) = _≈₃_.trans (rights h) (rights h₁)
  rights {u} {v} (cong h h₁) = _≈₃_.cong (rights h) (rights h₁)
  rights {u} {v} assoc = _≈₃_.assoc
  rights {u} {v} left-unit = _≈₃_.left-unit
  rights {u} {v} right-unit = _≈₃_.right-unit
  rights {u} {v} (axiom x) = _≈₃_.axiom (right x)

-- Equalities in either component presentation lift to equalities in
-- the union Γ ∪ Δ.
module LeftRightCongruence-∪
  {A : Set}
  (Γ : WRel A)
  (Δ : WRel A)
  where

  open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_)
  open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_)
  open PB (Γ ∪ Δ) renaming (_===_ to _===₃_ ; _≈_ to _≈₃_)

  -- The congruence of Γ is included in the congruence of Γ ∪ Δ.
  lefts :  ∀ {u v} → u ≈₁ v → u ≈₃ v
  lefts {u} {v} refl = _≈₃_.refl
  lefts {u} {v} (sym h) = _≈₃_.sym (lefts h)
  lefts {u} {v} (trans h h₁) = _≈₃_.trans (lefts h) (lefts h₁)
  lefts {u} {v} (cong h h₁) = _≈₃_.cong (lefts h) (lefts h₁)
  lefts {u} {v} assoc = _≈₃_.assoc
  lefts {u} {v} left-unit = _≈₃_.left-unit
  lefts {u} {v} right-unit = _≈₃_.right-unit
  lefts {u} {v} (axiom x) = _≈₃_.axiom (left x)

  -- The congruence of Δ is included in the congruence of Γ ∪ Δ.
  rights :  ∀ {u v} → u ≈₂ v → u ≈₃ v
  rights {u} {v} refl = _≈₃_.refl
  rights {u} {v} (sym h) = _≈₃_.sym (rights h)
  rights {u} {v} (trans h h₁) = _≈₃_.trans (rights h) (rights h₁)
  rights {u} {v} (cong h h₁) = _≈₃_.cong (rights h) (rights h₁)
  rights {u} {v} assoc = _≈₃_.assoc
  rights {u} {v} left-unit = _≈₃_.left-unit
  rights {u} {v} right-unit = _≈₃_.right-unit
  rights {u} {v} (axiom x) = _≈₃_.axiom (right x)

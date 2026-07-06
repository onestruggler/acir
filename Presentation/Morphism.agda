------------------------------------------------------------------------
-- Presentations of groups
--
-- Monoid and group homomorphism / monomorphism / isomorphism builders
-- for the extension (f *) and the lift wmap f, together with transfer
-- of normal forms along a generator retraction
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Word.Base

module Presentation.Morphism {A B : Set} (Γ : WRel A) (Δ : WRel B) where

open import Algebra.Bundles using (Monoid ; Group)
open import Algebra.Bundles.Raw using (RawGroup)
open import Algebra.Morphism.Structures
  using (module MonoidMorphisms ; module GroupMorphisms)
open import Data.Product using (proj₂)
open import Function using (_∘_)
open import Function.Definitions using (Surjective)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR

import Presentation.Base as PB
open import Presentation.GroupLike
import Normalization.Base as NFBase
import Presentation.Properties as PP
open import Presentation.Reidemeister-Schreier

open PB Γ renaming
  (_===_ to _===₁_ ; _≈_ to _≈₁_ ; refl to refl₁ ; cong to cong₁ ; sym to sym₁)
open PP Γ renaming (•-ε-monoid to monoid₁)
open PB Δ renaming
  (_===_ to _===₂_ ; _≈_ to _≈₂_ ; refl to refl₂ ; cong to cong₂ ; sym to sym₂)
open PP Δ renaming (•-ε-monoid to monoid₂ ; word-setoid to setoid₂)
open PB

------------------------------------------------------------------------
-- GenCongruence: (f *) and wmap f preserve _≈_

-- GenCongruence for the extension (f *) of a map f : A → Word B.
module StarCongruence
  (f : A → Word B)
  (f-well-defined : ∀ {w v} → w ===₁ v → (f *) w ≈₂ (f *) v)
  where

  -- Extend well-definedness on the axioms to the whole congruence.
  f*-cong : ∀ {w v : Word A} → w ≈₁ v → (f *) w ≈₂ (f *) v
  f*-cong _≈₁_.refl      = _≈₂_.refl
  f*-cong (sym h)        = _≈₂_.sym (f*-cong h)
  f*-cong (trans h h₁)   = _≈₂_.trans (f*-cong h) (f*-cong h₁)
  f*-cong (cong h h₁)    = _≈₂_.cong (f*-cong h) (f*-cong h₁)
  f*-cong assoc          = _≈₂_.assoc
  f*-cong left-unit      = _≈₂_.left-unit
  f*-cong right-unit     = _≈₂_.right-unit
  f*-cong (axiom a)      = f-well-defined a

-- GenCongruence for the lift wmap f of a generator map f : A → B.
module GenCongruence
  (f : A → B)
  (f-well-defined : let f* = wmap f in ∀ {w v} → w ===₁ v → (f*) w ≈₂ (f*) v)
  where

  f* = wmap f

  -- Extend well-definedness on the axioms to the whole congruence.
  f*-cong : ∀ {w v : Word A} → w ≈₁ v → (f*) w ≈₂ (f*) v
  f*-cong _≈₁_.refl      = _≈₂_.refl
  f*-cong (sym h)        = _≈₂_.sym (f*-cong h)
  f*-cong (trans h h₁)   = _≈₂_.trans (f*-cong h) (f*-cong h₁)
  f*-cong (cong h h₁)    = _≈₂_.cong (f*-cong h) (f*-cong h₁)
  f*-cong assoc          = _≈₂_.assoc
  f*-cong left-unit      = _≈₂_.left-unit
  f*-cong right-unit     = _≈₂_.right-unit
  f*-cong (axiom a)      = f-well-defined a

------------------------------------------------------------------------
-- Monoid morphisms

open MonoidMorphisms
  (Monoid.rawMonoid monoid₁) (Monoid.rawMonoid monoid₂)

-- Epimorphisms are not in the standard library.
record IsMonoidEpimorphism (f : Word A → Word B) : Set where
  field
    isMonoidHomomorphism : IsMonoidHomomorphism f
    surjective           : Surjective _≈₁_ _≈₂_ f

  open IsMonoidHomomorphism isMonoidHomomorphism public

-- Build a monoid homomorphism from (f *).
module StarHomomorphism
  (f : A → Word B)
  (f-well-defined : ∀ {w v} → w ===₁ v → (f *) w ≈₂ (f *) v)
  where

  isMonoidHomomorphism : IsMonoidHomomorphism (f *)
  isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = f*-cong f f-well-defined }
      ; homo = λ x y → _≈₂_.refl
      }
    ; ε-homo = _≈₂_.refl
    }
    where open StarCongruence

-- Build a monoid homomorphism from wmap f.
module GenHomomorphism
  (f : A → B)
  (f-well-defined : let f* = wmap f in ∀ {w v} → w ===₁ v → (f*) w ≈₂ (f*) v)
  where

  f* = wmap f

  isMonoidHomomorphism : IsMonoidHomomorphism (f*)
  isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = f*-cong f f-well-defined }
      ; homo = λ x y → _≈₂_.refl
      }
    ; ε-homo = _≈₂_.refl
    }
    where open GenCongruence

-- Build a monoid monomorphism from (f *), using Reidemeister-Schreier.
module StarMonomorphism
  (f : A → Word B)
  (g : B → Word A)
  (f-well-defined : ∀ {w v} → w ===₁ v → (f *) w ≈₂ (f *) v)
  (g-well-defined : ∀ {u t : Word B} → u ===₂ t → (g *) u ≈₁ (g *) t)
  (g-left-inv-gen : ∀ (x : A) → [ x ]ʷ ≈₁ (g *) (f x))
  where

  open StarHomomorphism f f-well-defined
  open Star-Injective-Simplified Γ Δ
  open Reidemeister-Schreier-Simplified f g g-well-defined g-left-inv-gen

  isMonoidMonomorphism : IsMonoidMonomorphism (f *)
  isMonoidMonomorphism = record
    { isMonoidHomomorphism = isMonoidHomomorphism
    ; injective = f*-inj
    }

-- Build a monoid isomorphism from (f *).
module StarIsomorphism
  (f : A → Word B)
  (g : B → Word A)
  (f-well-defined  : ∀ {w v} → w ===₁ v → (f *) w ≈₂ (f *) v)
  (f-left-inv-gen  : ∀ (x : B) → [ x ]ʷ ≈₂ (f *) (g x))
  (g-well-defined  : ∀ {u t : Word B} → u ===₂ t → (g *) u ≈₁ (g *) t)
  (g-left-inv-gen  : ∀ (x : A) → [ x ]ʷ ≈₁ (g *) (f x))
  where

  open StarMonomorphism f g f-well-defined g-well-defined g-left-inv-gen
  open Star-Injective-Simplified Δ Γ
  open Reidemeister-Schreier-Simplified g f f-well-defined f-left-inv-gen
    renaming (g*-surj to f*-surj)

  isMonoidIsomorphism : IsMonoidIsomorphism (f *)
  isMonoidIsomorphism = record
    { isMonoidMonomorphism = isMonoidMonomorphism
    ; surjective = f*-surj
    }

-- Transfer a normal-form witness along a generator bijection.
module WeakNormalFormTransfer
  (f : A → B)
  (g : B → A)
  (f∘g≗id : ∀ x → f (g x) ≡ x)
  (f-well-defined : let f* = wmap f in ∀ {w v} → w ===₁ v → (f*) w ≈₂ (f*) v)
  where

  open GenCongruence f f-well-defined

  -- Precomposing a normal form on Γ with wmap g yields a weak normal
  -- form on Δ.
  weakNormalForm : NFBase.NormalFormWithoutInverse Γ → NFBase.WeakNormalForm Δ
  weakNormalForm gp = record { ANF = NF ; anf = anf ; anf-injective = inj }
    where
    open NFBase.NormalFormWithoutInverse gp
    anf = nf ∘ wmap g
    open SR setoid₂
    g* = wmap g

    f*∘g*≗id : ∀ w → f* (g* w) ≡ w
    f*∘g*≗id [ x ]ʷ   rewrite f∘g≗id x = Eq.refl
    f*∘g*≗id ε        = Eq.refl
    f*∘g*≗id (w • w₁) rewrite f*∘g*≗id w | f*∘g*≗id w₁ = Eq.refl

    inj : {w v : Word B} → nf (wmap g w) ≡ nf (wmap g v) → w ≈₂ v
    inj {w} {v} eq =
      begin w          ≡⟨ Eq.sym (f*∘g*≗id w) ⟩
        f* (g* w)      ≈⟨ f*-cong (nf-injective eq) ⟩
        f* (g* v)      ≡⟨ f*∘g*≗id v ⟩
        v ∎

------------------------------------------------------------------------
-- Group morphisms

-- Upgrade the monoid morphism builders to group morphisms, given
-- Grouplike witnesses for both presentations.
module GroupMorphism
  (group-like₁ : Grouplike _===₁_)
  (group-like₂ : Grouplike _===₂_)
  where

  open Group-Lemmas _===₁_ group-like₁
    renaming (•-ε-group to •-ε-group₁)
  open Group-Lemmas _===₂_ group-like₂
    renaming ( •-ε-group       to •-ε-group₂
             ; inverseˡ-unique to inverseˡ-unique₂
             ; ⁻¹-cong         to ⁻¹-cong₂
             )

  open GroupMorphisms (Group.rawGroup •-ε-group₁) (Group.rawGroup •-ε-group₂)

  -- Build a group homomorphism from (f *).
  module StarGroupHomomorphism
    (f : A → Word B)
    (f-well-defined : ∀ {w v} → w ===₁ v → (f *) w ≈₂ (f *) v)
    where

    open StarCongruence f f-well-defined
    open StarHomomorphism f f-well-defined
    open RawGroup (Group.rawGroup •-ε-group₁) renaming (_⁻¹ to _⁻¹₁)
    open RawGroup (Group.rawGroup •-ε-group₂) renaming (_⁻¹ to _⁻¹₂)

    -- (f *) maps inverses to inverses.
    ⁻¹-homo : ∀ x → (f *) (x ⁻¹₁) ≈₂ ((f *) x) ⁻¹₂
    ⁻¹-homo [ x ]ʷ =
      begin
        (f *) ([ x ]ʷ ⁻¹₁) ≈⟨ inverseˡ-unique₂ {g = (f *) [ x ]ʷ}
              {h = (f *) ([ x ]ʷ ⁻¹₁)} (f*-cong (group-like₁ x .proj₂)) ⟩
        (f *) [ x ]ʷ ⁻¹₂ ∎
      where open SR setoid₂
    ⁻¹-homo ε = refl₂
    ⁻¹-homo (x • y) =
      begin
        (f *) ((x • y) ⁻¹₁) ≈⟨ f*-cong {(x • y) ⁻¹₁} {y ⁻¹₁ • x ⁻¹₁} refl₁ ⟩
        (f *) (y ⁻¹₁ • x ⁻¹₁)         ≈⟨ refl₂ ⟩
        (f *) (y ⁻¹₁) • (f *) (x ⁻¹₁) ≈⟨ cong₂ (⁻¹-homo y) (⁻¹-homo x) ⟩
        ((f *) y) ⁻¹₂ • ((f *) x) ⁻¹₂ ≈⟨ refl₂ ⟩
        (f *) (x • y) ⁻¹₂ ∎
      where open SR setoid₂

    -- (f *) is a group homomorphism.
    isGroupHomomorphism : IsGroupHomomorphism (f *)
    isGroupHomomorphism = record
      { isMonoidHomomorphism = isMonoidHomomorphism
      ; ⁻¹-homo = ⁻¹-homo
      }

  -- Build a group homomorphism from wmap f.
  module GenGroupHomomorphism
    (f : A → B)
    (f-well-defined : let f* = wmap f in ∀ {w v} → w ===₁ v → (f*) w ≈₂ (f*) v)
    where

    open GenCongruence f f-well-defined
    open GenHomomorphism f f-well-defined hiding (f*)
    open RawGroup (Group.rawGroup •-ε-group₁) renaming (_⁻¹ to _⁻¹₁)
    open RawGroup (Group.rawGroup •-ε-group₂) renaming (_⁻¹ to _⁻¹₂)

    -- wmap f maps inverses to inverses.
    ⁻¹-homo : ∀ x → f* (x ⁻¹₁) ≈₂ (f* x) ⁻¹₂
    ⁻¹-homo [ x ]ʷ =
      begin
        f* ([ x ]ʷ ⁻¹₁) ≈⟨ inverseˡ-unique₂ {g = f* [ x ]ʷ}
             {h = f* ([ x ]ʷ ⁻¹₁)} (f*-cong (group-like₁ x .proj₂)) ⟩
        f* [ x ]ʷ ⁻¹₂ ∎
      where open SR setoid₂
    ⁻¹-homo ε = refl₂
    ⁻¹-homo (x • y) =
      begin
        f* ((x • y) ⁻¹₁)        ≈⟨ f*-cong {(x • y) ⁻¹₁} {y ⁻¹₁ • x ⁻¹₁} refl₁ ⟩
        f* (y ⁻¹₁ • x ⁻¹₁)      ≈⟨ refl₂ ⟩
        f* (y ⁻¹₁) • f* (x ⁻¹₁) ≈⟨ cong₂ (⁻¹-homo y) (⁻¹-homo x) ⟩
        (f* y) ⁻¹₂ • (f* x) ⁻¹₂ ≈⟨ refl₂ ⟩
        f* (x • y) ⁻¹₂ ∎
      where open SR setoid₂

    -- wmap f is a group homomorphism.
    isGroupHomomorphism : IsGroupHomomorphism (f*)
    isGroupHomomorphism = record
      { isMonoidHomomorphism = isMonoidHomomorphism
      ; ⁻¹-homo = ⁻¹-homo
      }

  -- Build a group monomorphism from (f *) via Reidemeister-Schreier.
  module StarGroupMonomorphism
    (f : A → Word B)
    (g : B → Word A)
    (f-well-defined : ∀ {w v} → w ===₁ v → (f *) w ≈₂ (f *) v)
    (g-well-defined : ∀ {u t : Word B} → u ===₂ t → (g *) u ≈₁ (g *) t)
    (g-left-inv-gen : ∀ (x : A) → [ x ]ʷ ≈₁ (g *) (f x))
    where

    open StarGroupHomomorphism f f-well-defined
    open Star-Injective-Simplified Γ Δ
    open Reidemeister-Schreier-Simplified f g g-well-defined g-left-inv-gen

    isGroupMonomorphism : IsGroupMonomorphism (f *)
    isGroupMonomorphism = record
      { isGroupHomomorphism = isGroupHomomorphism
      ; injective = f*-inj
      }

  -- Build a group isomorphism from (f *).
  module StarGroupIsomorphism
    (f : A → Word B)
    (g : B → Word A)
    (f-well-defined  : ∀ {w v} → w ===₁ v → (f *) w ≈₂ (f *) v)
    (f-left-inv-gen  : ∀ (x : B) → [ x ]ʷ ≈₂ (f *) (g x))
    (g-well-defined  : ∀ {u t : Word B} → u ===₂ t → (g *) u ≈₁ (g *) t)
    (g-left-inv-gen  : ∀ (x : A) → [ x ]ʷ ≈₁ (g *) (f x))
    where

    open StarGroupMonomorphism f g f-well-defined g-well-defined g-left-inv-gen
    open Star-Injective-Simplified Δ Γ
    open Reidemeister-Schreier-Simplified g f f-well-defined f-left-inv-gen
      renaming (g*-surj to f*-surj)

    isGroupIsomorphism : IsGroupIsomorphism (f *)
    isGroupIsomorphism = record
      { isGroupMonomorphism = isGroupMonomorphism
      ; surjective = f*-surj
      }

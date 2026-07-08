------------------------------------------------------------------------
-- Presentations of groups
--
-- Monoid and group homomorphism / monomorphism / isomorphism builders
-- for the extension (f ʷ) and the lift wmap f, together with transfer
-- of normal forms along a generator retraction
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base

module Presentation.Morphism {A B : Set} (Γ : WRel A) (Δ : WRel B) where

open import Algebra.Bundles using (Monoid ; Group)
open import Algebra.Morphism.Structures
  using (module MonoidMorphisms ; module GroupMorphisms)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR

import Presentation.Base as PB
open import Presentation.GroupLike
import Normalization.Base as NFBase
import Presentation.Properties as PP
open import Normalization.Reidemeister-Schreier
open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)

open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_)
open PP Γ renaming (•-ε-monoid to monoid₁)
open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; refl to refl₂)
open PP Δ renaming (•-ε-monoid to monoid₂ ; word-setoid to setoid₂)

------------------------------------------------------------------------
-- Monoid morphisms
--
-- The congruence lemmas "(f ʷ) / wmap f preserve ≈" live in
-- Presentation.Properties (modules StarCongruence and GenCongruence);
-- the builders below open them at (Γ , Δ).

open MonoidMorphisms
  (Monoid.rawMonoid monoid₁) (Monoid.rawMonoid monoid₂)

-- Build a monoid homomorphism from (f ʷ).
module StarHomomorphism
  (f : A → Word B)
  (f-well-defined : ∀ {w v} → w ===₁ v → (f ʷ) w ≈₂ (f ʷ) v)
  where

  isMonoidHomomorphism : IsMonoidHomomorphism (f ʷ)
  isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = fʷ-cong f f-well-defined }
      ; homo = λ x y → refl₂
      }
    ; ε-homo = refl₂
    }
    where open PP.StarCongruence Γ Δ

-- Build a monoid homomorphism from wmap f.
module GenHomomorphism
  (f : A → B)
  (f-well-defined : let fʷ = wmap f in ∀ {w v} → w ===₁ v → (fʷ) w ≈₂ (fʷ) v)
  where

  fʷ = wmap f

  isMonoidHomomorphism : IsMonoidHomomorphism (fʷ)
  isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = fʷ-cong f f-well-defined }
      ; homo = λ x y → refl₂
      }
    ; ε-homo = refl₂
    }
    where open PP.GenCongruence Γ Δ using (fʷ-cong)

-- Build a monoid monomorphism from (f ʷ), using Reidemeister-Schreier.
module StarMonomorphism
  (f : A → Word B)
  (g : B → Word A)
  (f-well-defined : ∀ {w v} → w ===₁ v → (f ʷ) w ≈₂ (f ʷ) v)
  (g-well-defined : ∀ {u t : Word B} → u ===₂ t → (g ʷ) u ≈₁ (g ʷ) t)
  (g-left-inv-gen : ∀ (x : A) → [ x ]ʷ ≈₁ (g ʷ) (f x))
  where

  open StarHomomorphism f f-well-defined
  open Star-Injective-Simplified Γ Δ
  open Reidemeister-Schreier-Simplified f g g-well-defined g-left-inv-gen

  isMonoidMonomorphism : IsMonoidMonomorphism (f ʷ)
  isMonoidMonomorphism = record
    { isMonoidHomomorphism = isMonoidHomomorphism
    ; injective = fʷ-inj
    }

-- Build a monoid isomorphism from (f ʷ).
module StarIsomorphism
  (f : A → Word B)
  (g : B → Word A)
  (f-well-defined  : ∀ {w v} → w ===₁ v → (f ʷ) w ≈₂ (f ʷ) v)
  (f-left-inv-gen  : ∀ (x : B) → [ x ]ʷ ≈₂ (f ʷ) (g x))
  (g-well-defined  : ∀ {u t : Word B} → u ===₂ t → (g ʷ) u ≈₁ (g ʷ) t)
  (g-left-inv-gen  : ∀ (x : A) → [ x ]ʷ ≈₁ (g ʷ) (f x))
  where

  open StarMonomorphism f g f-well-defined g-well-defined g-left-inv-gen
  open Star-Injective-Simplified Δ Γ
  open Reidemeister-Schreier-Simplified g f f-well-defined f-left-inv-gen
    renaming (gʷ-surj to fʷ-surj)

  isMonoidIsomorphism : IsMonoidIsomorphism (f ʷ)
  isMonoidIsomorphism = record
    { isMonoidMonomorphism = isMonoidMonomorphism
    ; surjective = fʷ-surj
    }

-- Transfer a normal-form witness along a generator bijection.
module WeakNormalFormTransfer
  (f : A → B)
  (g : B → A)
  (f∘g≗id : ∀ x → f (g x) ≡ x)
  (f-well-defined : let fʷ = wmap f in ∀ {w v} → w ===₁ v → (fʷ) w ≈₂ (fʷ) v)
  where

  open PP.GenCongruence Γ Δ f f-well-defined

  -- Precomposing a normal form on Γ with wmap g yields a weak normal
  -- form on Δ.
  weakNormalForm : NFBase.NormalFormWithoutInverse Γ → NFBase.WeakNormalForm Δ
  weakNormalForm gp = record { ANF = NF ; anf = anf ; anf-injective = inj }
    where
    open NFBase.NormalFormWithoutInverse gp
    anf = nf ∘ wmap g
    open SR setoid₂
    gʷ = wmap g

    fʷ∘gʷ≗id : ∀ w → fʷ (gʷ w) ≡ w
    fʷ∘gʷ≗id [ x ]ʷ   rewrite f∘g≗id x = Eq.refl
    fʷ∘gʷ≗id ε        = Eq.refl
    fʷ∘gʷ≗id (w • w₁) rewrite fʷ∘gʷ≗id w | fʷ∘gʷ≗id w₁ = Eq.refl

    inj : {w v : Word B} → nf (wmap g w) ≡ nf (wmap g v) → w ≈₂ v
    inj {w} {v} eq = begin
        w              ≡⟨ Eq.sym (fʷ∘gʷ≗id w) ⟩
        fʷ (gʷ w)      ≈⟨ fʷ-cong (nf-injective eq) ⟩
        fʷ (gʷ v)      ≡⟨ fʷ∘gʷ≗id v ⟩
        v ∎

------------------------------------------------------------------------
-- Group morphisms

-- Upgrade the monoid morphism builders to group morphisms, given
-- Grouplike witnesses for both presentations.
module GroupMorphism
  (group-like₁ : Grouplike _===₁_)
  (group-like₂ : Grouplike _===₂_)
  where

  open Group-Lemmas _===₁_ group-like₁ renaming (•-ε-group to •-ε-group₁)
  open Group-Lemmas _===₂_ group-like₂ renaming (•-ε-group to •-ε-group₂)

  open GroupMorphisms (Group.rawGroup •-ε-group₁) (Group.rawGroup •-ε-group₂)

  -- A monoid homomorphism between the two grouplike presentations is
  -- automatically a group homomorphism (see
  -- ForStdlib.Algebra.Morphism.Consequences), instantiated at the two
  -- word groups.
  module MonoidHom⇒GroupHom
    (h : Word A → Word B)
    (mono : IsMonoidHomomorphism h)
    where

    isGroupHomomorphism : IsGroupHomomorphism h
    isGroupHomomorphism =
      isMonoidHomomorphism⇒isGroupHomomorphism •-ε-group₁ •-ε-group₂ mono

    open IsGroupHomomorphism isGroupHomomorphism public using (⁻¹-homo)

  -- Build a group homomorphism from (f ʷ).
  module StarGroupHomomorphism
    (f : A → Word B)
    (f-well-defined : ∀ {w v} → w ===₁ v → (f ʷ) w ≈₂ (f ʷ) v)
    where

    open StarHomomorphism f f-well-defined using (isMonoidHomomorphism)
    open MonoidHom⇒GroupHom (f ʷ) isMonoidHomomorphism public
      using (⁻¹-homo ; isGroupHomomorphism)

  -- Build a group homomorphism from wmap f.
  module GenGroupHomomorphism
    (f : A → B)
    (f-well-defined : let fʷ = wmap f in ∀ {w v} → w ===₁ v → (fʷ) w ≈₂ (fʷ) v)
    where

    open GenHomomorphism f f-well-defined using (fʷ ; isMonoidHomomorphism)
    open MonoidHom⇒GroupHom fʷ isMonoidHomomorphism public
      using (⁻¹-homo ; isGroupHomomorphism)

  -- Build a group monomorphism from (f ʷ) via Reidemeister-Schreier.
  module StarGroupMonomorphism
    (f : A → Word B)
    (g : B → Word A)
    (f-well-defined : ∀ {w v} → w ===₁ v → (f ʷ) w ≈₂ (f ʷ) v)
    (g-well-defined : ∀ {u t : Word B} → u ===₂ t → (g ʷ) u ≈₁ (g ʷ) t)
    (g-left-inv-gen : ∀ (x : A) → [ x ]ʷ ≈₁ (g ʷ) (f x))
    where

    open StarGroupHomomorphism f f-well-defined
    open Star-Injective-Simplified Γ Δ
    open Reidemeister-Schreier-Simplified f g g-well-defined g-left-inv-gen

    isGroupMonomorphism : IsGroupMonomorphism (f ʷ)
    isGroupMonomorphism = record
      { isGroupHomomorphism = isGroupHomomorphism
      ; injective = fʷ-inj
      }

  -- Build a group isomorphism from (f ʷ).
  module StarGroupIsomorphism
    (f : A → Word B)
    (g : B → Word A)
    (f-well-defined  : ∀ {w v} → w ===₁ v → (f ʷ) w ≈₂ (f ʷ) v)
    (f-left-inv-gen  : ∀ (x : B) → [ x ]ʷ ≈₂ (f ʷ) (g x))
    (g-well-defined  : ∀ {u t : Word B} → u ===₂ t → (g ʷ) u ≈₁ (g ʷ) t)
    (g-left-inv-gen  : ∀ (x : A) → [ x ]ʷ ≈₁ (g ʷ) (f x))
    where

    open StarGroupMonomorphism f g f-well-defined g-well-defined g-left-inv-gen
    open Star-Injective-Simplified Δ Γ
    open Reidemeister-Schreier-Simplified g f f-well-defined f-left-inv-gen
      renaming (gʷ-surj to fʷ-surj)

    isGroupIsomorphism : IsGroupIsomorphism (f ʷ)
    isGroupIsomorphism = record
      { isGroupMonomorphism = isGroupMonomorphism
      ; surjective = fʷ-surj
      }

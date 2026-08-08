------------------------------------------------------------------------
-- Presentations of groups
--
-- Coset normal forms, with the Reidemeister–Schreier hypothesis replaced
-- by a semantic one.
--
-- Normalization.CosetNF.SingleLevel.Transfer takes five hypotheses, of
-- which
--
--   h-wd-ax : ∀ c {u t} → u ===₂ t → ((h ᵗ) c u) ~ ((h ᵗ) c t)
--
-- is by far the hardest: it is the well-definedness of the coset action
-- on every axiom, at every coset.  In the Symplectic development it is
-- `srel-wd`, and it is where essentially all the remaining work sits.
--
-- Crucially, `h-wd-ax` is consumed in exactly ONE place: it feeds
-- Reidemeister-Schreier-Full to produce
--
--   fʷ-injective : (f ʷ) w ≈₂ (f ʷ) v → w ≈₁ v
--
-- Everything else in Transfer (the normal-form map, its inverse, the
-- round-trip laws) comes from RightAction, which does not use it.
--
-- This module obtains that same `fʷ-injective` from semantics instead:
--
--   * SOUNDNESS of the axioms of Δ under an interpretation ⟦_⟧ into a
--     setoid S — i.e. the interpretation is a model.  (Lifted from the
--     axioms to the whole congruence by `Sound.sound` below, by
--     induction on the derivation.)
--
--   * FAITHFULNESS on the subgroup, i.e. uniqueness of the coset
--     decomposition: if two subgroup words have equal interpretations
--     after embedding, they were already related by ≈₁.
--
-- The point is that this breaks the circularity.  Deriving ↑-injectivity
-- from Reidemeister–Schreier requires h-wd-ax at the SAME level, so it
-- cannot be used to prove h-wd-ax.  A semantic model has no such
-- dependency: soundness is proved once, directly, against the semantics
-- (in the Symplectic development, `Transport.sound-ax`), and
-- faithfulness is a statement about the model, not about the coset
-- action.
--
-- Note that `fʷ-injective` obtained this way needs NO coset data at all
-- — not h, not [_], not I.  The coset machinery is only needed for the
-- normal-form half of the construction.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Binary using (Setoid)

open import Level using (0ℓ)
open import Data.Product using (_,_ ; _×_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW

open import Word.Base
open import Word.Properties

import Presentation.Base as PB

module Normalization.CosetNF2 where

------------------------------------------------------------------------
-- Soundness: an interpretation that models the axioms models the whole
-- congruence.
--
-- `_≈_` (Presentation.Base) is the congruence closure of the axioms with
-- the monoid laws adjoined, so a model must respect exactly: congruence
-- for _•_, associativity, the two unit laws, and the axioms.  Given
-- those, soundness for the full relation is immediate by induction —
-- this is the only place the constructors of `_≈_` are inspected.

module Sound
  {X : Set}
  (Γ : WRel X)
  (S : Setoid 0ℓ 0ℓ)
  (⟦_⟧ : Word X → Setoid.Carrier S)
  where

  open Setoid S using ()
    renaming (_≈_ to _≈ˢ_ ; refl to reflˢ ; sym to symˢ ; trans to transˢ)
  open PB Γ

  module _
    (⟦⟧-cong  : ∀ {w w' v v'} → ⟦ w ⟧ ≈ˢ ⟦ w' ⟧ → ⟦ v ⟧ ≈ˢ ⟦ v' ⟧ →
                ⟦ w • v ⟧ ≈ˢ ⟦ w' • v' ⟧)
    (⟦⟧-assoc : ∀ {w v u} → ⟦ (w • v) • u ⟧ ≈ˢ ⟦ w • (v • u) ⟧)
    (⟦⟧-lunit : ∀ {w} → ⟦ ε • w ⟧ ≈ˢ ⟦ w ⟧)
    (⟦⟧-runit : ∀ {w} → ⟦ w • ε ⟧ ≈ˢ ⟦ w ⟧)
    (⟦⟧-ax    : ∀ {w v} → w === v → ⟦ w ⟧ ≈ˢ ⟦ v ⟧)
    where

    -- Soundness for the full congruence.
    sound : ∀ {w v} → w ≈ v → ⟦ w ⟧ ≈ˢ ⟦ v ⟧
    sound refl          = reflˢ
    sound (sym e)       = symˢ (sound e)
    sound (trans e₁ e₂) = transˢ (sound e₁) (sound e₂)
    sound (cong e₁ e₂)  = ⟦⟧-cong (sound e₁) (sound e₂)
    sound assoc         = ⟦⟧-assoc
    sound left-unit     = ⟦⟧-lunit
    sound right-unit    = ⟦⟧-runit
    sound (axiom x)     = ⟦⟧-ax x

------------------------------------------------------------------------
-- Semantic injectivity of the embedding.
--
-- This is the replacement for Reidemeister–Schreier.  Compare
-- CosetNF.SingleLevel.Transfer.fʷ-injective, which is
-- RSF.reidemeister-schreier and needs h=⁻¹f-gen and h-wd-ax.

module SemInjective
  {X Y : Set}
  (Γ : WRel X)                 -- subgroup presentation (letters X)
  (Δ : WRel Y)                 -- group presentation    (letters Y)
  (f : X → Word Y)             -- generator embedding H ↪ G
  (S : Setoid 0ℓ 0ℓ)           -- semantic domain for Δ
  (⟦_⟧ : Word Y → Setoid.Carrier S)
  where

  open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
  open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
  open Setoid S using () renaming (_≈_ to _≈ˢ_)

  [_]ₓ = f ʷ

  module _
    -- The interpretation is a model of Δ: it respects the monoid laws
    -- and validates every axiom.
    (⟦⟧-cong  : ∀ {w w' v v'} → ⟦ w ⟧ ≈ˢ ⟦ w' ⟧ → ⟦ v ⟧ ≈ˢ ⟦ v' ⟧ →
                ⟦ w • v ⟧ ≈ˢ ⟦ w' • v' ⟧)
    (⟦⟧-assoc : ∀ {w v u} → ⟦ (w • v) • u ⟧ ≈ˢ ⟦ w • (v • u) ⟧)
    (⟦⟧-lunit : ∀ {w} → ⟦ ε • w ⟧ ≈ˢ ⟦ w ⟧)
    (⟦⟧-runit : ∀ {w} → ⟦ w • ε ⟧ ≈ˢ ⟦ w ⟧)
    (⟦⟧-ax    : ∀ {u t} → u ===₂ t → ⟦ u ⟧ ≈ˢ ⟦ t ⟧)
    -- Uniqueness of the coset decomposition: the semantics of an
    -- embedded subgroup word determines that word up to ≈₁.  This is
    -- where faithfulness of the model enters; it says the relation
    -- ≈₁ holds as soon as the interpretations agree.
    (reflect  : ∀ (w v : Word X) → ⟦ [ w ]ₓ ⟧ ≈ˢ ⟦ [ v ]ₓ ⟧ → w ≈₁ v)
    where

    module Sd = Sound Δ S ⟦_⟧

    -- Soundness of Δ, lifted to the congruence.
    sound₂ : ∀ {u t} → u ≈₂ t → ⟦ u ⟧ ≈ˢ ⟦ t ⟧
    sound₂ = Sd.sound ⟦⟧-cong ⟦⟧-assoc ⟦⟧-lunit ⟦⟧-runit ⟦⟧-ax

    -- THE REPLACEMENT.  Same statement as
    -- CosetNF.SingleLevel.Transfer.fʷ-injective, but obtained from the
    -- model rather than from Reidemeister–Schreier — so it does not
    -- presuppose h-wd-ax, and can therefore be used to prove it.
    fʷ-injective : (w v : Word X) → [ w ]ₓ ≈₂ [ v ]ₓ → w ≈₁ v
    fʷ-injective w v eq = reflect w v (sound₂ eq)

------------------------------------------------------------------------
-- The h-wd-ax hypothesis, recovered.
--
-- With fʷ-injective in hand from semantics, the coset action's
-- well-definedness on the axioms becomes derivable rather than assumed,
-- PROVIDED the action is sound (h=ract, already a hypothesis of the
-- original Transfer) — this is the shape RhoExAbstract.Strategy-B uses
-- in the Symplectic development: soundness plus cancellation plus
-- injectivity of the lift gives the residual half of every obligation
-- from its coset half.
--
-- The statement is recorded here with its precise dependencies rather
-- than proved: discharging it needs the cancellation lemma of the
-- ambient presented monoid (Presentation.GroupLike.Group-Lemmas), which
-- is not available at this generality — Γ and Δ here are arbitrary
-- presentations, not group-like ones.  Instantiate at a group-like Δ to
-- discharge it.

module Recover
  {X Y : Set}
  (Γ : WRel X) (Δ : WRel Y)
  (C : Set)
  (f : X → Word Y)
  (h : C → Y → Word X × C)
  ([_] : C → Word Y)
  where

  open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
  open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()

  [_]ₓ = f ʷ

  infix 4 _~_
  _~_ = PW.Pointwise _≈₁_ (_≡_ {A = C})

  -- What CosetNF.SingleLevel.Transfer takes as hypothesis (2).
  h-wd-ax-Statement : Set
  h-wd-ax-Statement =
    ∀ (c : C) {u t : Word Y} → u ===₂ t → ((h ᵗ) c u) ~ ((h ᵗ) c t)

  -- The coset half alone — the ≡ component of ~.  In the Symplectic
  -- development this is the part that is pure computation (ExAction,
  -- SrelWDSel11i/j/k all discharge it directly), while the ≈ component
  -- is what costs hundreds of lines per branch.
  coset-half-Statement : Set
  coset-half-Statement =
    ∀ (c : C) {u t : Word Y} → u ===₂ t →
      ((h ᵗ) c u) .proj₂ ≡ ((h ᵗ) c t) .proj₂

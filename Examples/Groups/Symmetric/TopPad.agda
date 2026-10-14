------------------------------------------------------------------------
-- Presentations of groups
--
-- Sₙ's rules on their own wires, padded by Circuit.TopPad, give the
-- same congruence as Syntactics' rules at every width, lifted by
-- Circuit.Base's Lift-Relation
--
-- Syntactics states order and yang-baxter at every width (₂₊ n and
-- ₃₊ n: the rule on the bottom wires of any wider circuit) and opens
-- Lift-Relation over them.  Here the same two rules are stated on their
-- own wires only (2 and 3), and Top-Pad adds an idle wire on top
-- (cong↓) beside the structural rules.  The circuits are the same
-- words, and each relation's rules hold in the other's congruence:
--
--   * a rule at width ₂₊ n is the rule on its own wires with n idle
--     wires on top (order↓, yang-baxter↓);
--   * back, a rule on its own wires is the rule at n = 0, and an idle
--     wire on top is closure of Lift-Relation's congruence under ⇓,
--     which holds rule by rule (lr-⇓): a rule's words are closed, so
--     ⇓'d it is the same rule one wire wider, and cong↑ commutes with
--     the new wire (↑⇓).
--
-- So the identity is a group isomorphism of the two word groups.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Symmetric.TopPad where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Function using (id)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)
open import Word.Base using (WRel ; [_]ʷ ; ε ; _•_)

import Circuit.TopPad
import Presentation.Base as PB

open import Examples.Groups.Symmetric.Syntactics

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- The rules on their own wires, padded by Top-Pad

infix 4 _Base,_===_
data _Base,_===_ : (n : ℕ) → WRel (Gen n) where
  order₀       : 2 Base, σ • σ === ε
  yang-baxter₀ : 3 Base, σ • σ ↑ • σ === σ ↑ • σ • σ ↑

open Circuit.TopPad Gate using (_↧ ; _⇓ ; ↑⇓)

module TP = Circuit.TopPad.Top-Pad Gate _Base,_===_

infix 4 _PRel,_===_
_PRel,_===_ : (n : ℕ) → WRel (Gen n)
_PRel,_===_ = TP._VRel,_===_

-- Each rule on the bottom wires of every wider circuit: a closed word
-- one wire wider is the same word (σ ⇓ is σ).
order↓ : (₂₊ n) PRel, σ • σ === ε
order↓ {0}    = TP.srel order₀
order↓ {₁₊ n} = TP.cong↓ order↓

yang-baxter↓ : (₃₊ n) PRel, σ • σ ↑ • σ === σ ↑ • σ • σ ↑
yang-baxter↓ {0}    = TP.srel yang-baxter₀
yang-baxter↓ {₁₊ n} = TP.cong↓ yang-baxter↓

grouplikeᵖ : Grouplike (_PRel,_===_ n)
grouplikeᵖ {₂₊ k} (gate₂ σ-gate) = σ , PB.axiom order↓
grouplikeᵖ {₁₊ n} (g ↥) with grouplikeᵖ {n} g
... | ig , prf = ig ↑ , TP.lemma-cong↑ (ig • [ g ]ʷ) ε prf

------------------------------------------------------------------------
-- Lift-Relation's rules hold with an idle wire on top

lr-⇓ : n VRel, w === v → (₁₊ n) VRel, w ⇓ === v ⇓
lr-⇓ (srel order)       = srel order
lr-⇓ (srel yang-baxter) = srel yang-baxter
lr-⇓ {₁₊ n} (cong↑ {w = w} {v} r) =
  Eq.subst₂ ((₂₊ n) VRel,_===_) (Eq.sym (↑⇓ w)) (Eq.sym (↑⇓ v))
            (cong↑ (lr-⇓ r))
lr-⇓ (comm₁ () g)
lr-⇓ (comm₂ σ-gate g)   = comm₂ σ-gate (g ↧)
lr-⇓ (ω↑=ω ())

lr-⇓* : PB._≈_ (n VRel,_===_) w v → PB._≈_ ((₁₊ n) VRel,_===_) (w ⇓) (v ⇓)
lr-⇓* PB.refl          = PB.refl
lr-⇓* (PB.sym e)       = PB.sym (lr-⇓* e)
lr-⇓* (PB.trans e f)   = PB.trans (lr-⇓* e) (lr-⇓* f)
lr-⇓* (PB.cong e f)    = PB.cong (lr-⇓* e) (lr-⇓* f)
lr-⇓* PB.assoc         = PB.assoc
lr-⇓* PB.left-unit     = PB.left-unit
lr-⇓* PB.right-unit    = PB.right-unit
lr-⇓* (PB.axiom x)     = PB.axiom (lr-⇓ x)

------------------------------------------------------------------------
-- Each relation's rules, in the other's congruence

lr⇒tp-ax : n VRel, w === v → PB._≈_ (n PRel,_===_) w v
lr⇒tp-ax (srel order)       = PB.axiom order↓
lr⇒tp-ax (srel yang-baxter) = PB.axiom yang-baxter↓
lr⇒tp-ax (cong↑ r)          = TP.lemma-cong↑ _ _ (lr⇒tp-ax r)
lr⇒tp-ax (comm₁ () g)
lr⇒tp-ax (comm₂ σ-gate g)   = PB.axiom (TP.comm₂ σ-gate g)
lr⇒tp-ax (ω↑=ω ())

tp⇒lr-ax : n PRel, w === v → PB._≈_ (n VRel,_===_) w v
tp⇒lr-ax (TP.srel order₀)       = PB.axiom (srel order)
tp⇒lr-ax (TP.srel yang-baxter₀) = PB.axiom (srel yang-baxter)
tp⇒lr-ax (TP.cong↓ r)           = lr-⇓* (tp⇒lr-ax r)
tp⇒lr-ax (TP.cong↑ r)           = lemma-cong↑ _ _ (tp⇒lr-ax r)
tp⇒lr-ax (TP.comm₁ () g)
tp⇒lr-ax (TP.comm₂ σ-gate g)    = PB.axiom (comm₂ σ-gate g)
tp⇒lr-ax (TP.ω↑=ω ())

------------------------------------------------------------------------
-- So the congruences coincide, and the identity is a group isomorphism

module _ (n : ℕ) where

  open import Presentation.MorphismId (n VRel,_===_) (n PRel,_===_)
    using (module Star-Congruence ; module GroupMorphs)

  lr⇒tp : ∀ {w v} → PB._≈_ (n VRel,_===_) w v → PB._≈_ (n PRel,_===_) w v
  lr⇒tp = Star-Congruence.lemma-id*-cong lr⇒tp-ax

  module W  = Group-Lemmas (n VRel,_===_) (grouplike {n})
  module Wᵖ = Group-Lemmas (n PRel,_===_) (grouplikeᵖ {n})

  open GroupMorphs (grouplike {n}) (grouplikeᵖ {n})

  lr≅tp : GroupMorphisms.IsGroupIsomorphism
            (Group.rawGroup W.•-ε-group) (Group.rawGroup Wᵖ.•-ε-group) id
  lr≅tp = StarGroupIsomorphism.isGroupIsomorphism lr⇒tp-ax tp⇒lr-ax

module _ (n : ℕ) where

  open import Presentation.MorphismId (n PRel,_===_) (n VRel,_===_)
    using (module Star-Congruence)

  tp⇒lr : ∀ {w v} → PB._≈_ (n PRel,_===_) w v → PB._≈_ (n VRel,_===_) w v
  tp⇒lr = Star-Congruence.lemma-id*-cong tp⇒lr-ax

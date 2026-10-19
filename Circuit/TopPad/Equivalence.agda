------------------------------------------------------------------------
-- Presentations of groups
--
-- A relation stated at every width and lifted by Lift-Relation, and the
-- same rules stated on their own wires and padded by Top-Pad, generate
-- the same congruence
--
-- The two have the same rules when three things hold, rule by rule
-- (SameRules):
--
--   * pad    — a rule at a width holds in Top-Pad's congruence: it is
--              the rule on its own wires with idle wires on top;
--   * unpad  — a rule on its own wires holds in Lift-Relation's;
--   * srel-⇓ — a rule at a width holds one wire wider with the new top
--              wire idle, in Lift-Relation's congruence (for a rule
--              between closed words, the same rule one wire wider).
--
-- Everything else is the structural rules, the same on both sides, and
-- one fact about them: Lift-Relation's congruence is closed under ⇓
-- (lr-⇓*), cong↑ commuting with the new wire (↑⇓) and every comm rule
-- and ω↑=ω, ⇓'d, being the same rule one wire wider.  So the identity
-- on circuits carries each congruence into the other (lr⇒tp, tp⇒lr),
-- and, the lifted relation being grouplike, is an isomorphism of the
-- two word groups (Iso.lr≅tp).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Circuit.TopPad.Equivalence (Gate : ℕ → Set) where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Product using (_,_)
open import Function using (id)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)
open import Word.Base

open import Circuit.Base Gate
open import Circuit.TopPad Gate using (_↧ ; _⇓ ; ↑⇓ ; module Top-Pad)

import Presentation.Base as PB

module Lift≅Top-Pad
  -- The rules at every width, lifted ...
  (_SRel,_===_ : (n : ℕ) → CRel n)
  -- ... and on their own wires, padded.
  (_Base,_===_ : (n : ℕ) → CRel n)
  where

  private
    module L = Lift-Relation _SRel,_===_
    module T = Top-Pad _Base,_===_

    variable
      n : ℕ
      w v : Circuit n

  infix 4 _LRel,_===_ _TRel,_===_ _⊢ᴸ_≈_ _⊢ᵀ_≈_

  _LRel,_===_ _TRel,_===_ : (n : ℕ) → CRel n
  _LRel,_===_ = L._VRel,_===_
  _TRel,_===_ = T._VRel,_===_

  -- The two congruences.
  _⊢ᴸ_≈_ _⊢ᵀ_≈_ : (n : ℕ) → Circuit n → Circuit n → Set
  n ⊢ᴸ w ≈ v = PB._≈_ (n LRel,_===_) w v
  n ⊢ᵀ w ≈ v = PB._≈_ (n TRel,_===_) w v

  -- For a rule whose words do not compute under ⇓ (a power with an
  -- exponent that is not a numeral), the padded rule and the rule ⇓'d
  -- go through equations between words, which Circuit.TopPad.Closed's
  -- ⇓-same proves.
  cong↓≡ : {w v : Circuit n} {w′ v′ : Circuit (₁₊ n)} →
           w ⇓ ≡ w′ → v ⇓ ≡ v′ → n TRel, w === v → (₁₊ n) TRel, w′ === v′
  cong↓≡ Eq.refl Eq.refl r = T.cong↓ r

  axiom≡ : {x y w′ v′ : Circuit n} →
           x ≡ w′ → y ≡ v′ → n LRel, w′ === v′ → n ⊢ᴸ x ≈ y
  axiom≡ Eq.refl Eq.refl r = PB.axiom r

  record SameRules : Set where
    field
      pad    : ∀ {n} {w v : Circuit n} → n SRel, w === v → n ⊢ᵀ w ≈ v
      unpad  : ∀ {n} {w v : Circuit n} → n Base, w === v → n ⊢ᴸ w ≈ v
      srel-⇓ : ∀ {n} {w v : Circuit n} → n SRel, w === v → (₁₊ n) ⊢ᴸ w ⇓ ≈ v ⇓

  module Equivalent (same : SameRules) where

    open SameRules same

    ----------------------------------------------------------------------
    -- Lift-Relation's congruence holds with an idle wire on top

    lr-⇓ : n LRel, w === v → (₁₊ n) ⊢ᴸ w ⇓ ≈ v ⇓
    lr-⇓ (L.srel s)    = srel-⇓ s
    lr-⇓ {₁₊ n} (L.cong↑ {w = w} {v} r) =
      Eq.subst₂ (λ a b → (₂₊ n) ⊢ᴸ a ≈ b) (Eq.sym (↑⇓ w)) (Eq.sym (↑⇓ v))
                (L.lemma-cong↑ _ _ (lr-⇓ r))
    lr-⇓ (L.comm₁ h g) = PB.axiom (L.comm₁ h (g ↧))
    lr-⇓ (L.comm₂ h g) = PB.axiom (L.comm₂ h (g ↧))
    lr-⇓ (L.comm₃ h g) = PB.axiom (L.comm₃ h (g ↧))
    lr-⇓ (L.ω↑=ω h)    = PB.axiom (L.ω↑=ω h)

    lr-⇓* : n ⊢ᴸ w ≈ v → (₁₊ n) ⊢ᴸ w ⇓ ≈ v ⇓
    lr-⇓* PB.refl        = PB.refl
    lr-⇓* (PB.sym e)     = PB.sym (lr-⇓* e)
    lr-⇓* (PB.trans e f) = PB.trans (lr-⇓* e) (lr-⇓* f)
    lr-⇓* (PB.cong e f)  = PB.cong (lr-⇓* e) (lr-⇓* f)
    lr-⇓* PB.assoc       = PB.assoc
    lr-⇓* PB.left-unit   = PB.left-unit
    lr-⇓* PB.right-unit  = PB.right-unit
    lr-⇓* (PB.axiom x)   = lr-⇓ x

    ----------------------------------------------------------------------
    -- Each relation's rules, in the other's congruence

    lr⇒tp-ax : n LRel, w === v → n ⊢ᵀ w ≈ v
    lr⇒tp-ax (L.srel s)    = pad s
    lr⇒tp-ax (L.cong↑ r)   = T.lemma-cong↑ _ _ (lr⇒tp-ax r)
    lr⇒tp-ax (L.comm₁ h g) = PB.axiom (T.comm₁ h g)
    lr⇒tp-ax (L.comm₂ h g) = PB.axiom (T.comm₂ h g)
    lr⇒tp-ax (L.comm₃ h g) = PB.axiom (T.comm₃ h g)
    lr⇒tp-ax (L.ω↑=ω h)    = PB.axiom (T.ω↑=ω h)

    tp⇒lr-ax : n TRel, w === v → n ⊢ᴸ w ≈ v
    tp⇒lr-ax (T.srel b)    = unpad b
    tp⇒lr-ax (T.cong↓ r)   = lr-⇓* (tp⇒lr-ax r)
    tp⇒lr-ax (T.cong↑ r)   = L.lemma-cong↑ _ _ (tp⇒lr-ax r)
    tp⇒lr-ax (T.comm₁ h g) = PB.axiom (L.comm₁ h g)
    tp⇒lr-ax (T.comm₂ h g) = PB.axiom (L.comm₂ h g)
    tp⇒lr-ax (T.comm₃ h g) = PB.axiom (L.comm₃ h g)
    tp⇒lr-ax (T.ω↑=ω h)    = PB.axiom (L.ω↑=ω h)

    ----------------------------------------------------------------------
    -- So the congruences coincide

    lr⇒tp : n ⊢ᴸ w ≈ v → n ⊢ᵀ w ≈ v
    lr⇒tp PB.refl        = PB.refl
    lr⇒tp (PB.sym e)     = PB.sym (lr⇒tp e)
    lr⇒tp (PB.trans e f) = PB.trans (lr⇒tp e) (lr⇒tp f)
    lr⇒tp (PB.cong e f)  = PB.cong (lr⇒tp e) (lr⇒tp f)
    lr⇒tp PB.assoc       = PB.assoc
    lr⇒tp PB.left-unit   = PB.left-unit
    lr⇒tp PB.right-unit  = PB.right-unit
    lr⇒tp (PB.axiom x)   = lr⇒tp-ax x

    tp⇒lr : n ⊢ᵀ w ≈ v → n ⊢ᴸ w ≈ v
    tp⇒lr PB.refl        = PB.refl
    tp⇒lr (PB.sym e)     = PB.sym (tp⇒lr e)
    tp⇒lr (PB.trans e f) = PB.trans (tp⇒lr e) (tp⇒lr f)
    tp⇒lr (PB.cong e f)  = PB.cong (tp⇒lr e) (tp⇒lr f)
    tp⇒lr PB.assoc       = PB.assoc
    tp⇒lr PB.left-unit   = PB.left-unit
    tp⇒lr PB.right-unit  = PB.right-unit
    tp⇒lr (PB.axiom x)   = tp⇒lr-ax x

    ----------------------------------------------------------------------
    -- ... and the identity is a group isomorphism

    module Iso (gl : ∀ {n} → Grouplike (n LRel,_===_)) where

      -- Top-Pad's relation is grouplike with the same inverses.
      glᵀ : Grouplike (n TRel,_===_)
      glᵀ x with gl x
      ... | ix , e = ix , lr⇒tp e

      module _ (n : ℕ) where

        open import Presentation.MorphismId (n LRel,_===_) (n TRel,_===_)
          using (module GroupMorphs)

        module Wᴸ = Group-Lemmas (n LRel,_===_) (gl {n})
        module Wᵀ = Group-Lemmas (n TRel,_===_) (glᵀ {n})

        open GroupMorphs (gl {n}) (glᵀ {n})

        lr≅tp : GroupMorphisms.IsGroupIsomorphism
                  (Group.rawGroup Wᴸ.•-ε-group) (Group.rawGroup Wᵀ.•-ε-group) id
        lr≅tp = StarGroupIsomorphism.isGroupIsomorphism lr⇒tp-ax tp⇒lr-ax

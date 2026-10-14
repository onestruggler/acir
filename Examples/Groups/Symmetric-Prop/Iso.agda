------------------------------------------------------------------------
-- Presentations of groups
--
-- The PROP and the PRO presentations of Sₙ have the same congruence
--
-- The circuits are the same words (Symmetric-Prop reuses Symmetric's
-- gates), so the identity is the isomorphism: each relation's rules
-- hold in the other's congruence.  From the PROP to the PRO, σ-inv is
-- order and σ-nat₂ at the swap is yang-baxter re-bracketed; there is
-- no gate on one or three wires, so σ-nat₁ and σ-nat₃ have no
-- instance.  Back, order and yang-baxter are Circuit.Prop's σ-invol
-- and yang-baxter, and an idle wire on top (cong↓) is closure of the
-- PROP's congruence under ⇓.  The other structural rules are the same
-- on both sides.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Symmetric-Prop.Iso where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Nat using (ℕ)
open import Notations using (₁₊ ; ₂₊)
open import Function using (id)
open import Presentation.GroupLike using (module Group-Lemmas)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

import Presentation.Base as PB

import Examples.Groups.Symmetric.Syntactics as PRO
open PRO using (_↧ ; _⇓ ; ↑⇓)
open import Examples.Groups.Symmetric-Prop.Syntactics

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- Each relation's rules, in the other's congruence

prop⇒pro-ax : n VRel, w === v → PB._≈_ (n PRO.VRel,_===_) w v
prop⇒pro-ax (srel (σrel σ-inv))              = PB.axiom PRO.order↓
prop⇒pro-ax (srel (σrel (σ-nat₁ ())))
prop⇒pro-ax (srel (σrel (σ-nat₂ σ-gate)))    =
  PB.trans (PB.axiom PRO.yang-baxter↓) (PB.sym PB.assoc)
prop⇒pro-ax (srel (σrel (σ-nat₃ ())))
prop⇒pro-ax (srel (srel ()))
prop⇒pro-ax (cong↑ r)                       = PRO.lemma-cong↑ _ _ (prop⇒pro-ax r)
prop⇒pro-ax (comm₁ () g)
prop⇒pro-ax (comm₂ σ-gate g)                = PB.axiom (PRO.comm₂ σ-gate g)
prop⇒pro-ax (comm₃ () g)
prop⇒pro-ax (ω↑=ω ())

-- The PROP's congruence holds with an idle wire on top, rule by rule:
-- a swap rule's words are closed, so ⇓'d it is the same rule one wire
-- wider, and cong↑ commutes with the new wire (↑⇓).
prop-⇓ : n VRel, w === v → (₁₊ n) ⊢ w ⇓ ≈ v ⇓
prop-⇓ (srel (σrel σ-inv))           = PB.axiom (srel (σrel σ-inv))
prop-⇓ (srel (σrel (σ-nat₁ ())))
prop-⇓ (srel (σrel (σ-nat₂ σ-gate))) = PB.axiom (srel (σrel (σ-nat₂ σ-gate)))
prop-⇓ (srel (σrel (σ-nat₃ ())))
prop-⇓ (srel (srel ()))
prop-⇓ {₁₊ n} (cong↑ {w = w} {v} r) =
  Eq.subst₂ (λ a b → (₂₊ n) ⊢ a ≈ b) (Eq.sym (↑⇓ w)) (Eq.sym (↑⇓ v))
            (lemma-cong↑ _ _ (prop-⇓ r))
prop-⇓ (comm₁ () g)
prop-⇓ (comm₂ σ-gate g)              = PB.axiom (comm₂ σ-gate (g ↧))
prop-⇓ (comm₃ () g)
prop-⇓ (ω↑=ω ())

⇓-cong : n ⊢ w ≈ v → (₁₊ n) ⊢ w ⇓ ≈ v ⇓
⇓-cong PB.refl          = PB.refl
⇓-cong (PB.sym e)       = PB.sym (⇓-cong e)
⇓-cong (PB.trans e f)   = PB.trans (⇓-cong e) (⇓-cong f)
⇓-cong (PB.cong e f)    = PB.cong (⇓-cong e) (⇓-cong f)
⇓-cong PB.assoc         = PB.assoc
⇓-cong PB.left-unit     = PB.left-unit
⇓-cong PB.right-unit    = PB.right-unit
⇓-cong (PB.axiom x)     = prop-⇓ x

pro⇒prop-ax : n PRO.VRel, w === v → n ⊢ w ≈ v
pro⇒prop-ax (PRO.srel PRO.order)       = order
pro⇒prop-ax (PRO.srel PRO.yang-baxter) = yang-baxter
pro⇒prop-ax (PRO.cong↓ r)              = ⇓-cong (pro⇒prop-ax r)
pro⇒prop-ax (PRO.cong↑ r)              = lemma-cong↑ _ _ (pro⇒prop-ax r)
pro⇒prop-ax (PRO.comm₁ () g)
pro⇒prop-ax (PRO.comm₂ σ-gate g)       = PB.axiom (comm₂ σ-gate g)
pro⇒prop-ax (PRO.ω↑=ω ())

------------------------------------------------------------------------
-- So the congruences coincide, and the identity is a group isomorphism

module _ (n : ℕ) where

  open import Presentation.MorphismId (n VRel,_===_) (n PRO.VRel,_===_)
    using (module Star-Congruence ; module GroupMorphs)

  prop⇒pro : ∀ {w v} → n ⊢ w ≈ v → PB._≈_ (n PRO.VRel,_===_) w v
  prop⇒pro = Star-Congruence.lemma-id*-cong prop⇒pro-ax

  module W = Group-Lemmas (n VRel,_===_) (grouplike {n})
  module Wᴾ = Group-Lemmas (n PRO.VRel,_===_) (PRO.grouplike {n})

  open GroupMorphs (grouplike {n}) (PRO.grouplike {n})

  prop≅pro : GroupMorphisms.IsGroupIsomorphism
               (Group.rawGroup W.•-ε-group) (Group.rawGroup Wᴾ.•-ε-group) id
  prop≅pro = StarGroupIsomorphism.isGroupIsomorphism prop⇒pro-ax pro⇒prop-ax

module _ (n : ℕ) where

  open import Presentation.MorphismId (n PRO.VRel,_===_) (n VRel,_===_)
    using (module Star-Congruence)

  pro⇒prop : ∀ {w v} → PB._≈_ (n PRO.VRel,_===_) w v → n ⊢ w ≈ v
  pro⇒prop = Star-Congruence.lemma-id*-cong pro⇒prop-ax

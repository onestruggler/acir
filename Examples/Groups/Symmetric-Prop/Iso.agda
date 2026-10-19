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
-- and yang-baxter.  The structural rules are the same on both sides.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Symmetric-Prop.Iso where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Nat using (ℕ)
open import Function using (id)
open import Presentation.GroupLike using (module Group-Lemmas)

import Presentation.Base as PB

import Examples.Groups.Symmetric.Syntactics as PRO
open import Examples.Groups.Symmetric-Prop.Syntactics

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- Each relation's rules, in the other's congruence

prop⇒pro-ax : n VRel, w === v → PB._≈_ (n PRO.VRel,_===_) w v
prop⇒pro-ax (srel (σrel σ-inv))              = PB.axiom (PRO.srel PRO.order)
prop⇒pro-ax (srel (σrel (σ-nat₁ ())))
prop⇒pro-ax (srel (σrel (σ-nat₂ σ-gate)))    =
  PB.trans (PB.axiom (PRO.srel PRO.yang-baxter)) (PB.sym PB.assoc)
prop⇒pro-ax (srel (σrel (σ-nat₃ ())))
prop⇒pro-ax (srel (srel ()))
prop⇒pro-ax (cong↑ r)                       = PRO.lemma-cong↑ _ _ (prop⇒pro-ax r)
prop⇒pro-ax (comm₁ () g)
prop⇒pro-ax (comm₂ σ-gate g)                = PB.axiom (PRO.comm₂ σ-gate g)
prop⇒pro-ax (comm₃ () g)
prop⇒pro-ax (ω↑=ω ())

pro⇒prop-ax : n PRO.VRel, w === v → n ⊢ w ≈ v
pro⇒prop-ax (PRO.srel PRO.order)       = order
pro⇒prop-ax (PRO.srel PRO.yang-baxter) = yang-baxter
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

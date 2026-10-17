------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness of the rules on every number of wires
--
-- The five-wire rules are sound (Five.Soundness), and the control
-- schema is because controlled versions of sound equations are sound
-- (Lambda.Semantics.λ¹ᵏ-~).  The congruence is closed as in
-- Five.Soundness, through the monoid reading of StarInterp, here over
-- the relation with the schema.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.Soundness where

open import Data.Nat using (ℕ ; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Examples.Groups.Clifford+CS.Semantics using (Scaled-monoid ; _~_ ; _∙_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation
  using (⟦_⟧ ; ⟦_⟧ᵍ ; module Ext ; ⟦⟧ᴱ-def)
open import Examples.Groups.Clifford+CS.Soundness
  using (cong↑-sound ; comm₁-sound ; comm₂-sound ; ω↑=ω-sound)
open import Examples.Groups.Clifford+CS.Five.Rules using (srelₓ)
open import Examples.Groups.Clifford+CS.Five.Soundness using (axiom-soundₓ)
open import Examples.Groups.Clifford+CS.Lambda.Semantics using (λ¹ᵏ-~)
open import Examples.Groups.Clifford+CS.Stable.Rules

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- The axioms

axiom-soundᵧ : n YVRel, w === v → ⟦ w ⟧ ~ ⟦ v ⟧
axiom-soundᵧ (srelᵧ (five a))         = axiom-soundₓ (srelₓ a)
axiom-soundᵧ (srelᵧ (ctl k {w} {v} p)) = λ¹ᵏ-~ (suc k) {w} {v} (axiom-soundₓ (srelₓ (wide-rule p)))
axiom-soundᵧ (cong↑ᵧ r)               = cong↑-sound (axiom-soundᵧ r)
axiom-soundᵧ (comm₁ᵧ h g)             = comm₁-sound h g
axiom-soundᵧ (comm₂ᵧ h g)             = comm₂-sound h g
axiom-soundᵧ (ω↑=ωᵧ h)                = ω↑=ω-sound h

------------------------------------------------------------------------
-- The congruence

private
  module YE (n : ℕ) where
    open import Normalization.StarInterp (_YVRel,_===_ n)
    open Extend (Scaled-monoid n) (λ g → 1 , ⟦ g ⟧ᵍ) public renaming (⟦_⟧ to ⟦_⟧ʸ)

  -- The reading over this relation is the one over the old.
  same-ext : (w : Circuit n) → YE.⟦_⟧ʸ n w ≡ Ext.⟦_⟧ᴱ n w
  same-ext [ g ]ʷ  = Eq.refl
  same-ext ε       = Eq.refl
  same-ext (w • v) = Eq.cong₂ _∙_ (same-ext w) (same-ext v)

  def : (w : Circuit n) → YE.⟦_⟧ʸ n w ≡ ⟦ w ⟧
  def w = Eq.trans (same-ext w) (⟦⟧ᴱ-def w)

  axiom-soundʸ : n YVRel, w === v → YE.⟦_⟧ʸ n w ~ YE.⟦_⟧ʸ n v
  axiom-soundʸ {w = w} {v} a = Eq.subst₂ _~_ (Eq.sym (def w)) (Eq.sym (def v)) (axiom-soundᵧ a)

soundᵧ : n ⊢ᵧ w ≈ v → ⟦ w ⟧ ~ ⟦ v ⟧
soundᵧ {n} {w} {v} e =
  Eq.subst₂ _~_ (def w) (def v) (YE.Cong.fʷ-cong n axiom-soundʸ e)

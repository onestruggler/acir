------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness of the rules on five wires and more
--
-- The rules of Syntactics are sound (Soundness); so is AX, one
-- evaluation at five wires carried to every width by
-- Interpretation.by-relator.  The congruence is closed as in
-- Soundness, through the monoid reading of StarInterp, here over the
-- extended relation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Soundness where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Examples.Groups.Clifford+CS.Semantics using (Scaled ; Scaled-monoid ; _~_ ; _∙_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation
  using (⟦_⟧ ; ⟦_⟧ᵍ ; by-relator ; module Ext ; ⟦⟧ᴱ-def)
open import Examples.Groups.Clifford+CS.Soundness
  using (axiom-sound ; cong↑-sound ; comm₁-sound ; comm₂-sound ; ω↑=ω-sound)
open import Examples.Groups.Clifford+CS.Soundness.Relators using (Same ; same-≡)
open import Examples.Groups.Clifford+CS.Five.Rules

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- The axioms

-- AX on five wires, by one evaluation.
mAX : Same (AX.l {0}) (AX.r {0})
mAX = Eq.refl

axiom-soundₓ : n XVRel, w === v → ⟦ w ⟧ ~ ⟦ v ⟧
axiom-soundₓ (srelₓ (old a))  = axiom-sound (srel a)
axiom-soundₓ (srelₓ ax)       =
  by-relator (AX.l {0}) (AX.r {0}) Eq.refl Eq.refl (same-≡ (AX.l {0}) (AX.r {0}) mAX)
axiom-soundₓ (cong↑ₓ r)       = cong↑-sound (axiom-soundₓ r)
axiom-soundₓ (comm₁ₓ h g)     = comm₁-sound h g
axiom-soundₓ (comm₂ₓ h g)     = comm₂-sound h g
axiom-soundₓ (ω↑=ωₓ h)        = ω↑=ω-sound h

------------------------------------------------------------------------
-- The congruence

private
  module XE (n : ℕ) where
    open import Normalization.StarInterp (_XVRel,_===_ n)
    open Extend (Scaled-monoid n) (λ g → 1 , ⟦ g ⟧ᵍ) public renaming (⟦_⟧ to ⟦_⟧ˣ)

  -- The reading over the extended relation is the one over the old.
  same-ext : (w : Circuit n) → XE.⟦_⟧ˣ n w ≡ Ext.⟦_⟧ᴱ n w
  same-ext [ g ]ʷ  = Eq.refl
  same-ext ε       = Eq.refl
  same-ext (w • v) = Eq.cong₂ _∙_ (same-ext w) (same-ext v)

  def : (w : Circuit n) → XE.⟦_⟧ˣ n w ≡ ⟦ w ⟧
  def w = Eq.trans (same-ext w) (⟦⟧ᴱ-def w)

  axiom-soundˣ : n XVRel, w === v → XE.⟦_⟧ˣ n w ~ XE.⟦_⟧ˣ n v
  axiom-soundˣ {w = w} {v} a = Eq.subst₂ _~_ (Eq.sym (def w)) (Eq.sym (def v)) (axiom-soundₓ a)

soundₓ : n ⊢ₓ w ≈ v → ⟦ w ⟧ ~ ⟦ v ⟧
soundₓ {n} {w} {v} e =
  Eq.subst₂ _~_ (def w) (def v) (XE.Cong.fʷ-cong n axiom-soundˣ e)

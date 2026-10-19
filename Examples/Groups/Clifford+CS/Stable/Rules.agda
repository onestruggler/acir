------------------------------------------------------------------------
-- Presentations of groups
--
-- The rules on every number of wires: the five-wire rules and their
-- control schema
--
-- The rules of Five.Rules (Syntactics' rules, AX and the controlled
-- four-wire rules) are complete on five wires (Five.Main).  From six on
-- the joint paper's stability theorem (scratchpad/joint/
-- stability-notes.md, Theorem S) asks that the controlled versions of
-- the widest equations be derivable, and those of the five-wire rules
-- are not expected to be (AX's has the parity invariant of the
-- conjecture there against it).  So the rule set for every width adds
-- the control schema: each five-wire rule (`Wide`) under k + 1 further
-- controls on the top wires (Lambda.λ¹ᵏ, the controlled functor at every
-- width),
-- so that the controlled version of an instance of a five-wire rule, or
-- of the schema, is again an instance.  AX keeps its idle wires above
-- it, under the controls.
--
-- They are kept in a relation of their own, the rules of Five.Rules
-- included through `five`, so that nothing built on Five.Rules changes
-- (as Five.Rules includes Syntactics through `old`); `embed₅` carries a
-- derivation of the five-wire theory to this one.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.Rules where

open import Data.Nat using (ℕ ; suc) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (Word ; WRel ; ε)
open import Notations using (₄₊)

import Circuit.Base
import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Five.Rules as F
  using ( _XRel,_===_ ; _XVRel,_===_ ; _⊢ₓ_≈_ ; srelₓ ; cong↑ₓ ; comm₁ₓ ; comm₂ₓ ; ω↑=ωₓ
        ; module AX )
open import Examples.Groups.Clifford+CS.Five.Lambda using (λc)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ᵏ)

private
  variable
    n : ℕ
    w v : Word (Gen n)

private module SC = Circuit.Base Gate

------------------------------------------------------------------------
-- The relation

-- The five-wire rules the schema is over, as a family of pairs of words:
-- AX (with its idle wires above it) and the controlled four-wire rules.
data Wide : (n : ℕ) → Circuit n → Circuit n → Set where
  w-ax     : Wide (suc (₄₊ n)) AX.l AX.r
  w-lf     : Wide 5 (λc LF.Hyb) (λc LF.Dec)
  w-hyb-sq : Wide 5 (λc HSQ.Sq) (λc ε)
  w-hyb-yb : Wide 5 (λc HYB.Yl) (λc HYB.Yr)

-- Each is a rule of Five.Rules.
wide-rule : ∀ {w v : Circuit n} → Wide n w v → n XRel, w === v
wide-rule w-ax     = F.ax
wide-rule w-lf     = F.λ-lf
wide-rule w-hyb-sq = F.λ-hyb-sq
wide-rule w-hyb-yb = F.λ-hyb-yb

infix 4 _YRel,_===_
data _YRel,_===_ : (n : ℕ) → WRel (Gen n) where

  -- The rules of Five.Rules.
  five : n XRel, w === v → n YRel, w === v

  -- The control schema: a five-wire rule under k + 1 more controls.
  -- Stated over the family Wide, not word by word, so that no statement
  -- about the schema mentions the words themselves: a conversion that is
  -- not syntactic would evaluate the λ-images of thousand-gate words.
  ctl : ∀ k {w v : Circuit (₄₊ n)} → Wide (₄₊ n) w v →
        (₄₊ (suc k +ℕ n)) YRel, λ¹ᵏ (suc k) w === λ¹ᵏ (suc k) v

private module LY = SC.Lift-Relation _YRel,_===_

open LY public
  using ()
  renaming ( _VRel,_===_ to _YVRel,_===_ ; srel to srelᵧ ; cong↑ to cong↑ᵧ
           ; comm₁ to comm₁ᵧ ; comm₂ to comm₂ᵧ ; ω↑=ω to ω↑=ωᵧ
           ; lemma-cong↑ to lemma-cong↑ᵧ )

-- There is one scalar, so it is central.
open LY.Single-Scalar (λ { I-gate I-gate → Eq.refl }) public
  using () renaming (comm₀ to comm₀ᵧ ; comm-gate₀-w to comm-gate₀-wᵧ)

-- The congruence generated, at each width.
infix 4 _⊢ᵧ_≈_
_⊢ᵧ_≈_ : (n : ℕ) → Circuit n → Circuit n → Set
n ⊢ᵧ w ≈ v = PB._≈_ (_YVRel,_===_ n) w v

------------------------------------------------------------------------
-- The five-wire theory in this one

embed₅-ax : n XVRel, w === v → n YVRel, w === v
embed₅-ax (srelₓ a)    = LY.srel (five a)
embed₅-ax (cong↑ₓ a)   = LY.cong↑ (embed₅-ax a)
embed₅-ax (comm₁ₓ h g) = LY.comm₁ h g
embed₅-ax (comm₂ₓ h g) = LY.comm₂ h g
embed₅-ax (ω↑=ωₓ h)    = LY.ω↑=ω h

embed₅ : n ⊢ₓ w ≈ v → n ⊢ᵧ w ≈ v
embed₅ PB.refl          = PB.refl
embed₅ (PB.sym e)       = PB.sym (embed₅ e)
embed₅ (PB.trans e e₁)  = PB.trans (embed₅ e) (embed₅ e₁)
embed₅ (PB.cong e e₁)   = PB.cong (embed₅ e) (embed₅ e₁)
embed₅ PB.assoc         = PB.assoc
embed₅ PB.left-unit     = PB.left-unit
embed₅ PB.right-unit    = PB.right-unit
embed₅ (PB.axiom a)     = PB.axiom (embed₅-ax a)

-- And the old theory.  The implicits given: inferring them exhausted a
-- 3 GB heap.
embed : n ⊢ w ≈ v → n ⊢ᵧ w ≈ v
embed {n} {w} {v} e = embed₅ {n} {w} {v} (F.embed {n} {w} {v} e)

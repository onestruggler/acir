------------------------------------------------------------------------
-- Presentations of groups
--
-- Selecting Paper-V1's rules by name
--
-- Circuit.Independence.Structural removes a structural rule from a
-- lifted relation.  This module does the same for a gate-specific
-- one: it names the fifteen rules of Paper-V1 (the paper's Figure 1),
-- reads off the rule an axiom instance comes from, and selects the
-- instances that do not use a given rule.  An instance of the full
-- relation uses r when it is an instance of r or a shift of one, so
-- removing r removes all its shifts too, and the selection is closed
-- under cong↑ in both directions — which is all the soundness engine
-- of Circuit.Independence.Structural asks of a selection.
--
-- A rule r is then independent as soon as one of its instances is not
-- derivable from the instances that do not use r: from the other
-- fourteen rules, at every width and every shift, together with all
-- the structural rules.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.ProjectiveClifford.Qupit.Independence.Selection
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open import Data.Empty using (⊥)
open import Relation.Nullary.Negation using (¬_)

open import Word.Base using (Word)
import Presentation.Base as PB
open import Presentation.Independence
  using (Select ; _∣_ ; Derivable ; Independent)
import Circuit.Base
import Circuit.Independence

import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Syntactics
  p-3 p-prime g* g-gen as Pap
open Pap using (SympGate ; Gen ; _↑)
open Pap.Clifford-Relations
  using (module Base ; _QRel,_===_ ; srel ; cong↑ ; comm₁ ; comm₂)
open Base using (_SRel,_===_)
open Circuit.Base.Lift-Relation SympGate _SRel,_===_ using (ω↑=ω)

private
  variable
    n : ℕ
    w v : Word (Gen n)

------------------------------------------------------------------------
-- The rules, by name
--
-- The names are those of the constructors of Base._SRel,_===_; Agda
-- tells the two apart by type.  M-power is one name for its p
-- instances, one per exponent.

data Rule : Set where
  -- one wire
  order-S order-H M-power semi-MR comm-HHSHHS : Rule
  -- two wires
  order-CZ order-Ex comm-CZ-S↑ semi-M↑CZ : Rule
  semi-Ex-S↑ semi-Ex-H↑ blake-c12 : Rule
  -- three wires
  yang-baxter cz-slide semi-CX↑-CZ↓ : Rule

-- The rule a gate-specific axiom instance is an instance of.
rule : n SRel, w === v → Rule
rule Base.order-S      = order-S
rule Base.order-H      = order-H
rule (Base.M-power _)  = M-power
rule Base.semi-MR      = semi-MR
rule Base.comm-HHSHHS  = comm-HHSHHS
rule Base.order-CZ     = order-CZ
rule Base.order-Ex     = order-Ex
rule Base.comm-CZ-S↑   = comm-CZ-S↑
rule Base.semi-M↑CZ    = semi-M↑CZ
rule Base.semi-Ex-S↑   = semi-Ex-S↑
rule Base.semi-Ex-H↑   = semi-Ex-H↑
rule Base.blake-c12    = blake-c12
rule Base.yang-baxter  = yang-baxter
rule Base.cz-slide     = cz-slide
rule Base.semi-CX↑-CZ↓ = semi-CX↑-CZ↓

------------------------------------------------------------------------
-- Selecting the instances that do not use a rule

-- Uses r a: the axiom instance a is an instance of r, possibly
-- shifted.  The structural rules use no gate-specific rule, and the
-- qupit alphabet has no scalar, so ω↑=ω has no instances.
Uses : Rule → n QRel, w === v → Set
Uses r (srel s)    = rule s ≡ r
Uses r (cong↑ a)   = Uses r a
Uses r (comm₁ _ _) = ⊥
Uses r (comm₂ _ _) = ⊥
Uses r (ω↑=ω ())

-- The selection of every axiom instance not using r.
Without : Rule → Select (n QRel,_===_)
Without r a = ¬ Uses r a

-- A shift uses what its unshifted instance uses, so the selection is
-- closed under cong↑ both ways.  The first direction is what
-- Structural.Soundness asks for; the second makes what is derivable
-- without r at width n derivable without r one wire up.
Without-cong↑⁻ : ∀ r {a : n QRel, w === v} →
                 Without r (cong↑ a) → Without r a
Without-cong↑⁻ r ¬u = ¬u

Without-cong↑⁺ : ∀ r {a : n QRel, w === v} →
                 Without r a → Without r (cong↑ a)
Without-cong↑⁺ r ¬u = ¬u

-- Derivability of an instance from the instances not using r, and its
-- negation.
infix 4 _DerivableWithout_ _IndependentOf_

_DerivableWithout_ : n QRel, w === v → Rule → Set
a DerivableWithout r = Derivable (_ QRel,_===_) (Without r) a

_IndependentOf_ : n QRel, w === v → Rule → Set
a IndependentOf r = Independent (_ QRel,_===_) (Without r) a

------------------------------------------------------------------------
-- The soundness engine, at a gate-rule selection
--
-- Structural's engine takes any selection together with its closure
-- under unshifting; here that selection is Without r.  A model for
-- the independence of r is a monoid per width with a reading of the
-- generators, and owes soundness of every rule other than r.

private
  module Str = Circuit.Independence.Structural SympGate _SRel,_===_

module Soundness (r : Rule) =
  Str.Soundness (Without r) (λ {n} {w} {v} {a} → Without-cong↑⁻ r {a = a})

-- What is derivable without r at width n is derivable without r one
-- wire up.
lemma-cong↑-without : ∀ r {w v : Word (Gen n)} →
  let open PB ((n QRel,_===_) ∣ Without r) using (_≈_)
      open PB (((₁₊ n) QRel,_===_) ∣ Without r) using ()
        renaming (_≈_ to _≈↑_)
  in w ≈ v → w ↑ ≈↑ v ↑
lemma-cong↑-without r =
  Str.Lift.lemma-cong↑∣ (Without r)
    (λ {n} {w} {v} {a} → Without-cong↑⁺ r {a = a})

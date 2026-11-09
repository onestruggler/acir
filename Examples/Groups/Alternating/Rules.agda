------------------------------------------------------------------------
-- Presentations of groups
--
-- The rules of Lafont's Fig. 10, in a theory and as a theory.
--
-- Lemma 8 of the paper: any circuit reduces to a canonical form by the
-- rules of Fig. 10 (and the interchange law, which here is comm₃).
-- The seven rules are numbered in the figure's reading order: the rule
-- on top, then each row left to right.  Read as rewriting steps (left
-- to right), each moves a cycle down past one of Lafont's stairs:
--
--   rule₁  ω₁ ω₃           → ω₃ ω₃ ω₂ ω₃ ω₁   (used by Lemma 7)
--   rule₂  ω₁ ω₂ ω₃ ω₁     → ω₃ ω₁ ω₂ ω₃      (stairs of size ≥ 3)
--   rule₃  ω₁ ω₂ ω₁        → ω₂ ω₂            (stairs of size 2)
--   rule₄  ω₁ ω₁           → ω₂ ω₁ ω₂         (stairs of size 1)
--   rule₅  ω₁ ω₂ ω₃ ω₃ ω₁  → ω₂ ω₁ ω₂ ω₃ ω₃   (the last stairs, 5 wires)
--   rule₆  ω₁ ω₂ ω₂ ω₁     → ω₂ ω₂ ω₁ ω₂ ω₂   (the last stairs, 4 wires)
--   rule₇  ω₁ ω₁ ω₁        → id               (the last stairs, 3 wires)
--
-- in the paper's numbering, ω_i on the wires i, i + 1, i + 2 and the
-- words drawn top to bottom; here ω_i is ω ↑ applied i − 1 times.
-- Normalization proves Lemma 8 in any theory where the rules hold
-- (Fig10 T), Derivations derives them from Theorem 4's relations
-- (Lafont's Fig. 11), and the rules themselves are a theory,
-- _RRel,_===_, which presents 𝔄ₙ too (Presentation).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alternating.Rules where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Notations using (₁₊ ; ₃₊ ; ₄₊)
open import Presentation.GroupLike using (Grouplike)
open import Word.Base using (WRel ; [_]ʷ ; ε ; _•_)

import Presentation.Base as PB

open import Examples.Groups.Alternating.Syntactics
  using ( Gen ; ω ; ω-gen ; _↥ ; _↑ ; ₅₊ ; Theory ; _∣_⊢_≈_
        ; module Lift-Relation )

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The rules of Fig. 10 hold in a theory

record Fig10 (T : Theory) : Set where
  field
    rule₁ : ∀ {n} → T ∣ ₅₊ n ⊢ ω • ω ↑ ↑ ≈ ω ↑ ↑ • ω ↑ ↑ • ω ↑ • ω ↑ ↑ • ω
    rule₂ : ∀ {n} → T ∣ ₅₊ n ⊢ ω • ω ↑ • ω ↑ ↑ • ω ≈ ω ↑ ↑ • ω • ω ↑ • ω ↑ ↑
    rule₃ : ∀ {n} → T ∣ ₄₊ n ⊢ ω • ω ↑ • ω ≈ ω ↑ • ω ↑
    rule₄ : ∀ {n} → T ∣ ₄₊ n ⊢ ω • ω ≈ ω ↑ • ω • ω ↑
    rule₅ : ∀ {n} → T ∣ ₅₊ n ⊢ ω • ω ↑ • ω ↑ ↑ • ω ↑ ↑ • ω ≈
                                ω ↑ • ω • ω ↑ • ω ↑ ↑ • ω ↑ ↑
    rule₆ : ∀ {n} → T ∣ ₄₊ n ⊢ ω • ω ↑ • ω ↑ • ω ≈ ω ↑ • ω ↑ • ω • ω ↑ • ω ↑
    rule₇ : ∀ {n} → T ∣ ₃₊ n ⊢ ω • ω • ω ≈ ε


------------------------------------------------------------------------
-- A theory with the rules is grouplike

-- By rule₇, ω • ω is an inverse of ω; a shifted generator has the
-- shifted inverse.
module _ {T : Theory} (rules : Fig10 T) where

  open Fig10 rules using (rule₇)
  open Lift-Relation T using (_VRel,_===_ ; lemma-cong↑)

  grouplike : Grouplike (n VRel,_===_)
  grouplike {₃₊ k} ω-gen = ω • ω , PB.trans PB.assoc rule₇
  grouplike {₁₊ k} (g ↥) with grouplike {k} g
  ... | ig , prf = ig ↑ , lemma-cong↑ (ig • [ g ]ʷ) ε prf

------------------------------------------------------------------------
-- The rules as a theory

infix 4 _RRel,_===_
data _RRel,_===_ : (n : ℕ) → WRel (Gen n) where
  rule₁ : (₅₊ n) RRel, ω • ω ↑ ↑ === ω ↑ ↑ • ω ↑ ↑ • ω ↑ • ω ↑ ↑ • ω
  rule₂ : (₅₊ n) RRel, ω • ω ↑ • ω ↑ ↑ • ω === ω ↑ ↑ • ω • ω ↑ • ω ↑ ↑
  rule₃ : (₄₊ n) RRel, ω • ω ↑ • ω === ω ↑ • ω ↑
  rule₄ : (₄₊ n) RRel, ω • ω === ω ↑ • ω • ω ↑
  rule₅ : (₅₊ n) RRel, ω • ω ↑ • ω ↑ ↑ • ω ↑ ↑ • ω ===
                       ω ↑ • ω • ω ↑ • ω ↑ ↑ • ω ↑ ↑
  rule₆ : (₄₊ n) RRel, ω • ω ↑ • ω ↑ • ω === ω ↑ • ω ↑ • ω • ω ↑ • ω ↑
  rule₇ : (₃₊ n) RRel, ω • ω • ω === ε

private module LRᴿ = Lift-Relation _RRel,_===_

-- The rules with the structural rules.
open LRᴿ public using () renaming (_VRel,_===_ to _RVRel,_===_)

-- In their own theory the rules hold by definition.
axioms : Fig10 _RRel,_===_
axioms = record
  { rule₁ = PB.axiom (LRᴿ.srel rule₁)
  ; rule₂ = PB.axiom (LRᴿ.srel rule₂)
  ; rule₃ = PB.axiom (LRᴿ.srel rule₃)
  ; rule₄ = PB.axiom (LRᴿ.srel rule₄)
  ; rule₅ = PB.axiom (LRᴿ.srel rule₅)
  ; rule₆ = PB.axiom (LRᴿ.srel rule₆)
  ; rule₇ = PB.axiom (LRᴿ.srel rule₇)
  }

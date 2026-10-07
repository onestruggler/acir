------------------------------------------------------------------------
-- Presentations of groups
--
-- Equational reasoning for CNOT-dihedral circuits
--
-- The congruence at a fixed width with its reasoning combinators and
-- the associativity solvers (module Width), the axioms as derivations
-- (ax), derivations moved up a wire (lift), and a few laws of
-- involutions used throughout: a gate equal to its own inverse can be
-- cancelled, and conjugating by it moves it across.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.Reasoning where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊)

import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Examples.Groups.CNOT+Dihedral.Syntactics

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- Axioms, and derivations one wire up

ax : n SRel, w === v → n ⊢ w ≈ v
ax r = PB.axiom (srel r)

-- A structural rule.
ax' : n VRel, w === v → n ⊢ w ≈ v
ax' = PB.axiom

lift : n ⊢ w ≈ v → (₁₊ n) ⊢ w ↑ ≈ v ↑
lift {w = w} {v} = lemma-cong↑ w v

------------------------------------------------------------------------
-- Reasoning at a fixed width

module Width (n : ℕ) where

  open PB (n VRel,_===_) public
    using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit ; refl')
  open PP (n VRel,_===_) public using (word-setoid ; by-assoc)
  open PP.Pattern-Assoc (n VRel,_===_) public using (by-passoc ; □)
  open SR word-setoid public

  -- Rewriting at the front, at the back, and in the middle.
  front : ∀ {a b} (s : Circuit n) → a ≈ b → a • s ≈ b • s
  front s e = cong e refl

  back : ∀ (p : Circuit n) {a b} → a ≈ b → p • a ≈ p • b
  back p e = cong refl e

  mid : ∀ (p : Circuit n) {a b} (s : Circuit n) → a ≈ b → p • a • s ≈ p • b • s
  mid p s e = cong refl (cong e refl)

  -- A word g slid across a product, each factor turning into another.
  slide : ∀ {g a a' b b'} → g • a ≈ a' • g → g • b ≈ b' • g →
          g • (a • b) ≈ (a' • b') • g
  slide {g} {a} {a'} {b} {b'} ea eb = begin
    g • (a • b)        ≈⟨ sym assoc ⟩
    (g • a) • b        ≈⟨ front b ea ⟩
    (a' • g) • b       ≈⟨ assoc ⟩
    a' • (g • b)       ≈⟨ back a' eb ⟩
    a' • (b' • g)      ≈⟨ sym assoc ⟩
    (a' • b') • g      ∎

  slide-ε : ∀ {g} → g • ε ≈ ε • g
  slide-ε = trans right-unit (sym left-unit)

  ----------------------------------------------------------------------
  -- Involutions

  module Involution {x : Circuit n} (xx : x • x ≈ ε) where

    -- x cancels against itself in front of a word, and behind one.
    cancelˡ : (u : Circuit n) → x • x • u ≈ u
    cancelˡ u = trans (sym assoc) (trans (front u xx) left-unit)

    cancelʳ : (u : Circuit n) → u • x • x ≈ u
    cancelʳ u = trans (back u xx) right-unit

    -- Conjugating by x moves it across.
    conj→ : ∀ {y z} → x • y • x ≈ z → x • y ≈ z • x
    conj→ {y} {z} e = begin
      x • y                ≈⟨ sym (cancelʳ (x • y)) ⟩
      (x • y) • x • x      ≈⟨ sym assoc ⟩
      ((x • y) • x) • x    ≈⟨ front x assoc ⟩
      (x • y • x) • x      ≈⟨ front x e ⟩
      z • x                ∎

    conj← : ∀ {y z} → x • y ≈ z • x → x • y • x ≈ z
    conj← {y} {z} e = begin
      x • y • x            ≈⟨ sym assoc ⟩
      (x • y) • x          ≈⟨ front x e ⟩
      (z • x) • x          ≈⟨ assoc ⟩
      z • x • x            ≈⟨ cancelʳ z ⟩
      z                    ∎

    -- And moves the other way.
    conj→' : ∀ {y z} → x • y • x ≈ z → y • x ≈ x • z
    conj→' {y} {z} e = begin
      y • x                ≈⟨ sym (cancelˡ (y • x)) ⟩
      x • x • y • x        ≈⟨ back x e ⟩
      x • z                ∎

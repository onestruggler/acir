------------------------------------------------------------------------
-- Presentations of groups
--
-- Equational reasoning for phase-affine circuits
--
-- The congruence at a fixed width with its reasoning combinators and
-- the associativity tactics (Width), rewriting at the front, back and
-- middle of a product, and the cancellation of an involution.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Reasoning
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) where

open import Word.Base using (ε ; _•_)

open import Notations using (₁₊)

import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- Rules, and derivations one wire up

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

  back : ∀ (q : Circuit n) {a b} → a ≈ b → q • a ≈ q • b
  back q e = cong refl e

  mid : ∀ (q : Circuit n) {a b} (s : Circuit n) → a ≈ b → q • a • s ≈ q • b • s
  mid q s e = cong refl (cong e refl)

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

  -- Cancelling a pair u • v ≈ ε in context.
  cancel-in : ∀ {u v} → u • v ≈ ε → (s : Circuit n) → u • v • s ≈ s
  cancel-in e s = trans (sym assoc) (trans (front s e) left-unit)

  cancel-at : ∀ {u v} → u • v ≈ ε → (s : Circuit n) → s • u • v ≈ s
  cancel-at e s = trans (back s e) right-unit

  ----------------------------------------------------------------------
  -- Involutions

  module Involution {x : Circuit n} (xx : x • x ≈ ε) where

    -- x cancels against itself in front of a word, and behind one.
    cancelˡ : (u : Circuit n) → x • x • u ≈ u
    cancelˡ = cancel-in xx

    cancelʳ : (u : Circuit n) → u • x • x ≈ u
    cancelʳ = cancel-at xx

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

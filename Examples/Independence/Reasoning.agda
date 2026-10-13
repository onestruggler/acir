------------------------------------------------------------------------
-- Presentations of groups
--
-- Equational reasoning in a fragment's theory
--
-- After Examples.Groups.CNOT+Dihedral.Reasoning: an axiom on the bottom
-- wires of a circuit of any width (Circuit.Prop's pad, for the arities
-- up to four that the fragments have), lifting a derivation one wire up,
-- and at a fixed width the setoid reasoning of the congruence with
-- rewriting at the front, the back or in the middle of a word, and
-- re-bracketing by the associativity solver.  A symmetry rule is
-- Circuit.Prop's sym-rule, which every fragment exports.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Independence.Reasoning (Gate : ℕ → Set) where

open import Data.Bool.Base using (T)
open import Data.Nat using (_+_ ; _≤ᵇ_)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊)

import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Examples.Independence.Prop Gate

module Theory (_SRel,_===_ : (n : ℕ) → CRel n) where

  open Lift-To-Prop _SRel,_===_

  private
    variable
      n : ℕ
      w v : Circuit n

  -- The axiom a, of arity n ≤ 4, on the bottom wires of a circuit of
  -- n + k wires.
  ax-at : (a : n SRel, w === v) {_ : T (n ≤ᵇ 4)} (k : ℕ) →
          (n + k) ⊢ w ↓ᵏ k ≈ v ↓ᵏ k
  ax-at {n} a {t} = pad (≤ᵇ⇒≤ n 4 t) (PB.axiom (srel (srel a)))

  -- A derivation, one wire up.
  lift : n ⊢ w ≈ v → (₁₊ n) ⊢ w ↑ ≈ v ↑
  lift {w = w} {v} = lemma-cong↑ w v

  module Width (n : ℕ) where

    open PB (n VRel,_===_) public
      using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit ; refl')
    open PP (n VRel,_===_) public using (word-setoid ; by-assoc)
    open SR word-setoid public

    -- Rewriting at the front, at the back, and in the middle.
    front : ∀ {a b} (s : Circuit n) → a ≈ b → a • s ≈ b • s
    front s e = cong e refl

    back : ∀ (p : Circuit n) {a b} → a ≈ b → p • a ≈ p • b
    back p e = cong refl e

    mid : ∀ (p : Circuit n) {a b} (s : Circuit n) → a ≈ b → p • a • s ≈ p • b • s
    mid p s e = cong refl (cong e refl)

    -- Cancelling a word that is equivalent to ε.
    drop-ε : ∀ {a} (p s : Circuit n) → a ≈ ε → p • a • s ≈ p • s
    drop-ε p s e = trans (mid p s e) (cong refl left-unit)

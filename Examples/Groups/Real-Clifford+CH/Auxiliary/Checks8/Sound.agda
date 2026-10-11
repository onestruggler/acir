------------------------------------------------------------------------
-- Presentations of groups
--
-- The statement "two words over P have the same matrix on three
-- qubits", behind an abstract name
--
-- Checks8.sound proves one such statement per rule of Figure 8, by
-- cases on the rule.  At each case Agda compares the statement the
-- case proves with the one the rule's indices ask for; the two spell
-- the same words differently (a width written 3 or ₃₊ 0, a constant
-- of Figure8 or of Checks8.Base), and were the statement transparent
-- the comparison would go through the operators of the words — sums
-- over every intermediate basis vector, exponential in the word.
-- Behind an abstract name the comparison is on the words.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.Sound where

open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Word.Base using (Word)

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.Base

open BF using (⟦_⟧Y)

abstract
  Sound : Word (GenP 3) → Word (GenP 3) → Set
  Sound u t = ⟦ u ⟧Y ~ ⟦ t ⟧Y

  -- From a decision.
  sound-by : (u t : Word (GenP 3)) → decide u t ≡ true → Sound u t
  sound-by = decide-sound

  -- What the name stands for.
  unSound : ∀ {u t} → Sound u t → ⟦ u ⟧Y ~ ⟦ t ⟧Y
  unSound s = s

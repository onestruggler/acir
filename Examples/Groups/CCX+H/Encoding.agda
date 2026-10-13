------------------------------------------------------------------------
-- Presentations of groups
--
-- An explicit encoding into Li--Ross--Selinger's scaled alphabet.
--
-- The classical gates are disjoint products of transpositions.
-- IH acts on adjacent pairs of levels, hence on wire 0.  Conjugating
-- it by the permutation exchanging wire 0 and wire p gives H on p.
-- This is one global IH, not a product of two-level Hadamards: the
-- latter do not in general belong to the scaled dyadic group.
--
-- This defines the compiler.  Its identification with an independent
-- tensor semantics at arbitrary width is a separate proof obligation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.Encoding where

open import Data.Bool.Base using (not ; _∧_ ; if_then_else_)
open import Data.List.Base using (upTo)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _∸_)
  renaming (_^_ to _^ℕ_)
open import Word.Base using (Word ; ε ; _•_ ; _ʷ)

import Examples.Groups.CCX+HH.Encoding as D
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
open import Examples.Groups.CCX+H.Syntactics

private
  variable
    n : ℕ

Levels : ℕ → Set
Levels n = Word (T.Genᴸ (2 ^ℕ n))

-- The wire permutation (0,p), as pairwise disjoint transpositions.
-- For p>0, select the indices with bit 0 = 1 and bit p = 0.  Their
-- partners have bit 0 = 0 and bit p = 1, hence index a+2^p-1.
E-swap : (n p : ℕ) → D.Levels n
E-swap n zero = ε
E-swap n (suc p) = D.∏ (upTo (2 ^ℕ n)) λ a →
  if D.bit a 0 ∧ not (D.bit a (suc p))
  then D.xword n a ((a + 2 ^ℕ suc p) ∸ 1)
  else ε

E-H : (n p : ℕ) → Levels n
E-H n zero = T.H
E-H n (suc p) =
  T.⌊ E-swap n (suc p) ⌋ʷ • T.H • T.⌊ E-swap n (suc p) ⌋ʷ

encode-view : (n : ℕ) → View → Levels n
encode-view n (at-X p) = T.⌊ D.E-X n p ⌋ʷ
encode-view n (at-H p) = E-H n p
encode-view n (at-CX p) = T.⌊ D.E-CX n (suc p) p ⌋ʷ
encode-view n (at-CCX p) = T.⌊ D.E-CCX n (suc p) (suc (suc p)) p ⌋ʷ

e : Gen n → Levels n
e {n} g = encode-view n (view g)

encode : Circuit n → Levels n
encode = e ʷ

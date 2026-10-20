------------------------------------------------------------------------
-- Presentations of groups
--
-- Complete equations whose H₂ normal forms both have even parity.
-- This discharges the extra two-level Hadamard rules without assuming
-- the circuit completeness theorem being constructed.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Repaired.EvenCompleteness where

open import Data.Bool.Base using (false ; true)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Examples.Groups.CCX+HH-3qubit.Repaired.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Matrix using (⟦_⟧ᴹ)
import Examples.Groups.CCX+HH-3qubit.Normalization as N
open import Examples.Groups.CCX+HH-3qubit.Repaired.DyadicCompleteness
  using (matrix-sound ; completeness)
open import Examples.Groups.CCX+HH-3qubit.Repaired.Even public
  using (even ; FromEven)
open import Presentation.Base _===_ hiding (_===_ ; _≈_)

from-even : FromEven
from-even {w} {v} b c pw pv eq = trans pw (trans bodies (sym pv))
  where
  bodies : N.dyadic b ≈ N.dyadic c
  bodies = completeness {w = b} {v = c}
    (Eq.trans (Eq.sym (matrix-sound {w} {N.dyadic b} pw))
      (Eq.trans eq (matrix-sound {v} {N.dyadic c} pv)))

by-even : (w v : Word Gen) →
          N.Normal.odd (N.normalize w) ≡ false →
          N.Normal.odd (N.normalize v) ≡ false →
          ⟦ w ⟧ᴹ ≡ ⟦ v ⟧ᴹ → w ≈ v
by-even w v ew ev eq = from-even bw bv pw pv eq
  where
  bw = N.Normal.body (N.normalize w)
  bv = N.Normal.body (N.normalize v)
  pw : w ≈ N.dyadic bw
  pw = even (N.normalize w) ew
  pv : v ≈ N.dyadic bv
  pv = even (N.normalize v) ev

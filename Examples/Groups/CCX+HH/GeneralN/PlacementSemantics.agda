------------------------------------------------------------------------
-- Presentations of groups
--
-- The fixed-width multiple-control compiler, including arbitrary wire
-- placement and expansion of SWAP, is correct in ordinary matrices.
-- Every basis input is covered, including both values of the borrowed
-- bit.  The theorem returns a circuit at exactly the requested width.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.CCX+HH.GeneralN.PlacementSemantics (extra : ℕ) where

open import Data.Fin.Base using (Fin)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality using (_≡_ ; trans)
open import Examples.Groups.CCX+HH.GeneralN.Placement extra
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (bits)
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
import Examples.Groups.CCX+HH.Semantics as Q

physical-controlled-ket : ∀ k (cs : Vec (Fin width) k) t r → N.Valid cs t r →
  ∀ s → quantum (physical-controlled k cs t r) (ket width s) ≡ ket width (N.controlled cs t s)
physical-controlled-ket k cs t r valid s = trans (physical-ket (controlled k cs t r) s)
  (ket-cong width (controlled-correct k cs t r valid s))

physical-controlled-column : ∀ k (cs : Vec (Fin width) k) t r → N.Valid cs t r →
  ∀ i → A.col (Q.interpret (physical-controlled k cs t r)) i ≡
    ket width (N.controlled cs t (bits width i))
physical-controlled-column k cs t r valid i = trans (physical-column (controlled k cs t r) i)
  (ket-cong width (controlled-correct k cs t r valid (bits width i)))

------------------------------------------------------------------------
-- Presentations of groups
--
-- Every disjoint pair of four-level K blocks has a physical CCX+HH
-- circuit at width >=4.  The two increasing embeddings name the
-- blocks and their disjointness excludes all support coincidences.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_ ; _^_)

module Examples.Groups.CCX+H.GeneralN.KPair (n : ℕ) where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb)
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
import Examples.Groups.CCX+HH.GeneralN.KPairBase as Base
import Examples.Groups.CCX+H.GeneralN.KPairRouting as Routing

module B = Base n
module R = Routing n
open R public using (DisjointBlocks)

private
  source : Emb 8 (2 ^ (4 + n))
  source = record { ι = B.level ; mono = B.increasing }

module Pair (target : DisjointBlocks) where
  module C = R.Compile source B.circuit B.correct target
  open C public using (circuit ; correct)

circuit : DisjointBlocks → H.Circuit (4 + n)
circuit target = Pair.circuit target

correct : ∀ target → Q.interpret (circuit target) ≡ A.⟦ R.DisjointBlocks.auxiliary target ⟧ᵐ
correct target = Pair.correct target

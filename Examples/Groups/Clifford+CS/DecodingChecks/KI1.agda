------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding checked on four qubits: the hybrid on a consecutive pair, both orientations (DecodingChecks.Base)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.DecodingChecks.KI1 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations

open import Examples.Groups.Clifford+CS.DecodingChecks.Base
open import Examples.Groups.Clifford+CS.Auxiliary.P using (pp ; px ; dx ; ki)

_ : chk (ki ₀ ₁ ₀ (lt ₀ ₁))
_ = Eq.refl

_ : chk (ki ₅ ₆ ₅ (lt ₅ ₆))
_ = Eq.refl


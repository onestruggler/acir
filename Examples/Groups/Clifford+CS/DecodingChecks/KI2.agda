------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding checked on four qubits: the hybrid with a gap (DecodingChecks.Base)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.DecodingChecks.KI2 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations

open import Examples.Groups.Clifford+CS.DecodingChecks.Base
open import Examples.Groups.Clifford+CS.Auxiliary.P using (pp ; px ; dx ; ki)

_ : chk (ki ₂ ₆ ₂ (lt ₂ ₆))
_ = Eq.refl


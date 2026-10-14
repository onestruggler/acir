------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding checked on four qubits: the double exchange (DecodingChecks.Base)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.DecodingChecks.DX1 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations

open import Examples.Groups.Clifford+CS.DecodingChecks.Base
open import Examples.Groups.Clifford+CS.Auxiliary.P using (pp ; px ; dx ; ki)

_ : chk (dx ₀ ₁ ₂ ₃ (lt ₀ ₁) (lt ₂ ₃))
_ = Eq.refl


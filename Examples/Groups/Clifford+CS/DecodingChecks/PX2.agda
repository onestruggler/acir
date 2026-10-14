------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding checked on four qubits: the signed exchange with a gap (DecodingChecks.Base)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.DecodingChecks.PX2 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations

open import Examples.Groups.Clifford+CS.DecodingChecks.Base
open import Examples.Groups.Clifford+CS.Auxiliary.P using (pp ; px ; dx ; ki)

_ : chk (px ₀ ₀ ₃ (lt ₀ ₃))
_ = Eq.refl

_ : chk (px ₃ ₀ ₃ (lt ₀ ₃))
_ = Eq.refl


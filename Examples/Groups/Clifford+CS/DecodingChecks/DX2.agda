------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding checked on four qubits: the double exchange with gaps (DecodingChecks.Base)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.DecodingChecks.DX2 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations

open import Examples.Groups.Clifford+CS.DecodingChecks.Base
open import Examples.Groups.Clifford+CS.Auxiliary.P using (pp ; px ; dx ; ki)

_ : chk (dx ₁ ₄ ₅ ₉ (lt ₁ ₄) (lt ₅ ₉))
_ = Eq.refl


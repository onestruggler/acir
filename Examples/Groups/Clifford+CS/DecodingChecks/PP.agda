------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding checked on four qubits: the phase pair (DecodingChecks.Base)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.DecodingChecks.PP where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations

open import Examples.Groups.Clifford+CS.DecodingChecks.Base
open import Examples.Groups.Clifford+CS.Auxiliary.P using (pp ; px ; dx ; ki)

-- The phase pair: consecutive in both orientations, a chain up, a chain
-- down.
_ : chk (pp ₀ ₁)
_ = Eq.refl
_ : chk (pp ₁ ₀)
_ = Eq.refl
_ : chk (pp ₅ ₆)
_ = Eq.refl
_ : chk (pp ₃ ₇)
_ = Eq.refl
_ : chk (pp ₉ ₂)
_ = Eq.refl


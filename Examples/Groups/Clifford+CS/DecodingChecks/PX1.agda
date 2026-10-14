------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding checked on four qubits: the signed exchange on a consecutive pair, either sign (DecodingChecks.Base)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.DecodingChecks.PX1 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations

open import Examples.Groups.Clifford+CS.DecodingChecks.Base
open import Examples.Groups.Clifford+CS.Auxiliary.P using (pp ; px ; dx ; ki)

_ : chk (px ₀ ₀ ₁ (lt ₀ ₁))
_ = Eq.refl

_ : chk (px ₁ ₀ ₁ (lt ₀ ₁))
_ = Eq.refl

_ : chk (px ₆ ₆ ₇ (lt ₆ ₇))
_ = Eq.refl


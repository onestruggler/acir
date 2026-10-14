------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding checked on four qubits: the signed exchange (DecodingChecks.Base)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.DecodingChecks.PX where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations

open import Examples.Groups.Clifford+CS.DecodingChecks.Base
open import Examples.Groups.Clifford+CS.Auxiliary.P using (pp ; px ; dx ; ki)

-- The signed exchange: both signs on a consecutive pair, a gap, the
-- sign elsewhere.
_ : chk (px ₀ ₀ ₁ (lt ₀ ₁))
_ = Eq.refl
_ : chk (px ₁ ₀ ₁ (lt ₀ ₁))
_ = Eq.refl
_ : chk (px ₆ ₆ ₇ (lt ₆ ₇))
_ = Eq.refl
_ : chk (px ₀ ₀ ₃ (lt ₀ ₃))
_ = Eq.refl
_ : chk (px ₃ ₀ ₃ (lt ₀ ₃))
_ = Eq.refl
_ : chk (px ₅ ₂ ₄ (lt ₂ ₄))
_ = Eq.refl


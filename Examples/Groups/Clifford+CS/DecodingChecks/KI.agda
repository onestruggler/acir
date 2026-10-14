------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding checked on four qubits: the hybrid (DecodingChecks.Base)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.DecodingChecks.KI where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations

open import Examples.Groups.Clifford+CS.DecodingChecks.Base
open import Examples.Groups.Clifford+CS.Auxiliary.P using (pp ; px ; dx ; ki)

-- The hybrid: consecutive in both orientations, a gap, the sink moved.
_ : chk (ki ₀ ₁ ₀ (lt ₀ ₁))
_ = Eq.refl
_ : chk (ki ₅ ₆ ₅ (lt ₅ ₆))
_ = Eq.refl
_ : chk (ki ₂ ₆ ₂ (lt ₂ ₆))
_ = Eq.refl
_ : chk (ki ₀ ₁ ₅ (lt ₀ ₁))
_ = Eq.refl
_ : chk (ki ₃ ₇ ₉ (lt ₃ ₇))
_ = Eq.refl

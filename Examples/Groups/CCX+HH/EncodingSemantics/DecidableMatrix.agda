------------------------------------------------------------------------
-- Presentations of groups
--
-- Exact finite-matrix equality from equality of scalar entries.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.EncodingSemantics.DecidableMatrix where

open import Data.Nat.Base using (ℕ)
import Data.Vec.Properties as Vec
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (refl)
open import Relation.Nullary.Decidable using (yes ; no)
open import Quantum.Synthesis.Matrix using (Matrix ; Matrix')

equality : ∀ {A : Set} {m n : ℕ} → DecidableEquality A → DecidableEquality (Matrix m n A)
equality dec (Matrix' a) (Matrix' b) with Vec.≡-dec (Vec.≡-dec dec) a b
... | yes eq = yes (Eq.cong Matrix' eq)
... | no neq = no (λ { refl → neq refl })

------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding of Definition 8.3 on three qubits, checked for the
-- signed exchanges (−1)_[3] X_[a,b], all a and b: an eighth of
-- DecodingChecks' signed exchanges, each eighth a module of its own so
-- that none takes long (about 18 s)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.DecodingChecks.ZX3 where

open import Data.Bool using (true)
open import Data.Bool.ListAction using (all)
open import Data.List using (allFin)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Notations using (₃)

open import Examples.Groups.Real-Clifford+CH.Encoding using (zx)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DecodingChecks.Base using (check)

zx-all₃ : all (λ a → all (λ b → check (zx ₃ a b)) (allFin 8)) (allFin 8) ≡ true
zx-all₃ = refl

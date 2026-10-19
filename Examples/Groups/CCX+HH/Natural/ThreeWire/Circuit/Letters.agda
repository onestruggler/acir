------------------------------------------------------------------------
-- Presentations of groups
--
-- The nine letters of the tower as three-wire circuits of Natural.
--
-- CXr i is HH i CX i HH i, the CNOT from wire i to wire i + 1, and Z1
-- is HH0 X1 HH0; every other letter is its gate.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Letters where

open import Data.List.Base using (List ; [] ; _∷_ ; concatMap)

open import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Kit
import Examples.Groups.CCX+HH.Natural.ThreeWire.Gamma as Γm

dec : Γm.L → List (Gen 3)
dec Γm.x0   = x₀ ∷ []
dec Γm.x1   = x₁ ∷ []
dec Γm.x2   = x₂ ∷ []
dec Γm.cx0  = cx₀ ∷ []
dec Γm.cx1  = cx₁ ∷ []
dec Γm.cxr0 = hh₀ ∷ cx₀ ∷ hh₀ ∷ []
dec Γm.cxr1 = hh₁ ∷ cx₁ ∷ hh₁ ∷ []
dec Γm.ccx0 = ccx₀ ∷ []
dec Γm.z1   = hh₀ ∷ x₁ ∷ hh₀ ∷ []

-- A relator of the tower, decoded.
decoded : Γm.Rel → List (Gen 3)
decoded r = concatMap dec (Γm.relator r)

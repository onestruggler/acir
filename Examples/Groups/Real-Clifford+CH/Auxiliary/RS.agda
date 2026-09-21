------------------------------------------------------------------------
-- Presentations of groups
--
-- The Reidemeister–Schreier data for the theory of P
-- (Clément, Appendix A.3)
--
-- Theorem 4.10 — completeness of Figure 8 for the alphabet P — is
-- obtained in the paper from Theorem 4.4, completeness of Figure 7 for
-- the auxiliary generators, by the Reidemeister–Schreier method for
-- monoids.  Its three data are a representative of each coset of the
-- even-parity subgroup (`Cosets`), a semantics-preserving map from P to
-- words over the auxiliary generators (`Auxiliary.P.asG`, the paper's
-- f) and a coset action (`CosetAction`, the paper's h).
--
-- This module fixes the two distinguished indices those definitions
-- are stated over: the paper's 0 and 1, which at width 2ⁿ with n ≥ 3
-- are `fin8 ₀` and `fin8 ₁`.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.RS (m : ℕ) where

open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ-inject≤)
open import Data.Nat using () renaming (_^_ to _^ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)

open import Notations using (₀ ; ₁ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (fin8)

------------------------------------------------------------------------
-- The two distinguished indices

-- The paper's 0 and 1.
z₀ o₁ : Fin (2 ^ℕ (₃₊ m))
z₀ = fin8 {m} ₀
o₁ = fin8 {m} ₁

-- The embedding into a wider index set keeps the numeral.
toℕ-z₀ : toℕ z₀ ≡ 0
toℕ-z₀ = toℕ-inject≤ ₀ _

toℕ-o₁ : toℕ o₁ ≡ 1
toℕ-o₁ = toℕ-inject≤ ₁ _

-- So they are distinct.
z₀≢o₁ : z₀ ≢ o₁
z₀≢o₁ e = 0≢1 (Eq.trans (Eq.sym (toℕ-inject≤ ₀ _))
               (Eq.trans (Eq.cong toℕ e) (toℕ-inject≤ ₁ _)))
  where
  0≢1 : 0 ≢ 1
  0≢1 ()

------------------------------------------------------------------------
-- The coset action at those indices

open import Examples.Groups.Real-Clifford+CH.Auxiliary.CosetAction
  (₃₊ m) z₀ o₁ z₀≢o₁ public using (act)

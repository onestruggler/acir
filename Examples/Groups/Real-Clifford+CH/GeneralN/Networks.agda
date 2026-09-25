------------------------------------------------------------------------
-- Presentations of groups
--
-- The cycles of Place as words of the symmetric presentation
--
-- So that PermCalc applies to them: two networks built from the cycles
-- and single swaps are equal as soon as their permutations agree, which
-- is decided by computing both at every wire.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Networks where

open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net ; net-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (cyc ; cyc⁻¹)

private
  variable
    r : ℕ

scyc scyc⁻¹ : (i : ℕ) → Word (S.Gen (₁₊ (i +ℕ r)))
scyc zero      = ε
scyc (suc i)   = S.σ • scyc i S.↑
scyc⁻¹ zero    = ε
scyc⁻¹ (suc i) = scyc⁻¹ i S.↑ • S.σ

net-cyc : ∀ i → net (scyc {r} i) ≡ cyc i
net-cyc zero    = Eq.refl
net-cyc (suc i) = Eq.cong (Ex ↓ •_) (Eq.trans (net-↑ (scyc i)) (Eq.cong _↑ (net-cyc i)))

net-cyc⁻¹ : ∀ i → net (scyc⁻¹ {r} i) ≡ cyc⁻¹ i
net-cyc⁻¹ zero    = Eq.refl
net-cyc⁻¹ (suc i) = Eq.cong (_• Ex ↓) (Eq.trans (net-↑ (scyc⁻¹ i)) (Eq.cong _↑ (net-cyc⁻¹ i)))

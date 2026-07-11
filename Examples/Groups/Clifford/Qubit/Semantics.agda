------------------------------------------------------------------------
-- Presentations of groups
--
-- The n-qubit Clifford group (p = 2) as a group extension
--
--     1 ─→ Pauli n ─→ Clifford n ─→ Sp(2n, 2) ─→ 1
--
-- Semantic side.  The total group is realised as the semidirect product
-- Pauli n ⋊ Sp(2n, 2) under the symplectic action φ (Examples.Groups.
-- Symplectic.Semidirect), packaged as a ForStdlib.Algebra.Construct.
-- Extension record: incl is the Pauli inclusion n ↦ (n , ε), proj is the
-- projection onto the symplectic quotient.  This is the group that
-- Examples.Groups.Clifford.Qubit.Presentation is a presentation of.
--
-- (The physical Clifford realisation lands the gate S at (X , σ_S), so
-- that S² = (X + σ_S X , id) = (Z , id) = the Pauli Z — matching the
-- order-S ↦ Z entry of the cocycle in Qubit.Presentation.)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Examples.Groups.Clifford.Qubit.Semantics where

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime ; prime?)
open import Relation.Nullary.Decidable using (from-yes)
open import Level using (0ℓ)
open import Algebra.Bundles using (Group)

-- Qubit case: fix the prime to 2.
p-2 : ℕ
p-2 = 0

p-prime : Prime 2
p-prime = from-yes (prime? 2)

open import ForStdlib.Algebra.Construct.Extension using (Extension ; semidirect)

open import Examples.Groups.Pauli.Semantics p-2 p-prime using (+ₚ-group)
open import Examples.Groups.Symplectic.Semantics p-2 p-prime using (Sp-group)
open import Examples.Groups.Symplectic.Semidirect p-2 p-prime using (φ)

------------------------------------------------------------------------
-- The Clifford group as an extension of Sp(2n, 2) by Pauli n

-- 1 → Pauli n → Clifford n → Sp(2n, 2) → 1, realised as the semidirect
-- product Pauli n ⋊ Sp(2n, 2) under the symplectic action φ.
Clifford-extension : (n : ℕ) → Extension (+ₚ-group n) (Sp-group n)
Clifford-extension n = semidirect (+ₚ-group n) (Sp-group n) (φ n)

-- The total group of the extension: the (affine) Clifford group.
Clifford-group : (n : ℕ) → Group 0ℓ 0ℓ
Clifford-group n = Extension.total (Clifford-extension n)

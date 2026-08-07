------------------------------------------------------------------------
-- Presentations of groups
--
-- The n-qubit Clifford group (p = 2) as group extensions, semantic side.
-- Two layers, neither of them split:
--
--     1 ─→ Pauli n ─→ Clifford n ─→ Sp(2n, 2) ─→ 1        (below)
--     1 ─→ ⟨ω⟩     ─→ Exact n    ─→ Clifford n ─→ 1        (scalar layer)
--
-- The first is re-exported from Examples.Groups.Clifford.Qubit.
-- CliffordGroup, where the total group is the quotient of Clifford words
-- by equal action on the phased Pauli group P4, and incl / proj /
-- exactness are proved from that action.  It is NOT a semidirect
-- product: `semidirect` would force S² = 1, whereas
-- CliffordGroup.S²=Z proves
--
--     S • S  ≈ᶜ  incl (pZ ∷ pIₙ),
--
-- i.e. the phase gate projects to an involution of Sp(2n,2) but squares
-- to the Pauli Z.  So proj admits no section taking that involution to
-- an involution, and the extension is genuinely non-split.  (This is the
-- semantic counterpart of corr (order-S) = Z₀, the single nontrivial
-- entry of the cocycle in Qubit.Presentation.)
--
-- The second layer restores the global scalar ω of order 8.  Only the
-- scalar group is built here; what the extension still needs is recorded
-- at the end of the file.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Semantics where

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime ; prime?)
open import Relation.Nullary.Decidable using (from-yes)
open import Level using (0ℓ)
open import Algebra.Bundles using (Group)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

-- Qubit case: fix the prime to 2.
p-2 : ℕ
p-2 = 0

p-prime : Prime 2
p-prime = from-yes (prime? 2)

open import ForStdlib.Algebra.Construct.Extension using (Extension)

open import Examples.Groups.Pauli.Semantics p-2 p-prime using (+ₚ-group)
open import Examples.Groups.Symplectic.Semantics p-2 p-prime using (Sp-group)

import Examples.Groups.Clifford.Qubit.CliffordGroup as CG

------------------------------------------------------------------------
-- Layer 1: the Clifford group as a non-split extension of Sp(2n, 2)

-- 1 → Pauli n → Clifford n → Sp(2n, 2) → 1.
Clifford-extension : (n : ℕ) → Extension (+ₚ-group n) (Sp-group n)
Clifford-extension = CG.Clifford-extension

-- The total group: Clifford words modulo equal action on P4.
Clifford-group : (n : ℕ) → Group 0ℓ 0ℓ
Clifford-group n = Extension.total (Clifford-extension n)

-- The witness that it does not split, re-exported for convenience.
open CG using (S²=Z) public

------------------------------------------------------------------------
-- Layer 2: the scalars ⟨ω⟩

-- ⟨ω⟩ ≅ ℤ/8, written additively in the exponent of ω: ωʲ · ωᵏ = ω^{j+k}.
-- (+-0-group m has carrier ℤ (₂₊ m), so the order 8 is m = 6; the check
-- below pins it, since an off-by-one here would silently change ω's order.)

open import Zp.ModularArithmetic using (ℤ ; +-0-group)

Scalar-group : Group 0ℓ 0ℓ
Scalar-group = +-0-group 6

private
  scalar-order-8 : Group.Carrier Scalar-group ≡ ℤ 8
  scalar-order-8 = Eq.refl

------------------------------------------------------------------------
-- Exact n : what is still missing
--
-- The scalar layer is central and non-split, so the construction to use
-- is ForStdlib.Algebra.Construct.CentralExtension:
--
--     centralExtension Scalar-abelian (Clifford-group n) γ
--       : Extension Scalar-group (Clifford-group n)
--
-- Everything there — the twisted group, both homomorphisms, all four
-- exactness conditions — is already proved.  The one missing input is
--
--     γ : Cocycle Scalar-abelian (Clifford-group n),
--
-- a normalised c : Clifford n → Clifford n → ℤ/8 satisfying the cocycle
-- identity, and with (SH)³ ↦ ω so that the scalar really has order 8.
--
-- Why this is not the qupit formula.  Examples.Groups.Clifford.Qupit.
-- Semantics twists by ½·sform P (ap S Q); ℤ/2 has no ½, and its p = 2
-- replacement is the ℤ/4-valued γ = ι ∘ β of SignedPauli.  But that
-- cocycle only reaches the Pauli layer: any twist whose symplectic
-- dependence enters through the action alone vanishes on the lift of SH
-- at zero Pauli part, giving (SH)³ = 1 instead of ω.  So c must depend on
-- the symplectic components directly — it represents the nontrivial
-- class in H²(Sp(2n,2), ℤ/8), the extension known group-theoretically as
-- 2^{2n}·Sp(2n,2).
--
-- Concretely, in the word model of Clifford n, supplying c is equivalent
-- to supplying
--
--     ωExp : (w : Word (Gen n)) → cact w ≗ id → ℤ/8,
--
-- since a word acting trivially on P4 is exactly a scalar ωᵏ.  That k is
-- precisely the datum cact discards, so it cannot be recovered from the
-- action; it has to come from a faithful model.  The two candidates in
-- reach are Selinger's exact normal form (Qubit.Selinger.NormalForm,
-- ExactNF n = NF n × Fin 8, uniqueness still WIP) and matrices over
-- ℤ[1/√2, i].

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
-- The second layer restores the global scalar ω of order 8.  It is built
-- as a central extension, from the ω-exponent Ω of a word; see
-- Qubit.ExactCocycle, which derives the whole cocycle from Ω, and the
-- note at the end of this file for why Ω is the one thing the P4-action
-- cannot supply.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

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
-- Layer 2: the scalars ⟨ω⟩, and the exact Clifford group
--
-- ⟨ω⟩ ≅ ℤ/8, written additively in the exponent of ω: ωʲ · ωᵏ = ω^{j+k}.
-- The extension itself is the central extension twisted by the cocycle
-- that Qubit.ExactCocycle derives from the ω-exponent Ω of a word.

open import Examples.Groups.Clifford.Qubit.ExactCocycle
  using (Scalar ; Scalar-abelian ; Scalar-group ; ScalarExponent ; Pins-ω)
  renaming (Exact to Exact-of)

-- 1 → ⟨ω⟩ → Exact n → Clifford n → 1.
Exact : ∀ {n} → ScalarExponent n → Extension Scalar-group (Clifford-group n)
Exact = Exact-of

------------------------------------------------------------------------
-- What Exact n still takes as input
--
-- Everything in ForStdlib.Algebra.Construct.CentralExtension — the
-- twisted group, both homomorphisms, all four exactness conditions — is
-- proved, and Qubit.ExactCocycle now derives the cocycle (normalisation
-- and the cocycle identity included) from a single function
--
--     Ω : Word (Gen n) → ℤ/8,
--
-- the power of ω that a word carries against a chosen exact lift.  So
-- `Exact` is a definition, not a hole; what remains is to *supply* one
-- ScalarExponent n meeting the specification Pins-ω, i.e. Ω ((SH)³) = ₁,
-- without which the ⟨ω⟩ layer is a proper quotient of ℤ/8.
--
-- Why no formula does it.  Examples.Groups.Clifford.Qupit.Semantics
-- twists by ½·sform P (ap S Q); ℤ/2 has no ½, and its p = 2 replacement
-- is the ℤ/4-valued γ = ι ∘ β of SignedPauli.  But that cocycle only
-- reaches the Pauli layer.  More sharply — and this is now a theorem,
-- ExactCocycle.action-blind — *any* Ω that is invariant under ≈ᶜ sends ω
-- to ₀ and so fails Pins-ω, because ω acts trivially on P4
-- (Selinger.Action.cact-ω).  The scalar is exactly the datum cact
-- discards, so Ω has to come from a faithful model of the exact Clifford
-- group.  The two candidates in reach are Selinger's exact normal form
-- (Qubit.Selinger.NormalForm, ExactNF n = NF n × Fin 8, uniqueness still
-- WIP) and matrices over ℤ[1/√2, i].
--
-- The trivial cocycle is not an escape: it gives the direct product
-- ℤ/8 × Clifford n, whose Ω is constant ₀ — action-invariant, hence
-- ruled out above.  Group-theoretically the extension is the non-split
-- 2^{2n}·Sp(2n,2), the nontrivial class in H²(Clifford n, ℤ/8).

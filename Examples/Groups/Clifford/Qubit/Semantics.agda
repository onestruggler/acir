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
-- The second layer restores the global scalar ω of order 8.  Its total
-- group is the one Figure 8 presents — Clifford words modulo the exact
-- congruence — so it is assembled by hand, like the first; see
-- Qubit.ExactExtension, and the note at the end of this file for what it
-- still takes as input and why the P4-action cannot supply it.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Semantics where

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime ; prime?)
open import Notations using (₁₊)
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
-- The extension is an ordinary one, assembled by hand exactly as layer 1
-- is: the total group is Clifford words modulo the *exact* congruence —
-- the one Selinger's Figure 8 presents, which unlike ≈ᶜ still sees the
-- global scalar — with incl k = ωᵏ and proj the identity on words.  See
-- Qubit.ExactExtension.
--
-- The scalar layer needs at least one qubit, ω living on the first wire.

open import Examples.Groups.Clifford.Qubit.ExactExtension
  using (Scalar-group ; Exact-group ; ExactData)
  renaming (Exact to Exact-of)

-- 1 → ⟨ω⟩ → Exact n → Clifford n → 1.
Exact : ∀ {n} → ExactData n → Extension Scalar-group (Clifford-group (₁₊ n))
Exact = Exact-of

------------------------------------------------------------------------
-- What Exact n still takes as input
--
-- The group structure of the Figure-8 words, that k ↦ ωᵏ is a
-- homomorphism ℤ/8 → Exact n, surjectivity of proj and that proj kills
-- the scalars are all proved in Qubit.ExactExtension.  So `Exact` is a
-- definition, not a hole; what remains is to supply one ExactData n, and
-- its three fields are Selinger's theorems rather than bookkeeping:
--
--   sound      — Figure-8-equal words act equally on P4;
--   scalars    — a word acting trivially on P4 is some ωᵏ;
--   ω-faithful — ω has order exactly 8 in the presented group.
--
-- `sound` is within reach: Selinger.Action already discharges C1, C2, C3,
-- C5-C9, C12 and C13, and C4 is an identity, leaving C10, C11, C14, C15.
--
-- The other two cannot come from the action, and ExactExtension.
-- action-blind makes that precise: ω acts trivially on P4
-- (Selinger.Action.cact-ω), so if ≈ᶜ implied the Figure-8 congruence then
-- ω = ω¹ and ε = ω⁰ would be identified and ω-faithful would force
-- ₁ ≡ ₀.  The scalar is exactly the datum cact discards, so ω-faithful
-- has to come from a faithful model of the exact Clifford group.  The two
-- candidates in reach are Selinger's exact normal form
-- (Qubit.Selinger.NormalForm, ExactNF n = NF n × Fin 8, uniqueness still
-- WIP) and matrices over ℤ[1/√2, i].
--
-- Group-theoretically the extension is the non-split 2^{1+2n}·Sp(2n,2);
-- in particular a direct product ℤ/8 × Clifford n would be the wrong
-- group, which is why the scalar cannot simply be adjoined.

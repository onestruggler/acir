------------------------------------------------------------------------
-- Presentations of groups
--
-- The n-qubit Clifford group (p = 2) as group extensions, semantic side.
-- Two layers are built here:
--
--     1 ─→ Pauli n ─→ Clifford n ─→ Sp(2n, 2) ─→ 1        (below)
--     1 ─→ ⟨ω⟩     ─→ Exact n    ─→ Clifford n ─→ 1        (scalar layer)
--
-- the second stacking the order-8 global scalar ω back on top of the
-- phaseless Clifford group of Qubit.CliffordGroup.  Only the scalar
-- group itself is built here; the extension is non-split and awaits a
-- ℤ/8 cocycle — see the note below.
--
-- The first extension's total group is realised as the semidirect product
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

open import ForStdlib.Algebra.Construct.Extension using (Extension ; semidirect)

open import Examples.Groups.Pauli.Semantics p-2 p-prime using (+ₚ-group)
open import Examples.Groups.Symplectic.Semantics p-2 p-prime using (Sp-group)
open import Examples.Construct.SemiDirectProduct.Clifford p-2 p-prime using (φ)

------------------------------------------------------------------------
-- The Clifford group as an extension of Sp(2n, 2) by Pauli n

-- 1 → Pauli n → Clifford n → Sp(2n, 2) → 1, realised as the semidirect
-- product Pauli n ⋊ Sp(2n, 2) under the symplectic action φ.
Clifford-extension : (n : ℕ) → Extension (+ₚ-group n) (Sp-group n)
Clifford-extension n = semidirect (+ₚ-group n) (Sp-group n) (φ n)

-- The total group of the extension: the (affine) Clifford group.
Clifford-group : (n : ℕ) → Group 0ℓ 0ℓ
Clifford-group n = Extension.total (Clifford-extension n)

------------------------------------------------------------------------
-- The scalar layer
--
-- The phaseless Clifford group of Qubit.CliffordGroup is the quotient of
-- the exact Clifford group by its centre, the global scalars ⟨ω⟩ with
-- ω = e^{iπ/4} of order 8 (Selinger's relation C1, ω⁸ = 1).  Adding that
-- layer back gives the second extension
--
--     1 ─→ ⟨ω⟩ ─→ Exact n ─→ Clifford n ─→ 1,
--
-- central because a scalar commutes with everything, so the action of
-- the quotient on ⟨ω⟩ is trivial.
--
-- This extension must NOT be built with `semidirect`.  A trivial action
-- makes the total group the direct product ⟨ω⟩ × Clifford n, in which
-- (SH)³ is trivial; in the exact Clifford group (SH)³ = ω has order 8
-- (Selinger's C1/C4 — see Qubit.Selinger.Figure8, where ω is *defined*
-- as (S·H)³).  The extension is genuinely non-split and needs a
-- ℤ/8-valued 2-cocycle.
--
-- The construction to use is ForStdlib.Algebra.Construct.CentralExtension:
--
--     centralExtension Scalar-abelian (CG.Clifford-group n) γ
--       : Extension Scalar-group (CG.Clifford-group n)
--
-- once γ : Cocycle Scalar-abelian (CG.Clifford-group n) is supplied, i.e.
-- a c : Clifford n → Clifford n → ℤ/8 that is normalised and satisfies
-- the cocycle identity.  Everything else — the twisted group, exactness,
-- both homomorphisms — is already proved there.
--
-- Supplying that c is the open problem.  The odd-prime analogue in
-- Examples.Groups.Clifford.Qupit.Semantics twists by ½·sform P (ap S Q),
-- and `half-half` makes it work; ℤ/2 has no ½, which is exactly why the
-- qubit case is the metaplectic one and admits no cocycle of that shape.
-- Note also that no abelian invariant can see ω: any χ with χ(ω) = 1
-- would need 2·χ(H) ≡ 0 (C2) and 4·χ(S) ≡ 0 (C3), forcing χ(ω) =
-- 3(χ(S) + χ(H)) to be even.  So c must come from a faithful model — the
-- repo's route is Selinger's exact normal form (Qubit.Selinger.NormalForm,
-- ExactNF n = NF n × Fin 8), which is still WIP.

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Zp.ModularArithmetic using (ℤ ; +-0-group)

-- ⟨ω⟩ ≅ ℤ/8, written additively in the exponent of ω: ωʲ · ωᵏ = ω^{j+k}.
-- (+-0-group m has carrier ℤ (₂₊ m), so the order 8 is m = 6; the check
-- below pins it, since an off-by-one here would silently change ω's order.)
Scalar-group : Group 0ℓ 0ℓ
Scalar-group = +-0-group 6

private
  scalar-order-8 : Group.Carrier Scalar-group ≡ ℤ 8
  scalar-order-8 = Eq.refl

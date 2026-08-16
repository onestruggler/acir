------------------------------------------------------------------------
-- Presentations of groups
--
-- The n-qubit Clifford group modulo scalars (p = 2), semantic side:
--
--     1 ─→ Pauli n ─→ CMS n ─→ Sp(2n, 2) ─→ 1
--
-- CMS n is the Clifford group modulo scalars, C(n)/⟨ω⟩, and the
-- extension is not split.  Note that the kernel is the *plain* Pauli
-- group Pauli n = (ℤ/2 × ℤ/2)ⁿ, with no phase: the ℤ/4 phase of
-- SignedPauli is used only to define equality of Clifford words, never
-- as the kernel.  See the header of Qubit.CliffordGroup for why it
-- cannot be dropped from that role.
--
-- The layer is re-exported from Examples.Groups.ProjectiveClifford.
-- Qubit.CliffordGroup, where the total group is the quotient of Clifford
-- words by equal action on the phased Pauli group P4, and incl / proj /
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
-- The scalar layer above this one — 1 → ⟨ω⟩ → Exact n → CMS n → 1,
-- which restores the global scalar ω of order 8 — is outside the
-- projective development, in Examples.Groups.Clifford.Qubit.Semantics.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qubit.Semantics.Semantics where

open import Data.Nat using (ℕ)
open import Level using (0ℓ)
open import Algebra.Bundles using (Group)

-- Qubit case: fix the prime to 2.
open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime)

open import ForStdlib.Algebra.Construct.Extension using (Extension)

open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime using (+ₚ-group)
open import Examples.Groups.Symplectic.Semantics p-2 p-prime using (Sp-group)

import Examples.Groups.ProjectiveClifford.Qubit.CliffordGroup as CG

------------------------------------------------------------------------
-- The Clifford group mod scalars as a non-split extension of Sp(2n, 2)

-- 1 → Pauli n → CMS n → Sp(2n, 2) → 1.
CMS-extension : (n : ℕ) → Extension (+ₚ-group n) (Sp-group n)
CMS-extension = CG.CMS-extension

-- The total group: Clifford words modulo equal action on P4.
CMS-group : (n : ℕ) → Group 0ℓ 0ℓ
CMS-group n = Extension.total (CMS-extension n)

-- The witness that it does not split, re-exported for convenience.
open CG using (S²=Z) public

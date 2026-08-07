------------------------------------------------------------------------
-- Presentations of groups
--
-- Selinger's Figure-8 presentation of the n-qubit Clifford operators
-- (arXiv:1310.6813), taken MOD SCALARS: the copy of
-- Examples.Groups.Clifford.Qubit.Selinger.Figure8 with the order-8
-- scalar ω quotiented out.
--
-- The scalar ω is removed outright: this relation set does not mention
-- it at all.  Against Figure8.agda:
--
--   * C1 (ω⁸ = 1) is dropped, and so is C4 (SHSHSH = ω), which was
--     definitional there.  The word ω = (SH)³ is gone with them.
--   * The ω⁻¹ tails of C10 and C11 are dropped, as is ω⁻¹ itself.
--   * Everything else — C2, C3, C5–C9, C12–C15, and the derived words
--     X = HSSH, Z = SS — is verbatim.
--
-- What this presents.  The ω-free C10 and C11 hold in the Clifford group
-- modulo scalars, so this relation set is sound for that quotient and
-- the induced map onto it is onto.  It is NOT thereby a presentation of
-- it: nothing here forces (SH)³ to the identity.  At n = 1 the surviving
-- relations are just H² = S⁴ = 1, whose group is ℤ/2 * ℤ/4, where
-- (SH)³ ≠ 1.  Whether the n ≥ 2 relations force (SH)³ = 1 — which is
-- exactly what the dropped C4 would have asserted — is open here.
--
-- Note that S⁴ = 1 (C3) stays: S² = Z is a Pauli, not a scalar, so it is
-- untouched by removing scalars.  Only the further quotient by the
-- Paulis gives the phaseless S² = 1 of the symplectic presentation.
--
-- As in Figure8, the structural rules (cong↑, comm₁, comm₂) come from
-- Lift-Relation rather than being restated.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Clifford.Qubit.Selinger.Figure8-Mod-Scalar
  (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Notations
open import Word.Base using (Word ; ε ; _•_ ; _^_)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic
  using (Gen ; SympGate ; _↑ ; _↓ ; S ; H ; CZ ; ⊤⊥ ; ⊥⊤)

-- CRel and the structural rules come straight from the circuit framework
-- that Symplectic itself is built on (it keeps its copy private).
open import Circuit.Base SympGate using (CRel ; module Lift-Relation)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Derived words: the Pauli operators X, Z
--
-- Neither ω nor ω⁻¹ is defined here: no relation below mentions the
-- scalar, so the words that named it are gone too.  SH stays — it is
-- still needed to state C10 and C11.

-- SH, the one-qubit word S·H.
SH : Word (Gen (₁₊ n))
SH = S • H

-- X = HSSH, Z = SS  (Selinger §4).
X : Word (Gen (₁₊ n))
X = H • S ^ 2 • H

Z : Word (Gen (₁₊ n))
Z = S ^ 2

------------------------------------------------------------------------
-- The Figure-8 relations, mod scalars

infix 4 _Sel,_===_

data _Sel,_===_ : (n : ℕ) → CRel n where

  -- (b) n ≥ 1
  c2  : ∀ {n} → (₁₊ n) Sel,  H ^ 2 === ε
  c3  : ∀ {n} → (₁₊ n) Sel,  S ^ 4 === ε

  -- (c) n ≥ 2
  c5  : ∀ {n} → (₂₊ n) Sel,  CZ ^ 2 === ε
  c6  : ∀ {n} → (₂₊ n) Sel,  S ↓ • CZ === CZ • S ↓
  c7  : ∀ {n} → (₂₊ n) Sel,  S ↑ • CZ === CZ • S ↑
  c8  : ∀ {n} → (₂₊ n) Sel,  X ↓ • CZ === CZ • X ↓ • Z ↑
  c9  : ∀ {n} → (₂₊ n) Sel,  X ↑ • CZ === CZ • Z ↓ • X ↑

  -- C10 and C11 lose their trailing ω⁻¹.
  c10 : ∀ {n} → (₂₊ n) Sel,  CZ • H ↑ • CZ ===
                             SH ↑ • CZ • (S • H • S) ↑ • S ↓
  c11 : ∀ {n} → (₂₊ n) Sel,  CZ • H ↓ • CZ ===
                             SH ↓ • CZ • (S • H • S) ↓ • S ↑

  -- (d) n ≥ 3
  c12 : ∀ {n} → (₃₊ n) Sel,  CZ ↑ • CZ === CZ • CZ ↑
  c13 : ∀ {n} → (₃₊ n) Sel,  ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ === ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
  c14 : ∀ {n} → (₃₊ n) Sel,  (⊤⊥ ↑ • CZ ↓) ^ 3 === ε
  c15 : ∀ {n} → (₃₊ n) Sel,  (⊥⊤ ↓ • CZ ↑) ^ 3 === ε

------------------------------------------------------------------------
-- The full relation, with the structural rules srel/cong↑/comm₁/comm₂.

open Lift-Relation _Sel,_===_ public

infix 4 _CRel,_===_
_CRel,_===_ : (n : ℕ) → CRel n
_CRel,_===_ = _VRel,_===_

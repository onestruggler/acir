------------------------------------------------------------------------
-- Presentations of groups
--
-- Selinger's Figure-8 presentation of the n-qubit Clifford operators
-- (arXiv:1310.6813), taken MOD SCALARS: the copy of
-- Examples.Groups.Clifford.Qubit.Selinger.Figure8 with the order-8
-- scalar ω quotiented out.
--
-- The scalars form the central subgroup ⟨ω⟩ ≅ ℤ/8, so the quotient is
-- presented by the same generators and the same relations plus ω = 1.
-- Adding that one relation is what "removing the scalars" means: by
-- applying direct consequences of ω = 1, we get the mod-scalar
-- version of Figure 8, oncretely:
--
--   * C4, becomes SHSHSH = 1.
--   * C1 (ω⁸ = 1) is dropped, so is the generator ω.
--   * The ω⁻¹ tails of C10 and C11 are dropped.
--   * Everything else — C2, C3, C5–C9, C12–C15, and the derived words
--     X = HSSH, Z = SS — is verbatim.
--
-- Note that S⁴ = 1 (C3) stays: S² = Z is a Pauli, not a scalar, so it
-- survives this quotient.  Only the further quotient by the Paulis gives
-- the phaseless S² = 1 of the symplectic presentation.
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
import Presentation.Base as PB

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Derived words: the Pauli operators X, Z
--
-- Neither ω nor ω⁻¹ is defined here.  ω named the scalar in Figure 8,
-- and modulo scalars there is nothing for it to name: C4 below sets the
-- word it stood for, (SH)³, to the identity, and says so directly.

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
  c2  : (₁₊ n) Sel,  H ^ 2 === ε
  c3  : (₁₊ n) Sel,  S ^ 4 === ε
  c4  : (₁₊ n) Sel,  SH ^ 3 === ε

  -- (c) n ≥ 2
  c5  : (₂₊ n) Sel,  CZ ^ 2 === ε
  c6  : (₂₊ n) Sel,  S ↓ • CZ === CZ • S ↓
  c7  : (₂₊ n) Sel,  S ↑ • CZ === CZ • S ↑
  c8  : (₂₊ n) Sel,  X ↓ • CZ === CZ • X ↓ • Z ↑
  c9  : (₂₊ n) Sel,  X ↑ • CZ === CZ • X ↑ • Z ↓

  -- C10 and C11 lose their trailing ω⁻¹.
  c10 : (₂₊ n) Sel,  CZ • H ↑ • CZ ===
                             SH ↑ • CZ • (S • H • S) ↑ • S ↓
  c11 : (₂₊ n) Sel,  CZ • H ↓ • CZ ===
                             SH ↓ • CZ • (S • H • S) ↓ • S ↑

  -- (d) n ≥ 3
  c12 : (₃₊ n) Sel,  CZ ↑ • CZ === CZ • CZ ↑
  c13 : (₃₊ n) Sel,  ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ === ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
  c14 : (₃₊ n) Sel,  (⊤⊥ ↑ • CZ ↓) ^ 3 === ε
  c15 : (₃₊ n) Sel,  (⊥⊤ ↓ • CZ ↑) ^ 3 === ε

------------------------------------------------------------------------
-- The full relation, with the structural rules srel/cong↑/comm₁/comm₂.

open Lift-Relation _Sel,_===_ public

infix 4 _CRel,_===_
_CRel,_===_ : (n : ℕ) → CRel n
_CRel,_===_ = _VRel,_===_

------------------------------------------------------------------------
-- Centrality of the scalar is free here
--
-- Figure 8 needs an axiom saying ω is central (Figure8.cω), because
-- there ω = (SH)³ is a derived word and nothing else makes it commute.
-- Modulo scalars that word is the identity (C4), so the same statement
-- is derivable, in four steps.  Nothing is lost by not assuming it.

SH³-central : (w : Word (Gen (₁₊ n))) →
              PB._≈_ ((₁₊ n) CRel,_===_) ((SH ^ 3) • w) (w • (SH ^ 3))
SH³-central w =
  PB.trans (PB.cong (PB.axiom (srel c4)) PB.refl)
    (PB.trans PB.left-unit
      (PB.trans (PB.sym PB.right-unit)
                (PB.cong PB.refl (PB.sym (PB.axiom (srel c4))))))

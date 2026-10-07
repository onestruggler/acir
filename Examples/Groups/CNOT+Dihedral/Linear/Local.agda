------------------------------------------------------------------------
-- Presentations of groups
--
-- CNOT and SWAP on two and three wires: the local identities of the
-- linear coset tower
--
-- The CNOTs on three wires are named by control and target (CNOT is
-- CX10, CNOT ↑ is CX21; the other four are conjugates by swaps).  The
-- identities below are the finitely many local facts the step lemmas
-- of Linear.Steps rest on: how a representative's gadget on the bottom
-- wires absorbs a bottom generator, and how it commutes with the
-- letters the level below emits.  Each is a derivation from R₄, R₅,
-- R₆ and the laws of the symmetry; the chains were found by a
-- breadth-first search over single rewrites and are written out in
-- full, every intermediate word being a regrouping or one rule
-- applied in context.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.Linear.Local where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₂₊ ; ₃₊)

open import Examples.Groups.CNOT+Dihedral.Syntactics
open import Examples.Groups.CNOT+Dihedral.Reasoning

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The CNOTs on three wires

CX01 : Circuit (₂₊ n)
CX01 = SWAP • CNOT • SWAP

CX12 CX20 CX02 : Circuit (₃₊ n)
CX12 = CX01 ↑
CX20 = SWAP ↑ • CNOT • SWAP ↑
CX02 = SWAP ↑ • CX01 • SWAP ↑

------------------------------------------------------------------------
-- The identities

-- CX01 is an involution.
CX01² : (₂₊ n) ⊢ CX01 • CX01 ≈ ε
CX01² {n} = begin
  CX01 • CX01
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • CNOT • (SWAP • SWAP) • CNOT • SWAP
    ≈⟨ back (SWAP) (back (CNOT) (front (CNOT • SWAP) (ax swap-order))) ⟩
  SWAP • CNOT • (ε) • CNOT • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • (CNOT • CNOT) • SWAP
    ≈⟨ back (SWAP) (front (SWAP) (ax R₄)) ⟩
  SWAP • (ε) • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP • SWAP)
    ≈⟨ ax swap-order ⟩
  (ε)
    ≈⟨ by-assoc Eq.refl ⟩
  ε ∎
  where open Width (₂₊ n)

-- R₅ read as a commutation.
R5a : (₂₊ n) ⊢ CNOT • SWAP ≈ CX01 • CNOT
R5a {n} = begin
  CNOT • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • (SWAP)
    ≈⟨ back (CNOT) (ax R₅) ⟩
  CNOT • (CNOT • SWAP • CNOT • SWAP • CNOT)
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT • CNOT) • SWAP • CNOT • SWAP • CNOT
    ≈⟨ front (SWAP • CNOT • SWAP • CNOT) (ax R₄) ⟩
  (ε) • SWAP • CNOT • SWAP • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CX01 • CNOT ∎
  where open Width (₂₊ n)

R5b : (₂₊ n) ⊢ SWAP • CNOT ≈ CNOT • CX01
R5b {n} = begin
  SWAP • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP) • CNOT
    ≈⟨ front (CNOT) (ax R₅) ⟩
  (CNOT • SWAP • CNOT • SWAP • CNOT) • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP • CNOT • SWAP • (CNOT • CNOT)
    ≈⟨ back (CNOT) (back (SWAP) (back (CNOT) (back (SWAP) (ax R₄)))) ⟩
  CNOT • SWAP • CNOT • SWAP • (ε)
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • CX01 ∎
  where open Width (₂₊ n)

C0e : (₂₊ n) ⊢ CX01 • CNOT ≈ CNOT • SWAP
C0e {n} = begin
  CX01 • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  (CX01 • CNOT)
    ≈⟨ sym (R5a) ⟩
  (CNOT • SWAP)
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP ∎
  where open Width (₂₊ n)

C0f : (₂₊ n) ⊢ CX01 • SWAP ≈ CNOT • CX01
C0f {n} = begin
  CX01 • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • (CNOT • SWAP) • SWAP
    ≈⟨ back (SWAP) (front (SWAP) (R5a)) ⟩
  SWAP • (CX01 • CNOT) • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP • SWAP) • CNOT • SWAP • CNOT • SWAP
    ≈⟨ front (CNOT • SWAP • CNOT • SWAP) (ax swap-order) ⟩
  (ε) • CNOT • SWAP • CNOT • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • CX01 ∎
  where open Width (₂₊ n)

-- CNOT₂₀ two ways.
N1 : (₃₊ n) ⊢ SWAP • CNOT ↑ • SWAP ≈ CX20
N1 {n} = begin
  SWAP • CNOT ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  (ε) • SWAP • CNOT ↑ • SWAP
    ≈⟨ front (SWAP • CNOT ↑ • SWAP) (sym (lift (ax swap-order))) ⟩
  (SWAP ↑ • SWAP ↑) • SWAP • CNOT ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • (SWAP ↑ • SWAP • CNOT ↑) • SWAP
    ≈⟨ back (SWAP ↑) (front (SWAP) (sym (ax swap-CNOT))) ⟩
  SWAP ↑ • (CNOT • SWAP ↑ • SWAP) • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • CNOT • SWAP ↑ • (SWAP • SWAP)
    ≈⟨ back (SWAP ↑) (back (CNOT) (back (SWAP ↑) (ax swap-order))) ⟩
  SWAP ↑ • CNOT • SWAP ↑ • (ε)
    ≈⟨ by-assoc Eq.refl ⟩
  CX20 ∎
  where open Width (₃₊ n)

-- CNOT₀₂ two ways.
N2 : (₃₊ n) ⊢ SWAP • CX12 • SWAP ≈ CX02
N2 {n} = begin
  SWAP • CX12 • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • SWAP ↑ • (ε) • CNOT ↑ • SWAP ↑ • SWAP
    ≈⟨ back (SWAP) (back (SWAP ↑) (front (CNOT ↑ • SWAP ↑ • SWAP) (sym (ax swap-order)))) ⟩
  SWAP • SWAP ↑ • (SWAP • SWAP) • CNOT ↑ • SWAP ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP • SWAP ↑ • SWAP) • SWAP • CNOT ↑ • SWAP ↑ • SWAP
    ≈⟨ front (SWAP • CNOT ↑ • SWAP ↑ • SWAP) (ax swap-braid) ⟩
  (SWAP ↑ • SWAP • SWAP ↑) • SWAP • CNOT ↑ • SWAP ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • SWAP • (SWAP ↑ • SWAP • CNOT ↑) • SWAP ↑ • SWAP
    ≈⟨ back (SWAP ↑) (back (SWAP) (front (SWAP ↑ • SWAP) (sym (ax swap-CNOT)))) ⟩
  SWAP ↑ • SWAP • (CNOT • SWAP ↑ • SWAP) • SWAP ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • SWAP • CNOT • (SWAP ↑ • SWAP • SWAP ↑) • SWAP
    ≈⟨ back (SWAP ↑) (back (SWAP) (back (CNOT) (front (SWAP) (sym (ax swap-braid))))) ⟩
  SWAP ↑ • SWAP • CNOT • (SWAP • SWAP ↑ • SWAP) • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • SWAP • CNOT • SWAP • SWAP ↑ • (SWAP • SWAP)
    ≈⟨ back (SWAP ↑) (back (SWAP) (back (CNOT) (back (SWAP) (back (SWAP ↑) (ax swap-order))))) ⟩
  SWAP ↑ • SWAP • CNOT • SWAP • SWAP ↑ • (ε)
    ≈⟨ by-assoc Eq.refl ⟩
  CX02 ∎
  where open Width (₃₊ n)

-- Shared control.
U1 : (₃₊ n) ⊢ CNOT • CX12 ≈ CX12 • CNOT
U1 {n} = begin
  CNOT • CX12
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP ↑ • (ε) • CNOT ↑ • SWAP ↑
    ≈⟨ back (CNOT) (back (SWAP ↑) (front (CNOT ↑ • SWAP ↑) (sym (ax R₄)))) ⟩
  CNOT • SWAP ↑ • (CNOT • CNOT) • CNOT ↑ • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP ↑ • CNOT • (ε) • CNOT • CNOT ↑ • SWAP ↑
    ≈⟨ back (CNOT) (back (SWAP ↑) (back (CNOT) (front (CNOT • CNOT ↑ • SWAP ↑) (sym (lift (ax R₄)))))) ⟩
  CNOT • SWAP ↑ • CNOT • (CNOT ↑ • CNOT ↑) • CNOT • CNOT ↑ • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP ↑ • CNOT • CNOT ↑ • (ε) • CNOT ↑ • CNOT • CNOT ↑ • SWAP ↑
    ≈⟨ back (CNOT) (back (SWAP ↑) (back (CNOT) (back (CNOT ↑) (front (CNOT ↑ • CNOT • CNOT ↑ • SWAP ↑) (sym (ax R₄)))))) ⟩
  CNOT • SWAP ↑ • CNOT • CNOT ↑ • (CNOT • CNOT) • CNOT ↑ • CNOT • CNOT ↑ • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP ↑ • CNOT • CNOT ↑ • CNOT • (CNOT • CNOT ↑ • CNOT • CNOT ↑) • SWAP ↑
    ≈⟨ back (CNOT) (back (SWAP ↑) (back (CNOT) (back (CNOT ↑) (back (CNOT) (front (SWAP ↑) (sym (ax R₆))))))) ⟩
  CNOT • SWAP ↑ • CNOT • CNOT ↑ • CNOT • (SWAP • CNOT ↑ • SWAP) • SWAP ↑
    ≈⟨ back (CNOT) (back (SWAP ↑) (back (CNOT) (back (CNOT ↑) (back (CNOT) (front (SWAP ↑) (N1)))))) ⟩
  CNOT • SWAP ↑ • CNOT • CNOT ↑ • CNOT • (CX20) • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP ↑ • CNOT • CNOT ↑ • CNOT • SWAP ↑ • CNOT • (SWAP ↑ • SWAP ↑)
    ≈⟨ back (CNOT) (back (SWAP ↑) (back (CNOT) (back (CNOT ↑) (back (CNOT) (back (SWAP ↑) (back (CNOT) (lift (ax swap-order)))))))) ⟩
  CNOT • SWAP ↑ • CNOT • CNOT ↑ • CNOT • SWAP ↑ • CNOT • (ε)
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP ↑ • CNOT • CNOT ↑ • CNOT • (ε) • SWAP ↑ • CNOT
    ≈⟨ back (CNOT) (back (SWAP ↑) (back (CNOT) (back (CNOT ↑) (back (CNOT) (front (SWAP ↑ • CNOT) (sym (lift (ax R₄)))))))) ⟩
  CNOT • SWAP ↑ • CNOT • CNOT ↑ • CNOT • (CNOT ↑ • CNOT ↑) • SWAP ↑ • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP ↑ • (CNOT • CNOT ↑ • CNOT • CNOT ↑) • CNOT ↑ • SWAP ↑ • CNOT
    ≈⟨ back (CNOT) (back (SWAP ↑) (front (CNOT ↑ • SWAP ↑ • CNOT) (sym (ax R₆)))) ⟩
  CNOT • SWAP ↑ • (SWAP • CNOT ↑ • SWAP) • CNOT ↑ • SWAP ↑ • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • (SWAP ↑ • SWAP • CNOT ↑) • SWAP • CNOT ↑ • SWAP ↑ • CNOT
    ≈⟨ back (CNOT) (front (SWAP • CNOT ↑ • SWAP ↑ • CNOT) (sym (ax swap-CNOT))) ⟩
  CNOT • (CNOT • SWAP ↑ • SWAP) • SWAP • CNOT ↑ • SWAP ↑ • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • CNOT • SWAP ↑ • (SWAP • SWAP) • CNOT ↑ • SWAP ↑ • CNOT
    ≈⟨ back (CNOT) (back (CNOT) (back (SWAP ↑) (front (CNOT ↑ • SWAP ↑ • CNOT) (ax swap-order)))) ⟩
  CNOT • CNOT • SWAP ↑ • (ε) • CNOT ↑ • SWAP ↑ • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT • CNOT) • SWAP ↑ • CNOT ↑ • SWAP ↑ • CNOT
    ≈⟨ front (SWAP ↑ • CNOT ↑ • SWAP ↑ • CNOT) (ax R₄) ⟩
  (ε) • SWAP ↑ • CNOT ↑ • SWAP ↑ • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CX12 • CNOT ∎
  where open Width (₃₊ n)

U2 : (₃₊ n) ⊢ SWAP • CX12 ≈ CX02 • SWAP
U2 {n} = begin
  SWAP • CX12
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • SWAP ↑ • CNOT ↑ • SWAP ↑ • (ε)
    ≈⟨ back (SWAP) (back (SWAP ↑) (back (CNOT ↑) (back (SWAP ↑) (sym (ax swap-order))))) ⟩
  SWAP • SWAP ↑ • CNOT ↑ • SWAP ↑ • (SWAP • SWAP)
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP • CX12 • SWAP) • SWAP
    ≈⟨ front (SWAP) (N2) ⟩
  (CX02) • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  CX02 • SWAP ∎
  where open Width (₃₊ n)

-- Shared target.
U3 : (₃₊ n) ⊢ CX01 • CNOT ↑ ≈ CNOT ↑ • CX01
U3 {n} = begin
  CX01 • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  (ε) • SWAP • CNOT • SWAP • CNOT ↑
    ≈⟨ front (SWAP • CNOT • SWAP • CNOT ↑) (sym (lift (ax R₄))) ⟩
  (CNOT ↑ • CNOT ↑) • SWAP • CNOT • SWAP • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • CNOT ↑ • SWAP • CNOT • SWAP • CNOT ↑ • (ε)
    ≈⟨ back (CNOT ↑) (back (CNOT ↑) (back (SWAP) (back (CNOT) (back (SWAP) (back (CNOT ↑) (sym (ax swap-order))))))) ⟩
  CNOT ↑ • CNOT ↑ • SWAP • CNOT • SWAP • CNOT ↑ • (SWAP • SWAP)
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • CNOT ↑ • SWAP • CNOT • (SWAP • CNOT ↑ • SWAP) • SWAP
    ≈⟨ back (CNOT ↑) (back (CNOT ↑) (back (SWAP) (back (CNOT) (front (SWAP) (ax R₆))))) ⟩
  CNOT ↑ • CNOT ↑ • SWAP • CNOT • (CNOT • CNOT ↑ • CNOT • CNOT ↑) • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • CNOT ↑ • SWAP • (CNOT • CNOT) • CNOT ↑ • CNOT • CNOT ↑ • SWAP
    ≈⟨ back (CNOT ↑) (back (CNOT ↑) (back (SWAP) (front (CNOT ↑ • CNOT • CNOT ↑ • SWAP) (ax R₄)))) ⟩
  CNOT ↑ • CNOT ↑ • SWAP • (ε) • CNOT ↑ • CNOT • CNOT ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • (ε) • CNOT ↑ • SWAP • CNOT ↑ • CNOT • CNOT ↑ • SWAP
    ≈⟨ back (CNOT ↑) (front (CNOT ↑ • SWAP • CNOT ↑ • CNOT • CNOT ↑ • SWAP) (sym (ax swap-order))) ⟩
  CNOT ↑ • (SWAP • SWAP) • CNOT ↑ • SWAP • CNOT ↑ • CNOT • CNOT ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • SWAP • (SWAP • CNOT ↑ • SWAP) • CNOT ↑ • CNOT • CNOT ↑ • SWAP
    ≈⟨ back (CNOT ↑) (back (SWAP) (front (CNOT ↑ • CNOT • CNOT ↑ • SWAP) (ax R₆))) ⟩
  CNOT ↑ • SWAP • (CNOT • CNOT ↑ • CNOT • CNOT ↑) • CNOT ↑ • CNOT • CNOT ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • SWAP • CNOT • CNOT ↑ • CNOT • (CNOT ↑ • CNOT ↑) • CNOT • CNOT ↑ • SWAP
    ≈⟨ back (CNOT ↑) (back (SWAP) (back (CNOT) (back (CNOT ↑) (back (CNOT) (front (CNOT • CNOT ↑ • SWAP) (lift (ax R₄))))))) ⟩
  CNOT ↑ • SWAP • CNOT • CNOT ↑ • CNOT • (ε) • CNOT • CNOT ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • SWAP • CNOT • CNOT ↑ • (CNOT • CNOT) • CNOT ↑ • SWAP
    ≈⟨ back (CNOT ↑) (back (SWAP) (back (CNOT) (back (CNOT ↑) (front (CNOT ↑ • SWAP) (ax R₄))))) ⟩
  CNOT ↑ • SWAP • CNOT • CNOT ↑ • (ε) • CNOT ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • SWAP • CNOT • (CNOT ↑ • CNOT ↑) • SWAP
    ≈⟨ back (CNOT ↑) (back (SWAP) (back (CNOT) (front (SWAP) (lift (ax R₄))))) ⟩
  CNOT ↑ • SWAP • CNOT • (ε) • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • CX01 ∎
  where open Width (₃₊ n)

U4 : (₃₊ n) ⊢ SWAP • CNOT ↑ ≈ CX20 • SWAP
U4 {n} = begin
  SWAP • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  (ε) • SWAP • CNOT ↑
    ≈⟨ front (SWAP • CNOT ↑) (sym (lift (ax swap-order))) ⟩
  (SWAP ↑ • SWAP ↑) • SWAP • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • (SWAP ↑ • SWAP • CNOT ↑)
    ≈⟨ back (SWAP ↑) (sym (ax swap-CNOT)) ⟩
  SWAP ↑ • (CNOT • SWAP ↑ • SWAP)
    ≈⟨ by-assoc Eq.refl ⟩
  CX20 • SWAP ∎
  where open Width (₃₊ n)

-- Naturality.
R1a : (₃₊ n) ⊢ SWAP • SWAP ↑ • CNOT ≈ CNOT ↑ • SWAP • SWAP ↑
R1a {n} = begin
  SWAP • SWAP ↑ • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • SWAP ↑ • CNOT • (ε)
    ≈⟨ back (SWAP) (back (SWAP ↑) (back (CNOT) (sym (lift (ax swap-order))))) ⟩
  SWAP • SWAP ↑ • CNOT • (SWAP ↑ • SWAP ↑)
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • (CX20) • SWAP ↑
    ≈⟨ back (SWAP) (front (SWAP ↑) (sym (N1))) ⟩
  SWAP • (SWAP • CNOT ↑ • SWAP) • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP • SWAP) • CNOT ↑ • SWAP • SWAP ↑
    ≈⟨ front (CNOT ↑ • SWAP • SWAP ↑) (ax swap-order) ⟩
  (ε) • CNOT ↑ • SWAP • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • SWAP • SWAP ↑ ∎
  where open Width (₃₊ n)

R1c : (₃₊ n) ⊢ SWAP • CNOT ↑ • CNOT ≈ (CNOT ↑ • CX01) • SWAP • CNOT ↑
R1c {n} = begin
  SWAP • CNOT ↑ • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • (ε) • CNOT ↑ • CNOT
    ≈⟨ back (SWAP) (front (CNOT ↑ • CNOT) (sym (ax R₄))) ⟩
  SWAP • (CNOT • CNOT) • CNOT ↑ • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • CNOT • CNOT • CNOT ↑ • CNOT • (ε)
    ≈⟨ back (SWAP) (back (CNOT) (back (CNOT) (back (CNOT ↑) (back (CNOT) (sym (lift (ax R₄))))))) ⟩
  SWAP • CNOT • CNOT • CNOT ↑ • CNOT • (CNOT ↑ • CNOT ↑)
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • CNOT • (CNOT • CNOT ↑ • CNOT • CNOT ↑) • CNOT ↑
    ≈⟨ back (SWAP) (back (CNOT) (front (CNOT ↑) (sym (ax R₆)))) ⟩
  SWAP • CNOT • (SWAP • CNOT ↑ • SWAP) • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  (CX01 • CNOT ↑) • SWAP • CNOT ↑
    ≈⟨ front (SWAP • CNOT ↑) (U3) ⟩
  (CNOT ↑ • CX01) • SWAP • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT ↑ • CX01) • SWAP • CNOT ↑ ∎
  where open Width (₃₊ n)

R1d : (₃₊ n) ⊢ SWAP • CNOT ↑ • SWAP ≈ SWAP ↑ • CNOT • SWAP ↑
R1d {n} = begin
  SWAP • CNOT ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP • CNOT ↑ • SWAP)
    ≈⟨ N1 ⟩
  (CX20)
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • CNOT • SWAP ↑ ∎
  where open Width (₃₊ n)

R1e : (₃₊ n) ⊢ CNOT • SWAP ↑ • CNOT ≈ (SWAP ↑ • CNOT ↑) • CNOT • CNOT ↑
R1e {n} = begin
  CNOT • SWAP ↑ • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP ↑ • (ε) • CNOT
    ≈⟨ back (CNOT) (back (SWAP ↑) (front (CNOT) (sym (ax swap-order)))) ⟩
  CNOT • SWAP ↑ • (SWAP • SWAP) • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP ↑ • SWAP • SWAP • CNOT • (ε)
    ≈⟨ back (CNOT) (back (SWAP ↑) (back (SWAP) (back (SWAP) (back (CNOT) (sym (ax swap-order)))))) ⟩
  CNOT • SWAP ↑ • SWAP • SWAP • CNOT • (SWAP • SWAP)
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT • SWAP ↑ • SWAP) • SWAP • CNOT • SWAP • SWAP
    ≈⟨ front (SWAP • CNOT • SWAP • SWAP) (ax swap-CNOT) ⟩
  (SWAP ↑ • SWAP • CNOT ↑) • SWAP • CNOT • SWAP • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • SWAP • CNOT ↑ • SWAP • CNOT • SWAP • SWAP • (ε)
    ≈⟨ back (SWAP ↑) (back (SWAP) (back (CNOT ↑) (back (SWAP) (back (CNOT) (back (SWAP) (back (SWAP) (sym (lift (ax R₄))))))))) ⟩
  SWAP ↑ • SWAP • CNOT ↑ • SWAP • CNOT • SWAP • SWAP • (CNOT ↑ • CNOT ↑)
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • SWAP • ((CNOT ↑ • CX01) • SWAP • CNOT ↑) • CNOT ↑
    ≈⟨ back (SWAP ↑) (back (SWAP) (front (CNOT ↑) (sym (R1c)))) ⟩
  SWAP ↑ • SWAP • (SWAP • CNOT ↑ • CNOT) • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • (SWAP • SWAP) • CNOT ↑ • CNOT • CNOT ↑
    ≈⟨ back (SWAP ↑) (front (CNOT ↑ • CNOT • CNOT ↑) (ax swap-order)) ⟩
  SWAP ↑ • (ε) • CNOT ↑ • CNOT • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP ↑ • CNOT ↑) • CNOT • CNOT ↑ ∎
  where open Width (₃₊ n)

R1g : (₃₊ n) ⊢ CNOT • CNOT ↑ • CNOT ≈ (CNOT ↑ • SWAP ↑) • CNOT • SWAP ↑
R1g {n} = begin
  CNOT • CNOT ↑ • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  (ε) • CNOT • CNOT ↑ • CNOT
    ≈⟨ front (CNOT • CNOT ↑ • CNOT) (sym (lift (ax R₄))) ⟩
  (CNOT ↑ • CNOT ↑) • CNOT • CNOT ↑ • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • (ε) • CNOT ↑ • CNOT • CNOT ↑ • CNOT
    ≈⟨ back (CNOT ↑) (front (CNOT ↑ • CNOT • CNOT ↑ • CNOT) (sym (lift (ax swap-order)))) ⟩
  CNOT ↑ • (SWAP ↑ • SWAP ↑) • CNOT ↑ • CNOT • CNOT ↑ • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • SWAP ↑ • ((SWAP ↑ • CNOT ↑) • CNOT • CNOT ↑) • CNOT
    ≈⟨ back (CNOT ↑) (back (SWAP ↑) (front (CNOT) (sym (R1e)))) ⟩
  CNOT ↑ • SWAP ↑ • (CNOT • SWAP ↑ • CNOT) • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • SWAP ↑ • CNOT • SWAP ↑ • (CNOT • CNOT)
    ≈⟨ back (CNOT ↑) (back (SWAP ↑) (back (CNOT) (back (SWAP ↑) (ax R₄)))) ⟩
  CNOT ↑ • SWAP ↑ • CNOT • SWAP ↑ • (ε)
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT ↑ • SWAP ↑) • CNOT • SWAP ↑ ∎
  where open Width (₃₊ n)

R1h : (₃₊ n) ⊢ CNOT • CNOT ↑ • SWAP ≈ (CNOT ↑ • CX01) • CNOT • CNOT ↑
R1h {n} = begin
  CNOT • CNOT ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  (ε) • CNOT • CNOT ↑ • SWAP
    ≈⟨ front (CNOT • CNOT ↑ • SWAP) (sym (lift (ax R₄))) ⟩
  (CNOT ↑ • CNOT ↑) • CNOT • CNOT ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • (ε) • CNOT ↑ • CNOT • CNOT ↑ • SWAP
    ≈⟨ back (CNOT ↑) (front (CNOT ↑ • CNOT • CNOT ↑ • SWAP) (sym (ax R₄))) ⟩
  CNOT ↑ • (CNOT • CNOT) • CNOT ↑ • CNOT • CNOT ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • CNOT • (CNOT • CNOT ↑ • CNOT • CNOT ↑) • SWAP
    ≈⟨ back (CNOT ↑) (back (CNOT) (front (SWAP) (sym (ax R₆)))) ⟩
  CNOT ↑ • CNOT • (SWAP • CNOT ↑ • SWAP) • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • (CNOT • SWAP) • CNOT ↑ • SWAP • SWAP
    ≈⟨ back (CNOT ↑) (front (CNOT ↑ • SWAP • SWAP) (R5a)) ⟩
  CNOT ↑ • (CX01 • CNOT) • CNOT ↑ • SWAP • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • SWAP • CNOT • SWAP • CNOT • CNOT ↑ • (SWAP • SWAP)
    ≈⟨ back (CNOT ↑) (back (SWAP) (back (CNOT) (back (SWAP) (back (CNOT) (back (CNOT ↑) (ax swap-order)))))) ⟩
  CNOT ↑ • SWAP • CNOT • SWAP • CNOT • CNOT ↑ • (ε)
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT ↑ • CX01) • CNOT • CNOT ↑ ∎
  where open Width (₃₊ n)

C1c : (₃₊ n) ⊢ SWAP • CX12 • CNOT ≈ CNOT • CX01 • CX12
C1c {n} = begin
  SWAP • CX12 • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • (CX12 • CNOT)
    ≈⟨ back (SWAP) (sym (U1)) ⟩
  SWAP • (CNOT • CX12)
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP • CNOT) • SWAP ↑ • CNOT ↑ • SWAP ↑
    ≈⟨ front (SWAP ↑ • CNOT ↑ • SWAP ↑) (R5b) ⟩
  (CNOT • CX01) • SWAP ↑ • CNOT ↑ • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • CX01 • CX12 ∎
  where open Width (₃₊ n)

C1d : (₃₊ n) ⊢ SWAP • CX12 • SWAP ≈ SWAP ↑ • CX01 • SWAP ↑
C1d {n} = begin
  SWAP • CX12 • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP • CX12 • SWAP)
    ≈⟨ N2 ⟩
  (CX02)
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • CX01 • SWAP ↑ ∎
  where open Width (₃₊ n)

C1e : (₃₊ n) ⊢ CX01 • SWAP ↑ • CNOT ≈ (CNOT • CNOT ↑ • CNOT) • CX01 • SWAP ↑
C1e {n} = begin
  CX01 • SWAP ↑ • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP • CNOT) • SWAP • SWAP ↑ • CNOT
    ≈⟨ front (SWAP • SWAP ↑ • CNOT) (R5b) ⟩
  (CNOT • CX01) • SWAP • SWAP ↑ • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP • CNOT • SWAP • (SWAP • SWAP ↑ • CNOT)
    ≈⟨ back (CNOT) (back (SWAP) (back (CNOT) (back (SWAP) (R1a)))) ⟩
  CNOT • SWAP • CNOT • SWAP • (CNOT ↑ • SWAP • SWAP ↑)
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • (CX01 • CNOT ↑) • SWAP • SWAP ↑
    ≈⟨ back (CNOT) (front (SWAP • SWAP ↑) (U3)) ⟩
  CNOT • (CNOT ↑ • CX01) • SWAP • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • CNOT ↑ • (CX01 • SWAP) • SWAP ↑
    ≈⟨ back (CNOT) (back (CNOT ↑) (front (SWAP ↑) (C0f))) ⟩
  CNOT • CNOT ↑ • (CNOT • CX01) • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT • CNOT ↑ • CNOT) • CX01 • SWAP ↑ ∎
  where open Width (₃₊ n)

C1f : (₃₊ n) ⊢ CX01 • SWAP ↑ • SWAP ≈ SWAP ↑ • SWAP • CX12
C1f {n} = begin
  CX01 • SWAP ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  (ε) • SWAP • CNOT • SWAP • SWAP ↑ • SWAP
    ≈⟨ front (SWAP • CNOT • SWAP • SWAP ↑ • SWAP) (sym (lift (ax swap-order))) ⟩
  (SWAP ↑ • SWAP ↑) • SWAP • CNOT • SWAP • SWAP ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • (CX02 • SWAP)
    ≈⟨ back (SWAP ↑) (sym (U2)) ⟩
  SWAP ↑ • (SWAP • CX12)
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • SWAP • CX12 ∎
  where open Width (₃₊ n)

C1g : (₃₊ n) ⊢ CX01 • CX12 • CNOT ≈ CNOT • SWAP • CX12
C1g {n} = begin
  CX01 • CX12 • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • CNOT • SWAP • (CX12 • CNOT)
    ≈⟨ back (SWAP) (back (CNOT) (back (SWAP) (sym (U1)))) ⟩
  SWAP • CNOT • SWAP • (CNOT • CX12)
    ≈⟨ by-assoc Eq.refl ⟩
  (CX01 • CNOT) • SWAP ↑ • CNOT ↑ • SWAP ↑
    ≈⟨ front (SWAP ↑ • CNOT ↑ • SWAP ↑) (sym (R5a)) ⟩
  (CNOT • SWAP) • SWAP ↑ • CNOT ↑ • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP • CX12 ∎
  where open Width (₃₊ n)

C1h : (₃₊ n) ⊢ CX01 • CX12 • SWAP ≈ (CNOT ↑ • SWAP ↑ • CNOT ↑ • CNOT) • CX01 • CX12
C1h {n} = begin
  CX01 • CX12 • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • CNOT • (SWAP • CX12 • SWAP)
    ≈⟨ back (SWAP) (back (CNOT) (N2)) ⟩
  SWAP • CNOT • (CX02)
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • (CNOT • SWAP ↑ • SWAP) • CNOT • SWAP • SWAP ↑
    ≈⟨ back (SWAP) (front (CNOT • SWAP • SWAP ↑) (ax swap-CNOT)) ⟩
  SWAP • (SWAP ↑ • SWAP • CNOT ↑) • CNOT • SWAP • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • SWAP ↑ • (SWAP) • CNOT ↑ • CNOT • SWAP • SWAP ↑
    ≈⟨ back (SWAP) (back (SWAP ↑) (front (CNOT ↑ • CNOT • SWAP • SWAP ↑) (ax R₅))) ⟩
  SWAP • SWAP ↑ • (CNOT • SWAP • CNOT • SWAP • CNOT) • CNOT ↑ • CNOT • SWAP • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP • SWAP ↑ • CNOT) • SWAP • CNOT • SWAP • CNOT • CNOT ↑ • CNOT • SWAP • SWAP ↑
    ≈⟨ front (SWAP • CNOT • SWAP • CNOT • CNOT ↑ • CNOT • SWAP • SWAP ↑) (R1a) ⟩
  (CNOT ↑ • SWAP • SWAP ↑) • SWAP • CNOT • SWAP • CNOT • CNOT ↑ • CNOT • SWAP • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • SWAP • SWAP ↑ • SWAP • CNOT • SWAP • (CNOT • CNOT ↑ • CNOT) • SWAP • SWAP ↑
    ≈⟨ back (CNOT ↑) (back (SWAP) (back (SWAP ↑) (back (SWAP) (back (CNOT) (back (SWAP) (front (SWAP • SWAP ↑) (R1g))))))) ⟩
  CNOT ↑ • SWAP • SWAP ↑ • SWAP • CNOT • SWAP • ((CNOT ↑ • SWAP ↑) • CNOT • SWAP ↑) • SWAP • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • SWAP • SWAP ↑ • SWAP • CNOT • SWAP • CNOT ↑ • (CX20 • SWAP) • SWAP ↑
    ≈⟨ back (CNOT ↑) (back (SWAP) (back (SWAP ↑) (back (SWAP) (back (CNOT) (back (SWAP) (back (CNOT ↑) (front (SWAP ↑) (sym (U4))))))))) ⟩
  CNOT ↑ • SWAP • SWAP ↑ • SWAP • CNOT • SWAP • CNOT ↑ • (SWAP • CNOT ↑) • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • SWAP • SWAP ↑ • SWAP • CNOT • (SWAP • CNOT ↑ • SWAP) • CNOT ↑ • SWAP ↑
    ≈⟨ back (CNOT ↑) (back (SWAP) (back (SWAP ↑) (back (SWAP) (back (CNOT) (front (CNOT ↑ • SWAP ↑) (N1)))))) ⟩
  CNOT ↑ • SWAP • SWAP ↑ • SWAP • CNOT • (CX20) • CNOT ↑ • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • (SWAP • SWAP ↑ • SWAP) • CNOT • SWAP ↑ • CNOT • SWAP ↑ • CNOT ↑ • SWAP ↑
    ≈⟨ back (CNOT ↑) (front (CNOT • SWAP ↑ • CNOT • SWAP ↑ • CNOT ↑ • SWAP ↑) (ax swap-braid)) ⟩
  CNOT ↑ • (SWAP ↑ • SWAP • SWAP ↑) • CNOT • SWAP ↑ • CNOT • SWAP ↑ • CNOT ↑ • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • SWAP ↑ • SWAP • (CX20) • CNOT • SWAP ↑ • CNOT ↑ • SWAP ↑
    ≈⟨ back (CNOT ↑) (back (SWAP ↑) (back (SWAP) (front (CNOT • SWAP ↑ • CNOT ↑ • SWAP ↑) (sym (N1))))) ⟩
  CNOT ↑ • SWAP ↑ • SWAP • (SWAP • CNOT ↑ • SWAP) • CNOT • SWAP ↑ • CNOT ↑ • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • SWAP ↑ • SWAP • SWAP • CNOT ↑ • (SWAP • CNOT) • SWAP ↑ • CNOT ↑ • SWAP ↑
    ≈⟨ back (CNOT ↑) (back (SWAP ↑) (back (SWAP) (back (SWAP) (back (CNOT ↑) (front (SWAP ↑ • CNOT ↑ • SWAP ↑) (R5b)))))) ⟩
  CNOT ↑ • SWAP ↑ • SWAP • SWAP • CNOT ↑ • (CNOT • CX01) • SWAP ↑ • CNOT ↑ • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • SWAP ↑ • (SWAP • SWAP) • CNOT ↑ • CNOT • SWAP • CNOT • SWAP • SWAP ↑ • CNOT ↑ • SWAP ↑
    ≈⟨ back (CNOT ↑) (back (SWAP ↑) (front (CNOT ↑ • CNOT • SWAP • CNOT • SWAP • SWAP ↑ • CNOT ↑ • SWAP ↑) (ax swap-order))) ⟩
  CNOT ↑ • SWAP ↑ • (ε) • CNOT ↑ • CNOT • SWAP • CNOT • SWAP • SWAP ↑ • CNOT ↑ • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT ↑ • SWAP ↑ • CNOT ↑ • CNOT) • CX01 • CX12 ∎
  where open Width (₃₊ n)

N1a : (₃₊ n) ⊢ CX01 • SWAP ↑ • CX01 ≈ (CNOT ↑ • SWAP ↑) • CX01 • CX12
N1a {n} = begin
  CX01 • SWAP ↑ • CX01
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • CNOT • SWAP • SWAP ↑ • (ε) • SWAP • CNOT • SWAP
    ≈⟨ back (SWAP) (back (CNOT) (back (SWAP) (back (SWAP ↑) (front (SWAP • CNOT • SWAP) (sym (ax R₄)))))) ⟩
  SWAP • CNOT • SWAP • SWAP ↑ • (CNOT • CNOT) • SWAP • CNOT • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • CNOT • SWAP • SWAP ↑ • CNOT • (CNOT • CX01)
    ≈⟨ back (SWAP) (back (CNOT) (back (SWAP) (back (SWAP ↑) (back (CNOT) (sym (R5b)))))) ⟩
  SWAP • CNOT • SWAP • SWAP ↑ • CNOT • (SWAP • CNOT)
    ≈⟨ by-assoc Eq.refl ⟩
  (CX01 • SWAP ↑ • CNOT) • SWAP • CNOT
    ≈⟨ front (SWAP • CNOT) (C1e) ⟩
  ((CNOT • CNOT ↑ • CNOT) • CX01 • SWAP ↑) • SWAP • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT • CNOT ↑ • CNOT) • SWAP • CNOT • SWAP • SWAP ↑ • SWAP • CNOT
    ≈⟨ front (SWAP • CNOT • SWAP • SWAP ↑ • SWAP • CNOT) (R1g) ⟩
  ((CNOT ↑ • SWAP ↑) • CNOT • SWAP ↑) • SWAP • CNOT • SWAP • SWAP ↑ • SWAP • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • SWAP ↑ • CNOT • (CX02 • SWAP) • CNOT
    ≈⟨ back (CNOT ↑) (back (SWAP ↑) (back (CNOT) (front (CNOT) (sym (U2))))) ⟩
  CNOT ↑ • SWAP ↑ • CNOT • (SWAP • CX12) • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • SWAP ↑ • CNOT • (SWAP • CX12 • CNOT)
    ≈⟨ back (CNOT ↑) (back (SWAP ↑) (back (CNOT) (C1c))) ⟩
  CNOT ↑ • SWAP ↑ • CNOT • (CNOT • CX01 • CX12)
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • SWAP ↑ • (CNOT • CNOT) • SWAP • CNOT • SWAP • SWAP ↑ • CNOT ↑ • SWAP ↑
    ≈⟨ back (CNOT ↑) (back (SWAP ↑) (front (SWAP • CNOT • SWAP • SWAP ↑ • CNOT ↑ • SWAP ↑) (ax R₄))) ⟩
  CNOT ↑ • SWAP ↑ • (ε) • SWAP • CNOT • SWAP • SWAP ↑ • CNOT ↑ • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT ↑ • SWAP ↑) • CX01 • CX12 ∎
  where open Width (₃₊ n)

N1b : (₃₊ n) ⊢ CX01 • CX12 • CX01 ≈ (SWAP ↑ • CNOT ↑) • CX01 • SWAP ↑
N1b {n} = begin
  CX01 • CX12 • CX01
    ≈⟨ by-assoc Eq.refl ⟩
  (ε) • SWAP • CNOT • SWAP • SWAP ↑ • CNOT ↑ • SWAP ↑ • SWAP • CNOT • SWAP
    ≈⟨ front (SWAP • CNOT • SWAP • SWAP ↑ • CNOT ↑ • SWAP ↑ • SWAP • CNOT • SWAP) (sym (lift (ax swap-order))) ⟩
  (SWAP ↑ • SWAP ↑) • SWAP • CNOT • SWAP • SWAP ↑ • CNOT ↑ • SWAP ↑ • SWAP • CNOT • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • (ε) • SWAP ↑ • SWAP • CNOT • SWAP • SWAP ↑ • CNOT ↑ • SWAP ↑ • SWAP • CNOT • SWAP
    ≈⟨ back (SWAP ↑) (front (SWAP ↑ • SWAP • CNOT • SWAP • SWAP ↑ • CNOT ↑ • SWAP ↑ • SWAP • CNOT • SWAP) (sym (lift (ax R₄)))) ⟩
  SWAP ↑ • (CNOT ↑ • CNOT ↑) • SWAP ↑ • SWAP • CNOT • SWAP • SWAP ↑ • CNOT ↑ • SWAP ↑ • SWAP • CNOT • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • CNOT ↑ • ((CNOT ↑ • SWAP ↑) • CX01 • CX12) • SWAP • CNOT • SWAP
    ≈⟨ back (SWAP ↑) (back (CNOT ↑) (front (SWAP • CNOT • SWAP) (sym (N1a)))) ⟩
  SWAP ↑ • CNOT ↑ • (CX01 • SWAP ↑ • CX01) • SWAP • CNOT • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • CNOT ↑ • SWAP • CNOT • SWAP • SWAP ↑ • (CX01 • CX01)
    ≈⟨ back (SWAP ↑) (back (CNOT ↑) (back (SWAP) (back (CNOT) (back (SWAP) (back (SWAP ↑) (CX01²)))))) ⟩
  SWAP ↑ • CNOT ↑ • SWAP • CNOT • SWAP • SWAP ↑ • (ε)
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP ↑ • CNOT ↑) • CX01 • SWAP ↑ ∎
  where open Width (₃₊ n)

------------------------------------------------------------------------
-- Presentations of groups
--
-- X past CNOT and SWAP: the local identities of the X column
--
-- An X on the target of a CNOT commutes with it, one on the control
-- copies itself onto the target, and a swap exchanges the wires of the
-- X's in front of it.  Derivations from R₁, R₂, R₃, R₄, the naturality
-- of the swap for X and the bifunctorial law, found by a breadth-first
-- search over single rewrites.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.LocalX where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₂₊)

open import Examples.Groups.CNOT+Dihedral.Syntactics
open import Examples.Groups.CNOT+Dihedral.Reasoning

private
  variable
    n : ℕ

-- X on the target.
CNOT-X : (₂₊ n) ⊢ CNOT • X ≈ X • CNOT
CNOT-X {n} = begin
  CNOT • X
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • (X)
    ≈⟨ back (CNOT) (sym (ax R₂)) ⟩
  CNOT • (CNOT • X • CNOT)
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT • CNOT) • X • CNOT
    ≈⟨ front (X • CNOT) (ax R₄) ⟩
  (ε) • X • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  X • CNOT ∎
  where open Width (₂₊ n)

-- X on the control.
CNOT-X↑ : (₂₊ n) ⊢ CNOT • X ↑ ≈ X • X ↑ • CNOT
CNOT-X↑ {n} = begin
  CNOT • X ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • X ↑ • (ε)
    ≈⟨ back (CNOT) (back (X ↑) (sym (ax R₄))) ⟩
  CNOT • X ↑ • (CNOT • CNOT)
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT • X ↑ • CNOT) • CNOT
    ≈⟨ front (CNOT) (ax R₃) ⟩
  (X ↑ • X) • CNOT
    ≈⟨ front (CNOT) (ax' (comm₁ X-gate X-gen)) ⟩
  (X • X ↑) • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  X • X ↑ • CNOT ∎
  where open Width (₂₊ n)

CNOT-XX↑ : (₂₊ n) ⊢ CNOT • X • X ↑ ≈ X ↑ • CNOT
CNOT-XX↑ {n} = begin
  CNOT • X • X ↑
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT • X) • X ↑
    ≈⟨ front (X ↑) (CNOT-X) ⟩
  (X • CNOT) • X ↑
    ≈⟨ by-assoc Eq.refl ⟩
  X • (CNOT • X ↑)
    ≈⟨ back (X) (CNOT-X↑) ⟩
  X • (X • X ↑ • CNOT)
    ≈⟨ by-assoc Eq.refl ⟩
  (X • X) • X ↑ • CNOT
    ≈⟨ front (X ↑ • CNOT) (ax R₁) ⟩
  (ε) • X ↑ • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  X ↑ • CNOT ∎
  where open Width (₂₊ n)

-- X past a swap.
SWAP-X : (₂₊ n) ⊢ SWAP • X ≈ X ↑ • SWAP
SWAP-X {n} = begin
  SWAP • X
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • X • (ε)
    ≈⟨ back (SWAP) (back (X) (sym (ax swap-order))) ⟩
  SWAP • X • (SWAP • SWAP)
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • (X • SWAP) • SWAP
    ≈⟨ back (SWAP) (front (SWAP) (ax swap-X)) ⟩
  SWAP • (SWAP • X ↑) • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP • SWAP) • X ↑ • SWAP
    ≈⟨ front (X ↑ • SWAP) (ax swap-order) ⟩
  (ε) • X ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  X ↑ • SWAP ∎
  where open Width (₂₊ n)

SWAP-X↑ : (₂₊ n) ⊢ SWAP • X ↑ ≈ X • SWAP
SWAP-X↑ {n} = begin
  SWAP • X ↑
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP • X ↑)
    ≈⟨ sym (ax swap-X) ⟩
  (X • SWAP)
    ≈⟨ by-assoc Eq.refl ⟩
  X • SWAP ∎
  where open Width (₂₊ n)

SWAP-XX↑ : (₂₊ n) ⊢ SWAP • X • X ↑ ≈ X • X ↑ • SWAP
SWAP-XX↑ {n} = begin
  SWAP • X • X ↑
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • (X • X ↑)
    ≈⟨ back (SWAP) (sym (ax' (comm₁ X-gate X-gen))) ⟩
  SWAP • (X ↑ • X)
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP • X ↑) • X
    ≈⟨ front (X) (sym (ax swap-X)) ⟩
  (X • SWAP) • X
    ≈⟨ by-assoc Eq.refl ⟩
  X • (SWAP • X)
    ≈⟨ back (X) (SWAP-X) ⟩
  X • (X ↑ • SWAP)
    ≈⟨ by-assoc Eq.refl ⟩
  X • X ↑ • SWAP ∎
  where open Width (₂₊ n)

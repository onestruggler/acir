------------------------------------------------------------------------
-- Presentations of groups
--
-- T, CNOT and SWAP on two wires: the local identities of the phase
-- gates
--
-- T on the control of a CNOT commutes with it, T commutes with U, and
-- conjugating T by a swap moves it up a wire.  Derivations from R₄,
-- R₅, R₁₂, the naturality of the swap for T and the bifunctorial law,
-- found by a breadth-first search over single rewrites.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.Diagonal.LocalT where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊)

open import Examples.Groups.CNOT+Dihedral.Syntactics
open import Examples.Groups.CNOT+Dihedral.Reasoning
open import Examples.Groups.CNOT+Dihedral.Linear.Local using (CX01)

private
  variable
    n : ℕ

-- Conjugating T by a swap moves it up.
SWAP-T-SWAP : (₂₊ n) ⊢ SWAP • T • SWAP ≈ T ↑
SWAP-T-SWAP {n} = begin
  SWAP • T • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • (T • SWAP)
    ≈⟨ back (SWAP) (ax swap-T) ⟩
  SWAP • (SWAP • T ↑)
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP • SWAP) • T ↑
    ≈⟨ front (T ↑) (ax swap-order) ⟩
  (ε) • T ↑
    ≈⟨ by-assoc Eq.refl ⟩
  T ↑ ∎
  where open Width (₂₊ n)

-- T on the control.
T-CX01 : (₂₊ n) ⊢ T • CX01 ≈ CX01 • T
T-CX01 {n} = begin
  T • CX01
    ≈⟨ by-assoc Eq.refl ⟩
  (T • SWAP) • CNOT • SWAP
    ≈⟨ front (CNOT • SWAP) (ax swap-T) ⟩
  (SWAP • T ↑) • CNOT • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • (T ↑) • CNOT • SWAP
    ≈⟨ back (SWAP) (front (CNOT • SWAP) (sym (ax R₁₂))) ⟩
  SWAP • (CNOT • T ↑ • CNOT) • CNOT • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • CNOT • (T ↑) • CNOT • CNOT • SWAP
    ≈⟨ back (SWAP) (back (CNOT) (front (CNOT • CNOT • SWAP) (sym (SWAP-T-SWAP)))) ⟩
  SWAP • CNOT • (SWAP • T • SWAP) • CNOT • CNOT • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • CNOT • SWAP • T • SWAP • (CNOT • CNOT) • SWAP
    ≈⟨ back (SWAP) (back (CNOT) (back (SWAP) (back (T) (back (SWAP) (front (SWAP) (ax R₄)))))) ⟩
  SWAP • CNOT • SWAP • T • SWAP • (ε) • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • CNOT • SWAP • T • (SWAP • SWAP)
    ≈⟨ back (SWAP) (back (CNOT) (back (SWAP) (back (T) (ax swap-order)))) ⟩
  SWAP • CNOT • SWAP • T • (ε)
    ≈⟨ by-assoc Eq.refl ⟩
  CX01 • T ∎
  where open Width (₂₊ n)

-- T and U commute.
T-U : (₂₊ n) ⊢ T • U ≈ U • T
T-U {n} = begin
  T • U
    ≈⟨ by-assoc Eq.refl ⟩
  T • (ε) • CNOT • T • CNOT
    ≈⟨ back (T) (front (CNOT • T • CNOT) (sym (ax swap-order))) ⟩
  T • (SWAP • SWAP) • CNOT • T • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  T • SWAP • (SWAP) • CNOT • T • CNOT
    ≈⟨ back (T) (back (SWAP) (front (CNOT • T • CNOT) (ax R₅))) ⟩
  T • SWAP • (CNOT • SWAP • CNOT • SWAP • CNOT) • CNOT • T • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  T • SWAP • CNOT • SWAP • CNOT • SWAP • (CNOT • CNOT) • T • CNOT
    ≈⟨ back (T) (back (SWAP) (back (CNOT) (back (SWAP) (back (CNOT) (back (SWAP) (front (T • CNOT) (ax R₄))))))) ⟩
  T • SWAP • CNOT • SWAP • CNOT • SWAP • (ε) • T • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  (T • SWAP) • CNOT • SWAP • CNOT • SWAP • T • CNOT
    ≈⟨ front (CNOT • SWAP • CNOT • SWAP • T • CNOT) (ax swap-T) ⟩
  (SWAP • T ↑) • CNOT • SWAP • CNOT • SWAP • T • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP) • T ↑ • CNOT • SWAP • CNOT • SWAP • T • CNOT
    ≈⟨ front (T ↑ • CNOT • SWAP • CNOT • SWAP • T • CNOT) (ax R₅) ⟩
  (CNOT • SWAP • CNOT • SWAP • CNOT) • T ↑ • CNOT • SWAP • CNOT • SWAP • T • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP • CNOT • SWAP • (CNOT • T ↑ • CNOT) • SWAP • CNOT • SWAP • T • CNOT
    ≈⟨ back (CNOT) (back (SWAP) (back (CNOT) (back (SWAP) (front (SWAP • CNOT • SWAP • T • CNOT) (ax R₁₂))))) ⟩
  CNOT • SWAP • CNOT • SWAP • (T ↑) • SWAP • CNOT • SWAP • T • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP • CNOT • SWAP • T ↑ • (CX01 • T) • CNOT
    ≈⟨ back (CNOT) (back (SWAP) (back (CNOT) (back (SWAP) (back (T ↑) (front (CNOT) (sym (T-CX01))))))) ⟩
  CNOT • SWAP • CNOT • SWAP • T ↑ • (T • CX01) • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP • CNOT • SWAP • (T ↑ • T) • SWAP • CNOT • SWAP • CNOT
    ≈⟨ back (CNOT) (back (SWAP) (back (CNOT) (back (SWAP) (front (SWAP • CNOT • SWAP • CNOT) (ax' (comm₁ T-gate T-gen)))))) ⟩
  CNOT • SWAP • CNOT • SWAP • (T • T ↑) • SWAP • CNOT • SWAP • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP • CNOT • SWAP • T • (T ↑) • SWAP • CNOT • SWAP • CNOT
    ≈⟨ back (CNOT) (back (SWAP) (back (CNOT) (back (SWAP) (back (T) (front (SWAP • CNOT • SWAP • CNOT) (sym (ax R₁₂))))))) ⟩
  CNOT • SWAP • CNOT • SWAP • T • (CNOT • T ↑ • CNOT) • SWAP • CNOT • SWAP • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP • CNOT • SWAP • T • CNOT • T ↑ • (CNOT • SWAP • CNOT • SWAP • CNOT)
    ≈⟨ back (CNOT) (back (SWAP) (back (CNOT) (back (SWAP) (back (T) (back (CNOT) (back (T ↑) (sym (ax R₅)))))))) ⟩
  CNOT • SWAP • CNOT • SWAP • T • CNOT • T ↑ • (SWAP)
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • (CX01 • T) • CNOT • T ↑ • SWAP
    ≈⟨ back (CNOT) (front (CNOT • T ↑ • SWAP) (sym (T-CX01))) ⟩
  CNOT • (T • CX01) • CNOT • T ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • T • (ε) • SWAP • CNOT • SWAP • CNOT • T ↑ • SWAP
    ≈⟨ back (CNOT) (back (T) (front (SWAP • CNOT • SWAP • CNOT • T ↑ • SWAP) (sym (ax R₄)))) ⟩
  CNOT • T • (CNOT • CNOT) • SWAP • CNOT • SWAP • CNOT • T ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • T • CNOT • (CNOT • SWAP • CNOT • SWAP • CNOT) • T ↑ • SWAP
    ≈⟨ back (CNOT) (back (T) (back (CNOT) (front (T ↑ • SWAP) (sym (ax R₅))))) ⟩
  CNOT • T • CNOT • (SWAP) • T ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • T • CNOT • (SWAP • T ↑) • SWAP
    ≈⟨ back (CNOT) (back (T) (back (CNOT) (front (SWAP) (sym (ax swap-T))))) ⟩
  CNOT • T • CNOT • (T • SWAP) • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • T • CNOT • T • (SWAP • SWAP)
    ≈⟨ back (CNOT) (back (T) (back (CNOT) (back (T) (ax swap-order)))) ⟩
  CNOT • T • CNOT • T • (ε)
    ≈⟨ by-assoc Eq.refl ⟩
  U • T ∎
  where open Width (₂₊ n)

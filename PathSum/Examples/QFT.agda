------------------------------------------------------------------------
-- Presentations of groups
--
-- Section 5.2: the quantum Fourier transform, at the paper's sizes
--
-- The paper verifies its QFT circuit for 16 and for 31 qubits (the
-- table of section 5; beyond 31 its dyadic arithmetic overflows).
-- PathSum.QFT proves the equivalence for every n at once, given the
-- precision n + 1 ≤ M; the paper's two sizes are instances of it
-- (QFT16, QFT31), obtained by applying the theorem -- nothing about
-- the closed circuits is computed.  So are the table's other columns
-- (PathSum.QFT.Count): 16 and 31 path variables, and 256 and 961
-- Clifford gates, which are the counts of the circuit without its
-- SWAPs -- with them, QFTC has 280 and 1006.
--
-- Also a cross-check of the circuit itself: QFTC 3, its gates listed
-- with the proofs that CNOT's wires differ erased, is Nielsen and
-- Chuang's figure 5.1 on three qubits followed by the reversal (the
-- top wire's Hadamard, the rotations CR_2 from wire 1 and CR_3 from
-- wire 0, each as its five-gate subcircuit; then wire 1; then wire 0;
-- then SWAP 0 2 as three CNOTs), and its highest rotation is R_4, the
-- precision n + 1 that the theorem asks for.
--
-- There is no brute-force cross-check (PathSum.Brute): on two qubits
-- at M₀ = 0 it did not finish within ten minutes, and the theorem
-- does not need it.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples.QFT where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using ([]; _∷_; map)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Data.Nat.Properties as ℕ


------------------------------------------------------------------------
-- The circuit on three qubits

module Three where

  open import PathSum.CRK.Circuit 3 using (Gate; H; CNOT; R; R†; level)
  open import PathSum.QFT.Circuit 0 using (QFTC)

  -- A gate with the proof that a CNOT's wires differ forgotten.

  data Shape (n : ℕ) : Set where
    h    : Fin n → Shape n
    cnot : Fin n → Fin n → Shape n
    r r† : ℕ → Fin n → Shape n

  shape : ∀ {n} → Gate n → Shape n
  shape (H w)        = h w
  shape (CNOT c t _) = cnot c t
  shape (R k w)      = r k w
  shape (R† k w)     = r† k w

  w₀ w₁ w₂ : Fin 3
  w₀ = zero
  w₁ = suc zero
  w₂ = suc (suc zero)

  -- Figure 5.1 of Nielsen and Chuang on three qubits, wire 2 the most
  -- significant, then the reversal.

  QFTC-3 : map shape (QFTC 3) ≡
    h w₂ ∷
    r 3 w₁ ∷ r 3 w₂ ∷ cnot w₁ w₂ ∷ r† 3 w₂ ∷ cnot w₁ w₂ ∷   -- CR_2 1 2
    r 4 w₀ ∷ r 4 w₂ ∷ cnot w₀ w₂ ∷ r† 4 w₂ ∷ cnot w₀ w₂ ∷   -- CR_3 0 2
    h w₁ ∷
    r 3 w₀ ∷ r 3 w₁ ∷ cnot w₀ w₁ ∷ r† 3 w₁ ∷ cnot w₀ w₁ ∷   -- CR_2 0 1
    h w₀ ∷
    cnot w₀ w₂ ∷ cnot w₂ w₀ ∷ cnot w₀ w₂ ∷                   -- SWAP 0 2
    []
  QFTC-3 = refl

  QFTC-3-level : level (QFTC 3) ≡ 4
  QFTC-3-level = refl


------------------------------------------------------------------------
-- The paper's sizes

-- At M₀ = 14 (phases over 2^17) the theorem covers 16 qubits, and at
-- M₀ = 29 (over 2^32) 31 qubits.  The types, ⟦ QFTC 16 ⟧ ≋ QFTˢ 16 and
-- ⟦ QFTC 31 ⟧ ≋ QFTˢ 31, are left for Agda to infer from the theorem:
-- written out, they would be compared with the theorem's instance by
-- unfolding the closed circuits' path-sums.  Likewise the numbers of
-- path variables, paths (QFTC 16) ≡ 16 and paths (QFTC 31) ≡ 31.

module Sixteen where

  open import PathSum.QFT 14 using (QFT-≋)
  open import PathSum.QFT.Circuit 14 using (QFT₀; QFTC)
  open import PathSum.QFT.Count 14 using
    (cliffords; cliffords-QFT₀; cliffords-QFTC; paths-QFTC)

  QFT16 : _
  QFT16 = QFT-≋ 16 ℕ.≤-refl

  -- Table 2: 16 path variables and 256 Clifford gates -- without the
  -- SWAPs; with them, 280.

  QFT16-paths : _
  QFT16-paths = paths-QFTC 16

  QFT16-cliffords : cliffords (QFT₀ 16) ≡ 256
  QFT16-cliffords = cliffords-QFT₀ 16

  QFT16-cliffords-SWAP : cliffords (QFTC 16) ≡ 280
  QFT16-cliffords-SWAP = cliffords-QFTC 16

module ThirtyOne where

  open import PathSum.QFT 29 using (QFT-≋)
  open import PathSum.QFT.Circuit 29 using (QFT₀; QFTC)
  open import PathSum.QFT.Count 29 using
    (cliffords; cliffords-QFT₀; cliffords-QFTC; paths-QFTC)

  QFT31 : _
  QFT31 = QFT-≋ 31 ℕ.≤-refl

  -- Table 2: 31 path variables and 961 Clifford gates -- without the
  -- SWAPs; with them, 1006.

  QFT31-paths : _
  QFT31-paths = paths-QFTC 31

  QFT31-cliffords : cliffords (QFT₀ 31) ≡ 961
  QFT31-cliffords = cliffords-QFT₀ 31

  QFT31-cliffords-SWAP : cliffords (QFTC 31) ≡ 1006
  QFT31-cliffords-SWAP = cliffords-QFTC 31

------------------------------------------------------------------------
-- Presentations of groups
--
-- The size of the QFT circuit, against the paper's table of results
-- (Amy, QPL 2018, section 5.2 and table 2)
--
-- Table 2 reports, for the QFT on n = 16 and n = 31 qubits, 16 and 31
-- path variables, 256 and 961 Clifford gates, and no T count.  This
-- module counts the same things for the circuits of
-- PathSum.QFT.Circuit, for every n:
--
--  * path variables: ⟦ QFTC n ⟧ and ⟦ QFT₀ n ⟧ have n, one for each
--    Hadamard (paths-QFTC, paths-QFT₀);
--  * Clifford gates -- H, CNOT, and R_k, R_k† for k ≤ 2 (R_1 = Z,
--    R_2 = S): QFT₀ n, the circuit without the final permutation, has
--    exactly n² (cliffords-QFT₀): n Hadamards and two CNOTs in each of
--    the n(n-1)/2 controlled rotations, whose R_(k+1) gates have
--    k + 1 ≥ 3 and are not Clifford; the reversal adds 3 ⌊n/2⌋ CNOTs
--    (cliffords-reversal), so QFTC n has n² + 3 ⌊n/2⌋
--    (cliffords-QFTC).
--
-- So the table's Clifford counts, 16² = 256 and 31² = 961, are those
-- of the circuit without SWAP gates, and not the 280 and 1006 of QFTC
-- 16 and QFTC 31 (PathSum.Examples.QFT).  That suggests the paper's
-- "final qubit permutation correction" was not counted as gates,
-- which is what a relabelling of the outputs costs
-- (PathSum.QFT.Relabel, where ⟦ QFT₀ n ⟧ ≋ QFTʳ n).  It is a
-- consistency check, not a proof of what the paper's implementation
-- did: the paper does not give its decomposition of the controlled
-- rotations, and any decomposition with two CNOTs and no Clifford
-- single-qubit gate (H, Z or S) gives the same count.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.QFT.Count (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (Fin; fromℕ)
  renaming (zero to fzero; suc to fsuc)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Nat.Base using (zero; suc; _+_; _*_; _≤ᵇ_; ⌊_/2⌋)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

import Data.Nat.Properties as ℕ
open import Data.Nat.Solver using (module +-*-Solver)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.CRK.Circuit M using
  (Gate; H; CNOT; R; R†; Circuit; paths; paths≡norm)
open import PathSum.CRK.Trace M₀ using (Injective; mapC)
open import PathSum.QFT.Circuit M₀ using
  (SWAP; rotations; QFT₀; inner; inner-injective; reversal; QFTC;
   norm-QFT₀; norm-QFTC)

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

private
  variable
    n n′ : ℕ


------------------------------------------------------------------------
-- Clifford gates

-- H, CNOT, and R_k, R_k† for k ≤ 2.

clifford : Gate n → Bool
clifford (H _)        = true
clifford (CNOT _ _ _) = true
clifford (R k _)      = k ≤ᵇ 2
clifford (R† k _)     = k ≤ᵇ 2

cliffords : Circuit n → ℕ
cliffords []      = 0
cliffords (g ∷ C) = if clifford g then suc (cliffords C) else cliffords C

-- They add up along a concatenation, and do not see the wires.

cliffords-++ : (C D : Circuit n) →
               cliffords (C ++ D) ≡ cliffords C + cliffords D
cliffords-++ []      D = refl
cliffords-++ (g ∷ C) D = step (clifford g) (cliffords-++ C D)
  where
  step : ∀ b → cliffords (C ++ D) ≡ cliffords C + cliffords D →
         (if b then suc (cliffords (C ++ D)) else cliffords (C ++ D)) ≡
         (if b then suc (cliffords C) else cliffords C) + cliffords D
  step true  e = cong suc e
  step false e = e

cliffords-map : (ρ : Fin n → Fin n′) (inj : Injective ρ) (C : Circuit n) →
                cliffords (mapC ρ inj C) ≡ cliffords C
cliffords-map ρ inj []                = refl
cliffords-map ρ inj (H _ ∷ C)         = cong suc (cliffords-map ρ inj C)
cliffords-map ρ inj (CNOT _ _ _ ∷ C)  = cong suc (cliffords-map ρ inj C)
cliffords-map ρ inj (R k _ ∷ C)       =
  cong (λ c → if k ≤ᵇ 2 then suc c else c) (cliffords-map ρ inj C)
cliffords-map ρ inj (R† k _ ∷ C)      =
  cong (λ c → if k ≤ᵇ 2 then suc c else c) (cliffords-map ρ inj C)


------------------------------------------------------------------------
-- The QFT circuit

-- Each controlled rotation CR_k, k ≥ 2, has two CNOTs and three
-- rotations R_(k+1), none of them Clifford.

cliffords-rotations : ∀ n → cliffords (rotations n) ≡ 2 * n
cliffords-rotations zero    = refl
cliffords-rotations (suc n) = trans
  (cliffords-++ (mapC fsuc _ (rotations n)) _)
  (trans (cong (_+ 2) (trans (cliffords-map fsuc _ (rotations n))
                             (cliffords-rotations n)))
         (solve 1 (λ n → con 2 :* n :+ con 2 := con 2 :* (con 1 :+ n))
                refl n))

-- n Hadamards and n(n-1) CNOTs: n².

cliffords-QFT₀ : ∀ n → cliffords (QFT₀ n) ≡ n * n
cliffords-QFT₀ zero    = refl
cliffords-QFT₀ (suc n) = cong suc (trans
  (cliffords-++ (rotations n) (mapC _ _ (QFT₀ n)))
  (trans (cong₂ _+_ (cliffords-rotations n)
                    (trans (cliffords-map _ _ (QFT₀ n)) (cliffords-QFT₀ n)))
         (solve 1 (λ n → con 2 :* n :+ n :* n := n :+ n :* (con 1 :+ n))
                refl n)))

-- The reversal: ⌊n/2⌋ SWAPs of three CNOTs.

cliffords-reversal : ∀ n → cliffords (reversal n) ≡ 3 * ⌊ n /2⌋
cliffords-reversal zero          = refl
cliffords-reversal (suc zero)    = refl
cliffords-reversal (suc (suc n)) = trans
  (cliffords-++ (SWAP fzero (fromℕ (suc n)) (λ ()))
                (mapC inner inner-injective (reversal n)))
  (trans (cong (3 +_) (trans (cliffords-map inner inner-injective
                                            (reversal n))
                             (cliffords-reversal n)))
         (sym (ℕ.*-suc 3 ⌊ n /2⌋)))

cliffords-QFTC : ∀ n → cliffords (QFTC n) ≡ n * n + 3 * ⌊ n /2⌋
cliffords-QFTC n = trans (cliffords-++ (QFT₀ n) (reversal n))
  (cong₂ _+_ (cliffords-QFT₀ n) (cliffords-reversal n))


------------------------------------------------------------------------
-- Path variables

-- One for each Hadamard.

paths-QFT₀ : ∀ n → paths (QFT₀ n) ≡ n
paths-QFT₀ n = trans (paths≡norm (QFT₀ n)) (norm-QFT₀ n)

paths-QFTC : ∀ n → paths (QFTC n) ≡ n
paths-QFTC n = trans (paths≡norm (QFTC n)) (norm-QFTC n)

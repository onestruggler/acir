------------------------------------------------------------------------
-- Presentations of groups
--
-- Various box definitions.  The interpretation of boxes as circuits
-- is defined elsewhere.
------------------------------------------------------------------------
{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; _≤_ ; _∸_ ; 2+)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_×_ ; _,_ ; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Data.Vec using (Vec)
open import Notations
open import Relation.Binary.PropositionalEquality using (_≢_)
open import ForStdlib.Data.Fin.Mod

module Examples.Groups.Symplectic.Normalization.Boxes
  (p-2 : ℕ) (p-prime : Prime (2+ p-2))
  where

open PrimeModulus p-2 p-prime

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Atomic box components

A : Set
A = Σ[ ab ∈ (ℤ ₚ × ℤ ₚ) ] (ab ≢ (₀ , ₀))

B : Set
B = ℤ ₚ × ℤ ₚ

D : Set
D = ℤ ₚ × ℤ ₚ

E : Set
E = ℤ ₚ

------------------------------------------------------------------------
-- Width-indexed boxes

Lj : (j : ℕ) → Set
Lj j = Vec B j × A

-- Natural numbers that are less than (₁₊ n).
LE : (n : ℕ) → Set
LE n = Σ[ j ∈ ℕ ] j ≤ n

-- n-indexed boxes (L, M, ML, NF) is of width n.
L : (n : ℕ) → Set
L 0 = ⊤
L 1 = A
L (₂₊ n) = Σ[ (j , le) ∈ LE (₁₊ n) ] Lj ((₁₊ n) ∸ j)

L' : ℕ → Set
L' 0 = ⊤
L' (₁₊ n) = Vec B n × A

M : ℕ → Set
M 0 = ⊤
M (₁₊ n) = Vec D n × E

ML' : (n : ℕ) → Set
ML' 0 = ⊤
ML' n@(₁₊ _) = M n × L' n

ML : (n : ℕ) → Set
ML 0 = ⊤
ML 1 = ML' 1
ML (₂₊ n) = ML' (₂₊ n) ⊎ D × ML (₁₊ n)

NF : (n : ℕ) → Set
NF 0 = ⊤
NF (₁₊ n) = NF n × ML (₁₊ n)

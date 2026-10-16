------------------------------------------------------------------------
-- Presentations of groups
--
-- The five-wire window lemmas of (F6)
--
-- With A = CX(1→4), C = λ⁰(S₀) = X4 CS04 X4 and E = CS01⁻¹ CCZ014:
-- A = K4 CS14 CS14 K4 i, A C A = E C, A C³ A = C³ CS01 CCZ014, A A = ε
-- (windows), and the joint paper's SB2, Σ01 Σ01 = CCZ014.  Written by
-- `scratchpad/five/f6.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.F6Ax where

open import Data.List using (List ; [] ; _∷_)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-SB2)
open import Examples.Groups.Clifford+CS.Five.D.D235 using (lem-f6-aa ; lem-f6-cx14 ; lem-f6-ee ; lem-f6-w1 ; lem-f6-w2)

cx14 : Complete 4 → ⟪ (CX14 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ CS14 ∷ CS14 ∷ K4 ∷ ι ∷ []) ⟫ʷ
cx14 c4 = lem-f6-cx14 c4

w1 : Complete 4 → ⟪ (CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CCZ014 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
w1 c4 = lem-f6-w1 c4

w2 : Complete 4 → ⟪ (CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS01 ∷ CCZ014 ∷ []) ⟫ʷ
w2 c4 = lem-f6-w2 c4

aa : Complete 4 → ⟪ (CX14 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
aa c4 = lem-f6-aa c4

ee : Complete 4 → ⟪ (CS01 ∷ CCZ014 ∷ CS01⁻ ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
ee c4 = lem-f6-ee c4

sb2 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
sb2 c4 = lem-SB2 c4

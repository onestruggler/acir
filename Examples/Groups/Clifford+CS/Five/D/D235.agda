{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D235 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-F5-CS01)
open import Examples.Groups.Clifford+CS.Five.D.D200 using (lem-F5-CS12)
open import Examples.Groups.Clifford+CS.Five.D.D214 using (lem-F4-CS23ᵖ0∣K3ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D215 using (lem-F4-CS23ᵖ0∣CS01ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D220 using (lem-F4-CS23ᵖ0∣CS12ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D222 using (lem-F4-CS23ᵖ0∣CS23ᵖ1 ; lem-F5-CS23)
-- calc F4 CS23 K3: 1 steps
lem-calc-F4-CS23-K3 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣K3ᵖ1 c4) ▸ done


-- calc F4 CS23 CS01: 1 steps
lem-calc-F4-CS23-CS01 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-CS01 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣CS01ᵖ1 c4) ▸ done


-- calc F4 CS23 CS12: 1 steps
lem-calc-F4-CS23-CS12 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-CS12 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣CS12ᵖ1 c4) ▸ done


-- calc F4 CS23 CS23: 1 steps
lem-calc-F4-CS23-CS23 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-CS23 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣CS23ᵖ1 c4) ▸ done


-- calc F5 I 0: 1 steps
lem-calc-F5-I-0 : Complete 4 → ⟪ (ι ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
lem-calc-F5-I-0 c4 = run b0
  where
  b0 : Chain (ι ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ [])
  b0 = at 0 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (lw1 c4 (ι ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F5 I 1: 1 steps
lem-calc-F5-I-1 : Complete 4 → ⟪ (ι1 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
lem-calc-F5-I-1 c4 = run b0
  where
  b0 : Chain (ι1 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ [])
  b0 = at 0 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (lw0 c4 (ι1 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F5 I 2: 1 steps
lem-calc-F5-I-2 : Complete 4 → ⟪ (ι2 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
lem-calc-F5-I-2 c4 = run b0
  where
  b0 : Chain (ι2 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ [])
  b0 = at 0 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (lw0 c4 (ι2 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F5 I 3: 1 steps
lem-calc-F5-I-3 : Complete 4 → ⟪ (ι3 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
lem-calc-F5-I-3 c4 = run b0
  where
  b0 : Chain (ι3 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ [])
  b0 = at 0 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (lw0 c4 (ι3 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F5 I 4: 1 steps
lem-calc-F5-I-4 : Complete 4 → ⟪ (ι4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
lem-calc-F5-I-4 c4 = run b0
  where
  b0 : Chain (ι4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ [])
  b0 = at 0 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (lw0 c4 (ι4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F5 S0: 1 steps
lem-calc-F5-S0 : Complete 4 → ⟪ (S0 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
lem-calc-F5-S0 c4 = run b0
  where
  b0 : Chain (S0 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ [])
  b0 = at 0 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (pw1 c4 (S0 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl) ▸ done


-- calc F5 K0: 1 steps
lem-calc-F5-K0 : Complete 4 → ⟪ (K0 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
lem-calc-F5-K0 c4 = run b0
  where
  b0 : Chain (K0 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ [])
  b0 = at 0 1 (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (pw1 c4 (K0 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl) ▸ done


-- calc F5 S1: 1 steps
lem-calc-F5-S1 : Complete 4 → ⟪ (S1 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
lem-calc-F5-S1 c4 = run b0
  where
  b0 : Chain (S1 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ [])
  b0 = at 0 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (lw0 c4 (S1 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done


-- calc F5 K1: 1 steps
lem-calc-F5-K1 : Complete 4 → ⟪ (K1 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
lem-calc-F5-K1 c4 = run b0
  where
  b0 : Chain (K1 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ [])
  b0 = at 0 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (lw0 c4 (K1 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) tt tt Eq.refl) ▸ done


-- calc F5 S2: 1 steps
lem-calc-F5-S2 : Complete 4 → ⟪ (S2 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
lem-calc-F5-S2 c4 = run b0
  where
  b0 : Chain (S2 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ [])
  b0 = at 0 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (lw0 c4 (S2 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl) ▸ done


-- calc F5 K2: 1 steps
lem-calc-F5-K2 : Complete 4 → ⟪ (K2 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
lem-calc-F5-K2 c4 = run b0
  where
  b0 : Chain (K2 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ [])
  b0 = at 0 1 (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (lw0 c4 (K2 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) tt tt Eq.refl) ▸ done


-- calc F5 S3: 1 steps
lem-calc-F5-S3 : Complete 4 → ⟪ (S3 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
lem-calc-F5-S3 c4 = run b0
  where
  b0 : Chain (S3 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ [])
  b0 = at 0 1 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (lw0 c4 (S3 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl) ▸ done


-- calc F5 K3: 1 steps
lem-calc-F5-K3 : Complete 4 → ⟪ (K3 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
lem-calc-F5-K3 c4 = run b0
  where
  b0 : Chain (K3 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ [])
  b0 = at 0 1 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (lw0 c4 (K3 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) tt tt Eq.refl) ▸ done


-- calc F5 CS01: 1 steps
lem-calc-F5-CS01 : Complete 4 → ⟪ (CS01 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-calc-F5-CS01 c4 = run b0
  where
  b0 : Chain (CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-CS01 c4)) ▸ done


-- calc F5 CS12: 1 steps
lem-calc-F5-CS12 : Complete 4 → ⟪ (CS12 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-calc-F5-CS12 c4 = run b0
  where
  b0 : Chain (CS12 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸ done


-- calc F5 CS23: 1 steps
lem-calc-F5-CS23 : Complete 4 → ⟪ (CS23 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-calc-F5-CS23 c4 = run b0
  where
  b0 : Chain (CS23 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-CS23 c4)) ▸ done


-- calc x4x4: 1 steps
lem-calc-x4x4 : Complete 4 → ⟪ (X4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-calc-x4x4 c4 = run b0
  where
  b0 : Chain (X4 ∷ X4 ∷ []) []
  b0 = at 0 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done


-- f6 cx14: 2 steps
lem-f6-cx14 : Complete 4 → ⟪ (CX14 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ CS14 ∷ CS14 ∷ K4 ∷ ι ∷ []) ⟫ʷ
lem-f6-cx14 c4 = run b0
  where
  b0 : Chain (CX14 ∷ []) (K4 ∷ CS14 ∷ CS14 ∷ K4 ∷ ι ∷ [])
  b0 = at 0 1 (K4 ∷ CS14 ∷ CS14 ∷ K4 ∷ ι1 ∷ []) (pw0 c4 (CX14 ∷ []) (K4 ∷ CS14 ∷ CS14 ∷ K4 ∷ ι1 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸ done


-- f6 w1: 1 steps
lem-f6-w1 : Complete 4 → ⟪ (CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CCZ014 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-f6-w1 c4 = run b0
  where
  b0 : Chain (CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ []) (CS01⁻ ∷ CCZ014 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 5 (CS01⁻ ∷ CCZ014 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (pw2 c4 (CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ []) (CS01⁻ ∷ CCZ014 ∷ X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- f6 w2: 1 steps
lem-f6-w2 : Complete 4 → ⟪ (CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS01 ∷ CCZ014 ∷ []) ⟫ʷ
lem-f6-w2 c4 = run b0
  where
  b0 : Chain (CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS01 ∷ CCZ014 ∷ [])
  b0 = at 0 11 (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS01 ∷ CCZ014 ∷ []) (pw2 c4 (CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS01 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸ done


-- f6 aa: 1 steps
lem-f6-aa : Complete 4 → ⟪ (CX14 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-f6-aa c4 = run b0
  where
  b0 : Chain (CX14 ∷ CX14 ∷ []) []
  b0 = at 0 2 [] (lw0 c4 (CX14 ∷ CX14 ∷ []) [] tt tt Eq.refl) ▸ done


-- f6 ee: 1 steps
lem-f6-ee : Complete 4 → ⟪ (CS01 ∷ CCZ014 ∷ CS01⁻ ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-f6-ee c4 = run b0
  where
  b0 : Chain (CS01 ∷ CCZ014 ∷ CS01⁻ ∷ CCZ014 ∷ []) []
  b0 = at 0 4 [] (pw2 c4 (CS01 ∷ CCZ014 ∷ CS01⁻ ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸ done


{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D234 where

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
open import Examples.Groups.Clifford+CS.Five.D.D156 using (lem-F4-S3ᵖ0∣CS01ᵖ1 ; lem-F4-S3ᵖ0∣CS12ᵖ1 ; lem-F4-S3ᵖ0∣CS23ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D157 using (lem-F4-CS01ᵖ0∣iIᵖ1 ; lem-F4-K2ᵖ0∣CS01ᵖ1 ; lem-F4-K2ᵖ0∣CS12ᵖ1 ; lem-F4-K2ᵖ0∣CS23ᵖ1 ; lem-F4-K3ᵖ0∣CS01ᵖ1 ; lem-F4-K3ᵖ0∣CS12ᵖ1 ; lem-F4-K3ᵖ0∣CS23ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D158 using (lem-F4-CS01ᵖ0∣K0ᵖ1 ; lem-F4-CS01ᵖ0∣S0ᵖ1 ; lem-F4-CS01ᵖ0∣S1ᵖ1 ; lem-F4-CS01ᵖ0∣S2ᵖ1 ; lem-F4-CS01ᵖ0∣S3ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D159 using (lem-F4-CS01ᵖ0∣K1ᵖ1 ; lem-F4-CS01ᵖ0∣K2ᵖ1 ; lem-F4-CS01ᵖ0∣K3ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D160 using (lem-F4-CS01ᵖ0∣CS01ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D166 using (lem-F4-CS01ᵖ0∣CS12ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D170 using (lem-F4-CS01ᵖ0∣CS23ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D193 using (lem-F4-CS12ᵖ0∣K0ᵖ1 ; lem-F4-CS12ᵖ0∣S0ᵖ1 ; lem-F4-CS12ᵖ0∣S1ᵖ1 ; lem-F4-CS12ᵖ0∣S2ᵖ1 ; lem-F4-CS12ᵖ0∣S3ᵖ1 ; lem-F4-CS12ᵖ0∣iIᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D194 using (lem-F4-CS12ᵖ0∣K1ᵖ1 ; lem-F4-CS12ᵖ0∣K2ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D195 using (lem-F4-CS12ᵖ0∣K3ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D197 using (lem-F4-CS12ᵖ0∣CS01ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D200 using (lem-F4-CS12ᵖ0∣CS12ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D203 using (lem-F4-CS12ᵖ0∣CS23ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D212 using (lem-F4-CS23ᵖ0∣S0ᵖ1 ; lem-F4-CS23ᵖ0∣iIᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D213 using (lem-F4-CS23ᵖ0∣K0ᵖ1 ; lem-F4-CS23ᵖ0∣K1ᵖ1 ; lem-F4-CS23ᵖ0∣S1ᵖ1 ; lem-F4-CS23ᵖ0∣S2ᵖ1 ; lem-F4-CS23ᵖ0∣S3ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D214 using (lem-F4-CS23ᵖ0∣K2ᵖ1)
-- calc F4 K2 K1: 1 steps
lem-calc-F4-K2-K1 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 K2 S2: 1 steps
lem-calc-F4-K2-S2 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 K2 K2: 1 steps
lem-calc-F4-K2-K2 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 K2 S3: 1 steps
lem-calc-F4-K2-S3 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 K2 K3: 1 steps
lem-calc-F4-K2-K3 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 K2 CS01: 1 steps
lem-calc-F4-K2-CS01 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-CS01 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2ᵖ0∣CS01ᵖ1 c4) ▸ done


-- calc F4 K2 CS12: 1 steps
lem-calc-F4-K2-CS12 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-CS12 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2ᵖ0∣CS12ᵖ1 c4) ▸ done


-- calc F4 K2 CS23: 1 steps
lem-calc-F4-K2-CS23 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-CS23 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2ᵖ0∣CS23ᵖ1 c4) ▸ done


-- calc F4 S3 I: 1 steps
lem-calc-F4-S3-I : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 S3 S0: 1 steps
lem-calc-F4-S3-S0 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 S3 K0: 1 steps
lem-calc-F4-S3-K0 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 S3 S1: 1 steps
lem-calc-F4-S3-S1 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 S3 K1: 1 steps
lem-calc-F4-S3-K1 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 S3 S2: 1 steps
lem-calc-F4-S3-S2 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 S3 K2: 1 steps
lem-calc-F4-S3-K2 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 S3 S3: 1 steps
lem-calc-F4-S3-S3 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 S3 K3: 1 steps
lem-calc-F4-S3-K3 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 S3 CS01: 1 steps
lem-calc-F4-S3-CS01 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-CS01 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3ᵖ0∣CS01ᵖ1 c4) ▸ done


-- calc F4 S3 CS12: 1 steps
lem-calc-F4-S3-CS12 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-CS12 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3ᵖ0∣CS12ᵖ1 c4) ▸ done


-- calc F4 S3 CS23: 1 steps
lem-calc-F4-S3-CS23 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-CS23 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3ᵖ0∣CS23ᵖ1 c4) ▸ done


-- calc F4 K3 I: 1 steps
lem-calc-F4-K3-I : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 K3 S0: 1 steps
lem-calc-F4-K3-S0 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 K3 K0: 1 steps
lem-calc-F4-K3-K0 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 K3 S1: 1 steps
lem-calc-F4-K3-S1 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 K3 K1: 1 steps
lem-calc-F4-K3-K1 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 K3 S2: 1 steps
lem-calc-F4-K3-S2 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 K3 K2: 1 steps
lem-calc-F4-K3-K2 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 K3 S3: 1 steps
lem-calc-F4-K3-S3 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 K3 K3: 1 steps
lem-calc-F4-K3-K3 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 K3 CS01: 1 steps
lem-calc-F4-K3-CS01 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-CS01 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3ᵖ0∣CS01ᵖ1 c4) ▸ done


-- calc F4 K3 CS12: 1 steps
lem-calc-F4-K3-CS12 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-CS12 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3ᵖ0∣CS12ᵖ1 c4) ▸ done


-- calc F4 K3 CS23: 1 steps
lem-calc-F4-K3-CS23 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-CS23 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3ᵖ0∣CS23ᵖ1 c4) ▸ done


-- calc F4 CS01 I: 1 steps
lem-calc-F4-CS01-I : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-I c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣iIᵖ1 c4) ▸ done


-- calc F4 CS01 S0: 1 steps
lem-calc-F4-CS01-S0 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣S0ᵖ1 c4) ▸ done


-- calc F4 CS01 K0: 1 steps
lem-calc-F4-CS01-K0 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣K0ᵖ1 c4) ▸ done


-- calc F4 CS01 S1: 1 steps
lem-calc-F4-CS01-S1 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣S1ᵖ1 c4) ▸ done


-- calc F4 CS01 K1: 1 steps
lem-calc-F4-CS01-K1 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣K1ᵖ1 c4) ▸ done


-- calc F4 CS01 S2: 1 steps
lem-calc-F4-CS01-S2 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣S2ᵖ1 c4) ▸ done


-- calc F4 CS01 K2: 1 steps
lem-calc-F4-CS01-K2 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣K2ᵖ1 c4) ▸ done


-- calc F4 CS01 S3: 1 steps
lem-calc-F4-CS01-S3 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣S3ᵖ1 c4) ▸ done


-- calc F4 CS01 K3: 1 steps
lem-calc-F4-CS01-K3 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣K3ᵖ1 c4) ▸ done


-- calc F4 CS01 CS01: 1 steps
lem-calc-F4-CS01-CS01 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-CS01 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4) ▸ done


-- calc F4 CS01 CS12: 1 steps
lem-calc-F4-CS01-CS12 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-CS12 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣CS12ᵖ1 c4) ▸ done


-- calc F4 CS01 CS23: 1 steps
lem-calc-F4-CS01-CS23 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-CS23 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣CS23ᵖ1 c4) ▸ done


-- calc F4 CS12 I: 1 steps
lem-calc-F4-CS12-I : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-I c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣iIᵖ1 c4) ▸ done


-- calc F4 CS12 S0: 1 steps
lem-calc-F4-CS12-S0 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣S0ᵖ1 c4) ▸ done


-- calc F4 CS12 K0: 1 steps
lem-calc-F4-CS12-K0 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣K0ᵖ1 c4) ▸ done


-- calc F4 CS12 S1: 1 steps
lem-calc-F4-CS12-S1 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣S1ᵖ1 c4) ▸ done


-- calc F4 CS12 K1: 1 steps
lem-calc-F4-CS12-K1 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣K1ᵖ1 c4) ▸ done


-- calc F4 CS12 S2: 1 steps
lem-calc-F4-CS12-S2 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣S2ᵖ1 c4) ▸ done


-- calc F4 CS12 K2: 1 steps
lem-calc-F4-CS12-K2 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣K2ᵖ1 c4) ▸ done


-- calc F4 CS12 S3: 1 steps
lem-calc-F4-CS12-S3 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣S3ᵖ1 c4) ▸ done


-- calc F4 CS12 K3: 1 steps
lem-calc-F4-CS12-K3 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣K3ᵖ1 c4) ▸ done


-- calc F4 CS12 CS01: 1 steps
lem-calc-F4-CS12-CS01 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-CS01 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣CS01ᵖ1 c4) ▸ done


-- calc F4 CS12 CS12: 1 steps
lem-calc-F4-CS12-CS12 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-CS12 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4) ▸ done


-- calc F4 CS12 CS23: 1 steps
lem-calc-F4-CS12-CS23 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-CS23 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣CS23ᵖ1 c4) ▸ done


-- calc F4 CS23 I: 1 steps
lem-calc-F4-CS23-I : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-I c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣iIᵖ1 c4) ▸ done


-- calc F4 CS23 S0: 1 steps
lem-calc-F4-CS23-S0 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣S0ᵖ1 c4) ▸ done


-- calc F4 CS23 K0: 1 steps
lem-calc-F4-CS23-K0 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣K0ᵖ1 c4) ▸ done


-- calc F4 CS23 S1: 1 steps
lem-calc-F4-CS23-S1 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣S1ᵖ1 c4) ▸ done


-- calc F4 CS23 K1: 1 steps
lem-calc-F4-CS23-K1 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣K1ᵖ1 c4) ▸ done


-- calc F4 CS23 S2: 1 steps
lem-calc-F4-CS23-S2 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣S2ᵖ1 c4) ▸ done


-- calc F4 CS23 K2: 1 steps
lem-calc-F4-CS23-K2 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣K2ᵖ1 c4) ▸ done


-- calc F4 CS23 S3: 1 steps
lem-calc-F4-CS23-S3 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣S3ᵖ1 c4) ▸ done


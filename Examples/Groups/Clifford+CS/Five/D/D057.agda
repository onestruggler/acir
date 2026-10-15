{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D057 where

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
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-box-cP-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D028 using (lem-CSu-box-2-at122441 ; lem-CSu-box-2-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D032 using (lem-CSu-box-2-at0210243143)
-- F2-S0-K2: 1 steps
lem-F2-S0-K2 : Complete 4 → ⟪ (CS04 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-K2 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CK42 ∷ []) (CK42 ∷ CS04 ∷ [])
  b0 = at 0 2 (CK42 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ CK42 ∷ []) (CK42 ∷ CS04 ∷ []) tt tt Eq.refl) ▸ done


-- F2-S0-K3: 1 steps
lem-F2-S0-K3 : Complete 4 → ⟪ (CS04 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-K3 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CK43 ∷ []) (CK43 ∷ CS04 ∷ [])
  b0 = at 0 2 (CK43 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ CK43 ∷ []) (CK43 ∷ CS04 ∷ []) tt tt Eq.refl) ▸ done


-- F2-S0-CS1: 11 steps
lem-F2-S0-CS1 : Complete 4 → ⟪ (CS04 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-CS1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS04 ∷ Sb0-1-42-3 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS04 ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (Bx0-1423 ∷ CS04 ∷ []) (lem-CSu-box-2-at243243 c4) ▸
       at 1 2 (Toff324 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ Toff324 ∷ []) (Toff324 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS13 ∷ CS04 ∷ []) (pw2 c4 (CS04 ∷ CS13 ∷ []) (CS13 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff324 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ Toff324 ∷ []) (Toff324 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS13⁻ ∷ CS04 ∷ []) (pw2 c4 (CS04 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS04 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS04 ∷ []) (Sb0-1-42-3 ∷ CS04 ∷ [])
  b1 = at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- F2-S0-CS2: 11 steps
lem-F2-S0-CS2 : Complete 4 → ⟪ (CS04 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS04 ∷ Sb0-2-43-1 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS04 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Bx0-2431 ∷ CS04 ∷ []) (lem-CSu-box-2-at122441 c4) ▸
       at 1 2 (Toff134 ∷ CS04 ∷ []) (pw2 c4 (CS04 ∷ Toff134 ∷ []) (Toff134 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS12 ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ CS12 ∷ []) (CS12 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff134 ∷ CS04 ∷ []) (pw2 c4 (CS04 ∷ Toff134 ∷ []) (Toff134 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS12⁻ ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS04 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS04 ∷ []) (Sb0-2-43-1 ∷ CS04 ∷ [])
  b1 = at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F2-S1-S2: 1 steps
lem-F2-S1-S2 : Complete 4 → ⟪ (CS14 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-S2 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CS24 ∷ []) (CS24 ∷ CS14 ∷ [])
  b0 = at 0 2 (CS24 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CS24 ∷ []) (CS24 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done


-- F2-S1-S3: 1 steps
lem-F2-S1-S3 : Complete 4 → ⟪ (CS14 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-S3 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CS34 ∷ []) (CS34 ∷ CS14 ∷ [])
  b0 = at 0 2 (CS34 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CS34 ∷ []) (CS34 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done


-- F2-S1-K0: 1 steps
lem-F2-S1-K0 : Complete 4 → ⟪ (CS14 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-K0 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CK40 ∷ []) (CK40 ∷ CS14 ∷ [])
  b0 = at 0 2 (CK40 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CK40 ∷ []) (CK40 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done


-- F2-S1-K2: 1 steps
lem-F2-S1-K2 : Complete 4 → ⟪ (CS14 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-K2 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CK42 ∷ []) (CK42 ∷ CS14 ∷ [])
  b0 = at 0 2 (CK42 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CK42 ∷ []) (CK42 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done


-- F2-S1-K3: 1 steps
lem-F2-S1-K3 : Complete 4 → ⟪ (CS14 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-K3 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CK43 ∷ []) (CK43 ∷ CS14 ∷ [])
  b0 = at 0 2 (CK43 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CK43 ∷ []) (CK43 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done


-- F2-S1-CS2: 13 steps
lem-F2-S1-CS2 : Complete 4 → ⟪ (CS14 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS14 ∷ Sb0-2-43-1 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS14 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff013 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ Toff013 ∷ []) (Toff013 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ Toff013 ∷ []) (Toff013 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS14 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Sb0-2-43-1 ∷ CS14 ∷ [])
  b1 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 5 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F2-S2-S3: 1 steps
lem-F2-S2-S3 : Complete 4 → ⟪ (CS24 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2-S3 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CS34 ∷ []) (CS34 ∷ CS24 ∷ [])
  b0 = at 0 2 (CS34 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ CS34 ∷ []) (CS34 ∷ CS24 ∷ []) tt tt Eq.refl) ▸ done


-- F2-S2-K0: 1 steps
lem-F2-S2-K0 : Complete 4 → ⟪ (CS24 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2-K0 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CK40 ∷ []) (CK40 ∷ CS24 ∷ [])
  b0 = at 0 2 (CK40 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CK40 ∷ []) (CK40 ∷ CS24 ∷ []) tt tt Eq.refl) ▸ done


-- F2-S2-K1: 1 steps
lem-F2-S2-K1 : Complete 4 → ⟪ (CS24 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2-K1 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CK41 ∷ []) (CK41 ∷ CS24 ∷ [])
  b0 = at 0 2 (CK41 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ CK41 ∷ []) (CK41 ∷ CS24 ∷ []) tt tt Eq.refl) ▸ done


-- F2-S2-K3: 1 steps
lem-F2-S2-K3 : Complete 4 → ⟪ (CS24 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2-K3 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CK43 ∷ []) (CK43 ∷ CS24 ∷ [])
  b0 = at 0 2 (CK43 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ CK43 ∷ []) (CK43 ∷ CS24 ∷ []) tt tt Eq.refl) ▸ done


-- F2-S2-CS0: 11 steps
lem-F2-S2-CS0 : Complete 4 → ⟪ (CS24 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2-CS0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS24 ∷ Sb2-0-41-3 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS24 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (Bx2-0413 ∷ CS24 ∷ []) (lem-CSu-box-2-at0210243143 c4) ▸
       at 1 2 (Toff314 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ Toff314 ∷ []) (Toff314 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS03 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CS03 ∷ []) (CS03 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff314 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ Toff314 ∷ []) (Toff314 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS03⁻ ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS24 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS24 ∷ []) (Sb2-0-41-3 ∷ CS24 ∷ [])
  b1 = at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- F2-S3-K0: 1 steps
lem-F2-S3-K0 : Complete 4 → ⟪ (CS34 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3-K0 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CK40 ∷ []) (CK40 ∷ CS34 ∷ [])
  b0 = at 0 2 (CK40 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CK40 ∷ []) (CK40 ∷ CS34 ∷ []) tt tt Eq.refl) ▸ done


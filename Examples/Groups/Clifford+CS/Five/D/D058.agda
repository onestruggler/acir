{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D058 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-cP-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-box-cP-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-box-tQ-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D031 using (lem-box-perm-1324-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D035 using (lem-box-perm-1324-at0210243143 ; lem-cQ-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D038 using (lem-CKu-box-2-at0210243143 ; lem-CKu-box-2-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D039 using (lem-CKu-box-2-at122441)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CS23-CCZ014 ; lem-comm-CSd23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-comm-CK41-TOFF023)
-- F2-S3-K1: 1 steps
lem-F2-S3-K1 : Complete 4 → ⟪ (CS34 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3-K1 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CK41 ∷ []) (CK41 ∷ CS34 ∷ [])
  b0 = at 0 2 (CK41 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ CK41 ∷ []) (CK41 ∷ CS34 ∷ []) tt tt Eq.refl) ▸ done


-- F2-S3-K2: 1 steps
lem-F2-S3-K2 : Complete 4 → ⟪ (CS34 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3-K2 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CK42 ∷ []) (CK42 ∷ CS34 ∷ [])
  b0 = at 0 2 (CK42 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ CK42 ∷ []) (CK42 ∷ CS34 ∷ []) tt tt Eq.refl) ▸ done


-- F2-S3-CS0: 13 steps
lem-F2-S3-CS0 : Complete 4 → ⟪ (CS34 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3-CS0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS34 ∷ Sb2-0-41-3 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS34 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ Toff213 ∷ []) (Toff213 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ Toff213 ∷ []) (Toff213 ∷ CS34 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS34 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Sb2-0-41-3 ∷ CS34 ∷ [])
  b1 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 5 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- F2-S3-CS1: 13 steps
lem-F2-S3-CS1 : Complete 4 → ⟪ (CS34 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3-CS1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS34 ∷ Sb0-1-42-3 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS34 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 2 (CCZ014 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ Toff023 ∷ []) (Toff023 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ014 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ Toff023 ∷ []) (Toff023 ∷ CS34 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS34 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Sb0-1-42-3 ∷ CS34 ∷ [])
  b1 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 5 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- F2-K0-K1: 1 steps
lem-F2-K0-K1 : Complete 4 → ⟪ (CK40 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0-K1 c4 = run b0
  where
  b0 : Chain (CK40 ∷ CK41 ∷ []) (CK41 ∷ CK40 ∷ [])
  b0 = at 0 2 (CK41 ∷ CK40 ∷ []) (pw2 c4 (CK40 ∷ CK41 ∷ []) (CK41 ∷ CK40 ∷ []) tt tt Eq.refl) ▸ done


-- F2-K0-K2: 1 steps
lem-F2-K0-K2 : Complete 4 → ⟪ (CK40 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0-K2 c4 = run b0
  where
  b0 : Chain (CK40 ∷ CK42 ∷ []) (CK42 ∷ CK40 ∷ [])
  b0 = at 0 2 (CK42 ∷ CK40 ∷ []) (pw1 c4 (CK40 ∷ CK42 ∷ []) (CK42 ∷ CK40 ∷ []) tt tt Eq.refl) ▸ done


-- F2-K0-K3: 1 steps
lem-F2-K0-K3 : Complete 4 → ⟪ (CK40 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0-K3 c4 = run b0
  where
  b0 : Chain (CK40 ∷ CK43 ∷ []) (CK43 ∷ CK40 ∷ [])
  b0 = at 0 2 (CK43 ∷ CK40 ∷ []) (pw1 c4 (CK40 ∷ CK43 ∷ []) (CK43 ∷ CK40 ∷ []) tt tt Eq.refl) ▸ done


-- F2-K0-CS1: 11 steps
lem-F2-K0-CS1 : Complete 4 → ⟪ (CK40 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0-CS1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK40 ∷ Sb0-1-42-3 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK40 ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (Bx0-1423 ∷ CK40 ∷ []) (lem-CKu-box-2-at243243 c4) ▸
       at 1 2 (Toff324 ∷ CK40 ∷ []) (pw1 c4 (CK40 ∷ Toff324 ∷ []) (Toff324 ∷ CK40 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS13 ∷ CK40 ∷ []) (pw2 c4 (CK40 ∷ CS13 ∷ []) (CS13 ∷ CK40 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff324 ∷ CK40 ∷ []) (pw1 c4 (CK40 ∷ Toff324 ∷ []) (Toff324 ∷ CK40 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS13⁻ ∷ CK40 ∷ []) (pw2 c4 (CK40 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CK40 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK40 ∷ []) (Sb0-1-42-3 ∷ CK40 ∷ [])
  b1 = at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- F2-K0-CS2: 11 steps
lem-F2-K0-CS2 : Complete 4 → ⟪ (CK40 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK40 ∷ Sb0-2-43-1 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK40 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Bx0-2431 ∷ CK40 ∷ []) (lem-CKu-box-2-at122441 c4) ▸
       at 1 2 (Toff134 ∷ CK40 ∷ []) (pw2 c4 (CK40 ∷ Toff134 ∷ []) (Toff134 ∷ CK40 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS12 ∷ CK40 ∷ []) (pw3 c4 (CK40 ∷ CS12 ∷ []) (CS12 ∷ CK40 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff134 ∷ CK40 ∷ []) (pw2 c4 (CK40 ∷ Toff134 ∷ []) (Toff134 ∷ CK40 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS12⁻ ∷ CK40 ∷ []) (pw3 c4 (CK40 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CK40 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK40 ∷ []) (Sb0-2-43-1 ∷ CK40 ∷ [])
  b1 = at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F2-K1-K2: 1 steps
lem-F2-K1-K2 : Complete 4 → ⟪ (CK41 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CK41 ∷ []) ⟫ʷ
lem-F2-K1-K2 c4 = run b0
  where
  b0 : Chain (CK41 ∷ CK42 ∷ []) (CK42 ∷ CK41 ∷ [])
  b0 = at 0 2 (CK42 ∷ CK41 ∷ []) (lw0 c4 (CK41 ∷ CK42 ∷ []) (CK42 ∷ CK41 ∷ []) tt tt Eq.refl) ▸ done


-- F2-K1-K3: 1 steps
lem-F2-K1-K3 : Complete 4 → ⟪ (CK41 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CK41 ∷ []) ⟫ʷ
lem-F2-K1-K3 c4 = run b0
  where
  b0 : Chain (CK41 ∷ CK43 ∷ []) (CK43 ∷ CK41 ∷ [])
  b0 = at 0 2 (CK43 ∷ CK41 ∷ []) (lw0 c4 (CK41 ∷ CK43 ∷ []) (CK43 ∷ CK41 ∷ []) tt tt Eq.refl) ▸ done


-- F2-K1-CS2: 35 steps
lem-F2-K1-CS2 : Complete 4 → ⟪ (CK41 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CK41 ∷ []) ⟫ʷ
lem-F2-K1-CS2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CK41 ∷ Sb0-2-43-1 ∷ []) (Toff023 ∷ CCZ014 ∷ CZ01 ∷ CK41 ∷ Toff023 ∷ CZ01 ∷ CCZ123 ∷ CCZ014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at12233441 c4) ▸
       at 0 2 (Toff023 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF023 c4) ▸
       at 1 2 (CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ []) (pw2 c4 (CK41 ∷ CCZ014 ∷ []) (CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (lw4 c4 (CZ01 ∷ Toff023 ∷ []) (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ CZ01 ∷ CK41 ∷ Toff023 ∷ CZ01 ∷ CCZ123 ∷ CCZ014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CZ01 ∷ CCZ123 ∷ CK41 ∷ CZ01 ∷ CCZ014 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 3 2 (Toff023 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF023 c4) ▸
       at 2 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (lw4 c4 (CZ01 ∷ Toff023 ∷ []) (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 8 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸ done

  b2 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CZ01 ∷ CCZ123 ∷ CK41 ∷ CZ01 ∷ CCZ014 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CZ01 ∷ CS23 ∷ CCZ014 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ CZ01 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b2 = at 8 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CZ01 ∷ []) (pw2 c4 (CZ01 ∷ CCZ014 ∷ []) (CCZ014 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ []) (pw2 c4 (CK41 ∷ CCZ014 ∷ []) (CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CZ01 ∷ CS23 ∷ CCZ014 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ CZ01 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK41 ∷ [])
  b3 = at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CZ01 ∷ []) (pw2 c4 (CZ01 ∷ CCZ014 ∷ []) (CCZ014 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (CZ01 ∷ CK41 ∷ []) (pw2 c4 (CZ01 ∷ CK41 ∷ CZ01 ∷ CZ01 ∷ []) (CZ01 ∷ CK41 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CCZ123 ∷ []) (lw4 c4 (CZ01 ∷ CCZ123 ∷ CZ01 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-2341 ∷ []) (sym (lem-box-tQ-at12233441 c4)) ▸
       at 0 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 1 7 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK41 ∷ []) (lw0 c4 (CCZ123 ∷ CK41 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK41 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK41 ∷ []) (Sb0-2-43-1 ∷ CK41 ∷ [])
  b4 = at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F2-K2-K3: 1 steps
lem-F2-K2-K3 : Complete 4 → ⟪ (CK42 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CK42 ∷ []) ⟫ʷ
lem-F2-K2-K3 c4 = run b0
  where
  b0 : Chain (CK42 ∷ CK43 ∷ []) (CK43 ∷ CK42 ∷ [])
  b0 = at 0 2 (CK43 ∷ CK42 ∷ []) (lw0 c4 (CK42 ∷ CK43 ∷ []) (CK43 ∷ CK42 ∷ []) tt tt Eq.refl) ▸ done


-- F2-K2-CS0: 11 steps
lem-F2-K2-CS0 : Complete 4 → ⟪ (CK42 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK42 ∷ []) ⟫ʷ
lem-F2-K2-CS0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK42 ∷ Sb2-0-41-3 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK42 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (Bx2-0413 ∷ CK42 ∷ []) (lem-CKu-box-2-at0210243143 c4) ▸
       at 1 2 (Toff314 ∷ CK42 ∷ []) (lw0 c4 (CK42 ∷ Toff314 ∷ []) (Toff314 ∷ CK42 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS03 ∷ CK42 ∷ []) (pw1 c4 (CK42 ∷ CS03 ∷ []) (CS03 ∷ CK42 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff314 ∷ CK42 ∷ []) (lw0 c4 (CK42 ∷ Toff314 ∷ []) (Toff314 ∷ CK42 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS03⁻ ∷ CK42 ∷ []) (pw1 c4 (CK42 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CK42 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK42 ∷ []) (Sb2-0-41-3 ∷ CK42 ∷ [])
  b1 = at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- box-tQ @0210213443: 13 steps
lem-box-tQ-at0210213443 : Complete 4 → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at0210213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0143 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (pw1 c4 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (pw1 c4 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff201 ∷ CCZ012 ∷ CZ01 ∷ []) (lw4 c4 (CCZ012 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ012 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-cQ-at0210213443 c4) ▸
       at 2 4 (Toff201 ∷ []) (lw4 c4 (CCZ012 ∷ CZ01 ∷ Toff201 ∷ CCZ012 ∷ []) (Toff201 ∷ []) tt tt Eq.refl) ▸ done


-- F2-K3-CS0: 35 steps
lem-F2-K3-CS0 : Complete 4 → ⟪ (CK43 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK43 ∷ []) ⟫ʷ
lem-F2-K3-CS0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CK43 ∷ Sb2-0-41-3 ∷ []) (Toff201 ∷ CCZ234 ∷ CZ23 ∷ CK43 ∷ Toff201 ∷ CZ23 ∷ CCZ013 ∷ CCZ234 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 1 (Bx2-0143 ∷ []) (lem-box-perm-1324-at0210243143 c4) ▸
       at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0210213443 c4) ▸
       at 0 2 (Toff201 ∷ CK43 ∷ []) (sym (c₃ (Toffᵗ) (CK₁₀))) ▸
       at 1 2 (CCZ234 ∷ CZ23 ∷ CK43 ∷ CZ23 ∷ []) (lw0 c4 (CK43 ∷ CCZ234 ∷ []) (CCZ234 ∷ CZ23 ∷ CK43 ∷ CZ23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff201 ∷ CZ23 ∷ CCZ013 ∷ []) (lw4 c4 (CZ23 ∷ Toff201 ∷ []) (Toff201 ∷ CZ23 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff201 ∷ CCZ234 ∷ CZ23 ∷ CK43 ∷ Toff201 ∷ CZ23 ∷ CCZ013 ∷ CCZ234 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CZ23 ∷ CCZ013 ∷ CK43 ∷ CZ23 ∷ CCZ234 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b1 = at 3 2 (Toff201 ∷ CK43 ∷ []) (sym (c₃ (Toffᵗ) (CK₁₀))) ▸
       at 2 2 (Toff201 ∷ CZ23 ∷ CCZ013 ∷ []) (lw4 c4 (CZ23 ∷ Toff201 ∷ []) (Toff201 ∷ CZ23 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CCZ234 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 9 2 (CCZ234 ∷ CS13⁻ ∷ []) (lw0 c4 (CS13⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 7 2 (CCZ234 ∷ CS13 ∷ []) (lw0 c4 (CS13 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS13 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CZ23 ∷ CCZ013 ∷ CK43 ∷ CZ23 ∷ CCZ234 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CZ23 ∷ CS13 ∷ CCZ234 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CZ23 ∷ CK43 ∷ CZ23 ∷ CZ23 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b2 = at 8 5 (CCZ013 ∷ []) (lw4 c4 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ234 ∷ CZ23 ∷ []) (lw0 c4 (CZ23 ∷ CCZ234 ∷ []) (CCZ234 ∷ CZ23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ234 ∷ CZ23 ∷ CK43 ∷ CZ23 ∷ []) (lw0 c4 (CK43 ∷ CCZ234 ∷ []) (CCZ234 ∷ CZ23 ∷ CK43 ∷ CZ23 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ234 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 6 2 (CCZ234 ∷ CS13⁻ ∷ []) (lw0 c4 (CS13⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸ done

  b3 : Chain (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CZ23 ∷ CS13 ∷ CCZ234 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CZ23 ∷ CK43 ∷ CZ23 ∷ CZ23 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK43 ∷ [])
  b3 = at 4 2 (CCZ234 ∷ CS13 ∷ []) (lw0 c4 (CS13 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (CCZ013 ∷ []) (lw4 c4 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ CZ23 ∷ []) (lw0 c4 (CZ23 ∷ CCZ234 ∷ []) (CCZ234 ∷ CZ23 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (CZ23 ∷ CK43 ∷ []) (lw0 c4 (CZ23 ∷ CK43 ∷ CZ23 ∷ CZ23 ∷ []) (CZ23 ∷ CK43 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CCZ013 ∷ []) (lw4 c4 (CZ23 ∷ CCZ013 ∷ CZ23 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-0143 ∷ []) (sym (lem-box-tQ-at0210213443 c4)) ▸
       at 0 1 (Bx2-0413 ∷ []) (sym (lem-box-perm-1324-at0210243143 c4)) ▸
       at 1 7 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK43 ∷ []) (pw2 c4 (CCZ013 ∷ CK43 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK43 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK43 ∷ []) (Sb2-0-41-3 ∷ CK43 ∷ [])
  b4 = at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


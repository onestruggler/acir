{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D039 where

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
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-box-cP-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-CSdu-box-2-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D029 using (lem-Kdu-box-at122441 ; lem-Ku-box-at122441 ; lem-sym-ab-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D030 using (lem-sym-bc-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.D031 using (lem-box-perm-1324-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D032 using (lem-box-cP-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D037 using (lem-box-cP-at12213443 ; lem-box-perm-1423-at122441)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd13-CCZ024 ; lem-comm-CX04-TOFF213 ; lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CZ14-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-TOFF013-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-comm-CX41-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-comm-CCZ023-CK41 ; lem-comm-CCZ024-CX13 ; lem-comm-CS02-TOFF314 ; lem-comm-CSd02-TOFF314 ; lem-comm-TOFF013-CK42 ; lem-comm-TOFF213-CX04)
-- F4-CS2-S2: 17 steps
lem-F4-CS2-S2 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-S2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ S2 ∷ CS24⁻ ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S2 ∷ CS24⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ []) (S2 ∷ CS24⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 6 (S2 ∷ CS24⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 2 (S2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ S2 ∷ []) (S2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ S2 ∷ CS24⁻ ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ S2 ∷ CS24⁻ ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b1 = at 3 3 (S2 ∷ CS24⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (S2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ S2 ∷ []) (S2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 c4) ▸
       at 1 3 (S2 ∷ CS24⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ S2 ∷ CS24⁻ ∷ Sb0-2-43-1 ∷ X4 ∷ []) (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b2 = at 0 3 (CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S2 ∷ CS24⁻ ∷ []) (CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS2-S3: 15 steps
lem-F4-CS2-S3 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-S3 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) (X4 ∷ CCZ024 ∷ Toff013 ∷ S3 ∷ CS34⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S3 ∷ CS34⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ []) (S3 ∷ CS34⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 6 (S3 ∷ CS34⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ S3 ∷ CS34⁻ ∷ []) (S3 ∷ CS34⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 3 (S3 ∷ CS34⁻ ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ S3 ∷ CS34⁻ ∷ []) (S3 ∷ CS34⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (S3 ∷ CS34⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ S3 ∷ CS34⁻ ∷ []) (S3 ∷ CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff013 ∷ S3 ∷ CS34⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b1 = at 2 3 (S3 ∷ CS34⁻ ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ S3 ∷ CS34⁻ ∷ []) (S3 ∷ CS34⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (S3 ∷ CS34⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ S3 ∷ CS34⁻ ∷ []) (S3 ∷ CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 3 (CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S3 ∷ CS34⁻ ∷ []) (CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- CKu-box-2 @122441: 7 steps
lem-CKu-box-2-at122441 : Complete 4 → ⟪ (CK40 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CK40 ∷ []) ⟫ʷ
lem-CKu-box-2-at122441 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CK40 ∷ [])
  b0 = at 0 1 (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0 ∷ CS04⁻ ∷ []) (pw1 c4 (CK40 ∷ []) (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-2431 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at122441 c4) ▸
       at 3 2 (Bx0-2431 ∷ K0 ∷ []) (lem-Ku-box-at122441 c4) ▸
       at 2 2 (Bx0-2431 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at122441 c4) ▸
       at 1 2 (Bx0-2431 ∷ K0⁻ ∷ []) (lem-Kdu-box-at122441 c4) ▸
       at 0 2 (Bx0-2431 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at122441 c4) ▸
       at 1 5 (CK40 ∷ []) (pw1 c4 (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0 ∷ CS04⁻ ∷ []) (CK40 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS2-K0: 20 steps
lem-F4-CS2-K0 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-K0 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ []) (X4 ∷ Bx0-2431 ∷ K0 ∷ CK40 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K0 ∷ CK40 ∷ S4 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 5 4 (K0 ∷ CK40 ∷ S4 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 4 (K0 ∷ CK40 ∷ S4 ∷ Toff134 ∷ []) (pw2 c4 (Toff134 ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (K0 ∷ CK40 ∷ S4 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (K0 ∷ CK40 ∷ S4 ∷ Toff134 ∷ []) (pw2 c4 (Toff134 ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ K0 ∷ CK40 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b1 = at 1 2 (K0 ∷ Bx0-2431 ∷ []) (sym (lem-Ku-box-at122441 c4)) ▸
       at 2 2 (CK40 ∷ Bx0-2431 ∷ []) (sym (lem-CKu-box-2-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 6 2 (S4 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ S4 ∷ []) (S4 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (S4 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ S4 ∷ []) (S4 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (S4 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ S4 ∷ []) (S4 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (S4 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ S4 ∷ []) (S4 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done

  b2 : Chain (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b2 = at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 4 (CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS2-K1: 21 steps
lem-F4-CS2-K1 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-K1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ []) (X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K1 ∷ CK41 ∷ S4 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ []) (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 7 (K1 ∷ CK41 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ K1 ∷ CK41 ∷ S4 ∷ []) (K1 ∷ CK41 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 1 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸
       at 4 4 (K1 ∷ CK41 ∷ S4 ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ K1 ∷ CK41 ∷ S4 ∷ []) (K1 ∷ CK41 ∷ S4 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K1 ∷ CK41 ∷ S4 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ Bx0-2341 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b1 = at 3 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CK41 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CK41 c4) ▸
       at 5 2 (S4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 2 4 (K1 ∷ CK41 ∷ S4 ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ K1 ∷ CK41 ∷ S4 ∷ []) (K1 ∷ CK41 ∷ S4 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CK41 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CK41 c4) ▸
       at 3 2 (S4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 4 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸ done

  b2 : Chain (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ Bx0-2341 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b2 = at 4 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 4 (CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ []) (CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS2-K2: 19 steps
lem-F4-CS2-K2 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-K2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ K2 ∷ CK42 ∷ Toff013 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K2 ∷ CK42 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 7 (K2 ∷ CK42 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CK42 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CK42 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ K2 ∷ CK42 ∷ Toff013 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b1 = at 6 2 (S4 ∷ Toff013 ∷ []) (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (S)) ▸
       at 3 4 (K2 ∷ CK42 ∷ S4 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CK42 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CK42 c4) ▸
       at 4 2 (S4 ∷ Toff013 ∷ []) (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (S)) ▸
       at 1 4 (K2 ∷ CK42 ∷ S4 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b2 = at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 4 (CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ []) (CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS2-K3: 21 steps
lem-F4-CS2-K3 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-K3 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K3 ∷ CK43 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ []) (K3 ∷ CK43 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 7 (K3 ∷ CK43 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ K3 ∷ CK43 ∷ S4 ∷ []) (K3 ∷ CK43 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-box-perm-1423-at122441 c4) ▸
       at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at12213443 c4) ▸
       at 4 4 (K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ K3 ∷ CK43 ∷ S4 ∷ []) (K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ Bx0-2143 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b1 = at 3 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 4 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸
       at 5 2 (S4 ∷ CCZ012 ∷ []) (c₃ (CCZ) (S ↑)) ▸
       at 2 4 (K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ K3 ∷ CK43 ∷ S4 ∷ []) (K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 2 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸
       at 3 2 (S4 ∷ CCZ012 ∷ []) (c₃ (CCZ) (S ↑)) ▸
       at 4 4 (Bx0-2143 ∷ []) (sym (lem-box-cP-at12213443 c4)) ▸ done

  b2 : Chain (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ Bx0-2143 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b2 = at 4 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1423-at122441 c4)) ▸
       at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 4 (CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ []) (CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS0-CS0: 286 steps
lem-F4-CS0-CS0 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-CS0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) (lw4 c4 (CZ02 ∷ Toff213 ∷ []) (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 6 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Sb2-0-41-3 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Sb2-0-41-3 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b1 = at 10 2 (CCZ024 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 c4) ▸
       at 7 2 (CCZ024 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 c4) ▸
       at 7 5 (CCZ013 ∷ []) (lw4 c4 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ CZ02 ∷ []) (pw3 c4 (CZ02 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (X4 ∷ Sb2-0-41-3 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CCZ024 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b2 = at 5 3 (X4 ∷ []) (lw3 c4 (X4 ∷ CZ02 ∷ CZ02 ∷ []) (X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff213 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 2 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 6 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 5 2 (CCZ024 ∷ CS03⁻ ∷ []) (pw1 c4 (CS03⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CCZ024 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b3 = at 6 2 (Toff213 ∷ CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CS03⁻ ∷ []) (pw1 c4 (CS03⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff213 ∷ CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ024 ∷ K3⁻ ∷ []) (pw1 c4 (K3⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b4 = at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ K3 ∷ []) (pw1 c4 (K3 ∷ CCZ024 ∷ []) (CCZ024 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 5 7 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ Toff213 ∷ []) (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ024 ∷ Toff314 ∷ Toff213 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b5 = at 13 2 (CCZ024 ∷ K3⁻ ∷ []) (pw1 c4 (K3⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 12 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 10 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 8 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ K3 ∷ []) (pw1 c4 (K3 ∷ CCZ024 ∷ []) (CCZ024 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 8 7 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ024 ∷ Toff314 ∷ Toff213 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b6 = at 6 2 (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (pw3 c4 (Toff214 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ Toff213 ∷ []) (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Toff213 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ Toff213 ∷ []) (Toff213 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 c4) ▸
       at 10 2 (Toff213 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 c4) ▸
       at 8 2 (Toff213 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ Toff213 ∷ []) (Toff213 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b7 = at 9 5 (CCZ014 ∷ []) (pw2 c4 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff213 ∷ Toff214 ∷ []) (lw0 c4 (Toff214 ∷ Toff213 ∷ []) (Toff213 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CCZ014 ∷ []) (pw3 c4 (Toff214 ∷ CCZ014 ∷ Toff214 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 3 2 (CCZ024 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff213 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ Toff213 ∷ []) (Toff213 ∷ CS03 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b8 = at 5 2 (CCZ024 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff213 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ Toff213 ∷ []) (Toff213 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 2 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ K3⁻ ∷ []) (pw1 c4 (K3⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸ done

  b9 : Chain (X4 ∷ Bx2-0413 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b9 = at 5 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 3 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ K3 ∷ []) (pw1 c4 (K3 ∷ CCZ024 ∷ []) (CCZ024 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 3 7 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ Toff213 ∷ []) (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CCZ024 ∷ K3⁻ ∷ []) (pw1 c4 (K3⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b10 = at 10 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 8 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 6 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ K3 ∷ []) (pw1 c4 (K3 ∷ CCZ024 ∷ []) (CCZ024 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (pw3 c4 (Toff214 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b11 = at 7 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ Toff213 ∷ []) (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Toff213 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ Toff213 ∷ []) (Toff213 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 c4) ▸
       at 8 2 (Toff213 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 c4) ▸
       at 6 2 (Toff213 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ Toff213 ∷ []) (Toff213 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 7 5 (CCZ014 ∷ []) (pw2 c4 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Bx2-0413 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b12 = at 5 2 (Toff213 ∷ Toff214 ∷ []) (lw0 c4 (Toff214 ∷ Toff213 ∷ []) (Toff213 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CCZ014 ∷ []) (pw3 c4 (Toff214 ∷ CCZ014 ∷ Toff214 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) (lw4 c4 (CZ02 ∷ Toff213 ∷ []) (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 4 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) tt tt Eq.refl) ▸ done

  b13 : Chain (CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Bx2-0413 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff213 ∷ Bx2-0413 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b13 = at 8 2 (CCZ024 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 c4) ▸
       at 5 5 (CCZ013 ∷ []) (lw4 c4 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CZ02 ∷ []) (pw3 c4 (CZ02 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸ done

  b14 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff213 ∷ Bx2-0413 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CCZ024 ∷ CX01 ∷ CS03 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b14 = at 3 3 (X4 ∷ []) (lw3 c4 (X4 ∷ CZ02 ∷ CZ02 ∷ []) (X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff213 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 2 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl) ▸ done

  b15 : Chain (Bx2-0413 ∷ X4 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CCZ024 ∷ CX01 ∷ CS03 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CCZ024 ∷ CX01 ∷ CS03 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b15 = at 4 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 c4) ▸
       at 3 2 (CCZ024 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 c4) ▸
       at 3 5 (CCZ013 ∷ []) (lw4 c4 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl) ▸ done

  b16 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CCZ024 ∷ CX01 ∷ CS03 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ Bx2-0413 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b16 = at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 c4) ▸
       at 5 5 (CCZ013 ∷ []) (lw4 c4 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff213 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 8 (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 10 2 [] (lw4 c4 (CCZ013 ∷ CCZ013 ∷ []) [] tt tt Eq.refl) ▸ done

  b17 : Chain (Bx2-0413 ∷ X4 ∷ Bx2-0413 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CX13 ∷ Toff314 ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b17 = at 3 3 (Toff314 ∷ CS03 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ Toff314 ∷ CS03 ∷ []) (Toff314 ∷ CS03 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 6 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 3 2 (CX13 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ []) (CX13 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (CS03 ∷ []) (refl) ▸ done

  b18 : Chain (Bx2-0413 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CX13 ∷ Toff314 ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ Toff314 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b18 = at 6 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 6 (CX13 ∷ Toff314 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX13 ∷ Toff314 ∷ []) (CX13 ∷ Toff314 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 5 2 (CX12 ∷ CX13 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CX13 ∷ []) (CX12 ∷ CX13 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ Toff314 ∷ []) (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CX12 ∷ []) (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 7 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b19 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ Toff314 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b19 = at 10 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K3 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CS34 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 12 2 (CS34⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 14 2 (CS14 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K3⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b20 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX12 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff213 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b20 = at 9 7 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX12 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CX12 ∷ []) (CX12 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS14 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ CS14 ∷ []) (CS14 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 c4) ▸
       at 6 2 (CS14⁻ ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 c4) ▸
       at 8 2 (CS01 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CS01 ∷ []) (CS01 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸ done

  b21 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX12 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff213 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ CX13 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ Toff213 ∷ CS01 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b21 = at 4 5 (CCZ014 ∷ []) (pw2 c4 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX12 ∷ CX13 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CX13 ∷ []) (CX12 ∷ CX13 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff214 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ Toff214 ∷ []) (Toff214 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CS14 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ CS14 ∷ []) (CS14 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 c4) ▸
       at 10 2 (CS14⁻ ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 c4) ▸ done

  b22 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ CX13 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ Toff213 ∷ CS01 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CX13 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b22 = at 12 2 (CS01 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CS01 ∷ []) (CS01 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 8 5 (CCZ014 ∷ []) (pw2 c4 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ Toff314 ∷ []) (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CCZ014 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ CX12 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CCZ014 ∷ []) (pw3 c4 (Toff214 ∷ CCZ014 ∷ Toff214 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (CX13 ∷ Toff314 ∷ []) (pw2 c4 (CCZ014 ∷ CX13 ∷ CCZ014 ∷ Toff314 ∷ []) (CX13 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 4 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸ done

  b23 : Chain (Bx2-0413 ∷ X4 ∷ CX13 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CX13 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b23 = at 3 2 (K3 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS34 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 6 2 (CS34⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 8 2 (CS14 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K3⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 7 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸ done

  b24 : Chain (Bx2-0413 ∷ X4 ∷ CX13 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS03 ∷ X4 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b24 = at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 1 3 (Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ Toff314 ∷ []) (Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ []) (CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸ done

  b25 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS03 ∷ X4 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CS03 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b25 = at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 5 (CS03 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS03 ∷ []) (CS03 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 6 2 (CS03 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CS03 ∷ []) (CS03 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS03 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS03 ∷ []) (CS03 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS03 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CS03 ∷ []) (CS03 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS03 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS03 ∷ []) (CS03 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸ done

  b26 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CS03 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX13 ∷ Toff314 ∷ X4 ∷ CS03⁻ ∷ [])
  b26 = at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 2 2 (CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ []) (CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX13 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ []) (CX13 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 6 1 (CS03 ∷ []) (refl) ▸
       at 8 1 (CS03⁻ ∷ []) (refl) ▸ done

  b27 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX13 ∷ Toff314 ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b27 = at 5 6 (CX13 ∷ Toff314 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX13 ∷ Toff314 ∷ []) (CX13 ∷ Toff314 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 7 2 (CX12 ∷ CX13 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CX13 ∷ []) (CX12 ∷ CX13 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ Toff314 ∷ []) (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CX12 ∷ []) (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 9 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸ done

  b28 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b28 = at 11 2 (K3 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (CS34 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 14 2 (CS34⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 16 2 (CS14 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K3⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 11 7 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸ done

  b29 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ Toff213 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b29 = at 5 2 (CX12 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CX12 ∷ []) (CX12 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS14 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ CS14 ∷ []) (CS14 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 c4) ▸
       at 8 2 (CS14⁻ ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 c4) ▸
       at 10 2 (CS01 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CS01 ∷ []) (CS01 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ014 ∷ []) (pw2 c4 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸ done

  b30 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ Toff213 ∷ CX13 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ CX13 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff213 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b30 = at 7 2 (CX12 ∷ CX13 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CX13 ∷ []) (CX12 ∷ CX13 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff214 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ Toff214 ∷ []) (Toff214 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CS14 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ CS14 ∷ []) (CS14 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 c4) ▸
       at 12 2 (CS14⁻ ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 c4) ▸
       at 14 2 (CS01 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CS01 ∷ []) (CS01 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸ done

  b31 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ CX13 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff213 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CX13 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b31 = at 10 5 (CCZ014 ∷ []) (pw2 c4 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ Toff314 ∷ []) (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CCZ014 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ CX12 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CCZ014 ∷ []) (pw3 c4 (Toff214 ∷ CCZ014 ∷ Toff214 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CX13 ∷ Toff314 ∷ []) (pw2 c4 (CCZ014 ∷ CX13 ∷ CCZ014 ∷ Toff314 ∷ []) (CX13 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K3 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b32 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CX13 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CX13 ∷ Toff314 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b32 = at 6 2 (CS34 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 7 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸ done

  b33 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CX13 ∷ Toff314 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS03⁻ ∷ X4 ∷ [])
  b33 = at 8 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 10 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 6 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 3 3 (Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ Toff314 ∷ []) (Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 9 1 (CS03⁻ ∷ []) (refl) ▸ done

  b34 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS03⁻ ∷ X4 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ X4 ∷ CS03⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b34 = at 6 5 (CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 8 2 (CS03⁻ ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS03⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS03⁻ ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS03⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 8 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b35 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ X4 ∷ CS03⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b35 = at 10 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 6 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 4 2 (CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- box-perm-2314 @0210243143: 2 steps
lem-box-perm-2314-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-box-perm-2314-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-4103 ∷ [])
  b0 = at 0 1 (Bx2-4013 ∷ []) (lem-sym-ab-at0210243143 c4) ▸
       at 0 1 (Bx2-4103 ∷ []) (lem-sym-bc-at0214203143 c4) ▸ done


-- cQ @0314213042: 7 steps
lem-cQ-at0314213042 : Complete 4 → ⟪ (CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ
lem-cQ-at0314213042 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 c4) ▸
       at 2 2 (CCZ023 ∷ CS13⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 c4) ▸
       at 0 2 (CCZ023 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ134 ∷ []) (lw0 c4 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @0314213042: 13 steps
lem-box-tQ-at0314213042 : Complete 4 → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at0314213042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4102 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx4-302 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (pw1 c4 (CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (pw1 c4 (CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff314 ∷ CCZ134 ∷ CZ14 ∷ []) (lw0 c4 (CCZ134 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ134 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 c4) ▸
       at 1 2 (CCZ023 ∷ CCZ134 ∷ []) (lem-cQ-at0314213042 c4) ▸
       at 2 4 (Toff314 ∷ []) (lw0 c4 (CCZ134 ∷ CZ14 ∷ Toff314 ∷ CCZ134 ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸ done


-- CXbc-box @0314213042: 17 steps
lem-CXbc-box-at0314213042 : Complete 4 → ⟪ (CX10 ∷ Bx3-4102 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at0314213042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX10 ∷ Bx3-4102 ∷ CX10 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CX10 ∷ CCZ123 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CCZ023 ∷ CX41 ∷ CS24 ∷ CX10 ∷ [])
  b0 = at 1 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213042 c4) ▸
       at 0 2 (Toff314 ∷ CX10 ∷ []) (pw2 c4 (CX10 ∷ Toff314 ∷ []) (Toff314 ∷ CX10 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ CX10 ∷ CCZ123 ∷ []) (lw4 c4 (CX10 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX10 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff314 ∷ CCZ123 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ123 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ123 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff314 ∷ CX10 ∷ []) (pw2 c4 (CX10 ∷ Toff314 ∷ []) (Toff314 ∷ CX10 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ023 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 c4) ▸ done

  b1 : Chain (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CX10 ∷ CCZ123 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CCZ023 ∷ CX41 ∷ CS24 ∷ CX10 ∷ []) (Bx3-4102 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ [])
  b1 = at 7 2 (CCZ023 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 c4) ▸
       at 5 2 (CCZ023 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ124 ∷ []) (lw0 c4 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ023 ∷ CX10 ∷ CCZ123 ∷ []) (lw4 c4 (CX10 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX10 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX10 ∷ []) (lw4 c4 (CX10 ∷ CCZ123 ∷ CCZ123 ∷ []) (CX10 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx3-4102 ∷ []) (sym (lem-box-tQ-at0314213042 c4)) ▸ done

  b2 : Chain (Bx3-4102 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ []) (Bx3-4102 ∷ CCZ124 ∷ [])
  b2 = at 1 3 (CCZ124 ∷ []) (pw3 c4 (CX10 ∷ CCZ124 ∷ CX10 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @0314213042: 18 steps
lem-CXcb-box-at0314213042 : Complete 4 → ⟪ (CX01 ∷ Bx3-4102 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXcb-box-at0314213042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX01 ∷ Bx3-4102 ∷ CX01 ∷ []) (Toff314 ∷ CCZ023 ∷ CX01 ∷ Toff304 ∷ CS02 ∷ CX40 ∷ Toff314 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ CCZ023 ∷ CX01 ∷ [])
  b0 = at 1 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213042 c4) ▸
       at 0 2 (Toff314 ∷ CX01 ∷ Toff304 ∷ []) (pw2 c4 (CX01 ∷ Toff314 ∷ []) (Toff314 ∷ CX01 ∷ Toff304 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ023 ∷ Toff304 ∷ CCZ024 ∷ []) (pw1 c4 (Toff304 ∷ CCZ023 ∷ []) (CCZ023 ∷ Toff304 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ CX01 ∷ []) (lw4 c4 (CX01 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (pw3 c4 (CCZ024 ∷ []) (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff314 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ Toff314 ∷ []) (Toff314 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff314 ∷ CX40 ∷ []) (pw2 c4 (CX40 ∷ Toff314 ∷ []) (Toff314 ∷ CX40 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff314 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF314 c4) ▸ done

  b1 : Chain (Toff314 ∷ CCZ023 ∷ CX01 ∷ Toff304 ∷ CS02 ∷ CX40 ∷ Toff314 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ CCZ023 ∷ CX01 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ CX01 ∷ CCZ024 ∷ CX01 ∷ [])
  b1 = at 5 2 (Toff314 ∷ CX40 ∷ []) (pw2 c4 (CX40 ∷ Toff314 ∷ []) (Toff314 ∷ CX40 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff314 ∷ CS02 ∷ []) (lem-comm-CS02-TOFF314 c4) ▸
       at 5 5 (CCZ024 ∷ []) (pw3 c4 (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff314 ∷ Toff304 ∷ []) (pw2 c4 (Toff304 ∷ Toff314 ∷ []) (Toff314 ∷ Toff304 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff314 ∷ CX01 ∷ Toff304 ∷ []) (pw2 c4 (CX01 ∷ Toff314 ∷ []) (Toff314 ∷ CX01 ∷ Toff304 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX01 ∷ []) (pw2 c4 (CX01 ∷ Toff304 ∷ Toff304 ∷ []) (CX01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ023 ∷ CX01 ∷ []) (lw4 c4 (CX01 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX01 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ CX01 ∷ CCZ024 ∷ CX01 ∷ []) (Bx3-4102 ∷ CCZ024 ∷ [])
  b2 = at 0 4 (Bx3-4102 ∷ []) (sym (lem-box-tQ-at0314213042 c4)) ▸
       at 1 3 (CCZ024 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ CX01 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @0314213042: 11 steps
lem-SWbc-box-at0314213042 : Complete 4 → ⟪ (Sw01 ∷ Bx3-4102 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-SWbc-box-at0314213042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx3-4102 ∷ Sw01 ∷ []) (CX10 ∷ Bx3-4102 ∷ CX10 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (lw4 c4 (Sw01 ∷ []) (CX10 ∷ CX01 ∷ CX10 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (lw4 c4 (Sw01 ∷ []) (CX10 ∷ CX01 ∷ CX10 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx3-4102 ∷ CCZ124 ∷ []) (lem-CXbc-box-at0314213042 c4) ▸
       at 3 2 (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CX01 ∷ []) (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx3-4102 ∷ CCZ024 ∷ []) (lem-CXcb-box-at0314213042 c4) ▸
       at 4 2 (CX10 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CX10 ∷ []) (CX10 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CX10 ∷ []) (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CX10 ∷ []) (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX10 ∷ Bx3-4102 ∷ CX10 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ []) (Bx3-4102 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx3-4102 ∷ CCZ124 ∷ []) (lem-CXbc-box-at0314213042 c4) ▸
       at 1 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @0314213042: 23 steps
lem-nat-SWbc-at0314213042 : Complete 4 → ⟪ (Sw01 ∷ Bx3-4102 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-nat-SWbc-at0314213042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ Bx3-4102 ∷ Sw01 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ Sw01 ∷ CCZ034 ∷ Bx3-42 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx4-302 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff304 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ Toff314 ∷ []) (Toff304 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (refl) ▸
       at 2 2 (CCZ134 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff413 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ Toff403 ∷ []) (Toff413 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 5 2 (Toff413 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ Toff403 ∷ []) (Toff413 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ Sw01 ∷ CCZ034 ∷ Bx3-42 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ Sw01 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ Toff304 ∷ CCZ034 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Sw01 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CCZ134 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 8 2 (Toff304 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ Toff314 ∷ []) (Toff304 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ034 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (refl) ▸
       at 10 2 (CCZ134 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff413 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ Toff403 ∷ []) (Toff413 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸ done

  b2 : Chain (CCZ034 ∷ Toff304 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ Toff304 ∷ CCZ034 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Sw01 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ Sw01 ∷ []) (Bx3-4012 ∷ [])
  b2 = at 13 2 (Toff413 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ Toff403 ∷ []) (Toff413 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ134 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 16 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx4-312 ∷ []) (refl) ▸
       at 5 6 (Bx4-312 ∷ []) (refl) ▸
       at 0 6 (Bx3-4012 ∷ []) (refl) ▸ done


-- sym-bc @0314213042: 2 steps
lem-sym-bc-at0314213042 : Complete 4 → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-sym-bc-at0314213042 c4 = run b0
  where
  b0 : Chain (Bx3-4102 ∷ []) (Bx3-4012 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx3-4102 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at0314213042 c4)) ▸
       at 0 3 (Bx3-4012 ∷ []) (lem-nat-SWbc-at0314213042 c4) ▸ done


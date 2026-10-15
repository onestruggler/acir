{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D038 where

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
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-box-cP-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-box-cP-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-CSdu-box-2-at122441 ; lem-CSdu-box-2-at243243 ; lem-Su-box-at122441 ; lem-Su-box-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D026 using (lem-CSdu-box-2-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D028 using (lem-Kdu-box-at243243 ; lem-Ku-box-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D032 using (lem-Kdu-box-at0210243143 ; lem-Ku-box-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D034 using (lem-box-cP-at233442 ; lem-box-perm-1423-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D035 using (lem-box-cP-at0210213443 ; lem-box-perm-1324-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D036 using (lem-box-perm-1324-at243243)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-comm-TOFF023-CSd14)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-comm-CCZ013-CK42 ; lem-comm-TOFF023-CK41)
-- CKu-box-2 @0210243143: 7 steps
lem-CKu-box-2-at0210243143 : Complete 4 → ⟪ (CK42 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CK42 ∷ []) ⟫ʷ
lem-CKu-box-2-at0210243143 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CK42 ∷ [])
  b0 = at 0 1 (CS24⁻ ∷ K2⁻ ∷ CS24⁻ ∷ K2 ∷ CS24⁻ ∷ []) (lw0 c4 (CK42 ∷ []) (CS24⁻ ∷ K2⁻ ∷ CS24⁻ ∷ K2 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx2-0413 ∷ CS24⁻ ∷ []) (lem-CSdu-box-2-at0210243143 c4) ▸
       at 3 2 (Bx2-0413 ∷ K2 ∷ []) (lem-Ku-box-at0210243143 c4) ▸
       at 2 2 (Bx2-0413 ∷ CS24⁻ ∷ []) (lem-CSdu-box-2-at0210243143 c4) ▸
       at 1 2 (Bx2-0413 ∷ K2⁻ ∷ []) (lem-Kdu-box-at0210243143 c4) ▸
       at 0 2 (Bx2-0413 ∷ CS24⁻ ∷ []) (lem-CSdu-box-2-at0210243143 c4) ▸
       at 1 5 (CK42 ∷ []) (lw0 c4 (CS24⁻ ∷ K2⁻ ∷ CS24⁻ ∷ K2 ∷ CS24⁻ ∷ []) (CK42 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS0-K2: 20 steps
lem-F4-CS0-K2 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-K2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ []) (X4 ∷ Bx2-0413 ∷ K2 ∷ CK42 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K2 ∷ CK42 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 5 4 (K2 ∷ CK42 ∷ S4 ∷ CS03⁻ ∷ []) (pw1 c4 (CS03⁻ ∷ K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 4 (K2 ∷ CK42 ∷ S4 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (K2 ∷ CK42 ∷ S4 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (K2 ∷ CK42 ∷ S4 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ K2 ∷ CK42 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b1 = at 1 2 (K2 ∷ Bx2-0413 ∷ []) (sym (lem-Ku-box-at0210243143 c4)) ▸
       at 2 2 (CK42 ∷ Bx2-0413 ∷ []) (sym (lem-CKu-box-2-at0210243143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 6 2 (S4 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ S4 ∷ []) (S4 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (S4 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ S4 ∷ []) (S4 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (S4 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ S4 ∷ []) (S4 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (S4 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ S4 ∷ []) (S4 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸ done

  b2 : Chain (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b2 = at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 4 (CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ []) (CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS0-K3: 21 steps
lem-F4-CS0-K3 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-K3 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ []) (X4 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ K3 ∷ CK43 ∷ S4 ∷ Toff234 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K3 ∷ CK43 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ []) (K3 ∷ CK43 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 7 (K3 ∷ CK43 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ K3 ∷ CK43 ∷ S4 ∷ []) (K3 ∷ CK43 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-0143 ∷ []) (lem-box-perm-1324-at0210243143 c4) ▸
       at 1 1 (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at0210213443 c4) ▸
       at 4 4 (K3 ∷ CK43 ∷ S4 ∷ Toff234 ∷ []) (lw0 c4 (Toff234 ∷ K3 ∷ CK43 ∷ S4 ∷ []) (K3 ∷ CK43 ∷ S4 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ K3 ∷ CK43 ∷ S4 ∷ Toff234 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ Bx2-0143 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b1 = at 3 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 4 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸
       at 5 2 (S4 ∷ CCZ012 ∷ []) (c₃ (CCZ) (S ↑)) ▸
       at 2 4 (K3 ∷ CK43 ∷ S4 ∷ Toff234 ∷ []) (lw0 c4 (Toff234 ∷ K3 ∷ CK43 ∷ S4 ∷ []) (K3 ∷ CK43 ∷ S4 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 2 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸
       at 3 2 (S4 ∷ CCZ012 ∷ []) (c₃ (CCZ) (S ↑)) ▸
       at 4 4 (Bx2-0143 ∷ []) (sym (lem-box-cP-at0210213443 c4)) ▸ done

  b2 : Chain (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ Bx2-0143 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b2 = at 4 1 (Bx2-0413 ∷ []) (sym (lem-box-perm-1324-at0210243143 c4)) ▸
       at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 4 (CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ []) (CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS1-I: 17 steps
lem-F4-CS1-I : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-I c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ ι ∷ S4⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (ι ∷ S4⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ S4 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 2 6 (ι1 ∷ S4⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (pw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ ι1 ∷ S4⁻ ∷ []) (ι1 ∷ S4⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ ι ∷ S4⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ ι ∷ S4⁻ ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b1 = at 4 3 (ι ∷ S4⁻ ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (ι ∷ S4⁻ ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (ι ∷ S4⁻ ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (ι ∷ S4⁻ ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ ι ∷ S4⁻ ∷ Sb0-1-42-3 ∷ X4 ∷ []) (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b2 = at 0 3 (S4 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ ι ∷ S4⁻ ∷ []) (S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS1-S0: 14 steps
lem-F4-CS1-S0 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-S0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ []) (X4 ∷ Bx0-1423 ∷ S0 ∷ CS04⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S0 ∷ CS04⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS04 ∷ []) (S0 ∷ CS04⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 3 (S0 ∷ CS04⁻ ∷ CS13⁻ ∷ []) (pw2 c4 (CS13⁻ ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 3 (S0 ∷ CS04⁻ ∷ Toff324 ∷ []) (pw1 c4 (Toff324 ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (S0 ∷ CS04⁻ ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (S0 ∷ CS04⁻ ∷ Toff324 ∷ []) (pw1 c4 (Toff324 ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ Toff324 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ S0 ∷ CS04⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b1 = at 1 2 (S0 ∷ Bx0-1423 ∷ []) (sym (lem-Su-box-at243243 c4)) ▸
       at 2 2 (CS04⁻ ∷ Bx0-1423 ∷ []) (sym (lem-CSdu-box-2-at243243 c4)) ▸
       at 5 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 3 (CS04 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ S0 ∷ CS04⁻ ∷ []) (CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS1-S1: 17 steps
lem-F4-CS1-S1 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-S1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ S1 ∷ CS14⁻ ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S1 ∷ CS14⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS14 ∷ []) (S1 ∷ CS14⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 6 (S1 ∷ CS14⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (lw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S1 ∷ CS14⁻ ∷ []) (S1 ∷ CS14⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 2 (S1 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ S1 ∷ []) (S1 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS14⁻ ∷ Toff023 ∷ []) (lem-comm-TOFF023-CSd14 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ S1 ∷ CS14⁻ ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ S1 ∷ CS14⁻ ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b1 = at 3 3 (S1 ∷ CS14⁻ ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ S1 ∷ CS14⁻ ∷ []) (S1 ∷ CS14⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (S1 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ S1 ∷ []) (S1 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS14⁻ ∷ Toff023 ∷ []) (lem-comm-TOFF023-CSd14 c4) ▸
       at 1 3 (S1 ∷ CS14⁻ ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ S1 ∷ CS14⁻ ∷ []) (S1 ∷ CS14⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ S1 ∷ CS14⁻ ∷ Sb0-1-42-3 ∷ X4 ∷ []) (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b2 = at 0 3 (CS14 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S1 ∷ CS14⁻ ∷ []) (CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS1-S2: 15 steps
lem-F4-CS1-S2 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-S2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (X4 ∷ CCZ014 ∷ Toff023 ∷ S2 ∷ CS24⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S2 ∷ CS24⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ []) (S2 ∷ CS24⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 6 (S2 ∷ CS24⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (lw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 3 (S2 ∷ CS24⁻ ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (S2 ∷ CS24⁻ ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ CCZ014 ∷ Toff023 ∷ S2 ∷ CS24⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b1 = at 2 3 (S2 ∷ CS24⁻ ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (S2 ∷ CS24⁻ ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 3 (CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S2 ∷ CS24⁻ ∷ []) (CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS1-S3: 15 steps
lem-F4-CS1-S3 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-S3 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ []) (X4 ∷ CCZ014 ∷ Toff023 ∷ S3 ∷ CS34⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S3 ∷ CS34⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ []) (S3 ∷ CS34⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 6 (S3 ∷ CS34⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (lw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S3 ∷ CS34⁻ ∷ []) (S3 ∷ CS34⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 3 (S3 ∷ CS34⁻ ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ S3 ∷ CS34⁻ ∷ []) (S3 ∷ CS34⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (S3 ∷ CS34⁻ ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ S3 ∷ CS34⁻ ∷ []) (S3 ∷ CS34⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ CCZ014 ∷ Toff023 ∷ S3 ∷ CS34⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b1 = at 2 3 (S3 ∷ CS34⁻ ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ S3 ∷ CS34⁻ ∷ []) (S3 ∷ CS34⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (S3 ∷ CS34⁻ ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ S3 ∷ CS34⁻ ∷ []) (S3 ∷ CS34⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 3 (CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S3 ∷ CS34⁻ ∷ []) (CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- CKu-box-2 @243243: 7 steps
lem-CKu-box-2-at243243 : Complete 4 → ⟪ (CK40 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CK40 ∷ []) ⟫ʷ
lem-CKu-box-2-at243243 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CK40 ∷ [])
  b0 = at 0 1 (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0 ∷ CS04⁻ ∷ []) (pw1 c4 (CK40 ∷ []) (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-1423 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at243243 c4) ▸
       at 3 2 (Bx0-1423 ∷ K0 ∷ []) (lem-Ku-box-at243243 c4) ▸
       at 2 2 (Bx0-1423 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at243243 c4) ▸
       at 1 2 (Bx0-1423 ∷ K0⁻ ∷ []) (lem-Kdu-box-at243243 c4) ▸
       at 0 2 (Bx0-1423 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at243243 c4) ▸
       at 1 5 (CK40 ∷ []) (pw1 c4 (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0 ∷ CS04⁻ ∷ []) (CK40 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS1-K0: 20 steps
lem-F4-CS1-K0 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-K0 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ []) (X4 ∷ Bx0-1423 ∷ K0 ∷ CK40 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K0 ∷ CK40 ∷ S4 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 4 (K0 ∷ CK40 ∷ S4 ∷ CS13⁻ ∷ []) (pw2 c4 (CS13⁻ ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 4 (K0 ∷ CK40 ∷ S4 ∷ Toff324 ∷ []) (pw1 c4 (Toff324 ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (K0 ∷ CK40 ∷ S4 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (K0 ∷ CK40 ∷ S4 ∷ Toff324 ∷ []) (pw1 c4 (Toff324 ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ K0 ∷ CK40 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b1 = at 1 2 (K0 ∷ Bx0-1423 ∷ []) (sym (lem-Ku-box-at243243 c4)) ▸
       at 2 2 (CK40 ∷ Bx0-1423 ∷ []) (sym (lem-CKu-box-2-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 6 2 (S4 ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ S4 ∷ []) (S4 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (S4 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ S4 ∷ []) (S4 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (S4 ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ S4 ∷ []) (S4 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (S4 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ S4 ∷ []) (S4 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done

  b2 : Chain (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b2 = at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 4 (CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS1-K1: 19 steps
lem-F4-CS1-K1 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-K1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ CK41 ∷ Toff023 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ []) (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 7 (K1 ∷ CK41 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (lw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ K1 ∷ CK41 ∷ S4 ∷ []) (K1 ∷ CK41 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 2 (K1 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ K1 ∷ []) (K1 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CK41 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CK41 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ CK41 ∷ Toff023 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b1 = at 6 2 (S4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 3 4 (K1 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ K1 ∷ CK41 ∷ S4 ∷ []) (K1 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (K1 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ K1 ∷ []) (K1 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CK41 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CK41 c4) ▸
       at 4 2 (S4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 1 4 (K1 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ K1 ∷ CK41 ∷ S4 ∷ []) (K1 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b2 = at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 4 (CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ []) (CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS1-K2: 21 steps
lem-F4-CS1-K2 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-K2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K2 ∷ CK42 ∷ S4 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K2 ∷ CK42 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 7 (K2 ∷ CK42 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (lw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-1342 ∷ []) (lem-box-perm-1423-at243243 c4) ▸
       at 1 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at233442 c4) ▸
       at 4 4 (K2 ∷ CK42 ∷ S4 ∷ Toff024 ∷ []) (pw1 c4 (Toff024 ∷ K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K2 ∷ CK42 ∷ S4 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ Bx0-1342 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b1 = at 3 2 (K2 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CK42 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CK42 c4) ▸
       at 5 2 (S4 ∷ CCZ013 ∷ []) (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (S)) ▸
       at 2 4 (K2 ∷ CK42 ∷ S4 ∷ Toff024 ∷ []) (pw1 c4 (Toff024 ∷ K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K2 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CK42 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CK42 c4) ▸
       at 3 2 (S4 ∷ CCZ013 ∷ []) (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (S)) ▸
       at 4 4 (Bx0-1342 ∷ []) (sym (lem-box-cP-at233442 c4)) ▸ done

  b2 : Chain (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ Bx0-1342 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b2 = at 4 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1423-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 4 (CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ []) (CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS1-K3: 21 steps
lem-F4-CS1-K3 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-K3 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ []) (X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K3 ∷ CK43 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ []) (K3 ∷ CK43 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 7 (K3 ∷ CK43 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (lw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ K3 ∷ CK43 ∷ S4 ∷ []) (K3 ∷ CK43 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4) ▸
       at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at3443 c4) ▸
       at 4 4 (K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ K3 ∷ CK43 ∷ S4 ∷ []) (K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ Bx0-1243 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b1 = at 3 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 4 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸
       at 5 2 (S4 ∷ CCZ012 ∷ []) (c₃ (CCZ) (S ↑)) ▸
       at 2 4 (K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ K3 ∷ CK43 ∷ S4 ∷ []) (K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 2 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸
       at 3 2 (S4 ∷ CCZ012 ∷ []) (c₃ (CCZ) (S ↑)) ▸
       at 4 4 (Bx0-1243 ∷ []) (sym (lem-box-cP-at3443 c4)) ▸ done

  b2 : Chain (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ Bx0-1243 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b2 = at 4 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1324-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 4 (CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ []) (CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS2-I: 17 steps
lem-F4-CS2-I : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-I c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ ι ∷ S4⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (ι ∷ S4⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ S4 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 6 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 2 6 (ι1 ∷ S4⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (pw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ ι1 ∷ S4⁻ ∷ []) (ι1 ∷ S4⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ ι ∷ S4⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ ι ∷ S4⁻ ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b1 = at 4 3 (ι ∷ S4⁻ ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (ι ∷ S4⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (ι ∷ S4⁻ ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (ι ∷ S4⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ ι ∷ S4⁻ ∷ Sb0-2-43-1 ∷ X4 ∷ []) (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b2 = at 0 3 (S4 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ ι ∷ S4⁻ ∷ []) (S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS2-S0: 14 steps
lem-F4-CS2-S0 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-S0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ []) (X4 ∷ Bx0-2431 ∷ S0 ∷ CS04⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S0 ∷ CS04⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS04 ∷ []) (S0 ∷ CS04⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 5 3 (S0 ∷ CS04⁻ ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 3 (S0 ∷ CS04⁻ ∷ Toff134 ∷ []) (pw2 c4 (Toff134 ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (S0 ∷ CS04⁻ ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (S0 ∷ CS04⁻ ∷ Toff134 ∷ []) (pw2 c4 (Toff134 ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ Toff134 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ S0 ∷ CS04⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b1 = at 1 2 (S0 ∷ Bx0-2431 ∷ []) (sym (lem-Su-box-at122441 c4)) ▸
       at 2 2 (CS04⁻ ∷ Bx0-2431 ∷ []) (sym (lem-CSdu-box-2-at122441 c4)) ▸
       at 5 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 3 (CS04 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ S0 ∷ CS04⁻ ∷ []) (CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS2-S1: 15 steps
lem-F4-CS2-S1 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-S1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ []) (X4 ∷ CCZ024 ∷ Toff013 ∷ S1 ∷ CS14⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S1 ∷ CS14⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS14 ∷ []) (S1 ∷ CS14⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 6 (S1 ∷ CS14⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ S1 ∷ CS14⁻ ∷ []) (S1 ∷ CS14⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 3 (S1 ∷ CS14⁻ ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ S1 ∷ CS14⁻ ∷ []) (S1 ∷ CS14⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (S1 ∷ CS14⁻ ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ S1 ∷ CS14⁻ ∷ []) (S1 ∷ CS14⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff013 ∷ S1 ∷ CS14⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b1 = at 2 3 (S1 ∷ CS14⁻ ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ S1 ∷ CS14⁻ ∷ []) (S1 ∷ CS14⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (S1 ∷ CS14⁻ ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ S1 ∷ CS14⁻ ∷ []) (S1 ∷ CS14⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 3 (CS14 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S1 ∷ CS14⁻ ∷ []) (CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


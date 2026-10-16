{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D081 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-Cz-beta ; lem-sym23)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym12-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-X1-beta ; lem-sym12-at233442 ; lem-sym23-at2332 ; lem-sym34-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-BOXd-BOX-at0210243143 ; lem-SBtgt ; lem-SBtgtd ; lem-sym12-at2332 ; lem-sym23-at021021 ; lem-sym34-at233442)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-sym23-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-F5-CS01 ; lem-sym12-at0213203441 ; lem-sym12-at13213442 ; lem-sym34-at0210233441)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-CS12-beta-at021021 ; lem-sym23-at02102331 ; lem-sym34-at02102331)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-F5d-CS01)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-sym23-at0220 ; lem-sym23-at022330)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-sym34-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D079 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423 ; lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.D080 using (lem-Cz-beta-at0220 ; lem-auto-CS01-∣-BOX⟨2·1340⟩ ; lem-auto-CX01-∣-BOX⟨1·0234⟩ ; lem-auto-CX01-∣-TOFF234 ; lem-sym12-at02233440 ; lem-sym34-at022330 ; lem-sym34-at02233440)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-3-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-2-TOFF204 ; lem-nat-2-TOFF304)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF014 ; lem-nat-0-TOFF104 ; lem-nat-1-TOFF104 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-TOFF304 ; lem-nat-0-TOFF314)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-1-TOFF304)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-1-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0412⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-CS01)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-CS04 ; lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-CS04 ; lem-nat-1-CSd02 ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-2-CS02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨2·0341⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-1-CSd04 ; lem-nat-3-CSd04)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-0-CSd14 ; lem-nat-2-CS04 ; lem-nat-2-CSd04 ; lem-nat-3-CS03)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-nat-2-SBOXd⟨0·1·23·4⟩ ; lem-nat-2-SBOXd⟨0·1·32·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-BOX⟨2·3140⟩)
open import Examples.Groups.Clifford+CS.Five.D.R022 using (lem-nat-0-SBOXd⟨0·1·42·3⟩ ; lem-nat-0-SBOXd⟨1·0·42·3⟩ ; lem-nat-1-SBOXd⟨1·0·42·3⟩ ; lem-nat-1-SBOXd⟨2·0·41·3⟩ ; lem-nat-3-SBOXd⟨0·1·32·4⟩ ; lem-nat-3-SBOXd⟨0·1·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-1-BOX⟨3·0142⟩)
open import Examples.Groups.Clifford+CS.Five.D.R024 using (lem-nat-0-SBOX⟨2·1·40·3⟩ ; lem-nat-1-SBOX⟨1·2·40·3⟩ ; lem-nat-2-SBOX⟨1·3·40·2⟩ ; lem-nat-3-SBOX⟨1·4·30·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R025 using (lem-nat-1-SBOX⟨3·4·12·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R026 using (lem-nat-0-SBOX⟨2·4·01·3⟩ ; lem-nat-1-SBOX⟨2·4·10·3⟩ ; lem-nat-1-SBOX⟨3·4·21·0⟩ ; lem-nat-2-SBOX⟨1·4·20·3⟩ ; lem-nat-2-SBOX⟨2·4·31·0⟩ ; lem-nat-2-SBOX⟨3·4·21·0⟩ ; lem-nat-3-SBOX⟨2·3·41·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R027 using (lem-nat-0-SBOX⟨2·0·41·3⟩ ; lem-nat-0-SBOX⟨2·3·40·1⟩ ; lem-nat-0-SBOX⟨2·3·41·0⟩ ; lem-nat-0-SBOXd⟨2·0·41·3⟩ ; lem-nat-0-SBOXd⟨2·1·40·3⟩ ; lem-nat-0-SBOXd⟨2·4·10·3⟩ ; lem-nat-1-SBOX⟨1·3·40·2⟩ ; lem-nat-1-SBOX⟨2·1·40·3⟩ ; lem-nat-1-SBOX⟨2·3·40·1⟩ ; lem-nat-1-SBOXd⟨1·4·20·3⟩ ; lem-nat-1-SBOXd⟨2·1·40·3⟩ ; lem-nat-2-SBOX⟨1·2·40·3⟩ ; lem-nat-2-SBOXd⟨1·2·40·3⟩ ; lem-nat-2-SBOXd⟨1·4·30·2⟩ ; lem-nat-3-SBOX⟨2·4·31·0⟩ ; lem-nat-3-SBOXd⟨1·3·40·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R028 using (lem-nat-0-SBOXd⟨2·4·01·3⟩ ; lem-nat-1-BOX⟨3·0421⟩ ; lem-nat-1-SBOXd⟨1·2·40·3⟩ ; lem-nat-1-SBOXd⟨2·4·10·3⟩ ; lem-nat-2-BOX⟨2·0431⟩ ; lem-nat-2-BOXd⟨3·0412⟩ ; lem-nat-2-SBOXd⟨1·3·40·2⟩ ; lem-nat-2-SBOXd⟨1·4·20·3⟩ ; lem-nat-3-SBOXd⟨1·4·30·2⟩)
-- auto CS01 | SBOX(2;1;34;0): 9 steps
lem-auto-CS01-∣-SBOX⟨2·1·34·0⟩ : Complete 4 → ⟪ (CS01 ∷ Sb2-1-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-34-0 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·1·34·0⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS01 ∷ Sb2-1-34-0 ∷ []) (Bx2-1340 ∷ Toff034 ∷ Sb2-1-0-4 ∷ Toff034 ∷ Sb⁻2-1-0-4 ∷ CS01 ∷ [])
  b0 = at 1 1 (Bx2-1340 ∷ Toff034 ∷ Sb2-1-0-4 ∷ Toff034 ∷ Sb⁻2-1-0-4 ∷ []) (refl) ▸
       at 0 2 (Bx2-1340 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1340⟩ c4) ▸
       at 3 1 (CS01 ∷ []) (refl) ▸
       at 1 4 (Toff034 ∷ CS01 ∷ Toff034 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ Toff034 ∷ CS01 ∷ Toff034 ∷ []) (Toff034 ∷ CS01 ∷ Toff034 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-1-0-4 ∷ []) (refl) ▸
       at 5 1 (CS01⁻ ∷ []) (refl) ▸
       at 4 2 (CS01⁻ ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻2-1-0-4 ∷ []) (refl) ▸ done

  b1 : Chain (Bx2-1340 ∷ Toff034 ∷ Sb2-1-0-4 ∷ Toff034 ∷ Sb⁻2-1-0-4 ∷ CS01 ∷ []) (Sb2-1-34-0 ∷ CS01 ∷ [])
  b1 = at 0 5 (Sb2-1-34-0 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(2;0341): 5 steps
lem-auto-CS01-∣-BOX⟨2·0341⟩ : Complete 4 → ⟪ (CS01 ∷ Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·0341⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx2-0341 ∷ []) (Bx2-0341 ∷ CS01 ∷ [])
  b0 = at 1 1 (Bx2-0314 ∷ []) (lem-sym34-at0210233441 c4) ▸
       at 1 1 (Bx2-0134 ∷ []) (lem-sym23-at02102331 c4) ▸
       at 0 2 (Bx2-0134 ∷ CS01 ∷ []) (lem-CS12-beta-at021021 c4) ▸
       at 0 1 (Bx2-0314 ∷ []) (lem-sym23-at021021 c4) ▸
       at 0 1 (Bx2-0341 ∷ []) (lem-sym34-at02102331 c4) ▸ done


-- auto CS01 | SBOX(2;0;34;1): 9 steps
lem-auto-CS01-∣-SBOX⟨2·0·34·1⟩ : Complete 4 → ⟪ (CS01 ∷ Sb2-0-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-34-1 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·0·34·1⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS01 ∷ Sb2-0-34-1 ∷ []) (Bx2-0341 ∷ Toff134 ∷ Sb2-0-1-4 ∷ Toff134 ∷ Sb⁻2-0-1-4 ∷ CS01 ∷ [])
  b0 = at 1 1 (Bx2-0341 ∷ Toff134 ∷ Sb2-0-1-4 ∷ Toff134 ∷ Sb⁻2-0-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx2-0341 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨2·0341⟩ c4) ▸
       at 3 1 (CS01 ∷ []) (refl) ▸
       at 1 4 (Toff134 ∷ CS01 ∷ Toff134 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ Toff134 ∷ CS01 ∷ Toff134 ∷ []) (Toff134 ∷ CS01 ∷ Toff134 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-0-1-4 ∷ []) (refl) ▸
       at 5 1 (CS01⁻ ∷ []) (refl) ▸
       at 4 2 (CS01⁻ ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻2-0-1-4 ∷ []) (refl) ▸ done

  b1 : Chain (Bx2-0341 ∷ Toff134 ∷ Sb2-0-1-4 ∷ Toff134 ∷ Sb⁻2-0-1-4 ∷ CS01 ∷ []) (Sb2-0-34-1 ∷ CS01 ∷ [])
  b1 = at 0 5 (Sb2-0-34-1 ∷ []) (refl) ▸ done


-- auto CX01 | TOFF234 @2332: 7 steps
lem-auto-CX01-∣-TOFF234-at2332 : Complete 4 → ⟪ (CX01 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CX01 ∷ []) ⟫ʷ
lem-auto-CX01-∣-TOFF234-at2332 c4 = run b0
  where
  b0 : Chain (CX01 ∷ Toff324 ∷ []) (Toff324 ∷ CX01 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 2 2 (Toff234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ CX01 ∷ []) (lem-auto-CX01-∣-TOFF234 c4) ▸
       at 0 2 (Toff324 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CX01 | TOFF234 @243243: 7 steps
lem-auto-CX01-∣-TOFF234-at243243 : Complete 4 → ⟪ (CX01 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CX01 ∷ []) ⟫ʷ
lem-auto-CX01-∣-TOFF234-at243243 c4 = run b0
  where
  b0 : Chain (CX01 ∷ Toff423 ∷ []) (Toff423 ∷ CX01 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 2 2 (Toff324 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff423 ∷ []) (Toff324 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ CX01 ∷ []) (lem-auto-CX01-∣-TOFF234-at2332 c4) ▸
       at 0 2 (Toff423 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff324 ∷ []) (Toff423 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CX01 | SBOX(1;0;23;4): 11 steps
lem-auto-CX01-∣-SBOX⟨1·0·23·4⟩ : Complete 4 → ⟪ (CX01 ∷ Sb1-0-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-23-4 ∷ CX01 ∷ []) ⟫ʷ
lem-auto-CX01-∣-SBOX⟨1·0·23·4⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX01 ∷ Sb1-0-23-4 ∷ []) (Bx1-0234 ∷ Toff423 ∷ Sb1-0-4-3 ∷ Toff423 ∷ CX01 ∷ CS04⁻ ∷ [])
  b0 = at 1 1 (Bx1-0234 ∷ Toff423 ∷ Sb1-0-4-3 ∷ Toff423 ∷ Sb⁻1-0-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-0234 ∷ CX01 ∷ []) (lem-auto-CX01-∣-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (Toff423 ∷ CX01 ∷ []) (lem-auto-CX01-∣-TOFF234-at243243 c4) ▸
       at 3 1 (CS04 ∷ []) (refl) ▸
       at 2 2 (CS04 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CS04 ∷ []) (CS04 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-0-4-3 ∷ []) (refl) ▸
       at 3 2 (Toff423 ∷ CX01 ∷ []) (lem-auto-CX01-∣-TOFF234-at243243 c4) ▸
       at 5 1 (CS04⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx1-0234 ∷ Toff423 ∷ Sb1-0-4-3 ∷ Toff423 ∷ CX01 ∷ CS04⁻ ∷ []) (Sb1-0-23-4 ∷ CX01 ∷ [])
  b1 = at 4 2 (CS04⁻ ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻1-0-4-3 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-23-4 ∷ []) (refl) ▸ done


-- auto CCZ012 | BOX(0;3142): 7 steps
lem-auto-CCZ012-∣-BOX⟨0·3142⟩ : Complete 4 → ⟪ (CCZ012 ∷ Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨0·3142⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx0-3142 ∷ []) (Bx0-3142 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx0-1342 ∷ []) (lem-sym12-at13213442 c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym34-at233442 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 2 (Bx0-1234 ∷ CCZ012 ∷ []) (lem-Cz-beta c4) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym12-at233442 c4) ▸ done


-- sym12 @0213213440: 5 steps
lem-sym12-at0213213440 : Complete 4 → ⟪ (Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-sym12-at0213213440 c4 = run b0
  where
  b0 : Chain (Bx2-3140 ∷ []) (Bx2-1340 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-3041 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3140⟩ c4) ▸
       at 1 1 (Bx2-0341 ∷ []) (lem-sym12-at0213203441 c4) ▸
       at 0 2 (Bx2-1340 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0341⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(2;3140): 9 steps
lem-auto-CCZ012-∣-BOX⟨2·3140⟩ : Complete 4 → ⟪ (CCZ012 ∷ Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨2·3140⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Bx2-3140 ∷ []) (Bx2-3140 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-1340 ∷ []) (lem-sym12-at0213213440 c4) ▸
       at 1 1 (Bx2-1304 ∷ []) (lem-sym34-at02233440 c4) ▸
       at 1 1 (Bx2-1034 ∷ []) (lem-sym23-at022330 c4) ▸
       at 0 2 (Bx2-1034 ∷ CCZ012 ∷ []) (lem-Cz-beta-at0220 c4) ▸
       at 0 1 (Bx2-1304 ∷ []) (lem-sym23-at0220 c4) ▸
       at 0 1 (Bx2-1340 ∷ []) (lem-sym34-at022330 c4) ▸
       at 0 1 (Bx2-3140 ∷ []) (lem-sym12-at02233440 c4) ▸ done

  b1 : Chain (Bx2-3140 ∷ CCZ012 ∷ []) (Bx2-3140 ∷ CCZ012 ∷ [])
  b1 = at 1 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(0;3124): 5 steps
lem-auto-CCZ012-∣-BOX⟨0·3124⟩ : Complete 4 → ⟪ (CCZ012 ∷ Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨0·3124⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx0-3124 ∷ []) (Bx0-3124 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 2 (Bx0-1234 ∷ CCZ012 ∷ []) (lem-Cz-beta c4) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸ done


-- auto CCZ012 | SBOX(0;3;4;2): 1 steps
lem-auto-CCZ012-∣-SBOX⟨0·3·4·2⟩ : Complete 4 → ⟪ (CCZ012 ∷ Sb0-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-4-2 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨0·3·4·2⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Sb0-3-4-2 ∷ []) (Sb0-3-4-2 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (Sb0-3-4-2 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸ done


-- auto CCZ012 | SBOXd(0;3;4;2): 1 steps
lem-auto-CCZ012-∣-SBOXd⟨0·3·4·2⟩ : Complete 4 → ⟪ (CCZ012 ∷ Sb⁻0-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-4-2 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOXd⟨0·3·4·2⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Sb⁻0-3-4-2 ∷ []) (Sb⁻0-3-4-2 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (Sb⁻0-3-4-2 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS)) ▸ done


-- auto CCZ012 | SBOX(0;3;12;4): 7 steps
lem-auto-CCZ012-∣-SBOX⟨0·3·12·4⟩ : Complete 4 → ⟪ (CCZ012 ∷ Sb0-3-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-12-4 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨0·3·12·4⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Sb0-3-12-4 ∷ []) (Sb0-3-12-4 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx0-3124 ∷ Toff412 ∷ Sb0-3-4-2 ∷ Toff412 ∷ Sb⁻0-3-4-2 ∷ []) (refl) ▸
       at 0 2 (Bx0-3124 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨0·3124⟩ c4) ▸
       at 1 2 (Toff412 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-3-4-2 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨0·3·4·2⟩ c4) ▸
       at 3 2 (Toff412 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻0-3-4-2 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOXd⟨0·3·4·2⟩ c4) ▸
       at 0 5 (Sb0-3-12-4 ∷ []) (refl) ▸ done


-- F5 CS01 @0110: 8 steps
lem-F5-CS01-at0110 : Complete 4 → ⟪ (X4 ∷ Sb2-1-40-3 ∷ X4 ∷ Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
lem-F5-CS01-at0110 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-1-40-3 ∷ X4 ∷ Sb2-1-40-3 ∷ []) (CS01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑)) ▸
       at 2 2 (Sb2-0-41-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·40·3⟩ c4) ▸
       at 3 2 (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑)) ▸
       at 4 2 (Sb2-0-41-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·40·3⟩ c4) ▸
       at 1 4 (CS01 ∷ []) (lem-F5-CS01 c4) ▸
       at 0 2 (CS01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5 CS01 @021021: 8 steps
lem-F5-CS01-at021021 : Complete 4 → ⟪ (X4 ∷ Sb1-2-40-3 ∷ X4 ∷ Sb1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
lem-F5-CS01-at021021 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb1-2-40-3 ∷ X4 ∷ Sb1-2-40-3 ∷ []) (CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 2 2 (Sb2-1-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·40·3⟩ c4) ▸
       at 3 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 4 2 (Sb2-1-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·40·3⟩ c4) ▸
       at 1 4 (CS01 ∷ []) (lem-F5-CS01-at0110 c4) ▸
       at 0 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5 CS01 @03102132: 8 steps
lem-F5-CS01-at03102132 : Complete 4 → ⟪ (X4 ∷ Sb1-3-40-2 ∷ X4 ∷ Sb1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ []) ⟫ʷ
lem-F5-CS01-at03102132 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb1-3-40-2 ∷ X4 ∷ Sb1-3-40-2 ∷ []) (CS03 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 2 2 (Sb1-2-40-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·40·2⟩ c4) ▸
       at 3 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 4 2 (Sb1-2-40-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·40·2⟩ c4) ▸
       at 1 4 (CS02 ∷ []) (lem-F5-CS01-at021021 c4) ▸
       at 0 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5 CS01 @0410213243: 8 steps
lem-F5-CS01-at0410213243 : Complete 4 → ⟪ (X3 ∷ Sb1-4-30-2 ∷ X3 ∷ Sb1-4-30-2 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
lem-F5-CS01-at0410213243 c4 = run b0
  where
  b0 : Chain (X3 ∷ Sb1-4-30-2 ∷ X3 ∷ Sb1-4-30-2 ∷ []) (CS04 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ X3 ∷ []) (X4 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-3-40-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·4·30·2⟩ c4) ▸
       at 3 2 (X4 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ X3 ∷ []) (X4 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb1-3-40-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·4·30·2⟩ c4) ▸
       at 1 4 (CS03 ∷ []) (lem-F5-CS01-at03102132 c4) ▸
       at 0 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5 CS01 @04102142: 8 steps
lem-F5-CS01-at04102142 : Complete 4 → ⟪ (X2 ∷ Sb1-4-20-3 ∷ X2 ∷ Sb1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
lem-F5-CS01-at04102142 c4 = run b0
  where
  b0 : Chain (X2 ∷ Sb1-4-20-3 ∷ X2 ∷ Sb1-4-20-3 ∷ []) (CS04 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-4-30-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·4·20·3⟩ c4) ▸
       at 3 2 (X3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb1-4-30-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·4·20·3⟩ c4) ▸
       at 1 4 (CS04 ∷ []) (lem-F5-CS01-at0410213243 c4) ▸
       at 0 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5 CS01 @041041: 8 steps
lem-F5-CS01-at041041 : Complete 4 → ⟪ (X1 ∷ Sb2-4-10-3 ∷ X1 ∷ Sb2-4-10-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
lem-F5-CS01-at041041 c4 = run b0
  where
  b0 : Chain (X1 ∷ Sb2-4-10-3 ∷ X1 ∷ Sb2-4-10-3 ∷ []) (CS04 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ X1 ∷ []) (X2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-4-20-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·4·10·3⟩ c4) ▸
       at 3 2 (X2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ X1 ∷ []) (X2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb1-4-20-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·4·10·3⟩ c4) ▸
       at 1 4 (CS04 ∷ []) (lem-F5-CS01-at04102142 c4) ▸
       at 0 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5 CS01 @0440: 8 steps
lem-F5-CS01-at0440 : Complete 4 → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ []) ⟫ʷ
lem-F5-CS01-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (CS14 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X1 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ X0 ∷ []) (X1 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb2-4-10-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·4·01·3⟩ c4) ▸
       at 3 2 (X1 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ X0 ∷ []) (X1 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb2-4-10-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·4·01·3⟩ c4) ▸
       at 1 4 (CS04 ∷ []) (lem-F5-CS01-at041041 c4) ▸
       at 0 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBtgt @0110: 5 steps
lem-SBtgt-at0110 : Complete 4 → ⟪ (Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-10-3 ∷ []) ⟫ʷ
lem-SBtgt-at0110 c4 = run b0
  where
  b0 : Chain (Sb2-1-40-3 ∷ []) (Sb2-4-10-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·40·3⟩ c4) ▸
       at 1 1 (Sb2-4-01-3 ∷ []) (lem-SBtgt c4) ▸
       at 0 2 (Sb2-4-10-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·4·01·3⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBtgt @021021: 5 steps
lem-SBtgt-at021021 : Complete 4 → ⟪ (Sb1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-20-3 ∷ []) ⟫ʷ
lem-SBtgt-at021021 c4 = run b0
  where
  b0 : Chain (Sb1-2-40-3 ∷ []) (Sb1-4-20-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb2-1-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·40·3⟩ c4) ▸
       at 1 1 (Sb2-4-10-3 ∷ []) (lem-SBtgt-at0110 c4) ▸
       at 0 2 (Sb1-4-20-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·4·10·3⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBtgt @03102132: 5 steps
lem-SBtgt-at03102132 : Complete 4 → ⟪ (Sb1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-30-2 ∷ []) ⟫ʷ
lem-SBtgt-at03102132 c4 = run b0
  where
  b0 : Chain (Sb1-3-40-2 ∷ []) (Sb1-4-30-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-2-40-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·40·2⟩ c4) ▸
       at 1 1 (Sb1-4-20-3 ∷ []) (lem-SBtgt-at021021 c4) ▸
       at 0 2 (Sb1-4-30-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·4·20·3⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBtgt @0410213243: 5 steps
lem-SBtgt-at0410213243 : Complete 4 → ⟪ (Sb1-4-30-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-40-2 ∷ []) ⟫ʷ
lem-SBtgt-at0410213243 c4 = run b0
  where
  b0 : Chain (Sb1-4-30-2 ∷ []) (Sb1-3-40-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-3-40-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·4·30·2⟩ c4) ▸
       at 1 1 (Sb1-4-30-2 ∷ []) (lem-SBtgt-at03102132 c4) ▸
       at 0 2 (Sb1-3-40-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·4·30·2⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBtgt @04102142: 5 steps
lem-SBtgt-at04102142 : Complete 4 → ⟪ (Sb1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-40-3 ∷ []) ⟫ʷ
lem-SBtgt-at04102142 c4 = run b0
  where
  b0 : Chain (Sb1-4-20-3 ∷ []) (Sb1-2-40-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-4-30-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·4·20·3⟩ c4) ▸
       at 1 1 (Sb1-3-40-2 ∷ []) (lem-SBtgt-at0410213243 c4) ▸
       at 0 2 (Sb1-2-40-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·40·2⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBtgt @041041: 5 steps
lem-SBtgt-at041041 : Complete 4 → ⟪ (Sb2-4-10-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-40-3 ∷ []) ⟫ʷ
lem-SBtgt-at041041 c4 = run b0
  where
  b0 : Chain (Sb2-4-10-3 ∷ []) (Sb2-1-40-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-4-20-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·4·10·3⟩ c4) ▸
       at 1 1 (Sb1-2-40-3 ∷ []) (lem-SBtgt-at04102142 c4) ▸
       at 0 2 (Sb2-1-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·40·3⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBtgt @0440: 5 steps
lem-SBtgt-at0440 : Complete 4 → ⟪ (Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ
lem-SBtgt-at0440 c4 = run b0
  where
  b0 : Chain (Sb2-4-01-3 ∷ []) (Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb2-4-10-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·4·01·3⟩ c4) ▸
       at 1 1 (Sb2-1-40-3 ∷ []) (lem-SBtgt-at041041 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·40·3⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | SBOX(3;4;12;0) @1221: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at1221 : Complete 4 → ⟪ (Toff012 ∷ Sb3-4-21-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-21-0 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at1221 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Sb3-4-21-0 ∷ []) (Sb3-4-21-0 ∷ Toff012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb3-4-12-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·21·0⟩ c4) ▸
       at 1 2 (Sb3-4-12-0 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩ c4) ▸
       at 0 2 (Sb3-4-21-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·12·0⟩ c4) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | SBOX(3;4;12;0) @132132: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at132132 : Complete 4 → ⟪ (Toff013 ∷ Sb2-4-31-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-31-0 ∷ Toff013 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at132132 c4 = run b0
  where
  b0 : Chain (Toff013 ∷ Sb2-4-31-0 ∷ []) (Sb2-4-31-0 ∷ Toff013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 2 2 (Sb3-4-21-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·4·31·0⟩ c4) ▸
       at 1 2 (Sb3-4-21-0 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at1221 c4) ▸
       at 0 2 (Sb2-4-31-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·4·21·0⟩ c4) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | SBOX(3;4;12;0) @14213243: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at14213243 : Complete 4 → ⟪ (Toff014 ∷ Sb2-3-41-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-41-0 ∷ Toff014 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at14213243 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Sb2-3-41-0 ∷ []) (Sb2-3-41-0 ∷ Toff014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 2 2 (Sb2-4-31-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·3·41·0⟩ c4) ▸
       at 1 2 (Sb2-4-31-0 ∷ Toff013 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at132132 c4) ▸
       at 0 2 (Sb2-3-41-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·4·31·0⟩ c4) ▸
       at 1 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | SBOX(3;4;12;0) @0114203243: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0114203243 : Complete 4 → ⟪ (Toff104 ∷ Sb2-3-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-40-1 ∷ Toff104 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0114203243 c4 = run b0
  where
  b0 : Chain (Toff104 ∷ Sb2-3-40-1 ∷ []) (Sb2-3-40-1 ∷ Toff104 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 2 2 (Sb2-3-41-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·40·1⟩ c4) ▸
       at 1 2 (Sb2-3-41-0 ∷ Toff014 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at14213243 c4) ▸
       at 0 2 (Sb2-3-40-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·41·0⟩ c4) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | SBOX(3;4;12;0) @0214203143: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0214203143 : Complete 4 → ⟪ (Toff204 ∷ Sb1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-40-2 ∷ Toff204 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0214203143 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Sb1-3-40-2 ∷ []) (Sb1-3-40-2 ∷ Toff204 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 2 2 (Sb2-3-40-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·3·40·2⟩ c4) ▸
       at 1 2 (Sb2-3-40-1 ∷ Toff104 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0114203243 c4) ▸
       at 0 2 (Sb1-3-40-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·3·40·1⟩ c4) ▸
       at 1 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | SBOX(3;4;12;0) @0314203142: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314203142 : Complete 4 → ⟪ (Toff304 ∷ Sb1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-40-3 ∷ Toff304 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314203142 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ Sb1-2-40-3 ∷ []) (Sb1-2-40-3 ∷ Toff304 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 2 2 (Sb1-3-40-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·2·40·3⟩ c4) ▸
       at 1 2 (Sb1-3-40-2 ∷ Toff204 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0214203143 c4) ▸
       at 0 2 (Sb1-2-40-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·40·2⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | SBOX(3;4;12;0) @0314203241: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314203241 : Complete 4 → ⟪ (Toff304 ∷ Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-40-3 ∷ Toff304 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314203241 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ Sb2-1-40-3 ∷ []) (Sb2-1-40-3 ∷ Toff304 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 2 2 (Sb1-2-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·40·3⟩ c4) ▸
       at 1 2 (Sb1-2-40-3 ∷ Toff304 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314203142 c4) ▸
       at 0 2 (Sb2-1-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·40·3⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | SBOX(3;4;12;0) @0314213240: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314213240 : Complete 4 → ⟪ (Toff314 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Toff314 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314213240 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Toff314 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 2 2 (Sb2-1-40-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 (Sb2-1-40-3 ∷ Toff304 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314203241 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·40·3⟩ c4) ▸
       at 1 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- X1-beta @2332: 8 steps
lem-X1-beta-at2332 : Complete 4 → ⟪ (X1 ∷ Bx0-1324 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-X1-beta-at2332 c4 = run b0
  where
  b0 : Chain (X1 ∷ Bx0-1324 ∷ X1 ∷ []) (CCZ234 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X1 ∷ Sw23 ∷ []) (sym (c₂ (X ↑) (Swap))) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (c₂ (X ↑) (Swap))) ▸
       at 1 3 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-X1-beta c4) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- X1-beta @243243: 8 steps
lem-X1-beta-at243243 : Complete 4 → ⟪ (X1 ∷ Bx0-1423 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-X1-beta-at243243 c4 = run b0
  where
  b0 : Chain (X1 ∷ Bx0-1423 ∷ X1 ∷ []) (CCZ234 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X1 ∷ Sw34 ∷ []) (sym (c₂ (X ↑) (Swap ↑))) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 3 2 (X1 ∷ Sw34 ∷ []) (sym (c₂ (X ↑) (Swap ↑))) ▸
       at 1 3 (CCZ234 ∷ Bx0-1324 ∷ []) (lem-X1-beta-at2332 c4) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- X1-beta @0110243243: 8 steps
lem-X1-beta-at0110243243 : Complete 4 → ⟪ (X0 ∷ Bx1-0423 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-X1-beta-at0110243243 c4 = run b0
  where
  b0 : Chain (X0 ∷ Bx1-0423 ∷ X0 ∷ []) (CCZ234 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X1 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ X0 ∷ []) (X1 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 3 2 (X1 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ X0 ∷ []) (X1 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CCZ234 ∷ Bx0-1423 ∷ []) (lem-X1-beta-at243243 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- X1-beta @0210243143: 8 steps
lem-X1-beta-at0210243143 : Complete 4 → ⟪ (X0 ∷ Bx2-0413 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-X1-beta-at0210243143 c4 = run b0
  where
  b0 : Chain (X0 ∷ Bx2-0413 ∷ X0 ∷ []) (CCZ134 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X0 ∷ Sw12 ∷ []) (sym (c₁ (X) (Swap))) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 3 2 (X0 ∷ Sw12 ∷ []) (sym (c₁ (X) (Swap))) ▸
       at 1 3 (CCZ234 ∷ Bx1-0423 ∷ []) (lem-X1-beta-at0110243243 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ234 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234 c4) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ234 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at2332 c4) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ234 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0110243243 : Complete 4 → ⟪ (Sb1-0-42-3 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at243243 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ234 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0210243143 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0110243243 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5d CS01 @0110: 8 steps
lem-F5d-CS01-at0110 : Complete 4 → ⟪ (CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-40-3 ∷ X4 ∷ Sb⁻2-1-40-3 ∷ X4 ∷ []) ⟫ʷ
lem-F5d-CS01-at0110 c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ []) (Sb⁻2-1-40-3 ∷ X4 ∷ Sb⁻2-1-40-3 ∷ X4 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb⁻2-0-41-3 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ []) (lem-F5d-CS01 c4) ▸
       at 0 2 (Sb⁻2-1-40-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·0·41·3⟩ c4) ▸
       at 1 2 (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑)) ▸
       at 2 2 (Sb⁻2-1-40-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·0·41·3⟩ c4) ▸
       at 3 2 (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑)) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5d CS01 @021021: 8 steps
lem-F5d-CS01-at021021 : Complete 4 → ⟪ (CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-40-3 ∷ X4 ∷ Sb⁻1-2-40-3 ∷ X4 ∷ []) ⟫ʷ
lem-F5d-CS01-at021021 c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ []) (Sb⁻1-2-40-3 ∷ X4 ∷ Sb⁻1-2-40-3 ∷ X4 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 1 1 (Sb⁻2-1-40-3 ∷ X4 ∷ Sb⁻2-1-40-3 ∷ X4 ∷ []) (lem-F5d-CS01-at0110 c4) ▸
       at 0 2 (Sb⁻1-2-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·1·40·3⟩ c4) ▸
       at 1 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 2 2 (Sb⁻1-2-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·1·40·3⟩ c4) ▸
       at 3 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5d CS01 @03102132: 8 steps
lem-F5d-CS01-at03102132 : Complete 4 → ⟪ (CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-40-2 ∷ X4 ∷ Sb⁻1-3-40-2 ∷ X4 ∷ []) ⟫ʷ
lem-F5d-CS01-at03102132 c4 = run b0
  where
  b0 : Chain (CS03⁻ ∷ []) (Sb⁻1-3-40-2 ∷ X4 ∷ Sb⁻1-3-40-2 ∷ X4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4) ▸
       at 1 1 (Sb⁻1-2-40-3 ∷ X4 ∷ Sb⁻1-2-40-3 ∷ X4 ∷ []) (lem-F5d-CS01-at021021 c4) ▸
       at 0 2 (Sb⁻1-3-40-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·2·40·3⟩ c4) ▸
       at 1 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 2 2 (Sb⁻1-3-40-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·2·40·3⟩ c4) ▸
       at 3 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5d CS01 @0410213243: 8 steps
lem-F5d-CS01-at0410213243 : Complete 4 → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-30-2 ∷ X3 ∷ Sb⁻1-4-30-2 ∷ X3 ∷ []) ⟫ʷ
lem-F5d-CS01-at0410213243 c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ []) (Sb⁻1-4-30-2 ∷ X3 ∷ Sb⁻1-4-30-2 ∷ X3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 c4) ▸
       at 1 1 (Sb⁻1-3-40-2 ∷ X4 ∷ Sb⁻1-3-40-2 ∷ X4 ∷ []) (lem-F5d-CS01-at03102132 c4) ▸
       at 0 2 (Sb⁻1-4-30-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·3·40·2⟩ c4) ▸
       at 1 2 (X3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ X4 ∷ []) (X3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻1-4-30-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·3·40·2⟩ c4) ▸
       at 3 2 (X3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ X4 ∷ []) (X3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5d CS01 @04102142: 8 steps
lem-F5d-CS01-at04102142 : Complete 4 → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-20-3 ∷ X2 ∷ Sb⁻1-4-20-3 ∷ X2 ∷ []) ⟫ʷ
lem-F5d-CS01-at04102142 c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ []) (Sb⁻1-4-20-3 ∷ X2 ∷ Sb⁻1-4-20-3 ∷ X2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 c4) ▸
       at 1 1 (Sb⁻1-4-30-2 ∷ X3 ∷ Sb⁻1-4-30-2 ∷ X3 ∷ []) (lem-F5d-CS01-at0410213243 c4) ▸
       at 0 2 (Sb⁻1-4-20-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·4·30·2⟩ c4) ▸
       at 1 2 (X2 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ X3 ∷ []) (X2 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻1-4-20-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·4·30·2⟩ c4) ▸
       at 3 2 (X2 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ X3 ∷ []) (X2 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5d CS01 @041041: 8 steps
lem-F5d-CS01-at041041 : Complete 4 → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-10-3 ∷ X1 ∷ Sb⁻2-4-10-3 ∷ X1 ∷ []) ⟫ʷ
lem-F5d-CS01-at041041 c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ []) (Sb⁻2-4-10-3 ∷ X1 ∷ Sb⁻2-4-10-3 ∷ X1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS04⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd04 c4) ▸
       at 1 1 (Sb⁻1-4-20-3 ∷ X2 ∷ Sb⁻1-4-20-3 ∷ X2 ∷ []) (lem-F5d-CS01-at04102142 c4) ▸
       at 0 2 (Sb⁻2-4-10-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·4·20·3⟩ c4) ▸
       at 1 2 (X1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ X2 ∷ []) (X1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻2-4-10-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·4·20·3⟩ c4) ▸
       at 3 2 (X1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ X2 ∷ []) (X1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5d CS01 @0440: 8 steps
lem-F5d-CS01-at0440 : Complete 4 → ⟪ (CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-01-3 ∷ X0 ∷ Sb⁻2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F5d-CS01-at0440 c4 = run b0
  where
  b0 : Chain (CS14⁻ ∷ []) (Sb⁻2-4-01-3 ∷ X0 ∷ Sb⁻2-4-01-3 ∷ X0 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS04⁻ ∷ Sw01 ∷ []) (lem-nat-0-CSd14 c4) ▸
       at 1 1 (Sb⁻2-4-10-3 ∷ X1 ∷ Sb⁻2-4-10-3 ∷ X1 ∷ []) (lem-F5d-CS01-at041041 c4) ▸
       at 0 2 (Sb⁻2-4-01-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·4·10·3⟩ c4) ▸
       at 1 2 (X0 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻2-4-01-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·4·10·3⟩ c4) ▸
       at 3 2 (X0 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBtgtd @0110: 5 steps
lem-SBtgtd-at0110 : Complete 4 → ⟪ (Sb⁻2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-10-3 ∷ []) ⟫ʷ
lem-SBtgtd-at0110 c4 = run b0
  where
  b0 : Chain (Sb⁻2-1-40-3 ∷ []) (Sb⁻2-4-10-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·1·40·3⟩ c4) ▸
       at 1 1 (Sb⁻2-4-01-3 ∷ []) (lem-SBtgtd c4) ▸
       at 0 2 (Sb⁻2-4-10-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·4·01·3⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBtgtd @021021: 5 steps
lem-SBtgtd-at021021 : Complete 4 → ⟪ (Sb⁻1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-20-3 ∷ []) ⟫ʷ
lem-SBtgtd-at021021 c4 = run b0
  where
  b0 : Chain (Sb⁻1-2-40-3 ∷ []) (Sb⁻1-4-20-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻2-1-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·2·40·3⟩ c4) ▸
       at 1 1 (Sb⁻2-4-10-3 ∷ []) (lem-SBtgtd-at0110 c4) ▸
       at 0 2 (Sb⁻1-4-20-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·4·10·3⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBtgtd @03102132: 5 steps
lem-SBtgtd-at03102132 : Complete 4 → ⟪ (Sb⁻1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-30-2 ∷ []) ⟫ʷ
lem-SBtgtd-at03102132 c4 = run b0
  where
  b0 : Chain (Sb⁻1-3-40-2 ∷ []) (Sb⁻1-4-30-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-2-40-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·3·40·2⟩ c4) ▸
       at 1 1 (Sb⁻1-4-20-3 ∷ []) (lem-SBtgtd-at021021 c4) ▸
       at 0 2 (Sb⁻1-4-30-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·4·20·3⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBtgtd @0410213243: 5 steps
lem-SBtgtd-at0410213243 : Complete 4 → ⟪ (Sb⁻1-4-30-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-40-2 ∷ []) ⟫ʷ
lem-SBtgtd-at0410213243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-4-30-2 ∷ []) (Sb⁻1-3-40-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-3-40-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·4·30·2⟩ c4) ▸
       at 1 1 (Sb⁻1-4-30-2 ∷ []) (lem-SBtgtd-at03102132 c4) ▸
       at 0 2 (Sb⁻1-3-40-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·4·30·2⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBtgtd @04102142: 5 steps
lem-SBtgtd-at04102142 : Complete 4 → ⟪ (Sb⁻1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-40-3 ∷ []) ⟫ʷ
lem-SBtgtd-at04102142 c4 = run b0
  where
  b0 : Chain (Sb⁻1-4-20-3 ∷ []) (Sb⁻1-2-40-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-4-30-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·4·20·3⟩ c4) ▸
       at 1 1 (Sb⁻1-3-40-2 ∷ []) (lem-SBtgtd-at0410213243 c4) ▸
       at 0 2 (Sb⁻1-2-40-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·3·40·2⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBtgtd @041041: 5 steps
lem-SBtgtd-at041041 : Complete 4 → ⟪ (Sb⁻2-4-10-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-40-3 ∷ []) ⟫ʷ
lem-SBtgtd-at041041 c4 = run b0
  where
  b0 : Chain (Sb⁻2-4-10-3 ∷ []) (Sb⁻2-1-40-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-4-20-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·4·10·3⟩ c4) ▸
       at 1 1 (Sb⁻1-2-40-3 ∷ []) (lem-SBtgtd-at04102142 c4) ▸
       at 0 2 (Sb⁻2-1-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·2·40·3⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBtgtd @0440: 5 steps
lem-SBtgtd-at0440 : Complete 4 → ⟪ (Sb⁻2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-SBtgtd-at0440 c4 = run b0
  where
  b0 : Chain (Sb⁻2-4-01-3 ∷ []) (Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻2-4-10-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·4·01·3⟩ c4) ▸
       at 1 1 (Sb⁻2-1-40-3 ∷ []) (lem-SBtgtd-at041041 c4) ▸
       at 0 2 (Sb⁻2-0-41-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·1·40·3⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | TOFF423 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ Toff423 ∷ []) (Toff423 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Toff423 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff423 ∷ []) (Toff423 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff423 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423 c4) ▸
       at 0 2 (Toff423 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff423 ∷ []) (Toff423 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | TOFF423 @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at243243 : Complete 4 → ⟪ (Sb⁻0-1-42-3 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-42-3 ∷ Toff324 ∷ []) (Toff324 ∷ Sb⁻0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Toff423 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff324 ∷ []) (Toff423 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff423 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at2332 c4) ▸
       at 0 2 (Toff324 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff423 ∷ []) (Toff324 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | TOFF423 @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0110243243 : Complete 4 → ⟪ (Sb⁻1-0-42-3 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ Toff324 ∷ []) (Toff324 ∷ Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 2 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 2 (Toff324 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at243243 c4) ▸
       at 0 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | TOFF423 @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0210243143 : Complete 4 → ⟪ (Sb⁻2-0-41-3 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ Toff314 ∷ []) (Toff314 ∷ Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ c4) ▸
       at 2 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0110243243 c4) ▸
       at 0 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @0310243142: 5 steps
lem-BOXd-BOX-at0310243142 : Complete 4 → ⟪ (Bx⁻3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-BOXd-BOX-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx⁻3-0412 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·0412⟩ c4) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 0 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0310243142: 5 steps
lem-sym34-at0310243142 : Complete 4 → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-sym34-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Bx3-0421 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ c4) ▸
       at 1 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸
       at 0 2 (Bx3-0421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0431⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0310243241: 5 steps
lem-sym23-at0310243241 : Complete 4 → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-sym23-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ []) (Bx3-0241 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ c4) ▸
       at 1 1 (Bx3-0142 ∷ []) (lem-sym23-at0310243142 c4) ▸
       at 0 2 (Bx3-0241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0142⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


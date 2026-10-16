{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D007 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-CS12-beta ; lem-K0-pass-c ; lem-K0-pass-ci ; lem-beta-T ; lem-sym12 ; lem-sym34)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-T312-beta ; lem-sym12-at1221 ; lem-sym23-at1221 ; lem-sym34-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F0 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ034 ; lem-auto-BOX⟨0·1234⟩-∣-TOFF012 ; lem-sym12-at233442 ; lem-sym23-at12213443 ; lem-sym23-at122331 ; lem-sym23-at12243143 ; lem-sym23-at243243 ; lem-sym23-at3443 ; lem-sym34-at12213443 ; lem-sym34-at2332 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-SBsym ; lem-sym23-at021021 ; lem-sym34-at122331 ; lem-sym34-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-CS12-beta-at243243 ; lem-CSd12-beta-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231 ; lem-auto-BOX⟨0·1234⟩-∣-CS14 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-F0-at0214213043 ; lem-beta-T-at2442 ; lem-sym12-at0213203441 ; lem-sym23-at01102332 ; lem-sym34-at0210233441)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-3-BOX⟨0·1243⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-2-TOFF413)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨3·0124⟩ ; lem-nat-3-BOX⟨0·1234⟩ ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-BOX⟨0·1243⟩ ; lem-nat-2-BOX⟨0·1342⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-BOX⟨0·1342⟩ ; lem-nat-1-BOX⟨0·2341⟩ ; lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨0·1342⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-BOX⟨0·3142⟩ ; lem-nat-0-BOX⟨1·0324⟩ ; lem-nat-0-BOX⟨1·0342⟩ ; lem-nat-1-BOX⟨1·0342⟩ ; lem-nat-1-BOX⟨1·3042⟩ ; lem-nat-1-BOX⟨2·0314⟩ ; lem-nat-1-BOX⟨2·0341⟩ ; lem-nat-1-SBOX⟨1·0·32·4⟩ ; lem-nat-3-SBOX⟨2·0·31·4⟩ ; lem-nat-3-SBOX⟨3·0·41·2⟩ ; lem-nat-3-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-0-BOX⟨4·0231⟩ ; lem-nat-0-BOX⟨4·1230⟩ ; lem-nat-0-SBOX⟨0·1·23·4⟩ ; lem-nat-0-SBOX⟨1·0·32·4⟩ ; lem-nat-0-SBOX⟨4·0·23·1⟩ ; lem-nat-1-BOX⟨4·0132⟩ ; lem-nat-1-BOX⟨4·0231⟩ ; lem-nat-1-SBOX⟨2·0·13·4⟩ ; lem-nat-1-SBOX⟨4·0·31·2⟩ ; lem-nat-2-BOX⟨4·0123⟩ ; lem-nat-2-BOX⟨4·0132⟩ ; lem-nat-2-SBOX⟨1·0·23·4⟩ ; lem-nat-2-SBOX⟨4·0·32·1⟩ ; lem-nat-3-BOX⟨3·0124⟩ ; lem-nat-3-BOX⟨4·0123⟩ ; lem-nat-3-SBOX⟨2·0·14·3⟩)
-- sym23 @02102331: 5 steps
lem-sym23-at02102331 : Complete 4 → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-sym23-at02102331 c4 = run b0
  where
  b0 : Chain (Bx2-0314 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0314⟩ c4) ▸
       at 1 1 (Bx1-0234 ∷ []) (lem-sym23-at01102332 c4) ▸
       at 0 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- CS12-beta @0110: 7 steps
lem-CS12-beta-at0110 : Complete 4 → ⟪ (CS02 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CS02 ∷ []) ⟫ʷ
lem-CS12-beta-at0110 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ CS12 ∷ []) (lem-CS12-beta c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- CS12-beta @021021: 7 steps
lem-CS12-beta-at021021 : Complete 4 → ⟪ (CS01 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ CS01 ∷ []) ⟫ʷ
lem-CS12-beta-at021021 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 2 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 1 2 (Bx1-0234 ∷ CS02 ∷ []) (lem-CS12-beta-at0110 c4) ▸
       at 0 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @01102332: 5 steps
lem-sym34-at01102332 : Complete 4 → ⟪ (Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ []) ⟫ʷ
lem-sym34-at01102332 c4 = run b0
  where
  b0 : Chain (Bx1-0324 ∷ []) (Bx1-0342 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0324⟩ c4) ▸
       at 1 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 0 2 (Bx1-0342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1342⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @02102331: 5 steps
lem-sym34-at02102331 : Complete 4 → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-sym34-at02102331 c4 = run b0
  where
  b0 : Chain (Bx2-0314 ∷ []) (Bx2-0341 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0314⟩ c4) ▸
       at 1 1 (Bx1-0342 ∷ []) (lem-sym34-at01102332 c4) ▸
       at 0 2 (Bx2-0341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0342⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0110233442: 5 steps
lem-sym12-at0110233442 : Complete 4 → ⟪ (Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3042 ∷ []) ⟫ʷ
lem-sym12-at0110233442 c4 = run b0
  where
  b0 : Chain (Bx1-0342 ∷ []) (Bx1-3042 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0342⟩ c4) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-sym12-at233442 c4) ▸
       at 0 2 (Bx1-3042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3142⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0210233441: 5 steps
lem-sym12-at0210233441 : Complete 4 → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ []) ⟫ʷ
lem-sym12-at0210233441 c4 = run b0
  where
  b0 : Chain (Bx2-0341 ∷ []) (Bx2-3041 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0341⟩ c4) ▸
       at 1 1 (Bx1-3042 ∷ []) (lem-sym12-at0110233442 c4) ▸
       at 0 2 (Bx2-3041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3042⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(2;3041): 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩ : Complete 4 → ⟪ (CS01 ∷ Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx2-3041 ∷ []) (Bx2-3041 ∷ CS01 ∷ [])
  b0 = at 1 1 (Bx2-0341 ∷ []) (lem-sym12-at0213203441 c4) ▸
       at 1 1 (Bx2-0314 ∷ []) (lem-sym34-at0210233441 c4) ▸
       at 1 1 (Bx2-0134 ∷ []) (lem-sym23-at02102331 c4) ▸
       at 0 2 (Bx2-0134 ∷ CS01 ∷ []) (lem-CS12-beta-at021021 c4) ▸
       at 0 1 (Bx2-0314 ∷ []) (lem-sym23-at021021 c4) ▸
       at 0 1 (Bx2-0341 ∷ []) (lem-sym34-at02102331 c4) ▸
       at 0 1 (Bx2-3041 ∷ []) (lem-sym12-at0210233441 c4) ▸ done


-- auto CS01 | SBOX(2;3;04;1): 9 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩ : Complete 4 → ⟪ (CS01 ∷ Sb2-3-04-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-04-1 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS01 ∷ Sb2-3-04-1 ∷ []) (Bx2-3041 ∷ Toff104 ∷ Sb2-3-1-4 ∷ Toff104 ∷ Sb⁻2-3-1-4 ∷ CS01 ∷ [])
  b0 = at 1 1 (Bx2-3041 ∷ Toff104 ∷ Sb2-3-1-4 ∷ Toff104 ∷ Sb⁻2-3-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx2-3041 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩ c4) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 1 4 (Toff104 ∷ CS13 ∷ Toff104 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ Toff104 ∷ CS13 ∷ Toff104 ∷ []) (Toff104 ∷ CS13 ∷ Toff104 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-3-1-4 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 2 (CS13⁻ ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻2-3-1-4 ∷ []) (refl) ▸ done

  b1 : Chain (Bx2-3041 ∷ Toff104 ∷ Sb2-3-1-4 ∷ Toff104 ∷ Sb⁻2-3-1-4 ∷ CS01 ∷ []) (Sb2-3-04-1 ∷ CS01 ∷ [])
  b1 = at 0 5 (Sb2-3-04-1 ∷ []) (refl) ▸ done


-- auto K0 | BOX(0;1234): 1 steps
lem-auto-K0-∣-BOX⟨0·1234⟩ : Complete 4 → ⟪ (K0 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ K0 ∷ []) ⟫ʷ
lem-auto-K0-∣-BOX⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (K0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0 ∷ [])
  b0 = at 0 2 (Bx0-1234 ∷ K0 ∷ []) (lem-K0-pass-c c4) ▸ done


-- auto K0 | BOX(0;1234) @3443: 7 steps
lem-auto-K0-∣-BOX⟨0·1234⟩-at3443 : Complete 4 → ⟪ (K0 ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ K0 ∷ []) ⟫ʷ
lem-auto-K0-∣-BOX⟨0·1234⟩-at3443 c4 = run b0
  where
  b0 : Chain (K0 ∷ Bx0-1243 ∷ []) (Bx0-1243 ∷ K0 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 2 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ K0 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩ c4) ▸
       at 0 2 (Bx0-1243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto K0 | BOX(0;1234) @233442: 7 steps
lem-auto-K0-∣-BOX⟨0·1234⟩-at233442 : Complete 4 → ⟪ (K0 ∷ Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ K0 ∷ []) ⟫ʷ
lem-auto-K0-∣-BOX⟨0·1234⟩-at233442 c4 = run b0
  where
  b0 : Chain (K0 ∷ Bx0-1342 ∷ []) (Bx0-1342 ∷ K0 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 2 2 (Bx0-1243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1342⟩ c4) ▸
       at 1 2 (Bx0-1243 ∷ K0 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩-at3443 c4) ▸
       at 0 2 (Bx0-1342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1243⟩ c4) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto K0 | BOX(0;1234) @12233441: 7 steps
lem-auto-K0-∣-BOX⟨0·1234⟩-at12233441 : Complete 4 → ⟪ (K0 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ K0 ∷ []) ⟫ʷ
lem-auto-K0-∣-BOX⟨0·1234⟩-at12233441 c4 = run b0
  where
  b0 : Chain (K0 ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ K0 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 (Bx0-1342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2341⟩ c4) ▸
       at 1 2 (Bx0-1342 ∷ K0 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩-at233442 c4) ▸
       at 0 2 (Bx0-2341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1342⟩ c4) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto K0 | SBOX(1;2;34;0): 13 steps
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩ : Complete 4 → ⟪ (K0 ∷ Sb1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-34-0 ∷ K0 ∷ []) ⟫ʷ
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (K0 ∷ Sb1-2-34-0 ∷ []) (Bx0-2341 ∷ Toff134 ∷ Sb0-2-1-4 ∷ Toff134 ∷ K0 ∷ Sb⁻0-2-1-4 ∷ [])
  b0 = at 1 1 (Sb0-2-34-1 ∷ []) (lem-F0-at0214213043 c4) ▸
       at 1 1 (Bx0-2341 ∷ Toff134 ∷ Sb0-2-1-4 ∷ Toff134 ∷ Sb⁻0-2-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx0-2341 ∷ K0 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩-at12233441 c4) ▸
       at 1 2 (Toff134 ∷ K0 ∷ []) (pw2 c4 (K0 ∷ Toff134 ∷ []) (Toff134 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 2 2 (CS12 ∷ K0 ∷ []) (lw4 c4 (K0 ∷ CS12 ∷ []) (CS12 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-2-1-4 ∷ []) (refl) ▸
       at 3 2 (Toff134 ∷ K0 ∷ []) (pw2 c4 (K0 ∷ Toff134 ∷ []) (Toff134 ∷ K0 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx0-2341 ∷ Toff134 ∷ Sb0-2-1-4 ∷ Toff134 ∷ K0 ∷ Sb⁻0-2-1-4 ∷ []) (Sb1-2-34-0 ∷ K0 ∷ [])
  b1 = at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ K0 ∷ []) (lw4 c4 (K0 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-2-1-4 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-34-1 ∷ []) (refl) ▸
       at 0 1 (Sb1-2-34-0 ∷ []) (sym (lem-F0-at0214213043 c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;1432): 14 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ : Complete 4 → ⟪ (Sb0-1-2-3 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-2-3 ∷ Bx0-1432 ∷ []) (Toff014 ∷ CCZ023 ∷ CS12 ∷ Toff014 ∷ CCZ023 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸
       at 0 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (Toff014 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ Toff014 ∷ []) (Toff014 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 1 1 (CS12 ∷ []) (refl) ▸
       at 1 2 (CCZ023 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 2 1 (CS12 ∷ []) (refl) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ CS12 ∷ Toff014 ∷ CCZ023 ∷ []) (Bx0-1432 ∷ Sb0-1-2-3 ∷ [])
  b1 = at 2 2 (Toff014 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ Toff014 ∷ []) (Toff014 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 3 2 (CCZ023 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx0-1432 ∷ []) (sym (lem-beta-T-at2442 c4)) ▸ done


-- auto SBOX(0;1;2;3) | SBOX(0;1;43;2): 13 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩ : Complete 4 → ⟪ (Sb0-1-2-3 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-2-3 ∷ Sb0-1-43-2 ∷ []) (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ CS12 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 1 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-1432 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ c4) ▸
       at 1 1 (CS12 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 1 4 (Toff234 ∷ CS12 ∷ Toff234 ∷ CS12 ∷ []) (lw0 c4 (CS12 ∷ Toff234 ∷ CS12 ∷ Toff234 ∷ []) (Toff234 ∷ CS12 ∷ Toff234 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 4 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 4 1 (CS12 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ CS12 ∷ Sb⁻0-1-2-3 ∷ []) (Sb0-1-43-2 ∷ Sb0-1-2-3 ∷ [])
  b1 = at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 5 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-43-2 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | BOX(0;1234): 6 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·1234⟩ : Complete 4 → ⟪ (Bx0-1234 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T c4) ▸
       at 0 2 (Toff012 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012 c4) ▸
       at 1 2 (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ034 c4) ▸
       at 2 2 (Toff012 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012 c4) ▸
       at 3 2 (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ034 c4) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-beta-T c4)) ▸ done


-- auto BOX(0;1234) | SBOX(0;1;4;3): 3 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·4·3⟩ : Complete 4 → ⟪ (Bx0-1234 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-3 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·4·3⟩ c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-3 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14 c4) ▸
       at 0 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | SBOXd(0;1;4;3): 3 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOXd⟨0·1·4·3⟩ : Complete 4 → ⟪ (Bx0-1234 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-3 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOXd⟨0·1·4·3⟩ c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-3 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14 c4) ▸
       at 0 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) TOFF423 | CCZ231: 2 steps
lem-auto-BOX⟨0·1234⟩-TOFF423-∣-CCZ231 : Complete 4 → ⟪ (Bx0-1234 ∷ Toff423 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1234 ∷ Toff423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-TOFF423-∣-CCZ231 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Toff423 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1234 ∷ Toff423 ∷ [])
  b0 = at 1 2 (CCZ123 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231 c4) ▸ done


-- T312-beta @3443: 8 steps
lem-T312-beta-at3443 : Complete 4 → ⟪ (Toff412 ∷ Bx0-1243 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ CCZ123 ∷ []) ⟫ʷ
lem-T312-beta-at3443 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ Bx0-1243 ∷ Toff412 ∷ []) (Bx0-1243 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw34 ∷ []) (lem-nat-3-TOFF412 c4) ▸
       at 2 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw34 ∷ []) (lem-nat-3-TOFF412 c4) ▸
       at 1 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-T312-beta c4) ▸
       at 0 2 (Bx0-1243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @233442: 8 steps
lem-T312-beta-at233442 : Complete 4 → ⟪ (Toff413 ∷ Bx0-1342 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ CCZ123 ∷ []) ⟫ʷ
lem-T312-beta-at233442 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ Bx0-1342 ∷ Toff413 ∷ []) (Bx0-1342 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 2 2 (Bx0-1243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1342⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 1 3 (Bx0-1243 ∷ CCZ123 ∷ []) (lem-T312-beta-at3443 c4) ▸
       at 0 2 (Bx0-1342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1243⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @12233441: 8 steps
lem-T312-beta-at12233441 : Complete 4 → ⟪ (Toff423 ∷ Bx0-2341 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ CCZ123 ∷ []) ⟫ʷ
lem-T312-beta-at12233441 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ Bx0-2341 ∷ Toff423 ∷ []) (Bx0-2341 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2341⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-1342 ∷ CCZ123 ∷ []) (lem-T312-beta-at233442 c4) ▸
       at 0 2 (Bx0-2341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1342⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | SBOX(0;1;23;4): 31 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩ : Complete 4 → ⟪ (Bx0-1234 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Bx0-1234 ∷ Sb0-1-23-4 ∷ []) (Bx0-1234 ∷ Toff423 ∷ Bx0-2314 ∷ CCZ123 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 1 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-1234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·1234⟩ c4) ▸
       at 1 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 3 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 3 1 (Bx0-2341 ∷ []) (lem-sym34-at122331 c4) ▸
       at 2 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-T312-beta-at12233441 c4) ▸
       at 2 1 (Bx0-2314 ∷ []) (lem-sym34-at12233441 c4) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ Bx0-2314 ∷ CCZ123 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx0-1234 ∷ Toff423 ∷ CCZ123 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Toff423 ∷ Bx0-2341 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b1 = at 2 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 2 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 2 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231 c4) ▸
       at 3 2 (Sb0-1-4-3 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·4·3⟩ c4) ▸
       at 4 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 6 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 6 1 (Bx0-2341 ∷ []) (lem-sym34-at122331 c4) ▸ done

  b2 : Chain (Bx0-1234 ∷ Toff423 ∷ CCZ123 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Toff423 ∷ Bx0-2341 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CCZ123 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Bx0-1234 ∷ [])
  b2 = at 5 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-T312-beta-at12233441 c4) ▸
       at 5 1 (Bx0-2314 ∷ []) (lem-sym34-at12233441 c4) ▸
       at 5 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 5 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 5 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231 c4) ▸
       at 6 2 (Sb⁻0-1-4-3 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-1234 ∷ Toff423 ∷ []) (lem-auto-BOX⟨0·1234⟩-TOFF423-∣-CCZ231 c4) ▸
       at 4 2 (CCZ123 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (CCZ123 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Bx0-1234 ∷ []) (Sb0-1-23-4 ∷ Bx0-1234 ∷ [])
  b3 = at 3 1 (CS14 ∷ []) (refl) ▸
       at 3 2 (CCZ123 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 2 2 (CCZ123 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231 c4) ▸
       at 0 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 0 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CS41: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS41 : Complete 4 → ⟪ (Bx0-1234 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS41 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (lw0 c4 (CS14 ∷ []) (CS14 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS14 ∷ Bx0-1423 ∷ []) (sym (lem-CS12-beta-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CS14 ∷ []) (lw0 c4 (CS14 ∷ []) (CS14 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS41: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS14 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CS14 ∷ []) (CS14 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CS14 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14 ∷ []) (CS14 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS41 c4) ▸ done

  b1 : Chain (CS14 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS14 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | K0: 1 steps
lem-auto-BOX⟨0·1234⟩-∣-K0 : Complete 4 → ⟪ (Bx0-1234 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ K0 ∷ []) (K0 ∷ Bx0-1234 ∷ [])
  b0 = at 0 2 (K0 ∷ Bx0-1234 ∷ []) (sym (lem-K0-pass-c c4)) ▸ done


-- F0 @3443: 5 steps
lem-F0-at3443 : Complete 4 → ⟪ (Sb2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-31-2 ∷ []) ⟫ʷ
lem-F0-at3443 c4 = run b0
  where
  b0 : Chain (Sb2-0-31-4 ∷ []) (Sb4-0-31-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·31·4⟩ c4) ▸
       at 1 1 (Sb3-0-41-2 ∷ []) (lem-F0 c4) ▸
       at 0 2 (Sb4-0-31-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨3·0·41·2⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0 @12213443: 5 steps
lem-F0-at12213443 : Complete 4 → ⟪ (Sb1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-32-1 ∷ []) ⟫ʷ
lem-F0-at12213443 c4 = run b0
  where
  b0 : Chain (Sb1-0-32-4 ∷ []) (Sb4-0-32-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb2-0-31-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·32·4⟩ c4) ▸
       at 1 1 (Sb4-0-31-2 ∷ []) (lem-F0-at3443 c4) ▸
       at 0 2 (Sb4-0-32-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨4·0·31·2⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0 @13213442: 5 steps
lem-F0-at13213442 : Complete 4 → ⟪ (Sb1-0-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-23-1 ∷ []) ⟫ʷ
lem-F0-at13213442 c4 = run b0
  where
  b0 : Chain (Sb1-0-23-4 ∷ []) (Sb4-0-23-1 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·23·4⟩ c4) ▸
       at 1 1 (Sb4-0-32-1 ∷ []) (lem-F0-at12213443 c4) ▸
       at 0 2 (Sb4-0-23-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·0·32·1⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0 @0113203442: 5 steps
lem-F0-at0113203442 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-23-0 ∷ []) ⟫ʷ
lem-F0-at0113203442 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ []) (Sb4-1-23-0 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-23-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·23·4⟩ c4) ▸
       at 1 1 (Sb4-0-23-1 ∷ []) (lem-F0-at13213442 c4) ▸
       at 0 2 (Sb4-1-23-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨4·0·23·1⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | K0 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at0110 : Complete 4 → ⟪ (Bx1-0234 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ K1 ∷ []) (K1 ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 2 2 (K0 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0 c4) ▸
       at 0 2 (K1 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | K0 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ K2 ∷ []) (K2 ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 2 2 (K1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K2 ∷ []) (K1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K1 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at0110 c4) ▸
       at 0 2 (K2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | K0 @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ K3 ∷ []) (K3 ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ c4) ▸
       at 2 2 (K2 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K3 ∷ []) (K2 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K2 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at021021 c4) ▸
       at 0 2 (K3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | K0 @0410213243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at0410213243 : Complete 4 → ⟪ (Bx4-0123 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx4-0123 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ K4 ∷ []) (K4 ∷ Bx4-0123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0123⟩ c4) ▸
       at 2 2 (K3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K4 ∷ []) (K3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K3 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at03102132 c4) ▸
       at 0 2 (K4 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K3 ∷ []) (K4 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0124⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | K0 @04102142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at04102142 : Complete 4 → ⟪ (Bx4-0132 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx4-0132 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at04102142 c4 = run b0
  where
  b0 : Chain (Bx4-0132 ∷ K4 ∷ []) (K4 ∷ Bx4-0132 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0132⟩ c4) ▸
       at 2 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (K4 ∷ Bx4-0123 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at0410213243 c4) ▸
       at 0 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (Bx4-0132 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0123⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | K0 @041041: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at041041 : Complete 4 → ⟪ (Bx4-0231 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx4-0231 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at041041 c4 = run b0
  where
  b0 : Chain (Bx4-0231 ∷ K4 ∷ []) (K4 ∷ Bx4-0231 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0231⟩ c4) ▸
       at 2 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 1 2 (K4 ∷ Bx4-0132 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at04102142 c4) ▸
       at 0 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 1 2 (Bx4-0231 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0132⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | K0 @0440: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at0440 : Complete 4 → ⟪ (Bx4-1230 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx4-1230 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at0440 c4 = run b0
  where
  b0 : Chain (Bx4-1230 ∷ K4 ∷ []) (K4 ∷ Bx4-1230 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0231 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1230⟩ c4) ▸
       at 2 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸
       at 1 2 (K4 ∷ Bx4-0231 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at041041 c4) ▸
       at 0 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸
       at 1 2 (Bx4-1230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0231⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | K4: 13 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ K4 ∷ []) (Bx4-1230 ∷ Toff023 ∷ K4 ∷ CS01 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ [])
  b0 = at 0 1 (Sb4-1-23-0 ∷ []) (lem-F0-at0113203442 c4) ▸
       at 0 1 (Bx4-1230 ∷ Toff023 ∷ Sb4-1-0-3 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ []) (refl) ▸
       at 4 1 (CS01⁻ ∷ []) (refl) ▸
       at 4 2 (K4 ∷ CS01⁻ ∷ []) (lw2 c4 (CS01⁻ ∷ K4 ∷ []) (K4 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻4-1-0-3 ∷ []) (refl) ▸
       at 3 2 (K4 ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ K4 ∷ []) (K4 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS01 ∷ []) (refl) ▸
       at 2 2 (K4 ∷ CS01 ∷ []) (lw2 c4 (CS01 ∷ K4 ∷ []) (K4 ∷ CS01 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx4-1230 ∷ Toff023 ∷ K4 ∷ CS01 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ []) (K4 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 3 1 (Sb4-1-0-3 ∷ []) (refl) ▸
       at 1 2 (K4 ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ K4 ∷ []) (K4 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (K4 ∷ Bx4-1230 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at0440 c4) ▸
       at 1 5 (Sb4-1-23-0 ∷ []) (refl) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-F0-at0113203442 c4)) ▸ done


-- CS12-beta @12243143: 7 steps
lem-CS12-beta-at12243143 : Complete 4 → ⟪ (CS24 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ CS24 ∷ []) ⟫ʷ
lem-CS12-beta-at12243143 c4 = run b0
  where
  b0 : Chain (CS24 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ CS24 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ c4) ▸
       at 1 2 (Bx0-1423 ∷ CS14 ∷ []) (lem-CS12-beta-at243243 c4) ▸
       at 0 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS24: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS24 : Complete 4 → ⟪ (Bx0-1234 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS24 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS24 ∷ []) (CS24 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 0 2 (CS24 ∷ Bx0-2413 ∷ []) (sym (lem-CS12-beta-at12243143 c4)) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done


-- auto SBOX(0;1;23;4) | CS24: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS24 ∷ []) (CS24 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS24 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CS24 ∷ []) (CS24 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CS24 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14 ∷ Toff423 ∷ CS24 ∷ []) (CS24 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS24 c4) ▸ done

  b1 : Chain (CS24 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS24 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- SBsym @3443: 5 steps
lem-SBsym-at3443 : Complete 4 → ⟪ (Sb2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-13-4 ∷ []) ⟫ʷ
lem-SBsym-at3443 c4 = run b0
  where
  b0 : Chain (Sb2-0-31-4 ∷ []) (Sb2-0-13-4 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·31·4⟩ c4) ▸
       at 1 1 (Sb2-0-14-3 ∷ []) (lem-SBsym c4) ▸
       at 0 2 (Sb2-0-13-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·14·3⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBsym @12213443: 5 steps
lem-SBsym-at12213443 : Complete 4 → ⟪ (Sb1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-23-4 ∷ []) ⟫ʷ
lem-SBsym-at12213443 c4 = run b0
  where
  b0 : Chain (Sb1-0-32-4 ∷ []) (Sb1-0-23-4 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb2-0-31-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·32·4⟩ c4) ▸
       at 1 1 (Sb2-0-13-4 ∷ []) (lem-SBsym-at3443 c4) ▸
       at 0 2 (Sb1-0-23-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·13·4⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBsym @13213442: 5 steps
lem-SBsym-at13213442 : Complete 4 → ⟪ (Sb1-0-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-32-4 ∷ []) ⟫ʷ
lem-SBsym-at13213442 c4 = run b0
  where
  b0 : Chain (Sb1-0-23-4 ∷ []) (Sb1-0-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·23·4⟩ c4) ▸
       at 1 1 (Sb1-0-23-4 ∷ []) (lem-SBsym-at12213443 c4) ▸
       at 0 2 (Sb1-0-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·23·4⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBsym @0113203442: 5 steps
lem-SBsym-at0113203442 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ []) ⟫ʷ
lem-SBsym-at0113203442 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-23-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·23·4⟩ c4) ▸
       at 1 1 (Sb1-0-32-4 ∷ []) (lem-SBsym-at13213442 c4) ▸
       at 0 2 (Sb0-1-32-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·32·4⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS24 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS34 ∷ []) (CS34 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS24 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24 c4) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS34 CS34: 6 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-CS34 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS34 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-CS34 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS34 ∷ CS34 ∷ []) (CS34 ∷ CS34 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 1 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 1 2 (CS34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 c4) ▸
       at 2 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS34 CS34 @2332: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-CS34-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS24 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-CS34-at2332 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS24 ∷ CS24 ∷ []) (CS24 ∷ CS24 ∷ Sb0-1-32-4 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS34 ∷ CS34 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-CS34 c4) ▸
       at 0 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸ done

  b1 : Chain (CS24 ∷ CS24 ∷ Sb0-1-32-4 ∷ Sw23 ∷ Sw23 ∷ []) (CS24 ∷ CS24 ∷ Sb0-1-32-4 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CZ24: 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ24 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (CZ24 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ24 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ CZ24 ∷ []) (CZ24 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS24 ∷ CS24 ∷ []) (lw0 c4 (CZ24 ∷ []) (CS24 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 3 (CS24 ∷ CS24 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-CS34-at2332 c4) ▸
       at 2 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 2 (CZ24 ∷ []) (lw0 c4 (CS24 ∷ CS24 ∷ []) (CZ24 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | Kd0: 1 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0 : Complete 4 → ⟪ (Bx0-1234 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ K0⁻ ∷ []) (K0⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 0 2 (K0⁻ ∷ Bx0-1234 ∷ []) (sym (lem-K0-pass-ci c4)) ▸ done


-- auto BOX(0;1234) | Kd0 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0110 : Complete 4 → ⟪ (Bx1-0234 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ K1⁻ ∷ []) (K1⁻ ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 2 2 (K0⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K1⁻ ∷ []) (K0⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0 c4) ▸
       at 0 2 (K1⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K0⁻ ∷ []) (K1⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | Kd0 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ K2⁻ ∷ []) (K2⁻ ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 2 2 (K1⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K2⁻ ∷ []) (K1⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K1⁻ ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0110 c4) ▸
       at 0 2 (K2⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1⁻ ∷ []) (K2⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | Kd0 @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ K3⁻ ∷ []) (K3⁻ ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ c4) ▸
       at 2 2 (K2⁻ ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K3⁻ ∷ []) (K2⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K2⁻ ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at021021 c4) ▸
       at 0 2 (K3⁻ ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2⁻ ∷ []) (K3⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | Kd0 @0410213243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0410213243 : Complete 4 → ⟪ (Bx4-0123 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx4-0123 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx4-0123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0123⟩ c4) ▸
       at 2 2 (K3⁻ ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K4⁻ ∷ []) (K3⁻ ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K3⁻ ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at03102132 c4) ▸
       at 0 2 (K4⁻ ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K3⁻ ∷ []) (K4⁻ ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0124⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | Kd0 @04102142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at04102142 : Complete 4 → ⟪ (Bx4-0132 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx4-0132 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at04102142 c4 = run b0
  where
  b0 : Chain (Bx4-0132 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx4-0132 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0132⟩ c4) ▸
       at 2 2 (K4⁻ ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K • iI)) ▸
       at 1 2 (K4⁻ ∷ Bx4-0123 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0410213243 c4) ▸
       at 0 2 (K4⁻ ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K • iI)) ▸
       at 1 2 (Bx4-0132 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0123⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | Kd0 @041041: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at041041 : Complete 4 → ⟪ (Bx4-0231 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx4-0231 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at041041 c4 = run b0
  where
  b0 : Chain (Bx4-0231 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx4-0231 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0231⟩ c4) ▸
       at 2 2 (K4⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) ((K • iI) ↑)) ▸
       at 1 2 (K4⁻ ∷ Bx4-0132 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at04102142 c4) ▸
       at 0 2 (K4⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) ((K • iI) ↑)) ▸
       at 1 2 (Bx4-0231 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0132⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | Kd0 @0440: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0440 : Complete 4 → ⟪ (Bx4-1230 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx4-1230 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0440 c4 = run b0
  where
  b0 : Chain (Bx4-1230 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx4-1230 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0231 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1230⟩ c4) ▸
       at 2 2 (K4⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((K • iI) ↑ ↑)) ▸
       at 1 2 (K4⁻ ∷ Bx4-0231 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at041041 c4) ▸
       at 0 2 (K4⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((K • iI) ↑ ↑)) ▸
       at 1 2 (Bx4-1230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0231⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | Kd4: 13 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ K4⁻ ∷ []) (Bx4-1230 ∷ Toff023 ∷ K4⁻ ∷ CS01 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ [])
  b0 = at 0 1 (Sb4-1-23-0 ∷ []) (lem-F0-at0113203442 c4) ▸
       at 0 1 (Bx4-1230 ∷ Toff023 ∷ Sb4-1-0-3 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ []) (refl) ▸
       at 4 1 (CS01⁻ ∷ []) (refl) ▸
       at 4 2 (K4⁻ ∷ CS01⁻ ∷ []) (lw2 c4 (CS01⁻ ∷ K4⁻ ∷ []) (K4⁻ ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻4-1-0-3 ∷ []) (refl) ▸
       at 3 2 (K4⁻ ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ K4⁻ ∷ []) (K4⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS01 ∷ []) (refl) ▸
       at 2 2 (K4⁻ ∷ CS01 ∷ []) (lw2 c4 (CS01 ∷ K4⁻ ∷ []) (K4⁻ ∷ CS01 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx4-1230 ∷ Toff023 ∷ K4⁻ ∷ CS01 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ []) (K4⁻ ∷ Sb0-1-23-4 ∷ [])
  b1 = at 3 1 (Sb4-1-0-3 ∷ []) (refl) ▸
       at 1 2 (K4⁻ ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ K4⁻ ∷ []) (K4⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (K4⁻ ∷ Bx4-1230 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0440 c4) ▸
       at 1 5 (Sb4-1-23-0 ∷ []) (refl) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-F0-at0113203442 c4)) ▸ done


-- auto SBOX(0;1;23;4) | K4 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ K4 ∷ []) (K4 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (K4 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4 c4) ▸
       at 0 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CZ24 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ24-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (CZ34 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ24-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CZ34 ∷ []) (CZ34 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CZ24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ34 ∷ []) (CZ24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CZ24 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ24 c4) ▸
       at 0 2 (CZ34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ24 ∷ []) (CZ34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | Kd4 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (K4⁻ ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K • iI)) ▸
       at 1 2 (K4⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4 c4) ▸
       at 0 2 (K4⁻ ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K • iI)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CX34: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ CX34 ∷ []) (CX34 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (K4 ∷ CZ34 ∷ K4⁻ ∷ []) (lw0 c4 (CX34 ∷ []) (K4 ∷ CZ34 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (K4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 c4) ▸
       at 1 2 (CZ34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ24-at2332 c4) ▸
       at 2 2 (K4⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 c4) ▸
       at 3 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 3 (CX34 ∷ []) (lw0 c4 (K4 ∷ CZ34 ∷ K4⁻ ∷ []) (CX34 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd41: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd41 : Complete 4 → ⟪ (Bx0-1234 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd41 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ []) (CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS14⁻ ∷ Bx0-1423 ∷ []) (sym (lem-CSd12-beta-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ []) (CS14⁻ ∷ []) tt tt Eq.refl) ▸ done


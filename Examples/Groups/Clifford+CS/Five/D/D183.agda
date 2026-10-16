{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D183 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-T-beta ; lem-sym23 ; lem-sym34)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-sym12-at233442 ; lem-sym23-at2332 ; lem-sym34-at2332 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym23-at0110 ; lem-sym34-at233442)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-sym12-at13213442 ; lem-sym23-at01102332)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-SBsym-at0113203442 ; lem-T312-beta-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D080 using (lem-Cz-beta-at0110 ; lem-auto-CS01-∣-BOX⟨1·0234⟩)
open import Examples.Groups.Clifford+CS.Five.D.D135 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS12-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D136 using (lem-beta-T-at04103143)
open import Examples.Groups.Clifford+CS.Five.D.D137 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ403 ; lem-auto-CCZ012-∣-CCZ342-at04103143)
open import Examples.Groups.Clifford+CS.Five.D.D138 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ123)
open import Examples.Groups.Clifford+CS.Five.D.D149 using (lem-auto-CCZ012-∣-TOFF342)
open import Examples.Groups.Clifford+CS.Five.D.D174 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd12-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D182 using (lem-auto-CSd01-∣-BOX⟨1·0234⟩-at243243)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-2-TOFF201)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ134 ; lem-nat-0-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-TOFF413 ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-TOFF401 ; lem-nat-2-TOFF402 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-BOX⟨2·0413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-BOX⟨2·0413⟩ ; lem-nat-0-BOX⟨2·1403⟩ ; lem-nat-1-CSd02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOX⟨1·0·43·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-1-CSd01)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-BOX⟨0·3142⟩ ; lem-nat-0-BOX⟨1·3042⟩ ; lem-nat-1-BOX⟨1·3042⟩ ; lem-nat-1-BOX⟨2·3041⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-1-TOFF402 ; lem-nat-2-BOX⟨1·0234⟩ ; lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-2-SBOX⟨0·1·42·3⟩ ; lem-nat-2-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-2-SBOX⟨1·0·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R024 using (lem-nat-0-SBOX⟨2·1·3·0⟩ ; lem-nat-0-SBOXd⟨2·1·3·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R027 using (lem-nat-0-SBOX⟨2·0·3·1⟩ ; lem-nat-0-SBOXd⟨2·0·3·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R028 using (lem-nat-2-BOX⟨1·0324⟩ ; lem-nat-3-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R029 using (lem-nat-1-BOX⟨4·0213⟩ ; lem-nat-3-BOX⟨1·0324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R030 using (lem-nat-0-BOX⟨4·0123⟩ ; lem-nat-0-BOX⟨4·0213⟩ ; lem-nat-0-BOX⟨4·1023⟩ ; lem-nat-0-BOX⟨4·1203⟩ ; lem-nat-1-BOX⟨4·0123⟩ ; lem-nat-1-BOX⟨4·1032⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-0-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R034 using (lem-nat-0-SBOX⟨1·0·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R038 using (lem-nat-1-BOX⟨4·2031⟩ ; lem-nat-2-BOX⟨4·1023⟩ ; lem-nat-2-BOX⟨4·1032⟩)
open import Examples.Groups.Clifford+CS.Five.D.R039 using (lem-nat-2-BOX⟨2·1403⟩ ; lem-nat-2-BOX⟨2·3041⟩ ; lem-nat-2-BOX⟨3·1402⟩ ; lem-nat-2-BOX⟨3·2041⟩ ; lem-nat-2-BOX⟨4·1203⟩ ; lem-nat-2-BOX⟨4·1302⟩ ; lem-nat-2-SBOX⟨2·1·3·0⟩ ; lem-nat-2-SBOX⟨3·1·2·0⟩ ; lem-nat-2-SBOX⟨4·1·2·0⟩ ; lem-nat-2-SBOX⟨4·1·3·0⟩ ; lem-nat-2-SBOXd⟨2·1·3·0⟩ ; lem-nat-2-SBOXd⟨3·1·2·0⟩ ; lem-nat-2-SBOXd⟨4·1·2·0⟩ ; lem-nat-2-SBOXd⟨4·1·3·0⟩ ; lem-nat-3-BOX⟨3·1402⟩ ; lem-nat-3-BOX⟨3·2041⟩ ; lem-nat-3-BOX⟨4·1302⟩ ; lem-nat-3-BOX⟨4·2031⟩ ; lem-nat-3-SBOX⟨1·0·32·4⟩ ; lem-nat-3-SBOX⟨1·0·42·3⟩ ; lem-nat-3-SBOX⟨3·1·2·0⟩ ; lem-nat-3-SBOX⟨4·1·2·0⟩ ; lem-nat-3-SBOXd⟨3·1·2·0⟩ ; lem-nat-3-SBOXd⟨4·1·2·0⟩)
-- auto CSd01 | BOX(1;0234) @12243143: 7 steps
lem-auto-CSd01-∣-BOX⟨1·0234⟩-at12243143 : Complete 4 → ⟪ (CS02⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·0234⟩-at12243143 c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS02⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Bx1-0423 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·0234⟩-at243243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(1;0234) @0112243043: 7 steps
lem-auto-CSd01-∣-BOX⟨1·0234⟩-at0112243043 : Complete 4 → ⟪ (CS12⁻ ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·0234⟩-at0112243043 c4 = run b0
  where
  b0 : Chain (CS12⁻ ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ CS12⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1403⟩ c4) ▸
       at 1 2 (Bx2-0413 ∷ CS02⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·0234⟩-at12243143 c4) ▸
       at 0 2 (Bx2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (CS12⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(2;1403): 3 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩ c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Bx2-1403 ∷ CS12⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·0234⟩-at0112243043 c4) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


-- auto TOFF012 | BOX(0;3142): 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩ : Complete 4 → ⟪ (Toff012 ∷ Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩ c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Bx0-3142 ∷ []) (Bx0-3142 ∷ Toff012 ∷ [])
  b0 = at 1 1 (Bx0-1342 ∷ []) (lem-sym12-at13213442 c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym34-at233442 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 2 (Bx0-1234 ∷ Toff012 ∷ []) (lem-T-beta c4) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym12-at233442 c4) ▸ done


-- auto CS01 | BOX(1;0234) @2332: 7 steps
lem-auto-CS01-∣-BOX⟨1·0234⟩-at2332 : Complete 4 → ⟪ (CS01 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·0234⟩-at2332 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 2 2 (Bx1-0234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (Bx1-0234 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·0234⟩ c4) ▸
       at 0 2 (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(1;0234) @243243: 7 steps
lem-auto-CS01-∣-BOX⟨1·0234⟩-at243243 : Complete 4 → ⟪ (CS01 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·0234⟩-at243243 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 2 2 (Bx1-0324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Bx1-0324 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·0234⟩-at2332 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(1;0234) @12243143: 7 steps
lem-auto-CS01-∣-BOX⟨1·0234⟩-at12243143 : Complete 4 → ⟪ (CS02 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·0234⟩-at12243143 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Bx1-0423 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·0234⟩-at243243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(1;0234) @0112243043: 7 steps
lem-auto-CS01-∣-BOX⟨1·0234⟩-at0112243043 : Complete 4 → ⟪ (CS12 ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ CS12 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·0234⟩-at0112243043 c4 = run b0
  where
  b0 : Chain (CS12 ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ CS12 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1403⟩ c4) ▸
       at 1 2 (Bx2-0413 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨1·0234⟩-at12243143 c4) ▸
       at 0 2 (Bx2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (CS12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(2;1403): 3 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩ : Complete 4 → ⟪ (Sb0-1-2-3 ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-2-3 ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ Sb0-1-2-3 ∷ [])
  b0 = at 0 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (Bx2-1403 ∷ CS12 ∷ []) (lem-auto-CS01-∣-BOX⟨1·0234⟩-at0112243043 c4) ▸
       at 1 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done


-- beta-T @043043: 8 steps
lem-beta-T-at043043 : Complete 4 → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-T-at043043 c4 = run b0
  where
  b0 : Chain (Bx4-1203 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0213 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1203⟩ c4) ▸
       at 1 1 (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-beta-T-at04103143 c4) ▸
       at 0 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 1 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 2 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 3 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ342 @0410233142: 7 steps
lem-auto-CCZ012-∣-CCZ342-at0410233142 : Complete 4 → ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at0410233142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 2 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at04103143 c4) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(4;1203): 19 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·1203⟩ : Complete 4 → ⟪ (Bx0-1234 ∷ Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·1203⟩ c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-1234 ∷ Bx4-1203 ∷ []) (Toff412 ∷ CCZ123 ∷ CCZ034 ∷ Toff412 ∷ Toff412 ∷ Bx0-1234 ∷ Toff412 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-beta-T-at043043 c4) ▸
       at 0 0 (Toff412 ∷ Toff412 ∷ []) (lw0 c4 [] (Toff412 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 1 3 (Bx0-1243 ∷ CCZ123 ∷ []) (lem-T312-beta-at3443 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 1 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123 c4) ▸
       at 2 2 (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ403 c4) ▸
       at 3 0 (Toff412 ∷ Toff412 ∷ []) (lw0 c4 [] (Toff412 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff412 ∷ CCZ123 ∷ CCZ034 ∷ Toff412 ∷ Toff412 ∷ Bx0-1234 ∷ Toff412 ∷ CCZ034 ∷ []) (CCZ123 ∷ Toff412 ∷ CCZ123 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Bx0-1234 ∷ [])
  b1 = at 5 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 4 3 (Bx0-1243 ∷ CCZ123 ∷ []) (lem-T312-beta-at3443 c4) ▸
       at 4 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 4 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123 c4) ▸
       at 5 2 (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ403 c4) ▸
       at 0 2 (CCZ123 ∷ Toff412 ∷ []) (lw0 c4 (Toff412 ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ Toff412 ∷ []) (lw0 c4 (Toff412 ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ123 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0410233142 c4) ▸ done

  b2 : Chain (CCZ123 ∷ Toff412 ∷ CCZ123 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Bx0-1234 ∷ []) (Bx4-1203 ∷ Bx0-1234 ∷ [])
  b2 = at 1 2 (CCZ123 ∷ Toff412 ∷ []) (lw0 c4 (Toff412 ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 0 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx4-1203 ∷ []) (sym (lem-beta-T-at043043 c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(2;1403) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩-at2332 : Complete 4 → ⟪ (Sb⁻0-1-3-2 ∷ Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-3-2 ∷ Bx3-1402 ∷ []) (Bx3-1402 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx2-1403 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·1402⟩ c4) ▸
       at 1 2 (Bx2-1403 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩ c4) ▸
       at 0 2 (Bx3-1402 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·1403⟩ c4) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(2;1403) @243243: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩-at243243 : Complete 4 → ⟪ (Sb⁻0-1-4-2 ∷ Bx4-1302 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1302 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-2 ∷ Bx4-1302 ∷ []) (Bx4-1302 ∷ Sb⁻0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx3-1402 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·1302⟩ c4) ▸
       at 1 2 (Bx3-1402 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩-at2332 c4) ▸
       at 0 2 (Bx4-1302 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·1402⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(2;1403) @2442: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩-at2442 : Complete 4 → ⟪ (Sb⁻0-1-4-3 ∷ Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-3 ∷ Bx4-1203 ∷ []) (Bx4-1203 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx4-1302 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·1203⟩ c4) ▸
       at 1 2 (Bx4-1302 ∷ Sb⁻0-1-4-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩-at243243 c4) ▸
       at 0 2 (Bx4-1203 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·1302⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3142) @0110: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0110 : Complete 4 → ⟪ (Toff102 ∷ Bx1-3042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3042 ∷ Toff102 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0110 c4 = run b0
  where
  b0 : Chain (Toff102 ∷ Bx1-3042 ∷ []) (Bx1-3042 ∷ Toff102 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-3142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3042⟩ c4) ▸
       at 1 2 (Bx0-3142 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩ c4) ▸
       at 0 2 (Bx1-3042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3142⟩ c4) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3142) @021021: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at021021 : Complete 4 → ⟪ (Toff201 ∷ Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ Toff201 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at021021 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Bx2-3041 ∷ []) (Bx2-3041 ∷ Toff201 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-3042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3041⟩ c4) ▸
       at 1 2 (Bx1-3042 ∷ Toff102 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0110 c4) ▸
       at 0 2 (Bx2-3041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3042⟩ c4) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3142) @03102132: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at03102132 : Complete 4 → ⟪ (Toff301 ∷ Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ Toff301 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at03102132 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Bx3-2041 ∷ []) (Bx3-2041 ∷ Toff301 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 2 2 (Bx2-3041 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·2041⟩ c4) ▸
       at 1 2 (Bx2-3041 ∷ Toff201 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at021021 c4) ▸
       at 0 2 (Bx3-2041 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·3041⟩ c4) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3142) @0410213243: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0410213243 : Complete 4 → ⟪ (Toff401 ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ Toff401 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (Toff401 ∷ Bx4-2031 ∷ []) (Bx4-2031 ∷ Toff401 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 2 2 (Bx3-2041 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·2031⟩ c4) ▸
       at 1 2 (Bx3-2041 ∷ Toff301 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at03102132 c4) ▸
       at 0 2 (Bx4-2031 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·2041⟩ c4) ▸
       at 1 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3142) @04103143: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at04103143 : Complete 4 → ⟪ (Toff402 ∷ Bx4-1032 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1032 ∷ Toff402 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at04103143 c4 = run b0
  where
  b0 : Chain (Toff402 ∷ Bx4-1032 ∷ []) (Bx4-1032 ∷ Toff402 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 2 2 (Bx4-2031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·1032⟩ c4) ▸
       at 1 2 (Bx4-2031 ∷ Toff401 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0410213243 c4) ▸
       at 0 2 (Bx4-1032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·2031⟩ c4) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3142) @0410233142: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0410233142 : Complete 4 → ⟪ (Toff403 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ Toff403 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0410233142 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ Bx4-1023 ∷ []) (Bx4-1023 ∷ Toff403 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 2 2 (Bx4-1032 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·1023⟩ c4) ▸
       at 1 2 (Bx4-1032 ∷ Toff402 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at04103143 c4) ▸
       at 0 2 (Bx4-1023 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·1032⟩ c4) ▸
       at 1 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3142) @04233042: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at04233042 : Complete 4 → ⟪ (Toff413 ∷ Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ Toff413 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at04233042 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ Bx4-0123 ∷ []) (Bx4-0123 ∷ Toff413 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 2 2 (Bx4-1023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0123⟩ c4) ▸
       at 1 2 (Bx4-1023 ∷ Toff403 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0410233142 c4) ▸
       at 0 2 (Bx4-0123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1023⟩ c4) ▸
       at 1 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3142) @0412233041: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0412233041 : Complete 4 → ⟪ (Toff423 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Toff423 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0412233041 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Toff423 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-0123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0213⟩ c4) ▸
       at 1 2 (Bx4-0123 ∷ Toff413 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at04233042 c4) ▸
       at 0 2 (Bx4-0213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0123⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3142) @0412233140: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0412233140 : Complete 4 → ⟪ (Toff423 ∷ Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ Toff423 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0412233140 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ Bx4-1203 ∷ []) (Bx4-1203 ∷ Toff423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (Bx4-0213 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1203⟩ c4) ▸
       at 1 2 (Bx4-0213 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0412233041 c4) ▸
       at 0 2 (Bx4-1203 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0213⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(2;1403) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩-at2332 : Complete 4 → ⟪ (Sb0-1-3-2 ∷ Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-3-2 ∷ Bx3-1402 ∷ []) (Bx3-1402 ∷ Sb0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx2-1403 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·1402⟩ c4) ▸
       at 1 2 (Bx2-1403 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩ c4) ▸
       at 0 2 (Bx3-1402 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·1403⟩ c4) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(2;1403) @243243: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩-at243243 : Complete 4 → ⟪ (Sb0-1-4-2 ∷ Bx4-1302 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1302 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-2 ∷ Bx4-1302 ∷ []) (Bx4-1302 ∷ Sb0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx3-1402 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·1302⟩ c4) ▸
       at 1 2 (Bx3-1402 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩-at2332 c4) ▸
       at 0 2 (Bx4-1302 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·1402⟩ c4) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(2;1403) @2442: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩-at2442 : Complete 4 → ⟪ (Sb0-1-4-3 ∷ Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-3 ∷ Bx4-1203 ∷ []) (Bx4-1203 ∷ Sb0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx4-1302 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·1203⟩ c4) ▸
       at 1 2 (Bx4-1302 ∷ Sb0-1-4-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩-at243243 c4) ▸
       at 0 2 (Bx4-1203 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·1302⟩ c4) ▸
       at 1 2 (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(4;1203): 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·1203⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·1203⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Bx4-1203 ∷ []) (Bx4-1203 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 2 (Bx4-1203 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩-at2442 c4) ▸
       at 3 2 (Bx4-1203 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0412233140 c4) ▸
       at 2 2 (Bx4-1203 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·1403⟩-at2442 c4) ▸
       at 1 2 (Bx4-1203 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0412233140 c4) ▸
       at 0 2 (Bx4-1203 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·1203⟩ c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto CCZ012 | BOX(1;0324): 5 steps
lem-auto-CCZ012-∣-BOX⟨1·0324⟩ : Complete 4 → ⟪ (CCZ012 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨1·0324⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx1-0234 ∷ []) (lem-sym23-at01102332 c4) ▸
       at 0 2 (Bx1-0234 ∷ CCZ012 ∷ []) (lem-Cz-beta-at0110 c4) ▸
       at 0 1 (Bx1-0324 ∷ []) (lem-sym23-at0110 c4) ▸
       at 1 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF342 @3443: 7 steps
lem-auto-CCZ012-∣-TOFF342-at3443 : Complete 4 → ⟪ (CCZ012 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at3443 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (Toff324 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff423 ∷ []) (Toff324 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF342 c4) ▸
       at 0 2 (Toff423 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff324 ∷ []) (Toff423 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(1;0;32;4): 11 steps
lem-auto-CCZ012-∣-SBOX⟨1·0·32·4⟩ : Complete 4 → ⟪ (CCZ012 ∷ Sb1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-32-4 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨1·0·32·4⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Sb1-0-32-4 ∷ []) (Bx1-0324 ∷ Toff423 ∷ Sb1-0-4-2 ∷ Toff423 ∷ CCZ012 ∷ CS04⁻ ∷ [])
  b0 = at 1 1 (Bx1-0324 ∷ Toff423 ∷ Sb1-0-4-2 ∷ Toff423 ∷ Sb⁻1-0-4-2 ∷ []) (refl) ▸
       at 0 2 (Bx1-0324 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (Toff423 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at3443 c4) ▸
       at 3 1 (CS04 ∷ []) (refl) ▸
       at 2 2 (CS04 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CS04 ∷ []) (CS04 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-0-4-2 ∷ []) (refl) ▸
       at 3 2 (Toff423 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at3443 c4) ▸
       at 5 1 (CS04⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx1-0324 ∷ Toff423 ∷ Sb1-0-4-2 ∷ Toff423 ∷ CCZ012 ∷ CS04⁻ ∷ []) (Sb1-0-32-4 ∷ CCZ012 ∷ [])
  b1 = at 4 2 (CS04⁻ ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻1-0-4-2 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-32-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(4;1;3;0): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·1·3·0⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Sb4-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-3-0 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·1·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb4-1-3-0 ∷ []) (Sb4-1-3-0 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS13 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS12-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb4-1-3-0 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(4;1;3;0): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·1·3·0⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Sb⁻4-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-1-3-0 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·1·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb⁻4-1-3-0 ∷ []) (Sb⁻4-1-3-0 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS13⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd12-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb⁻4-1-3-0 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(4;1203) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·1203⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Bx4-1302 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1302 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·1203⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Bx4-1302 ∷ []) (Bx4-1302 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Bx4-1203 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·1302⟩ c4) ▸
       at 1 2 (Bx4-1203 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·1203⟩ c4) ▸
       at 0 2 (Bx4-1302 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·1203⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(4;1203) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·1203⟩-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·1203⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Bx3-1402 ∷ []) (Bx3-1402 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Bx4-1302 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·1402⟩ c4) ▸
       at 1 2 (Bx4-1302 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·1203⟩-at2332 c4) ▸
       at 0 2 (Bx3-1402 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·1302⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(4;1203) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·1203⟩-at2442 : Complete 4 → ⟪ (Sb0-1-43-2 ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·1203⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 (Bx3-1402 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·1403⟩ c4) ▸
       at 1 2 (Bx3-1402 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·1203⟩-at243243 c4) ▸
       at 0 2 (Bx2-1403 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·1402⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(4;1203) @01102442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·1203⟩-at01102442 : Complete 4 → ⟪ (Sb1-0-43-2 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·1203⟩-at01102442 c4 = run b0
  where
  b0 : Chain (Sb1-0-43-2 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ Sb1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 2 2 (Bx2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Bx2-1403 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·1203⟩-at2442 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1403⟩ c4) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(1;0;32;4) @3443: 7 steps
lem-auto-CCZ012-∣-SBOX⟨1·0·32·4⟩-at3443 : Complete 4 → ⟪ (CCZ012 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨1·0·32·4⟩-at3443 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (Sb1-0-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (Sb1-0-32-4 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨1·0·32·4⟩ c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·32·4⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(1;0;32;4) @233442: 7 steps
lem-auto-CCZ012-∣-SBOX⟨1·0·32·4⟩-at233442 : Complete 4 → ⟪ (CCZ013 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨1·0·32·4⟩-at233442 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨1·0·32·4⟩-at3443 c4) ▸
       at 0 2 (Sb1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(4;1;3;0) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·1·3·0⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Sb4-1-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-2-0 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·1·3·0⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb4-1-2-0 ∷ []) (Sb4-1-2-0 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Sb4-1-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·1·2·0⟩ c4) ▸
       at 1 2 (Sb4-1-3-0 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·1·3·0⟩ c4) ▸
       at 0 2 (Sb4-1-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·1·3·0⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(4;1;3;0) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·1·3·0⟩-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Sb3-1-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-2-0 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·1·3·0⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb3-1-2-0 ∷ []) (Sb3-1-2-0 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Sb4-1-2-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨3·1·2·0⟩ c4) ▸
       at 1 2 (Sb4-1-2-0 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·1·3·0⟩-at2332 c4) ▸
       at 0 2 (Sb3-1-2-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨4·1·2·0⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(4;1;3;0) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·1·3·0⟩-at2442 : Complete 4 → ⟪ (Sb0-1-43-2 ∷ Sb2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-3-0 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·1·3·0⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Sb2-1-3-0 ∷ []) (Sb2-1-3-0 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 (Sb3-1-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·1·3·0⟩ c4) ▸
       at 1 2 (Sb3-1-2-0 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·1·3·0⟩-at243243 c4) ▸
       at 0 2 (Sb2-1-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·1·2·0⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(4;1;3;0) @01102442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·1·3·0⟩-at01102442 : Complete 4 → ⟪ (Sb1-0-43-2 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-1 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·1·3·0⟩-at01102442 c4 = run b0
  where
  b0 : Chain (Sb1-0-43-2 ∷ Sb2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Sb1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 2 2 (Sb2-1-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·3·1⟩ c4) ▸
       at 1 2 (Sb2-1-3-0 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·1·3·0⟩-at2442 c4) ▸
       at 0 2 (Sb2-0-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·3·0⟩ c4) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(4;1;3;0) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·1·3·0⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Sb⁻4-1-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-1-2-0 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·1·3·0⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb⁻4-1-2-0 ∷ []) (Sb⁻4-1-2-0 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Sb⁻4-1-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·1·2·0⟩ c4) ▸
       at 1 2 (Sb⁻4-1-3-0 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·1·3·0⟩ c4) ▸
       at 0 2 (Sb⁻4-1-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·1·3·0⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(4;1;3;0) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·1·3·0⟩-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Sb⁻3-1-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-1-2-0 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·1·3·0⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb⁻3-1-2-0 ∷ []) (Sb⁻3-1-2-0 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Sb⁻4-1-2-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨3·1·2·0⟩ c4) ▸
       at 1 2 (Sb⁻4-1-2-0 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·1·3·0⟩-at2332 c4) ▸
       at 0 2 (Sb⁻3-1-2-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨4·1·2·0⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(4;1;3;0) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·1·3·0⟩-at2442 : Complete 4 → ⟪ (Sb0-1-43-2 ∷ Sb⁻2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-3-0 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·1·3·0⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Sb⁻2-1-3-0 ∷ []) (Sb⁻2-1-3-0 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 (Sb⁻3-1-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·1·3·0⟩ c4) ▸
       at 1 2 (Sb⁻3-1-2-0 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·1·3·0⟩-at243243 c4) ▸
       at 0 2 (Sb⁻2-1-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·1·2·0⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(4;1;3;0) @01102442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·1·3·0⟩-at01102442 : Complete 4 → ⟪ (Sb1-0-43-2 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-1 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·1·3·0⟩-at01102442 c4 = run b0
  where
  b0 : Chain (Sb1-0-43-2 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻2-0-3-1 ∷ Sb1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 2 2 (Sb⁻2-1-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·0·3·1⟩ c4) ▸
       at 1 2 (Sb⁻2-1-3-0 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·1·3·0⟩-at2442 c4) ▸
       at 0 2 (Sb⁻2-0-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·1·3·0⟩ c4) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


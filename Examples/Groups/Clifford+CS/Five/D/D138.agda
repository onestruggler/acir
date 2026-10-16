{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D138 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym23 ; lem-sym34)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-T312-beta ; lem-T312-beta-at0314203142 ; lem-T312-beta-at0314213240 ; lem-c124-beta-at3443 ; lem-sym12-at0314203142 ; lem-sym23-at0314203142 ; lem-sym23-at0314213042 ; lem-sym34-at0314213042 ; lem-sym34-at0314213240)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F0 ; lem-sym23-at2332 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-SB2 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-F0-at1221 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-F0-at3443 ; lem-SBsym-at0113203442)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-CS20-beta-ci-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-auto-BOX⟨0·1234⟩-∣-CS42)
open import Examples.Groups.Clifford+CS.Five.D.D080 using (lem-sym12-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D135 using (lem-F0-at0112203443 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ241 ; lem-sym23-at04233240 ; lem-sym23-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D137 using (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·0312⟩ ; lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at243243 ; lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2442 ; lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0412233041)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF024 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF301 ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-2-TOFF201 ; lem-nat-3-BOX⟨0·1324⟩ ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨3·4102⟩ ; lem-nat-0-CCZ034 ; lem-nat-0-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨3·4021⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨3·4120⟩ ; lem-nat-1-BOX⟨3·4012⟩ ; lem-nat-1-BOX⟨3·4021⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨3·4012⟩ ; lem-nat-1-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0124⟩ ; lem-nat-2-BOX⟨3·0412⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-1-BOX⟨3·0412⟩ ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-2-CS02 ; lem-nat-2-CSd02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-1-BOX⟨4·0312⟩ ; lem-nat-3-SBOX⟨2·0·31·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-0-BOX⟨4·0231⟩ ; lem-nat-0-BOX⟨4·1230⟩ ; lem-nat-1-BOX⟨4·0132⟩ ; lem-nat-1-BOX⟨4·0231⟩ ; lem-nat-2-BOX⟨4·0123⟩ ; lem-nat-2-BOX⟨4·0132⟩ ; lem-nat-3-BOX⟨3·0124⟩ ; lem-nat-3-BOX⟨4·0123⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-CS03 ; lem-nat-2-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-TOFF124)
open import Examples.Groups.Clifford+CS.Five.D.R024 using (lem-nat-1-SBOX⟨2·4·1·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R025 using (lem-nat-0-BOX⟨3·4210⟩ ; lem-nat-1-BOX⟨3·4120⟩ ; lem-nat-2-SBOX⟨3·4·1·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R028 using (lem-nat-1-BOX⟨3·0421⟩ ; lem-nat-1-BOX⟨3·4102⟩ ; lem-nat-1-BOX⟨3·4201⟩ ; lem-nat-2-SBOX⟨2·4·1·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R029 using (lem-nat-0-BOX⟨4·0321⟩ ; lem-nat-0-BOX⟨4·1320⟩ ; lem-nat-1-BOX⟨4·0213⟩ ; lem-nat-1-BOX⟨4·0321⟩ ; lem-nat-2-BOX⟨4·0312⟩)
open import Examples.Groups.Clifford+CS.Five.D.R030 using (lem-nat-1-BOX⟨4·0123⟩ ; lem-nat-2-BOX⟨4·0213⟩)
open import Examples.Groups.Clifford+CS.Five.D.R031 using (lem-nat-0-SBOX⟨0·4·2·1⟩ ; lem-nat-0-SBOX⟨1·4·2·0⟩ ; lem-nat-0-SBOX⟨4·0·3·1⟩ ; lem-nat-0-SBOX⟨4·1·3·0⟩ ; lem-nat-1-SBOX⟨1·4·2·0⟩ ; lem-nat-1-SBOX⟨4·1·3·0⟩ ; lem-nat-1-SBOX⟨4·2·3·0⟩ ; lem-nat-1-SBOX⟨4·3·1·0⟩ ; lem-nat-1-SBOX⟨4·3·2·0⟩ ; lem-nat-2-SBOX⟨3·0·21·4⟩ ; lem-nat-2-SBOX⟨4·0·31·2⟩ ; lem-nat-2-SBOX⟨4·2·3·0⟩ ; lem-nat-2-SBOX⟨4·3·2·0⟩ ; lem-nat-2-SBOXd⟨4·0·2·1⟩ ; lem-nat-3-SBOX⟨3·4·1·0⟩ ; lem-nat-3-SBOX⟨4·3·1·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R032 using (lem-nat-0-BOX⟨3·0421⟩ ; lem-nat-0-BOX⟨3·1420⟩ ; lem-nat-0-BOX⟨3·4201⟩ ; lem-nat-0-SBOX⟨3·0·42·1⟩ ; lem-nat-2-SBOX⟨2·0·31·4⟩ ; lem-nat-2-SBOXd⟨4·0·3·1⟩ ; lem-nat-3-SBOX⟨2·0·41·3⟩)
-- auto SBOX(0;1;2;3) | BOX(2;0314) @2442: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2442 : Complete 4 → ⟪ (Sb0-1-4-3 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-3 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Sb0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ c4) ▸
       at 1 2 (Bx4-0213 ∷ Sb0-1-4-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at243243 c4) ▸
       at 0 2 (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ c4) ▸
       at 1 2 (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(4;0312): 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0312⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0312⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 2 (Bx4-0312 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2442 c4) ▸
       at 3 2 (Bx4-0312 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0412233041 c4) ▸
       at 2 2 (Bx4-0312 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2442 c4) ▸
       at 1 2 (Bx4-0312 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0412233041 c4) ▸
       at 0 2 (Bx4-0312 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·0312⟩ c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | SBOX(0;4;2;1): 3 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩ : Complete 4 → ⟪ (Bx0-1234 ∷ Sb0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-2-1 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩ c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Sb0-4-2-1 ∷ []) (Sb0-4-2-1 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS42 c4) ▸
       at 0 1 (Sb0-4-2-1 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CSd03: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd03 : Complete 4 → ⟪ (Bx0-1234 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd03 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CS03⁻ ∷ Bx0-1324 ∷ []) (sym (lem-CS20-beta-ci-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸ done


-- auto SBOX(0;1;23;4) | CSd03: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd03 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd03 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS03⁻ ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS03⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS03⁻ ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS03⁻ ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS03⁻ ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS03⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS03⁻ ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS03⁻ ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS03⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd03 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd03 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd03-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd03-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4) ▸
       at 1 2 (CS03⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd03 c4) ▸
       at 0 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(4;0;2;1): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·2·1⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Sb⁻4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-2-1 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻4-0-2-1 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS02⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd03-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb⁻4-0-2-1 ∷ []) (refl) ▸ done


-- F0 @233442: 5 steps
lem-F0-at233442 : Complete 4 → ⟪ (Sb3-0-21-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-21-3 ∷ []) ⟫ʷ
lem-F0-at233442 c4 = run b0
  where
  b0 : Chain (Sb3-0-21-4 ∷ []) (Sb4-0-21-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb2-0-31-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·21·4⟩ c4) ▸
       at 1 1 (Sb4-0-31-2 ∷ []) (lem-F0-at3443 c4) ▸
       at 0 2 (Sb4-0-21-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·0·31·2⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(4;0312) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0312⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0312⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ c4) ▸
       at 1 2 (Bx4-0312 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0312⟩ c4) ▸
       at 0 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @0110: 8 steps
lem-T312-beta-at0110 : Complete 4 → ⟪ (Toff302 ∷ Bx1-0234 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CCZ024 ∷ []) ⟫ʷ
lem-T312-beta-at0110 c4 = run b0
  where
  b0 : Chain (Toff302 ∷ Bx1-0234 ∷ Toff302 ∷ []) (Bx1-0234 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-T312-beta c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @021021: 8 steps
lem-T312-beta-at021021 : Complete 4 → ⟪ (Toff301 ∷ Bx2-0134 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ CCZ014 ∷ []) ⟫ʷ
lem-T312-beta-at021021 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Bx2-0134 ∷ Toff301 ∷ []) (Bx2-0134 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 2 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 1 3 (Bx1-0234 ∷ CCZ024 ∷ []) (lem-T312-beta-at0110 c4) ▸
       at 0 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @03102132: 8 steps
lem-T312-beta-at03102132 : Complete 4 → ⟪ (Toff201 ∷ Bx3-0124 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ CCZ014 ∷ []) ⟫ʷ
lem-T312-beta-at03102132 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Bx3-0124 ∷ Toff201 ∷ []) (Bx3-0124 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 2 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 1 3 (Bx2-0134 ∷ CCZ014 ∷ []) (lem-T312-beta-at021021 c4) ▸
       at 0 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @0410213243: 8 steps
lem-T312-beta-at0410213243 : Complete 4 → ⟪ (Toff201 ∷ Bx4-0123 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ CCZ013 ∷ []) ⟫ʷ
lem-T312-beta-at0410213243 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Bx4-0123 ∷ Toff201 ∷ []) (Bx4-0123 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 2 2 (Bx3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0123⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 1 3 (Bx3-0124 ∷ CCZ014 ∷ []) (lem-T312-beta-at03102132 c4) ▸
       at 0 2 (Bx4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0124⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @04102142: 8 steps
lem-T312-beta-at04102142 : Complete 4 → ⟪ (Toff301 ∷ Bx4-0132 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0132 ∷ CCZ012 ∷ []) ⟫ʷ
lem-T312-beta-at04102142 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Bx4-0132 ∷ Toff301 ∷ []) (Bx4-0132 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 2 2 (Bx4-0123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0132⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 1 3 (Bx4-0123 ∷ CCZ013 ∷ []) (lem-T312-beta-at0410213243 c4) ▸
       at 0 2 (Bx4-0132 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0123⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @041041: 8 steps
lem-T312-beta-at041041 : Complete 4 → ⟪ (Toff302 ∷ Bx4-0231 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ CCZ012 ∷ []) ⟫ʷ
lem-T312-beta-at041041 c4 = run b0
  where
  b0 : Chain (Toff302 ∷ Bx4-0231 ∷ Toff302 ∷ []) (Bx4-0231 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 2 2 (Bx4-0132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0231⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 1 3 (Bx4-0132 ∷ CCZ012 ∷ []) (lem-T312-beta-at04102142 c4) ▸
       at 0 2 (Bx4-0231 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0132⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @0440: 8 steps
lem-T312-beta-at0440 : Complete 4 → ⟪ (Toff312 ∷ Bx4-1230 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ CCZ012 ∷ []) ⟫ʷ
lem-T312-beta-at0440 c4 = run b0
  where
  b0 : Chain (Toff312 ∷ Bx4-1230 ∷ Toff312 ∷ []) (Bx4-1230 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-0231 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1230⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx4-0231 ∷ CCZ012 ∷ []) (lem-T312-beta-at041041 c4) ▸
       at 0 2 (Bx4-1230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0231⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ134 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0110 : Complete 4 → ⟪ (Bx1-0234 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (CCZ134 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134 c4) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ134 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 2 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0110 c4) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ134 @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ c4) ▸
       at 2 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (CCZ034 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at021021 c4) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ134 @0410213243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410213243 : Complete 4 → ⟪ (Bx4-0123 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Bx4-0123 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ CCZ023 ∷ []) (CCZ023 ∷ Bx4-0123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0123⟩ c4) ▸
       at 2 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (CCZ024 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at03102132 c4) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Bx4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0124⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ134 @04103143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at04103143 : Complete 4 → ⟪ (Bx4-0213 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Bx4-0213 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at04103143 c4 = run b0
  where
  b0 : Chain (Bx4-0213 ∷ CCZ013 ∷ []) (CCZ013 ∷ Bx4-0213 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0213⟩ c4) ▸
       at 2 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (CCZ023 ∷ Bx4-0123 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410213243 c4) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Bx4-0213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0123⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ134 @0410233142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410233142 : Complete 4 → ⟪ (Bx4-0312 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx4-0312 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410233142 c4 = run b0
  where
  b0 : Chain (Bx4-0312 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx4-0312 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ c4) ▸
       at 2 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (CCZ013 ∷ Bx4-0213 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at04103143 c4) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ134 @0410233241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410233241 : Complete 4 → ⟪ (Bx4-0321 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx4-0321 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410233241 c4 = run b0
  where
  b0 : Chain (Bx4-0321 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx4-0321 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0321⟩ c4) ▸
       at 2 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Bx4-0312 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410233142 c4) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0312⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ134 @04233240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at04233240 : Complete 4 → ⟪ (Bx4-1320 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx4-1320 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at04233240 c4 = run b0
  where
  b0 : Chain (Bx4-1320 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx4-1320 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1320⟩ c4) ▸
       at 2 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Bx4-0321 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410233241 c4) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-1320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0321⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | SBOX(0;4;2;1) @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0110 : Complete 4 → ⟪ (Bx1-0234 ∷ Sb1-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-2-0 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ Sb1-4-2-0 ∷ []) (Sb1-4-2-0 ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 2 2 (Sb0-4-2-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·4·2·0⟩ c4) ▸
       at 1 2 (Sb0-4-2-1 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩ c4) ▸
       at 0 2 (Sb1-4-2-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·4·2·1⟩ c4) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | SBOX(0;4;2;1) @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ Sb2-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-1-0 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ Sb2-4-1-0 ∷ []) (Sb2-4-1-0 ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 2 2 (Sb1-4-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·4·1·0⟩ c4) ▸
       at 1 2 (Sb1-4-2-0 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0110 c4) ▸
       at 0 2 (Sb2-4-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·4·2·0⟩ c4) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | SBOX(0;4;2;1) @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ Sb3-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-1-0 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ Sb3-4-1-0 ∷ []) (Sb3-4-1-0 ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ c4) ▸
       at 2 2 (Sb2-4-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·4·1·0⟩ c4) ▸
       at 1 2 (Sb2-4-1-0 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at021021 c4) ▸
       at 0 2 (Sb3-4-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·4·1·0⟩ c4) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | SBOX(0;4;2;1) @0410213243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410213243 : Complete 4 → ⟪ (Bx4-0123 ∷ Sb4-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-3-1-0 ∷ Bx4-0123 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ Sb4-3-1-0 ∷ []) (Sb4-3-1-0 ∷ Bx4-0123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0123⟩ c4) ▸
       at 2 2 (Sb3-4-1-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨4·3·1·0⟩ c4) ▸
       at 1 2 (Sb3-4-1-0 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at03102132 c4) ▸
       at 0 2 (Sb4-3-1-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨3·4·1·0⟩ c4) ▸
       at 1 2 (Bx4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0124⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | SBOX(0;4;2;1) @04103143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at04103143 : Complete 4 → ⟪ (Bx4-0213 ∷ Sb4-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-3-2-0 ∷ Bx4-0213 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at04103143 c4 = run b0
  where
  b0 : Chain (Bx4-0213 ∷ Sb4-3-2-0 ∷ []) (Sb4-3-2-0 ∷ Bx4-0213 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0213⟩ c4) ▸
       at 2 2 (Sb4-3-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨4·3·2·0⟩ c4) ▸
       at 1 2 (Sb4-3-1-0 ∷ Bx4-0123 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410213243 c4) ▸
       at 0 2 (Sb4-3-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨4·3·1·0⟩ c4) ▸
       at 1 2 (Bx4-0213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0123⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | SBOX(0;4;2;1) @0410233142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410233142 : Complete 4 → ⟪ (Bx4-0312 ∷ Sb4-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-3-0 ∷ Bx4-0312 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410233142 c4 = run b0
  where
  b0 : Chain (Bx4-0312 ∷ Sb4-2-3-0 ∷ []) (Sb4-2-3-0 ∷ Bx4-0312 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ c4) ▸
       at 2 2 (Sb4-3-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·2·3·0⟩ c4) ▸
       at 1 2 (Sb4-3-2-0 ∷ Bx4-0213 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at04103143 c4) ▸
       at 0 2 (Sb4-2-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·3·2·0⟩ c4) ▸
       at 1 2 (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | SBOX(0;4;2;1) @0410233241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410233241 : Complete 4 → ⟪ (Bx4-0321 ∷ Sb4-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-3-0 ∷ Bx4-0321 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410233241 c4 = run b0
  where
  b0 : Chain (Bx4-0321 ∷ Sb4-1-3-0 ∷ []) (Sb4-1-3-0 ∷ Bx4-0321 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0321⟩ c4) ▸
       at 2 2 (Sb4-2-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨4·1·3·0⟩ c4) ▸
       at 1 2 (Sb4-2-3-0 ∷ Bx4-0312 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410233142 c4) ▸
       at 0 2 (Sb4-1-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨4·2·3·0⟩ c4) ▸
       at 1 2 (Bx4-0321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0312⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | SBOX(0;4;2;1) @04233240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at04233240 : Complete 4 → ⟪ (Bx4-1320 ∷ Sb4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-3-1 ∷ Bx4-1320 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at04233240 c4 = run b0
  where
  b0 : Chain (Bx4-1320 ∷ Sb4-0-3-1 ∷ []) (Sb4-0-3-1 ∷ Bx4-1320 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1320⟩ c4) ▸
       at 2 2 (Sb4-1-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨4·0·3·1⟩ c4) ▸
       at 1 2 (Sb4-1-3-0 ∷ Bx4-0321 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410233241 c4) ▸
       at 0 2 (Sb4-0-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨4·1·3·0⟩ c4) ▸
       at 1 2 (Bx4-1320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0321⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(4;0;2;1) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·2·1⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Sb⁻4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-3-1 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·2·1⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb⁻4-0-3-1 ∷ []) (Sb⁻4-0-3-1 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Sb⁻4-0-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·0·3·1⟩ c4) ▸
       at 1 2 (Sb⁻4-0-2-1 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·2·1⟩ c4) ▸
       at 0 2 (Sb⁻4-0-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·0·2·1⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(3;0;21;4): 42 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Sb3-0-21-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-21-4 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb3-0-21-4 ∷ []) (Bx4-0213 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ CS01⁻ ∷ Toff312 ∷ CS03 ∷ Toff312 ∷ Sb⁻4-0-3-1 ∷ [])
  b0 = at 1 1 (Sb4-0-21-3 ∷ []) (lem-F0-at233442 c4) ▸
       at 1 1 (Bx4-0213 ∷ Toff312 ∷ Sb4-0-3-1 ∷ Toff312 ∷ Sb⁻4-0-3-1 ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (Bx4-0213 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0312⟩-at2332 c4) ▸
       at 1 1 (Sb4-1-32-0 ∷ []) (lem-F0-at0112203443 c4) ▸
       at 1 1 (Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ []) (refl) ▸
       at 5 1 (CS01⁻ ∷ []) (refl) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸ done

  b1 : Chain (Bx4-0213 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ CS01⁻ ∷ Toff312 ∷ CS03 ∷ Toff312 ∷ Sb⁻4-0-3-1 ∷ []) (Bx4-0213 ∷ Bx4-1320 ∷ Toff312 ∷ Sb4-0-3-1 ∷ Toff312 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ Sb⁻4-0-3-1 ∷ [])
  b1 = at 5 4 (Toff312 ∷ CS03 ∷ Toff312 ∷ CS01⁻ ∷ []) (lw4 c4 (CS01⁻ ∷ Toff312 ∷ CS03 ∷ Toff312 ∷ []) (Toff312 ∷ CS03 ∷ Toff312 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb4-0-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-1-0-2 ∷ []) (refl) ▸
       at 3 1 (CS01 ∷ []) (refl) ▸
       at 6 1 (CS03 ∷ []) (refl) ▸
       at 2 6 (Toff312 ∷ CS03 ∷ Toff312 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS01 ∷ Toff023 ∷ Toff312 ∷ CS03 ∷ Toff312 ∷ []) (Toff312 ∷ CS03 ∷ Toff312 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb4-0-3-1 ∷ []) (refl) ▸
       at 6 1 (Sb4-1-0-2 ∷ []) (refl) ▸ done

  b2 : Chain (Bx4-0213 ∷ Bx4-1320 ∷ Toff312 ∷ Sb4-0-3-1 ∷ Toff312 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ Sb⁻4-0-3-1 ∷ []) (Bx4-0213 ∷ Toff312 ∷ CCZ012 ∷ Sb4-0-3-1 ∷ Bx4-1320 ∷ Toff312 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ Sb⁻4-0-3-1 ∷ [])
  b2 = at 1 0 (Toff312 ∷ Toff312 ∷ []) (lw4 c4 [] (Toff312 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Toff312 ∷ []) (lw4 c4 (Toff312 ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Toff312 ∷ []) (lw4 c4 (Toff312 ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx4-1230 ∷ []) (lem-sym23-at04233240 c4) ▸
       at 2 3 (Bx4-1230 ∷ CCZ012 ∷ []) (lem-T312-beta-at0440 c4) ▸
       at 2 1 (Bx4-1320 ∷ []) (lem-sym23-at0440 c4) ▸
       at 2 2 (CCZ012 ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at04233240 c4) ▸
       at 3 2 (Sb4-0-3-1 ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at04233240 c4) ▸ done

  b3 : Chain (Bx4-0213 ∷ Toff312 ∷ CCZ012 ∷ Sb4-0-3-1 ∷ Bx4-1320 ∷ Toff312 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ Sb⁻4-0-3-1 ∷ []) (Bx4-0213 ∷ CCZ012 ∷ Toff312 ∷ Sb4-0-3-1 ∷ Toff312 ∷ CCZ012 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ Sb⁻4-0-3-1 ∷ [])
  b3 = at 4 0 (Toff312 ∷ Toff312 ∷ []) (lw4 c4 [] (Toff312 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Toff312 ∷ []) (lw4 c4 (Toff312 ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Toff312 ∷ []) (lw4 c4 (Toff312 ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx4-1230 ∷ []) (lem-sym23-at04233240 c4) ▸
       at 5 3 (Bx4-1230 ∷ CCZ012 ∷ []) (lem-T312-beta-at0440 c4) ▸
       at 5 1 (Bx4-1320 ∷ []) (lem-sym23-at0440 c4) ▸
       at 5 2 (CCZ012 ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at04233240 c4) ▸
       at 1 2 (CCZ012 ∷ Toff312 ∷ []) (lw4 c4 (Toff312 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Bx4-0213 ∷ CCZ012 ∷ Toff312 ∷ Sb4-0-3-1 ∷ Toff312 ∷ CCZ012 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ Sb⁻4-0-3-1 ∷ []) (Bx4-0213 ∷ Toff312 ∷ Sb4-0-3-1 ∷ Toff312 ∷ Sb⁻4-0-3-1 ∷ Sb0-1-23-4 ∷ [])
  b4 = at 3 1 (CS03 ∷ []) (refl) ▸
       at 2 4 (CCZ012 ∷ Toff312 ∷ CS03 ∷ Toff312 ∷ []) (lw4 c4 (Toff312 ∷ CS03 ∷ Toff312 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff312 ∷ CS03 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb4-0-3-1 ∷ []) (refl) ▸
       at 1 2 [] (lw4 c4 (CCZ012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb4-1-32-0 ∷ []) (refl) ▸
       at 4 1 (Sb0-1-32-4 ∷ []) (sym (lem-F0-at0112203443 c4)) ▸
       at 4 2 (Sb⁻4-0-3-1 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·2·1⟩-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸ done

  b5 : Chain (Bx4-0213 ∷ Toff312 ∷ Sb4-0-3-1 ∷ Toff312 ∷ Sb⁻4-0-3-1 ∷ Sb0-1-23-4 ∷ []) (Sb3-0-21-4 ∷ Sb0-1-23-4 ∷ [])
  b5 = at 0 5 (Sb4-0-21-3 ∷ []) (refl) ▸
       at 0 1 (Sb3-0-21-4 ∷ []) (sym (lem-F0-at233442 c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(3;0;21;4) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Sb2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-31-4 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb2-0-31-4 ∷ []) (Sb2-0-31-4 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Sb3-0-21-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·31·4⟩ c4) ▸
       at 1 2 (Sb3-0-21-4 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩ c4) ▸
       at 0 2 (Sb2-0-31-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·21·4⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(3;0;21;4) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Sb2-0-31-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 (Sb2-0-31-4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩-at2332 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·31·4⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- F1 comm-CS-CS: 1 steps
lem-F1-comm-CS-CS : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-CS c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩-at243243 c4) ▸ done


-- auto BOX(0;1234) | CCZ123: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 2 (CCZ123 ∷ Bx0-1243 ∷ []) (sym (lem-c124-beta-at3443 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸ done


-- SB2 @1221: 6 steps
lem-SB2-at1221 : Complete 4 → ⟪ (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ []) ⟫ʷ
lem-SB2-at1221 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ []) (CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- SB2 @011220: 6 steps
lem-SB2-at011220 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
lem-SB2-at011220 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (CCZ124 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (CCZ024 ∷ []) (lem-SB2-at1221 c4) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ231 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 : Complete 4 → ⟪ (Bx3-0412 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ c4) ▸
       at 2 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS14 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 : Complete 4 → ⟪ (Bx3-0412 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ CS02 ∷ []) (CS02 ∷ Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ c4) ▸
       at 2 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 1 2 (CS03 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 c4) ▸
       at 0 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 1 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd14 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 : Complete 4 → ⟪ (Bx3-0412 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ c4) ▸
       at 2 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4) ▸
       at 1 2 (CS03⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 c4) ▸
       at 0 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4) ▸
       at 1 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0314203241: 5 steps
lem-sym23-at0314203241 : Complete 4 → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-sym23-at0314203241 c4 = run b0
  where
  b0 : Chain (Bx3-4021 ∷ []) (Bx3-4201 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-4012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4021⟩ c4) ▸
       at 1 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 0 2 (Bx3-4201 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4102⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0314213240: 5 steps
lem-sym23-at0314213240 : Complete 4 → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ []) ⟫ʷ
lem-sym23-at0314213240 c4 = run b0
  where
  b0 : Chain (Bx3-4120 ∷ []) (Bx3-4210 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-4021 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4120⟩ c4) ▸
       at 1 1 (Bx3-4201 ∷ []) (lem-sym23-at0314203241 c4) ▸
       at 0 2 (Bx3-4210 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4201⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @0314213042: 8 steps
lem-T312-beta-at0314213042 : Complete 4 → ⟪ (Toff014 ∷ Bx3-4102 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ CCZ124 ∷ []) ⟫ʷ
lem-T312-beta-at0314213042 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Bx3-4102 ∷ Toff014 ∷ []) (Bx3-4102 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 2 2 (Bx3-4012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4102⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 1 3 (Bx3-4012 ∷ CCZ024 ∷ []) (lem-T312-beta-at0314203142 c4) ▸
       at 0 2 (Bx3-4102 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4012⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @03143041: 8 steps
lem-T312-beta-at03143041 : Complete 4 → ⟪ (Toff024 ∷ Bx3-4201 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ CCZ124 ∷ []) ⟫ʷ
lem-T312-beta-at03143041 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ Bx3-4201 ∷ Toff024 ∷ []) (Bx3-4201 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 2 2 (Bx3-4102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4201⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 1 3 (Bx3-4102 ∷ CCZ124 ∷ []) (lem-T312-beta-at0314213042 c4) ▸
       at 0 2 (Bx3-4201 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4102⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @03143140: 8 steps
lem-T312-beta-at03143140 : Complete 4 → ⟪ (Toff124 ∷ Bx3-4210 ∷ Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ CCZ024 ∷ []) ⟫ʷ
lem-T312-beta-at03143140 c4 = run b0
  where
  b0 : Chain (Toff124 ∷ Bx3-4210 ∷ Toff124 ∷ []) (Bx3-4210 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 2 2 (Bx3-4201 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4210⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 1 3 (Bx3-4201 ∷ CCZ124 ∷ []) (lem-T312-beta-at03143041 c4) ▸
       at 0 2 (Bx3-4210 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4201⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @03143041: 5 steps
lem-sym23-at03143041 : Complete 4 → ⟪ (Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-sym23-at03143041 c4 = run b0
  where
  b0 : Chain (Bx3-4201 ∷ []) (Bx3-4021 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-4102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4201⟩ c4) ▸
       at 1 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 0 2 (Bx3-4021 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4012⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @03143140: 5 steps
lem-sym23-at03143140 : Complete 4 → ⟪ (Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-sym23-at03143140 c4 = run b0
  where
  b0 : Chain (Bx3-4210 ∷ []) (Bx3-4120 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-4201 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4210⟩ c4) ▸
       at 1 1 (Bx3-4021 ∷ []) (lem-sym23-at03143041 c4) ▸
       at 0 2 (Bx3-4120 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4021⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ241 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (CCZ124 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241 c4) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ241 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ134 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at2332 c4) ▸
       at 0 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ241 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (CCZ134 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at243243 c4) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ241 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 2 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0110243243 c4) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ241 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 : Complete 4 → ⟪ (Bx3-0412 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ c4) ▸
       at 2 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (CCZ034 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F1 rel-266 [nf of rhs]: 55 steps
lem-F1-rel-266-nf-of-rhs : Complete 4 → ⟪ (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-F1-rel-266-nf-of-rhs c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Sb2-0-41-3 ∷ Toff124 ∷ Toff214 ∷ [])
  b0 = at 1 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 5 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 10 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 14 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 0 4 (Toff214 ∷ []) (lw0 c4 (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff124 ∷ []) (lw0 c4 (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Toff124 ∷ []) (lw0 c4 (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Toff214 ∷ []) (lw0 c4 (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff214 ∷ Toff124 ∷ Sb2-0-41-3 ∷ Toff124 ∷ Toff214 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ Bx3-4120 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ Toff214 ∷ [])
  b1 = at 2 1 (Sb3-0-41-2 ∷ []) (lem-F0 c4) ▸
       at 2 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 4 1 (CS02 ∷ []) (refl) ▸
       at 6 1 (CS02⁻ ∷ []) (refl) ▸
       at 2 0 (Toff214 ∷ Toff214 ∷ []) (lw0 c4 [] (Toff214 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 4 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 4 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸ done

  b2 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ Bx3-4120 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ Toff214 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff214 ∷ Bx3-4012 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ Toff214 ∷ [])
  b2 = at 3 3 (Bx3-4120 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314213240 c4) ▸
       at 3 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 3 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 3 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 3 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4) ▸
       at 4 2 (CS02 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 c4) ▸
       at 5 0 (Toff214 ∷ Toff214 ∷ []) (lw0 c4 [] (Toff214 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸ done

  b3 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff214 ∷ Bx3-4012 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ Toff214 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ Toff124 ∷ Toff214 ∷ [])
  b3 = at 7 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 7 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸
       at 6 3 (Bx3-4120 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314213240 c4) ▸
       at 6 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 6 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 6 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 6 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4) ▸
       at 7 2 (CS02⁻ ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 c4) ▸ done

  b4 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ Toff124 ∷ Toff214 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ Bx3-4102 ∷ CCZ024 ∷ Toff214 ∷ [])
  b4 = at 8 0 (Toff124 ∷ Toff124 ∷ []) (lw0 c4 [] (Toff124 ∷ Toff124 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 10 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 10 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸
       at 10 1 (Bx3-4210 ∷ []) (lem-sym23-at0314213240 c4) ▸
       at 9 3 (Bx3-4210 ∷ CCZ024 ∷ []) (lem-T312-beta-at03143140 c4) ▸
       at 9 1 (Bx3-4120 ∷ []) (lem-sym23-at03143140 c4) ▸
       at 9 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸ done

  b5 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ Bx3-4102 ∷ CCZ024 ∷ Toff214 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ Bx3-4120 ∷ CCZ014 ∷ [])
  b5 = at 9 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 9 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 9 2 (CCZ024 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 c4) ▸
       at 10 0 (Toff214 ∷ Toff214 ∷ []) (lw0 c4 [] (Toff214 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 12 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 12 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸
       at 11 3 (Bx3-4120 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314213240 c4) ▸ done

  b6 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ Bx3-4120 ∷ CCZ014 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b6 = at 11 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 11 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 11 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 11 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4) ▸
       at 9 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff124 ∷ CS02⁻ ∷ []) (pw3 c4 (CS02⁻ ∷ Toff124 ∷ []) (Toff124 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff124 ∷ CCZ014 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ014 ∷ Toff124 ∷ []) (Toff124 ∷ CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done


-- F0 @011220: 5 steps
lem-F0-at011220 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ []) ⟫ʷ
lem-F0-at011220 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ []) (Sb3-1-42-0 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 1 (Sb3-0-42-1 ∷ []) (lem-F0-at1221 c4) ▸
       at 0 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0310243241: 5 steps
lem-sym12-at0310243241 : Complete 4 → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-sym12-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ []) (Bx3-4021 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ c4) ▸
       at 1 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 0 2 (Bx3-4021 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4012⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @03243240: 5 steps
lem-sym12-at03243240 : Complete 4 → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-sym12-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ []) (Bx3-4120 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ c4) ▸
       at 1 1 (Bx3-4021 ∷ []) (lem-sym12-at0310243241 c4) ▸
       at 0 2 (Bx3-4120 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4021⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @03143041: 5 steps
lem-sym34-at03143041 : Complete 4 → ⟪ (Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ []) ⟫ʷ
lem-sym34-at03143041 c4 = run b0
  where
  b0 : Chain (Bx3-4201 ∷ []) (Bx3-4210 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-4102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4201⟩ c4) ▸
       at 1 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸
       at 0 2 (Bx3-4210 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4120⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @03143140: 5 steps
lem-sym34-at03143140 : Complete 4 → ⟪ (Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-sym34-at03143140 c4 = run b0
  where
  b0 : Chain (Bx3-4210 ∷ []) (Bx3-4201 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-4201 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4210⟩ c4) ▸
       at 1 1 (Bx3-4210 ∷ []) (lem-sym34-at03143041 c4) ▸
       at 0 2 (Bx3-4201 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4210⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0314203241: 5 steps
lem-sym12-at0314203241 : Complete 4 → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-sym12-at0314203241 c4 = run b0
  where
  b0 : Chain (Bx3-4021 ∷ []) (Bx3-0421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-4012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4021⟩ c4) ▸
       at 1 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 0 2 (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0314213240: 5 steps
lem-sym12-at0314213240 : Complete 4 → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-sym12-at0314213240 c4 = run b0
  where
  b0 : Chain (Bx3-4120 ∷ []) (Bx3-1420 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-4021 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4120⟩ c4) ▸
       at 1 1 (Bx3-0421 ∷ []) (lem-sym12-at0314203241 c4) ▸
       at 0 2 (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ231 @0310243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243241 : Complete 4 → ⟪ (Bx3-0421 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx3-0421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ c4) ▸
       at 2 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


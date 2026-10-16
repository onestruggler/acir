{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D174 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-beta-T-at243243 ; lem-sym23)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-inv-at0110243243 ; lem-sym12-at0114203243 ; lem-sym12-at132132 ; lem-sym23-at0114203243)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-Cz-beta-at13243142 ; lem-auto-BOX⟨0·1234⟩-∣-TOFF012 ; lem-c124-beta-at0310213442 ; lem-sym12-at12213443 ; lem-sym12-at233442 ; lem-sym12-at3443 ; lem-sym23-at12213443 ; lem-sym23-at12243143 ; lem-sym23-at13213442 ; lem-sym23-at13243142 ; lem-sym23-at2332 ; lem-sym34-at13213442 ; lem-sym34-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym12-at0110243243)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0110243243 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at0110243243 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0110243243)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-X1-beta-at0114203243 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0110243243 ; lem-auto-BOX⟨0·1234⟩-∣-CS13-at0110243243)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-SBsym-at0113203442 ; lem-T312-beta-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-beta-T-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D081 using (lem-sym23-at0310243241)
open import Examples.Groups.Clifford+CS.Five.D.D082 using (lem-sym23-at03103441)
open import Examples.Groups.Clifford+CS.Five.D.D135 using (lem-auto-BOX⟨0·1234⟩-∣-CSd12 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS12-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D145 using (lem-T312-beta-at1441 ; lem-sym34-at143143 ; lem-sym34-at1441)
open import Examples.Groups.Clifford+CS.Five.D.D153 using (lem-sym34-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D157 using (lem-sym23-at12233441 ; lem-sym23-at122441 ; lem-sym34-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D159 using (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D160 using (lem-sym23-at01143043)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨0·4213⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-BOX⟨0·1243⟩ ; lem-nat-2-BOX⟨0·1342⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-CSd12 ; lem-nat-2-CSd13)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-1-SBOX⟨3·0·41·2⟩ ; lem-nat-2-BOX⟨0·1432⟩ ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-BOX⟨0·1423⟩ ; lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-BOX⟨0·1432⟩ ; lem-nat-3-BOX⟨0·1342⟩)
open import Examples.Groups.Clifford+CS.Five.D.R022 using (lem-nat-0-BOX⟨1·0432⟩)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-1-BOX⟨3·0142⟩ ; lem-nat-1-BOX⟨3·0241⟩)
open import Examples.Groups.Clifford+CS.Five.D.R025 using (lem-nat-0-BOX⟨1·4203⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-0-SBOX⟨0·1·2·3⟩ ; lem-nat-0-SBOX⟨1·0·2·3⟩ ; lem-nat-0-SBOXd⟨0·1·2·3⟩ ; lem-nat-0-SBOXd⟨1·0·2·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R037 using (lem-nat-0-BOX⟨0·4231⟩ ; lem-nat-0-BOX⟨1·4230⟩ ; lem-nat-1-SBOX⟨3·0·42·1⟩ ; lem-nat-2-SBOX⟨0·1·2·4⟩ ; lem-nat-2-SBOX⟨0·1·3·4⟩ ; lem-nat-2-SBOX⟨2·0·41·3⟩ ; lem-nat-2-SBOX⟨3·0·41·2⟩ ; lem-nat-2-SBOXd⟨0·1·2·4⟩ ; lem-nat-2-SBOXd⟨0·1·3·4⟩ ; lem-nat-3-BOX⟨0·1432⟩ ; lem-nat-3-SBOX⟨0·1·2·3⟩ ; lem-nat-3-SBOX⟨0·1·2·4⟩ ; lem-nat-3-SBOXd⟨0·1·2·3⟩ ; lem-nat-3-SBOXd⟨0·1·2·4⟩)
-- sym34 @01143043: 5 steps
lem-sym34-at01143043 : Complete 4 → ⟪ (Bx1-4203 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4230 ∷ []) ⟫ʷ
lem-sym34-at01143043 c4 = run b0
  where
  b0 : Chain (Bx1-4203 ∷ []) (Bx1-4230 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4213 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4203⟩ c4) ▸
       at 1 1 (Bx0-4231 ∷ []) (lem-sym34-at143143 c4) ▸
       at 0 2 (Bx1-4230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4231⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @011440: 8 steps
lem-T312-beta-at011440 : Complete 4 → ⟪ (Toff324 ∷ Bx1-4230 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4230 ∷ CCZ024 ∷ []) ⟫ʷ
lem-T312-beta-at011440 c4 = run b0
  where
  b0 : Chain (Toff324 ∷ Bx1-4230 ∷ Toff324 ∷ []) (Bx1-4230 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Bx0-4231 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4230⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 3 (Bx0-4231 ∷ CCZ124 ∷ []) (lem-T312-beta-at1441 c4) ▸
       at 0 2 (Bx1-4230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4231⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @011440: 5 steps
lem-sym34-at011440 : Complete 4 → ⟪ (Bx1-4230 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4203 ∷ []) ⟫ʷ
lem-sym34-at011440 c4 = run b0
  where
  b0 : Chain (Bx1-4230 ∷ []) (Bx1-4203 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4231 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4230⟩ c4) ▸
       at 1 1 (Bx0-4213 ∷ []) (lem-sym34-at1441 c4) ▸
       at 0 2 (Bx1-4203 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4213⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5 CS02: 38 steps
lem-F5-CS02 : Complete 4 → ⟪ (X4 ∷ Sb1-0-42-3 ∷ X4 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
lem-F5-CS02 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (X4 ∷ Sb1-0-42-3 ∷ X4 ∷ Sb1-0-42-3 ∷ []) (CCZ023 ∷ Bx1-0423 ∷ X4 ∷ Toff324 ∷ CS03 ∷ Toff324 ∷ CS03⁻ ∷ X4 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b0 = at 1 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx1-4023 ∷ []) (lem-sym12-at0110243243 c4) ▸
       at 0 3 (CCZ023 ∷ Bx1-4023 ∷ []) (lem-X1-beta-at0114203243 c4) ▸
       at 1 1 (Bx1-0423 ∷ []) (lem-sym12-at0114203243 c4) ▸
       at 8 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Bx1-0423 ∷ X4 ∷ Toff324 ∷ CS03 ∷ Toff324 ∷ CS03⁻ ∷ X4 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (CCZ023 ∷ CS02 ∷ CCZ023 ∷ CS03 ∷ Toff324 ∷ Toff324 ∷ Bx1-4023 ∷ Toff324 ∷ CS03⁻ ∷ Toff324 ∷ Bx1-0423 ∷ Toff324 ∷ CS03 ∷ Toff324 ∷ CS03⁻ ∷ [])
  b1 = at 10 1 (CS03 ∷ []) (refl) ▸
       at 12 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 6 (CS02 ∷ CCZ023 ∷ CS03 ∷ Toff324 ∷ CS03⁻ ∷ Toff324 ∷ []) (pw1 c4 (X4 ∷ Toff324 ∷ CS03 ∷ Toff324 ∷ CS03⁻ ∷ X4 ∷ []) (CS02 ∷ CCZ023 ∷ CS03 ∷ Toff324 ∷ CS03⁻ ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at0110243243 c4) ▸
       at 2 2 (CCZ023 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0110243243 c4) ▸
       at 3 2 (CS03 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0110243243 c4) ▸
       at 4 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx1-4023 ∷ []) (lem-sym12-at0110243243 c4) ▸ done

  b2 : Chain (CCZ023 ∷ CS02 ∷ CCZ023 ∷ CS03 ∷ Toff324 ∷ Toff324 ∷ Bx1-4023 ∷ Toff324 ∷ CS03⁻ ∷ Toff324 ∷ Bx1-0423 ∷ Toff324 ∷ CS03 ∷ Toff324 ∷ CS03⁻ ∷ []) (CCZ023 ∷ CS02 ∷ CCZ023 ∷ CS03 ∷ Toff324 ∷ CCZ024 ∷ CS03⁻ ∷ Bx1-0423 ∷ Toff324 ∷ Bx1-0423 ∷ Toff324 ∷ CS03 ∷ Toff324 ∷ CS03⁻ ∷ [])
  b2 = at 6 1 (Bx1-4203 ∷ []) (lem-sym23-at0114203243 c4) ▸
       at 6 1 (Bx1-4230 ∷ []) (lem-sym34-at01143043 c4) ▸
       at 5 3 (Bx1-4230 ∷ CCZ024 ∷ []) (lem-T312-beta-at011440 c4) ▸
       at 5 1 (Bx1-4203 ∷ []) (lem-sym34-at011440 c4) ▸
       at 5 1 (Bx1-4023 ∷ []) (lem-sym23-at01143043 c4) ▸
       at 5 1 (Bx1-0423 ∷ []) (lem-sym12-at0114203243 c4) ▸
       at 5 2 (CCZ024 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0110243243 c4) ▸
       at 6 2 (CS03⁻ ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0110243243 c4) ▸ done

  b3 : Chain (CCZ023 ∷ CS02 ∷ CCZ023 ∷ CS03 ∷ Toff324 ∷ CCZ024 ∷ CS03⁻ ∷ Bx1-0423 ∷ Toff324 ∷ Bx1-0423 ∷ Toff324 ∷ CS03 ∷ Toff324 ∷ CS03⁻ ∷ []) (CCZ023 ∷ CS02 ∷ CCZ023 ∷ CS03 ∷ Toff324 ∷ CCZ024 ∷ CS03⁻ ∷ Toff324 ∷ Bx1-0423 ∷ CCZ024 ∷ Bx1-0423 ∷ Toff324 ∷ CS03 ∷ Toff324 ∷ CS03⁻ ∷ [])
  b3 = at 7 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Bx1-4023 ∷ []) (lem-sym12-at0110243243 c4) ▸
       at 9 1 (Bx1-4203 ∷ []) (lem-sym23-at0114203243 c4) ▸
       at 9 1 (Bx1-4230 ∷ []) (lem-sym34-at01143043 c4) ▸
       at 8 3 (Bx1-4230 ∷ CCZ024 ∷ []) (lem-T312-beta-at011440 c4) ▸
       at 8 1 (Bx1-4203 ∷ []) (lem-sym34-at011440 c4) ▸
       at 8 1 (Bx1-4023 ∷ []) (lem-sym23-at01143043 c4) ▸
       at 8 1 (Bx1-0423 ∷ []) (lem-sym12-at0114203243 c4) ▸ done

  b4 : Chain (CCZ023 ∷ CS02 ∷ CCZ023 ∷ CS03 ∷ Toff324 ∷ CCZ024 ∷ CS03⁻ ∷ Toff324 ∷ Bx1-0423 ∷ CCZ024 ∷ Bx1-0423 ∷ Toff324 ∷ CS03 ∷ Toff324 ∷ CS03⁻ ∷ []) (CS02 ∷ [])
  b4 = at 8 2 (CCZ024 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0110243243 c4) ▸
       at 1 5 (CCZ024 ∷ CS02 ∷ CCZ023 ∷ CS03 ∷ Toff324 ∷ []) (pw1 c4 (CS02 ∷ CCZ023 ∷ CS03 ∷ Toff324 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS02 ∷ CCZ023 ∷ CS03 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 2 7 (CCZ024 ∷ CS02 ∷ CCZ023 ∷ CS03 ∷ Toff324 ∷ CS03⁻ ∷ Toff324 ∷ []) (pw1 c4 (CS02 ∷ CCZ023 ∷ CS03 ∷ Toff324 ∷ CS03⁻ ∷ Toff324 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS02 ∷ CCZ023 ∷ CS03 ∷ Toff324 ∷ CS03⁻ ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lem-beta-inv-at0110243243 c4) ▸
       at 0 11 (CS02 ∷ []) (pw1 c4 (CCZ023 ∷ CS02 ∷ CCZ023 ∷ CS03 ∷ Toff324 ∷ CS03⁻ ∷ Toff324 ∷ Toff324 ∷ CS03 ∷ Toff324 ∷ CS03⁻ ∷ []) (CS02 ∷ []) tt tt Eq.refl) ▸ done


-- auto CS01 | SBOX(2;0;31;4) @12213443: 7 steps
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at12213443 : Complete 4 → ⟪ (CS02 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at12213443 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 2 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (Sb2-0-41-3 ∷ CS01 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at3443 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 CS02^0|CS02^1: 63 steps
lem-F4-CS02ᵖ0∣CS02ᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb1-0-42-3 ∷ X4 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS02ᵖ0∣CS02ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (X4 ∷ Sb1-0-42-3 ∷ X4 ∷ Sb1-0-42-3 ∷ []) (CS02 ∷ CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Bx⁻1-03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Toff104 ∷ CCZ014 ∷ [])
  b0 = at 0 4 (CS02 ∷ []) (lem-F5-CS02 c4) ▸
       at 1 0 (CCZ014 ∷ CCZ014 ∷ []) (pw2 c4 [] (CCZ014 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Toff104 ∷ Toff104 ∷ []) (pw2 c4 [] (Toff104 ∷ Toff104 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) (lw4 c4 [] (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx1-03 ∷ []) (refl) ▸
       at 8 1 (Bx1-03 ∷ []) (refl) ▸
       at 3 6 (Bx0-123 ∷ []) (refl) ▸
       at 4 1 (Bx⁻1-03 ∷ []) (refl) ▸ done

  b1 : Chain (CS02 ∷ CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Bx⁻1-03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Toff104 ∷ CCZ014 ∷ []) (CS02 ∷ CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-123 ∷ Toff104 ∷ CCZ014 ∷ [])
  b1 = at 7 1 (Bx⁻1-03 ∷ []) (refl) ▸
       at 4 6 (Bx⁻0-123 ∷ []) (refl) ▸
       at 4 0 (Toff104 ∷ Toff104 ∷ []) (pw2 c4 [] (Toff104 ∷ Toff104 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (CCZ014 ∷ CCZ014 ∷ []) (pw2 c4 [] (CCZ014 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) (lw4 c4 [] (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Bx1-03 ∷ []) (refl) ▸
       at 11 1 (Bx1-03 ∷ []) (refl) ▸
       at 6 6 (Bx0-123 ∷ []) (refl) ▸ done

  b2 : Chain (CS02 ∷ CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-123 ∷ Toff104 ∷ CCZ014 ∷ []) (CS02 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ CS03⁻ ∷ Toff324 ∷ Bx⁻1-0423 ∷ [])
  b2 = at 7 1 (Bx⁻1-03 ∷ []) (refl) ▸
       at 10 1 (Bx⁻1-03 ∷ []) (refl) ▸
       at 7 6 (Bx⁻0-123 ∷ []) (refl) ▸
       at 1 6 (Bx1-0423 ∷ []) (refl) ▸
       at 2 6 (Bx⁻1-0423 ∷ []) (refl) ▸
       at 2 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (CS03 ∷ CS03⁻ ∷ []) (lw4 c4 [] (CS03 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb1-0-3-2 ∷ []) (refl) ▸ done

  b3 : Chain (CS02 ∷ Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ CS03⁻ ∷ Toff324 ∷ Bx⁻1-0423 ∷ []) (Sb1-0-42-3 ∷ CS02 ∷ Sb⁻1-0-42-3 ∷ [])
  b3 = at 4 1 (Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 4 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (CS03⁻ ∷ CS03 ∷ []) (lw4 c4 [] (CS03⁻ ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 6 1 (Sb1-0-3-2 ∷ []) (refl) ▸
       at 1 5 (Sb1-0-42-3 ∷ []) (refl) ▸
       at 2 5 (Sb⁻1-0-42-3 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-42-3 ∷ CS02 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at12213443 c4) ▸ done

  b4 : Chain (Sb1-0-42-3 ∷ CS02 ∷ Sb⁻1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ Bx1-0423 ∷ Toff324 ∷ CS03 ∷ Sb⁻1-0-3-2 ∷ Toff324 ∷ Bx⁻1-0423 ∷ [])
  b4 = at 1 1 (X4 ∷ Sb1-0-42-3 ∷ X4 ∷ Sb1-0-42-3 ∷ []) (sym (lem-F5-CS02 c4)) ▸
       at 5 1 (Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Toff324 ∷ Bx⁻1-0423 ∷ []) (refl) ▸
       at 4 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 8 1 (CS03⁻ ∷ []) (refl) ▸
       at 9 1 (CS03 ∷ []) (refl) ▸
       at 8 2 [] (lw4 c4 (CS03⁻ ∷ CS03 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (Toff324 ∷ Toff324 ∷ []) [] tt tt Eq.refl) ▸
       at 6 1 (CS03 ∷ []) (refl) ▸ done

  b5 : Chain (Sb1-0-42-3 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ Bx1-0423 ∷ Toff324 ∷ CS03 ∷ Sb⁻1-0-3-2 ∷ Toff324 ∷ Bx⁻1-0423 ∷ []) (Sb1-0-42-3 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Bx⁻0-123 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-123 ∷ Toff104 ∷ CCZ014 ∷ [])
  b5 = at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 6 2 [] (lw4 c4 (CS03 ∷ CS03⁻ ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Toff324 ∷ Toff324 ∷ []) [] tt tt Eq.refl) ▸
       at 5 1 (Bx⁻0-123 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-123 ∷ Toff104 ∷ CCZ014 ∷ []) (refl) ▸
       at 4 1 (CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ []) (refl) ▸
       at 9 1 (CCZ012 ∷ Toff012 ∷ Bx1-03 ∷ Toff012 ∷ CCZ012 ∷ Bx1-03 ∷ []) (refl) ▸
       at 11 1 (CZ03 ∷ []) (refl) ▸
       at 14 1 (CZ03 ∷ []) (refl) ▸ done

  b6 : Chain (Sb1-0-42-3 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Bx⁻0-123 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-123 ∷ Toff104 ∷ CCZ014 ∷ []) (Sb1-0-42-3 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ CCZ014 ∷ Toff104 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Bx1-03 ∷ Bx⁻0-123 ∷ Toff104 ∷ CCZ014 ∷ [])
  b6 = at 15 1 (Bx⁻1-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 15 1 (CZ03 ∷ []) (refl) ▸
       at 18 1 (CZ03 ∷ []) (refl) ▸
       at 9 12 [] (lw4 c4 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (pw2 c4 (Toff104 ∷ Toff104 ∷ []) [] tt tt Eq.refl) ▸
       at 6 1 (CCZ012 ∷ Toff012 ∷ Bx1-03 ∷ Toff012 ∷ CCZ012 ∷ Bx1-03 ∷ []) (refl) ▸
       at 8 1 (CZ03 ∷ []) (refl) ▸ done

  b7 : Chain (Sb1-0-42-3 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ CCZ014 ∷ Toff104 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Bx1-03 ∷ Bx⁻0-123 ∷ Toff104 ∷ CCZ014 ∷ []) (Sb1-0-42-3 ∷ X4 ∷ Sb1-0-42-3 ∷ X4 ∷ [])
  b7 = at 11 1 (CZ03 ∷ []) (refl) ▸
       at 12 1 (Bx⁻1-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 12 1 (CZ03 ∷ []) (refl) ▸
       at 15 1 (CZ03 ∷ []) (refl) ▸
       at 6 12 [] (lw4 c4 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (pw2 c4 (Toff104 ∷ Toff104 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;1423): 14 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx0-1423 ∷ []) (Toff014 ∷ CCZ023 ∷ CS12⁻ ∷ Toff014 ∷ CCZ023 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Toff014 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 2 (CCZ023 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 2 1 (CS12⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ CS12⁻ ∷ Toff014 ∷ CCZ023 ∷ []) (Bx0-1423 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 2 2 (Toff014 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 3 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 2 (CCZ023 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;1423): 14 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩ : Complete 4 → ⟪ (Sb0-1-2-3 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-2-3 ∷ Bx0-1423 ∷ []) (Toff014 ∷ CCZ023 ∷ CS12 ∷ Toff014 ∷ CCZ023 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 0 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (Toff014 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ Toff014 ∷ []) (Toff014 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 1 1 (CS12 ∷ []) (refl) ▸
       at 1 2 (CCZ023 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 2 1 (CS12 ∷ []) (refl) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ CS12 ∷ Toff014 ∷ CCZ023 ∷ []) (Bx0-1423 ∷ Sb0-1-2-3 ∷ [])
  b1 = at 2 2 (Toff014 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ Toff014 ∷ []) (Toff014 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 3 2 (CCZ023 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸ done


-- auto BOX(0;1234) | CCZ043: 11 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ043 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx0-3124 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym12-at233442 c4) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4) ▸
       at 0 2 (CCZ034 ∷ Bx0-3412 ∷ []) (sym (lem-Cz-beta-at13243142 c4)) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4) ▸ done

  b1 : Chain (CCZ034 ∷ Bx0-3124 ∷ []) (CCZ034 ∷ Bx0-1234 ∷ [])
  b1 = at 1 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(0;1243): 6 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·1243⟩ : Complete 4 → ⟪ (Bx0-1234 ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·1243⟩ c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Bx0-1243 ∷ []) (Bx0-1243 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at3443 c4) ▸
       at 0 2 (Toff012 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012 c4) ▸
       at 1 2 (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ043 c4) ▸
       at 2 2 (Toff012 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012 c4) ▸
       at 3 2 (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ043 c4) ▸
       at 0 4 (Bx0-1243 ∷ []) (sym (lem-beta-T-at3443 c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;1423) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩-at2332 : Complete 4 → ⟪ (Sb⁻0-1-3-2 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-3-2 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (Bx0-1423 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩ c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;1423) @243243: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩-at243243 : Complete 4 → ⟪ (Sb⁻0-1-4-2 ∷ Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-2 ∷ Bx0-1342 ∷ []) (Bx0-1342 ∷ Sb⁻0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx0-1432 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1342⟩ c4) ▸
       at 1 2 (Bx0-1432 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩-at2332 c4) ▸
       at 0 2 (Bx0-1342 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;1423) @2442: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩-at2442 : Complete 4 → ⟪ (Sb⁻0-1-4-3 ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-3 ∷ Bx0-1243 ∷ []) (Bx0-1243 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx0-1342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1243⟩ c4) ▸
       at 1 2 (Bx0-1342 ∷ Sb⁻0-1-4-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩-at243243 c4) ▸
       at 0 2 (Bx0-1243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1342⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;1423) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩-at2332 : Complete 4 → ⟪ (Sb0-1-3-2 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-3-2 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ Sb0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (Bx0-1423 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩ c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;1423) @243243: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩-at243243 : Complete 4 → ⟪ (Sb0-1-4-2 ∷ Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-2 ∷ Bx0-1342 ∷ []) (Bx0-1342 ∷ Sb0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx0-1432 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1342⟩ c4) ▸
       at 1 2 (Bx0-1432 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩-at2332 c4) ▸
       at 0 2 (Bx0-1342 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;1423) @2442: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩-at2442 : Complete 4 → ⟪ (Sb0-1-4-3 ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-3 ∷ Bx0-1243 ∷ []) (Bx0-1243 ∷ Sb0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx0-1342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1243⟩ c4) ▸
       at 1 2 (Bx0-1342 ∷ Sb0-1-4-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩-at243243 c4) ▸
       at 0 2 (Bx0-1243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1342⟩ c4) ▸
       at 1 2 (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;1243): 34 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1243⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1243⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ Bx0-1243 ∷ []) (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Bx0-2341 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 2 (Bx0-1243 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩-at2442 c4) ▸
       at 5 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-2143 ∷ []) (lem-sym12-at3443 c4) ▸
       at 4 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 4 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸
       at 4 1 (Bx0-2341 ∷ []) (lem-sym23-at122441 c4) ▸
       at 3 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-T312-beta-at12233441 c4) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Bx0-2341 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx0-1234 ∷ Toff423 ∷ Bx0-2413 ∷ Toff423 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b1 = at 3 1 (Bx0-2431 ∷ []) (lem-sym23-at12233441 c4) ▸
       at 3 1 (Bx0-2413 ∷ []) (lem-sym34-at122441 c4) ▸
       at 3 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 3 1 (Bx0-1243 ∷ []) (lem-sym12-at12213443 c4) ▸
       at 2 2 (Bx0-1243 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1423⟩-at2442 c4) ▸
       at 3 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-2143 ∷ []) (lem-sym12-at3443 c4) ▸
       at 2 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸ done

  b2 : Chain (Bx0-1234 ∷ Toff423 ∷ Bx0-2413 ∷ Toff423 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx0-1243 ∷ Bx0-1234 ∷ CCZ123 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b2 = at 2 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸
       at 2 1 (Bx0-2341 ∷ []) (lem-sym23-at122441 c4) ▸
       at 1 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-T312-beta-at12233441 c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-sym23-at12233441 c4) ▸
       at 1 1 (Bx0-2413 ∷ []) (lem-sym34-at122441 c4) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym12-at12213443 c4) ▸
       at 0 2 (Bx0-1243 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·1243⟩ c4) ▸ done

  b3 : Chain (Bx0-1243 ∷ Bx0-1234 ∷ CCZ123 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx0-1243 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ123 ∷ CCZ123 ∷ [])
  b3 = at 7 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 3 (Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ Toff423 ∷ CS14⁻ ∷ []) (Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14 ∷ []) (refl) ▸
       at 6 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 5 (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸ done

  b4 : Chain (Bx0-1243 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ123 ∷ CCZ123 ∷ []) (Bx0-1243 ∷ Sb0-1-23-4 ∷ [])
  b4 = at 6 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- c124-beta @03103441: 7 steps
lem-c124-beta-at03103441 : Complete 4 → ⟪ (CCZ012 ∷ Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ CCZ012 ∷ []) ⟫ʷ
lem-c124-beta-at03103441 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-0241 ∷ []) (Bx3-0241 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-0142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0241⟩ c4) ▸
       at 1 2 (Bx3-0142 ∷ CCZ012 ∷ []) (lem-c124-beta-at0310213442 c4) ▸
       at 0 2 (Bx3-0241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0142⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;0421): 5 steps
lem-auto-CCZ012-∣-BOX⟨3·0421⟩ : Complete 4 → ⟪ (CCZ012 ∷ Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0421⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-0421 ∷ []) (Bx3-0421 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx3-0241 ∷ []) (lem-sym23-at0310243241 c4) ▸
       at 0 2 (Bx3-0241 ∷ CCZ012 ∷ []) (lem-c124-beta-at03103441 c4) ▸
       at 0 1 (Bx3-0421 ∷ []) (lem-sym23-at03103441 c4) ▸
       at 1 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;0;42;1): 9 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩ : Complete 4 → ⟪ (CCZ012 ∷ Sb3-0-42-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-42-1 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Sb3-0-42-1 ∷ []) (Bx3-0421 ∷ Toff124 ∷ Sb3-0-1-2 ∷ Toff124 ∷ Sb⁻3-0-1-2 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx3-0421 ∷ Toff124 ∷ Sb3-0-1-2 ∷ Toff124 ∷ Sb⁻3-0-1-2 ∷ []) (refl) ▸
       at 0 2 (Bx3-0421 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0421⟩ c4) ▸
       at 3 1 (CS01 ∷ []) (refl) ▸
       at 1 4 (Toff124 ∷ CS01 ∷ Toff124 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ Toff124 ∷ CS01 ∷ Toff124 ∷ []) (Toff124 ∷ CS01 ∷ Toff124 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb3-0-1-2 ∷ []) (refl) ▸
       at 5 1 (CS01⁻ ∷ []) (refl) ▸
       at 4 2 (CS01⁻ ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻3-0-1-2 ∷ []) (refl) ▸ done

  b1 : Chain (Bx3-0421 ∷ Toff124 ∷ Sb3-0-1-2 ∷ Toff124 ∷ Sb⁻3-0-1-2 ∷ CCZ012 ∷ []) (Sb3-0-42-1 ∷ CCZ012 ∷ [])
  b1 = at 0 5 (Sb3-0-42-1 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;1;3;4): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·3·4⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Sb0-1-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-4 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb0-1-3-4 ∷ []) (Sb0-1-3-4 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS13 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS12-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb0-1-3-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd12: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd12 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd12 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS12⁻ ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS12⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS12⁻ ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS12⁻ ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS12⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS12⁻ ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS12⁻ ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS12⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd12 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd12 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd12-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd12-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 c4) ▸
       at 1 2 (CS12⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd12 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;1;3;4): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·3·4⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Sb⁻0-1-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-4 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb⁻0-1-3-4 ∷ []) (Sb⁻0-1-3-4 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS13⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd12-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb⁻0-1-3-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;1243) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1243⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1243⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Bx0-1342 ∷ []) (Bx0-1342 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Bx0-1243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1342⟩ c4) ▸
       at 1 2 (Bx0-1243 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1243⟩ c4) ▸
       at 0 2 (Bx0-1342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1243⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;1243) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1243⟩-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1243⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Bx0-1342 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (Bx0-1342 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1243⟩-at2332 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1342⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;1243) @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1243⟩-at0110243243 : Complete 4 → ⟪ (Sb1-0-42-3 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1243⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ Bx1-0432 ∷ []) (Bx1-0432 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ c4) ▸
       at 1 2 (Bx0-1432 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1243⟩-at243243 c4) ▸
       at 0 2 (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;0;42;1) @1221: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩-at1221 : Complete 4 → ⟪ (CCZ012 ∷ Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩-at1221 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Sb3-0-41-2 ∷ []) (Sb3-0-41-2 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ c4) ▸
       at 1 2 (Sb3-0-42-1 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩ c4) ▸
       at 0 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;0;42;1) @132132: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩-at132132 : Complete 4 → ⟪ (CCZ013 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩-at132132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 (Sb3-0-41-2 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩-at1221 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;0;42;1) @1331: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩-at1331 : Complete 4 → ⟪ (CCZ023 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩-at1331 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (Sb2-0-41-3 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩-at132132 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;1;3;4) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·3·4⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Sb0-1-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-4 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·3·4⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb0-1-2-4 ∷ []) (Sb0-1-2-4 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Sb0-1-3-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·4⟩ c4) ▸
       at 1 2 (Sb0-1-3-4 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·3·4⟩ c4) ▸
       at 0 2 (Sb0-1-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·4⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;1;3;4) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·3·4⟩-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·3·4⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-2-3 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Sb0-1-2-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·2·3⟩ c4) ▸
       at 1 2 (Sb0-1-2-4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·3·4⟩-at2332 c4) ▸
       at 0 2 (Sb0-1-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·2·4⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;1;3;4) @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·3·4⟩-at0110243243 : Complete 4 → ⟪ (Sb1-0-42-3 ∷ Sb1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-3 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·3·4⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-2-3 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 (Sb0-1-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·3·4⟩-at243243 c4) ▸
       at 0 2 (Sb1-0-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·2·3⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;1;3;4) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·3·4⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Sb⁻0-1-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-4 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·3·4⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb⁻0-1-2-4 ∷ []) (Sb⁻0-1-2-4 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Sb⁻0-1-3-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·4⟩ c4) ▸
       at 1 2 (Sb⁻0-1-3-4 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·3·4⟩ c4) ▸
       at 0 2 (Sb⁻0-1-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·4⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;1;3;4) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·3·4⟩-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·3·4⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Sb⁻0-1-2-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 1 2 (Sb⁻0-1-2-4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·3·4⟩-at2332 c4) ▸
       at 0 2 (Sb⁻0-1-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·2·4⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;1;3;4) @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·3·4⟩-at0110243243 : Complete 4 → ⟪ (Sb1-0-42-3 ∷ Sb⁻1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-3 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·3·4⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-2-3 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 (Sb⁻0-1-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·3·4⟩-at243243 c4) ▸
       at 0 2 (Sb⁻1-0-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


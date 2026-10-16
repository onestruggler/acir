{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D191 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym12 ; lem-sym23)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at14213243 ; lem-sym12-at1221 ; lem-sym12-at132132 ; lem-sym23-at132132 ; lem-sym34-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-Cz-beta-at2332 ; lem-c124-beta-at0310213442 ; lem-sym23-at12213443 ; lem-sym23-at12243143 ; lem-sym23-at2332 ; lem-sym34-at12213443)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym12-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-SBsym-at0113203442 ; lem-T312-beta-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D080 using (lem-sym23-at1331)
open import Examples.Groups.Clifford+CS.Five.D.D135 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ243)
open import Examples.Groups.Clifford+CS.Five.D.D136 using (lem-CX23-beta-at122331 ; lem-CX23-beta-at1331 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at2332 ; lem-sym12-at122331 ; lem-sym12-at1331)
open import Examples.Groups.Clifford+CS.Five.D.D142 using (lem-T-beta-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D143 using (lem-sym23-at0312203441 ; lem-sym23-at0312243041)
open import Examples.Groups.Clifford+CS.Five.D.D145 using (lem-sym12-at122441 ; lem-sym12-at1441)
open import Examples.Groups.Clifford+CS.Five.D.D150 using (lem-T312-beta-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D154 using (lem-X1-beta-at1441)
open import Examples.Groups.Clifford+CS.Five.D.D157 using (lem-beta-T-at122441 ; lem-sym23-at12233441 ; lem-sym23-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D163 using (lem-auto-BOX⟨0·1234⟩-∣-CSd10)
open import Examples.Groups.Clifford+CS.Five.D.D167 using (lem-auto-CCZ012-∣-CCZ341-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D169 using (lem-T312-beta-at0112233440 ; lem-auto-CCZ012-∣-TOFF301-SBOXd⟨2·4·3·1⟩-at0213203441 ; lem-sym23-at0112233440 ; lem-sym23-at01122440)
open import Examples.Groups.Clifford+CS.Five.D.D189 using (lem-F0-at01132032)
open import Examples.Groups.Clifford+CS.Five.D.D190 using (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·2430⟩ ; lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·2430⟩)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-1-TOFF014 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-TOFF024)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-BOX⟨0·4132⟩ ; lem-nat-2-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-2-SBOX⟨0·1·42·3⟩ ; lem-nat-2-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-BOX⟨0·2431⟩ ; lem-nat-0-BOX⟨1·2430⟩ ; lem-nat-1-SBOX⟨0·2·43·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R032 using (lem-nat-1-BOX⟨3·1042⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-0-BOX⟨3·0142⟩ ; lem-nat-0-BOX⟨3·1042⟩ ; lem-nat-0-SBOX⟨0·1·43·2⟩ ; lem-nat-1-BOX⟨0·4231⟩ ; lem-nat-1-BOX⟨3·2041⟩ ; lem-nat-2-BOX⟨0·4231⟩)
open import Examples.Groups.Clifford+CS.Five.D.R034 using (lem-nat-0-SBOX⟨1·0·43·2⟩ ; lem-nat-2-BOX⟨0·2431⟩)
open import Examples.Groups.Clifford+CS.Five.D.R035 using (lem-comm-CCZ023-SBOX⟨0·1·4·3⟩ ; lem-comm-CCZ023-SBOXd⟨0·1·4·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R037 using (lem-nat-0-BOX⟨0·4231⟩ ; lem-nat-0-BOX⟨1·4230⟩ ; lem-nat-2-BOX⟨0·3421⟩ ; lem-nat-2-BOX⟨1·2430⟩ ; lem-nat-2-BOX⟨1·3420⟩)
open import Examples.Groups.Clifford+CS.Five.D.R040 using (lem-nat-0-BOX⟨3·2041⟩ ; lem-nat-0-BOX⟨3·2140⟩ ; lem-nat-0-BOX⟨3·2401⟩ ; lem-nat-0-BOX⟨3·2410⟩ ; lem-nat-0-SBOX⟨2·0·43·1⟩ ; lem-nat-0-SBOX⟨2·1·43·0⟩ ; lem-nat-1-SBOX⟨2·1·43·0⟩ ; lem-nat-1-SBOX⟨3·1·42·0⟩ ; lem-nat-1-SBOX⟨3·2·41·0⟩ ; lem-nat-2-BOX⟨0·4321⟩ ; lem-nat-2-BOX⟨1·4230⟩ ; lem-nat-2-BOX⟨1·4320⟩ ; lem-nat-2-SBOX⟨2·1·43·0⟩ ; lem-nat-2-SBOX⟨3·1·42·0⟩ ; lem-nat-3-BOX⟨0·3421⟩ ; lem-nat-3-BOX⟨0·4321⟩ ; lem-nat-3-BOX⟨1·3420⟩ ; lem-nat-3-BOX⟨1·4320⟩)
-- auto BOX(0;1234) | CCZ130: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ130 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ130 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ013 ∷ []) (CCZ013 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CCZ013 ∷ Bx0-1324 ∷ []) (sym (lem-Cz-beta-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- beta-T @142142: 8 steps
lem-beta-T-at142142 : Complete 4 → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-beta-T-at142142 c4 = run b0
  where
  b0 : Chain (Bx0-4132 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4132⟩ c4) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at14213243 c4) ▸
       at 0 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 1 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 3 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @1441: 8 steps
lem-beta-T-at1441 : Complete 4 → ⟪ (Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-beta-T-at1441 c4 = run b0
  where
  b0 : Chain (Bx0-4231 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·4231⟩ c4) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at142142 c4) ▸
       at 0 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 3 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @011440: 8 steps
lem-beta-T-at011440 : Complete 4 → ⟪ (Bx1-4230 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ []) ⟫ʷ
lem-beta-T-at011440 c4 = run b0
  where
  b0 : Chain (Bx1-4230 ∷ []) (Toff124 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4231 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4230⟩ c4) ▸
       at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at1441 c4) ▸
       at 0 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 3 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ341 @01132032: 7 steps
lem-auto-CCZ012-∣-CCZ341-at01132032 : Complete 4 → ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ341-at01132032 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-CCZ341-at132132 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(1;4230): 31 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·4230⟩ : Complete 4 → ⟪ (Bx0-1234 ∷ Bx1-4230 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4230 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·4230⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Bx0-1234 ∷ Bx1-4230 ∷ []) (Toff124 ∷ Bx0-2413 ∷ CCZ234 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ [])
  b0 = at 1 1 (Toff124 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ []) (lem-beta-T-at011440 c4) ▸
       at 0 0 (Toff124 ∷ Toff124 ∷ []) (lw0 c4 [] (Toff124 ∷ Toff124 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Toff124 ∷ []) (lw0 c4 (Toff124 ∷ []) (Toff124 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Toff124 ∷ []) (lw0 c4 (Toff124 ∷ []) (Toff124 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 2 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 2 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 1 3 (Bx0-2413 ∷ CCZ234 ∷ []) (lem-T312-beta-at12243143 c4) ▸ done

  b1 : Chain (Toff124 ∷ Bx0-2413 ∷ CCZ234 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ []) (Toff124 ∷ CCZ234 ∷ CCZ013 ∷ Toff124 ∷ Toff124 ∷ Bx0-1234 ∷ Toff124 ∷ CCZ013 ∷ [])
  b1 = at 1 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 1 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243 c4) ▸
       at 2 2 (CCZ013 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ130 c4) ▸
       at 3 0 (Toff124 ∷ Toff124 ∷ []) (lw0 c4 [] (Toff124 ∷ Toff124 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Toff124 ∷ []) (lw0 c4 (Toff124 ∷ []) (Toff124 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Toff124 ∷ []) (lw0 c4 (Toff124 ∷ []) (Toff124 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff124 ∷ CCZ234 ∷ CCZ013 ∷ Toff124 ∷ Toff124 ∷ Bx0-1234 ∷ Toff124 ∷ CCZ013 ∷ []) (Toff124 ∷ CCZ234 ∷ CCZ013 ∷ Toff124 ∷ CCZ234 ∷ Bx0-1234 ∷ CCZ013 ∷ [])
  b2 = at 5 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 5 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 5 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 4 3 (Bx0-2413 ∷ CCZ234 ∷ []) (lem-T312-beta-at12243143 c4) ▸
       at 4 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 4 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸
       at 4 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 4 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243 c4) ▸ done

  b3 : Chain (Toff124 ∷ CCZ234 ∷ CCZ013 ∷ Toff124 ∷ CCZ234 ∷ Bx0-1234 ∷ CCZ013 ∷ []) (Bx1-4230 ∷ Bx0-1234 ∷ [])
  b3 = at 5 2 (CCZ013 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ130 c4) ▸
       at 0 2 (CCZ234 ∷ Toff124 ∷ []) (lw0 c4 (Toff124 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ Toff124 ∷ []) (lw0 c4 (Toff124 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff124 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ234 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-CCZ341-at01132032 c4) ▸
       at 1 2 (CCZ234 ∷ Toff124 ∷ []) (lw0 c4 (Toff124 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff124 ∷ []) tt tt Eq.refl) ▸
       at 0 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx1-4230 ∷ []) (sym (lem-beta-T-at011440 c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(1;2430) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·2430⟩-at2332 : Complete 4 → ⟪ (Sb⁻0-1-3-2 ∷ Bx1-3420 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3420 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·2430⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-3-2 ∷ Bx1-3420 ∷ []) (Bx1-3420 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx1-2430 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·3420⟩ c4) ▸
       at 1 2 (Bx1-2430 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·2430⟩ c4) ▸
       at 0 2 (Bx1-3420 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·2430⟩ c4) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(1;2430) @243243: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·2430⟩-at243243 : Complete 4 → ⟪ (Sb⁻0-1-4-2 ∷ Bx1-4320 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4320 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·2430⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-2 ∷ Bx1-4320 ∷ []) (Bx1-4320 ∷ Sb⁻0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx1-3420 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·4320⟩ c4) ▸
       at 1 2 (Bx1-3420 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·2430⟩-at2332 c4) ▸
       at 0 2 (Bx1-4320 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·3420⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(1;2430) @2442: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·2430⟩-at2442 : Complete 4 → ⟪ (Sb⁻0-1-4-3 ∷ Bx1-4230 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4230 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·2430⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-3 ∷ Bx1-4230 ∷ []) (Bx1-4230 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx1-4320 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·4230⟩ c4) ▸
       at 1 2 (Bx1-4320 ∷ Sb⁻0-1-4-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·2430⟩-at243243 c4) ▸
       at 0 2 (Bx1-4230 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·4320⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @011440: 5 steps
lem-sym12-at011440 : Complete 4 → ⟪ (Bx1-4230 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2430 ∷ []) ⟫ʷ
lem-sym12-at011440 c4 = run b0
  where
  b0 : Chain (Bx1-4230 ∷ []) (Bx1-2430 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4231 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4230⟩ c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 0 2 (Bx1-2430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2431⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @01122440: 5 steps
lem-sym12-at01122440 : Complete 4 → ⟪ (Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4230 ∷ []) ⟫ʷ
lem-sym12-at01122440 c4 = run b0
  where
  b0 : Chain (Bx1-2430 ∷ []) (Bx1-4230 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2430⟩ c4) ▸
       at 1 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 0 2 (Bx1-4230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4231⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(1;2430) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·2430⟩-at2332 : Complete 4 → ⟪ (Sb0-1-3-2 ∷ Bx1-3420 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3420 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·2430⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-3-2 ∷ Bx1-3420 ∷ []) (Bx1-3420 ∷ Sb0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx1-2430 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·3420⟩ c4) ▸
       at 1 2 (Bx1-2430 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·2430⟩ c4) ▸
       at 0 2 (Bx1-3420 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·2430⟩ c4) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(1;2430) @243243: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·2430⟩-at243243 : Complete 4 → ⟪ (Sb0-1-4-2 ∷ Bx1-4320 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4320 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·2430⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-2 ∷ Bx1-4320 ∷ []) (Bx1-4320 ∷ Sb0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx1-3420 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·4320⟩ c4) ▸
       at 1 2 (Bx1-3420 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·2430⟩-at2332 c4) ▸
       at 0 2 (Bx1-4320 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·3420⟩ c4) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(1;2430) @2442: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·2430⟩-at2442 : Complete 4 → ⟪ (Sb0-1-4-3 ∷ Bx1-4230 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4230 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·2430⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-3 ∷ Bx1-4230 ∷ []) (Bx1-4230 ∷ Sb0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx1-4320 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·4230⟩ c4) ▸
       at 1 2 (Bx1-4320 ∷ Sb0-1-4-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·2430⟩-at243243 c4) ▸
       at 0 2 (Bx1-4230 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·4320⟩ c4) ▸
       at 1 2 (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(1;4230): 23 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨1·4230⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Bx1-4230 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4230 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨1·4230⟩ c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sb0-1-23-4 ∷ Bx1-4230 ∷ []) (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Bx1-4230 ∷ CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 2 (Bx1-4230 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·2430⟩-at2442 c4) ▸
       at 5 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx1-2430 ∷ []) (lem-sym12-at011440 c4) ▸
       at 4 1 (Bx1-2340 ∷ []) (lem-sym23-at01122440 c4) ▸
       at 3 3 (Bx1-2340 ∷ CCZ023 ∷ []) (lem-T312-beta-at0112233440 c4) ▸
       at 3 1 (Bx1-2430 ∷ []) (lem-sym23-at0112233440 c4) ▸
       at 3 1 (Bx1-4230 ∷ []) (lem-sym12-at01122440 c4) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Bx1-4230 ∷ CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx1-4230 ∷ Bx0-1234 ∷ CCZ023 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b1 = at 2 2 (Bx1-4230 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·2430⟩-at2442 c4) ▸
       at 3 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx1-2430 ∷ []) (lem-sym12-at011440 c4) ▸
       at 2 1 (Bx1-2340 ∷ []) (lem-sym23-at01122440 c4) ▸
       at 1 3 (Bx1-2340 ∷ CCZ023 ∷ []) (lem-T312-beta-at0112233440 c4) ▸
       at 1 1 (Bx1-2430 ∷ []) (lem-sym23-at0112233440 c4) ▸
       at 1 1 (Bx1-4230 ∷ []) (lem-sym12-at01122440 c4) ▸
       at 0 2 (Bx1-4230 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·4230⟩ c4) ▸ done

  b2 : Chain (Bx1-4230 ∷ Bx0-1234 ∷ CCZ023 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx1-4230 ∷ Sb0-1-23-4 ∷ [])
  b2 = at 5 3 (Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-TOFF301-SBOXd⟨2·4·3·1⟩-at0213203441 c4) ▸
       at 2 2 (Toff423 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Sb0-1-4-3 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-SBOX⟨0·1·4·3⟩ c4) ▸
       at 4 2 (Toff423 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Sb⁻0-1-4-3 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 6 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CSd10 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd10-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd10-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 1 2 (CS01⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd10 c4) ▸
       at 0 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ021: 40 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ021 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ021 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ012 ∷ []) (CS01 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ CX21 ∷ Toff423 ∷ CS01⁻ ∷ CX21 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ [])
  b0 = at 1 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS01 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 4 (CX21 ∷ CS01⁻ ∷ CX21 ∷ CS14⁻ ∷ []) (pw3 c4 (CS14⁻ ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ []) (CX21 ∷ CS01⁻ ∷ CX21 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 4 2 (CX21 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX21 ∷ []) (CX21 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS01 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ CX21 ∷ Toff423 ∷ CS01⁻ ∷ CX21 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ []) (CS01 ∷ Bx0-1324 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ [])
  b1 = at 5 2 (CS01⁻ ∷ Toff423 ∷ []) (sym (c₂ (CS • CS • CS) (Toffᵗ))) ▸
       at 6 2 (CX21 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX21 ∷ []) (CX21 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸
       at 3 4 (CX21 ∷ CS01⁻ ∷ CX21 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ []) (CX21 ∷ CS01⁻ ∷ CX21 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 2 2 (CX21 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX21 ∷ []) (CX21 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS01⁻ ∷ Toff423 ∷ []) (sym (c₂ (CS • CS • CS) (Toffᵗ))) ▸
       at 4 2 (CX21 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX21 ∷ []) (CX21 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CS01 ∷ Bx0-1324 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ []) (CS01 ∷ CX21 ∷ CCZ234 ∷ CS01⁻ ∷ Bx0-1324 ∷ CX21 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ [])
  b2 = at 1 0 (CX21 ∷ CX21 ∷ []) (lw4 c4 [] (CX21 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸
       at 3 1 (Bx0-3214 ∷ []) (lem-sym23-at132132 c4) ▸
       at 2 3 (Bx0-3214 ∷ CCZ234 ∷ []) (lem-CX23-beta-at1331 c4) ▸
       at 2 1 (Bx0-3124 ∷ []) (lem-sym23-at1331 c4) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 2 2 (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at2332 c4) ▸
       at 3 2 (CS01⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd10-at2332 c4) ▸ done

  b3 : Chain (CS01 ∷ CX21 ∷ CCZ234 ∷ CS01⁻ ∷ Bx0-1324 ∷ CX21 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ []) (CS01 ∷ CCZ234 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CCZ234 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ [])
  b3 = at 4 0 (CX21 ∷ CX21 ∷ []) (lw4 c4 [] (CX21 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸
       at 6 1 (Bx0-3214 ∷ []) (lem-sym23-at132132 c4) ▸
       at 5 3 (Bx0-3214 ∷ CCZ234 ∷ []) (lem-CX23-beta-at1331 c4) ▸
       at 5 1 (Bx0-3124 ∷ []) (lem-sym23-at1331 c4) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 5 2 (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at2332 c4) ▸
       at 1 2 (CCZ234 ∷ CX21 ∷ []) (lw0 c4 (CX21 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX21 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (CS01 ∷ CCZ234 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CCZ234 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ []) (CCZ012 ∷ Sb0-1-23-4 ∷ [])
  b4 = at 4 2 (CCZ234 ∷ CX21 ∷ []) (lw0 c4 (CX21 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CX21 ∷ []) (lw0 c4 (CX21 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS02 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ012 ∷ []) (lw4 c4 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ021 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ021-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ021-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (CCZ012 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ021 c4) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | TOFF031: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF031 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF031 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Toff013 ∷ []) (Toff013 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (K0 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 c4) ▸
       at 1 2 (CCZ013 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ021-at2332 c4) ▸
       at 2 2 (K0⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332 c4) ▸
       at 3 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ031: 44 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ031 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ031 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ013 ∷ []) (CS01 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ CX31 ∷ Toff423 ∷ CS01⁻ ∷ CX31 ∷ Sb⁻0-1-4-2 ∷ CS03 ∷ [])
  b0 = at 1 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS01 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 4 (CX31 ∷ CS01⁻ ∷ CX31 ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ []) (CX31 ∷ CS01⁻ ∷ CX31 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 4 2 (CX31 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX31 ∷ []) (CX31 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS01 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ CX31 ∷ Toff423 ∷ CS01⁻ ∷ CX31 ∷ Sb⁻0-1-4-2 ∷ CS03 ∷ []) (CS01 ∷ Bx0-1324 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS03 ∷ [])
  b1 = at 5 2 (CS01⁻ ∷ Toff423 ∷ []) (sym (c₂ (CS • CS • CS) (Toffᵗ))) ▸
       at 6 2 (CX31 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX31 ∷ []) (CX31 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸
       at 3 4 (CX31 ∷ CS01⁻ ∷ CX31 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ []) (CX31 ∷ CS01⁻ ∷ CX31 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 2 2 (CX31 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX31 ∷ []) (CX31 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS01⁻ ∷ Toff423 ∷ []) (sym (c₂ (CS • CS • CS) (Toffᵗ))) ▸
       at 4 2 (CX31 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX31 ∷ []) (CX31 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CS01 ∷ Bx0-1324 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS03 ∷ []) (CS01 ∷ CX31 ∷ Bx0-1324 ∷ CCZ234 ∷ CS01⁻ ∷ CX31 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS03 ∷ [])
  b2 = at 1 0 (CX31 ∷ CX31 ∷ []) (lw4 c4 [] (CX31 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸
       at 3 1 (Bx0-3214 ∷ []) (lem-sym23-at132132 c4) ▸
       at 3 1 (Bx0-2314 ∷ []) (lem-sym12-at1331 c4) ▸
       at 2 3 (Bx0-2314 ∷ CCZ234 ∷ []) (lem-CX23-beta-at122331 c4) ▸
       at 2 1 (Bx0-3214 ∷ []) (lem-sym12-at122331 c4) ▸
       at 2 1 (Bx0-3124 ∷ []) (lem-sym23-at1331 c4) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸ done

  b3 : Chain (CS01 ∷ CX31 ∷ Bx0-1324 ∷ CCZ234 ∷ CS01⁻ ∷ CX31 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS03 ∷ []) (CS01 ∷ CX31 ∷ CCZ234 ∷ CS01⁻ ∷ CX31 ∷ Bx0-3214 ∷ CCZ234 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS03 ∷ [])
  b3 = at 2 2 (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at2332 c4) ▸
       at 3 2 (CS01⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd10-at2332 c4) ▸
       at 4 0 (CX31 ∷ CX31 ∷ []) (lw4 c4 [] (CX31 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸
       at 6 1 (Bx0-3214 ∷ []) (lem-sym23-at132132 c4) ▸
       at 6 1 (Bx0-2314 ∷ []) (lem-sym12-at1331 c4) ▸
       at 5 3 (Bx0-2314 ∷ CCZ234 ∷ []) (lem-CX23-beta-at122331 c4) ▸
       at 5 1 (Bx0-3214 ∷ []) (lem-sym12-at122331 c4) ▸ done

  b4 : Chain (CS01 ∷ CX31 ∷ CCZ234 ∷ CS01⁻ ∷ CX31 ∷ Bx0-3214 ∷ CCZ234 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS03 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS03 ∷ [])
  b4 = at 5 1 (Bx0-3124 ∷ []) (lem-sym23-at1331 c4) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 5 2 (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at2332 c4) ▸
       at 1 2 (CCZ234 ∷ CX31 ∷ []) (lw0 c4 (CX31 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ CX31 ∷ []) (lw0 c4 (CX31 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CX31 ∷ []) (lw0 c4 (CX31 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸ done

  b5 : Chain (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS03 ∷ []) (CCZ013 ∷ Sb0-1-23-4 ∷ [])
  b5 = at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS03 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ013 ∷ []) (lw4 c4 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ031 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ031-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ031-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (CCZ013 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ031 c4) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | TOFF021: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF021 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF021 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Toff012 ∷ []) (Toff012 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (K0 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 c4) ▸
       at 1 2 (CCZ012 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ031-at2332 c4) ▸
       at 2 2 (K0⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332 c4) ▸
       at 3 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 3 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;2431): 14 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx0-2431 ∷ []) (Toff024 ∷ CCZ013 ∷ CS12⁻ ∷ Toff024 ∷ CCZ013 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Toff024 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 2 (CCZ013 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 2 1 (CS12⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ CS12⁻ ∷ Toff024 ∷ CCZ013 ∷ []) (Bx0-2431 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 2 2 (Toff024 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 3 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 2 (CCZ013 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;2431): 14 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩ : Complete 4 → ⟪ (Sb0-1-2-3 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-2-3 ∷ Bx0-2431 ∷ []) (Toff024 ∷ CCZ013 ∷ CS12 ∷ Toff024 ∷ CCZ013 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 0 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (Toff024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ Toff024 ∷ []) (Toff024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 1 1 (CS12 ∷ []) (refl) ▸
       at 1 2 (CCZ013 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 2 1 (CS12 ∷ []) (refl) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ CS12 ∷ Toff024 ∷ CCZ013 ∷ []) (Bx0-2431 ∷ Sb0-1-2-3 ∷ [])
  b1 = at 2 2 (Toff024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ Toff024 ∷ []) (Toff024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 3 2 (CCZ013 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸ done


-- auto BOX(0;1234) | TOFF042: 9 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF042 : Complete 4 → ⟪ (Bx0-1234 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ Toff024 ∷ []) (Toff024 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (Toff024 ∷ []) (pw1 c4 (Toff024 ∷ []) (Toff024 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 0 2 (Toff024 ∷ Bx0-2413 ∷ []) (sym (lem-T-beta-at12243143 c4)) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done

  b1 : Chain (Toff024 ∷ Bx0-1234 ∷ []) (Toff024 ∷ Bx0-1234 ∷ [])
  b1 = at 0 1 (Toff024 ∷ []) (pw1 c4 (Toff024 ∷ []) (Toff024 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ031: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ031 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ031 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ013 ∷ []) (CCZ013 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CCZ013 ∷ Bx0-1324 ∷ []) (sym (lem-Cz-beta-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(0;4231): 6 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·4231⟩ : Complete 4 → ⟪ (Bx0-1234 ∷ Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·4231⟩ c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Bx0-4231 ∷ []) (Bx0-4231 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at1441 c4) ▸
       at 0 2 (Toff024 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF042 c4) ▸
       at 1 2 (CCZ013 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ031 c4) ▸
       at 2 2 (Toff024 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF042 c4) ▸
       at 3 2 (CCZ013 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ031 c4) ▸
       at 0 4 (Bx0-4231 ∷ []) (sym (lem-beta-T-at1441 c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;2431) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩-at2332 : Complete 4 → ⟪ (Sb⁻0-1-3-2 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-3-2 ∷ Bx0-3421 ∷ []) (Bx0-3421 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx0-2431 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3421⟩ c4) ▸
       at 1 2 (Bx0-2431 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩ c4) ▸
       at 0 2 (Bx0-3421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2431⟩ c4) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;2431) @243243: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩-at243243 : Complete 4 → ⟪ (Sb⁻0-1-4-2 ∷ Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-2 ∷ Bx0-4321 ∷ []) (Bx0-4321 ∷ Sb⁻0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx0-3421 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4321⟩ c4) ▸
       at 1 2 (Bx0-3421 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩-at2332 c4) ▸
       at 0 2 (Bx0-4321 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3421⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;2431) @2442: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩-at2442 : Complete 4 → ⟪ (Sb⁻0-1-4-3 ∷ Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-3 ∷ Bx0-4231 ∷ []) (Bx0-4231 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx0-4321 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4231⟩ c4) ▸
       at 1 2 (Bx0-4321 ∷ Sb⁻0-1-4-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩-at243243 c4) ▸
       at 0 2 (Bx0-4231 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4321⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;2431) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩-at2332 : Complete 4 → ⟪ (Sb0-1-3-2 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-3-2 ∷ Bx0-3421 ∷ []) (Bx0-3421 ∷ Sb0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx0-2431 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3421⟩ c4) ▸
       at 1 2 (Bx0-2431 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩ c4) ▸
       at 0 2 (Bx0-3421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2431⟩ c4) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;2431) @243243: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩-at243243 : Complete 4 → ⟪ (Sb0-1-4-2 ∷ Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-2 ∷ Bx0-4321 ∷ []) (Bx0-4321 ∷ Sb0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx0-3421 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4321⟩ c4) ▸
       at 1 2 (Bx0-3421 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩-at2332 c4) ▸
       at 0 2 (Bx0-4321 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3421⟩ c4) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;2431) @2442: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩-at2442 : Complete 4 → ⟪ (Sb0-1-4-3 ∷ Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-3 ∷ Bx0-4231 ∷ []) (Bx0-4231 ∷ Sb0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx0-4321 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4231⟩ c4) ▸
       at 1 2 (Bx0-4321 ∷ Sb0-1-4-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩-at243243 c4) ▸
       at 0 2 (Bx0-4231 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4321⟩ c4) ▸
       at 1 2 (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;4231): 26 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4231⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4231⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb0-1-23-4 ∷ Bx0-4231 ∷ []) (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Bx0-4231 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 2 (Bx0-4231 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩-at2442 c4) ▸
       at 5 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 4 1 (Bx0-2341 ∷ []) (lem-sym23-at122441 c4) ▸
       at 3 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-T312-beta-at12233441 c4) ▸
       at 3 1 (Bx0-2431 ∷ []) (lem-sym23-at12233441 c4) ▸
       at 3 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Bx0-4231 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx0-4231 ∷ Bx0-1234 ∷ CCZ123 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b1 = at 2 2 (Bx0-4231 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2431⟩-at2442 c4) ▸
       at 3 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 2 1 (Bx0-2341 ∷ []) (lem-sym23-at122441 c4) ▸
       at 1 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-T312-beta-at12233441 c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-sym23-at12233441 c4) ▸
       at 1 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 0 2 (Bx0-4231 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·4231⟩ c4) ▸ done

  b2 : Chain (Bx0-4231 ∷ Bx0-1234 ∷ CCZ123 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx0-4231 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ123 ∷ CCZ123 ∷ [])
  b2 = at 7 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 3 (Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ Toff423 ∷ CS14⁻ ∷ []) (Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14 ∷ []) (refl) ▸
       at 6 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 5 (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸ done

  b3 : Chain (Bx0-4231 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ123 ∷ CCZ123 ∷ []) (Bx0-4231 ∷ Sb0-1-23-4 ∷ [])
  b3 = at 6 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- sym23 @0312243140: 5 steps
lem-sym23-at0312243140 : Complete 4 → ⟪ (Bx3-2410 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ []) ⟫ʷ
lem-sym23-at0312243140 c4 = run b0
  where
  b0 : Chain (Bx3-2410 ∷ []) (Bx3-2140 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-2401 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2410⟩ c4) ▸
       at 1 1 (Bx3-2041 ∷ []) (lem-sym23-at0312243041 c4) ▸
       at 0 2 (Bx3-2140 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2041⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- c124-beta @03203442: 7 steps
lem-c124-beta-at03203442 : Complete 4 → ⟪ (CCZ012 ∷ Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ CCZ012 ∷ []) ⟫ʷ
lem-c124-beta-at03203442 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-1042 ∷ []) (Bx3-1042 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-0142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1042⟩ c4) ▸
       at 1 2 (Bx3-0142 ∷ CCZ012 ∷ []) (lem-c124-beta-at0310213442 c4) ▸
       at 0 2 (Bx3-1042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0142⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- c124-beta @0312203441: 7 steps
lem-c124-beta-at0312203441 : Complete 4 → ⟪ (CCZ012 ∷ Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ CCZ012 ∷ []) ⟫ʷ
lem-c124-beta-at0312203441 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-2041 ∷ []) (Bx3-2041 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-1042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2041⟩ c4) ▸
       at 1 2 (Bx3-1042 ∷ CCZ012 ∷ []) (lem-c124-beta-at03203442 c4) ▸
       at 0 2 (Bx3-2041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1042⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- c124-beta @0312213440: 7 steps
lem-c124-beta-at0312213440 : Complete 4 → ⟪ (CCZ012 ∷ Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ CCZ012 ∷ []) ⟫ʷ
lem-c124-beta-at0312213440 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-2140 ∷ []) (Bx3-2140 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-2041 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2140⟩ c4) ▸
       at 1 2 (Bx3-2041 ∷ CCZ012 ∷ []) (lem-c124-beta-at0312203441 c4) ▸
       at 0 2 (Bx3-2140 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2041⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0312213440: 5 steps
lem-sym23-at0312213440 : Complete 4 → ⟪ (Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ []) ⟫ʷ
lem-sym23-at0312213440 c4 = run b0
  where
  b0 : Chain (Bx3-2140 ∷ []) (Bx3-2410 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-2041 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2140⟩ c4) ▸
       at 1 1 (Bx3-2401 ∷ []) (lem-sym23-at0312203441 c4) ▸
       at 0 2 (Bx3-2410 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2401⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;2410): 5 steps
lem-auto-CCZ012-∣-BOX⟨3·2410⟩ : Complete 4 → ⟪ (CCZ012 ∷ Bx3-2410 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·2410⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-2410 ∷ []) (Bx3-2410 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx3-2140 ∷ []) (lem-sym23-at0312243140 c4) ▸
       at 0 2 (Bx3-2140 ∷ CCZ012 ∷ []) (lem-c124-beta-at0312213440 c4) ▸
       at 0 1 (Bx3-2410 ∷ []) (lem-sym23-at0312213440 c4) ▸
       at 1 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;2;41;0): 9 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·41·0⟩ : Complete 4 → ⟪ (CCZ012 ∷ Sb3-2-41-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-2-41-0 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·41·0⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Sb3-2-41-0 ∷ []) (Bx3-2410 ∷ Toff014 ∷ Sb3-2-0-1 ∷ Toff014 ∷ Sb⁻3-2-0-1 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx3-2410 ∷ Toff014 ∷ Sb3-2-0-1 ∷ Toff014 ∷ Sb⁻3-2-0-1 ∷ []) (refl) ▸
       at 0 2 (Bx3-2410 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·2410⟩ c4) ▸
       at 3 1 (CS02 ∷ []) (refl) ▸
       at 1 4 (Toff014 ∷ CS02 ∷ Toff014 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ Toff014 ∷ CS02 ∷ Toff014 ∷ []) (Toff014 ∷ CS02 ∷ Toff014 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb3-2-0-1 ∷ []) (refl) ▸
       at 5 1 (CS02⁻ ∷ []) (refl) ▸
       at 4 2 (CS02⁻ ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻3-2-0-1 ∷ []) (refl) ▸ done

  b1 : Chain (Bx3-2410 ∷ Toff014 ∷ Sb3-2-0-1 ∷ Toff014 ∷ Sb⁻3-2-0-1 ∷ CCZ012 ∷ []) (Sb3-2-41-0 ∷ CCZ012 ∷ [])
  b1 = at 0 5 (Sb3-2-41-0 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;4;1;3): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·1·3⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Sb0-4-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-1-3 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb0-4-1-3 ∷ []) (Sb0-4-1-3 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb0-4-1-3 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;4;1;3): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·1·3⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Sb⁻0-4-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-1-3 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb⁻0-4-1-3 ∷ []) (Sb⁻0-4-1-3 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS14⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb⁻0-4-1-3 ∷ []) (refl) ▸ done


-- F0 @02132031: 5 steps
lem-F0-at02132031 : Complete 4 → ⟪ (Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ []) ⟫ʷ
lem-F0-at02132031 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 1 1 (Sb2-1-43-0 ∷ []) (lem-F0-at01132032 c4) ▸
       at 0 2 (Sb1-2-43-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·43·0⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- X1-beta @011440: 8 steps
lem-X1-beta-at011440 : Complete 4 → ⟪ (X4 ∷ Bx1-4230 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Bx1-4230 ∷ []) ⟫ʷ
lem-X1-beta-at011440 c4 = run b0
  where
  b0 : Chain (X4 ∷ Bx1-4230 ∷ X4 ∷ []) (CCZ023 ∷ Bx1-4230 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑)) ▸
       at 2 2 (Bx0-4231 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4230⟩ c4) ▸
       at 3 2 (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑)) ▸
       at 1 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-4230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4231⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;4231) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4231⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4231⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Bx0-4321 ∷ []) (Bx0-4321 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Bx0-4231 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4321⟩ c4) ▸
       at 1 2 (Bx0-4231 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4231⟩ c4) ▸
       at 0 2 (Bx0-4321 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4231⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;4231) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4231⟩-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4231⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Bx0-3421 ∷ []) (Bx0-3421 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Bx0-4321 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3421⟩ c4) ▸
       at 1 2 (Bx0-4321 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4231⟩-at2332 c4) ▸
       at 0 2 (Bx0-3421 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4321⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;4231) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4231⟩-at2442 : Complete 4 → ⟪ (Sb0-1-43-2 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4231⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 (Bx0-3421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2431⟩ c4) ▸
       at 1 2 (Bx0-3421 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4231⟩-at243243 c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3421⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;4231) @01102442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4231⟩-at01102442 : Complete 4 → ⟪ (Sb1-0-43-2 ∷ Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2430 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4231⟩-at01102442 c4 = run b0
  where
  b0 : Chain (Sb1-0-43-2 ∷ Bx1-2430 ∷ []) (Bx1-2430 ∷ Sb1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 2 2 (Bx0-2431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2430⟩ c4) ▸
       at 1 2 (Bx0-2431 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4231⟩-at2442 c4) ▸
       at 0 2 (Bx1-2430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2431⟩ c4) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;2;41;0) @1221: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·41·0⟩-at1221 : Complete 4 → ⟪ (CCZ012 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·41·0⟩-at1221 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Sb3-1-42-0 ∷ []) (Sb3-1-42-0 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb3-2-41-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·1·42·0⟩ c4) ▸
       at 1 2 (Sb3-2-41-0 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·2·41·0⟩ c4) ▸
       at 0 2 (Sb3-1-42-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·2·41·0⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;2;41;0) @132132: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·41·0⟩-at132132 : Complete 4 → ⟪ (CCZ013 ∷ Sb2-1-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-43-0 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·41·0⟩-at132132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Sb2-1-43-0 ∷ []) (Sb2-1-43-0 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Sb3-1-42-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·1·43·0⟩ c4) ▸
       at 1 2 (Sb3-1-42-0 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·2·41·0⟩-at1221 c4) ▸
       at 0 2 (Sb2-1-43-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·1·42·0⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;2;41;0) @01132032: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·41·0⟩-at01132032 : Complete 4 → ⟪ (CCZ013 ∷ Sb2-0-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-43-1 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·41·0⟩-at01132032 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Sb2-0-43-1 ∷ []) (Sb2-0-43-1 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb2-1-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·43·1⟩ c4) ▸
       at 1 2 (Sb2-1-43-0 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·2·41·0⟩-at132132 c4) ▸
       at 0 2 (Sb2-0-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·43·0⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


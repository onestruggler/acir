{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D090 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0012 ; wl0016 ; wl0034 ; wl0037 ; wl0038 ; wl0063 ; wl0064 ; wl0065 ; wl0078 ; wl0084 ; wl0086 ; wl0087 ; wl0096 ; wl0103 ; wl0119 ; wl0120 ; wl0132 ; wl0133 ; wl0155 ; wl0216 ; wl0280 ; wl0281 ; wl0282 ; wl0335 ; wl0336 ; wl0367 ; wl0368 ; wl0369 ; wl0370 ; wl0371 ; wl0497 ; wl0498 ; wl0499 ; wl0501 ; wl0502 ; wl0503 ; wl0504 ; wp0175 ; wp0176 ; wp0177)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-Cz-beta ; lem-c124-beta-at0310213442 ; lem-sym12-at0314203142 ; lem-sym12-at132132 ; lem-sym23)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-CX23-beta-at2332 ; lem-SBtgt ; lem-SBtgtd ; lem-X1-beta ; lem-auto-CCZ012-∣-CCZ314-at12243143 ; lem-beta-T-at0110 ; lem-sym12-at2332 ; lem-sym12-at233442 ; lem-sym23-at0310213442 ; lem-sym23-at0310243142 ; lem-sym23-at13213442 ; lem-sym23-at13243142 ; lem-sym23-at2332 ; lem-sym34-at13213442 ; lem-sym34-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-CS12-beta-at021021 ; lem-F5-CS01 ; lem-F5d-CS01 ; lem-SBsym-at0113203442 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-CSd12-beta-at021021 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210213443 ; lem-sym34-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D089 using (lem-CSd12-beta-at13243142 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-at2332 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423 ; lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩ ; lem-sym12-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF301 ; lem-nat-2-TOFF201 ; lem-nat-2-TOFF204 ; lem-nat-2-TOFF304 ; lem-nat-3-BOX⟨0·1324⟩ ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-BOX⟨3·4102⟩ ; lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF104 ; lem-nat-0-TOFF304 ; lem-nat-0-TOFF314 ; lem-nat-1-TOFF104 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-BOX⟨3·4012⟩ ; lem-nat-1-TOFF304)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0142⟩ ; lem-nat-2-BOX⟨3·0412⟩)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-CS01)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨2·0413⟩ ; lem-nat-0-BOX⟨2·1403⟩ ; lem-nat-0-CS04 ; lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-BOX⟨3·0412⟩ ; lem-nat-1-CS04 ; lem-nat-1-CSd02 ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-2-CS02 ; lem-nat-2-CSd02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨0·3142⟩ ; lem-nat-0-BOX⟨1·3042⟩ ; lem-nat-0-CSd14 ; lem-nat-1-BOX⟨1·3042⟩ ; lem-nat-1-BOX⟨2·3041⟩ ; lem-nat-1-CSd01 ; lem-nat-1-CSd04 ; lem-nat-2-BOX⟨1·0234⟩ ; lem-nat-2-CS04 ; lem-nat-2-CSd04 ; lem-nat-3-CSd04)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨0·3124⟩ ; lem-nat-0-BOX⟨2·0134⟩ ; lem-nat-0-BOX⟨2·1034⟩ ; lem-nat-2-CSd03 ; lem-nat-2-SBOXd⟨0·1·23·4⟩ ; lem-nat-2-SBOXd⟨0·1·32·4⟩ ; lem-nat-3-CS03 ; lem-nat-3-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-BOX⟨1·3024⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-0-SBOXd⟨0·1·42·3⟩ ; lem-nat-0-SBOXd⟨1·0·42·3⟩ ; lem-nat-1-BOX⟨3·0142⟩ ; lem-nat-1-BOX⟨3·0241⟩ ; lem-nat-1-SBOXd⟨1·0·42·3⟩ ; lem-nat-1-SBOXd⟨2·0·41·3⟩ ; lem-nat-3-SBOXd⟨0·1·32·4⟩ ; lem-nat-3-SBOXd⟨0·1·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-BOX⟨0·3412⟩ ; lem-nat-0-BOX⟨1·3402⟩ ; lem-nat-0-SBOX⟨2·1·40·3⟩ ; lem-nat-1-BOX⟨1·2403⟩ ; lem-nat-1-BOX⟨1·3402⟩ ; lem-nat-1-BOX⟨2·1403⟩ ; lem-nat-1-BOX⟨2·3401⟩ ; lem-nat-1-SBOX⟨1·2·40·3⟩ ; lem-nat-1-SBOX⟨3·4·12·0⟩ ; lem-nat-2-BOX⟨1·3402⟩ ; lem-nat-2-BOX⟨3·4201⟩ ; lem-nat-2-SBOX⟨1·3·40·2⟩ ; lem-nat-2-SBOX⟨3·4·20·1⟩ ; lem-nat-3-BOX⟨2·3401⟩ ; lem-nat-3-SBOX⟨1·4·30·2⟩ ; lem-nat-3-SBOX⟨2·3·40·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-0-SBOX⟨2·0·41·3⟩ ; lem-nat-0-SBOX⟨2·3·40·1⟩ ; lem-nat-0-SBOX⟨2·3·41·0⟩ ; lem-nat-0-SBOX⟨2·4·01·3⟩ ; lem-nat-0-SBOXd⟨2·0·41·3⟩ ; lem-nat-0-SBOXd⟨2·1·40·3⟩ ; lem-nat-0-SBOXd⟨2·4·01·3⟩ ; lem-nat-0-SBOXd⟨2·4·10·3⟩ ; lem-nat-1-SBOX⟨1·3·40·2⟩ ; lem-nat-1-SBOX⟨2·1·40·3⟩ ; lem-nat-1-SBOX⟨2·3·40·1⟩ ; lem-nat-1-SBOX⟨2·4·10·3⟩ ; lem-nat-1-SBOX⟨3·4·21·0⟩ ; lem-nat-1-SBOXd⟨1·2·40·3⟩ ; lem-nat-1-SBOXd⟨1·4·20·3⟩ ; lem-nat-1-SBOXd⟨2·1·40·3⟩ ; lem-nat-1-SBOXd⟨2·4·10·3⟩ ; lem-nat-2-BOX⟨1·2403⟩ ; lem-nat-2-SBOX⟨1·2·40·3⟩ ; lem-nat-2-SBOX⟨1·4·20·3⟩ ; lem-nat-2-SBOX⟨2·4·31·0⟩ ; lem-nat-2-SBOX⟨3·4·21·0⟩ ; lem-nat-2-SBOXd⟨1·2·40·3⟩ ; lem-nat-2-SBOXd⟨1·3·40·2⟩ ; lem-nat-2-SBOXd⟨1·4·20·3⟩ ; lem-nat-2-SBOXd⟨1·4·30·2⟩ ; lem-nat-3-SBOX⟨2·3·41·0⟩ ; lem-nat-3-SBOX⟨2·4·31·0⟩ ; lem-nat-3-SBOXd⟨1·3·40·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-SBOX⟨3·4·01·2⟩ ; lem-nat-0-SBOX⟨3·4·10·2⟩ ; lem-nat-1-BOX⟨3·0421⟩ ; lem-nat-1-BOX⟨3·4102⟩ ; lem-nat-1-BOX⟨3·4201⟩ ; lem-nat-1-SBOX⟨3·4·10·2⟩ ; lem-nat-1-SBOX⟨3·4·20·1⟩ ; lem-nat-2-BOX⟨1·0324⟩ ; lem-nat-2-BOX⟨2·0431⟩ ; lem-nat-2-BOX⟨2·4301⟩ ; lem-nat-2-BOXd⟨3·0412⟩ ; lem-nat-2-SBOX⟨2·4·30·1⟩ ; lem-nat-3-BOX⟨1·0324⟩ ; lem-nat-3-BOX⟨1·0423⟩ ; lem-nat-3-BOX⟨2·4301⟩ ; lem-nat-3-SBOX⟨2·4·30·1⟩ ; lem-nat-3-SBOXd⟨1·4·30·2⟩)
-- auto CCZ012 | BOX(3;4012): 5 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩ : Ws → ⟪ (CCZ012 ∷ Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-4012 ∷ []) (Bx3-4012 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 1 1 (Bx3-0142 ∷ []) (lem-sym23-at0310243142 c4) ▸
       at 0 2 (Bx3-0142 ∷ CCZ012 ∷ []) (lem-c124-beta-at0310213442 c4) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-sym23-at0310213442 c4) ▸
       at 0 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸ done


-- auto CCZ012 | SBOX(3;4;01;2): 9 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩ : Ws → ⟪ (CCZ012 ∷ Sb3-4-01-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-01-2 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Sb3-4-01-2 ∷ []) (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 0 2 (Bx3-4012 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩ c4) ▸
       at 3 1 (CS24 ∷ []) (refl) ▸
       at 1 4 (Toff201 ∷ CS24 ∷ Toff201 ∷ CCZ012 ∷ []) (wp0175 c4) ▸
       at 2 1 (Sb3-4-2-1 ∷ []) (refl) ▸
       at 5 1 (CS24⁻ ∷ []) (refl) ▸
       at 4 2 (CS24⁻ ∷ CCZ012 ∷ []) (wp0176 c4) ▸
       at 4 1 (Sb⁻3-4-2-1 ∷ []) (refl) ▸ done

  b1 : Chain (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ CCZ012 ∷ []) (Sb3-4-01-2 ∷ CCZ012 ∷ [])
  b1 = at 0 5 (Sb3-4-01-2 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CSd34: 9 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd34 : Ws → ⟪ (Bx0-1234 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd34 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Bx0-1324 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym12-at233442 c4) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4) ▸
       at 0 2 (CS34⁻ ∷ Bx0-3412 ∷ []) (sym (lem-CSd12-beta-at13243142 c4)) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸ done

  b1 : Chain (CS34⁻ ∷ Bx0-1324 ∷ []) (CS34⁻ ∷ Bx0-1234 ∷ [])
  b1 = at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸ done


-- auto BOX(0;1234) | CSd34 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd34-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd34-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 (lit c4))) ▸
       at 1 2 (CS34⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd34 c4) ▸
       at 0 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ432: 26 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ432 : Ws → ⟪ (Sb0-1-23-4 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ432 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ234 ∷ []) (CS24 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ [])
  b0 = at 1 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (wl0336 (lit c4)) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS24 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 4 (CX32 ∷ CS24⁻ ∷ CX32 ∷ CS14⁻ ∷ []) (wl0498 (lit c4)) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 4 4 (CX32 ∷ CS24⁻ ∷ CX32 ∷ Toff423 ∷ []) (sym (wl0497 (lit c4))) ▸ done

  b1 : Chain (CS24 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ []) (CS24 ∷ CX32 ∷ CCZ134 ∷ CS24⁻ ∷ Bx0-1324 ∷ CX32 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ [])
  b1 = at 3 1 (CS14 ∷ []) (refl) ▸
       at 3 4 (CX32 ∷ CS24⁻ ∷ CX32 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 2 4 (CX32 ∷ CS24⁻ ∷ CX32 ∷ Toff423 ∷ []) (sym (wl0497 (lit c4))) ▸
       at 1 0 (CX32 ∷ CX32 ∷ []) (sym (wl0216 (lit c4))) ▸
       at 2 3 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-CX23-beta-at2332 c4) ▸
       at 2 2 (CCZ134 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2332 c4) ▸
       at 3 2 (CS24⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd34-at2332 c4) ▸ done

  b2 : Chain (CS24 ∷ CX32 ∷ CCZ134 ∷ CS24⁻ ∷ Bx0-1324 ∷ CX32 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ []) (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ Sb0-1-32-4 ∷ [])
  b2 = at 4 0 (CX32 ∷ CX32 ∷ []) (sym (wl0216 (lit c4))) ▸
       at 5 3 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-CX23-beta-at2332 c4) ▸
       at 5 2 (CCZ134 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2332 c4) ▸
       at 1 2 (CCZ134 ∷ CX32 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 2 4 (CCZ134 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) (sym (wl0502 (lit c4))) ▸
       at 1 2 [] (wl0503 (lit c4)) ▸
       at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 c4) ▸ done

  b3 : Chain (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ Sb0-1-32-4 ∷ []) (CCZ234 ∷ Sb0-1-23-4 ∷ [])
  b3 = at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ234 ∷ []) (sym (wl0336 (lit c4))) ▸ done


-- auto SBOX(0;1;23;4) | CCZ432 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ432-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ432-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ432 c4) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | TOFF423: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423 : Ws → ⟪ (Sb0-1-23-4 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Toff423 ∷ []) (Toff423 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (sym (wl0335 (lit c4))) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (K4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 c4) ▸
       at 1 2 (CCZ234 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ432-at2332 c4) ▸
       at 2 2 (K4⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 c4) ▸
       at 3 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 3 (Toff423 ∷ []) (wl0335 (lit c4)) ▸ done


-- auto CSd01 | BOX(2;0134): 1 steps
lem-auto-CSd01-∣-BOX⟨2·0134⟩ : Ws → ⟪ (CS01⁻ ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·0134⟩ c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ CS01⁻ ∷ [])
  b0 = at 0 2 (Bx2-0134 ∷ CS01⁻ ∷ []) (lem-CSd12-beta-at021021 c4) ▸ done


-- auto S0 | BOX(1;0234): 6 steps
lem-auto-S0-∣-BOX⟨1·0234⟩ : Ws → ⟪ (S0 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·0234⟩ c4 = run b0
  where
  b0 : Chain (S0 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ S0 ∷ [])
  b0 = at 1 1 (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) (lem-beta-T-at0110 c4) ▸
       at 0 2 (Toff102 ∷ S0 ∷ []) (wl0504 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ S0 ∷ []) (c₁ (S) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 2 2 (Toff102 ∷ S0 ∷ []) (wl0504 (lit c4)) ▸
       at 3 2 (CCZ134 ∷ S0 ∷ []) (c₁ (S) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 0 4 (Bx1-0234 ∷ []) (sym (lem-beta-T-at0110 c4)) ▸ done


-- sym23 @0113243042: 5 steps
lem-sym23-at0113243042 : Ws → ⟪ (Bx1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3042 ∷ []) ⟫ʷ
lem-sym23-at0113243042 c4 = run b0
  where
  b0 : Chain (Bx1-3402 ∷ []) (Bx1-3042 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-3412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3402⟩ (lit c4)) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4) ▸
       at 0 2 (Bx1-3042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3142⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym23 @0213243041: 5 steps
lem-sym23-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ []) ⟫ʷ
lem-sym23-at0213243041 c4 = run b0
  where
  b0 : Chain (Bx2-3401 ∷ []) (Bx2-3041 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-3402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3401⟩ (lit c4)) ▸
       at 1 1 (Bx1-3042 ∷ []) (lem-sym23-at0113243042 c4) ▸
       at 0 2 (Bx2-3041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3042⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym34 @0113203442: 5 steps
lem-sym34-at0113203442 : Ws → ⟪ (Bx1-3042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3024 ∷ []) ⟫ʷ
lem-sym34-at0113203442 c4 = run b0
  where
  b0 : Chain (Bx1-3042 ∷ []) (Bx1-3024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-3142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3042⟩ (lit c4)) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4) ▸
       at 0 2 (Bx1-3024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3124⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym34 @0213203441: 5 steps
lem-sym34-at0213203441 : Ws → ⟪ (Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-sym34-at0213203441 c4 = run b0
  where
  b0 : Chain (Bx2-3041 ∷ []) (Bx2-3014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-3042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3041⟩ (lit c4)) ▸
       at 1 1 (Bx1-3024 ∷ []) (lem-sym34-at0113203442 c4) ▸
       at 0 2 (Bx2-3014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3024⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym23 @0113203442: 5 steps
lem-sym23-at0113203442 : Ws → ⟪ (Bx1-3042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ []) ⟫ʷ
lem-sym23-at0113203442 c4 = run b0
  where
  b0 : Chain (Bx1-3042 ∷ []) (Bx1-3402 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-3142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3042⟩ (lit c4)) ▸
       at 1 1 (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4) ▸
       at 0 2 (Bx1-3402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3412⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym23 @0213203441: 5 steps
lem-sym23-at0213203441 : Ws → ⟪ (Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ []) ⟫ʷ
lem-sym23-at0213203441 c4 = run b0
  where
  b0 : Chain (Bx2-3041 ∷ []) (Bx2-3401 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-3042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3041⟩ (lit c4)) ▸
       at 1 1 (Bx1-3402 ∷ []) (lem-sym23-at0113203442 c4) ▸
       at 0 2 (Bx2-3401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3402⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- CS12-beta @0220: 7 steps
lem-CS12-beta-at0220 : Ws → ⟪ (CS01 ∷ Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ CS01 ∷ []) ⟫ʷ
lem-CS12-beta-at0220 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx2-1034 ∷ []) (Bx2-1034 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 2 2 (Bx2-0134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1034⟩ (lit c4)) ▸
       at 1 2 (Bx2-0134 ∷ CS01 ∷ []) (lem-CS12-beta-at021021 c4) ▸
       at 0 2 (Bx2-1034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0134⟩ (lit c4)) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CCZ012 | BOX(0;3124): 5 steps
lem-auto-CCZ012-∣-BOX⟨0·3124⟩ : Ws → ⟪ (CCZ012 ∷ Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨0·3124⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx0-3124 ∷ []) (Bx0-3124 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 2 (Bx0-1234 ∷ CCZ012 ∷ []) (lem-Cz-beta c4) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸ done


-- auto CCZ012 | SBOX(0;3;4;2): 1 steps
lem-auto-CCZ012-∣-SBOX⟨0·3·4·2⟩ : Ws → ⟪ (CCZ012 ∷ Sb0-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-4-2 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨0·3·4·2⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Sb0-3-4-2 ∷ []) (Sb0-3-4-2 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (Sb0-3-4-2 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸ done


-- auto CCZ012 | SBOXd(0;3;4;2): 1 steps
lem-auto-CCZ012-∣-SBOXd⟨0·3·4·2⟩ : Ws → ⟪ (CCZ012 ∷ Sb⁻0-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-4-2 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOXd⟨0·3·4·2⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Sb⁻0-3-4-2 ∷ []) (Sb⁻0-3-4-2 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (Sb⁻0-3-4-2 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS)) ▸ done


-- auto CCZ012 | SBOX(0;3;12;4): 7 steps
lem-auto-CCZ012-∣-SBOX⟨0·3·12·4⟩ : Ws → ⟪ (CCZ012 ∷ Sb0-3-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-12-4 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨0·3·12·4⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Sb0-3-12-4 ∷ []) (Sb0-3-12-4 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx0-3124 ∷ Toff412 ∷ Sb0-3-4-2 ∷ Toff412 ∷ Sb⁻0-3-4-2 ∷ []) (refl) ▸
       at 0 2 (Bx0-3124 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨0·3124⟩ c4) ▸
       at 1 2 (Toff412 ∷ CCZ012 ∷ []) (wp0177 c4) ▸
       at 2 2 (Sb0-3-4-2 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨0·3·4·2⟩ c4) ▸
       at 3 2 (Toff412 ∷ CCZ012 ∷ []) (wp0177 c4) ▸
       at 4 2 (Sb⁻0-3-4-2 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOXd⟨0·3·4·2⟩ c4) ▸
       at 0 5 (Sb0-3-12-4 ∷ []) (refl) ▸ done


-- F5 CS01 @0110: 8 steps
lem-F5-CS01-at0110 : Ws → ⟪ (X4 ∷ Sb2-1-40-3 ∷ X4 ∷ Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
lem-F5-CS01-at0110 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-1-40-3 ∷ X4 ∷ Sb2-1-40-3 ∷ []) (CS01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑)) ▸
       at 2 2 (Sb2-0-41-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·40·3⟩ (lit c4)) ▸
       at 3 2 (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑)) ▸
       at 4 2 (Sb2-0-41-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·40·3⟩ (lit c4)) ▸
       at 1 4 (CS01 ∷ []) (lem-F5-CS01 c4) ▸
       at 0 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- F5 CS01 @021021: 8 steps
lem-F5-CS01-at021021 : Ws → ⟪ (X4 ∷ Sb1-2-40-3 ∷ X4 ∷ Sb1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
lem-F5-CS01-at021021 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb1-2-40-3 ∷ X4 ∷ Sb1-2-40-3 ∷ []) (CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 2 2 (Sb2-1-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·40·3⟩ (lit c4)) ▸
       at 3 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 4 2 (Sb2-1-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·40·3⟩ (lit c4)) ▸
       at 1 4 (CS01 ∷ []) (lem-F5-CS01-at0110 c4) ▸
       at 0 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- F5 CS01 @03102132: 8 steps
lem-F5-CS01-at03102132 : Ws → ⟪ (X4 ∷ Sb1-3-40-2 ∷ X4 ∷ Sb1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ []) ⟫ʷ
lem-F5-CS01-at03102132 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb1-3-40-2 ∷ X4 ∷ Sb1-3-40-2 ∷ []) (CS03 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 2 2 (Sb1-2-40-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·40·2⟩ (lit c4)) ▸
       at 3 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 4 2 (Sb1-2-40-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·40·2⟩ (lit c4)) ▸
       at 1 4 (CS02 ∷ []) (lem-F5-CS01-at021021 c4) ▸
       at 0 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- F5 CS01 @0410213243: 8 steps
lem-F5-CS01-at0410213243 : Ws → ⟪ (X3 ∷ Sb1-4-30-2 ∷ X3 ∷ Sb1-4-30-2 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
lem-F5-CS01-at0410213243 c4 = run b0
  where
  b0 : Chain (X3 ∷ Sb1-4-30-2 ∷ X3 ∷ Sb1-4-30-2 ∷ []) (CS04 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (X4 ∷ Sw34 ∷ []) (wl0367 (lit c4)) ▸
       at 2 2 (Sb1-3-40-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·4·30·2⟩ (lit c4)) ▸
       at 3 2 (X4 ∷ Sw34 ∷ []) (wl0367 (lit c4)) ▸
       at 4 2 (Sb1-3-40-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·4·30·2⟩ (lit c4)) ▸
       at 1 4 (CS03 ∷ []) (lem-F5-CS01-at03102132 c4) ▸
       at 0 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 (lit c4)) ▸
       at 1 2 [] (wl0007 (lit c4)) ▸ done


-- F5 CS01 @04102142: 8 steps
lem-F5-CS01-at04102142 : Ws → ⟪ (X2 ∷ Sb1-4-20-3 ∷ X2 ∷ Sb1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
lem-F5-CS01-at04102142 c4 = run b0
  where
  b0 : Chain (X2 ∷ Sb1-4-20-3 ∷ X2 ∷ Sb1-4-20-3 ∷ []) (CS04 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (X3 ∷ Sw23 ∷ []) (wl0368 (lit c4)) ▸
       at 2 2 (Sb1-4-30-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·4·20·3⟩ (lit c4)) ▸
       at 3 2 (X3 ∷ Sw23 ∷ []) (wl0368 (lit c4)) ▸
       at 4 2 (Sb1-4-30-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·4·20·3⟩ (lit c4)) ▸
       at 1 4 (CS04 ∷ []) (lem-F5-CS01-at0410213243 c4) ▸
       at 0 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- F5 CS01 @041041: 8 steps
lem-F5-CS01-at041041 : Ws → ⟪ (X1 ∷ Sb2-4-10-3 ∷ X1 ∷ Sb2-4-10-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
lem-F5-CS01-at041041 c4 = run b0
  where
  b0 : Chain (X1 ∷ Sb2-4-10-3 ∷ X1 ∷ Sb2-4-10-3 ∷ []) (CS04 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (X2 ∷ Sw12 ∷ []) (wl0369 (lit c4)) ▸
       at 2 2 (Sb1-4-20-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·4·10·3⟩ (lit c4)) ▸
       at 3 2 (X2 ∷ Sw12 ∷ []) (wl0369 (lit c4)) ▸
       at 4 2 (Sb1-4-20-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·4·10·3⟩ (lit c4)) ▸
       at 1 4 (CS04 ∷ []) (lem-F5-CS01-at04102142 c4) ▸
       at 0 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- F5 CS01 @0440: 8 steps
lem-F5-CS01-at0440 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ []) ⟫ʷ
lem-F5-CS01-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (CS14 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (X1 ∷ Sw01 ∷ []) (wl0370 (lit c4)) ▸
       at 2 2 (Sb2-4-10-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·4·01·3⟩ (lit c4)) ▸
       at 3 2 (X1 ∷ Sw01 ∷ []) (wl0370 (lit c4)) ▸
       at 4 2 (Sb2-4-10-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·4·01·3⟩ (lit c4)) ▸
       at 1 4 (CS04 ∷ []) (lem-F5-CS01-at041041 c4) ▸
       at 0 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- SBtgt @0110: 5 steps
lem-SBtgt-at0110 : Ws → ⟪ (Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-10-3 ∷ []) ⟫ʷ
lem-SBtgt-at0110 c4 = run b0
  where
  b0 : Chain (Sb2-1-40-3 ∷ []) (Sb2-4-10-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·40·3⟩ (lit c4)) ▸
       at 1 1 (Sb2-4-01-3 ∷ []) (lem-SBtgt c4) ▸
       at 0 2 (Sb2-4-10-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·4·01·3⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- SBtgt @021021: 5 steps
lem-SBtgt-at021021 : Ws → ⟪ (Sb1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-20-3 ∷ []) ⟫ʷ
lem-SBtgt-at021021 c4 = run b0
  where
  b0 : Chain (Sb1-2-40-3 ∷ []) (Sb1-4-20-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb2-1-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·40·3⟩ (lit c4)) ▸
       at 1 1 (Sb2-4-10-3 ∷ []) (lem-SBtgt-at0110 c4) ▸
       at 0 2 (Sb1-4-20-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·4·10·3⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- SBtgt @03102132: 5 steps
lem-SBtgt-at03102132 : Ws → ⟪ (Sb1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-30-2 ∷ []) ⟫ʷ
lem-SBtgt-at03102132 c4 = run b0
  where
  b0 : Chain (Sb1-3-40-2 ∷ []) (Sb1-4-30-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb1-2-40-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·40·2⟩ (lit c4)) ▸
       at 1 1 (Sb1-4-20-3 ∷ []) (lem-SBtgt-at021021 c4) ▸
       at 0 2 (Sb1-4-30-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·4·20·3⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- SBtgt @0410213243: 5 steps
lem-SBtgt-at0410213243 : Ws → ⟪ (Sb1-4-30-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-40-2 ∷ []) ⟫ʷ
lem-SBtgt-at0410213243 c4 = run b0
  where
  b0 : Chain (Sb1-4-30-2 ∷ []) (Sb1-3-40-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb1-3-40-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·4·30·2⟩ (lit c4)) ▸
       at 1 1 (Sb1-4-30-2 ∷ []) (lem-SBtgt-at03102132 c4) ▸
       at 0 2 (Sb1-3-40-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·4·30·2⟩ (lit c4)) ▸
       at 1 2 [] (wl0007 (lit c4)) ▸ done


-- SBtgt @04102142: 5 steps
lem-SBtgt-at04102142 : Ws → ⟪ (Sb1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-40-3 ∷ []) ⟫ʷ
lem-SBtgt-at04102142 c4 = run b0
  where
  b0 : Chain (Sb1-4-20-3 ∷ []) (Sb1-2-40-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb1-4-30-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·4·20·3⟩ (lit c4)) ▸
       at 1 1 (Sb1-3-40-2 ∷ []) (lem-SBtgt-at0410213243 c4) ▸
       at 0 2 (Sb1-2-40-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·40·2⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- SBtgt @041041: 5 steps
lem-SBtgt-at041041 : Ws → ⟪ (Sb2-4-10-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-40-3 ∷ []) ⟫ʷ
lem-SBtgt-at041041 c4 = run b0
  where
  b0 : Chain (Sb2-4-10-3 ∷ []) (Sb2-1-40-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb1-4-20-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·4·10·3⟩ (lit c4)) ▸
       at 1 1 (Sb1-2-40-3 ∷ []) (lem-SBtgt-at04102142 c4) ▸
       at 0 2 (Sb2-1-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·40·3⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- SBtgt @0440: 5 steps
lem-SBtgt-at0440 : Ws → ⟪ (Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ
lem-SBtgt-at0440 c4 = run b0
  where
  b0 : Chain (Sb2-4-01-3 ∷ []) (Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb2-4-10-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·4·01·3⟩ (lit c4)) ▸
       at 1 1 (Sb2-1-40-3 ∷ []) (lem-SBtgt-at041041 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·40·3⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto TOFF012 | SBOX(3;4;12;0) @1221: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at1221 : Ws → ⟪ (Toff012 ∷ Sb3-4-21-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-21-0 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at1221 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Sb3-4-21-0 ∷ []) (Sb3-4-21-0 ∷ Toff012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 (lit c4)) ▸
       at 2 2 (Sb3-4-12-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·21·0⟩ (lit c4)) ▸
       at 1 2 (Sb3-4-12-0 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩ c4) ▸
       at 0 2 (Sb3-4-21-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·12·0⟩ (lit c4)) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto TOFF012 | SBOX(3;4;12;0) @132132: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at132132 : Ws → ⟪ (Toff013 ∷ Sb2-4-31-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-31-0 ∷ Toff013 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at132132 c4 = run b0
  where
  b0 : Chain (Toff013 ∷ Sb2-4-31-0 ∷ []) (Sb2-4-31-0 ∷ Toff013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 (lit c4)) ▸
       at 2 2 (Sb3-4-21-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·4·31·0⟩ (lit c4)) ▸
       at 1 2 (Sb3-4-21-0 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at1221 c4) ▸
       at 0 2 (Sb2-4-31-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·4·21·0⟩ (lit c4)) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto TOFF012 | SBOX(3;4;12;0) @14213243: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at14213243 : Ws → ⟪ (Toff014 ∷ Sb2-3-41-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-41-0 ∷ Toff014 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at14213243 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Sb2-3-41-0 ∷ []) (Sb2-3-41-0 ∷ Toff014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 (lit c4)) ▸
       at 2 2 (Sb2-4-31-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·3·41·0⟩ (lit c4)) ▸
       at 1 2 (Sb2-4-31-0 ∷ Toff013 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at132132 c4) ▸
       at 0 2 (Sb2-3-41-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·4·31·0⟩ (lit c4)) ▸
       at 1 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto TOFF012 | SBOX(3;4;12;0) @0114203243: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0114203243 : Ws → ⟪ (Toff104 ∷ Sb2-3-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-40-1 ∷ Toff104 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0114203243 c4 = run b0
  where
  b0 : Chain (Toff104 ∷ Sb2-3-40-1 ∷ []) (Sb2-3-40-1 ∷ Toff104 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 (lit c4)) ▸
       at 2 2 (Sb2-3-41-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·40·1⟩ (lit c4)) ▸
       at 1 2 (Sb2-3-41-0 ∷ Toff014 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at14213243 c4) ▸
       at 0 2 (Sb2-3-40-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·41·0⟩ (lit c4)) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto TOFF012 | SBOX(3;4;12;0) @0214203143: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0214203143 : Ws → ⟪ (Toff204 ∷ Sb1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-40-2 ∷ Toff204 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0214203143 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Sb1-3-40-2 ∷ []) (Sb1-3-40-2 ∷ Toff204 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 (lit c4)) ▸
       at 2 2 (Sb2-3-40-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·3·40·2⟩ (lit c4)) ▸
       at 1 2 (Sb2-3-40-1 ∷ Toff104 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0114203243 c4) ▸
       at 0 2 (Sb1-3-40-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·3·40·1⟩ (lit c4)) ▸
       at 1 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto TOFF012 | SBOX(3;4;12;0) @0314203142: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314203142 : Ws → ⟪ (Toff304 ∷ Sb1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-40-3 ∷ Toff304 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314203142 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ Sb1-2-40-3 ∷ []) (Sb1-2-40-3 ∷ Toff304 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 (lit c4)) ▸
       at 2 2 (Sb1-3-40-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·2·40·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-3-40-2 ∷ Toff204 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0214203143 c4) ▸
       at 0 2 (Sb1-2-40-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·40·2⟩ (lit c4)) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto TOFF012 | SBOX(3;4;12;0) @0314203241: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314203241 : Ws → ⟪ (Toff304 ∷ Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-40-3 ∷ Toff304 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314203241 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ Sb2-1-40-3 ∷ []) (Sb2-1-40-3 ∷ Toff304 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 (lit c4)) ▸
       at 2 2 (Sb1-2-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·40·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-2-40-3 ∷ Toff304 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314203142 c4) ▸
       at 0 2 (Sb2-1-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·40·3⟩ (lit c4)) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto TOFF012 | SBOX(3;4;12;0) @0314213240: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314213240 : Ws → ⟪ (Toff314 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Toff314 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314213240 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Toff314 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 (lit c4)) ▸
       at 2 2 (Sb2-1-40-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (Sb2-1-40-3 ∷ Toff304 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314203241 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·40·3⟩ (lit c4)) ▸
       at 1 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- X1-beta @2332: 8 steps
lem-X1-beta-at2332 : Ws → ⟪ (X1 ∷ Bx0-1324 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-X1-beta-at2332 c4 = run b0
  where
  b0 : Chain (X1 ∷ Bx0-1324 ∷ X1 ∷ []) (CCZ234 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (X1 ∷ Sw23 ∷ []) (sym (c₂ (X ↑) (Swap))) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (c₂ (X ↑) (Swap))) ▸
       at 1 3 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-X1-beta c4) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- X1-beta @243243: 8 steps
lem-X1-beta-at243243 : Ws → ⟪ (X1 ∷ Bx0-1423 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-X1-beta-at243243 c4 = run b0
  where
  b0 : Chain (X1 ∷ Bx0-1423 ∷ X1 ∷ []) (CCZ234 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (X1 ∷ Sw34 ∷ []) (sym (c₂ (X ↑) (Swap ↑))) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 3 2 (X1 ∷ Sw34 ∷ []) (sym (c₂ (X ↑) (Swap ↑))) ▸
       at 1 3 (CCZ234 ∷ Bx0-1324 ∷ []) (lem-X1-beta-at2332 c4) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- X1-beta @0110243243: 8 steps
lem-X1-beta-at0110243243 : Ws → ⟪ (X0 ∷ Bx1-0423 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-X1-beta-at0110243243 c4 = run b0
  where
  b0 : Chain (X0 ∷ Bx1-0423 ∷ X0 ∷ []) (CCZ234 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (X1 ∷ Sw01 ∷ []) (wl0370 (lit c4)) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 3 2 (X1 ∷ Sw01 ∷ []) (wl0370 (lit c4)) ▸
       at 1 3 (CCZ234 ∷ Bx0-1423 ∷ []) (lem-X1-beta-at243243 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- X1-beta @0210243143: 8 steps
lem-X1-beta-at0210243143 : Ws → ⟪ (X0 ∷ Bx2-0413 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-X1-beta-at0210243143 c4 = run b0
  where
  b0 : Chain (X0 ∷ Bx2-0413 ∷ X0 ∷ []) (CCZ134 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (X0 ∷ Sw12 ∷ []) (sym (c₁ (X) (Swap))) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 3 2 (X0 ∷ Sw12 ∷ []) (sym (c₁ (X) (Swap))) ▸
       at 1 3 (CCZ234 ∷ Bx1-0423 ∷ []) (lem-X1-beta-at0110243243 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ234 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234 c4) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ234 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at2332 c4) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ234 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at243243 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ234 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0110243243 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F5d CS01 @0110: 8 steps
lem-F5d-CS01-at0110 : Ws → ⟪ (CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-40-3 ∷ X4 ∷ Sb⁻2-1-40-3 ∷ X4 ∷ []) ⟫ʷ
lem-F5d-CS01-at0110 c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ []) (Sb⁻2-1-40-3 ∷ X4 ∷ Sb⁻2-1-40-3 ∷ X4 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS01⁻ ∷ Sw01 ∷ []) (sym (wl0133 (lit c4))) ▸
       at 1 1 (Sb⁻2-0-41-3 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ []) (lem-F5d-CS01 c4) ▸
       at 0 2 (Sb⁻2-1-40-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑)) ▸
       at 2 2 (Sb⁻2-1-40-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·0·41·3⟩ (lit c4)) ▸
       at 3 2 (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑)) ▸
       at 4 2 [] (wl0002 (lit c4)) ▸ done


-- F5d CS01 @021021: 8 steps
lem-F5d-CS01-at021021 : Ws → ⟪ (CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-40-3 ∷ X4 ∷ Sb⁻1-2-40-3 ∷ X4 ∷ []) ⟫ʷ
lem-F5d-CS01-at021021 c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ []) (Sb⁻1-2-40-3 ∷ X4 ∷ Sb⁻1-2-40-3 ∷ X4 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 (lit c4)) ▸
       at 1 1 (Sb⁻2-1-40-3 ∷ X4 ∷ Sb⁻2-1-40-3 ∷ X4 ∷ []) (lem-F5d-CS01-at0110 c4) ▸
       at 0 2 (Sb⁻1-2-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·1·40·3⟩ (lit c4)) ▸
       at 1 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 2 2 (Sb⁻1-2-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·1·40·3⟩ (lit c4)) ▸
       at 3 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- F5d CS01 @03102132: 8 steps
lem-F5d-CS01-at03102132 : Ws → ⟪ (CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-40-2 ∷ X4 ∷ Sb⁻1-3-40-2 ∷ X4 ∷ []) ⟫ʷ
lem-F5d-CS01-at03102132 c4 = run b0
  where
  b0 : Chain (CS03⁻ ∷ []) (Sb⁻1-3-40-2 ∷ X4 ∷ Sb⁻1-3-40-2 ∷ X4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 (lit c4)) ▸
       at 1 1 (Sb⁻1-2-40-3 ∷ X4 ∷ Sb⁻1-2-40-3 ∷ X4 ∷ []) (lem-F5d-CS01-at021021 c4) ▸
       at 0 2 (Sb⁻1-3-40-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·2·40·3⟩ (lit c4)) ▸
       at 1 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 2 2 (Sb⁻1-3-40-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·2·40·3⟩ (lit c4)) ▸
       at 3 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 4 2 [] (wl0006 (lit c4)) ▸ done


-- F5d CS01 @0410213243: 8 steps
lem-F5d-CS01-at0410213243 : Ws → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-30-2 ∷ X3 ∷ Sb⁻1-4-30-2 ∷ X3 ∷ []) ⟫ʷ
lem-F5d-CS01-at0410213243 c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ []) (Sb⁻1-4-30-2 ∷ X3 ∷ Sb⁻1-4-30-2 ∷ X3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 (lit c4)) ▸
       at 1 1 (Sb⁻1-3-40-2 ∷ X4 ∷ Sb⁻1-3-40-2 ∷ X4 ∷ []) (lem-F5d-CS01-at03102132 c4) ▸
       at 0 2 (Sb⁻1-4-30-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·3·40·2⟩ (lit c4)) ▸
       at 1 2 (X3 ∷ Sw34 ∷ []) (wl0282 (lit c4)) ▸
       at 2 2 (Sb⁻1-4-30-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·3·40·2⟩ (lit c4)) ▸
       at 3 2 (X3 ∷ Sw34 ∷ []) (wl0282 (lit c4)) ▸
       at 4 2 [] (wl0007 (lit c4)) ▸ done


-- F5d CS01 @04102142: 8 steps
lem-F5d-CS01-at04102142 : Ws → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-20-3 ∷ X2 ∷ Sb⁻1-4-20-3 ∷ X2 ∷ []) ⟫ʷ
lem-F5d-CS01-at04102142 c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ []) (Sb⁻1-4-20-3 ∷ X2 ∷ Sb⁻1-4-20-3 ∷ X2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 (lit c4)) ▸
       at 1 1 (Sb⁻1-4-30-2 ∷ X3 ∷ Sb⁻1-4-30-2 ∷ X3 ∷ []) (lem-F5d-CS01-at0410213243 c4) ▸
       at 0 2 (Sb⁻1-4-20-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·4·30·2⟩ (lit c4)) ▸
       at 1 2 (X2 ∷ Sw23 ∷ []) (wl0281 (lit c4)) ▸
       at 2 2 (Sb⁻1-4-20-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·4·30·2⟩ (lit c4)) ▸
       at 3 2 (X2 ∷ Sw23 ∷ []) (wl0281 (lit c4)) ▸
       at 4 2 [] (wl0006 (lit c4)) ▸ done


-- F5d CS01 @041041: 8 steps
lem-F5d-CS01-at041041 : Ws → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-10-3 ∷ X1 ∷ Sb⁻2-4-10-3 ∷ X1 ∷ []) ⟫ʷ
lem-F5d-CS01-at041041 c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ []) (Sb⁻2-4-10-3 ∷ X1 ∷ Sb⁻2-4-10-3 ∷ X1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS04⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd04 (lit c4)) ▸
       at 1 1 (Sb⁻1-4-20-3 ∷ X2 ∷ Sb⁻1-4-20-3 ∷ X2 ∷ []) (lem-F5d-CS01-at04102142 c4) ▸
       at 0 2 (Sb⁻2-4-10-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·4·20·3⟩ (lit c4)) ▸
       at 1 2 (X1 ∷ Sw12 ∷ []) (wl0280 (lit c4)) ▸
       at 2 2 (Sb⁻2-4-10-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·4·20·3⟩ (lit c4)) ▸
       at 3 2 (X1 ∷ Sw12 ∷ []) (wl0280 (lit c4)) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- F5d CS01 @0440: 8 steps
lem-F5d-CS01-at0440 : Ws → ⟪ (CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-01-3 ∷ X0 ∷ Sb⁻2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F5d-CS01-at0440 c4 = run b0
  where
  b0 : Chain (CS14⁻ ∷ []) (Sb⁻2-4-01-3 ∷ X0 ∷ Sb⁻2-4-01-3 ∷ X0 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS04⁻ ∷ Sw01 ∷ []) (lem-nat-0-CSd14 (lit c4)) ▸
       at 1 1 (Sb⁻2-4-10-3 ∷ X1 ∷ Sb⁻2-4-10-3 ∷ X1 ∷ []) (lem-F5d-CS01-at041041 c4) ▸
       at 0 2 (Sb⁻2-4-01-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·4·10·3⟩ (lit c4)) ▸
       at 1 2 (X0 ∷ Sw01 ∷ []) (wl0371 (lit c4)) ▸
       at 2 2 (Sb⁻2-4-01-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·4·10·3⟩ (lit c4)) ▸
       at 3 2 (X0 ∷ Sw01 ∷ []) (wl0371 (lit c4)) ▸
       at 4 2 [] (wl0002 (lit c4)) ▸ done


-- SBtgtd @0110: 5 steps
lem-SBtgtd-at0110 : Ws → ⟪ (Sb⁻2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-10-3 ∷ []) ⟫ʷ
lem-SBtgtd-at0110 c4 = run b0
  where
  b0 : Chain (Sb⁻2-1-40-3 ∷ []) (Sb⁻2-4-10-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·1·40·3⟩ (lit c4)) ▸
       at 1 1 (Sb⁻2-4-01-3 ∷ []) (lem-SBtgtd c4) ▸
       at 0 2 (Sb⁻2-4-10-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·4·01·3⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- SBtgtd @021021: 5 steps
lem-SBtgtd-at021021 : Ws → ⟪ (Sb⁻1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-20-3 ∷ []) ⟫ʷ
lem-SBtgtd-at021021 c4 = run b0
  where
  b0 : Chain (Sb⁻1-2-40-3 ∷ []) (Sb⁻1-4-20-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb⁻2-1-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·2·40·3⟩ (lit c4)) ▸
       at 1 1 (Sb⁻2-4-10-3 ∷ []) (lem-SBtgtd-at0110 c4) ▸
       at 0 2 (Sb⁻1-4-20-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·4·10·3⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- SBtgtd @03102132: 5 steps
lem-SBtgtd-at03102132 : Ws → ⟪ (Sb⁻1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-30-2 ∷ []) ⟫ʷ
lem-SBtgtd-at03102132 c4 = run b0
  where
  b0 : Chain (Sb⁻1-3-40-2 ∷ []) (Sb⁻1-4-30-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻1-2-40-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·3·40·2⟩ (lit c4)) ▸
       at 1 1 (Sb⁻1-4-20-3 ∷ []) (lem-SBtgtd-at021021 c4) ▸
       at 0 2 (Sb⁻1-4-30-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·4·20·3⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- SBtgtd @0410213243: 5 steps
lem-SBtgtd-at0410213243 : Ws → ⟪ (Sb⁻1-4-30-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-40-2 ∷ []) ⟫ʷ
lem-SBtgtd-at0410213243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-4-30-2 ∷ []) (Sb⁻1-3-40-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb⁻1-3-40-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·4·30·2⟩ (lit c4)) ▸
       at 1 1 (Sb⁻1-4-30-2 ∷ []) (lem-SBtgtd-at03102132 c4) ▸
       at 0 2 (Sb⁻1-3-40-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·4·30·2⟩ (lit c4)) ▸
       at 1 2 [] (wl0007 (lit c4)) ▸ done


-- SBtgtd @04102142: 5 steps
lem-SBtgtd-at04102142 : Ws → ⟪ (Sb⁻1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-40-3 ∷ []) ⟫ʷ
lem-SBtgtd-at04102142 c4 = run b0
  where
  b0 : Chain (Sb⁻1-4-20-3 ∷ []) (Sb⁻1-2-40-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻1-4-30-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·4·20·3⟩ (lit c4)) ▸
       at 1 1 (Sb⁻1-3-40-2 ∷ []) (lem-SBtgtd-at0410213243 c4) ▸
       at 0 2 (Sb⁻1-2-40-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·3·40·2⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- SBtgtd @041041: 5 steps
lem-SBtgtd-at041041 : Ws → ⟪ (Sb⁻2-4-10-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-40-3 ∷ []) ⟫ʷ
lem-SBtgtd-at041041 c4 = run b0
  where
  b0 : Chain (Sb⁻2-4-10-3 ∷ []) (Sb⁻2-1-40-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb⁻1-4-20-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·4·10·3⟩ (lit c4)) ▸
       at 1 1 (Sb⁻1-2-40-3 ∷ []) (lem-SBtgtd-at04102142 c4) ▸
       at 0 2 (Sb⁻2-1-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·2·40·3⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- SBtgtd @0440: 5 steps
lem-SBtgtd-at0440 : Ws → ⟪ (Sb⁻2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-SBtgtd-at0440 c4 = run b0
  where
  b0 : Chain (Sb⁻2-4-01-3 ∷ []) (Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb⁻2-4-10-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·4·01·3⟩ (lit c4)) ▸
       at 1 1 (Sb⁻2-1-40-3 ∷ []) (lem-SBtgtd-at041041 c4) ▸
       at 0 2 (Sb⁻2-0-41-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·1·40·3⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | TOFF423 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ Toff423 ∷ []) (Toff423 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Toff423 ∷ Sw23 ∷ []) (wl0087 (lit c4)) ▸
       at 1 2 (Toff423 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423 c4) ▸
       at 0 2 (Toff423 ∷ Sw23 ∷ []) (wl0087 (lit c4)) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | TOFF423 @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at243243 : Ws → ⟪ (Sb⁻0-1-42-3 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-42-3 ∷ Toff324 ∷ []) (Toff324 ∷ Sb⁻0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Toff423 ∷ Sw34 ∷ []) (wl0119 (lit c4)) ▸
       at 1 2 (Toff423 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at2332 c4) ▸
       at 0 2 (Toff324 ∷ Sw34 ∷ []) (wl0120 (lit c4)) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | TOFF423 @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0110243243 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ Toff324 ∷ []) (Toff324 ∷ Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 2 (Toff324 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at243243 c4) ▸
       at 0 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | TOFF423 @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0210243143 : Ws → ⟪ (Sb⁻2-0-41-3 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ Toff314 ∷ []) (Toff314 ∷ Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 1 2 (Toff324 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0110243243 c4) ▸
       at 0 2 (Toff314 ∷ Sw12 ∷ []) (wl0063 (lit c4)) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- BOXd-BOX @0310243142: 5 steps
lem-BOXd-BOX-at0310243142 : Ws → ⟪ (Bx⁻3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-BOXd-BOX-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx⁻3-0412 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx⁻2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·0412⟩ (lit c4)) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 0 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- sym34 @0310243142: 5 steps
lem-sym34-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-sym34-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Bx3-0421 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4)) ▸
       at 1 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸
       at 0 2 (Bx3-0421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0431⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- sym23 @0310243241: 5 steps
lem-sym23-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-sym23-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ []) (Bx3-0241 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ (lit c4)) ▸
       at 1 1 (Bx3-0142 ∷ []) (lem-sym23-at0310243142 c4) ▸
       at 0 2 (Bx3-0241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0142⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- beta-T @0310213442: 8 steps
lem-beta-T-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) ⟫ʷ
lem-beta-T-at0310213442 c4 = run b0
  where
  b0 : Chain (Bx3-0142 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0142⟩ (lit c4)) ▸
       at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 0 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 (lit c4))) ▸
       at 2 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 (lit c4)) ▸
       at 3 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 (lit c4))) ▸
       at 4 2 [] (wl0006 (lit c4)) ▸ done


-- beta-T @03103441: 8 steps
lem-beta-T-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) ⟫ʷ
lem-beta-T-at03103441 c4 = run b0
  where
  b0 : Chain (Bx3-0241 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-0142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0241⟩ (lit c4)) ▸
       at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-beta-T-at0310213442 c4) ▸
       at 0 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 2 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 (lit c4)) ▸
       at 3 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- sym23 @03103441: 5 steps
lem-sym23-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-sym23-at03103441 c4 = run b0
  where
  b0 : Chain (Bx3-0241 ∷ []) (Bx3-0421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-0142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0241⟩ (lit c4)) ▸
       at 1 1 (Bx3-0412 ∷ []) (lem-sym23-at0310213442 c4) ▸
       at 0 2 (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym34 @0310243241: 5 steps
lem-sym34-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-sym34-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ (lit c4)) ▸
       at 1 1 (Bx3-0421 ∷ []) (lem-sym34-at0310243142 c4) ▸
       at 0 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ023 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023 c4) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ023 @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at243243 : Ws → ⟪ (Sb⁻0-1-42-3 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-42-3 ∷ CCZ024 ∷ []) (CCZ024 ∷ Sb⁻0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at2332 c4) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 (lit c4)) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ023 @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at0110243243 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at243243 c4) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4)) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ023 @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at0210243143 : Ws → ⟪ (Sb⁻2-0-41-3 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at0110243243 c4) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;4012) @0110: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0110 : Ws → ⟪ (CCZ012 ∷ Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0110 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-4102 ∷ []) (Bx3-4102 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 (lit c4))) ▸
       at 2 2 (Bx3-4012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4102⟩ (lit c4)) ▸
       at 1 2 (Bx3-4012 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩ c4) ▸
       at 0 2 (Bx3-4102 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4012⟩ (lit c4)) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;4012) @021021: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at021021 : Ws → ⟪ (CCZ012 ∷ Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at021021 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-4201 ∷ []) (Bx3-4201 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 2 2 (Bx3-4102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4201⟩ (lit c4)) ▸
       at 1 2 (Bx3-4102 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0110 c4) ▸
       at 0 2 (Bx3-4201 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4102⟩ (lit c4)) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;4012) @03102132: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at03102132 : Ws → ⟪ (CCZ013 ∷ Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at03102132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Bx2-4301 ∷ []) (Bx2-4301 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 2 2 (Bx3-4201 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4301⟩ (lit c4)) ▸
       at 1 2 (Bx3-4201 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at021021 c4) ▸
       at 0 2 (Bx2-4301 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4201⟩ (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;4012) @0410213243: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410213243 : Ws → ⟪ (CCZ014 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Bx2-3401 ∷ []) (Bx2-3401 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 (lit c4)) ▸
       at 2 2 (Bx2-4301 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·3401⟩ (lit c4)) ▸
       at 1 2 (Bx2-4301 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at03102132 c4) ▸
       at 0 2 (Bx2-3401 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·4301⟩ (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;4012) @04103143: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at04103143 : Ws → ⟪ (CCZ024 ∷ Bx1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at04103143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Bx1-3402 ∷ []) (Bx1-3402 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 2 2 (Bx2-3401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3402⟩ (lit c4)) ▸
       at 1 2 (Bx2-3401 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410213243 c4) ▸
       at 0 2 (Bx1-3402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3401⟩ (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;4012) @0410233142: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410233142 : Ws → ⟪ (CCZ034 ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410233142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Bx1-2403 ∷ []) (Bx1-2403 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 2 2 (Bx1-3402 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·2403⟩ (lit c4)) ▸
       at 1 2 (Bx1-3402 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at04103143 c4) ▸
       at 0 2 (Bx1-2403 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·3402⟩ (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;4012) @0410233241: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410233241 : Ws → ⟪ (CCZ034 ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410233241 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 2 2 (Bx1-2403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1403⟩ (lit c4)) ▸
       at 1 2 (Bx1-2403 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410233142 c4) ▸
       at 0 2 (Bx2-1403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2403⟩ (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;4012) @04233240: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at04233240 : Ws → ⟪ (CCZ134 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ134 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at04233240 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4)) ▸
       at 2 2 (Bx2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (Bx2-1403 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410233241 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1403⟩ (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;4;01;2) @0110: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0110 : Ws → ⟪ (CCZ012 ∷ Sb3-4-10-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-10-2 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0110 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Sb3-4-10-2 ∷ []) (Sb3-4-10-2 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 (lit c4))) ▸
       at 2 2 (Sb3-4-01-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·4·10·2⟩ (lit c4)) ▸
       at 1 2 (Sb3-4-01-2 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩ c4) ▸
       at 0 2 (Sb3-4-10-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·4·01·2⟩ (lit c4)) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;4;01;2) @021021: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at021021 : Ws → ⟪ (CCZ012 ∷ Sb3-4-20-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-20-1 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at021021 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Sb3-4-20-1 ∷ []) (Sb3-4-20-1 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 2 2 (Sb3-4-10-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·20·1⟩ (lit c4)) ▸
       at 1 2 (Sb3-4-10-2 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0110 c4) ▸
       at 0 2 (Sb3-4-20-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·10·2⟩ (lit c4)) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;4;01;2) @03102132: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at03102132 : Ws → ⟪ (CCZ013 ∷ Sb2-4-30-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-30-1 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at03102132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Sb2-4-30-1 ∷ []) (Sb2-4-30-1 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 2 2 (Sb3-4-20-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·4·30·1⟩ (lit c4)) ▸
       at 1 2 (Sb3-4-20-1 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at021021 c4) ▸
       at 0 2 (Sb2-4-30-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·4·20·1⟩ (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;4;01;2) @0410213243: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410213243 : Ws → ⟪ (CCZ014 ∷ Sb2-3-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-40-1 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Sb2-3-40-1 ∷ []) (Sb2-3-40-1 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 (lit c4)) ▸
       at 2 2 (Sb2-4-30-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·3·40·1⟩ (lit c4)) ▸
       at 1 2 (Sb2-4-30-1 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at03102132 c4) ▸
       at 0 2 (Sb2-3-40-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·4·30·1⟩ (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;4;01;2) @04103143: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at04103143 : Ws → ⟪ (CCZ024 ∷ Sb1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-40-2 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at04103143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Sb1-3-40-2 ∷ []) (Sb1-3-40-2 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 2 2 (Sb2-3-40-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·3·40·2⟩ (lit c4)) ▸
       at 1 2 (Sb2-3-40-1 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410213243 c4) ▸
       at 0 2 (Sb1-3-40-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·3·40·1⟩ (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;4;01;2) @0410233142: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410233142 : Ws → ⟪ (CCZ034 ∷ Sb1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-40-3 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410233142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Sb1-2-40-3 ∷ []) (Sb1-2-40-3 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 2 2 (Sb1-3-40-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·2·40·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-3-40-2 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at04103143 c4) ▸
       at 0 2 (Sb1-2-40-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·40·2⟩ (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;4;01;2) @0410233241: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410233241 : Ws → ⟪ (CCZ034 ∷ Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-40-3 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410233241 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Sb2-1-40-3 ∷ []) (Sb2-1-40-3 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 2 2 (Sb1-2-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·40·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-2-40-3 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410233142 c4) ▸
       at 0 2 (Sb2-1-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·40·3⟩ (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;4;01;2) @04233240: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at04233240 : Ws → ⟪ (CCZ134 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CCZ134 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at04233240 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4)) ▸
       at 2 2 (Sb2-1-40-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (Sb2-1-40-3 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410233241 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·40·3⟩ (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | TOFF423 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Toff423 ∷ []) (Toff423 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Toff423 ∷ Sw23 ∷ []) (wl0087 (lit c4)) ▸
       at 1 2 (Toff423 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423 c4) ▸
       at 0 2 (Toff423 ∷ Sw23 ∷ []) (wl0087 (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | TOFF423 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Toff324 ∷ []) (Toff324 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Toff423 ∷ Sw34 ∷ []) (wl0119 (lit c4)) ▸
       at 1 2 (Toff423 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at2332 c4) ▸
       at 0 2 (Toff324 ∷ Sw34 ∷ []) (wl0120 (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | TOFF423 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ Toff324 ∷ []) (Toff324 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 2 (Toff324 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at243243 c4) ▸
       at 0 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | TOFF423 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ Toff314 ∷ []) (Toff314 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4)) ▸
       at 1 2 (Toff324 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0110243243 c4) ▸
       at 0 2 (Toff314 ∷ Sw12 ∷ []) (wl0063 (lit c4)) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CSd01 | BOX(2;0134) @1221: 7 steps
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at1221 : Ws → ⟪ (CS02⁻ ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at1221 c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CS02⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 (lit c4)) ▸
       at 2 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4)) ▸
       at 1 2 (Bx2-0134 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨2·0134⟩ c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4)) ▸
       at 1 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CSd01 | BOX(2;0134) @132132: 7 steps
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at132132 : Ws → ⟪ (CS03⁻ ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at132132 c4 = run b0
  where
  b0 : Chain (CS03⁻ ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ CS03⁻ ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 (lit c4)) ▸
       at 2 2 (Bx1-0234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0324⟩ (lit c4)) ▸
       at 1 2 (Bx1-0234 ∷ CS02⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨2·0134⟩-at1221 c4) ▸
       at 0 2 (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ (lit c4)) ▸
       at 1 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CSd01 | BOX(2;0134) @14213243: 7 steps
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at14213243 : Ws → ⟪ (CS04⁻ ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at14213243 c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CS04⁻ ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 (lit c4)) ▸
       at 2 2 (Bx1-0324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (Bx1-0324 ∷ CS03⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨2·0134⟩-at132132 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0324⟩ (lit c4)) ▸
       at 1 2 (CS04⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd03 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CSd01 | BOX(2;0134) @143143: 7 steps
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at143143 : Ws → ⟪ (CS04⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at143143 c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS04⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS04⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd04 (lit c4)) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ CS04⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨2·0134⟩-at14213243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (CS04⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd04 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto S0 | BOX(1;0234) @2332: 7 steps
lem-auto-S0-∣-BOX⟨1·0234⟩-at2332 : Ws → ⟪ (S0 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·0234⟩-at2332 c4 = run b0
  where
  b0 : Chain (S0 ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ S0 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (S0 ∷ Sw23 ∷ []) (sym (c₁ (S) (Swap ↑))) ▸
       at 2 2 (Bx1-0234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0324⟩ (lit c4)) ▸
       at 1 2 (Bx1-0234 ∷ S0 ∷ []) (lem-auto-S0-∣-BOX⟨1·0234⟩ c4) ▸
       at 0 2 (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ (lit c4)) ▸
       at 1 2 (S0 ∷ Sw23 ∷ []) (sym (c₁ (S) (Swap ↑))) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto S0 | BOX(1;0234) @243243: 7 steps
lem-auto-S0-∣-BOX⟨1·0234⟩-at243243 : Ws → ⟪ (S0 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·0234⟩-at243243 c4 = run b0
  where
  b0 : Chain (S0 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ S0 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (S0 ∷ Sw34 ∷ []) (sym (c₁ (S) (Swap ↑ ↑))) ▸
       at 2 2 (Bx1-0324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (Bx1-0324 ∷ S0 ∷ []) (lem-auto-S0-∣-BOX⟨1·0234⟩-at2332 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0324⟩ (lit c4)) ▸
       at 1 2 (S0 ∷ Sw34 ∷ []) (sym (c₁ (S) (Swap ↑ ↑))) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto S0 | BOX(1;0234) @12243143: 7 steps
lem-auto-S0-∣-BOX⟨1·0234⟩-at12243143 : Ws → ⟪ (S0 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·0234⟩-at12243143 c4 = run b0
  where
  b0 : Chain (S0 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ S0 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (S0 ∷ Sw12 ∷ []) (sym (c₁ (S) (Swap))) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ S0 ∷ []) (lem-auto-S0-∣-BOX⟨1·0234⟩-at243243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (S0 ∷ Sw12 ∷ []) (sym (c₁ (S) (Swap))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | CCZ314 @0112243043: 7 steps
lem-auto-CCZ012-∣-CCZ314-at0112243043 : Ws → ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ314-at0112243043 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at12243143 c4) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ023 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CCZ024 ∷ []) (CCZ024 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at2332 c4) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ023 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at243243 c4) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ023 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at0110243243 c4) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


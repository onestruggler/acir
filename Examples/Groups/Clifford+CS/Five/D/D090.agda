{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D090 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0012 ; wl0016 ; wl0034 ; wl0037 ; wl0038 ; wl0063 ; wl0064 ; wl0065 ; wl0078 ; wl0084 ; wl0086 ; wl0087 ; wl0096 ; wl0103 ; wl0119 ; wl0120 ; wl0132 ; wl0133 ; wl0155 ; wl0216 ; wl0280 ; wl0281 ; wl0282 ; wl0335 ; wl0336 ; wl0367 ; wl0368 ; wl0369 ; wl0370 ; wl0371 ; wl0497 ; wl0498 ; wl0499 ; wl0501 ; wl0502 ; wl0503 ; wl0504 ; wp0175 ; wp0176 ; wp0177)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
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

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx3-4012 ∷ []) (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Bx3-0412 ∷ []) (Bx3-0142 ∷ []) (lem-sym23-at0310243142 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CCZ012 ∷ Bx3-0142 ∷ []) (Bx3-0142 ∷ CCZ012 ∷ []) (lem-c124-beta-at0310213442 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Bx3-0142 ∷ []) (Bx3-0412 ∷ []) (lem-sym23-at0310213442 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Bx3-0412 ∷ []) (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4)

-- auto CCZ012 | BOX(3;4012): 5 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩ : Ws → ⟪ (CCZ012 ∷ Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩ c4 = derive (CCZ012 ∷ Bx3-4012 ∷ []) (Bx3-4012 ∷ CCZ012 ∷ [])
  (rw 1 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 0 (q3 c4) ∷
   rw 0 (q4 c4) ∷
   rw 0 (q5 c4) ∷ []) Eq.refl

private
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ012 ∷ Bx3-4012 ∷ []) (Bx3-4012 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩ c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ012 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ []) (Toff201 ∷ CS24 ∷ Toff201 ∷ CCZ012 ∷ []) (wp0175 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ012 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ012 ∷ []) (wp0176 c4)

-- auto CCZ012 | SBOX(3;4;01;2): 9 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩ : Ws → ⟪ (CCZ012 ∷ Sb3-4-01-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-01-2 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩ c4 = derive (CCZ012 ∷ Sb3-4-01-2 ∷ []) (Sb3-4-01-2 ∷ CCZ012 ∷ [])
  (re 1 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) ∷
   rw 0 (q6 c4) ∷
   re 3 1 (CS24 ∷ []) ∷
   rw 1 (q7 c4) ∷
   re 2 1 (Sb3-4-2-1 ∷ []) ∷
   re 5 1 (CS24⁻ ∷ []) ∷
   rw 4 (q8 c4) ∷
   re 4 1 (Sb⁻3-4-2-1 ∷ []) ∷
   re 0 5 (Sb3-4-01-2 ∷ []) ∷ []) Eq.refl

private
  q9 : Ws → Eqn
  q9 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1324 ∷ []) (lem-sym23 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (Bx0-1324 ∷ []) (Bx0-1342 ∷ []) (lem-sym34-at2332 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Bx0-1342 ∷ []) (Bx0-3142 ∷ []) (lem-sym12-at233442 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Bx0-3142 ∷ []) (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (CS34⁻ ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ CS34⁻ ∷ []) (lem-CSd12-beta-at13243142 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx0-3412 ∷ []) (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (Bx0-3142 ∷ []) (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Bx0-3124 ∷ []) (Bx0-1324 ∷ []) (lem-sym12-at132132 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (Bx0-1324 ∷ []) (Bx0-1234 ∷ []) (lem-sym23-at2332 c4)

-- auto BOX(0;1234) | CSd34: 9 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd34 : Ws → ⟪ (Bx0-1234 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd34 c4 = derive (Bx0-1234 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Bx0-1234 ∷ [])
  (rw 0 (q9 c4) ∷
   rw 0 (q10 c4) ∷
   rw 0 (q11 c4) ∷
   rw 0 (q12 c4) ∷
   rw⁻ 0 (q13 c4) ∷
   rw 1 (q14 c4) ∷
   rw 1 (q15 c4) ∷
   rw 1 (q16 c4) ∷
   rw 1 (q17 c4) ∷ []) Eq.refl

private
  q18 : Ws → Eqn
  q18 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw23 ∷ Bx0-1324 ∷ []) (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl0012 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Bx0-1234 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd34 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl0016 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw23 ∷ Bx0-1234 ∷ []) (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4))

-- auto BOX(0;1234) | CSd34 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd34-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd34-at2332 c4 = derive (Bx0-1324 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q19 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   rw 1 (q21 c4) ∷
   rw⁻ 0 (q22 c4) ∷
   rw 1 (q23 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ234 ∷ []) (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (wl0336 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (Sb0-1-32-4 ∷ CS24 ∷ []) (CS24 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-at2332 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CS14⁻ ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) (CX32 ∷ CS24⁻ ∷ CX32 ∷ CS14⁻ ∷ []) (wl0498 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (CX32 ∷ CS24⁻ ∷ CX32 ∷ Toff423 ∷ []) (Toff423 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) (wl0497 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CS14 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) (CX32 ∷ CS24⁻ ∷ CX32 ∷ CS14 ∷ []) (wl0499 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CX32 ∷ CX32 ∷ []) [] (wl0216 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CX32 ∷ Bx0-1324 ∷ CX32 ∷ []) (Bx0-1324 ∷ CCZ134 ∷ []) (lem-CX23-beta-at2332 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Bx0-1324 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2332 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx0-1324 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd34-at2332 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (CCZ134 ∷ CX32 ∷ []) (CX32 ∷ CCZ134 ∷ []) (wl0501 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ134 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) (CX32 ∷ CS24⁻ ∷ CX32 ∷ CCZ134 ∷ []) (wl0502 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CCZ134 ∷ CCZ134 ∷ []) [] (wl0503 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (Sb0-1-32-4 ∷ CS34 ∷ []) (CS34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 c4)

-- auto SBOX(0;1;23;4) | CCZ432: 26 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ432 : Ws → ⟪ (Sb0-1-23-4 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ432 c4 = derive (Sb0-1-23-4 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb0-1-23-4 ∷ [])
  (rw 1 (q24 c4) ∷
   rw 0 (q25 c4) ∷
   rw 0 (q26 c4) ∷
   re 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) ∷
   re 5 1 (CS14⁻ ∷ []) ∷
   rw 5 (q27 c4) ∷
   re 8 1 (Sb⁻0-1-4-2 ∷ []) ∷
   rw⁻ 4 (q28 c4) ∷
   re 3 1 (CS14 ∷ []) ∷
   rw 3 (q29 c4) ∷
   re 6 1 (Sb0-1-4-2 ∷ []) ∷
   rw⁻ 2 (q28 c4) ∷
   rw⁻ 1 (q30 c4) ∷
   rw 2 (q31 c4) ∷
   rw 2 (q32 c4) ∷
   rw 3 (q33 c4) ∷
   rw⁻ 4 (q30 c4) ∷
   rw 5 (q31 c4) ∷
   rw 5 (q32 c4) ∷
   rw⁻ 1 (q34 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   rw 1 (q36 c4) ∷
   re 4 5 (Sb0-1-32-4 ∷ []) ∷
   rw 4 (q37 c4) ∷
   rw⁻ 5 (q25 c4) ∷
   rw⁻ 0 (q24 c4) ∷ []) Eq.refl

private
  q38 : Ws → Eqn
  q38 c4 = eqn (Sw23 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ234 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ234 ∷ []) (wl0086 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (Sb0-1-23-4 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ432 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (Sw23 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | CCZ432 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ432-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ432-at2332 c4 = derive (Sb0-1-32-4 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q38 c4) ∷
   rw⁻ 2 (q39 c4) ∷
   rw 1 (q40 c4) ∷
   rw⁻ 0 (q39 c4) ∷
   rw 1 (q41 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q42 : Ws → Eqn
  q42 c4 = eqn (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (Toff423 ∷ []) (wl0335 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (Sb0-1-32-4 ∷ K4 ∷ []) (K4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (Sb0-1-32-4 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ432-at2332 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (Sb0-1-32-4 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 c4)

-- auto SBOX(0;1;23;4) | TOFF423: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423 : Ws → ⟪ (Sb0-1-23-4 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423 c4 = derive (Sb0-1-23-4 ∷ Toff423 ∷ []) (Toff423 ∷ Sb0-1-23-4 ∷ [])
  (rw⁻ 1 (q42 c4) ∷
   rw 0 (q25 c4) ∷
   rw 0 (q43 c4) ∷
   rw 1 (q44 c4) ∷
   rw 2 (q45 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   rw 0 (q42 c4) ∷ []) Eq.refl

private
  q46 : Ws → Eqn
  q46 c4 = eqn (CS01⁻ ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ CS01⁻ ∷ []) (lem-CSd12-beta-at021021 c4)

-- auto CSd01 | BOX(2;0134): 1 steps
lem-auto-CSd01-∣-BOX⟨2·0134⟩ : Ws → ⟪ (CS01⁻ ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·0134⟩ c4 = derive (CS01⁻ ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ CS01⁻ ∷ [])
  (rw 0 (q46 c4) ∷ []) Eq.refl

private
  q47 : Ws → Eqn
  q47 c4 = eqn (Bx1-0234 ∷ []) (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) (lem-beta-T-at0110 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (S0 ∷ Toff102 ∷ []) (Toff102 ∷ S0 ∷ []) (wl0504 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (S0 ∷ CCZ134 ∷ []) (CCZ134 ∷ S0 ∷ []) (c₁ (S) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))

-- auto S0 | BOX(1;0234): 6 steps
lem-auto-S0-∣-BOX⟨1·0234⟩ : Ws → ⟪ (S0 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·0234⟩ c4 = derive (S0 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ S0 ∷ [])
  (rw 1 (q47 c4) ∷
   rw 0 (q48 c4) ∷
   rw 1 (q49 c4) ∷
   rw 2 (q48 c4) ∷
   rw 3 (q49 c4) ∷
   rw⁻ 0 (q47 c4) ∷ []) Eq.refl

private
  q50 : Ws → Eqn
  q50 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (Sw01 ∷ Bx1-3402 ∷ []) (Bx0-3412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3402⟩ (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (Sw01 ∷ Bx0-3142 ∷ []) (Bx1-3042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3142⟩ (lit c4))

-- sym23 @0113243042: 5 steps
lem-sym23-at0113243042 : Ws → ⟪ (Bx1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3042 ∷ []) ⟫ʷ
lem-sym23-at0113243042 c4 = derive (Bx1-3402 ∷ []) (Bx1-3042 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q51 c4) ∷
   rw 1 (q14 c4) ∷
   rw 0 (q52 c4) ∷
   rw 1 (q50 c4) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (Sw12 ∷ Bx2-3401 ∷ []) (Bx1-3402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3401⟩ (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (Bx1-3402 ∷ []) (Bx1-3042 ∷ []) (lem-sym23-at0113243042 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (Sw12 ∷ Bx1-3042 ∷ []) (Bx2-3041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3042⟩ (lit c4))

-- sym23 @0213243041: 5 steps
lem-sym23-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ []) ⟫ʷ
lem-sym23-at0213243041 c4 = derive (Bx2-3401 ∷ []) (Bx2-3041 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q54 c4) ∷
   rw 1 (q55 c4) ∷
   rw 0 (q56 c4) ∷
   rw 1 (q53 c4) ∷ []) Eq.refl

private
  q57 : Ws → Eqn
  q57 c4 = eqn (Sw01 ∷ Bx1-3042 ∷ []) (Bx0-3142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3042⟩ (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (Sw01 ∷ Bx0-3124 ∷ []) (Bx1-3024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3124⟩ (lit c4))

-- sym34 @0113203442: 5 steps
lem-sym34-at0113203442 : Ws → ⟪ (Bx1-3042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3024 ∷ []) ⟫ʷ
lem-sym34-at0113203442 c4 = derive (Bx1-3042 ∷ []) (Bx1-3024 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q57 c4) ∷
   rw 1 (q15 c4) ∷
   rw 0 (q58 c4) ∷
   rw 1 (q50 c4) ∷ []) Eq.refl

private
  q59 : Ws → Eqn
  q59 c4 = eqn (Sw12 ∷ Bx2-3041 ∷ []) (Bx1-3042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3041⟩ (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (Bx1-3042 ∷ []) (Bx1-3024 ∷ []) (lem-sym34-at0113203442 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (Sw12 ∷ Bx1-3024 ∷ []) (Bx2-3014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3024⟩ (lit c4))

-- sym34 @0213203441: 5 steps
lem-sym34-at0213203441 : Ws → ⟪ (Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-sym34-at0213203441 c4 = derive (Bx2-3041 ∷ []) (Bx2-3014 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q59 c4) ∷
   rw 1 (q60 c4) ∷
   rw 0 (q61 c4) ∷
   rw 1 (q53 c4) ∷ []) Eq.refl

private
  q62 : Ws → Eqn
  q62 c4 = eqn (Sw01 ∷ Bx0-3412 ∷ []) (Bx1-3402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3412⟩ (lit c4))

-- sym23 @0113203442: 5 steps
lem-sym23-at0113203442 : Ws → ⟪ (Bx1-3042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ []) ⟫ʷ
lem-sym23-at0113203442 c4 = derive (Bx1-3042 ∷ []) (Bx1-3402 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q57 c4) ∷
   rw 1 (q12 c4) ∷
   rw 0 (q62 c4) ∷
   rw 1 (q50 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = eqn (Bx1-3042 ∷ []) (Bx1-3402 ∷ []) (lem-sym23-at0113203442 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (Sw12 ∷ Bx1-3402 ∷ []) (Bx2-3401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3402⟩ (lit c4))

-- sym23 @0213203441: 5 steps
lem-sym23-at0213203441 : Ws → ⟪ (Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ []) ⟫ʷ
lem-sym23-at0213203441 c4 = derive (Bx2-3041 ∷ []) (Bx2-3401 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q59 c4) ∷
   rw 1 (q63 c4) ∷
   rw 0 (q64 c4) ∷
   rw 1 (q53 c4) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = eqn (CS01 ∷ Sw01 ∷ []) (Sw01 ∷ CS01 ∷ []) (wl0132 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (Sw01 ∷ Bx2-1034 ∷ []) (Bx2-0134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1034⟩ (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (CS01 ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ CS01 ∷ []) (lem-CS12-beta-at021021 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (Sw01 ∷ Bx2-0134 ∷ []) (Bx2-1034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0134⟩ (lit c4))

-- CS12-beta @0220: 7 steps
lem-CS12-beta-at0220 : Ws → ⟪ (CS01 ∷ Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ CS01 ∷ []) ⟫ʷ
lem-CS12-beta-at0220 c4 = derive (CS01 ∷ Bx2-1034 ∷ []) (Bx2-1034 ∷ CS01 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw⁻ 1 (q65 c4) ∷
   rw 2 (q66 c4) ∷
   rw 1 (q67 c4) ∷
   rw 0 (q68 c4) ∷
   rw⁻ 1 (q65 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q69 : Ws → Eqn
  q69 c4 = eqn (CCZ012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ012 ∷ []) (lem-Cz-beta c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (Bx0-1324 ∷ []) (Bx0-3124 ∷ []) (lem-sym12-at2332 c4)

-- auto CCZ012 | BOX(0;3124): 5 steps
lem-auto-CCZ012-∣-BOX⟨0·3124⟩ : Ws → ⟪ (CCZ012 ∷ Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨0·3124⟩ c4 = derive (CCZ012 ∷ Bx0-3124 ∷ []) (Bx0-3124 ∷ CCZ012 ∷ [])
  (rw 1 (q16 c4) ∷
   rw 1 (q17 c4) ∷
   rw 0 (q69 c4) ∷
   rw 0 (q9 c4) ∷
   rw 0 (q70 c4) ∷ []) Eq.refl

private
  q71 : Ws → Eqn
  q71 c4 = eqn (CCZ012 ∷ Sb0-3-4-2 ∷ []) (Sb0-3-4-2 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS))

-- auto CCZ012 | SBOX(0;3;4;2): 1 steps
lem-auto-CCZ012-∣-SBOX⟨0·3·4·2⟩ : Ws → ⟪ (CCZ012 ∷ Sb0-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-4-2 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨0·3·4·2⟩ c4 = derive (CCZ012 ∷ Sb0-3-4-2 ∷ []) (Sb0-3-4-2 ∷ CCZ012 ∷ [])
  (rw 0 (q71 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = eqn (CCZ012 ∷ Sb⁻0-3-4-2 ∷ []) (Sb⁻0-3-4-2 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS))

-- auto CCZ012 | SBOXd(0;3;4;2): 1 steps
lem-auto-CCZ012-∣-SBOXd⟨0·3·4·2⟩ : Ws → ⟪ (CCZ012 ∷ Sb⁻0-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-4-2 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOXd⟨0·3·4·2⟩ c4 = derive (CCZ012 ∷ Sb⁻0-3-4-2 ∷ []) (Sb⁻0-3-4-2 ∷ CCZ012 ∷ [])
  (rw 0 (q72 c4) ∷ []) Eq.refl

private
  q73 : Ws → Eqn
  q73 c4 = eqn (CCZ012 ∷ Bx0-3124 ∷ []) (Bx0-3124 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨0·3124⟩ c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (CCZ012 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ012 ∷ []) (wp0177 c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (CCZ012 ∷ Sb0-3-4-2 ∷ []) (Sb0-3-4-2 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨0·3·4·2⟩ c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (CCZ012 ∷ Sb⁻0-3-4-2 ∷ []) (Sb⁻0-3-4-2 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOXd⟨0·3·4·2⟩ c4)

-- auto CCZ012 | SBOX(0;3;12;4): 7 steps
lem-auto-CCZ012-∣-SBOX⟨0·3·12·4⟩ : Ws → ⟪ (CCZ012 ∷ Sb0-3-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-12-4 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨0·3·12·4⟩ c4 = derive (CCZ012 ∷ Sb0-3-12-4 ∷ []) (Sb0-3-12-4 ∷ CCZ012 ∷ [])
  (re 1 1 (Bx0-3124 ∷ Toff412 ∷ Sb0-3-4-2 ∷ Toff412 ∷ Sb⁻0-3-4-2 ∷ []) ∷
   rw 0 (q73 c4) ∷
   rw 1 (q74 c4) ∷
   rw 2 (q75 c4) ∷
   rw 3 (q74 c4) ∷
   rw 4 (q76 c4) ∷
   re 0 5 (Sb0-3-12-4 ∷ []) ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = eqn (Sw01 ∷ X4 ∷ []) (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑))
  q78 : Ws → Eqn
  q78 c4 = eqn (Sw01 ∷ Sb2-1-40-3 ∷ []) (Sb2-0-41-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·40·3⟩ (lit c4))
  q79 : Ws → Eqn
  q79 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CS01 ∷ []) (lem-F5-CS01 c4)

-- F5 CS01 @0110: 8 steps
lem-F5-CS01-at0110 : Ws → ⟪ (X4 ∷ Sb2-1-40-3 ∷ X4 ∷ Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
lem-F5-CS01-at0110 c4 = derive (X4 ∷ Sb2-1-40-3 ∷ X4 ∷ Sb2-1-40-3 ∷ []) (CS01 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q77 c4) ∷
   rw 2 (q78 c4) ∷
   rw 3 (q77 c4) ∷
   rw 4 (q78 c4) ∷
   rw 1 (q79 c4) ∷
   rw⁻ 0 (q65 c4) ∷
   rw 1 (q50 c4) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = eqn (Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑))
  q81 : Ws → Eqn
  q81 c4 = eqn (Sw12 ∷ Sb1-2-40-3 ∷ []) (Sb2-1-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·40·3⟩ (lit c4))
  q82 : Ws → Eqn
  q82 c4 = eqn (X4 ∷ Sb2-1-40-3 ∷ X4 ∷ Sb2-1-40-3 ∷ []) (CS01 ∷ []) (lem-F5-CS01-at0110 c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (Sw12 ∷ CS01 ∷ []) (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4))

-- F5 CS01 @021021: 8 steps
lem-F5-CS01-at021021 : Ws → ⟪ (X4 ∷ Sb1-2-40-3 ∷ X4 ∷ Sb1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
lem-F5-CS01-at021021 c4 = derive (X4 ∷ Sb1-2-40-3 ∷ X4 ∷ Sb1-2-40-3 ∷ []) (CS02 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q80 c4) ∷
   rw 2 (q81 c4) ∷
   rw 3 (q80 c4) ∷
   rw 4 (q81 c4) ∷
   rw 1 (q82 c4) ∷
   rw 0 (q83 c4) ∷
   rw 1 (q53 c4) ∷ []) Eq.refl

private
  q84 : Ws → Eqn
  q84 c4 = eqn (Sw23 ∷ X4 ∷ []) (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X))
  q85 : Ws → Eqn
  q85 c4 = eqn (Sw23 ∷ Sb1-3-40-2 ∷ []) (Sb1-2-40-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·40·2⟩ (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (X4 ∷ Sb1-2-40-3 ∷ X4 ∷ Sb1-2-40-3 ∷ []) (CS02 ∷ []) (lem-F5-CS01-at021021 c4)
  q87 : Ws → Eqn
  q87 c4 = eqn (Sw23 ∷ CS02 ∷ []) (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4))

-- F5 CS01 @03102132: 8 steps
lem-F5-CS01-at03102132 : Ws → ⟪ (X4 ∷ Sb1-3-40-2 ∷ X4 ∷ Sb1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ []) ⟫ʷ
lem-F5-CS01-at03102132 c4 = derive (X4 ∷ Sb1-3-40-2 ∷ X4 ∷ Sb1-3-40-2 ∷ []) (CS03 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q84 c4) ∷
   rw 2 (q85 c4) ∷
   rw 3 (q84 c4) ∷
   rw 4 (q85 c4) ∷
   rw 1 (q86 c4) ∷
   rw 0 (q87 c4) ∷
   rw 1 (q18 c4) ∷ []) Eq.refl

private
  q88 : Ws → Eqn
  q88 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 (lit c4))
  q89 : Ws → Eqn
  q89 c4 = eqn (Sw34 ∷ X3 ∷ []) (X4 ∷ Sw34 ∷ []) (wl0367 (lit c4))
  q90 : Ws → Eqn
  q90 c4 = eqn (Sw34 ∷ Sb1-4-30-2 ∷ []) (Sb1-3-40-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·4·30·2⟩ (lit c4))
  q91 : Ws → Eqn
  q91 c4 = eqn (X4 ∷ Sb1-3-40-2 ∷ X4 ∷ Sb1-3-40-2 ∷ []) (CS03 ∷ []) (lem-F5-CS01-at03102132 c4)
  q92 : Ws → Eqn
  q92 c4 = eqn (Sw34 ∷ CS03 ∷ []) (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 (lit c4))

-- F5 CS01 @0410213243: 8 steps
lem-F5-CS01-at0410213243 : Ws → ⟪ (X3 ∷ Sb1-4-30-2 ∷ X3 ∷ Sb1-4-30-2 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
lem-F5-CS01-at0410213243 c4 = derive (X3 ∷ Sb1-4-30-2 ∷ X3 ∷ Sb1-4-30-2 ∷ []) (CS04 ∷ [])
  (rw⁻ 0 (q88 c4) ∷
   rw 1 (q89 c4) ∷
   rw 2 (q90 c4) ∷
   rw 3 (q89 c4) ∷
   rw 4 (q90 c4) ∷
   rw 1 (q91 c4) ∷
   rw 0 (q92 c4) ∷
   rw 1 (q88 c4) ∷ []) Eq.refl

private
  q93 : Ws → Eqn
  q93 c4 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wl0368 (lit c4))
  q94 : Ws → Eqn
  q94 c4 = eqn (Sw23 ∷ Sb1-4-20-3 ∷ []) (Sb1-4-30-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·4·20·3⟩ (lit c4))
  q95 : Ws → Eqn
  q95 c4 = eqn (X3 ∷ Sb1-4-30-2 ∷ X3 ∷ Sb1-4-30-2 ∷ []) (CS04 ∷ []) (lem-F5-CS01-at0410213243 c4)
  q96 : Ws → Eqn
  q96 c4 = eqn (Sw23 ∷ CS04 ∷ []) (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4))

-- F5 CS01 @04102142: 8 steps
lem-F5-CS01-at04102142 : Ws → ⟪ (X2 ∷ Sb1-4-20-3 ∷ X2 ∷ Sb1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
lem-F5-CS01-at04102142 c4 = derive (X2 ∷ Sb1-4-20-3 ∷ X2 ∷ Sb1-4-20-3 ∷ []) (CS04 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q93 c4) ∷
   rw 2 (q94 c4) ∷
   rw 3 (q93 c4) ∷
   rw 4 (q94 c4) ∷
   rw 1 (q95 c4) ∷
   rw 0 (q96 c4) ∷
   rw 1 (q18 c4) ∷ []) Eq.refl

private
  q97 : Ws → Eqn
  q97 c4 = eqn (Sw12 ∷ X1 ∷ []) (X2 ∷ Sw12 ∷ []) (wl0369 (lit c4))
  q98 : Ws → Eqn
  q98 c4 = eqn (Sw12 ∷ Sb2-4-10-3 ∷ []) (Sb1-4-20-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·4·10·3⟩ (lit c4))
  q99 : Ws → Eqn
  q99 c4 = eqn (X2 ∷ Sb1-4-20-3 ∷ X2 ∷ Sb1-4-20-3 ∷ []) (CS04 ∷ []) (lem-F5-CS01-at04102142 c4)
  q100 : Ws → Eqn
  q100 c4 = eqn (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4))

-- F5 CS01 @041041: 8 steps
lem-F5-CS01-at041041 : Ws → ⟪ (X1 ∷ Sb2-4-10-3 ∷ X1 ∷ Sb2-4-10-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
lem-F5-CS01-at041041 c4 = derive (X1 ∷ Sb2-4-10-3 ∷ X1 ∷ Sb2-4-10-3 ∷ []) (CS04 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q97 c4) ∷
   rw 2 (q98 c4) ∷
   rw 3 (q97 c4) ∷
   rw 4 (q98 c4) ∷
   rw 1 (q99 c4) ∷
   rw 0 (q100 c4) ∷
   rw 1 (q53 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = eqn (Sw01 ∷ X0 ∷ []) (X1 ∷ Sw01 ∷ []) (wl0370 (lit c4))
  q102 : Ws → Eqn
  q102 c4 = eqn (Sw01 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-10-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·4·01·3⟩ (lit c4))
  q103 : Ws → Eqn
  q103 c4 = eqn (X1 ∷ Sb2-4-10-3 ∷ X1 ∷ Sb2-4-10-3 ∷ []) (CS04 ∷ []) (lem-F5-CS01-at041041 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (Sw01 ∷ CS04 ∷ []) (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4))

-- F5 CS01 @0440: 8 steps
lem-F5-CS01-at0440 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ []) ⟫ʷ
lem-F5-CS01-at0440 c4 = derive (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (CS14 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q101 c4) ∷
   rw 2 (q102 c4) ∷
   rw 3 (q101 c4) ∷
   rw 4 (q102 c4) ∷
   rw 1 (q103 c4) ∷
   rw 0 (q104 c4) ∷
   rw 1 (q50 c4) ∷ []) Eq.refl

private
  q105 : Ws → Eqn
  q105 c4 = eqn (Sb2-0-41-3 ∷ []) (Sb2-4-01-3 ∷ []) (lem-SBtgt c4)

-- SBtgt @0110: 5 steps
lem-SBtgt-at0110 : Ws → ⟪ (Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-10-3 ∷ []) ⟫ʷ
lem-SBtgt-at0110 c4 = derive (Sb2-1-40-3 ∷ []) (Sb2-4-10-3 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q78 c4) ∷
   rw 1 (q105 c4) ∷
   rw 0 (q102 c4) ∷
   rw 1 (q50 c4) ∷ []) Eq.refl

private
  q106 : Ws → Eqn
  q106 c4 = eqn (Sb2-1-40-3 ∷ []) (Sb2-4-10-3 ∷ []) (lem-SBtgt-at0110 c4)

-- SBtgt @021021: 5 steps
lem-SBtgt-at021021 : Ws → ⟪ (Sb1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-20-3 ∷ []) ⟫ʷ
lem-SBtgt-at021021 c4 = derive (Sb1-2-40-3 ∷ []) (Sb1-4-20-3 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q81 c4) ∷
   rw 1 (q106 c4) ∷
   rw 0 (q98 c4) ∷
   rw 1 (q53 c4) ∷ []) Eq.refl

private
  q107 : Ws → Eqn
  q107 c4 = eqn (Sb1-2-40-3 ∷ []) (Sb1-4-20-3 ∷ []) (lem-SBtgt-at021021 c4)

-- SBtgt @03102132: 5 steps
lem-SBtgt-at03102132 : Ws → ⟪ (Sb1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-30-2 ∷ []) ⟫ʷ
lem-SBtgt-at03102132 c4 = derive (Sb1-3-40-2 ∷ []) (Sb1-4-30-2 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q85 c4) ∷
   rw 1 (q107 c4) ∷
   rw 0 (q94 c4) ∷
   rw 1 (q18 c4) ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = eqn (Sb1-3-40-2 ∷ []) (Sb1-4-30-2 ∷ []) (lem-SBtgt-at03102132 c4)

-- SBtgt @0410213243: 5 steps
lem-SBtgt-at0410213243 : Ws → ⟪ (Sb1-4-30-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-40-2 ∷ []) ⟫ʷ
lem-SBtgt-at0410213243 c4 = derive (Sb1-4-30-2 ∷ []) (Sb1-3-40-2 ∷ [])
  (rw⁻ 0 (q88 c4) ∷
   rw 1 (q90 c4) ∷
   rw 1 (q108 c4) ∷
   rw 0 (q90 c4) ∷
   rw 1 (q88 c4) ∷ []) Eq.refl

private
  q109 : Ws → Eqn
  q109 c4 = eqn (Sb1-4-30-2 ∷ []) (Sb1-3-40-2 ∷ []) (lem-SBtgt-at0410213243 c4)

-- SBtgt @04102142: 5 steps
lem-SBtgt-at04102142 : Ws → ⟪ (Sb1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-40-3 ∷ []) ⟫ʷ
lem-SBtgt-at04102142 c4 = derive (Sb1-4-20-3 ∷ []) (Sb1-2-40-3 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q94 c4) ∷
   rw 1 (q109 c4) ∷
   rw 0 (q85 c4) ∷
   rw 1 (q18 c4) ∷ []) Eq.refl

private
  q110 : Ws → Eqn
  q110 c4 = eqn (Sb1-4-20-3 ∷ []) (Sb1-2-40-3 ∷ []) (lem-SBtgt-at04102142 c4)

-- SBtgt @041041: 5 steps
lem-SBtgt-at041041 : Ws → ⟪ (Sb2-4-10-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-40-3 ∷ []) ⟫ʷ
lem-SBtgt-at041041 c4 = derive (Sb2-4-10-3 ∷ []) (Sb2-1-40-3 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q98 c4) ∷
   rw 1 (q110 c4) ∷
   rw 0 (q81 c4) ∷
   rw 1 (q53 c4) ∷ []) Eq.refl

private
  q111 : Ws → Eqn
  q111 c4 = eqn (Sb2-4-10-3 ∷ []) (Sb2-1-40-3 ∷ []) (lem-SBtgt-at041041 c4)

-- SBtgt @0440: 5 steps
lem-SBtgt-at0440 : Ws → ⟪ (Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ
lem-SBtgt-at0440 c4 = derive (Sb2-4-01-3 ∷ []) (Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q102 c4) ∷
   rw 1 (q111 c4) ∷
   rw 0 (q78 c4) ∷
   rw 1 (q50 c4) ∷ []) Eq.refl

private
  q112 : Ws → Eqn
  q112 c4 = eqn (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) (wl0038 (lit c4))
  q113 : Ws → Eqn
  q113 c4 = eqn (Sw12 ∷ Sb3-4-21-0 ∷ []) (Sb3-4-12-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·21·0⟩ (lit c4))
  q114 : Ws → Eqn
  q114 c4 = eqn (Toff012 ∷ Sb3-4-12-0 ∷ []) (Sb3-4-12-0 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩ c4)
  q115 : Ws → Eqn
  q115 c4 = eqn (Sw12 ∷ Sb3-4-12-0 ∷ []) (Sb3-4-21-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·12·0⟩ (lit c4))

-- auto TOFF012 | SBOX(3;4;12;0) @1221: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at1221 : Ws → ⟪ (Toff012 ∷ Sb3-4-21-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-21-0 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at1221 c4 = derive (Toff012 ∷ Sb3-4-21-0 ∷ []) (Sb3-4-21-0 ∷ Toff012 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q112 c4) ∷
   rw 2 (q113 c4) ∷
   rw 1 (q114 c4) ∷
   rw 0 (q115 c4) ∷
   rw 1 (q112 c4) ∷
   rw 2 (q53 c4) ∷ []) Eq.refl

private
  q116 : Ws → Eqn
  q116 c4 = eqn (Sw23 ∷ Toff013 ∷ []) (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 (lit c4))
  q117 : Ws → Eqn
  q117 c4 = eqn (Sw23 ∷ Sb2-4-31-0 ∷ []) (Sb3-4-21-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·4·31·0⟩ (lit c4))
  q118 : Ws → Eqn
  q118 c4 = eqn (Toff012 ∷ Sb3-4-21-0 ∷ []) (Sb3-4-21-0 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at1221 c4)
  q119 : Ws → Eqn
  q119 c4 = eqn (Sw23 ∷ Sb3-4-21-0 ∷ []) (Sb2-4-31-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·4·21·0⟩ (lit c4))
  q120 : Ws → Eqn
  q120 c4 = eqn (Sw23 ∷ Toff012 ∷ []) (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4))

-- auto TOFF012 | SBOX(3;4;12;0) @132132: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at132132 : Ws → ⟪ (Toff013 ∷ Sb2-4-31-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-31-0 ∷ Toff013 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at132132 c4 = derive (Toff013 ∷ Sb2-4-31-0 ∷ []) (Sb2-4-31-0 ∷ Toff013 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q117 c4) ∷
   rw 1 (q118 c4) ∷
   rw 0 (q119 c4) ∷
   rw 1 (q120 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q121 : Ws → Eqn
  q121 c4 = eqn (Sw34 ∷ Toff014 ∷ []) (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 (lit c4))
  q122 : Ws → Eqn
  q122 c4 = eqn (Sw34 ∷ Sb2-3-41-0 ∷ []) (Sb2-4-31-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·3·41·0⟩ (lit c4))
  q123 : Ws → Eqn
  q123 c4 = eqn (Toff013 ∷ Sb2-4-31-0 ∷ []) (Sb2-4-31-0 ∷ Toff013 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at132132 c4)
  q124 : Ws → Eqn
  q124 c4 = eqn (Sw34 ∷ Sb2-4-31-0 ∷ []) (Sb2-3-41-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·4·31·0⟩ (lit c4))
  q125 : Ws → Eqn
  q125 c4 = eqn (Sw34 ∷ Toff013 ∷ []) (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 (lit c4))

-- auto TOFF012 | SBOX(3;4;12;0) @14213243: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at14213243 : Ws → ⟪ (Toff014 ∷ Sb2-3-41-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-41-0 ∷ Toff014 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at14213243 c4 = derive (Toff014 ∷ Sb2-3-41-0 ∷ []) (Sb2-3-41-0 ∷ Toff014 ∷ [])
  (rw⁻ 0 (q88 c4) ∷
   rw 1 (q121 c4) ∷
   rw 2 (q122 c4) ∷
   rw 1 (q123 c4) ∷
   rw 0 (q124 c4) ∷
   rw 1 (q125 c4) ∷
   rw 2 (q88 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = eqn (Sw01 ∷ Toff104 ∷ []) (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 (lit c4))
  q127 : Ws → Eqn
  q127 c4 = eqn (Sw01 ∷ Sb2-3-40-1 ∷ []) (Sb2-3-41-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·40·1⟩ (lit c4))
  q128 : Ws → Eqn
  q128 c4 = eqn (Toff014 ∷ Sb2-3-41-0 ∷ []) (Sb2-3-41-0 ∷ Toff014 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at14213243 c4)
  q129 : Ws → Eqn
  q129 c4 = eqn (Sw01 ∷ Sb2-3-41-0 ∷ []) (Sb2-3-40-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·41·0⟩ (lit c4))
  q130 : Ws → Eqn
  q130 c4 = eqn (Sw01 ∷ Toff014 ∷ []) (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 (lit c4))

-- auto TOFF012 | SBOX(3;4;12;0) @0114203243: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0114203243 : Ws → ⟪ (Toff104 ∷ Sb2-3-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-40-1 ∷ Toff104 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0114203243 c4 = derive (Toff104 ∷ Sb2-3-40-1 ∷ []) (Sb2-3-40-1 ∷ Toff104 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q126 c4) ∷
   rw 2 (q127 c4) ∷
   rw 1 (q128 c4) ∷
   rw 0 (q129 c4) ∷
   rw 1 (q130 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q131 : Ws → Eqn
  q131 c4 = eqn (Sw12 ∷ Toff204 ∷ []) (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 (lit c4))
  q132 : Ws → Eqn
  q132 c4 = eqn (Sw12 ∷ Sb1-3-40-2 ∷ []) (Sb2-3-40-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·3·40·2⟩ (lit c4))
  q133 : Ws → Eqn
  q133 c4 = eqn (Toff104 ∷ Sb2-3-40-1 ∷ []) (Sb2-3-40-1 ∷ Toff104 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0114203243 c4)
  q134 : Ws → Eqn
  q134 c4 = eqn (Sw12 ∷ Sb2-3-40-1 ∷ []) (Sb1-3-40-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·3·40·1⟩ (lit c4))
  q135 : Ws → Eqn
  q135 c4 = eqn (Sw12 ∷ Toff104 ∷ []) (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 (lit c4))

-- auto TOFF012 | SBOX(3;4;12;0) @0214203143: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0214203143 : Ws → ⟪ (Toff204 ∷ Sb1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-40-2 ∷ Toff204 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0214203143 c4 = derive (Toff204 ∷ Sb1-3-40-2 ∷ []) (Sb1-3-40-2 ∷ Toff204 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q131 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q133 c4) ∷
   rw 0 (q134 c4) ∷
   rw 1 (q135 c4) ∷
   rw 2 (q53 c4) ∷ []) Eq.refl

private
  q136 : Ws → Eqn
  q136 c4 = eqn (Sw23 ∷ Toff304 ∷ []) (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 (lit c4))
  q137 : Ws → Eqn
  q137 c4 = eqn (Sw23 ∷ Sb1-2-40-3 ∷ []) (Sb1-3-40-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·2·40·3⟩ (lit c4))
  q138 : Ws → Eqn
  q138 c4 = eqn (Toff204 ∷ Sb1-3-40-2 ∷ []) (Sb1-3-40-2 ∷ Toff204 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0214203143 c4)
  q139 : Ws → Eqn
  q139 c4 = eqn (Sw23 ∷ Toff204 ∷ []) (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 (lit c4))

-- auto TOFF012 | SBOX(3;4;12;0) @0314203142: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314203142 : Ws → ⟪ (Toff304 ∷ Sb1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-40-3 ∷ Toff304 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314203142 c4 = derive (Toff304 ∷ Sb1-2-40-3 ∷ []) (Sb1-2-40-3 ∷ Toff304 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q136 c4) ∷
   rw 2 (q137 c4) ∷
   rw 1 (q138 c4) ∷
   rw 0 (q85 c4) ∷
   rw 1 (q139 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q140 : Ws → Eqn
  q140 c4 = eqn (Sw12 ∷ Toff304 ∷ []) (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 (lit c4))
  q141 : Ws → Eqn
  q141 c4 = eqn (Sw12 ∷ Sb2-1-40-3 ∷ []) (Sb1-2-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·40·3⟩ (lit c4))
  q142 : Ws → Eqn
  q142 c4 = eqn (Toff304 ∷ Sb1-2-40-3 ∷ []) (Sb1-2-40-3 ∷ Toff304 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314203142 c4)

-- auto TOFF012 | SBOX(3;4;12;0) @0314203241: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314203241 : Ws → ⟪ (Toff304 ∷ Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-40-3 ∷ Toff304 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314203241 c4 = derive (Toff304 ∷ Sb2-1-40-3 ∷ []) (Sb2-1-40-3 ∷ Toff304 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q140 c4) ∷
   rw 2 (q141 c4) ∷
   rw 1 (q142 c4) ∷
   rw 0 (q81 c4) ∷
   rw 1 (q140 c4) ∷
   rw 2 (q53 c4) ∷ []) Eq.refl

private
  q143 : Ws → Eqn
  q143 c4 = eqn (Sw01 ∷ Toff314 ∷ []) (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 (lit c4))
  q144 : Ws → Eqn
  q144 c4 = eqn (Sw01 ∷ Sb2-0-41-3 ∷ []) (Sb2-1-40-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·41·3⟩ (lit c4))
  q145 : Ws → Eqn
  q145 c4 = eqn (Toff304 ∷ Sb2-1-40-3 ∷ []) (Sb2-1-40-3 ∷ Toff304 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314203241 c4)
  q146 : Ws → Eqn
  q146 c4 = eqn (Sw01 ∷ Toff304 ∷ []) (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 (lit c4))

-- auto TOFF012 | SBOX(3;4;12;0) @0314213240: 7 steps
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314213240 : Ws → ⟪ (Toff314 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Toff314 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314213240 c4 = derive (Toff314 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Toff314 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q143 c4) ∷
   rw 2 (q144 c4) ∷
   rw 1 (q145 c4) ∷
   rw 0 (q78 c4) ∷
   rw 1 (q146 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q147 : Ws → Eqn
  q147 c4 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (c₂ (X ↑) (Swap))
  q148 : Ws → Eqn
  q148 c4 = eqn (X1 ∷ Bx0-1234 ∷ X1 ∷ []) (CCZ234 ∷ Bx0-1234 ∷ []) (lem-X1-beta c4)

-- X1-beta @2332: 8 steps
lem-X1-beta-at2332 : Ws → ⟪ (X1 ∷ Bx0-1324 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-X1-beta-at2332 c4 = derive (X1 ∷ Bx0-1324 ∷ X1 ∷ []) (CCZ234 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw⁻ 1 (q147 c4) ∷
   rw 2 (q19 c4) ∷
   rw⁻ 3 (q147 c4) ∷
   rw 1 (q148 c4) ∷
   rw⁻ 0 (q39 c4) ∷
   rw 1 (q23 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q149 : Ws → Eqn
  q149 c4 = eqn (X1 ∷ Sw34 ∷ []) (Sw34 ∷ X1 ∷ []) (c₂ (X ↑) (Swap ↑))
  q150 : Ws → Eqn
  q150 c4 = eqn (Sw34 ∷ Bx0-1423 ∷ []) (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4))
  q151 : Ws → Eqn
  q151 c4 = eqn (X1 ∷ Bx0-1324 ∷ X1 ∷ []) (CCZ234 ∷ Bx0-1324 ∷ []) (lem-X1-beta-at2332 c4)
  q152 : Ws → Eqn
  q152 c4 = eqn (CCZ234 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ234 ∷ []) (wl0155 (lit c4))
  q153 : Ws → Eqn
  q153 c4 = eqn (Sw34 ∷ Bx0-1324 ∷ []) (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4))

-- X1-beta @243243: 8 steps
lem-X1-beta-at243243 : Ws → ⟪ (X1 ∷ Bx0-1423 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-X1-beta-at243243 c4 = derive (X1 ∷ Bx0-1423 ∷ X1 ∷ []) (CCZ234 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q88 c4) ∷
   rw⁻ 1 (q149 c4) ∷
   rw 2 (q150 c4) ∷
   rw⁻ 3 (q149 c4) ∷
   rw 1 (q151 c4) ∷
   rw⁻ 0 (q152 c4) ∷
   rw 1 (q153 c4) ∷
   rw 2 (q88 c4) ∷ []) Eq.refl

private
  q154 : Ws → Eqn
  q154 c4 = eqn (Sw01 ∷ Bx1-0423 ∷ []) (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4))
  q155 : Ws → Eqn
  q155 c4 = eqn (X1 ∷ Bx0-1423 ∷ X1 ∷ []) (CCZ234 ∷ Bx0-1423 ∷ []) (lem-X1-beta-at243243 c4)
  q156 : Ws → Eqn
  q156 c4 = eqn (Sw01 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ))
  q157 : Ws → Eqn
  q157 c4 = eqn (Sw01 ∷ Bx0-1423 ∷ []) (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4))

-- X1-beta @0110243243: 8 steps
lem-X1-beta-at0110243243 : Ws → ⟪ (X0 ∷ Bx1-0423 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-X1-beta-at0110243243 c4 = derive (X0 ∷ Bx1-0423 ∷ X0 ∷ []) (CCZ234 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q101 c4) ∷
   rw 2 (q154 c4) ∷
   rw 3 (q101 c4) ∷
   rw 1 (q155 c4) ∷
   rw 0 (q156 c4) ∷
   rw 1 (q157 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q158 : Ws → Eqn
  q158 c4 = eqn (X0 ∷ Sw12 ∷ []) (Sw12 ∷ X0 ∷ []) (c₁ (X) (Swap))
  q159 : Ws → Eqn
  q159 c4 = eqn (Sw12 ∷ Bx2-0413 ∷ []) (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4))
  q160 : Ws → Eqn
  q160 c4 = eqn (X0 ∷ Bx1-0423 ∷ X0 ∷ []) (CCZ234 ∷ Bx1-0423 ∷ []) (lem-X1-beta-at0110243243 c4)
  q161 : Ws → Eqn
  q161 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 (lit c4))
  q162 : Ws → Eqn
  q162 c4 = eqn (Sw12 ∷ Bx1-0423 ∷ []) (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4))

-- X1-beta @0210243143: 8 steps
lem-X1-beta-at0210243143 : Ws → ⟪ (X0 ∷ Bx2-0413 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-X1-beta-at0210243143 c4 = derive (X0 ∷ Bx2-0413 ∷ X0 ∷ []) (CCZ134 ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw⁻ 1 (q158 c4) ∷
   rw 2 (q159 c4) ∷
   rw⁻ 3 (q158 c4) ∷
   rw 1 (q160 c4) ∷
   rw⁻ 0 (q161 c4) ∷
   rw 1 (q162 c4) ∷
   rw 2 (q53 c4) ∷ []) Eq.refl

private
  q163 : Ws → Eqn
  q163 c4 = eqn (Sb0-1-23-4 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234 c4)

-- auto SBOX(0;1;23;4) | CCZ234 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at2332 c4 = derive (Sb0-1-32-4 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q38 c4) ∷
   rw⁻ 2 (q39 c4) ∷
   rw 1 (q163 c4) ∷
   rw⁻ 0 (q39 c4) ∷
   rw 1 (q41 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q164 : Ws → Eqn
  q164 c4 = eqn (Sw34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4))
  q165 : Ws → Eqn
  q165 c4 = eqn (Sb0-1-32-4 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at2332 c4)
  q166 : Ws → Eqn
  q166 c4 = eqn (Sw34 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | CCZ234 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at243243 c4 = derive (Sb0-1-42-3 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q88 c4) ∷
   rw 1 (q164 c4) ∷
   rw⁻ 2 (q152 c4) ∷
   rw 1 (q165 c4) ∷
   rw⁻ 0 (q152 c4) ∷
   rw 1 (q166 c4) ∷
   rw 2 (q88 c4) ∷ []) Eq.refl

private
  q167 : Ws → Eqn
  q167 c4 = eqn (Sw01 ∷ Sb1-0-42-3 ∷ []) (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4))
  q168 : Ws → Eqn
  q168 c4 = eqn (Sb0-1-42-3 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at243243 c4)
  q169 : Ws → Eqn
  q169 c4 = eqn (Sw01 ∷ Sb0-1-42-3 ∷ []) (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4))

-- auto SBOX(0;1;23;4) | CCZ234 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0110243243 c4 = derive (Sb1-0-42-3 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q167 c4) ∷
   rw 2 (q156 c4) ∷
   rw 1 (q168 c4) ∷
   rw 0 (q156 c4) ∷
   rw 1 (q169 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q170 : Ws → Eqn
  q170 c4 = eqn (Sw12 ∷ Sb2-0-41-3 ∷ []) (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4))
  q171 : Ws → Eqn
  q171 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl0084 (lit c4))
  q172 : Ws → Eqn
  q172 c4 = eqn (Sb1-0-42-3 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0110243243 c4)
  q173 : Ws → Eqn
  q173 c4 = eqn (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4))

-- auto SBOX(0;1;23;4) | CCZ234 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0210243143 c4 = derive (Sb2-0-41-3 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q170 c4) ∷
   rw⁻ 2 (q171 c4) ∷
   rw 1 (q172 c4) ∷
   rw⁻ 0 (q161 c4) ∷
   rw 1 (q173 c4) ∷
   rw 2 (q53 c4) ∷ []) Eq.refl

private
  q174 : Ws → Eqn
  q174 c4 = eqn (CS01⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS01⁻ ∷ []) (wl0133 (lit c4))
  q175 : Ws → Eqn
  q175 c4 = eqn (CS01⁻ ∷ []) (Sb⁻2-0-41-3 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ []) (lem-F5d-CS01 c4)
  q176 : Ws → Eqn
  q176 c4 = eqn (Sw01 ∷ Sb⁻2-0-41-3 ∷ []) (Sb⁻2-1-40-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·0·41·3⟩ (lit c4))

-- F5d CS01 @0110: 8 steps
lem-F5d-CS01-at0110 : Ws → ⟪ (CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-40-3 ∷ X4 ∷ Sb⁻2-1-40-3 ∷ X4 ∷ []) ⟫ʷ
lem-F5d-CS01-at0110 c4 = derive (CS01⁻ ∷ []) (Sb⁻2-1-40-3 ∷ X4 ∷ Sb⁻2-1-40-3 ∷ X4 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw⁻ 1 (q174 c4) ∷
   rw 1 (q175 c4) ∷
   rw 0 (q176 c4) ∷
   rw 1 (q77 c4) ∷
   rw 2 (q176 c4) ∷
   rw 3 (q77 c4) ∷
   rw 4 (q50 c4) ∷ []) Eq.refl

private
  q177 : Ws → Eqn
  q177 c4 = eqn (Sw12 ∷ CS02⁻ ∷ []) (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 (lit c4))
  q178 : Ws → Eqn
  q178 c4 = eqn (CS01⁻ ∷ []) (Sb⁻2-1-40-3 ∷ X4 ∷ Sb⁻2-1-40-3 ∷ X4 ∷ []) (lem-F5d-CS01-at0110 c4)
  q179 : Ws → Eqn
  q179 c4 = eqn (Sw12 ∷ Sb⁻2-1-40-3 ∷ []) (Sb⁻1-2-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·1·40·3⟩ (lit c4))

-- F5d CS01 @021021: 8 steps
lem-F5d-CS01-at021021 : Ws → ⟪ (CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-40-3 ∷ X4 ∷ Sb⁻1-2-40-3 ∷ X4 ∷ []) ⟫ʷ
lem-F5d-CS01-at021021 c4 = derive (CS02⁻ ∷ []) (Sb⁻1-2-40-3 ∷ X4 ∷ Sb⁻1-2-40-3 ∷ X4 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q177 c4) ∷
   rw 1 (q178 c4) ∷
   rw 0 (q179 c4) ∷
   rw 1 (q80 c4) ∷
   rw 2 (q179 c4) ∷
   rw 3 (q80 c4) ∷
   rw 4 (q53 c4) ∷ []) Eq.refl

private
  q180 : Ws → Eqn
  q180 c4 = eqn (Sw23 ∷ CS03⁻ ∷ []) (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 (lit c4))
  q181 : Ws → Eqn
  q181 c4 = eqn (CS02⁻ ∷ []) (Sb⁻1-2-40-3 ∷ X4 ∷ Sb⁻1-2-40-3 ∷ X4 ∷ []) (lem-F5d-CS01-at021021 c4)
  q182 : Ws → Eqn
  q182 c4 = eqn (Sw23 ∷ Sb⁻1-2-40-3 ∷ []) (Sb⁻1-3-40-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·2·40·3⟩ (lit c4))

-- F5d CS01 @03102132: 8 steps
lem-F5d-CS01-at03102132 : Ws → ⟪ (CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-40-2 ∷ X4 ∷ Sb⁻1-3-40-2 ∷ X4 ∷ []) ⟫ʷ
lem-F5d-CS01-at03102132 c4 = derive (CS03⁻ ∷ []) (Sb⁻1-3-40-2 ∷ X4 ∷ Sb⁻1-3-40-2 ∷ X4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q180 c4) ∷
   rw 1 (q181 c4) ∷
   rw 0 (q182 c4) ∷
   rw 1 (q84 c4) ∷
   rw 2 (q182 c4) ∷
   rw 3 (q84 c4) ∷
   rw 4 (q18 c4) ∷ []) Eq.refl

private
  q183 : Ws → Eqn
  q183 c4 = eqn (Sw34 ∷ CS04⁻ ∷ []) (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 (lit c4))
  q184 : Ws → Eqn
  q184 c4 = eqn (CS03⁻ ∷ []) (Sb⁻1-3-40-2 ∷ X4 ∷ Sb⁻1-3-40-2 ∷ X4 ∷ []) (lem-F5d-CS01-at03102132 c4)
  q185 : Ws → Eqn
  q185 c4 = eqn (Sw34 ∷ Sb⁻1-3-40-2 ∷ []) (Sb⁻1-4-30-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·3·40·2⟩ (lit c4))
  q186 : Ws → Eqn
  q186 c4 = eqn (Sw34 ∷ X4 ∷ []) (X3 ∷ Sw34 ∷ []) (wl0282 (lit c4))

-- F5d CS01 @0410213243: 8 steps
lem-F5d-CS01-at0410213243 : Ws → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-30-2 ∷ X3 ∷ Sb⁻1-4-30-2 ∷ X3 ∷ []) ⟫ʷ
lem-F5d-CS01-at0410213243 c4 = derive (CS04⁻ ∷ []) (Sb⁻1-4-30-2 ∷ X3 ∷ Sb⁻1-4-30-2 ∷ X3 ∷ [])
  (rw⁻ 0 (q88 c4) ∷
   rw 1 (q183 c4) ∷
   rw 1 (q184 c4) ∷
   rw 0 (q185 c4) ∷
   rw 1 (q186 c4) ∷
   rw 2 (q185 c4) ∷
   rw 3 (q186 c4) ∷
   rw 4 (q88 c4) ∷ []) Eq.refl

private
  q187 : Ws → Eqn
  q187 c4 = eqn (Sw23 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 (lit c4))
  q188 : Ws → Eqn
  q188 c4 = eqn (CS04⁻ ∷ []) (Sb⁻1-4-30-2 ∷ X3 ∷ Sb⁻1-4-30-2 ∷ X3 ∷ []) (lem-F5d-CS01-at0410213243 c4)
  q189 : Ws → Eqn
  q189 c4 = eqn (Sw23 ∷ Sb⁻1-4-30-2 ∷ []) (Sb⁻1-4-20-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·4·30·2⟩ (lit c4))
  q190 : Ws → Eqn
  q190 c4 = eqn (Sw23 ∷ X3 ∷ []) (X2 ∷ Sw23 ∷ []) (wl0281 (lit c4))

-- F5d CS01 @04102142: 8 steps
lem-F5d-CS01-at04102142 : Ws → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-20-3 ∷ X2 ∷ Sb⁻1-4-20-3 ∷ X2 ∷ []) ⟫ʷ
lem-F5d-CS01-at04102142 c4 = derive (CS04⁻ ∷ []) (Sb⁻1-4-20-3 ∷ X2 ∷ Sb⁻1-4-20-3 ∷ X2 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q187 c4) ∷
   rw 1 (q188 c4) ∷
   rw 0 (q189 c4) ∷
   rw 1 (q190 c4) ∷
   rw 2 (q189 c4) ∷
   rw 3 (q190 c4) ∷
   rw 4 (q18 c4) ∷ []) Eq.refl

private
  q191 : Ws → Eqn
  q191 c4 = eqn (Sw12 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd04 (lit c4))
  q192 : Ws → Eqn
  q192 c4 = eqn (CS04⁻ ∷ []) (Sb⁻1-4-20-3 ∷ X2 ∷ Sb⁻1-4-20-3 ∷ X2 ∷ []) (lem-F5d-CS01-at04102142 c4)
  q193 : Ws → Eqn
  q193 c4 = eqn (Sw12 ∷ Sb⁻1-4-20-3 ∷ []) (Sb⁻2-4-10-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·4·20·3⟩ (lit c4))
  q194 : Ws → Eqn
  q194 c4 = eqn (Sw12 ∷ X2 ∷ []) (X1 ∷ Sw12 ∷ []) (wl0280 (lit c4))

-- F5d CS01 @041041: 8 steps
lem-F5d-CS01-at041041 : Ws → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-10-3 ∷ X1 ∷ Sb⁻2-4-10-3 ∷ X1 ∷ []) ⟫ʷ
lem-F5d-CS01-at041041 c4 = derive (CS04⁻ ∷ []) (Sb⁻2-4-10-3 ∷ X1 ∷ Sb⁻2-4-10-3 ∷ X1 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q191 c4) ∷
   rw 1 (q192 c4) ∷
   rw 0 (q193 c4) ∷
   rw 1 (q194 c4) ∷
   rw 2 (q193 c4) ∷
   rw 3 (q194 c4) ∷
   rw 4 (q53 c4) ∷ []) Eq.refl

private
  q195 : Ws → Eqn
  q195 c4 = eqn (Sw01 ∷ CS14⁻ ∷ []) (CS04⁻ ∷ Sw01 ∷ []) (lem-nat-0-CSd14 (lit c4))
  q196 : Ws → Eqn
  q196 c4 = eqn (CS04⁻ ∷ []) (Sb⁻2-4-10-3 ∷ X1 ∷ Sb⁻2-4-10-3 ∷ X1 ∷ []) (lem-F5d-CS01-at041041 c4)
  q197 : Ws → Eqn
  q197 c4 = eqn (Sw01 ∷ Sb⁻2-4-10-3 ∷ []) (Sb⁻2-4-01-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·4·10·3⟩ (lit c4))
  q198 : Ws → Eqn
  q198 c4 = eqn (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) (wl0371 (lit c4))

-- F5d CS01 @0440: 8 steps
lem-F5d-CS01-at0440 : Ws → ⟪ (CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-01-3 ∷ X0 ∷ Sb⁻2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F5d-CS01-at0440 c4 = derive (CS14⁻ ∷ []) (Sb⁻2-4-01-3 ∷ X0 ∷ Sb⁻2-4-01-3 ∷ X0 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q195 c4) ∷
   rw 1 (q196 c4) ∷
   rw 0 (q197 c4) ∷
   rw 1 (q198 c4) ∷
   rw 2 (q197 c4) ∷
   rw 3 (q198 c4) ∷
   rw 4 (q50 c4) ∷ []) Eq.refl

private
  q199 : Ws → Eqn
  q199 c4 = eqn (Sw01 ∷ Sb⁻2-1-40-3 ∷ []) (Sb⁻2-0-41-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·1·40·3⟩ (lit c4))
  q200 : Ws → Eqn
  q200 c4 = eqn (Sb⁻2-0-41-3 ∷ []) (Sb⁻2-4-01-3 ∷ []) (lem-SBtgtd c4)
  q201 : Ws → Eqn
  q201 c4 = eqn (Sw01 ∷ Sb⁻2-4-01-3 ∷ []) (Sb⁻2-4-10-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·4·01·3⟩ (lit c4))

-- SBtgtd @0110: 5 steps
lem-SBtgtd-at0110 : Ws → ⟪ (Sb⁻2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-10-3 ∷ []) ⟫ʷ
lem-SBtgtd-at0110 c4 = derive (Sb⁻2-1-40-3 ∷ []) (Sb⁻2-4-10-3 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q199 c4) ∷
   rw 1 (q200 c4) ∷
   rw 0 (q201 c4) ∷
   rw 1 (q50 c4) ∷ []) Eq.refl

private
  q202 : Ws → Eqn
  q202 c4 = eqn (Sw12 ∷ Sb⁻1-2-40-3 ∷ []) (Sb⁻2-1-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·2·40·3⟩ (lit c4))
  q203 : Ws → Eqn
  q203 c4 = eqn (Sb⁻2-1-40-3 ∷ []) (Sb⁻2-4-10-3 ∷ []) (lem-SBtgtd-at0110 c4)
  q204 : Ws → Eqn
  q204 c4 = eqn (Sw12 ∷ Sb⁻2-4-10-3 ∷ []) (Sb⁻1-4-20-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·4·10·3⟩ (lit c4))

-- SBtgtd @021021: 5 steps
lem-SBtgtd-at021021 : Ws → ⟪ (Sb⁻1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-20-3 ∷ []) ⟫ʷ
lem-SBtgtd-at021021 c4 = derive (Sb⁻1-2-40-3 ∷ []) (Sb⁻1-4-20-3 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q202 c4) ∷
   rw 1 (q203 c4) ∷
   rw 0 (q204 c4) ∷
   rw 1 (q53 c4) ∷ []) Eq.refl

private
  q205 : Ws → Eqn
  q205 c4 = eqn (Sw23 ∷ Sb⁻1-3-40-2 ∷ []) (Sb⁻1-2-40-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·3·40·2⟩ (lit c4))
  q206 : Ws → Eqn
  q206 c4 = eqn (Sb⁻1-2-40-3 ∷ []) (Sb⁻1-4-20-3 ∷ []) (lem-SBtgtd-at021021 c4)
  q207 : Ws → Eqn
  q207 c4 = eqn (Sw23 ∷ Sb⁻1-4-20-3 ∷ []) (Sb⁻1-4-30-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·4·20·3⟩ (lit c4))

-- SBtgtd @03102132: 5 steps
lem-SBtgtd-at03102132 : Ws → ⟪ (Sb⁻1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-30-2 ∷ []) ⟫ʷ
lem-SBtgtd-at03102132 c4 = derive (Sb⁻1-3-40-2 ∷ []) (Sb⁻1-4-30-2 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q205 c4) ∷
   rw 1 (q206 c4) ∷
   rw 0 (q207 c4) ∷
   rw 1 (q18 c4) ∷ []) Eq.refl

private
  q208 : Ws → Eqn
  q208 c4 = eqn (Sw34 ∷ Sb⁻1-4-30-2 ∷ []) (Sb⁻1-3-40-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·4·30·2⟩ (lit c4))
  q209 : Ws → Eqn
  q209 c4 = eqn (Sb⁻1-3-40-2 ∷ []) (Sb⁻1-4-30-2 ∷ []) (lem-SBtgtd-at03102132 c4)

-- SBtgtd @0410213243: 5 steps
lem-SBtgtd-at0410213243 : Ws → ⟪ (Sb⁻1-4-30-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-40-2 ∷ []) ⟫ʷ
lem-SBtgtd-at0410213243 c4 = derive (Sb⁻1-4-30-2 ∷ []) (Sb⁻1-3-40-2 ∷ [])
  (rw⁻ 0 (q88 c4) ∷
   rw 1 (q208 c4) ∷
   rw 1 (q209 c4) ∷
   rw 0 (q208 c4) ∷
   rw 1 (q88 c4) ∷ []) Eq.refl

private
  q210 : Ws → Eqn
  q210 c4 = eqn (Sb⁻1-4-30-2 ∷ []) (Sb⁻1-3-40-2 ∷ []) (lem-SBtgtd-at0410213243 c4)

-- SBtgtd @04102142: 5 steps
lem-SBtgtd-at04102142 : Ws → ⟪ (Sb⁻1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-40-3 ∷ []) ⟫ʷ
lem-SBtgtd-at04102142 c4 = derive (Sb⁻1-4-20-3 ∷ []) (Sb⁻1-2-40-3 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q207 c4) ∷
   rw 1 (q210 c4) ∷
   rw 0 (q205 c4) ∷
   rw 1 (q18 c4) ∷ []) Eq.refl

private
  q211 : Ws → Eqn
  q211 c4 = eqn (Sb⁻1-4-20-3 ∷ []) (Sb⁻1-2-40-3 ∷ []) (lem-SBtgtd-at04102142 c4)

-- SBtgtd @041041: 5 steps
lem-SBtgtd-at041041 : Ws → ⟪ (Sb⁻2-4-10-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-40-3 ∷ []) ⟫ʷ
lem-SBtgtd-at041041 c4 = derive (Sb⁻2-4-10-3 ∷ []) (Sb⁻2-1-40-3 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q204 c4) ∷
   rw 1 (q211 c4) ∷
   rw 0 (q202 c4) ∷
   rw 1 (q53 c4) ∷ []) Eq.refl

private
  q212 : Ws → Eqn
  q212 c4 = eqn (Sb⁻2-4-10-3 ∷ []) (Sb⁻2-1-40-3 ∷ []) (lem-SBtgtd-at041041 c4)

-- SBtgtd @0440: 5 steps
lem-SBtgtd-at0440 : Ws → ⟪ (Sb⁻2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-SBtgtd-at0440 c4 = derive (Sb⁻2-4-01-3 ∷ []) (Sb⁻2-0-41-3 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q201 c4) ∷
   rw 1 (q212 c4) ∷
   rw 0 (q199 c4) ∷
   rw 1 (q50 c4) ∷ []) Eq.refl

private
  q213 : Ws → Eqn
  q213 c4 = eqn (Sw23 ∷ Sb⁻0-1-32-4 ∷ []) (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4))
  q214 : Ws → Eqn
  q214 c4 = eqn (Sw23 ∷ Toff423 ∷ []) (Toff423 ∷ Sw23 ∷ []) (wl0087 (lit c4))
  q215 : Ws → Eqn
  q215 c4 = eqn (Sb⁻0-1-23-4 ∷ Toff423 ∷ []) (Toff423 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423 c4)
  q216 : Ws → Eqn
  q216 c4 = eqn (Sw23 ∷ Sb⁻0-1-23-4 ∷ []) (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | TOFF423 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ Toff423 ∷ []) (Toff423 ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q213 c4) ∷
   rw 2 (q214 c4) ∷
   rw 1 (q215 c4) ∷
   rw 0 (q214 c4) ∷
   rw 1 (q216 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q217 : Ws → Eqn
  q217 c4 = eqn (Sw34 ∷ Sb⁻0-1-42-3 ∷ []) (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ (lit c4))
  q218 : Ws → Eqn
  q218 c4 = eqn (Sw34 ∷ Toff324 ∷ []) (Toff423 ∷ Sw34 ∷ []) (wl0119 (lit c4))
  q219 : Ws → Eqn
  q219 c4 = eqn (Sb⁻0-1-32-4 ∷ Toff423 ∷ []) (Toff423 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at2332 c4)
  q220 : Ws → Eqn
  q220 c4 = eqn (Sw34 ∷ Toff423 ∷ []) (Toff324 ∷ Sw34 ∷ []) (wl0120 (lit c4))
  q221 : Ws → Eqn
  q221 c4 = eqn (Sw34 ∷ Sb⁻0-1-32-4 ∷ []) (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | TOFF423 @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at243243 : Ws → ⟪ (Sb⁻0-1-42-3 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at243243 c4 = derive (Sb⁻0-1-42-3 ∷ Toff324 ∷ []) (Toff324 ∷ Sb⁻0-1-42-3 ∷ [])
  (rw⁻ 0 (q88 c4) ∷
   rw 1 (q217 c4) ∷
   rw 2 (q218 c4) ∷
   rw 1 (q219 c4) ∷
   rw 0 (q220 c4) ∷
   rw 1 (q221 c4) ∷
   rw 2 (q88 c4) ∷ []) Eq.refl

private
  q222 : Ws → Eqn
  q222 c4 = eqn (Sw01 ∷ Sb⁻1-0-42-3 ∷ []) (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ (lit c4))
  q223 : Ws → Eqn
  q223 c4 = eqn (Sw01 ∷ Toff324 ∷ []) (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))
  q224 : Ws → Eqn
  q224 c4 = eqn (Sb⁻0-1-42-3 ∷ Toff324 ∷ []) (Toff324 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at243243 c4)
  q225 : Ws → Eqn
  q225 c4 = eqn (Sw01 ∷ Sb⁻0-1-42-3 ∷ []) (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | TOFF423 @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0110243243 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0110243243 c4 = derive (Sb⁻1-0-42-3 ∷ Toff324 ∷ []) (Toff324 ∷ Sb⁻1-0-42-3 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q222 c4) ∷
   rw 2 (q223 c4) ∷
   rw 1 (q224 c4) ∷
   rw 0 (q223 c4) ∷
   rw 1 (q225 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q226 : Ws → Eqn
  q226 c4 = eqn (Sw12 ∷ Sb⁻2-0-41-3 ∷ []) (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ (lit c4))
  q227 : Ws → Eqn
  q227 c4 = eqn (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) (wl0064 (lit c4))
  q228 : Ws → Eqn
  q228 c4 = eqn (Sb⁻1-0-42-3 ∷ Toff324 ∷ []) (Toff324 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0110243243 c4)
  q229 : Ws → Eqn
  q229 c4 = eqn (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) (wl0063 (lit c4))
  q230 : Ws → Eqn
  q230 c4 = eqn (Sw12 ∷ Sb⁻1-0-42-3 ∷ []) (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | TOFF423 @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0210243143 : Ws → ⟪ (Sb⁻2-0-41-3 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0210243143 c4 = derive (Sb⁻2-0-41-3 ∷ Toff314 ∷ []) (Toff314 ∷ Sb⁻2-0-41-3 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q226 c4) ∷
   rw 2 (q227 c4) ∷
   rw 1 (q228 c4) ∷
   rw 0 (q229 c4) ∷
   rw 1 (q230 c4) ∷
   rw 2 (q53 c4) ∷ []) Eq.refl

private
  q231 : Ws → Eqn
  q231 c4 = eqn (Sw23 ∷ Bx⁻3-0412 ∷ []) (Bx⁻2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·0412⟩ (lit c4))
  q232 : Ws → Eqn
  q232 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q233 : Ws → Eqn
  q233 c4 = eqn (Sw23 ∷ Bx2-0413 ∷ []) (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4))

-- BOXd-BOX @0310243142: 5 steps
lem-BOXd-BOX-at0310243142 : Ws → ⟪ (Bx⁻3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-BOXd-BOX-at0310243142 c4 = derive (Bx⁻3-0412 ∷ []) (Bx3-0412 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q231 c4) ∷
   rw 1 (q232 c4) ∷
   rw 0 (q233 c4) ∷
   rw 1 (q18 c4) ∷ []) Eq.refl

private
  q234 : Ws → Eqn
  q234 c4 = eqn (Sw23 ∷ Bx3-0412 ∷ []) (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4))
  q235 : Ws → Eqn
  q235 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q236 : Ws → Eqn
  q236 c4 = eqn (Sw23 ∷ Bx2-0431 ∷ []) (Bx3-0421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0431⟩ (lit c4))

-- sym34 @0310243142: 5 steps
lem-sym34-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-sym34-at0310243142 c4 = derive (Bx3-0412 ∷ []) (Bx3-0421 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q234 c4) ∷
   rw 1 (q235 c4) ∷
   rw 0 (q236 c4) ∷
   rw 1 (q18 c4) ∷ []) Eq.refl

private
  q237 : Ws → Eqn
  q237 c4 = eqn (Sw12 ∷ Bx3-0421 ∷ []) (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ (lit c4))
  q238 : Ws → Eqn
  q238 c4 = eqn (Sw12 ∷ Bx3-0142 ∷ []) (Bx3-0241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0142⟩ (lit c4))

-- sym23 @0310243241: 5 steps
lem-sym23-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-sym23-at0310243241 c4 = derive (Bx3-0421 ∷ []) (Bx3-0241 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q237 c4) ∷
   rw 1 (q2 c4) ∷
   rw 0 (q238 c4) ∷
   rw 1 (q53 c4) ∷ []) Eq.refl

private
  q239 : Ws → Eqn
  q239 c4 = eqn (Sw23 ∷ Bx3-0142 ∷ []) (Bx2-0143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0142⟩ (lit c4))
  q240 : Ws → Eqn
  q240 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q241 : Ws → Eqn
  q241 c4 = eqn (Sw23 ∷ Toff201 ∷ []) (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 (lit c4))

-- beta-T @0310213442: 8 steps
lem-beta-T-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) ⟫ʷ
lem-beta-T-at0310213442 c4 = derive (Bx3-0142 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q239 c4) ∷
   rw 1 (q240 c4) ∷
   rw 0 (q241 c4) ∷
   rw⁻ 1 (q39 c4) ∷
   rw 2 (q241 c4) ∷
   rw⁻ 3 (q39 c4) ∷
   rw 4 (q18 c4) ∷ []) Eq.refl

private
  q242 : Ws → Eqn
  q242 c4 = eqn (Sw12 ∷ Bx3-0241 ∷ []) (Bx3-0142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0241⟩ (lit c4))
  q243 : Ws → Eqn
  q243 c4 = eqn (Bx3-0142 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-beta-T-at0310213442 c4)
  q244 : Ws → Eqn
  q244 c4 = eqn (Sw12 ∷ Toff301 ∷ []) (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 (lit c4))

-- beta-T @03103441: 8 steps
lem-beta-T-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) ⟫ʷ
lem-beta-T-at03103441 c4 = derive (Bx3-0241 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q242 c4) ∷
   rw 1 (q243 c4) ∷
   rw 0 (q244 c4) ∷
   rw⁻ 1 (q161 c4) ∷
   rw 2 (q244 c4) ∷
   rw⁻ 3 (q161 c4) ∷
   rw 4 (q53 c4) ∷ []) Eq.refl

private
  q245 : Ws → Eqn
  q245 c4 = eqn (Sw12 ∷ Bx3-0412 ∷ []) (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ (lit c4))

-- sym23 @03103441: 5 steps
lem-sym23-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-sym23-at03103441 c4 = derive (Bx3-0241 ∷ []) (Bx3-0421 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q242 c4) ∷
   rw 1 (q4 c4) ∷
   rw 0 (q245 c4) ∷
   rw 1 (q53 c4) ∷ []) Eq.refl

private
  q246 : Ws → Eqn
  q246 c4 = eqn (Bx3-0412 ∷ []) (Bx3-0421 ∷ []) (lem-sym34-at0310243142 c4)

-- sym34 @0310243241: 5 steps
lem-sym34-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-sym34-at0310243241 c4 = derive (Bx3-0421 ∷ []) (Bx3-0412 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q237 c4) ∷
   rw 1 (q246 c4) ∷
   rw 0 (q237 c4) ∷
   rw 1 (q53 c4) ∷ []) Eq.refl

private
  q247 : Ws → Eqn
  q247 c4 = eqn (CCZ023 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ023 ∷ []) (wl0065 (lit c4))
  q248 : Ws → Eqn
  q248 c4 = eqn (Sb⁻0-1-23-4 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023 c4)

-- auto SBOXd(0;1;23;4) | CCZ023 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q213 c4) ∷
   rw⁻ 2 (q247 c4) ∷
   rw 1 (q248 c4) ∷
   rw⁻ 0 (q247 c4) ∷
   rw 1 (q216 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q249 : Ws → Eqn
  q249 c4 = eqn (Sw34 ∷ CCZ024 ∷ []) (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 (lit c4))
  q250 : Ws → Eqn
  q250 c4 = eqn (Sb⁻0-1-32-4 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at2332 c4)
  q251 : Ws → Eqn
  q251 c4 = eqn (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 (lit c4))

-- auto SBOXd(0;1;23;4) | CCZ023 @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at243243 : Ws → ⟪ (Sb⁻0-1-42-3 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at243243 c4 = derive (Sb⁻0-1-42-3 ∷ CCZ024 ∷ []) (CCZ024 ∷ Sb⁻0-1-42-3 ∷ [])
  (rw⁻ 0 (q88 c4) ∷
   rw 1 (q217 c4) ∷
   rw 2 (q249 c4) ∷
   rw 1 (q250 c4) ∷
   rw 0 (q251 c4) ∷
   rw 1 (q221 c4) ∷
   rw 2 (q88 c4) ∷ []) Eq.refl

private
  q252 : Ws → Eqn
  q252 c4 = eqn (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4))
  q253 : Ws → Eqn
  q253 c4 = eqn (Sb⁻0-1-42-3 ∷ CCZ024 ∷ []) (CCZ024 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at243243 c4)
  q254 : Ws → Eqn
  q254 c4 = eqn (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4))

-- auto SBOXd(0;1;23;4) | CCZ023 @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at0110243243 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at0110243243 c4 = derive (Sb⁻1-0-42-3 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb⁻1-0-42-3 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q222 c4) ∷
   rw 2 (q252 c4) ∷
   rw 1 (q253 c4) ∷
   rw 0 (q254 c4) ∷
   rw 1 (q225 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q255 : Ws → Eqn
  q255 c4 = eqn (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) (wl0078 (lit c4))
  q256 : Ws → Eqn
  q256 c4 = eqn (Sb⁻1-0-42-3 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at0110243243 c4)

-- auto SBOXd(0;1;23;4) | CCZ023 @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at0210243143 : Ws → ⟪ (Sb⁻2-0-41-3 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at0210243143 c4 = derive (Sb⁻2-0-41-3 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb⁻2-0-41-3 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q226 c4) ∷
   rw⁻ 2 (q255 c4) ∷
   rw 1 (q256 c4) ∷
   rw⁻ 0 (q255 c4) ∷
   rw 1 (q230 c4) ∷
   rw 2 (q53 c4) ∷ []) Eq.refl

private
  q257 : Ws → Eqn
  q257 c4 = eqn (CCZ012 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ012 ∷ []) (wl0096 (lit c4))
  q258 : Ws → Eqn
  q258 c4 = eqn (Sw01 ∷ Bx3-4102 ∷ []) (Bx3-4012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4102⟩ (lit c4))
  q259 : Ws → Eqn
  q259 c4 = eqn (Sw01 ∷ Bx3-4012 ∷ []) (Bx3-4102 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4012⟩ (lit c4))

-- auto CCZ012 | BOX(3;4012) @0110: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0110 : Ws → ⟪ (CCZ012 ∷ Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0110 c4 = derive (CCZ012 ∷ Bx3-4102 ∷ []) (Bx3-4102 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw⁻ 1 (q257 c4) ∷
   rw 2 (q258 c4) ∷
   rw 1 (q6 c4) ∷
   rw 0 (q259 c4) ∷
   rw⁻ 1 (q257 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q260 : Ws → Eqn
  q260 c4 = eqn (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ []) (wl0037 (lit c4))
  q261 : Ws → Eqn
  q261 c4 = eqn (Sw12 ∷ Bx3-4201 ∷ []) (Bx3-4102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4201⟩ (lit c4))
  q262 : Ws → Eqn
  q262 c4 = eqn (CCZ012 ∷ Bx3-4102 ∷ []) (Bx3-4102 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0110 c4)
  q263 : Ws → Eqn
  q263 c4 = eqn (Sw12 ∷ Bx3-4102 ∷ []) (Bx3-4201 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4102⟩ (lit c4))

-- auto CCZ012 | BOX(3;4012) @021021: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at021021 : Ws → ⟪ (CCZ012 ∷ Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at021021 c4 = derive (CCZ012 ∷ Bx3-4201 ∷ []) (Bx3-4201 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw⁻ 1 (q260 c4) ∷
   rw 2 (q261 c4) ∷
   rw 1 (q262 c4) ∷
   rw 0 (q263 c4) ∷
   rw⁻ 1 (q260 c4) ∷
   rw 2 (q53 c4) ∷ []) Eq.refl

private
  q264 : Ws → Eqn
  q264 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4))
  q265 : Ws → Eqn
  q265 c4 = eqn (Sw23 ∷ Bx2-4301 ∷ []) (Bx3-4201 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4301⟩ (lit c4))
  q266 : Ws → Eqn
  q266 c4 = eqn (CCZ012 ∷ Bx3-4201 ∷ []) (Bx3-4201 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at021021 c4)
  q267 : Ws → Eqn
  q267 c4 = eqn (Sw23 ∷ Bx3-4201 ∷ []) (Bx2-4301 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4201⟩ (lit c4))
  q268 : Ws → Eqn
  q268 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4))

-- auto CCZ012 | BOX(3;4012) @03102132: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at03102132 : Ws → ⟪ (CCZ013 ∷ Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at03102132 c4 = derive (CCZ013 ∷ Bx2-4301 ∷ []) (Bx2-4301 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q264 c4) ∷
   rw 2 (q265 c4) ∷
   rw 1 (q266 c4) ∷
   rw 0 (q267 c4) ∷
   rw 1 (q268 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q269 : Ws → Eqn
  q269 c4 = eqn (Sw34 ∷ CCZ014 ∷ []) (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 (lit c4))
  q270 : Ws → Eqn
  q270 c4 = eqn (Sw34 ∷ Bx2-3401 ∷ []) (Bx2-4301 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·3401⟩ (lit c4))
  q271 : Ws → Eqn
  q271 c4 = eqn (CCZ013 ∷ Bx2-4301 ∷ []) (Bx2-4301 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at03102132 c4)
  q272 : Ws → Eqn
  q272 c4 = eqn (Sw34 ∷ Bx2-4301 ∷ []) (Bx2-3401 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·4301⟩ (lit c4))
  q273 : Ws → Eqn
  q273 c4 = eqn (Sw34 ∷ CCZ013 ∷ []) (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 (lit c4))

-- auto CCZ012 | BOX(3;4012) @0410213243: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410213243 : Ws → ⟪ (CCZ014 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410213243 c4 = derive (CCZ014 ∷ Bx2-3401 ∷ []) (Bx2-3401 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q88 c4) ∷
   rw 1 (q269 c4) ∷
   rw 2 (q270 c4) ∷
   rw 1 (q271 c4) ∷
   rw 0 (q272 c4) ∷
   rw 1 (q273 c4) ∷
   rw 2 (q88 c4) ∷ []) Eq.refl

private
  q274 : Ws → Eqn
  q274 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4))
  q275 : Ws → Eqn
  q275 c4 = eqn (CCZ014 ∷ Bx2-3401 ∷ []) (Bx2-3401 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410213243 c4)
  q276 : Ws → Eqn
  q276 c4 = eqn (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4))

-- auto CCZ012 | BOX(3;4012) @04103143: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at04103143 : Ws → ⟪ (CCZ024 ∷ Bx1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at04103143 c4 = derive (CCZ024 ∷ Bx1-3402 ∷ []) (Bx1-3402 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q274 c4) ∷
   rw 2 (q64 c4) ∷
   rw 1 (q275 c4) ∷
   rw 0 (q54 c4) ∷
   rw 1 (q276 c4) ∷
   rw 2 (q53 c4) ∷ []) Eq.refl

private
  q277 : Ws → Eqn
  q277 c4 = eqn (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4))
  q278 : Ws → Eqn
  q278 c4 = eqn (Sw23 ∷ Bx1-2403 ∷ []) (Bx1-3402 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·2403⟩ (lit c4))
  q279 : Ws → Eqn
  q279 c4 = eqn (CCZ024 ∷ Bx1-3402 ∷ []) (Bx1-3402 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at04103143 c4)
  q280 : Ws → Eqn
  q280 c4 = eqn (Sw23 ∷ Bx1-3402 ∷ []) (Bx1-2403 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·3402⟩ (lit c4))
  q281 : Ws → Eqn
  q281 c4 = eqn (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 (lit c4))

-- auto CCZ012 | BOX(3;4012) @0410233142: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410233142 : Ws → ⟪ (CCZ034 ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410233142 c4 = derive (CCZ034 ∷ Bx1-2403 ∷ []) (Bx1-2403 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q277 c4) ∷
   rw 2 (q278 c4) ∷
   rw 1 (q279 c4) ∷
   rw 0 (q280 c4) ∷
   rw 1 (q281 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q282 : Ws → Eqn
  q282 c4 = eqn (Sw12 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4))
  q283 : Ws → Eqn
  q283 c4 = eqn (Sw12 ∷ Bx2-1403 ∷ []) (Bx1-2403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1403⟩ (lit c4))
  q284 : Ws → Eqn
  q284 c4 = eqn (CCZ034 ∷ Bx1-2403 ∷ []) (Bx1-2403 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410233142 c4)
  q285 : Ws → Eqn
  q285 c4 = eqn (Sw12 ∷ Bx1-2403 ∷ []) (Bx2-1403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2403⟩ (lit c4))

-- auto CCZ012 | BOX(3;4012) @0410233241: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410233241 : Ws → ⟪ (CCZ034 ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410233241 c4 = derive (CCZ034 ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q282 c4) ∷
   rw 2 (q283 c4) ∷
   rw 1 (q284 c4) ∷
   rw 0 (q285 c4) ∷
   rw 1 (q282 c4) ∷
   rw 2 (q53 c4) ∷ []) Eq.refl

private
  q286 : Ws → Eqn
  q286 c4 = eqn (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4))
  q287 : Ws → Eqn
  q287 c4 = eqn (Sw01 ∷ Bx2-0413 ∷ []) (Bx2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0413⟩ (lit c4))
  q288 : Ws → Eqn
  q288 c4 = eqn (CCZ034 ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410233241 c4)
  q289 : Ws → Eqn
  q289 c4 = eqn (Sw01 ∷ Bx2-1403 ∷ []) (Bx2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1403⟩ (lit c4))
  q290 : Ws → Eqn
  q290 c4 = eqn (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 (lit c4))

-- auto CCZ012 | BOX(3;4012) @04233240: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at04233240 : Ws → ⟪ (CCZ134 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ134 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at04233240 c4 = derive (CCZ134 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CCZ134 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q286 c4) ∷
   rw 2 (q287 c4) ∷
   rw 1 (q288 c4) ∷
   rw 0 (q289 c4) ∷
   rw 1 (q290 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q291 : Ws → Eqn
  q291 c4 = eqn (Sw01 ∷ Sb3-4-10-2 ∷ []) (Sb3-4-01-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·4·10·2⟩ (lit c4))
  q292 : Ws → Eqn
  q292 c4 = eqn (CCZ012 ∷ Sb3-4-01-2 ∷ []) (Sb3-4-01-2 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩ c4)
  q293 : Ws → Eqn
  q293 c4 = eqn (Sw01 ∷ Sb3-4-01-2 ∷ []) (Sb3-4-10-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·4·01·2⟩ (lit c4))

-- auto CCZ012 | SBOX(3;4;01;2) @0110: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0110 : Ws → ⟪ (CCZ012 ∷ Sb3-4-10-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-10-2 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0110 c4 = derive (CCZ012 ∷ Sb3-4-10-2 ∷ []) (Sb3-4-10-2 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw⁻ 1 (q257 c4) ∷
   rw 2 (q291 c4) ∷
   rw 1 (q292 c4) ∷
   rw 0 (q293 c4) ∷
   rw⁻ 1 (q257 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q294 : Ws → Eqn
  q294 c4 = eqn (Sw12 ∷ Sb3-4-20-1 ∷ []) (Sb3-4-10-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·20·1⟩ (lit c4))
  q295 : Ws → Eqn
  q295 c4 = eqn (CCZ012 ∷ Sb3-4-10-2 ∷ []) (Sb3-4-10-2 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0110 c4)
  q296 : Ws → Eqn
  q296 c4 = eqn (Sw12 ∷ Sb3-4-10-2 ∷ []) (Sb3-4-20-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·10·2⟩ (lit c4))

-- auto CCZ012 | SBOX(3;4;01;2) @021021: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at021021 : Ws → ⟪ (CCZ012 ∷ Sb3-4-20-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-20-1 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at021021 c4 = derive (CCZ012 ∷ Sb3-4-20-1 ∷ []) (Sb3-4-20-1 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw⁻ 1 (q260 c4) ∷
   rw 2 (q294 c4) ∷
   rw 1 (q295 c4) ∷
   rw 0 (q296 c4) ∷
   rw⁻ 1 (q260 c4) ∷
   rw 2 (q53 c4) ∷ []) Eq.refl

private
  q297 : Ws → Eqn
  q297 c4 = eqn (Sw23 ∷ Sb2-4-30-1 ∷ []) (Sb3-4-20-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·4·30·1⟩ (lit c4))
  q298 : Ws → Eqn
  q298 c4 = eqn (CCZ012 ∷ Sb3-4-20-1 ∷ []) (Sb3-4-20-1 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at021021 c4)
  q299 : Ws → Eqn
  q299 c4 = eqn (Sw23 ∷ Sb3-4-20-1 ∷ []) (Sb2-4-30-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·4·20·1⟩ (lit c4))

-- auto CCZ012 | SBOX(3;4;01;2) @03102132: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at03102132 : Ws → ⟪ (CCZ013 ∷ Sb2-4-30-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-30-1 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at03102132 c4 = derive (CCZ013 ∷ Sb2-4-30-1 ∷ []) (Sb2-4-30-1 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q264 c4) ∷
   rw 2 (q297 c4) ∷
   rw 1 (q298 c4) ∷
   rw 0 (q299 c4) ∷
   rw 1 (q268 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q300 : Ws → Eqn
  q300 c4 = eqn (Sw34 ∷ Sb2-3-40-1 ∷ []) (Sb2-4-30-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·3·40·1⟩ (lit c4))
  q301 : Ws → Eqn
  q301 c4 = eqn (CCZ013 ∷ Sb2-4-30-1 ∷ []) (Sb2-4-30-1 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at03102132 c4)
  q302 : Ws → Eqn
  q302 c4 = eqn (Sw34 ∷ Sb2-4-30-1 ∷ []) (Sb2-3-40-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·4·30·1⟩ (lit c4))

-- auto CCZ012 | SBOX(3;4;01;2) @0410213243: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410213243 : Ws → ⟪ (CCZ014 ∷ Sb2-3-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-40-1 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410213243 c4 = derive (CCZ014 ∷ Sb2-3-40-1 ∷ []) (Sb2-3-40-1 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q88 c4) ∷
   rw 1 (q269 c4) ∷
   rw 2 (q300 c4) ∷
   rw 1 (q301 c4) ∷
   rw 0 (q302 c4) ∷
   rw 1 (q273 c4) ∷
   rw 2 (q88 c4) ∷ []) Eq.refl

private
  q303 : Ws → Eqn
  q303 c4 = eqn (CCZ014 ∷ Sb2-3-40-1 ∷ []) (Sb2-3-40-1 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410213243 c4)

-- auto CCZ012 | SBOX(3;4;01;2) @04103143: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at04103143 : Ws → ⟪ (CCZ024 ∷ Sb1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-40-2 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at04103143 c4 = derive (CCZ024 ∷ Sb1-3-40-2 ∷ []) (Sb1-3-40-2 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q274 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q303 c4) ∷
   rw 0 (q134 c4) ∷
   rw 1 (q276 c4) ∷
   rw 2 (q53 c4) ∷ []) Eq.refl

private
  q304 : Ws → Eqn
  q304 c4 = eqn (CCZ024 ∷ Sb1-3-40-2 ∷ []) (Sb1-3-40-2 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at04103143 c4)

-- auto CCZ012 | SBOX(3;4;01;2) @0410233142: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410233142 : Ws → ⟪ (CCZ034 ∷ Sb1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-40-3 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410233142 c4 = derive (CCZ034 ∷ Sb1-2-40-3 ∷ []) (Sb1-2-40-3 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q277 c4) ∷
   rw 2 (q137 c4) ∷
   rw 1 (q304 c4) ∷
   rw 0 (q85 c4) ∷
   rw 1 (q281 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q305 : Ws → Eqn
  q305 c4 = eqn (CCZ034 ∷ Sb1-2-40-3 ∷ []) (Sb1-2-40-3 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410233142 c4)

-- auto CCZ012 | SBOX(3;4;01;2) @0410233241: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410233241 : Ws → ⟪ (CCZ034 ∷ Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-40-3 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410233241 c4 = derive (CCZ034 ∷ Sb2-1-40-3 ∷ []) (Sb2-1-40-3 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q282 c4) ∷
   rw 2 (q141 c4) ∷
   rw 1 (q305 c4) ∷
   rw 0 (q81 c4) ∷
   rw 1 (q282 c4) ∷
   rw 2 (q53 c4) ∷ []) Eq.refl

private
  q306 : Ws → Eqn
  q306 c4 = eqn (CCZ034 ∷ Sb2-1-40-3 ∷ []) (Sb2-1-40-3 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410233241 c4)

-- auto CCZ012 | SBOX(3;4;01;2) @04233240: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at04233240 : Ws → ⟪ (CCZ134 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CCZ134 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at04233240 c4 = derive (CCZ134 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CCZ134 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q286 c4) ∷
   rw 2 (q144 c4) ∷
   rw 1 (q306 c4) ∷
   rw 0 (q78 c4) ∷
   rw 1 (q290 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q307 : Ws → Eqn
  q307 c4 = eqn (Sb0-1-23-4 ∷ Toff423 ∷ []) (Toff423 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423 c4)

-- auto SBOX(0;1;23;4) | TOFF423 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at2332 c4 = derive (Sb0-1-32-4 ∷ Toff423 ∷ []) (Toff423 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q38 c4) ∷
   rw 2 (q214 c4) ∷
   rw 1 (q307 c4) ∷
   rw 0 (q214 c4) ∷
   rw 1 (q41 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q308 : Ws → Eqn
  q308 c4 = eqn (Sb0-1-32-4 ∷ Toff423 ∷ []) (Toff423 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at2332 c4)

-- auto SBOX(0;1;23;4) | TOFF423 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at243243 c4 = derive (Sb0-1-42-3 ∷ Toff324 ∷ []) (Toff324 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q88 c4) ∷
   rw 1 (q164 c4) ∷
   rw 2 (q218 c4) ∷
   rw 1 (q308 c4) ∷
   rw 0 (q220 c4) ∷
   rw 1 (q166 c4) ∷
   rw 2 (q88 c4) ∷ []) Eq.refl

private
  q309 : Ws → Eqn
  q309 c4 = eqn (Sb0-1-42-3 ∷ Toff324 ∷ []) (Toff324 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at243243 c4)

-- auto SBOX(0;1;23;4) | TOFF423 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0110243243 c4 = derive (Sb1-0-42-3 ∷ Toff324 ∷ []) (Toff324 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q167 c4) ∷
   rw 2 (q223 c4) ∷
   rw 1 (q309 c4) ∷
   rw 0 (q223 c4) ∷
   rw 1 (q169 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q310 : Ws → Eqn
  q310 c4 = eqn (Sb1-0-42-3 ∷ Toff324 ∷ []) (Toff324 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0110243243 c4)

-- auto SBOX(0;1;23;4) | TOFF423 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0210243143 c4 = derive (Sb2-0-41-3 ∷ Toff314 ∷ []) (Toff314 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q170 c4) ∷
   rw 2 (q227 c4) ∷
   rw 1 (q310 c4) ∷
   rw 0 (q229 c4) ∷
   rw 1 (q173 c4) ∷
   rw 2 (q53 c4) ∷ []) Eq.refl

private
  q311 : Ws → Eqn
  q311 c4 = eqn (Sw12 ∷ Bx1-0234 ∷ []) (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4))
  q312 : Ws → Eqn
  q312 c4 = eqn (CS01⁻ ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨2·0134⟩ c4)
  q313 : Ws → Eqn
  q313 c4 = eqn (Sw12 ∷ Bx2-0134 ∷ []) (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4))
  q314 : Ws → Eqn
  q314 c4 = eqn (Sw12 ∷ CS01⁻ ∷ []) (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 (lit c4))

-- auto CSd01 | BOX(2;0134) @1221: 7 steps
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at1221 : Ws → ⟪ (CS02⁻ ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at1221 c4 = derive (CS02⁻ ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CS02⁻ ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q177 c4) ∷
   rw 2 (q311 c4) ∷
   rw 1 (q312 c4) ∷
   rw 0 (q313 c4) ∷
   rw 1 (q314 c4) ∷
   rw 2 (q53 c4) ∷ []) Eq.refl

private
  q315 : Ws → Eqn
  q315 c4 = eqn (Sw23 ∷ Bx1-0324 ∷ []) (Bx1-0234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0324⟩ (lit c4))
  q316 : Ws → Eqn
  q316 c4 = eqn (CS02⁻ ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CS02⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨2·0134⟩-at1221 c4)
  q317 : Ws → Eqn
  q317 c4 = eqn (Sw23 ∷ Bx1-0234 ∷ []) (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ (lit c4))
  q318 : Ws → Eqn
  q318 c4 = eqn (Sw23 ∷ CS02⁻ ∷ []) (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 (lit c4))

-- auto CSd01 | BOX(2;0134) @132132: 7 steps
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at132132 : Ws → ⟪ (CS03⁻ ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at132132 c4 = derive (CS03⁻ ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ CS03⁻ ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q180 c4) ∷
   rw 2 (q315 c4) ∷
   rw 1 (q316 c4) ∷
   rw 0 (q317 c4) ∷
   rw 1 (q318 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q319 : Ws → Eqn
  q319 c4 = eqn (Sw34 ∷ Bx1-0423 ∷ []) (Bx1-0324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0423⟩ (lit c4))
  q320 : Ws → Eqn
  q320 c4 = eqn (CS03⁻ ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ CS03⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨2·0134⟩-at132132 c4)
  q321 : Ws → Eqn
  q321 c4 = eqn (Sw34 ∷ Bx1-0324 ∷ []) (Bx1-0423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0324⟩ (lit c4))
  q322 : Ws → Eqn
  q322 c4 = eqn (Sw34 ∷ CS03⁻ ∷ []) (CS04⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd03 (lit c4))

-- auto CSd01 | BOX(2;0134) @14213243: 7 steps
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at14213243 : Ws → ⟪ (CS04⁻ ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at14213243 c4 = derive (CS04⁻ ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CS04⁻ ∷ [])
  (rw⁻ 0 (q88 c4) ∷
   rw 1 (q183 c4) ∷
   rw 2 (q319 c4) ∷
   rw 1 (q320 c4) ∷
   rw 0 (q321 c4) ∷
   rw 1 (q322 c4) ∷
   rw 2 (q88 c4) ∷ []) Eq.refl

private
  q323 : Ws → Eqn
  q323 c4 = eqn (CS04⁻ ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CS04⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨2·0134⟩-at14213243 c4)

-- auto CSd01 | BOX(2;0134) @143143: 7 steps
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at143143 : Ws → ⟪ (CS04⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at143143 c4 = derive (CS04⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS04⁻ ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q191 c4) ∷
   rw 2 (q159 c4) ∷
   rw 1 (q323 c4) ∷
   rw 0 (q162 c4) ∷
   rw 1 (q191 c4) ∷
   rw 2 (q53 c4) ∷ []) Eq.refl

private
  q324 : Ws → Eqn
  q324 c4 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (c₁ (S) (Swap ↑))
  q325 : Ws → Eqn
  q325 c4 = eqn (S0 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ S0 ∷ []) (lem-auto-S0-∣-BOX⟨1·0234⟩ c4)

-- auto S0 | BOX(1;0234) @2332: 7 steps
lem-auto-S0-∣-BOX⟨1·0234⟩-at2332 : Ws → ⟪ (S0 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·0234⟩-at2332 c4 = derive (S0 ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ S0 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw⁻ 1 (q324 c4) ∷
   rw 2 (q315 c4) ∷
   rw 1 (q325 c4) ∷
   rw 0 (q317 c4) ∷
   rw⁻ 1 (q324 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q326 : Ws → Eqn
  q326 c4 = eqn (S0 ∷ Sw34 ∷ []) (Sw34 ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑))
  q327 : Ws → Eqn
  q327 c4 = eqn (S0 ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ S0 ∷ []) (lem-auto-S0-∣-BOX⟨1·0234⟩-at2332 c4)

-- auto S0 | BOX(1;0234) @243243: 7 steps
lem-auto-S0-∣-BOX⟨1·0234⟩-at243243 : Ws → ⟪ (S0 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·0234⟩-at243243 c4 = derive (S0 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ S0 ∷ [])
  (rw⁻ 0 (q88 c4) ∷
   rw⁻ 1 (q326 c4) ∷
   rw 2 (q319 c4) ∷
   rw 1 (q327 c4) ∷
   rw 0 (q321 c4) ∷
   rw⁻ 1 (q326 c4) ∷
   rw 2 (q88 c4) ∷ []) Eq.refl

private
  q328 : Ws → Eqn
  q328 c4 = eqn (S0 ∷ Sw12 ∷ []) (Sw12 ∷ S0 ∷ []) (c₁ (S) (Swap))
  q329 : Ws → Eqn
  q329 c4 = eqn (S0 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ S0 ∷ []) (lem-auto-S0-∣-BOX⟨1·0234⟩-at243243 c4)

-- auto S0 | BOX(1;0234) @12243143: 7 steps
lem-auto-S0-∣-BOX⟨1·0234⟩-at12243143 : Ws → ⟪ (S0 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·0234⟩-at12243143 c4 = derive (S0 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ S0 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw⁻ 1 (q328 c4) ∷
   rw 2 (q159 c4) ∷
   rw 1 (q329 c4) ∷
   rw 0 (q162 c4) ∷
   rw⁻ 1 (q328 c4) ∷
   rw 2 (q53 c4) ∷ []) Eq.refl

private
  q330 : Ws → Eqn
  q330 c4 = eqn (CCZ123 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ []) (wl0103 (lit c4))
  q331 : Ws → Eqn
  q331 c4 = eqn (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at12243143 c4)
  q332 : Ws → Eqn
  q332 c4 = eqn (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ []) (wl0003 (lit c4))

-- auto CCZ012 | CCZ314 @0112243043: 7 steps
lem-auto-CCZ012-∣-CCZ314-at0112243043 : Ws → ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ314-at0112243043 c4 = derive (CCZ124 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q252 c4) ∷
   rw⁻ 2 (q330 c4) ∷
   rw 1 (q331 c4) ∷
   rw⁻ 0 (q332 c4) ∷
   rw 1 (q254 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q333 : Ws → Eqn
  q333 c4 = eqn (Sb0-1-32-4 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at2332 c4)

-- auto SBOX(0;1;23;4) | CCZ023 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at243243 c4 = derive (Sb0-1-42-3 ∷ CCZ024 ∷ []) (CCZ024 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q88 c4) ∷
   rw 1 (q164 c4) ∷
   rw 2 (q249 c4) ∷
   rw 1 (q333 c4) ∷
   rw 0 (q251 c4) ∷
   rw 1 (q166 c4) ∷
   rw 2 (q88 c4) ∷ []) Eq.refl

private
  q334 : Ws → Eqn
  q334 c4 = eqn (Sb0-1-42-3 ∷ CCZ024 ∷ []) (CCZ024 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at243243 c4)

-- auto SBOX(0;1;23;4) | CCZ023 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at0110243243 c4 = derive (Sb1-0-42-3 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q167 c4) ∷
   rw 2 (q252 c4) ∷
   rw 1 (q334 c4) ∷
   rw 0 (q254 c4) ∷
   rw 1 (q169 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q335 : Ws → Eqn
  q335 c4 = eqn (Sb1-0-42-3 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at0110243243 c4)

-- auto SBOX(0;1;23;4) | CCZ023 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at0210243143 c4 = derive (Sb2-0-41-3 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw 1 (q170 c4) ∷
   rw⁻ 2 (q255 c4) ∷
   rw 1 (q335 c4) ∷
   rw⁻ 0 (q255 c4) ∷
   rw 1 (q173 c4) ∷
   rw 2 (q53 c4) ∷ []) Eq.refl

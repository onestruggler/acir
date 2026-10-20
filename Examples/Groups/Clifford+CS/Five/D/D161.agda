{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D161 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0011 ; wl0012 ; wl0015 ; wl0016 ; wl0034 ; wl0035 ; wl0036 ; wl0037 ; wl0038 ; wl0039 ; wl0044 ; wl0047 ; wl0078 ; wl0084 ; wl0085 ; wl0086 ; wl0091 ; wl0096 ; wl0097 ; wl0099 ; wl0110 ; wl0111 ; wl0113 ; wl0116 ; wl0132 ; wl0133 ; wl0138 ; wl0139 ; wl0154 ; wl0155 ; wl0183 ; wl0212 ; wl0230 ; wl0244 ; wl0269 ; wl0332 ; wl0360 ; wl0596 ; wl0597 ; wl0598 ; wl0599 ; wl0600 ; wl0601 ; wl0602 ; wl0603 ; wl0604 ; wl0605 ; wl0606 ; wl0607 ; wl0608 ; wl0609 ; wl0610 ; wl0611 ; wl0612 ; wl0613 ; wl0614 ; wp0025 ; wp0118 ; wp0120 ; wp0260 ; wp0261 ; wp0262 ; wp0263 ; wp0264 ; wp0265)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0 ; lem-T-beta ; lem-T312-beta ; lem-T312-beta-at0314203142 ; lem-T312-beta-at0314213240 ; lem-c124-beta-at3443 ; lem-sym12 ; lem-sym12-at0314203142 ; lem-sym12-at1221 ; lem-sym12-at132132 ; lem-sym23 ; lem-sym23-at0314203142 ; lem-sym23-at0314213042 ; lem-sym23-at1221 ; lem-sym34 ; lem-sym34-at0314213042 ; lem-sym34-at0314213240 ; lem-sym34-at1221 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-Cz-beta-at12243143 ; lem-Cz-beta-at13243142 ; lem-SB2 ; lem-T312-beta-at2332 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 ; lem-beta-T-at03102132 ; lem-sym12-at233442 ; lem-sym23-at011220 ; lem-sym23-at01122330 ; lem-sym23-at12213443 ; lem-sym23-at122331 ; lem-sym23-at12243143 ; lem-sym23-at13213442 ; lem-sym23-at13243142 ; lem-sym23-at2332 ; lem-sym34-at12213443 ; lem-sym34-at122331 ; lem-sym34-at12233441 ; lem-sym34-at13213442 ; lem-sym34-at2332 ; lem-sym34-at233442)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F0-at1221 ; lem-F0-at3443 ; lem-SBsym-at0113203442 ; lem-T312-beta-at233442 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ134 ; lem-sym12-at13213442)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-CS20-beta-ci-at2332 ; lem-auto-BOX⟨0·1234⟩-∣-CS42 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-CS20-beta-c-at011220 ; lem-CS20-beta-ci-at011220)
open import Examples.Groups.Clifford+CS.Five.D.D089 using (lem-CSd12-beta-at12243143 ; lem-sym12-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-sym34-at0310243142 ; lem-sym34-at0310243241)
open import Examples.Groups.Clifford+CS.Five.D.D160 using (lem-F0-at0112203443 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ241 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ243 ; lem-sym12-at0410233142 ; lem-sym12-at0413203142 ; lem-sym23-at0413203142 ; lem-sym23-at0413213042 ; lem-sym23-at04233240 ; lem-sym23-at0440)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF024 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF301 ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF201 ; lem-nat-3-BOX⟨0·1324⟩ ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-BOX⟨3·4102⟩ ; lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF403 ; lem-nat-1-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-BOX⟨3·4012⟩ ; lem-nat-0-BOX⟨3·4021⟩ ; lem-nat-0-BOX⟨3·4120⟩ ; lem-nat-0-TOFF204 ; lem-nat-0-TOFF413 ; lem-nat-1-BOX⟨0·1234⟩ ; lem-nat-1-BOX⟨0·1324⟩ ; lem-nat-1-BOX⟨3·4012⟩ ; lem-nat-1-BOX⟨3·4021⟩ ; lem-nat-2-TOFF104 ; lem-nat-3-TOFF214 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-0-TOFF401 ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-1-TOFF401 ; lem-nat-2-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨2·0314⟩ ; lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0124⟩ ; lem-nat-2-BOX⟨3·0214⟩ ; lem-nat-2-BOX⟨3·0412⟩ ; lem-nat-2-CCZ014 ; lem-nat-2-TOFF402 ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-BOX⟨0·1342⟩ ; lem-nat-1-BOX⟨0·2341⟩ ; lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-1-BOX⟨3·0412⟩ ; lem-nat-1-CSd02 ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-2-CS02 ; lem-nat-2-CSd02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-2-TOFF403 ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨4·0231⟩ ; lem-nat-1-BOX⟨4·0312⟩ ; lem-nat-1-CSd01 ; lem-nat-3-BOX⟨3·0124⟩ ; lem-nat-3-BOX⟨4·0123⟩ ; lem-nat-3-SBOX⟨2·0·31·4⟩ ; lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨2·0314⟩ ; lem-nat-0-BOX⟨2·1304⟩ ; lem-nat-0-BOX⟨4·1230⟩ ; lem-nat-1-BOX⟨4·0132⟩ ; lem-nat-1-BOX⟨4·0231⟩ ; lem-nat-1-TOFF402 ; lem-nat-2-BOX⟨4·0123⟩ ; lem-nat-2-BOX⟨4·0132⟩ ; lem-nat-2-CS03 ; lem-nat-2-CSd03 ; lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-TOFF124 ; lem-nat-1-BOX⟨1·3240⟩ ; lem-nat-1-BOX⟨2·3140⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-BOX⟨3·0412⟩ ; lem-nat-0-BOX⟨3·4210⟩ ; lem-nat-1-BOX⟨0·3214⟩ ; lem-nat-1-BOX⟨3·4120⟩ ; lem-nat-1-SBOX⟨2·4·1·0⟩ ; lem-nat-2-SBOX⟨3·4·1·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-BOX⟨4·0321⟩ ; lem-nat-0-BOX⟨4·1023⟩ ; lem-nat-0-BOX⟨4·1320⟩ ; lem-nat-0-BOX⟨4·3102⟩ ; lem-nat-1-BOX⟨0·3241⟩ ; lem-nat-1-BOX⟨1·2304⟩ ; lem-nat-1-BOX⟨2·1304⟩ ; lem-nat-1-BOX⟨3·0421⟩ ; lem-nat-1-BOX⟨3·4102⟩ ; lem-nat-1-BOX⟨3·4201⟩ ; lem-nat-1-BOX⟨4·0123⟩ ; lem-nat-1-BOX⟨4·0213⟩ ; lem-nat-1-BOX⟨4·0321⟩ ; lem-nat-1-BOX⟨4·2013⟩ ; lem-nat-2-BOX⟨4·0213⟩ ; lem-nat-2-BOX⟨4·0312⟩ ; lem-nat-2-BOX⟨4·3012⟩ ; lem-nat-2-SBOX⟨2·4·1·0⟩ ; lem-nat-3-BOX⟨3·0214⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨0·3241⟩ ; lem-nat-0-BOX⟨1·3240⟩ ; lem-nat-0-BOX⟨3·0421⟩ ; lem-nat-0-BOX⟨3·1402⟩ ; lem-nat-0-BOX⟨3·1420⟩ ; lem-nat-0-BOX⟨3·4201⟩ ; lem-nat-0-SBOX⟨0·4·2·1⟩ ; lem-nat-0-SBOX⟨1·4·2·0⟩ ; lem-nat-0-SBOX⟨3·0·42·1⟩ ; lem-nat-0-SBOX⟨4·0·3·1⟩ ; lem-nat-0-SBOX⟨4·1·3·0⟩ ; lem-nat-1-BOX⟨0·3142⟩ ; lem-nat-1-BOX⟨4·1230⟩ ; lem-nat-1-BOX⟨4·2130⟩ ; lem-nat-1-SBOX⟨1·4·2·0⟩ ; lem-nat-1-SBOX⟨4·1·3·0⟩ ; lem-nat-1-SBOX⟨4·2·3·0⟩ ; lem-nat-1-SBOX⟨4·3·1·0⟩ ; lem-nat-1-SBOX⟨4·3·2·0⟩ ; lem-nat-2-BOX⟨2·3140⟩ ; lem-nat-2-BOX⟨3·2140⟩ ; lem-nat-2-BOX⟨4·1230⟩ ; lem-nat-2-BOX⟨4·1320⟩ ; lem-nat-2-SBOX⟨2·0·31·4⟩ ; lem-nat-2-SBOX⟨3·0·21·4⟩ ; lem-nat-2-SBOX⟨4·0·31·2⟩ ; lem-nat-2-SBOX⟨4·2·3·0⟩ ; lem-nat-2-SBOX⟨4·3·2·0⟩ ; lem-nat-2-SBOXd⟨4·0·2·1⟩ ; lem-nat-2-SBOXd⟨4·0·3·1⟩ ; lem-nat-3-BOX⟨3·2140⟩ ; lem-nat-3-BOX⟨4·0213⟩ ; lem-nat-3-BOX⟨4·2130⟩ ; lem-nat-3-SBOX⟨2·0·41·3⟩ ; lem-nat-3-SBOX⟨3·4·1·0⟩ ; lem-nat-3-SBOX⟨4·3·1·0⟩)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CS24⁻ ∷ []) (CS24⁻ ∷ []) (wl0596 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Bx0-1234 ∷ []) (Bx0-2134 ∷ []) (lem-sym12 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx0-2134 ∷ []) (Bx0-2143 ∷ []) (lem-sym34-at1221 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Bx0-2143 ∷ []) (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (CS24⁻ ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ CS24⁻ ∷ []) (lem-CSd12-beta-at12243143 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Bx0-2413 ∷ []) (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (Bx0-2143 ∷ []) (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (Bx0-2134 ∷ []) (Bx0-1234 ∷ []) (lem-sym12-at1221 c4)

-- auto BOX(0;1234) | CSd42: 9 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd42 : Ws → ⟪ (Bx0-1234 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd42 c4 = derive (Bx0-1234 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Bx0-1234 ∷ [])
  (rw 1 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw 0 (q3 c4) ∷
   rw 0 (q4 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw 1 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   rw 0 (q1 c4) ∷ []) Eq.refl

private
  q9 : Ws → Eqn
  q9 c4 = eqn (CS14⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS14⁻ ∷ []) (wl0597 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (CS24⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS24⁻ ∷ []) (wl0598 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Bx0-1234 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd42 c4)

-- auto SBOX(0;1;23;4) | CSd42: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42 : Ws → ⟪ (Sb0-1-23-4 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42 c4 = derive (Sb0-1-23-4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw 4 (q9 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw⁻ 1 (q10 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw 0 (q11 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (Sw23 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0015 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (Sb0-1-23-4 ∷ CS24 ∷ []) (CS24 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0011 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (Sw23 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | CS42 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42-at2332 c4 = derive (Sb0-1-32-4 ∷ CS34 ∷ []) (CS34 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q13 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 1 (q15 c4) ∷
   rw⁻ 0 (q16 c4) ∷
   rw 1 (q17 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q18 : Ws → Eqn
  q18 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl0016 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Sb0-1-23-4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl0012 (lit c4))

-- auto SBOX(0;1;23;4) | CSd42 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42-at2332 c4 = derive (Sb0-1-32-4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q13 c4) ∷
   rw⁻ 2 (q18 c4) ∷
   rw 1 (q19 c4) ∷
   rw⁻ 0 (q20 c4) ∷
   rw 1 (q17 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q21 : Ws → Eqn
  q21 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (Sw34 ∷ Bx4-0123 ∷ []) (Bx3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0123⟩ (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Bx3-0124 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-beta-T-at03102132 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (Sw34 ∷ Toff301 ∷ []) (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ234 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ234 ∷ []) (wl0155 (lit c4))

-- beta-T @0410213243: 8 steps
lem-beta-T-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) ⟫ʷ
lem-beta-T-at0410213243 c4 = derive (Bx4-0123 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   rw 1 (q23 c4) ∷
   rw 0 (q24 c4) ∷
   rw⁻ 1 (q25 c4) ∷
   rw 2 (q24 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   rw 4 (q21 c4) ∷ []) Eq.refl

private
  q26 : Ws → Eqn
  q26 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (Sw12 ∷ Bx0-3214 ∷ []) (Bx0-3124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3214⟩ (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (Bx0-3124 ∷ []) (Bx0-1324 ∷ []) (lem-sym12-at132132 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (Sw12 ∷ Bx0-1324 ∷ []) (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ (lit c4))

-- sym12 @1331: 5 steps
lem-sym12-at1331 : Ws → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-sym12-at1331 c4 = derive (Bx0-3214 ∷ []) (Bx0-2314 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q27 c4) ∷
   rw 1 (q28 c4) ∷
   rw 0 (q29 c4) ∷
   rw 1 (q26 c4) ∷ []) Eq.refl

-- auto BOX(0;1234) | CSd24: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd24 : Ws → ⟪ (Bx0-1234 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd24 c4 = derive (Bx0-1234 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Bx0-1234 ∷ [])
  (rw 0 (q2 c4) ∷
   rw 0 (q3 c4) ∷
   rw 0 (q4 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw 1 (q7 c4) ∷
   rw 1 (q8 c4) ∷ []) Eq.refl

private
  q30 : Ws → Eqn
  q30 c4 = eqn (CS01⁻ ∷ []) (CS01⁻ ∷ []) (wl0360 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (Bx1-2304 ∷ []) (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CS01⁻ ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CS01⁻ ∷ []) (lem-CS20-beta-ci-at011220 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx1-2034 ∷ []) (Bx1-2304 ∷ []) (lem-sym23-at011220 c4)

-- auto CSd01 | BOX(1;2304): 5 steps
lem-auto-CSd01-∣-BOX⟨1·2304⟩ : Ws → ⟪ (CS01⁻ ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2304⟩ c4 = derive (CS01⁻ ∷ Bx1-2304 ∷ []) (Bx1-2304 ∷ CS01⁻ ∷ [])
  (rw 0 (q30 c4) ∷
   rw 1 (q31 c4) ∷
   rw 0 (q32 c4) ∷
   rw 0 (q33 c4) ∷
   rw 1 (q30 c4) ∷ []) Eq.refl

private
  q34 : Ws → Eqn
  q34 c4 = eqn (Sw12 ∷ CS02⁻ ∷ []) (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (Sw12 ∷ Bx2-1304 ∷ []) (Bx1-2304 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1304⟩ (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CS01⁻ ∷ Bx1-2304 ∷ []) (Bx1-2304 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2304⟩ c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (Sw12 ∷ Bx1-2304 ∷ []) (Bx2-1304 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2304⟩ (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (Sw12 ∷ CS01⁻ ∷ []) (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 (lit c4))

-- auto CSd01 | BOX(1;2304) @1221: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at1221 : Ws → ⟪ (CS02⁻ ∷ Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at1221 c4 = derive (CS02⁻ ∷ Bx2-1304 ∷ []) (Bx2-1304 ∷ CS02⁻ ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q34 c4) ∷
   rw 2 (q35 c4) ∷
   rw 1 (q36 c4) ∷
   rw 0 (q37 c4) ∷
   rw 1 (q38 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wl0036 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (Sw01 ∷ Bx2-0314 ∷ []) (Bx2-1304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0314⟩ (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (CS02⁻ ∷ Bx2-1304 ∷ []) (Bx2-1304 ∷ CS02⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2304⟩-at1221 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (Sw01 ∷ Bx2-1304 ∷ []) (Bx2-0314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1304⟩ (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wl0139 (lit c4))

-- auto CSd01 | BOX(1;2304) @011220: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at011220 : Ws → ⟪ (CS12⁻ ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at011220 c4 = derive (CS12⁻ ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ CS12⁻ ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw⁻ 1 (q40 c4) ∷
   rw 2 (q41 c4) ∷
   rw 1 (q42 c4) ∷
   rw 0 (q43 c4) ∷
   rw⁻ 1 (q44 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q45 : Ws → Eqn
  q45 c4 = eqn (CS12⁻ ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ CS12⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2304⟩-at011220 c4)

-- auto SBOXd(0;1;2;3) | BOX(2;0314): 3 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩ : Ws → ⟪ (Sb⁻0-1-2-3 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩ c4 = derive (Sb⁻0-1-2-3 ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ Sb⁻0-1-2-3 ∷ [])
  (re 0 1 (CS12⁻ ∷ []) ∷
   rw 0 (q45 c4) ∷
   re 1 1 (Sb⁻0-1-2-3 ∷ []) ∷ []) Eq.refl

private
  q46 : Ws → Eqn
  q46 c4 = eqn (Sw12 ∷ Bx0-3241 ∷ []) (Bx0-3142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3241⟩ (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (Bx0-3142 ∷ []) (Bx0-1342 ∷ []) (lem-sym12-at13213442 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (Sw12 ∷ Bx0-1342 ∷ []) (Bx0-2341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1342⟩ (lit c4))

-- sym12 @133441: 5 steps
lem-sym12-at133441 : Ws → ⟪ (Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-sym12-at133441 c4 = derive (Bx0-3241 ∷ []) (Bx0-2341 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q46 c4) ∷
   rw 1 (q47 c4) ∷
   rw 0 (q48 c4) ∷
   rw 1 (q26 c4) ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = eqn (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) (wl0038 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (Sw12 ∷ Bx0-2134 ∷ []) (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (Toff012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Toff012 ∷ []) (lem-T-beta c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (Sw12 ∷ Bx0-1234 ∷ []) (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4))

-- T-beta @1221: 7 steps
lem-T-beta-at1221 : Ws → ⟪ (Toff012 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ Toff012 ∷ []) ⟫ʷ
lem-T-beta-at1221 c4 = derive (Toff012 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ Toff012 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q49 c4) ∷
   rw 2 (q50 c4) ∷
   rw 1 (q51 c4) ∷
   rw 0 (q52 c4) ∷
   rw 1 (q49 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = eqn (Sw12 ∷ Bx0-2341 ∷ []) (Bx0-1342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2341⟩ (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (Bx0-1342 ∷ []) (Bx0-3142 ∷ []) (lem-sym12-at233442 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (Sw12 ∷ Bx0-3142 ∷ []) (Bx0-3241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3142⟩ (lit c4))

-- sym12 @12233441: 5 steps
lem-sym12-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-sym12-at12233441 c4 = derive (Bx0-2341 ∷ []) (Bx0-3241 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q53 c4) ∷
   rw 1 (q54 c4) ∷
   rw 0 (q55 c4) ∷
   rw 1 (q26 c4) ∷ []) Eq.refl

private
  q56 : Ws → Eqn
  q56 c4 = eqn (Toff012 ∷ []) (Toff012 ∷ []) (wl0599 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (Bx0-3241 ∷ []) (Bx0-2341 ∷ []) (lem-sym12-at133441 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (Bx0-2341 ∷ []) (Bx0-2314 ∷ []) (lem-sym34-at12233441 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (Bx0-2314 ∷ []) (Bx0-2134 ∷ []) (lem-sym23-at122331 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (Toff012 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ Toff012 ∷ []) (lem-T-beta-at1221 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (Bx0-2134 ∷ []) (Bx0-2314 ∷ []) (lem-sym23-at1221 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (Bx0-2314 ∷ []) (Bx0-2341 ∷ []) (lem-sym34-at122331 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (Bx0-2341 ∷ []) (Bx0-3241 ∷ []) (lem-sym12-at12233441 c4)

-- auto TOFF012 | BOX(0;3241): 9 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩ : Ws → ⟪ (Toff012 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩ c4 = derive (Toff012 ∷ Bx0-3241 ∷ []) (Bx0-3241 ∷ Toff012 ∷ [])
  (rw 0 (q56 c4) ∷
   rw 1 (q57 c4) ∷
   rw 1 (q58 c4) ∷
   rw 1 (q59 c4) ∷
   rw 0 (q60 c4) ∷
   rw 0 (q61 c4) ∷
   rw 0 (q62 c4) ∷
   rw 0 (q63 c4) ∷
   rw 1 (q56 c4) ∷ []) Eq.refl

private
  q64 : Ws → Eqn
  q64 c4 = eqn (CS01 ∷ []) (CS01 ∷ []) (wl0332 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (CS01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CS01 ∷ []) (lem-CS20-beta-c-at011220 c4)

-- auto CS01 | BOX(1;2304): 5 steps
lem-auto-CS01-∣-BOX⟨1·2304⟩ : Ws → ⟪ (CS01 ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2304⟩ c4 = derive (CS01 ∷ Bx1-2304 ∷ []) (Bx1-2304 ∷ CS01 ∷ [])
  (rw 0 (q64 c4) ∷
   rw 1 (q31 c4) ∷
   rw 0 (q65 c4) ∷
   rw 0 (q33 c4) ∷
   rw 1 (q64 c4) ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = eqn (Sw12 ∷ CS02 ∷ []) (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (CS01 ∷ Bx1-2304 ∷ []) (Bx1-2304 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2304⟩ c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (Sw12 ∷ CS01 ∷ []) (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4))

-- auto CS01 | BOX(1;2304) @1221: 7 steps
lem-auto-CS01-∣-BOX⟨1·2304⟩-at1221 : Ws → ⟪ (CS02 ∷ Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2304⟩-at1221 c4 = derive (CS02 ∷ Bx2-1304 ∷ []) (Bx2-1304 ∷ CS02 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q66 c4) ∷
   rw 2 (q35 c4) ∷
   rw 1 (q67 c4) ∷
   rw 0 (q37 c4) ∷
   rw 1 (q68 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q69 : Ws → Eqn
  q69 c4 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wl0035 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (CS02 ∷ Bx2-1304 ∷ []) (Bx2-1304 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2304⟩-at1221 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wl0138 (lit c4))

-- auto CS01 | BOX(1;2304) @011220: 7 steps
lem-auto-CS01-∣-BOX⟨1·2304⟩-at011220 : Ws → ⟪ (CS12 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ CS12 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2304⟩-at011220 c4 = derive (CS12 ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ CS12 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw⁻ 1 (q69 c4) ∷
   rw 2 (q41 c4) ∷
   rw 1 (q70 c4) ∷
   rw 0 (q43 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = eqn (CS12 ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ CS12 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2304⟩-at011220 c4)

-- auto SBOX(0;1;2;3) | BOX(2;0314): 3 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩ : Ws → ⟪ (Sb0-1-2-3 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩ c4 = derive (Sb0-1-2-3 ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ Sb0-1-2-3 ∷ [])
  (re 0 1 (CS12 ∷ []) ∷
   rw 0 (q72 c4) ∷
   re 1 1 (Sb0-1-2-3 ∷ []) ∷ []) Eq.refl

private
  q73 : Ws → Eqn
  q73 c4 = eqn (CCZ012 ∷ CS34 ∷ []) (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS))

-- auto CCZ012 | CS34: 1 steps
lem-auto-CCZ012-∣-CS34 : Ws → ⟪ (CCZ012 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CS34 c4 = derive (CCZ012 ∷ CS34 ∷ []) (CS34 ∷ CCZ012 ∷ [])
  (rw 0 (q73 c4) ∷ []) Eq.refl

private
  q74 : Ws → Eqn
  q74 c4 = eqn (CCZ012 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (Swap))
  q75 : Ws → Eqn
  q75 c4 = eqn (CS34 ∷ Sw34 ∷ []) (Sw34 ∷ CS34 ∷ []) (wl0039 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (CCZ012 ∷ CS34 ∷ []) (CS34 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CS34 c4)

-- auto CCZ012 | CS34 @3443: 7 steps
lem-auto-CCZ012-∣-CS34-at3443 : Ws → ⟪ (CCZ012 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CS34-at3443 c4 = derive (CCZ012 ∷ CS34 ∷ []) (CS34 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw⁻ 1 (q74 c4) ∷
   rw⁻ 2 (q75 c4) ∷
   rw 1 (q76 c4) ∷
   rw⁻ 0 (q75 c4) ∷
   rw⁻ 1 (q74 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = eqn (CCZ034 ∷ []) (CCZ034 ∷ []) (wp0025 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1324 ∷ []) (lem-sym23 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (Bx0-1324 ∷ []) (Bx0-1342 ∷ []) (lem-sym34-at2332 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (Bx0-3142 ∷ []) (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (CCZ034 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ CCZ034 ∷ []) (lem-Cz-beta-at13243142 c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (Bx0-3412 ∷ []) (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (Bx0-3142 ∷ []) (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (Bx0-1324 ∷ []) (Bx0-1234 ∷ []) (lem-sym23-at2332 c4)

-- auto BOX(0;1234) | CCZ403: 11 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ403 : Ws → ⟪ (Bx0-1234 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ403 c4 = derive (Bx0-1234 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx0-1234 ∷ [])
  (rw 1 (q77 c4) ∷
   rw 0 (q78 c4) ∷
   rw 0 (q79 c4) ∷
   rw 0 (q54 c4) ∷
   rw 0 (q80 c4) ∷
   rw⁻ 0 (q81 c4) ∷
   rw 1 (q82 c4) ∷
   rw 1 (q83 c4) ∷
   rw 1 (q28 c4) ∷
   rw 1 (q84 c4) ∷
   rw 0 (q77 c4) ∷ []) Eq.refl

private
  q85 : Ws → Eqn
  q85 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (wl0600 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (CCZ012 ∷ CS23 ∷ []) (CS23 ∷ CCZ012 ∷ []) (wl0601 (lit c4))
  q87 : Ws → Eqn
  q87 c4 = eqn (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4))
  q88 : Ws → Eqn
  q88 c4 = eqn (CS02 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ []) (CX42 ∷ CS23⁻ ∷ CX42 ∷ CS02 ∷ []) (wp0260 c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (CX21 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ []) (CX42 ∷ CS23⁻ ∷ CX42 ∷ CX21 ∷ []) (wl0603 (lit c4))
  q90 : Ws → Eqn
  q90 c4 = eqn (CS01⁻ ∷ CX42 ∷ []) (CX42 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑ • CX₁₀ • Swap ↑))
  q91 : Ws → Eqn
  q91 c4 = eqn (CS01⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CS • CS • CS))
  q92 : Ws → Eqn
  q92 c4 = eqn (CS01 ∷ CX42 ∷ []) (CX42 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑ • CX₁₀ • Swap ↑))
  q93 : Ws → Eqn
  q93 c4 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (c₂ (CS) (CS • CS • CS))
  q94 : Ws → Eqn
  q94 c4 = eqn (CCZ012 ∷ CS34 ∷ []) (CS34 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CS34-at3443 c4)

-- auto CCZ012 | CCZ342: 15 steps
lem-auto-CCZ012-∣-CCZ342 : Ws → ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342 c4 = derive (CCZ012 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ012 ∷ [])
  (rw 1 (q85 c4) ∷
   rw 0 (q86 c4) ∷
   rw 1 (q87 c4) ∷
   rw 5 (q88 c4) ∷
   rw 4 (q89 c4) ∷
   rw 3 (q90 c4) ∷
   rw 4 (q91 c4) ∷
   rw 5 (q90 c4) ∷
   rw 2 (q89 c4) ∷
   rw 1 (q92 c4) ∷
   rw 2 (q93 c4) ∷
   rw 3 (q92 c4) ∷
   rw⁻ 4 (q87 c4) ∷
   rw 4 (q94 c4) ∷
   rw⁻ 0 (q85 c4) ∷ []) Eq.refl

private
  q95 : Ws → Eqn
  q95 c4 = eqn (CCZ024 ∷ []) (CCZ024 ∷ []) (wp0261 c4)
  q96 : Ws → Eqn
  q96 c4 = eqn (CCZ024 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ CCZ024 ∷ []) (lem-Cz-beta-at12243143 c4)

-- auto BOX(0;1234) | CCZ402: 9 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ402 : Ws → ⟪ (Bx0-1234 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ402 c4 = derive (Bx0-1234 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx0-1234 ∷ [])
  (rw 1 (q95 c4) ∷
   rw 0 (q2 c4) ∷
   rw 0 (q3 c4) ∷
   rw 0 (q4 c4) ∷
   rw⁻ 0 (q96 c4) ∷
   rw 1 (q6 c4) ∷
   rw 1 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   rw 0 (q95 c4) ∷ []) Eq.refl

private
  q97 : Ws → Eqn
  q97 c4 = eqn (CCZ123 ∷ []) (CCZ123 ∷ []) (wl0269 (lit c4))
  q98 : Ws → Eqn
  q98 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1243 ∷ []) (lem-sym34 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (CCZ123 ∷ Bx0-1243 ∷ []) (Bx0-1243 ∷ CCZ123 ∷ []) (lem-c124-beta-at3443 c4)
  q100 : Ws → Eqn
  q100 c4 = eqn (Bx0-1243 ∷ []) (Bx0-1234 ∷ []) (lem-sym34-at3443 c4)

-- auto BOX(0;1234) | CCZ132: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ132 : Ws → ⟪ (Bx0-1234 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ132 c4 = derive (Bx0-1234 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1234 ∷ [])
  (rw 1 (q97 c4) ∷
   rw 0 (q98 c4) ∷
   rw⁻ 0 (q99 c4) ∷
   rw 1 (q100 c4) ∷
   rw 0 (q97 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = eqn (Sw01 ∷ Bx4-1023 ∷ []) (Bx4-0123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1023⟩ (lit c4))
  q102 : Ws → Eqn
  q102 c4 = eqn (Bx4-0123 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-beta-T-at0410213243 c4)
  q103 : Ws → Eqn
  q103 c4 = eqn (Sw01 ∷ Toff401 ∷ []) (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 (lit c4))
  q104 : Ws → Eqn
  q104 c4 = eqn (Sw01 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ))

-- beta-T @04203243: 8 steps
lem-beta-T-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) ⟫ʷ
lem-beta-T-at04203243 c4 = derive (Bx4-1023 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q101 c4) ∷
   rw 1 (q102 c4) ∷
   rw 0 (q103 c4) ∷
   rw 1 (q104 c4) ∷
   rw 2 (q103 c4) ∷
   rw 3 (q104 c4) ∷
   rw 4 (q39 c4) ∷ []) Eq.refl

private
  q105 : Ws → Eqn
  q105 c4 = eqn (Sw12 ∷ Bx4-2013 ∷ []) (Bx4-1023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·2013⟩ (lit c4))
  q106 : Ws → Eqn
  q106 c4 = eqn (Bx4-1023 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-beta-T-at04203243 c4)
  q107 : Ws → Eqn
  q107 c4 = eqn (Sw12 ∷ Toff401 ∷ []) (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 (lit c4))
  q108 : Ws → Eqn
  q108 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 (lit c4))

-- beta-T @0412203143: 8 steps
lem-beta-T-at0412203143 : Ws → ⟪ (Bx4-2013 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) ⟫ʷ
lem-beta-T-at0412203143 c4 = derive (Bx4-2013 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q105 c4) ∷
   rw 1 (q106 c4) ∷
   rw 0 (q107 c4) ∷
   rw⁻ 1 (q108 c4) ∷
   rw 2 (q107 c4) ∷
   rw⁻ 3 (q108 c4) ∷
   rw 4 (q26 c4) ∷ []) Eq.refl

private
  q109 : Ws → Eqn
  q109 c4 = eqn (Sw23 ∷ Bx4-3012 ∷ []) (Bx4-2013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·3012⟩ (lit c4))
  q110 : Ws → Eqn
  q110 c4 = eqn (Bx4-2013 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-beta-T-at0412203143 c4)
  q111 : Ws → Eqn
  q111 c4 = eqn (Sw23 ∷ Toff402 ∷ []) (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 (lit c4))
  q112 : Ws → Eqn
  q112 c4 = eqn (Sw23 ∷ CCZ134 ∷ []) (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4))

-- beta-T @0413203142: 8 steps
lem-beta-T-at0413203142 : Ws → ⟪ (Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) ⟫ʷ
lem-beta-T-at0413203142 c4 = derive (Bx4-3012 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q109 c4) ∷
   rw 1 (q110 c4) ∷
   rw 0 (q111 c4) ∷
   rw 1 (q112 c4) ∷
   rw 2 (q111 c4) ∷
   rw 3 (q112 c4) ∷
   rw 4 (q12 c4) ∷ []) Eq.refl

private
  q113 : Ws → Eqn
  q113 c4 = eqn (Sw01 ∷ Bx4-3102 ∷ []) (Bx4-3012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·3102⟩ (lit c4))
  q114 : Ws → Eqn
  q114 c4 = eqn (Bx4-3012 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) (lem-beta-T-at0413203142 c4)
  q115 : Ws → Eqn
  q115 c4 = eqn (Sw01 ∷ Toff403 ∷ []) (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 (lit c4))
  q116 : Ws → Eqn
  q116 c4 = eqn (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4))

-- beta-T @0413213042: 8 steps
lem-beta-T-at0413213042 : Ws → ⟪ (Bx4-3102 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) ⟫ʷ
lem-beta-T-at0413213042 c4 = derive (Bx4-3102 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q113 c4) ∷
   rw 1 (q114 c4) ∷
   rw 0 (q115 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q115 c4) ∷
   rw 3 (q116 c4) ∷
   rw 4 (q39 c4) ∷ []) Eq.refl

private
  q117 : Ws → Eqn
  q117 c4 = eqn (CCZ012 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ012 ∷ []) (wl0096 (lit c4))
  q118 : Ws → Eqn
  q118 c4 = eqn (CCZ012 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ342 c4)

-- auto CCZ012 | CCZ342 @0110: 7 steps
lem-auto-CCZ012-∣-CCZ342-at0110 : Ws → ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at0110 c4 = derive (CCZ012 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw⁻ 1 (q117 c4) ∷
   rw 2 (q104 c4) ∷
   rw 1 (q118 c4) ∷
   rw 0 (q104 c4) ∷
   rw⁻ 1 (q117 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q119 : Ws → Eqn
  q119 c4 = eqn (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ []) (wl0037 (lit c4))
  q120 : Ws → Eqn
  q120 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl0084 (lit c4))
  q121 : Ws → Eqn
  q121 c4 = eqn (CCZ012 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0110 c4)

-- auto CCZ012 | CCZ342 @021021: 7 steps
lem-auto-CCZ012-∣-CCZ342-at021021 : Ws → ⟪ (CCZ012 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at021021 c4 = derive (CCZ012 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw⁻ 1 (q119 c4) ∷
   rw⁻ 2 (q120 c4) ∷
   rw 1 (q121 c4) ∷
   rw⁻ 0 (q108 c4) ∷
   rw⁻ 1 (q119 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q122 : Ws → Eqn
  q122 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4))
  q123 : Ws → Eqn
  q123 c4 = eqn (Sw23 ∷ CCZ124 ∷ []) (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4))
  q124 : Ws → Eqn
  q124 c4 = eqn (CCZ012 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at021021 c4)
  q125 : Ws → Eqn
  q125 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4))

-- auto CCZ012 | CCZ342 @03102132: 7 steps
lem-auto-CCZ012-∣-CCZ342-at03102132 : Ws → ⟪ (CCZ013 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at03102132 c4 = derive (CCZ013 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q122 c4) ∷
   rw 2 (q123 c4) ∷
   rw 1 (q124 c4) ∷
   rw 0 (q112 c4) ∷
   rw 1 (q125 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = eqn (Sw34 ∷ CCZ014 ∷ []) (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 (lit c4))
  q127 : Ws → Eqn
  q127 c4 = eqn (Sw34 ∷ CCZ123 ∷ []) (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 (lit c4))
  q128 : Ws → Eqn
  q128 c4 = eqn (CCZ013 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at03102132 c4)
  q129 : Ws → Eqn
  q129 c4 = eqn (Sw34 ∷ CCZ124 ∷ []) (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 (lit c4))
  q130 : Ws → Eqn
  q130 c4 = eqn (Sw34 ∷ CCZ013 ∷ []) (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 (lit c4))

-- auto CCZ012 | CCZ342 @0410213243: 7 steps
lem-auto-CCZ012-∣-CCZ342-at0410213243 : Ws → ⟪ (CCZ014 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at0410213243 c4 = derive (CCZ014 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q126 c4) ∷
   rw 2 (q127 c4) ∷
   rw 1 (q128 c4) ∷
   rw 0 (q129 c4) ∷
   rw 1 (q130 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q131 : Ws → Eqn
  q131 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4))
  q132 : Ws → Eqn
  q132 c4 = eqn (CCZ123 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ123 ∷ []) (wl0111 (lit c4))
  q133 : Ws → Eqn
  q133 c4 = eqn (CCZ014 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0410213243 c4)
  q134 : Ws → Eqn
  q134 c4 = eqn (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4))

-- auto CCZ012 | CCZ342 @04103143: 7 steps
lem-auto-CCZ012-∣-CCZ342-at04103143 : Ws → ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at04103143 c4 = derive (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q131 c4) ∷
   rw⁻ 2 (q132 c4) ∷
   rw 1 (q133 c4) ∷
   rw⁻ 0 (q132 c4) ∷
   rw 1 (q134 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q135 : Ws → Eqn
  q135 c4 = eqn (Bx4-0312 ∷ []) (Bx4-3012 ∷ []) (lem-sym12-at0410233142 c4)
  q136 : Ws → Eqn
  q136 c4 = eqn (Bx4-3012 ∷ []) (Bx4-3102 ∷ []) (lem-sym23-at0413203142 c4)
  q137 : Ws → Eqn
  q137 c4 = eqn (Bx4-3102 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-beta-T-at0413213042 c4)
  q138 : Ws → Eqn
  q138 c4 = eqn (Toff413 ∷ Toff413 ∷ []) [] (wl0604 (lit c4))
  q139 : Ws → Eqn
  q139 c4 = eqn (Toff413 ∷ []) (Toff413 ∷ []) (wl0605 (lit c4))
  q140 : Ws → Eqn
  q140 c4 = eqn (Toff413 ∷ Bx0-1342 ∷ Toff413 ∷ []) (Bx0-1342 ∷ CCZ123 ∷ []) (lem-T312-beta-at233442 c4)
  q141 : Ws → Eqn
  q141 c4 = eqn (Bx0-1342 ∷ []) (Bx0-1324 ∷ []) (lem-sym34-at233442 c4)
  q142 : Ws → Eqn
  q142 c4 = eqn (Bx0-1234 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ132 c4)
  q143 : Ws → Eqn
  q143 c4 = eqn (Bx0-1234 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ402 c4)
  q144 : Ws → Eqn
  q144 c4 = eqn (CCZ123 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ123 ∷ []) (wl0606 (lit c4))
  q145 : Ws → Eqn
  q145 c4 = eqn (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at04103143 c4)
  q146 : Ws → Eqn
  q146 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl0212 (lit c4))
  q147 : Ws → Eqn
  q147 c4 = eqn (Bx4-3102 ∷ []) (Bx4-3012 ∷ []) (lem-sym23-at0413213042 c4)
  q148 : Ws → Eqn
  q148 c4 = eqn (Bx4-3012 ∷ []) (Bx4-0312 ∷ []) (lem-sym12-at0413203142 c4)

-- auto BOX(0;1234) | BOX(4;0312): 31 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·0312⟩ : Ws → ⟪ (Bx0-1234 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·0312⟩ c4 = derive (Bx0-1234 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Bx0-1234 ∷ [])
  (rw 1 (q135 c4) ∷
   rw 1 (q136 c4) ∷
   rw 1 (q137 c4) ∷
   rw⁻ 0 (q138 c4) ∷
   rw 1 (q139 c4) ∷
   rw 3 (q139 c4) ∷
   rw 2 (q78 c4) ∷
   rw 2 (q79 c4) ∷
   rw 1 (q140 c4) ∷
   rw 1 (q141 c4) ∷
   rw 1 (q84 c4) ∷
   rw 1 (q142 c4) ∷
   rw 2 (q143 c4) ∷
   rw⁻ 3 (q138 c4) ∷
   rw 4 (q139 c4) ∷
   rw 6 (q139 c4) ∷
   rw 5 (q78 c4) ∷
   rw 5 (q79 c4) ∷
   rw 4 (q140 c4) ∷
   rw 4 (q141 c4) ∷
   rw 4 (q84 c4) ∷
   rw 4 (q142 c4) ∷
   rw 5 (q143 c4) ∷
   rw⁻ 0 (q144 c4) ∷
   rw⁻ 3 (q144 c4) ∷
   rw 2 (q145 c4) ∷
   rw⁻ 1 (q144 c4) ∷
   rw 0 (q146 c4) ∷
   rw⁻ 0 (q137 c4) ∷
   rw 0 (q147 c4) ∷
   rw 0 (q148 c4) ∷ []) Eq.refl

private
  q149 : Ws → Eqn
  q149 c4 = eqn (Sw23 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ (lit c4))
  q150 : Ws → Eqn
  q150 c4 = eqn (Sw23 ∷ Bx3-0214 ∷ []) (Bx2-0314 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0214⟩ (lit c4))
  q151 : Ws → Eqn
  q151 c4 = eqn (Sb⁻0-1-2-3 ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩ c4)
  q152 : Ws → Eqn
  q152 c4 = eqn (Sw23 ∷ Bx2-0314 ∷ []) (Bx3-0214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0314⟩ (lit c4))
  q153 : Ws → Eqn
  q153 c4 = eqn (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ (lit c4))

-- auto SBOXd(0;1;2;3) | BOX(2;0314) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2332 : Ws → ⟪ (Sb⁻0-1-3-2 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2332 c4 = derive (Sb⁻0-1-3-2 ∷ Bx3-0214 ∷ []) (Bx3-0214 ∷ Sb⁻0-1-3-2 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q149 c4) ∷
   rw 2 (q150 c4) ∷
   rw 1 (q151 c4) ∷
   rw 0 (q152 c4) ∷
   rw 1 (q153 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q154 : Ws → Eqn
  q154 c4 = eqn (Sw34 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ (lit c4))
  q155 : Ws → Eqn
  q155 c4 = eqn (Sw34 ∷ Bx4-0213 ∷ []) (Bx3-0214 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0213⟩ (lit c4))
  q156 : Ws → Eqn
  q156 c4 = eqn (Sb⁻0-1-3-2 ∷ Bx3-0214 ∷ []) (Bx3-0214 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2332 c4)
  q157 : Ws → Eqn
  q157 c4 = eqn (Sw34 ∷ Bx3-0214 ∷ []) (Bx4-0213 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0214⟩ (lit c4))
  q158 : Ws → Eqn
  q158 c4 = eqn (Sw34 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ (lit c4))

-- auto SBOXd(0;1;2;3) | BOX(2;0314) @243243: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at243243 : Ws → ⟪ (Sb⁻0-1-4-2 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at243243 c4 = derive (Sb⁻0-1-4-2 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Sb⁻0-1-4-2 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q154 c4) ∷
   rw 2 (q155 c4) ∷
   rw 1 (q156 c4) ∷
   rw 0 (q157 c4) ∷
   rw 1 (q158 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q159 : Ws → Eqn
  q159 c4 = eqn (Sw23 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ (lit c4))
  q160 : Ws → Eqn
  q160 c4 = eqn (Sw23 ∷ Bx4-0312 ∷ []) (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ (lit c4))
  q161 : Ws → Eqn
  q161 c4 = eqn (Sb⁻0-1-4-2 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Sb⁻0-1-4-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at243243 c4)
  q162 : Ws → Eqn
  q162 c4 = eqn (Sw23 ∷ Bx4-0213 ∷ []) (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ (lit c4))
  q163 : Ws → Eqn
  q163 c4 = eqn (Sw23 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ (lit c4))

-- auto SBOXd(0;1;2;3) | BOX(2;0314) @2442: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2442 : Ws → ⟪ (Sb⁻0-1-4-3 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2442 c4 = derive (Sb⁻0-1-4-3 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Sb⁻0-1-4-3 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q159 c4) ∷
   rw 2 (q160 c4) ∷
   rw 1 (q161 c4) ∷
   rw 0 (q162 c4) ∷
   rw 1 (q163 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q164 : Ws → Eqn
  q164 c4 = eqn (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) (wl0097 (lit c4))
  q165 : Ws → Eqn
  q165 c4 = eqn (Sw01 ∷ Bx1-3240 ∷ []) (Bx0-3241 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3240⟩ (lit c4))
  q166 : Ws → Eqn
  q166 c4 = eqn (Toff012 ∷ Bx0-3241 ∷ []) (Bx0-3241 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩ c4)
  q167 : Ws → Eqn
  q167 c4 = eqn (Sw01 ∷ Bx0-3241 ∷ []) (Bx1-3240 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3241⟩ (lit c4))
  q168 : Ws → Eqn
  q168 c4 = eqn (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) (wl0099 (lit c4))

-- auto TOFF012 | BOX(0;3241) @0110: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0110 : Ws → ⟪ (Toff102 ∷ Bx1-3240 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3240 ∷ Toff102 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0110 c4 = derive (Toff102 ∷ Bx1-3240 ∷ []) (Bx1-3240 ∷ Toff102 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q164 c4) ∷
   rw 2 (q165 c4) ∷
   rw 1 (q166 c4) ∷
   rw 0 (q167 c4) ∷
   rw 1 (q168 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q169 : Ws → Eqn
  q169 c4 = eqn (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) (wl0044 (lit c4))
  q170 : Ws → Eqn
  q170 c4 = eqn (Sw12 ∷ Bx2-3140 ∷ []) (Bx1-3240 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3140⟩ (lit c4))
  q171 : Ws → Eqn
  q171 c4 = eqn (Toff102 ∷ Bx1-3240 ∷ []) (Bx1-3240 ∷ Toff102 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0110 c4)
  q172 : Ws → Eqn
  q172 c4 = eqn (Sw12 ∷ Bx1-3240 ∷ []) (Bx2-3140 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3240⟩ (lit c4))
  q173 : Ws → Eqn
  q173 c4 = eqn (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) (wl0047 (lit c4))

-- auto TOFF012 | BOX(0;3241) @021021: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at021021 : Ws → ⟪ (Toff201 ∷ Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ Toff201 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at021021 c4 = derive (Toff201 ∷ Bx2-3140 ∷ []) (Bx2-3140 ∷ Toff201 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q169 c4) ∷
   rw 2 (q170 c4) ∷
   rw 1 (q171 c4) ∷
   rw 0 (q172 c4) ∷
   rw 1 (q173 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q174 : Ws → Eqn
  q174 c4 = eqn (Sw23 ∷ Toff301 ∷ []) (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 (lit c4))
  q175 : Ws → Eqn
  q175 c4 = eqn (Sw23 ∷ Bx3-2140 ∷ []) (Bx2-3140 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·2140⟩ (lit c4))
  q176 : Ws → Eqn
  q176 c4 = eqn (Toff201 ∷ Bx2-3140 ∷ []) (Bx2-3140 ∷ Toff201 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at021021 c4)
  q177 : Ws → Eqn
  q177 c4 = eqn (Sw23 ∷ Bx2-3140 ∷ []) (Bx3-2140 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·3140⟩ (lit c4))
  q178 : Ws → Eqn
  q178 c4 = eqn (Sw23 ∷ Toff201 ∷ []) (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 (lit c4))

-- auto TOFF012 | BOX(0;3241) @03102132: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at03102132 : Ws → ⟪ (Toff301 ∷ Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ Toff301 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at03102132 c4 = derive (Toff301 ∷ Bx3-2140 ∷ []) (Bx3-2140 ∷ Toff301 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q174 c4) ∷
   rw 2 (q175 c4) ∷
   rw 1 (q176 c4) ∷
   rw 0 (q177 c4) ∷
   rw 1 (q178 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q179 : Ws → Eqn
  q179 c4 = eqn (Sw34 ∷ Toff401 ∷ []) (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 (lit c4))
  q180 : Ws → Eqn
  q180 c4 = eqn (Sw34 ∷ Bx4-2130 ∷ []) (Bx3-2140 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·2130⟩ (lit c4))
  q181 : Ws → Eqn
  q181 c4 = eqn (Toff301 ∷ Bx3-2140 ∷ []) (Bx3-2140 ∷ Toff301 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at03102132 c4)
  q182 : Ws → Eqn
  q182 c4 = eqn (Sw34 ∷ Bx3-2140 ∷ []) (Bx4-2130 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·2140⟩ (lit c4))

-- auto TOFF012 | BOX(0;3241) @0410213243: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0410213243 : Ws → ⟪ (Toff401 ∷ Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ Toff401 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0410213243 c4 = derive (Toff401 ∷ Bx4-2130 ∷ []) (Bx4-2130 ∷ Toff401 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q179 c4) ∷
   rw 2 (q180 c4) ∷
   rw 1 (q181 c4) ∷
   rw 0 (q182 c4) ∷
   rw 1 (q24 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q183 : Ws → Eqn
  q183 c4 = eqn (Sw12 ∷ Toff402 ∷ []) (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 (lit c4))
  q184 : Ws → Eqn
  q184 c4 = eqn (Sw12 ∷ Bx4-1230 ∷ []) (Bx4-2130 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·1230⟩ (lit c4))
  q185 : Ws → Eqn
  q185 c4 = eqn (Toff401 ∷ Bx4-2130 ∷ []) (Bx4-2130 ∷ Toff401 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0410213243 c4)
  q186 : Ws → Eqn
  q186 c4 = eqn (Sw12 ∷ Bx4-2130 ∷ []) (Bx4-1230 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·2130⟩ (lit c4))

-- auto TOFF012 | BOX(0;3241) @04103143: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at04103143 : Ws → ⟪ (Toff402 ∷ Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ Toff402 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at04103143 c4 = derive (Toff402 ∷ Bx4-1230 ∷ []) (Bx4-1230 ∷ Toff402 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q183 c4) ∷
   rw 2 (q184 c4) ∷
   rw 1 (q185 c4) ∷
   rw 0 (q186 c4) ∷
   rw 1 (q107 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q187 : Ws → Eqn
  q187 c4 = eqn (Sw23 ∷ Toff403 ∷ []) (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 (lit c4))
  q188 : Ws → Eqn
  q188 c4 = eqn (Sw23 ∷ Bx4-1320 ∷ []) (Bx4-1230 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·1320⟩ (lit c4))
  q189 : Ws → Eqn
  q189 c4 = eqn (Toff402 ∷ Bx4-1230 ∷ []) (Bx4-1230 ∷ Toff402 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at04103143 c4)
  q190 : Ws → Eqn
  q190 c4 = eqn (Sw23 ∷ Bx4-1230 ∷ []) (Bx4-1320 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·1230⟩ (lit c4))

-- auto TOFF012 | BOX(0;3241) @0410233142: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0410233142 : Ws → ⟪ (Toff403 ∷ Bx4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ Toff403 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0410233142 c4 = derive (Toff403 ∷ Bx4-1320 ∷ []) (Bx4-1320 ∷ Toff403 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q187 c4) ∷
   rw 2 (q188 c4) ∷
   rw 1 (q189 c4) ∷
   rw 0 (q190 c4) ∷
   rw 1 (q111 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q191 : Ws → Eqn
  q191 c4 = eqn (Sw01 ∷ Toff413 ∷ []) (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 (lit c4))
  q192 : Ws → Eqn
  q192 c4 = eqn (Sw01 ∷ Bx4-0321 ∷ []) (Bx4-1320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0321⟩ (lit c4))
  q193 : Ws → Eqn
  q193 c4 = eqn (Toff403 ∷ Bx4-1320 ∷ []) (Bx4-1320 ∷ Toff403 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0410233142 c4)
  q194 : Ws → Eqn
  q194 c4 = eqn (Sw01 ∷ Bx4-1320 ∷ []) (Bx4-0321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1320⟩ (lit c4))

-- auto TOFF012 | BOX(0;3241) @04233042: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at04233042 : Ws → ⟪ (Toff413 ∷ Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ Toff413 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at04233042 c4 = derive (Toff413 ∷ Bx4-0321 ∷ []) (Bx4-0321 ∷ Toff413 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q191 c4) ∷
   rw 2 (q192 c4) ∷
   rw 1 (q193 c4) ∷
   rw 0 (q194 c4) ∷
   rw 1 (q115 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q195 : Ws → Eqn
  q195 c4 = eqn (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) (wl0091 (lit c4))
  q196 : Ws → Eqn
  q196 c4 = eqn (Sw12 ∷ Bx4-0312 ∷ []) (Bx4-0321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0312⟩ (lit c4))
  q197 : Ws → Eqn
  q197 c4 = eqn (Toff413 ∷ Bx4-0321 ∷ []) (Bx4-0321 ∷ Toff413 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at04233042 c4)
  q198 : Ws → Eqn
  q198 c4 = eqn (Sw12 ∷ Bx4-0321 ∷ []) (Bx4-0312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0321⟩ (lit c4))
  q199 : Ws → Eqn
  q199 c4 = eqn (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) (wl0085 (lit c4))

-- auto TOFF012 | BOX(0;3241) @0412233041: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0412233041 : Ws → ⟪ (Toff423 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Toff423 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0412233041 c4 = derive (Toff423 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Toff423 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q195 c4) ∷
   rw 2 (q196 c4) ∷
   rw 1 (q197 c4) ∷
   rw 0 (q198 c4) ∷
   rw 1 (q199 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q200 : Ws → Eqn
  q200 c4 = eqn (Sw23 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ (lit c4))
  q201 : Ws → Eqn
  q201 c4 = eqn (Sb0-1-2-3 ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩ c4)
  q202 : Ws → Eqn
  q202 c4 = eqn (Sw23 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ (lit c4))

-- auto SBOX(0;1;2;3) | BOX(2;0314) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2332 : Ws → ⟪ (Sb0-1-3-2 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2332 c4 = derive (Sb0-1-3-2 ∷ Bx3-0214 ∷ []) (Bx3-0214 ∷ Sb0-1-3-2 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q200 c4) ∷
   rw 2 (q150 c4) ∷
   rw 1 (q201 c4) ∷
   rw 0 (q152 c4) ∷
   rw 1 (q202 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q203 : Ws → Eqn
  q203 c4 = eqn (Sw34 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ (lit c4))
  q204 : Ws → Eqn
  q204 c4 = eqn (Sb0-1-3-2 ∷ Bx3-0214 ∷ []) (Bx3-0214 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2332 c4)
  q205 : Ws → Eqn
  q205 c4 = eqn (Sw34 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ (lit c4))

-- auto SBOX(0;1;2;3) | BOX(2;0314) @243243: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at243243 : Ws → ⟪ (Sb0-1-4-2 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at243243 c4 = derive (Sb0-1-4-2 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Sb0-1-4-2 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q203 c4) ∷
   rw 2 (q155 c4) ∷
   rw 1 (q204 c4) ∷
   rw 0 (q157 c4) ∷
   rw 1 (q205 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q206 : Ws → Eqn
  q206 c4 = eqn (Sw23 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ (lit c4))
  q207 : Ws → Eqn
  q207 c4 = eqn (Sb0-1-4-2 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Sb0-1-4-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at243243 c4)
  q208 : Ws → Eqn
  q208 c4 = eqn (Sw23 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ (lit c4))

-- auto SBOX(0;1;2;3) | BOX(2;0314) @2442: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2442 : Ws → ⟪ (Sb0-1-4-3 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2442 c4 = derive (Sb0-1-4-3 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Sb0-1-4-3 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q206 c4) ∷
   rw 2 (q160 c4) ∷
   rw 1 (q207 c4) ∷
   rw 0 (q162 c4) ∷
   rw 1 (q208 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q209 : Ws → Eqn
  q209 c4 = eqn (Sb⁻0-1-4-3 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2442 c4)
  q210 : Ws → Eqn
  q210 c4 = eqn (Toff423 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0412233041 c4)
  q211 : Ws → Eqn
  q211 c4 = eqn (Sb0-1-4-3 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2442 c4)
  q212 : Ws → Eqn
  q212 c4 = eqn (Bx0-1234 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·0312⟩ c4)

-- auto SBOX(0;1;23;4) | BOX(4;0312): 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0312⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0312⟩ c4 = derive (Sb0-1-23-4 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   rw 4 (q209 c4) ∷
   rw 3 (q210 c4) ∷
   rw 2 (q211 c4) ∷
   rw 1 (q210 c4) ∷
   rw 0 (q212 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q213 : Ws → Eqn
  q213 c4 = eqn (Bx0-1234 ∷ CS24 ∷ []) (CS24 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS42 c4)

-- auto BOX(0;1234) | SBOX(0;4;2;1): 3 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩ : Ws → ⟪ (Bx0-1234 ∷ Sb0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-2-1 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩ c4 = derive (Bx0-1234 ∷ Sb0-4-2-1 ∷ []) (Sb0-4-2-1 ∷ Bx0-1234 ∷ [])
  (re 1 1 (CS24 ∷ []) ∷
   rw 0 (q213 c4) ∷
   re 0 1 (Sb0-4-2-1 ∷ []) ∷ []) Eq.refl

private
  q214 : Ws → Eqn
  q214 c4 = eqn (CS03⁻ ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS03⁻ ∷ []) (lem-CS20-beta-ci-at2332 c4)

-- auto BOX(0;1234) | CSd03: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd03 : Ws → ⟪ (Bx0-1234 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd03 c4 = derive (Bx0-1234 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx0-1234 ∷ [])
  (rw 0 (q78 c4) ∷
   rw⁻ 0 (q214 c4) ∷
   rw 1 (q84 c4) ∷ []) Eq.refl

private
  q215 : Ws → Eqn
  q215 c4 = eqn (CS03⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS03⁻ ∷ []) (wp0118 c4)
  q216 : Ws → Eqn
  q216 c4 = eqn (CS03⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS03⁻ ∷ []) (wp0262 c4)
  q217 : Ws → Eqn
  q217 c4 = eqn (CS03⁻ ∷ CS14 ∷ []) (CS14 ∷ CS03⁻ ∷ []) (wp0120 c4)
  q218 : Ws → Eqn
  q218 c4 = eqn (Bx0-1234 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd03 c4)

-- auto SBOX(0;1;23;4) | CSd03: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd03 : Ws → ⟪ (Sb0-1-23-4 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd03 c4 = derive (Sb0-1-23-4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q215 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw⁻ 3 (q216 c4) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw⁻ 2 (q217 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw⁻ 1 (q216 c4) ∷
   rw 0 (q218 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q219 : Ws → Eqn
  q219 c4 = eqn (Sw23 ∷ CS02⁻ ∷ []) (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 (lit c4))
  q220 : Ws → Eqn
  q220 c4 = eqn (Sb0-1-23-4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd03 c4)
  q221 : Ws → Eqn
  q221 c4 = eqn (Sw23 ∷ CS03⁻ ∷ []) (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 (lit c4))

-- auto SBOX(0;1;23;4) | CSd03 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd03-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd03-at2332 c4 = derive (Sb0-1-32-4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q13 c4) ∷
   rw 2 (q219 c4) ∷
   rw 1 (q220 c4) ∷
   rw 0 (q221 c4) ∷
   rw 1 (q17 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q222 : Ws → Eqn
  q222 c4 = eqn (Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4)
  q223 : Ws → Eqn
  q223 c4 = eqn (Sb0-1-32-4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd03-at2332 c4)

-- auto SBOX(0;1;23;4) | SBOXd(4;0;2;1): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·2·1⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb⁻4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-2-1 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·2·1⟩ c4 = derive (Sb0-1-23-4 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻4-0-2-1 ∷ Sb0-1-23-4 ∷ [])
  (re 1 1 (CS02⁻ ∷ []) ∷
   rw 0 (q222 c4) ∷
   rw 0 (q223 c4) ∷
   rw⁻ 1 (q222 c4) ∷
   re 0 1 (Sb⁻4-0-2-1 ∷ []) ∷ []) Eq.refl

private
  q224 : Ws → Eqn
  q224 c4 = eqn (Sw23 ∷ Sb3-0-21-4 ∷ []) (Sb2-0-31-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·21·4⟩ (lit c4))
  q225 : Ws → Eqn
  q225 c4 = eqn (Sb2-0-31-4 ∷ []) (Sb4-0-31-2 ∷ []) (lem-F0-at3443 c4)
  q226 : Ws → Eqn
  q226 c4 = eqn (Sw23 ∷ Sb4-0-31-2 ∷ []) (Sb4-0-21-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·0·31·2⟩ (lit c4))

-- F0 @233442: 5 steps
lem-F0-at233442 : Ws → ⟪ (Sb3-0-21-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-21-3 ∷ []) ⟫ʷ
lem-F0-at233442 c4 = derive (Sb3-0-21-4 ∷ []) (Sb4-0-21-3 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q224 c4) ∷
   rw 1 (q225 c4) ∷
   rw 0 (q226 c4) ∷
   rw 1 (q12 c4) ∷ []) Eq.refl

private
  q227 : Ws → Eqn
  q227 c4 = eqn (Sb0-1-23-4 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0312⟩ c4)

-- auto SBOX(0;1;23;4) | BOX(4;0312) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0312⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0312⟩-at2332 c4 = derive (Sb0-1-32-4 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q13 c4) ∷
   rw 2 (q162 c4) ∷
   rw 1 (q227 c4) ∷
   rw 0 (q160 c4) ∷
   rw 1 (q17 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q228 : Ws → Eqn
  q228 c4 = eqn (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) (wl0116 (lit c4))
  q229 : Ws → Eqn
  q229 c4 = eqn (Sw01 ∷ Bx1-0234 ∷ []) (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4))
  q230 : Ws → Eqn
  q230 c4 = eqn (Toff312 ∷ Bx0-1234 ∷ Toff312 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ []) (lem-T312-beta c4)
  q231 : Ws → Eqn
  q231 c4 = eqn (Sw01 ∷ Bx0-1234 ∷ []) (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4))

-- T312-beta @0110: 8 steps
lem-T312-beta-at0110 : Ws → ⟪ (Toff302 ∷ Bx1-0234 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CCZ024 ∷ []) ⟫ʷ
lem-T312-beta-at0110 c4 = derive (Toff302 ∷ Bx1-0234 ∷ Toff302 ∷ []) (Bx1-0234 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q228 c4) ∷
   rw 2 (q229 c4) ∷
   rw 3 (q228 c4) ∷
   rw 1 (q230 c4) ∷
   rw 0 (q231 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q232 : Ws → Eqn
  q232 c4 = eqn (Sw12 ∷ Toff301 ∷ []) (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 (lit c4))
  q233 : Ws → Eqn
  q233 c4 = eqn (Sw12 ∷ Bx2-0134 ∷ []) (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4))
  q234 : Ws → Eqn
  q234 c4 = eqn (Toff302 ∷ Bx1-0234 ∷ Toff302 ∷ []) (Bx1-0234 ∷ CCZ024 ∷ []) (lem-T312-beta-at0110 c4)
  q235 : Ws → Eqn
  q235 c4 = eqn (Sw12 ∷ Bx1-0234 ∷ []) (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4))

-- T312-beta @021021: 8 steps
lem-T312-beta-at021021 : Ws → ⟪ (Toff301 ∷ Bx2-0134 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ CCZ014 ∷ []) ⟫ʷ
lem-T312-beta-at021021 c4 = derive (Toff301 ∷ Bx2-0134 ∷ Toff301 ∷ []) (Bx2-0134 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q232 c4) ∷
   rw 2 (q233 c4) ∷
   rw 3 (q232 c4) ∷
   rw 1 (q234 c4) ∷
   rw 0 (q235 c4) ∷
   rw 1 (q131 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q236 : Ws → Eqn
  q236 c4 = eqn (Sw23 ∷ Bx3-0124 ∷ []) (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ (lit c4))
  q237 : Ws → Eqn
  q237 c4 = eqn (Toff301 ∷ Bx2-0134 ∷ Toff301 ∷ []) (Bx2-0134 ∷ CCZ014 ∷ []) (lem-T312-beta-at021021 c4)
  q238 : Ws → Eqn
  q238 c4 = eqn (Sw23 ∷ Bx2-0134 ∷ []) (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ (lit c4))
  q239 : Ws → Eqn
  q239 c4 = eqn (Sw23 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 (lit c4))

-- T312-beta @03102132: 8 steps
lem-T312-beta-at03102132 : Ws → ⟪ (Toff201 ∷ Bx3-0124 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ CCZ014 ∷ []) ⟫ʷ
lem-T312-beta-at03102132 c4 = derive (Toff201 ∷ Bx3-0124 ∷ Toff201 ∷ []) (Bx3-0124 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q178 c4) ∷
   rw 2 (q236 c4) ∷
   rw 3 (q178 c4) ∷
   rw 1 (q237 c4) ∷
   rw 0 (q238 c4) ∷
   rw 1 (q239 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q240 : Ws → Eqn
  q240 c4 = eqn (Toff201 ∷ Sw34 ∷ []) (Sw34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (Swap))
  q241 : Ws → Eqn
  q241 c4 = eqn (Toff201 ∷ Bx3-0124 ∷ Toff201 ∷ []) (Bx3-0124 ∷ CCZ014 ∷ []) (lem-T312-beta-at03102132 c4)
  q242 : Ws → Eqn
  q242 c4 = eqn (Sw34 ∷ Bx3-0124 ∷ []) (Bx4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0124⟩ (lit c4))

-- T312-beta @0410213243: 8 steps
lem-T312-beta-at0410213243 : Ws → ⟪ (Toff201 ∷ Bx4-0123 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ CCZ013 ∷ []) ⟫ʷ
lem-T312-beta-at0410213243 c4 = derive (Toff201 ∷ Bx4-0123 ∷ Toff201 ∷ []) (Bx4-0123 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw⁻ 1 (q240 c4) ∷
   rw 2 (q22 c4) ∷
   rw⁻ 3 (q240 c4) ∷
   rw 1 (q241 c4) ∷
   rw 0 (q242 c4) ∷
   rw 1 (q126 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q243 : Ws → Eqn
  q243 c4 = eqn (Sw23 ∷ Bx4-0132 ∷ []) (Bx4-0123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0132⟩ (lit c4))
  q244 : Ws → Eqn
  q244 c4 = eqn (Toff201 ∷ Bx4-0123 ∷ Toff201 ∷ []) (Bx4-0123 ∷ CCZ013 ∷ []) (lem-T312-beta-at0410213243 c4)
  q245 : Ws → Eqn
  q245 c4 = eqn (Sw23 ∷ Bx4-0123 ∷ []) (Bx4-0132 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0123⟩ (lit c4))

-- T312-beta @04102142: 8 steps
lem-T312-beta-at04102142 : Ws → ⟪ (Toff301 ∷ Bx4-0132 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0132 ∷ CCZ012 ∷ []) ⟫ʷ
lem-T312-beta-at04102142 c4 = derive (Toff301 ∷ Bx4-0132 ∷ Toff301 ∷ []) (Bx4-0132 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q174 c4) ∷
   rw 2 (q243 c4) ∷
   rw 3 (q174 c4) ∷
   rw 1 (q244 c4) ∷
   rw 0 (q245 c4) ∷
   rw 1 (q122 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q246 : Ws → Eqn
  q246 c4 = eqn (Sw12 ∷ Toff302 ∷ []) (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 (lit c4))
  q247 : Ws → Eqn
  q247 c4 = eqn (Sw12 ∷ Bx4-0231 ∷ []) (Bx4-0132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0231⟩ (lit c4))
  q248 : Ws → Eqn
  q248 c4 = eqn (Toff301 ∷ Bx4-0132 ∷ Toff301 ∷ []) (Bx4-0132 ∷ CCZ012 ∷ []) (lem-T312-beta-at04102142 c4)
  q249 : Ws → Eqn
  q249 c4 = eqn (Sw12 ∷ Bx4-0132 ∷ []) (Bx4-0231 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0132⟩ (lit c4))

-- T312-beta @041041: 8 steps
lem-T312-beta-at041041 : Ws → ⟪ (Toff302 ∷ Bx4-0231 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ CCZ012 ∷ []) ⟫ʷ
lem-T312-beta-at041041 c4 = derive (Toff302 ∷ Bx4-0231 ∷ Toff302 ∷ []) (Bx4-0231 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q246 c4) ∷
   rw 2 (q247 c4) ∷
   rw 3 (q246 c4) ∷
   rw 1 (q248 c4) ∷
   rw 0 (q249 c4) ∷
   rw⁻ 1 (q119 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q250 : Ws → Eqn
  q250 c4 = eqn (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) (wl0110 (lit c4))
  q251 : Ws → Eqn
  q251 c4 = eqn (Sw01 ∷ Bx4-1230 ∷ []) (Bx4-0231 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1230⟩ (lit c4))
  q252 : Ws → Eqn
  q252 c4 = eqn (Toff302 ∷ Bx4-0231 ∷ Toff302 ∷ []) (Bx4-0231 ∷ CCZ012 ∷ []) (lem-T312-beta-at041041 c4)
  q253 : Ws → Eqn
  q253 c4 = eqn (Sw01 ∷ Bx4-0231 ∷ []) (Bx4-1230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0231⟩ (lit c4))

-- T312-beta @0440: 8 steps
lem-T312-beta-at0440 : Ws → ⟪ (Toff312 ∷ Bx4-1230 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ CCZ012 ∷ []) ⟫ʷ
lem-T312-beta-at0440 c4 = derive (Toff312 ∷ Bx4-1230 ∷ Toff312 ∷ []) (Bx4-1230 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q250 c4) ∷
   rw 2 (q251 c4) ∷
   rw 3 (q250 c4) ∷
   rw 1 (q252 c4) ∷
   rw 0 (q253 c4) ∷
   rw⁻ 1 (q117 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q254 : Ws → Eqn
  q254 c4 = eqn (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 (lit c4))
  q255 : Ws → Eqn
  q255 c4 = eqn (Bx0-1234 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134 c4)
  q256 : Ws → Eqn
  q256 c4 = eqn (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4))

-- auto BOX(0;1234) | CCZ134 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0110 : Ws → ⟪ (Bx1-0234 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0110 c4 = derive (Bx1-0234 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx1-0234 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q229 c4) ∷
   rw 2 (q254 c4) ∷
   rw 1 (q255 c4) ∷
   rw 0 (q256 c4) ∷
   rw 1 (q231 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q257 : Ws → Eqn
  q257 c4 = eqn (Sw12 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4))
  q258 : Ws → Eqn
  q258 c4 = eqn (Bx1-0234 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0110 c4)

-- auto BOX(0;1234) | CCZ134 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at021021 : Ws → ⟪ (Bx2-0134 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at021021 c4 = derive (Bx2-0134 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx2-0134 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q233 c4) ∷
   rw 2 (q257 c4) ∷
   rw 1 (q258 c4) ∷
   rw 0 (q257 c4) ∷
   rw 1 (q235 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q259 : Ws → Eqn
  q259 c4 = eqn (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 (lit c4))
  q260 : Ws → Eqn
  q260 c4 = eqn (Bx2-0134 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at021021 c4)
  q261 : Ws → Eqn
  q261 c4 = eqn (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4))

-- auto BOX(0;1234) | CCZ134 @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at03102132 : Ws → ⟪ (Bx3-0124 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at03102132 c4 = derive (Bx3-0124 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0124 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q236 c4) ∷
   rw 2 (q259 c4) ∷
   rw 1 (q260 c4) ∷
   rw 0 (q261 c4) ∷
   rw 1 (q238 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q262 : Ws → Eqn
  q262 c4 = eqn (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 (lit c4))
  q263 : Ws → Eqn
  q263 c4 = eqn (Bx3-0124 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at03102132 c4)
  q264 : Ws → Eqn
  q264 c4 = eqn (Sw34 ∷ CCZ024 ∷ []) (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 (lit c4))

-- auto BOX(0;1234) | CCZ134 @0410213243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Bx4-0123 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410213243 c4 = derive (Bx4-0123 ∷ CCZ023 ∷ []) (CCZ023 ∷ Bx4-0123 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   rw 2 (q262 c4) ∷
   rw 1 (q263 c4) ∷
   rw 0 (q264 c4) ∷
   rw 1 (q242 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q265 : Ws → Eqn
  q265 c4 = eqn (Sw12 ∷ Bx4-0213 ∷ []) (Bx4-0123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0213⟩ (lit c4))
  q266 : Ws → Eqn
  q266 c4 = eqn (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4))
  q267 : Ws → Eqn
  q267 c4 = eqn (Bx4-0123 ∷ CCZ023 ∷ []) (CCZ023 ∷ Bx4-0123 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410213243 c4)
  q268 : Ws → Eqn
  q268 c4 = eqn (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4))
  q269 : Ws → Eqn
  q269 c4 = eqn (Sw12 ∷ Bx4-0123 ∷ []) (Bx4-0213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0123⟩ (lit c4))

-- auto BOX(0;1234) | CCZ134 @04103143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at04103143 : Ws → ⟪ (Bx4-0213 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Bx4-0213 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at04103143 c4 = derive (Bx4-0213 ∷ CCZ013 ∷ []) (CCZ013 ∷ Bx4-0213 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q265 c4) ∷
   rw 2 (q266 c4) ∷
   rw 1 (q267 c4) ∷
   rw 0 (q268 c4) ∷
   rw 1 (q269 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q270 : Ws → Eqn
  q270 c4 = eqn (Bx4-0213 ∷ CCZ013 ∷ []) (CCZ013 ∷ Bx4-0213 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at04103143 c4)

-- auto BOX(0;1234) | CCZ134 @0410233142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410233142 : Ws → ⟪ (Bx4-0312 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx4-0312 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410233142 c4 = derive (Bx4-0312 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx4-0312 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q160 c4) ∷
   rw 2 (q125 c4) ∷
   rw 1 (q270 c4) ∷
   rw 0 (q122 c4) ∷
   rw 1 (q162 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q271 : Ws → Eqn
  q271 c4 = eqn (Bx4-0312 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx4-0312 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410233142 c4)

-- auto BOX(0;1234) | CCZ134 @0410233241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410233241 : Ws → ⟪ (Bx4-0321 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx4-0321 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410233241 c4 = derive (Bx4-0321 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx4-0321 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q198 c4) ∷
   rw⁻ 2 (q119 c4) ∷
   rw 1 (q271 c4) ∷
   rw⁻ 0 (q119 c4) ∷
   rw 1 (q196 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q272 : Ws → Eqn
  q272 c4 = eqn (Bx4-0321 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx4-0321 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410233241 c4)

-- auto BOX(0;1234) | CCZ134 @04233240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at04233240 : Ws → ⟪ (Bx4-1320 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx4-1320 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at04233240 c4 = derive (Bx4-1320 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx4-1320 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q194 c4) ∷
   rw⁻ 2 (q117 c4) ∷
   rw 1 (q272 c4) ∷
   rw⁻ 0 (q117 c4) ∷
   rw 1 (q192 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q273 : Ws → Eqn
  q273 c4 = eqn (Sw01 ∷ Sb1-4-2-0 ∷ []) (Sb0-4-2-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·4·2·0⟩ (lit c4))
  q274 : Ws → Eqn
  q274 c4 = eqn (Bx0-1234 ∷ Sb0-4-2-1 ∷ []) (Sb0-4-2-1 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩ c4)
  q275 : Ws → Eqn
  q275 c4 = eqn (Sw01 ∷ Sb0-4-2-1 ∷ []) (Sb1-4-2-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·4·2·1⟩ (lit c4))

-- auto BOX(0;1234) | SBOX(0;4;2;1) @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0110 : Ws → ⟪ (Bx1-0234 ∷ Sb1-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-2-0 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0110 c4 = derive (Bx1-0234 ∷ Sb1-4-2-0 ∷ []) (Sb1-4-2-0 ∷ Bx1-0234 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q229 c4) ∷
   rw 2 (q273 c4) ∷
   rw 1 (q274 c4) ∷
   rw 0 (q275 c4) ∷
   rw 1 (q231 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q276 : Ws → Eqn
  q276 c4 = eqn (Sw12 ∷ Sb2-4-1-0 ∷ []) (Sb1-4-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·4·1·0⟩ (lit c4))
  q277 : Ws → Eqn
  q277 c4 = eqn (Bx1-0234 ∷ Sb1-4-2-0 ∷ []) (Sb1-4-2-0 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0110 c4)
  q278 : Ws → Eqn
  q278 c4 = eqn (Sw12 ∷ Sb1-4-2-0 ∷ []) (Sb2-4-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·4·2·0⟩ (lit c4))

-- auto BOX(0;1234) | SBOX(0;4;2;1) @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at021021 : Ws → ⟪ (Bx2-0134 ∷ Sb2-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-1-0 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at021021 c4 = derive (Bx2-0134 ∷ Sb2-4-1-0 ∷ []) (Sb2-4-1-0 ∷ Bx2-0134 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q233 c4) ∷
   rw 2 (q276 c4) ∷
   rw 1 (q277 c4) ∷
   rw 0 (q278 c4) ∷
   rw 1 (q235 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q279 : Ws → Eqn
  q279 c4 = eqn (Sw23 ∷ Sb3-4-1-0 ∷ []) (Sb2-4-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·4·1·0⟩ (lit c4))
  q280 : Ws → Eqn
  q280 c4 = eqn (Bx2-0134 ∷ Sb2-4-1-0 ∷ []) (Sb2-4-1-0 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at021021 c4)
  q281 : Ws → Eqn
  q281 c4 = eqn (Sw23 ∷ Sb2-4-1-0 ∷ []) (Sb3-4-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·4·1·0⟩ (lit c4))

-- auto BOX(0;1234) | SBOX(0;4;2;1) @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at03102132 : Ws → ⟪ (Bx3-0124 ∷ Sb3-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-1-0 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at03102132 c4 = derive (Bx3-0124 ∷ Sb3-4-1-0 ∷ []) (Sb3-4-1-0 ∷ Bx3-0124 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q236 c4) ∷
   rw 2 (q279 c4) ∷
   rw 1 (q280 c4) ∷
   rw 0 (q281 c4) ∷
   rw 1 (q238 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q282 : Ws → Eqn
  q282 c4 = eqn (Sw34 ∷ Sb4-3-1-0 ∷ []) (Sb3-4-1-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨4·3·1·0⟩ (lit c4))
  q283 : Ws → Eqn
  q283 c4 = eqn (Bx3-0124 ∷ Sb3-4-1-0 ∷ []) (Sb3-4-1-0 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at03102132 c4)
  q284 : Ws → Eqn
  q284 c4 = eqn (Sw34 ∷ Sb3-4-1-0 ∷ []) (Sb4-3-1-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨3·4·1·0⟩ (lit c4))

-- auto BOX(0;1234) | SBOX(0;4;2;1) @0410213243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ Sb4-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-3-1-0 ∷ Bx4-0123 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410213243 c4 = derive (Bx4-0123 ∷ Sb4-3-1-0 ∷ []) (Sb4-3-1-0 ∷ Bx4-0123 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   rw 2 (q282 c4) ∷
   rw 1 (q283 c4) ∷
   rw 0 (q284 c4) ∷
   rw 1 (q242 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q285 : Ws → Eqn
  q285 c4 = eqn (Sw12 ∷ Sb4-3-2-0 ∷ []) (Sb4-3-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨4·3·2·0⟩ (lit c4))
  q286 : Ws → Eqn
  q286 c4 = eqn (Bx4-0123 ∷ Sb4-3-1-0 ∷ []) (Sb4-3-1-0 ∷ Bx4-0123 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410213243 c4)
  q287 : Ws → Eqn
  q287 c4 = eqn (Sw12 ∷ Sb4-3-1-0 ∷ []) (Sb4-3-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨4·3·1·0⟩ (lit c4))

-- auto BOX(0;1234) | SBOX(0;4;2;1) @04103143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at04103143 : Ws → ⟪ (Bx4-0213 ∷ Sb4-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-3-2-0 ∷ Bx4-0213 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at04103143 c4 = derive (Bx4-0213 ∷ Sb4-3-2-0 ∷ []) (Sb4-3-2-0 ∷ Bx4-0213 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q265 c4) ∷
   rw 2 (q285 c4) ∷
   rw 1 (q286 c4) ∷
   rw 0 (q287 c4) ∷
   rw 1 (q269 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q288 : Ws → Eqn
  q288 c4 = eqn (Sw23 ∷ Sb4-2-3-0 ∷ []) (Sb4-3-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·2·3·0⟩ (lit c4))
  q289 : Ws → Eqn
  q289 c4 = eqn (Bx4-0213 ∷ Sb4-3-2-0 ∷ []) (Sb4-3-2-0 ∷ Bx4-0213 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at04103143 c4)
  q290 : Ws → Eqn
  q290 c4 = eqn (Sw23 ∷ Sb4-3-2-0 ∷ []) (Sb4-2-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·3·2·0⟩ (lit c4))

-- auto BOX(0;1234) | SBOX(0;4;2;1) @0410233142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410233142 : Ws → ⟪ (Bx4-0312 ∷ Sb4-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-3-0 ∷ Bx4-0312 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410233142 c4 = derive (Bx4-0312 ∷ Sb4-2-3-0 ∷ []) (Sb4-2-3-0 ∷ Bx4-0312 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q160 c4) ∷
   rw 2 (q288 c4) ∷
   rw 1 (q289 c4) ∷
   rw 0 (q290 c4) ∷
   rw 1 (q162 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q291 : Ws → Eqn
  q291 c4 = eqn (Sw12 ∷ Sb4-1-3-0 ∷ []) (Sb4-2-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨4·1·3·0⟩ (lit c4))
  q292 : Ws → Eqn
  q292 c4 = eqn (Bx4-0312 ∷ Sb4-2-3-0 ∷ []) (Sb4-2-3-0 ∷ Bx4-0312 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410233142 c4)
  q293 : Ws → Eqn
  q293 c4 = eqn (Sw12 ∷ Sb4-2-3-0 ∷ []) (Sb4-1-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨4·2·3·0⟩ (lit c4))

-- auto BOX(0;1234) | SBOX(0;4;2;1) @0410233241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410233241 : Ws → ⟪ (Bx4-0321 ∷ Sb4-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-3-0 ∷ Bx4-0321 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410233241 c4 = derive (Bx4-0321 ∷ Sb4-1-3-0 ∷ []) (Sb4-1-3-0 ∷ Bx4-0321 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q198 c4) ∷
   rw 2 (q291 c4) ∷
   rw 1 (q292 c4) ∷
   rw 0 (q293 c4) ∷
   rw 1 (q196 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q294 : Ws → Eqn
  q294 c4 = eqn (Sw01 ∷ Sb4-0-3-1 ∷ []) (Sb4-1-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨4·0·3·1⟩ (lit c4))
  q295 : Ws → Eqn
  q295 c4 = eqn (Bx4-0321 ∷ Sb4-1-3-0 ∷ []) (Sb4-1-3-0 ∷ Bx4-0321 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410233241 c4)
  q296 : Ws → Eqn
  q296 c4 = eqn (Sw01 ∷ Sb4-1-3-0 ∷ []) (Sb4-0-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨4·1·3·0⟩ (lit c4))

-- auto BOX(0;1234) | SBOX(0;4;2;1) @04233240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at04233240 : Ws → ⟪ (Bx4-1320 ∷ Sb4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-3-1 ∷ Bx4-1320 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at04233240 c4 = derive (Bx4-1320 ∷ Sb4-0-3-1 ∷ []) (Sb4-0-3-1 ∷ Bx4-1320 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q194 c4) ∷
   rw 2 (q294 c4) ∷
   rw 1 (q295 c4) ∷
   rw 0 (q296 c4) ∷
   rw 1 (q192 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q297 : Ws → Eqn
  q297 c4 = eqn (Sw23 ∷ Sb⁻4-0-3-1 ∷ []) (Sb⁻4-0-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·0·3·1⟩ (lit c4))
  q298 : Ws → Eqn
  q298 c4 = eqn (Sb0-1-23-4 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻4-0-2-1 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·2·1⟩ c4)
  q299 : Ws → Eqn
  q299 c4 = eqn (Sw23 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻4-0-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·0·2·1⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(4;0;2;1) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·2·1⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb⁻4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-3-1 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·2·1⟩-at2332 c4 = derive (Sb0-1-32-4 ∷ Sb⁻4-0-3-1 ∷ []) (Sb⁻4-0-3-1 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q13 c4) ∷
   rw 2 (q297 c4) ∷
   rw 1 (q298 c4) ∷
   rw 0 (q299 c4) ∷
   rw 1 (q17 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q300 : Ws → Eqn
  q300 c4 = eqn (Sb3-0-21-4 ∷ []) (Sb4-0-21-3 ∷ []) (lem-F0-at233442 c4)
  q301 : Ws → Eqn
  q301 c4 = eqn (Sb0-1-32-4 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0312⟩-at2332 c4)
  q302 : Ws → Eqn
  q302 c4 = eqn (Sb0-1-32-4 ∷ []) (Sb4-1-32-0 ∷ []) (lem-F0-at0112203443 c4)
  q303 : Ws → Eqn
  q303 c4 = eqn (CS01⁻ ∷ Toff312 ∷ CS03 ∷ Toff312 ∷ []) (Toff312 ∷ CS03 ∷ Toff312 ∷ CS01⁻ ∷ []) (wl0607 (lit c4))
  q304 : Ws → Eqn
  q304 c4 = eqn (Toff023 ∷ CS01 ∷ Toff023 ∷ Toff312 ∷ CS03 ∷ Toff312 ∷ []) (Toff312 ∷ CS03 ∷ Toff312 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ []) (wl0608 (lit c4))
  q305 : Ws → Eqn
  q305 c4 = eqn (Toff312 ∷ Toff312 ∷ []) [] (wl0230 (lit c4))
  q306 : Ws → Eqn
  q306 c4 = eqn (Toff312 ∷ []) (Toff312 ∷ []) (wl0609 (lit c4))
  q307 : Ws → Eqn
  q307 c4 = eqn (Bx4-1320 ∷ []) (Bx4-1230 ∷ []) (lem-sym23-at04233240 c4)
  q308 : Ws → Eqn
  q308 c4 = eqn (Toff312 ∷ Bx4-1230 ∷ Toff312 ∷ []) (Bx4-1230 ∷ CCZ012 ∷ []) (lem-T312-beta-at0440 c4)
  q309 : Ws → Eqn
  q309 c4 = eqn (Bx4-1230 ∷ []) (Bx4-1320 ∷ []) (lem-sym23-at0440 c4)
  q310 : Ws → Eqn
  q310 c4 = eqn (Bx4-1320 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at04233240 c4)
  q311 : Ws → Eqn
  q311 c4 = eqn (Bx4-1320 ∷ Sb4-0-3-1 ∷ []) (Sb4-0-3-1 ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at04233240 c4)
  q312 : Ws → Eqn
  q312 c4 = eqn (CCZ012 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ012 ∷ []) (wl0610 (lit c4))
  q313 : Ws → Eqn
  q313 c4 = eqn (CCZ012 ∷ Toff312 ∷ CS03 ∷ Toff312 ∷ []) (Toff312 ∷ CS03 ∷ Toff312 ∷ CCZ012 ∷ []) (wl0611 (lit c4))
  q314 : Ws → Eqn
  q314 c4 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wl0183 (lit c4))
  q315 : Ws → Eqn
  q315 c4 = eqn (Sb0-1-32-4 ∷ Sb⁻4-0-3-1 ∷ []) (Sb⁻4-0-3-1 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·2·1⟩-at2332 c4)

-- auto SBOX(0;1;23;4) | SBOX(3;0;21;4): 42 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb3-0-21-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-21-4 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩ c4 = derive (Sb0-1-23-4 ∷ Sb3-0-21-4 ∷ []) (Sb3-0-21-4 ∷ Sb0-1-23-4 ∷ [])
  (rw 1 (q300 c4) ∷
   re 1 1 (Bx4-0213 ∷ Toff312 ∷ Sb4-0-3-1 ∷ Toff312 ∷ Sb⁻4-0-3-1 ∷ []) ∷
   rw 0 (q222 c4) ∷
   rw 0 (q301 c4) ∷
   rw 1 (q302 c4) ∷
   re 1 1 (Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ []) ∷
   re 5 1 (CS01⁻ ∷ []) ∷
   re 7 1 (CS03 ∷ []) ∷
   rw 5 (q303 c4) ∷
   re 6 1 (Sb4-0-3-1 ∷ []) ∷
   re 8 1 (Sb⁻4-1-0-2 ∷ []) ∷
   re 3 1 (CS01 ∷ []) ∷
   re 6 1 (CS03 ∷ []) ∷
   rw 2 (q304 c4) ∷
   re 3 1 (Sb4-0-3-1 ∷ []) ∷
   re 6 1 (Sb4-1-0-2 ∷ []) ∷
   rw⁻ 1 (q305 c4) ∷
   rw 2 (q306 c4) ∷
   rw 4 (q306 c4) ∷
   rw 3 (q307 c4) ∷
   rw 2 (q308 c4) ∷
   rw 2 (q309 c4) ∷
   rw 2 (q310 c4) ∷
   rw 3 (q311 c4) ∷
   rw⁻ 4 (q305 c4) ∷
   rw 5 (q306 c4) ∷
   rw 7 (q306 c4) ∷
   rw 6 (q307 c4) ∷
   rw 5 (q308 c4) ∷
   rw 5 (q309 c4) ∷
   rw 5 (q310 c4) ∷
   rw⁻ 1 (q312 c4) ∷
   re 3 1 (CS03 ∷ []) ∷
   rw⁻ 2 (q313 c4) ∷
   re 4 1 (Sb4-0-3-1 ∷ []) ∷
   rw 1 (q314 c4) ∷
   re 4 5 (Sb4-1-32-0 ∷ []) ∷
   rw⁻ 4 (q302 c4) ∷
   rw 4 (q315 c4) ∷
   rw⁻ 5 (q222 c4) ∷
   re 0 5 (Sb4-0-21-3 ∷ []) ∷
   rw⁻ 0 (q300 c4) ∷ []) Eq.refl

private
  q316 : Ws → Eqn
  q316 c4 = eqn (Sw23 ∷ Sb2-0-31-4 ∷ []) (Sb3-0-21-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·31·4⟩ (lit c4))
  q317 : Ws → Eqn
  q317 c4 = eqn (Sb0-1-23-4 ∷ Sb3-0-21-4 ∷ []) (Sb3-0-21-4 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩ c4)

-- auto SBOX(0;1;23;4) | SBOX(3;0;21;4) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-31-4 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩-at2332 c4 = derive (Sb0-1-32-4 ∷ Sb2-0-31-4 ∷ []) (Sb2-0-31-4 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q13 c4) ∷
   rw 2 (q316 c4) ∷
   rw 1 (q317 c4) ∷
   rw 0 (q224 c4) ∷
   rw 1 (q17 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q318 : Ws → Eqn
  q318 c4 = eqn (Sw34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4))
  q319 : Ws → Eqn
  q319 c4 = eqn (Sw34 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-31-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·41·3⟩ (lit c4))
  q320 : Ws → Eqn
  q320 c4 = eqn (Sb0-1-32-4 ∷ Sb2-0-31-4 ∷ []) (Sb2-0-31-4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩-at2332 c4)
  q321 : Ws → Eqn
  q321 c4 = eqn (Sw34 ∷ Sb2-0-31-4 ∷ []) (Sb2-0-41-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·31·4⟩ (lit c4))
  q322 : Ws → Eqn
  q322 c4 = eqn (Sw34 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(3;0;21;4) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩-at243243 c4 = derive (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q318 c4) ∷
   rw 2 (q319 c4) ∷
   rw 1 (q320 c4) ∷
   rw 0 (q321 c4) ∷
   rw 1 (q322 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q323 : Ws → Eqn
  q323 c4 = eqn (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩-at243243 c4)

-- F1 comm-CS-CS: 1 steps
lem-F1-comm-CS-CS : Ws → ⟪ (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-CS c4 = derive (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ [])
  (rw 0 (q323 c4) ∷ []) Eq.refl

-- auto BOX(0;1234) | CCZ123: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123 : Ws → ⟪ (Bx0-1234 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123 c4 = derive (Bx0-1234 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1234 ∷ [])
  (rw 0 (q98 c4) ∷
   rw⁻ 0 (q99 c4) ∷
   rw 1 (q100 c4) ∷ []) Eq.refl

private
  q324 : Ws → Eqn
  q324 c4 = eqn (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4))
  q325 : Ws → Eqn
  q325 c4 = eqn (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (CCZ014 ∷ []) (lem-SB2 c4)

-- SB2 @1221: 6 steps
lem-SB2-at1221 : Ws → ⟪ (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ []) ⟫ʷ
lem-SB2-at1221 c4 = derive (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ []) (CCZ024 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q324 c4) ∷
   rw 2 (q324 c4) ∷
   rw 1 (q325 c4) ∷
   rw 0 (q134 c4) ∷
   rw 1 (q26 c4) ∷ []) Eq.refl

private
  q326 : Ws → Eqn
  q326 c4 = eqn (Sw01 ∷ Sb0-1-42-3 ∷ []) (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4))
  q327 : Ws → Eqn
  q327 c4 = eqn (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ []) (CCZ024 ∷ []) (lem-SB2-at1221 c4)
  q328 : Ws → Eqn
  q328 c4 = eqn (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4))

-- SB2 @011220: 6 steps
lem-SB2-at011220 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
lem-SB2-at011220 c4 = derive (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (CCZ124 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q326 c4) ∷
   rw 2 (q326 c4) ∷
   rw 1 (q327 c4) ∷
   rw 0 (q328 c4) ∷
   rw 1 (q39 c4) ∷ []) Eq.refl

private
  q329 : Ws → Eqn
  q329 c4 = eqn (Sw23 ∷ Bx3-0412 ∷ []) (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4))
  q330 : Ws → Eqn
  q330 c4 = eqn (Bx2-0413 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4)
  q331 : Ws → Eqn
  q331 c4 = eqn (Sw23 ∷ Bx2-0413 ∷ []) (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4))

-- auto BOX(0;1234) | CCZ231 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4 = derive (Bx3-0412 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx3-0412 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q329 c4) ∷
   rw 2 (q239 c4) ∷
   rw 1 (q330 c4) ∷
   rw 0 (q239 c4) ∷
   rw 1 (q331 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q332 : Ws → Eqn
  q332 c4 = eqn (Sw23 ∷ CS02 ∷ []) (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4))
  q333 : Ws → Eqn
  q333 c4 = eqn (Bx2-0413 ∷ CS03 ∷ []) (CS03 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 c4)
  q334 : Ws → Eqn
  q334 c4 = eqn (Sw23 ∷ CS03 ∷ []) (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 (lit c4))

-- auto BOX(0;1234) | CS14 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 c4 = derive (Bx3-0412 ∷ CS02 ∷ []) (CS02 ∷ Bx3-0412 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q329 c4) ∷
   rw 2 (q332 c4) ∷
   rw 1 (q333 c4) ∷
   rw 0 (q334 c4) ∷
   rw 1 (q331 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q335 : Ws → Eqn
  q335 c4 = eqn (Bx2-0413 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 c4)

-- auto BOX(0;1234) | CSd14 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 c4 = derive (Bx3-0412 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx3-0412 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q329 c4) ∷
   rw 2 (q219 c4) ∷
   rw 1 (q335 c4) ∷
   rw 0 (q221 c4) ∷
   rw 1 (q331 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q336 : Ws → Eqn
  q336 c4 = eqn (Sw12 ∷ Bx3-4021 ∷ []) (Bx3-4012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4021⟩ (lit c4))
  q337 : Ws → Eqn
  q337 c4 = eqn (Bx3-4012 ∷ []) (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4)
  q338 : Ws → Eqn
  q338 c4 = eqn (Sw12 ∷ Bx3-4102 ∷ []) (Bx3-4201 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4102⟩ (lit c4))

-- sym23 @0314203241: 5 steps
lem-sym23-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-sym23-at0314203241 c4 = derive (Bx3-4021 ∷ []) (Bx3-4201 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q336 c4) ∷
   rw 1 (q337 c4) ∷
   rw 0 (q338 c4) ∷
   rw 1 (q26 c4) ∷ []) Eq.refl

private
  q339 : Ws → Eqn
  q339 c4 = eqn (Sw01 ∷ Bx3-4120 ∷ []) (Bx3-4021 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4120⟩ (lit c4))
  q340 : Ws → Eqn
  q340 c4 = eqn (Bx3-4021 ∷ []) (Bx3-4201 ∷ []) (lem-sym23-at0314203241 c4)
  q341 : Ws → Eqn
  q341 c4 = eqn (Sw01 ∷ Bx3-4201 ∷ []) (Bx3-4210 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4201⟩ (lit c4))

-- sym23 @0314213240: 5 steps
lem-sym23-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ []) ⟫ʷ
lem-sym23-at0314213240 c4 = derive (Bx3-4120 ∷ []) (Bx3-4210 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q339 c4) ∷
   rw 1 (q340 c4) ∷
   rw 0 (q341 c4) ∷
   rw 1 (q39 c4) ∷ []) Eq.refl

private
  q342 : Ws → Eqn
  q342 c4 = eqn (Sw01 ∷ Toff014 ∷ []) (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 (lit c4))
  q343 : Ws → Eqn
  q343 c4 = eqn (Sw01 ∷ Bx3-4102 ∷ []) (Bx3-4012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4102⟩ (lit c4))
  q344 : Ws → Eqn
  q344 c4 = eqn (Toff104 ∷ Bx3-4012 ∷ Toff104 ∷ []) (Bx3-4012 ∷ CCZ024 ∷ []) (lem-T312-beta-at0314203142 c4)
  q345 : Ws → Eqn
  q345 c4 = eqn (Sw01 ∷ Bx3-4012 ∷ []) (Bx3-4102 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4012⟩ (lit c4))

-- T312-beta @0314213042: 8 steps
lem-T312-beta-at0314213042 : Ws → ⟪ (Toff014 ∷ Bx3-4102 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ CCZ124 ∷ []) ⟫ʷ
lem-T312-beta-at0314213042 c4 = derive (Toff014 ∷ Bx3-4102 ∷ Toff014 ∷ []) (Bx3-4102 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q342 c4) ∷
   rw 2 (q343 c4) ∷
   rw 3 (q342 c4) ∷
   rw 1 (q344 c4) ∷
   rw 0 (q345 c4) ∷
   rw 1 (q328 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q346 : Ws → Eqn
  q346 c4 = eqn (Sw12 ∷ Toff024 ∷ []) (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 (lit c4))
  q347 : Ws → Eqn
  q347 c4 = eqn (Sw12 ∷ Bx3-4201 ∷ []) (Bx3-4102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4201⟩ (lit c4))
  q348 : Ws → Eqn
  q348 c4 = eqn (Toff014 ∷ Bx3-4102 ∷ Toff014 ∷ []) (Bx3-4102 ∷ CCZ124 ∷ []) (lem-T312-beta-at0314213042 c4)
  q349 : Ws → Eqn
  q349 c4 = eqn (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) (wl0078 (lit c4))

-- T312-beta @03143041: 8 steps
lem-T312-beta-at03143041 : Ws → ⟪ (Toff024 ∷ Bx3-4201 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ CCZ124 ∷ []) ⟫ʷ
lem-T312-beta-at03143041 c4 = derive (Toff024 ∷ Bx3-4201 ∷ Toff024 ∷ []) (Bx3-4201 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q346 c4) ∷
   rw 2 (q347 c4) ∷
   rw 3 (q346 c4) ∷
   rw 1 (q348 c4) ∷
   rw 0 (q338 c4) ∷
   rw⁻ 1 (q349 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q350 : Ws → Eqn
  q350 c4 = eqn (Sw01 ∷ Toff124 ∷ []) (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 (lit c4))
  q351 : Ws → Eqn
  q351 c4 = eqn (Sw01 ∷ Bx3-4210 ∷ []) (Bx3-4201 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4210⟩ (lit c4))
  q352 : Ws → Eqn
  q352 c4 = eqn (Toff024 ∷ Bx3-4201 ∷ Toff024 ∷ []) (Bx3-4201 ∷ CCZ124 ∷ []) (lem-T312-beta-at03143041 c4)

-- T312-beta @03143140: 8 steps
lem-T312-beta-at03143140 : Ws → ⟪ (Toff124 ∷ Bx3-4210 ∷ Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ CCZ024 ∷ []) ⟫ʷ
lem-T312-beta-at03143140 c4 = derive (Toff124 ∷ Bx3-4210 ∷ Toff124 ∷ []) (Bx3-4210 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q350 c4) ∷
   rw 2 (q351 c4) ∷
   rw 3 (q350 c4) ∷
   rw 1 (q352 c4) ∷
   rw 0 (q341 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q353 : Ws → Eqn
  q353 c4 = eqn (Bx3-4102 ∷ []) (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4)
  q354 : Ws → Eqn
  q354 c4 = eqn (Sw12 ∷ Bx3-4012 ∷ []) (Bx3-4021 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4012⟩ (lit c4))

-- sym23 @03143041: 5 steps
lem-sym23-at03143041 : Ws → ⟪ (Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-sym23-at03143041 c4 = derive (Bx3-4201 ∷ []) (Bx3-4021 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q347 c4) ∷
   rw 1 (q353 c4) ∷
   rw 0 (q354 c4) ∷
   rw 1 (q26 c4) ∷ []) Eq.refl

private
  q355 : Ws → Eqn
  q355 c4 = eqn (Bx3-4201 ∷ []) (Bx3-4021 ∷ []) (lem-sym23-at03143041 c4)
  q356 : Ws → Eqn
  q356 c4 = eqn (Sw01 ∷ Bx3-4021 ∷ []) (Bx3-4120 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4021⟩ (lit c4))

-- sym23 @03143140: 5 steps
lem-sym23-at03143140 : Ws → ⟪ (Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-sym23-at03143140 c4 = derive (Bx3-4210 ∷ []) (Bx3-4120 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q351 c4) ∷
   rw 1 (q355 c4) ∷
   rw 0 (q356 c4) ∷
   rw 1 (q39 c4) ∷ []) Eq.refl

private
  q357 : Ws → Eqn
  q357 c4 = eqn (Sw23 ∷ Bx0-1324 ∷ []) (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4))
  q358 : Ws → Eqn
  q358 c4 = eqn (Bx0-1234 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241 c4)
  q359 : Ws → Eqn
  q359 c4 = eqn (Sw23 ∷ Bx0-1234 ∷ []) (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4))

-- auto BOX(0;1234) | CCZ241 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at2332 c4 = derive (Bx0-1324 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q357 c4) ∷
   rw 2 (q112 c4) ∷
   rw 1 (q358 c4) ∷
   rw 0 (q123 c4) ∷
   rw 1 (q359 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q360 : Ws → Eqn
  q360 c4 = eqn (Sw34 ∷ Bx0-1423 ∷ []) (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4))
  q361 : Ws → Eqn
  q361 c4 = eqn (CCZ134 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ134 ∷ []) (wl0154 (lit c4))
  q362 : Ws → Eqn
  q362 c4 = eqn (Bx0-1324 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at2332 c4)
  q363 : Ws → Eqn
  q363 c4 = eqn (Sw34 ∷ Bx0-1324 ∷ []) (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4))

-- auto BOX(0;1234) | CCZ241 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at243243 : Ws → ⟪ (Bx0-1423 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at243243 c4 = derive (Bx0-1423 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q360 c4) ∷
   rw⁻ 2 (q361 c4) ∷
   rw 1 (q362 c4) ∷
   rw⁻ 0 (q361 c4) ∷
   rw 1 (q363 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q364 : Ws → Eqn
  q364 c4 = eqn (Sw01 ∷ Bx1-0423 ∷ []) (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4))
  q365 : Ws → Eqn
  q365 c4 = eqn (Bx0-1423 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at243243 c4)
  q366 : Ws → Eqn
  q366 c4 = eqn (Sw01 ∷ Bx0-1423 ∷ []) (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4))

-- auto BOX(0;1234) | CCZ241 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0110243243 c4 = derive (Bx1-0423 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q364 c4) ∷
   rw 2 (q254 c4) ∷
   rw 1 (q365 c4) ∷
   rw 0 (q256 c4) ∷
   rw 1 (q366 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q367 : Ws → Eqn
  q367 c4 = eqn (Sw12 ∷ Bx2-0413 ∷ []) (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4))
  q368 : Ws → Eqn
  q368 c4 = eqn (Bx1-0423 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0110243243 c4)
  q369 : Ws → Eqn
  q369 c4 = eqn (Sw12 ∷ Bx1-0423 ∷ []) (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4))

-- auto BOX(0;1234) | CCZ241 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0210243143 c4 = derive (Bx2-0413 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q367 c4) ∷
   rw 2 (q257 c4) ∷
   rw 1 (q368 c4) ∷
   rw 0 (q257 c4) ∷
   rw 1 (q369 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q370 : Ws → Eqn
  q370 c4 = eqn (Bx2-0413 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0210243143 c4)

-- auto BOX(0;1234) | CCZ241 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 c4 = derive (Bx3-0412 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0412 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q329 c4) ∷
   rw 2 (q259 c4) ∷
   rw 1 (q370 c4) ∷
   rw 0 (q261 c4) ∷
   rw 1 (q331 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q371 : Ws → Eqn
  q371 c4 = eqn (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (CCZ124 ∷ []) (lem-SB2-at011220 c4)
  q372 : Ws → Eqn
  q372 c4 = eqn (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ []) (wl0612 (lit c4))
  q373 : Ws → Eqn
  q373 c4 = eqn (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ []) (wl0613 (lit c4))
  q374 : Ws → Eqn
  q374 c4 = eqn (Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ []) (lem-F0 c4)
  q375 : Ws → Eqn
  q375 c4 = eqn (Toff214 ∷ Toff214 ∷ []) [] (wl0244 (lit c4))
  q376 : Ws → Eqn
  q376 c4 = eqn (Bx3-0412 ∷ []) (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4)
  q377 : Ws → Eqn
  q377 c4 = eqn (Bx3-4102 ∷ []) (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4)
  q378 : Ws → Eqn
  q378 c4 = eqn (Toff214 ∷ Bx3-4120 ∷ Toff214 ∷ []) (Bx3-4120 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314213240 c4)
  q379 : Ws → Eqn
  q379 c4 = eqn (Bx3-4120 ∷ []) (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4)
  q380 : Ws → Eqn
  q380 c4 = eqn (Bx3-4012 ∷ []) (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4)
  q381 : Ws → Eqn
  q381 c4 = eqn (Bx3-0412 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4)
  q382 : Ws → Eqn
  q382 c4 = eqn (Bx3-0412 ∷ CS02 ∷ []) (CS02 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 c4)
  q383 : Ws → Eqn
  q383 c4 = eqn (Bx3-0412 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 c4)
  q384 : Ws → Eqn
  q384 c4 = eqn (Toff124 ∷ Toff124 ∷ []) [] (wl0614 (lit c4))
  q385 : Ws → Eqn
  q385 c4 = eqn (Bx3-4120 ∷ []) (Bx3-4210 ∷ []) (lem-sym23-at0314213240 c4)
  q386 : Ws → Eqn
  q386 c4 = eqn (Toff124 ∷ Bx3-4210 ∷ Toff124 ∷ []) (Bx3-4210 ∷ CCZ024 ∷ []) (lem-T312-beta-at03143140 c4)
  q387 : Ws → Eqn
  q387 c4 = eqn (Bx3-4210 ∷ []) (Bx3-4120 ∷ []) (lem-sym23-at03143140 c4)
  q388 : Ws → Eqn
  q388 c4 = eqn (Bx3-0412 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 c4)
  q389 : Ws → Eqn
  q389 c4 = eqn (CCZ024 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4)
  q390 : Ws → Eqn
  q390 c4 = eqn (CS02⁻ ∷ Toff124 ∷ []) (Toff124 ∷ CS02⁻ ∷ []) (wp0264 c4)
  q391 : Ws → Eqn
  q391 c4 = eqn (CCZ014 ∷ Toff124 ∷ []) (Toff124 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0265 c4)

-- F1 rel-266 [nf of rhs]: 55 steps
lem-F1-rel-266-nf-of-rhs : Ws → ⟪ (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-F1-rel-266-nf-of-rhs c4 = derive (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  (rw 1 (q371 c4) ∷
   rw 5 (q371 c4) ∷
   rw 10 (q371 c4) ∷
   rw 14 (q371 c4) ∷
   rw 0 (q372 c4) ∷
   rw 1 (q373 c4) ∷
   rw 3 (q373 c4) ∷
   rw 4 (q372 c4) ∷
   rw 2 (q374 c4) ∷
   re 2 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   re 4 1 (CS02 ∷ []) ∷
   re 6 1 (CS02⁻ ∷ []) ∷
   rw⁻ 2 (q375 c4) ∷
   rw 4 (q376 c4) ∷
   rw 4 (q337 c4) ∷
   rw 4 (q377 c4) ∷
   rw 3 (q378 c4) ∷
   rw 3 (q379 c4) ∷
   rw 3 (q353 c4) ∷
   rw 3 (q380 c4) ∷
   rw 3 (q381 c4) ∷
   rw 4 (q382 c4) ∷
   rw⁻ 5 (q375 c4) ∷
   rw 7 (q376 c4) ∷
   rw 7 (q337 c4) ∷
   rw 7 (q377 c4) ∷
   rw 6 (q378 c4) ∷
   rw 6 (q379 c4) ∷
   rw 6 (q353 c4) ∷
   rw 6 (q380 c4) ∷
   rw 6 (q381 c4) ∷
   rw 7 (q383 c4) ∷
   rw⁻ 8 (q384 c4) ∷
   rw 10 (q376 c4) ∷
   rw 10 (q337 c4) ∷
   rw 10 (q377 c4) ∷
   rw 10 (q385 c4) ∷
   rw 9 (q386 c4) ∷
   rw 9 (q387 c4) ∷
   rw 9 (q379 c4) ∷
   rw 9 (q353 c4) ∷
   rw 9 (q380 c4) ∷
   rw 9 (q388 c4) ∷
   rw⁻ 10 (q375 c4) ∷
   rw 12 (q376 c4) ∷
   rw 12 (q337 c4) ∷
   rw 12 (q377 c4) ∷
   rw 11 (q378 c4) ∷
   rw 11 (q379 c4) ∷
   rw 11 (q353 c4) ∷
   rw 11 (q380 c4) ∷
   rw 11 (q381 c4) ∷
   rw 9 (q389 c4) ∷
   rw 7 (q390 c4) ∷
   rw 6 (q391 c4) ∷ []) Eq.refl

private
  q392 : Ws → Eqn
  q392 c4 = eqn (Sb1-0-42-3 ∷ []) (Sb3-0-42-1 ∷ []) (lem-F0-at1221 c4)
  q393 : Ws → Eqn
  q393 c4 = eqn (Sw01 ∷ Sb3-0-42-1 ∷ []) (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ (lit c4))

-- F0 @011220: 5 steps
lem-F0-at011220 : Ws → ⟪ (Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ []) ⟫ʷ
lem-F0-at011220 c4 = derive (Sb0-1-42-3 ∷ []) (Sb3-1-42-0 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q326 c4) ∷
   rw 1 (q392 c4) ∷
   rw 0 (q393 c4) ∷
   rw 1 (q39 c4) ∷ []) Eq.refl

private
  q394 : Ws → Eqn
  q394 c4 = eqn (Sw12 ∷ Bx3-0421 ∷ []) (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ (lit c4))

-- sym12 @0310243241: 5 steps
lem-sym12-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-sym12-at0310243241 c4 = derive (Bx3-0421 ∷ []) (Bx3-4021 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q394 c4) ∷
   rw 1 (q376 c4) ∷
   rw 0 (q354 c4) ∷
   rw 1 (q26 c4) ∷ []) Eq.refl

private
  q395 : Ws → Eqn
  q395 c4 = eqn (Sw01 ∷ Bx3-1420 ∷ []) (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ (lit c4))
  q396 : Ws → Eqn
  q396 c4 = eqn (Bx3-0421 ∷ []) (Bx3-4021 ∷ []) (lem-sym12-at0310243241 c4)

-- sym12 @03243240: 5 steps
lem-sym12-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-sym12-at03243240 c4 = derive (Bx3-1420 ∷ []) (Bx3-4120 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q395 c4) ∷
   rw 1 (q396 c4) ∷
   rw 0 (q356 c4) ∷
   rw 1 (q39 c4) ∷ []) Eq.refl

private
  q397 : Ws → Eqn
  q397 c4 = eqn (Sw12 ∷ Bx3-4120 ∷ []) (Bx3-4210 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4120⟩ (lit c4))

-- sym34 @03143041: 5 steps
lem-sym34-at03143041 : Ws → ⟪ (Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ []) ⟫ʷ
lem-sym34-at03143041 c4 = derive (Bx3-4201 ∷ []) (Bx3-4210 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q347 c4) ∷
   rw 1 (q377 c4) ∷
   rw 0 (q397 c4) ∷
   rw 1 (q26 c4) ∷ []) Eq.refl

private
  q398 : Ws → Eqn
  q398 c4 = eqn (Bx3-4201 ∷ []) (Bx3-4210 ∷ []) (lem-sym34-at03143041 c4)

-- sym34 @03143140: 5 steps
lem-sym34-at03143140 : Ws → ⟪ (Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-sym34-at03143140 c4 = derive (Bx3-4210 ∷ []) (Bx3-4201 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q351 c4) ∷
   rw 1 (q398 c4) ∷
   rw 0 (q351 c4) ∷
   rw 1 (q39 c4) ∷ []) Eq.refl

private
  q399 : Ws → Eqn
  q399 c4 = eqn (Sw12 ∷ Bx3-0412 ∷ []) (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ (lit c4))

-- sym12 @0314203241: 5 steps
lem-sym12-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-sym12-at0314203241 c4 = derive (Bx3-4021 ∷ []) (Bx3-0421 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q336 c4) ∷
   rw 1 (q380 c4) ∷
   rw 0 (q399 c4) ∷
   rw 1 (q26 c4) ∷ []) Eq.refl

private
  q400 : Ws → Eqn
  q400 c4 = eqn (Bx3-4021 ∷ []) (Bx3-0421 ∷ []) (lem-sym12-at0314203241 c4)
  q401 : Ws → Eqn
  q401 c4 = eqn (Sw01 ∷ Bx3-0421 ∷ []) (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ (lit c4))

-- sym12 @0314213240: 5 steps
lem-sym12-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-sym12-at0314213240 c4 = derive (Bx3-4120 ∷ []) (Bx3-1420 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q339 c4) ∷
   rw 1 (q400 c4) ∷
   rw 0 (q401 c4) ∷
   rw 1 (q39 c4) ∷ []) Eq.refl

-- auto BOX(0;1234) | CCZ231 @0310243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx3-0421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243241 c4 = derive (Bx3-0421 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0421 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q394 c4) ∷
   rw 2 (q131 c4) ∷
   rw 1 (q381 c4) ∷
   rw 0 (q134 c4) ∷
   rw 1 (q399 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q402 : Ws → Eqn
  q402 c4 = eqn (Bx3-0421 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243241 c4)

-- auto BOX(0;1234) | CCZ231 @03243240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 : Ws → ⟪ (Bx3-1420 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 c4 = derive (Bx3-1420 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-1420 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q395 c4) ∷
   rw 2 (q116 c4) ∷
   rw 1 (q402 c4) ∷
   rw 0 (q328 c4) ∷
   rw 1 (q401 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

-- auto BOX(0;1234) | CS14 @0310243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Bx3-0421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243241 c4 = derive (Bx3-0421 ∷ CS01 ∷ []) (CS01 ∷ Bx3-0421 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q394 c4) ∷
   rw 2 (q68 c4) ∷
   rw 1 (q382 c4) ∷
   rw 0 (q66 c4) ∷
   rw 1 (q399 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q403 : Ws → Eqn
  q403 c4 = eqn (CS01 ∷ Sw01 ∷ []) (Sw01 ∷ CS01 ∷ []) (wl0132 (lit c4))
  q404 : Ws → Eqn
  q404 c4 = eqn (Bx3-0421 ∷ CS01 ∷ []) (CS01 ∷ Bx3-0421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243241 c4)

-- auto BOX(0;1234) | CS14 @03243240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14-at03243240 : Ws → ⟪ (Bx3-1420 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14-at03243240 c4 = derive (Bx3-1420 ∷ CS01 ∷ []) (CS01 ∷ Bx3-1420 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q395 c4) ∷
   rw⁻ 2 (q403 c4) ∷
   rw 1 (q404 c4) ∷
   rw⁻ 0 (q403 c4) ∷
   rw 1 (q401 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

-- auto BOX(0;1234) | CSd14 @0310243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Bx3-0421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243241 c4 = derive (Bx3-0421 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Bx3-0421 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q394 c4) ∷
   rw 2 (q38 c4) ∷
   rw 1 (q383 c4) ∷
   rw 0 (q34 c4) ∷
   rw 1 (q399 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q405 : Ws → Eqn
  q405 c4 = eqn (CS01⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS01⁻ ∷ []) (wl0133 (lit c4))
  q406 : Ws → Eqn
  q406 c4 = eqn (Bx3-0421 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Bx3-0421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243241 c4)

-- auto BOX(0;1234) | CSd14 @03243240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at03243240 : Ws → ⟪ (Bx3-1420 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at03243240 c4 = derive (Bx3-1420 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Bx3-1420 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q395 c4) ∷
   rw⁻ 2 (q405 c4) ∷
   rw 1 (q406 c4) ∷
   rw⁻ 0 (q405 c4) ∷
   rw 1 (q401 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q407 : Ws → Eqn
  q407 c4 = eqn (CCZ234 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ234 ∷ []) (wl0086 (lit c4))
  q408 : Ws → Eqn
  q408 c4 = eqn (Bx0-1234 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243 c4)

-- auto BOX(0;1234) | CCZ243 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at2332 c4 = derive (Bx0-1324 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q357 c4) ∷
   rw⁻ 2 (q407 c4) ∷
   rw 1 (q408 c4) ∷
   rw⁻ 0 (q407 c4) ∷
   rw 1 (q359 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q409 : Ws → Eqn
  q409 c4 = eqn (Bx0-1324 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at2332 c4)

-- auto BOX(0;1234) | CCZ243 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at243243 : Ws → ⟪ (Bx0-1423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at243243 c4 = derive (Bx0-1423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q360 c4) ∷
   rw⁻ 2 (q25 c4) ∷
   rw 1 (q409 c4) ∷
   rw⁻ 0 (q25 c4) ∷
   rw 1 (q363 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q410 : Ws → Eqn
  q410 c4 = eqn (Bx0-1423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at243243 c4)

-- auto BOX(0;1234) | CCZ243 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0110243243 c4 = derive (Bx1-0423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q364 c4) ∷
   rw 2 (q104 c4) ∷
   rw 1 (q410 c4) ∷
   rw 0 (q104 c4) ∷
   rw 1 (q366 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q411 : Ws → Eqn
  q411 c4 = eqn (Bx1-0423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0110243243 c4)

-- auto BOX(0;1234) | CCZ243 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0210243143 c4 = derive (Bx2-0413 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q367 c4) ∷
   rw⁻ 2 (q120 c4) ∷
   rw 1 (q411 c4) ∷
   rw⁻ 0 (q108 c4) ∷
   rw 1 (q369 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q412 : Ws → Eqn
  q412 c4 = eqn (Bx2-0413 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0210243143 c4)

-- auto BOX(0;1234) | CCZ243 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0310243142 c4 = derive (Bx3-0412 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-0412 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q329 c4) ∷
   rw 2 (q123 c4) ∷
   rw 1 (q412 c4) ∷
   rw 0 (q112 c4) ∷
   rw 1 (q331 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q413 : Ws → Eqn
  q413 c4 = eqn (Bx3-0412 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0310243142 c4)

-- auto BOX(0;1234) | CCZ243 @0310243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx3-0421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0310243241 c4 = derive (Bx3-0421 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-0421 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q394 c4) ∷
   rw⁻ 2 (q349 c4) ∷
   rw 1 (q413 c4) ∷
   rw⁻ 0 (q349 c4) ∷
   rw 1 (q399 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q414 : Ws → Eqn
  q414 c4 = eqn (Bx3-0421 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-0421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0310243241 c4)

-- auto BOX(0;1234) | CCZ243 @03243240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at03243240 : Ws → ⟪ (Bx3-1420 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at03243240 c4 = derive (Bx3-1420 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-1420 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q395 c4) ∷
   rw 2 (q328 c4) ∷
   rw 1 (q414 c4) ∷
   rw 0 (q116 c4) ∷
   rw 1 (q401 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q415 : Ws → Eqn
  q415 c4 = eqn (Bx3-0421 ∷ []) (Bx3-0412 ∷ []) (lem-sym34-at0310243241 c4)
  q416 : Ws → Eqn
  q416 c4 = eqn (Sw01 ∷ Bx3-0412 ∷ []) (Bx3-1402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0412⟩ (lit c4))

-- sym34 @03243240: 5 steps
lem-sym34-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ []) ⟫ʷ
lem-sym34-at03243240 c4 = derive (Bx3-1420 ∷ []) (Bx3-1402 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q395 c4) ∷
   rw 1 (q415 c4) ∷
   rw 0 (q416 c4) ∷
   rw 1 (q39 c4) ∷ []) Eq.refl

private
  q417 : Ws → Eqn
  q417 c4 = eqn (Sw34 ∷ Toff214 ∷ []) (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 (lit c4))
  q418 : Ws → Eqn
  q418 c4 = eqn (Toff213 ∷ Bx0-1324 ∷ Toff213 ∷ []) (Bx0-1324 ∷ CCZ134 ∷ []) (lem-T312-beta-at2332 c4)

-- T312-beta @243243: 8 steps
lem-T312-beta-at243243 : Ws → ⟪ (Toff214 ∷ Bx0-1423 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ134 ∷ []) ⟫ʷ
lem-T312-beta-at243243 c4 = derive (Toff214 ∷ Bx0-1423 ∷ Toff214 ∷ []) (Bx0-1423 ∷ CCZ134 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q417 c4) ∷
   rw 2 (q360 c4) ∷
   rw 3 (q417 c4) ∷
   rw 1 (q418 c4) ∷
   rw 0 (q363 c4) ∷
   rw⁻ 1 (q361 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q419 : Ws → Eqn
  q419 c4 = eqn (Sw01 ∷ Toff204 ∷ []) (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 (lit c4))
  q420 : Ws → Eqn
  q420 c4 = eqn (Toff214 ∷ Bx0-1423 ∷ Toff214 ∷ []) (Bx0-1423 ∷ CCZ134 ∷ []) (lem-T312-beta-at243243 c4)

-- T312-beta @0110243243: 8 steps
lem-T312-beta-at0110243243 : Ws → ⟪ (Toff204 ∷ Bx1-0423 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CCZ034 ∷ []) ⟫ʷ
lem-T312-beta-at0110243243 c4 = derive (Toff204 ∷ Bx1-0423 ∷ Toff204 ∷ []) (Bx1-0423 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q419 c4) ∷
   rw 2 (q364 c4) ∷
   rw 3 (q419 c4) ∷
   rw 1 (q420 c4) ∷
   rw 0 (q366 c4) ∷
   rw 1 (q256 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q421 : Ws → Eqn
  q421 c4 = eqn (Sw12 ∷ Toff104 ∷ []) (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 (lit c4))
  q422 : Ws → Eqn
  q422 c4 = eqn (Toff204 ∷ Bx1-0423 ∷ Toff204 ∷ []) (Bx1-0423 ∷ CCZ034 ∷ []) (lem-T312-beta-at0110243243 c4)

-- T312-beta @0210243143: 8 steps
lem-T312-beta-at0210243143 : Ws → ⟪ (Toff104 ∷ Bx2-0413 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ034 ∷ []) ⟫ʷ
lem-T312-beta-at0210243143 c4 = derive (Toff104 ∷ Bx2-0413 ∷ Toff104 ∷ []) (Bx2-0413 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q421 c4) ∷
   rw 2 (q367 c4) ∷
   rw 3 (q421 c4) ∷
   rw 1 (q422 c4) ∷
   rw 0 (q369 c4) ∷
   rw 1 (q257 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q423 : Ws → Eqn
  q423 c4 = eqn (Sw23 ∷ Toff104 ∷ []) (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 (lit c4))
  q424 : Ws → Eqn
  q424 c4 = eqn (Toff104 ∷ Bx2-0413 ∷ Toff104 ∷ []) (Bx2-0413 ∷ CCZ034 ∷ []) (lem-T312-beta-at0210243143 c4)

-- T312-beta @0310243142: 8 steps
lem-T312-beta-at0310243142 : Ws → ⟪ (Toff104 ∷ Bx3-0412 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CCZ024 ∷ []) ⟫ʷ
lem-T312-beta-at0310243142 c4 = derive (Toff104 ∷ Bx3-0412 ∷ Toff104 ∷ []) (Bx3-0412 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q423 c4) ∷
   rw 2 (q329 c4) ∷
   rw 3 (q423 c4) ∷
   rw 1 (q424 c4) ∷
   rw 0 (q331 c4) ∷
   rw 1 (q261 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q425 : Ws → Eqn
  q425 c4 = eqn (Sw01 ∷ Bx3-1402 ∷ []) (Bx3-0412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1402⟩ (lit c4))
  q426 : Ws → Eqn
  q426 c4 = eqn (Toff104 ∷ Bx3-0412 ∷ Toff104 ∷ []) (Bx3-0412 ∷ CCZ024 ∷ []) (lem-T312-beta-at0310243142 c4)

-- T312-beta @03243042: 8 steps
lem-T312-beta-at03243042 : Ws → ⟪ (Toff014 ∷ Bx3-1402 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ CCZ124 ∷ []) ⟫ʷ
lem-T312-beta-at03243042 c4 = derive (Toff014 ∷ Bx3-1402 ∷ Toff014 ∷ []) (Bx3-1402 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q342 c4) ∷
   rw 2 (q425 c4) ∷
   rw 3 (q342 c4) ∷
   rw 1 (q426 c4) ∷
   rw 0 (q416 c4) ∷
   rw 1 (q328 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q427 : Ws → Eqn
  q427 c4 = eqn (Bx3-0412 ∷ []) (Bx3-0421 ∷ []) (lem-sym34-at0310243142 c4)

-- sym34 @03243042: 5 steps
lem-sym34-at03243042 : Ws → ⟪ (Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-sym34-at03243042 c4 = derive (Bx3-1402 ∷ []) (Bx3-1420 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q425 c4) ∷
   rw 1 (q427 c4) ∷
   rw 0 (q401 c4) ∷
   rw 1 (q39 c4) ∷ []) Eq.refl

private
  q428 : Ws → Eqn
  q428 c4 = eqn (CCZ123 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ123 ∷ []) (wl0113 (lit c4))
  q429 : Ws → Eqn
  q429 c4 = eqn (Bx0-1234 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123 c4)

-- auto BOX(0;1234) | CCZ123 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at2332 c4 = derive (Bx0-1324 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q357 c4) ∷
   rw⁻ 2 (q428 c4) ∷
   rw 1 (q429 c4) ∷
   rw⁻ 0 (q428 c4) ∷
   rw 1 (q359 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q430 : Ws → Eqn
  q430 c4 = eqn (Bx0-1324 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at2332 c4)

-- auto BOX(0;1234) | CCZ123 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at243243 : Ws → ⟪ (Bx0-1423 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at243243 c4 = derive (Bx0-1423 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q360 c4) ∷
   rw 2 (q129 c4) ∷
   rw 1 (q430 c4) ∷
   rw 0 (q127 c4) ∷
   rw 1 (q363 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q431 : Ws → Eqn
  q431 c4 = eqn (Bx0-1423 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at243243 c4)

-- auto BOX(0;1234) | CCZ123 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0110243243 c4 = derive (Bx1-0423 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q364 c4) ∷
   rw 2 (q328 c4) ∷
   rw 1 (q431 c4) ∷
   rw 0 (q116 c4) ∷
   rw 1 (q366 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q432 : Ws → Eqn
  q432 c4 = eqn (Bx1-0423 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0110243243 c4)

-- auto BOX(0;1234) | CCZ123 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0210243143 c4 = derive (Bx2-0413 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q367 c4) ∷
   rw 2 (q134 c4) ∷
   rw 1 (q432 c4) ∷
   rw 0 (q131 c4) ∷
   rw 1 (q369 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q433 : Ws → Eqn
  q433 c4 = eqn (Bx2-0413 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0210243143 c4)

-- auto BOX(0;1234) | CCZ123 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0310243142 c4 = derive (Bx3-0412 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx3-0412 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q329 c4) ∷
   rw 2 (q239 c4) ∷
   rw 1 (q433 c4) ∷
   rw 0 (q239 c4) ∷
   rw 1 (q331 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q434 : Ws → Eqn
  q434 c4 = eqn (Bx3-0412 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0310243142 c4)

-- auto BOX(0;1234) | CCZ123 @0310243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx3-0421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0310243241 c4 = derive (Bx3-0421 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0421 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q394 c4) ∷
   rw 2 (q131 c4) ∷
   rw 1 (q434 c4) ∷
   rw 0 (q134 c4) ∷
   rw 1 (q399 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q435 : Ws → Eqn
  q435 c4 = eqn (Bx3-0421 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0310243241 c4)

-- auto BOX(0;1234) | CCZ123 @03243240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at03243240 : Ws → ⟪ (Bx3-1420 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at03243240 c4 = derive (Bx3-1420 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-1420 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 1 (q395 c4) ∷
   rw 2 (q116 c4) ∷
   rw 1 (q435 c4) ∷
   rw 0 (q328 c4) ∷
   rw 1 (q401 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

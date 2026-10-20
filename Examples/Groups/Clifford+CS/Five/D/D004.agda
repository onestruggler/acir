{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D004 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0011 ; wl0015 ; wl0021 ; wl0024 ; wl0025 ; wl0031 ; wl0033 ; wl0035 ; wl0036 ; wl0044 ; wl0047 ; wl0052 ; wl0056 ; wl0057 ; wl0058 ; wl0062 ; wl0065 ; wl0067 ; wl0068 ; wl0076 ; wl0078 ; wl0085 ; wl0091 ; wl0097 ; wl0099 ; wl0108 ; wl0132 ; wl0133 ; wl0138 ; wl0139 ; wl0212 ; wl0218 ; wl0257 ; wl0296 ; wl0299 ; wl0300 ; wl0301 ; wl0302 ; wl0303 ; wl0304 ; wl0306 ; wl0307 ; wl0308 ; wl0309 ; wl0310 ; wl0311 ; wl0312 ; wl0313 ; wl0314 ; wl0317 ; wl0318 ; wl0325 ; wl0326 ; wl0327 ; wl0328 ; wl0329 ; wl0330 ; wl0331 ; wl0332 ; wl0333 ; wl0334 ; wl0335 ; wl0336 ; wl0337 ; wl0338 ; wl0339 ; wl0340 ; wl0341 ; wl0342 ; wl0343 ; wl0344 ; wl0345 ; wl0346 ; wl0347 ; wl0348 ; wl0349 ; wl0350 ; wl0351 ; wl0352 ; wl0353 ; wl0354 ; wl0355 ; wl0356 ; wl0357 ; wl0358 ; wl0359 ; wl0360 ; wp0094 ; wp0095 ; wp0096 ; wp0097 ; wp0098 ; wp0099 ; wp0100 ; wp0101 ; wp0102 ; wp0103 ; wp0104 ; wp0105 ; wp0106 ; wp0107 ; wp0108 ; wp0109 ; wp0110 ; wp0111 ; wp0112 ; wp0113 ; wp0114 ; wp0115 ; wp0116 ; wp0117 ; wp0118 ; wp0119 ; wp0120 ; wp0121 ; wp0122)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-BOXd-BOX ; lem-CS20-beta-c ; lem-CS20-beta-ci ; lem-CSd12-beta ; lem-CX23-beta ; lem-F0d ; lem-K0-pass-c ; lem-K0-pass-ci ; lem-beta-T-at2332 ; lem-c124-beta ; lem-c124-beta-at0310213442 ; lem-sym12 ; lem-sym12-at1221 ; lem-sym12-at132132 ; lem-sym23 ; lem-sym23-at1221 ; lem-sym34 ; lem-sym34-at1221 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at2332 ; lem-CS12-beta-at243243 ; lem-CS20-beta-c-at1221 ; lem-CSd12-beta-at243243 ; lem-SBsymd ; lem-auto-BOX⟨0·1234⟩-∣-CS14 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14 ; lem-beta-T-at122331 ; lem-c124-beta-at2332 ; lem-sym12-at2332 ; lem-sym12-at233442 ; lem-sym23-at021021 ; lem-sym23-at12213443 ; lem-sym23-at122331 ; lem-sym23-at12243143 ; lem-sym23-at13213442 ; lem-sym23-at13243142 ; lem-sym23-at2332 ; lem-sym23-at243243 ; lem-sym23-at3443 ; lem-sym34-at12213443 ; lem-sym34-at122331 ; lem-sym34-at12233441 ; lem-sym34-at13213442 ; lem-sym34-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-CS12-beta-at12243143 ; lem-SBsym-at0113203442 ; lem-T312-beta-at12233441 ; lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·1234⟩ ; lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332 ; lem-auto-BOX⟨0·1234⟩-∣-K0 ; lem-auto-BOX⟨0·1234⟩-∣-Kd0 ; lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ ; lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ ; lem-sym23-at02102331)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-BOX⟨0·3412⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-TOFF301 ; lem-nat-3-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-2-BOX⟨0·2413⟩ ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF201 ; lem-nat-3-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ014 ; lem-nat-0-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-TOFF413 ; lem-nat-1-BOX⟨0·1234⟩ ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-TOFF401 ; lem-nat-2-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨0·1324⟩ ; lem-nat-0-BOX⟨1·2304⟩ ; lem-nat-1-BOX⟨1·0324⟩ ; lem-nat-1-CS01 ; lem-nat-1-CS02 ; lem-nat-2-CS12 ; lem-nat-2-CS13)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-1-CSd02 ; lem-nat-2-BOX⟨0·1432⟩ ; lem-nat-2-CS02 ; lem-nat-2-CSd02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-2-TOFF403 ; lem-nat-3-CS23 ; lem-nat-3-CS24 ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨1·0324⟩ ; lem-nat-1-BOX⟨2·0314⟩ ; lem-nat-1-CSd01 ; lem-nat-3-CS04 ; lem-nat-3-CSd04 ; lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-CCZ024-CX13 ; lem-comm-CSd03-CCZ124 ; lem-nat-0-BOX⟨0·3124⟩ ; lem-nat-0-BOX⟨1·3024⟩ ; lem-nat-0-BOX⟨2·0134⟩ ; lem-nat-0-BOX⟨2·0314⟩ ; lem-nat-0-BOX⟨2·1034⟩ ; lem-nat-0-BOX⟨2·1304⟩ ; lem-nat-0-BOX⟨2·3104⟩ ; lem-nat-0-BOXd⟨0·1234⟩ ; lem-nat-0-BOXd⟨1·0234⟩ ; lem-nat-0-BOXd⟨4·0231⟩ ; lem-nat-0-BOXd⟨4·1230⟩ ; lem-nat-0-SBOXd⟨0·1·23·4⟩ ; lem-nat-0-SBOXd⟨1·0·32·4⟩ ; lem-nat-0-SBOXd⟨4·0·23·1⟩ ; lem-nat-1-BOX⟨2·3014⟩ ; lem-nat-1-BOXd⟨1·0234⟩ ; lem-nat-1-BOXd⟨2·0134⟩ ; lem-nat-1-BOXd⟨4·0132⟩ ; lem-nat-1-BOXd⟨4·0231⟩ ; lem-nat-1-SBOXd⟨1·0·32·4⟩ ; lem-nat-1-SBOXd⟨2·0·13·4⟩ ; lem-nat-1-SBOXd⟨4·0·31·2⟩ ; lem-nat-1-TOFF402 ; lem-nat-2-BOX⟨0·1423⟩ ; lem-nat-2-BOXd⟨2·0134⟩ ; lem-nat-2-BOXd⟨3·0124⟩ ; lem-nat-2-BOXd⟨4·0123⟩ ; lem-nat-2-BOXd⟨4·0132⟩ ; lem-nat-2-CS03 ; lem-nat-2-CSd03 ; lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·23·4⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·32·4⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨1·0·23·4⟩ ; lem-nat-2-SBOXd⟨4·0·32·1⟩ ; lem-nat-3-BOXd⟨3·0124⟩ ; lem-nat-3-BOXd⟨4·0123⟩ ; lem-nat-3-CS03 ; lem-nat-3-CSd03 ; lem-nat-3-SBOXd⟨2·0·14·3⟩ ; lem-nat-3-SBOXd⟨2·0·31·4⟩ ; lem-nat-3-SBOXd⟨3·0·41·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨2·3014⟩ ; lem-nat-1-BOX⟨1·3024⟩)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx⁻0-1234 ∷ []) (Bx0-1234 ∷ []) (lem-BOXd-BOX c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1243 ∷ []) (lem-sym34 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx0-1243 ∷ []) (Bx0-1423 ∷ []) (lem-sym23-at3443 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CS14 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS14 ∷ []) (lem-CS12-beta-at243243 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Bx0-1423 ∷ []) (Bx0-1243 ∷ []) (lem-sym23-at243243 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Bx0-1243 ∷ []) (Bx0-1234 ∷ []) (lem-sym34-at3443 c4)

-- auto BOXd(0;1234) | CS14: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS14 : Ws → ⟪ (Bx⁻0-1234 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS14 c4 = derive (Bx⁻0-1234 ∷ CS14 ∷ []) (CS14 ∷ Bx⁻0-1234 ∷ [])
  (rw 0 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw 0 (q3 c4) ∷
   rw⁻ 0 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw⁻ 1 (q1 c4) ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = eqn (Bx⁻0-1234 ∷ CS14 ∷ []) (CS14 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS14 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CS14 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CS14 ∷ []) (wl0325 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CS14 ∷ CS14 ∷ []) (CS14 ∷ CS14 ∷ []) (wl0326 (lit c4))

-- auto SBOXd(0;1;23;4) | CS14: 9 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS14 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS14 c4 = derive (Sb⁻0-1-23-4 ∷ CS14 ∷ []) (CS14 ∷ Sb⁻0-1-23-4 ∷ [])
  (re 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) ∷
   rw 4 (q7 c4) ∷
   re 2 1 (CS14⁻ ∷ []) ∷
   rw⁻ 1 (q8 c4) ∷
   re 3 1 (Sb⁻0-1-4-3 ∷ []) ∷
   re 0 1 (CS14 ∷ []) ∷
   rw 0 (q9 c4) ∷
   re 1 1 (Sb0-1-4-3 ∷ []) ∷
   re 1 5 (Sb⁻0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q10 : Ws → Eqn
  q10 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw34 ∷ Sb⁻2-0-31-4 ∷ []) (Sb⁻2-0-41-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·31·4⟩ (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sb⁻2-0-41-3 ∷ []) (Sb⁻2-0-14-3 ∷ []) (lem-SBsymd c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Sw34 ∷ Sb⁻2-0-14-3 ∷ []) (Sb⁻2-0-13-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·14·3⟩ (lit c4))

-- SBsymd @3443: 5 steps
lem-SBsymd-at3443 : Ws → ⟪ (Sb⁻2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-13-4 ∷ []) ⟫ʷ
lem-SBsymd-at3443 c4 = derive (Sb⁻2-0-31-4 ∷ []) (Sb⁻2-0-13-4 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q11 c4) ∷
   rw 1 (q12 c4) ∷
   rw 0 (q13 c4) ∷
   rw 1 (q10 c4) ∷ []) Eq.refl

private
  q14 : Ws → Eqn
  q14 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (Sw12 ∷ Sb⁻1-0-32-4 ∷ []) (Sb⁻2-0-31-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·32·4⟩ (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (Sb⁻2-0-31-4 ∷ []) (Sb⁻2-0-13-4 ∷ []) (lem-SBsymd-at3443 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (Sw12 ∷ Sb⁻2-0-13-4 ∷ []) (Sb⁻1-0-23-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·13·4⟩ (lit c4))

-- SBsymd @12213443: 5 steps
lem-SBsymd-at12213443 : Ws → ⟪ (Sb⁻1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-23-4 ∷ []) ⟫ʷ
lem-SBsymd-at12213443 c4 = derive (Sb⁻1-0-32-4 ∷ []) (Sb⁻1-0-23-4 ∷ [])
  (rw⁻ 0 (q14 c4) ∷
   rw 1 (q15 c4) ∷
   rw 1 (q16 c4) ∷
   rw 0 (q17 c4) ∷
   rw 1 (q14 c4) ∷ []) Eq.refl

private
  q18 : Ws → Eqn
  q18 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw23 ∷ Sb⁻1-0-23-4 ∷ []) (Sb⁻1-0-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·23·4⟩ (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (Sb⁻1-0-32-4 ∷ []) (Sb⁻1-0-23-4 ∷ []) (lem-SBsymd-at12213443 c4)

-- SBsymd @13213442: 5 steps
lem-SBsymd-at13213442 : Ws → ⟪ (Sb⁻1-0-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-32-4 ∷ []) ⟫ʷ
lem-SBsymd-at13213442 c4 = derive (Sb⁻1-0-23-4 ∷ []) (Sb⁻1-0-32-4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q19 c4) ∷
   rw 1 (q20 c4) ∷
   rw 0 (q19 c4) ∷
   rw 1 (q18 c4) ∷ []) Eq.refl

private
  q21 : Ws → Eqn
  q21 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (Sw01 ∷ Sb⁻0-1-23-4 ∷ []) (Sb⁻1-0-23-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·23·4⟩ (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Sb⁻1-0-23-4 ∷ []) (Sb⁻1-0-32-4 ∷ []) (lem-SBsymd-at13213442 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (Sw01 ∷ Sb⁻1-0-32-4 ∷ []) (Sb⁻0-1-32-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·32·4⟩ (lit c4))

-- SBsymd @0113203442: 5 steps
lem-SBsymd-at0113203442 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-SBsymd-at0113203442 c4 = derive (Sb⁻0-1-23-4 ∷ []) (Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   rw 1 (q23 c4) ∷
   rw 0 (q24 c4) ∷
   rw 1 (q21 c4) ∷ []) Eq.refl

private
  q25 : Ws → Eqn
  q25 c4 = eqn (Sw23 ∷ Sb⁻0-1-32-4 ∷ []) (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl0021 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (Sb⁻0-1-23-4 ∷ CS14 ∷ []) (CS14 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS14 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (Sw23 ∷ Sb⁻0-1-23-4 ∷ []) (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | CS14 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS14-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS14-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ CS14 ∷ []) (CS14 ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q25 c4) ∷
   rw⁻ 2 (q26 c4) ∷
   rw 1 (q27 c4) ∷
   rw⁻ 0 (q26 c4) ∷
   rw 1 (q28 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = eqn (Sb⁻0-1-23-4 ∷ []) (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (Sb⁻0-1-32-4 ∷ CS14 ∷ []) (CS14 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS14-at2332 c4)

-- auto SBOXd(0;1;23;4) | SBOX(0;1;4;3): 5 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩ : Ws → ⟪ (Sb⁻0-1-23-4 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-3 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩ c4 = derive (Sb⁻0-1-23-4 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-3 ∷ Sb⁻0-1-23-4 ∷ [])
  (re 1 1 (CS14 ∷ []) ∷
   rw 0 (q29 c4) ∷
   rw 0 (q30 c4) ∷
   rw⁻ 1 (q29 c4) ∷
   re 0 1 (Sb0-1-4-3 ∷ []) ∷ []) Eq.refl

private
  q31 : Ws → Eqn
  q31 c4 = eqn (K0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0 ∷ []) (lem-K0-pass-c c4)

-- auto BOXd(0;1234) | K0: 3 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0 : Ws → ⟪ (Bx⁻0-1234 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0 c4 = derive (Bx⁻0-1234 ∷ K0 ∷ []) (K0 ∷ Bx⁻0-1234 ∷ [])
  (rw 0 (q1 c4) ∷
   rw⁻ 0 (q31 c4) ∷
   rw⁻ 1 (q1 c4) ∷ []) Eq.refl

private
  q32 : Ws → Eqn
  q32 c4 = eqn (Sb⁻2-0-41-3 ∷ []) (Sb⁻3-0-41-2 ∷ []) (lem-F0d c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Sw34 ∷ Sb⁻3-0-41-2 ∷ []) (Sb⁻4-0-31-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨3·0·41·2⟩ (lit c4))

-- F0d @3443: 5 steps
lem-F0d-at3443 : Ws → ⟪ (Sb⁻2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-31-2 ∷ []) ⟫ʷ
lem-F0d-at3443 c4 = derive (Sb⁻2-0-31-4 ∷ []) (Sb⁻4-0-31-2 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q11 c4) ∷
   rw 1 (q32 c4) ∷
   rw 0 (q33 c4) ∷
   rw 1 (q10 c4) ∷ []) Eq.refl

private
  q34 : Ws → Eqn
  q34 c4 = eqn (Sb⁻2-0-31-4 ∷ []) (Sb⁻4-0-31-2 ∷ []) (lem-F0d-at3443 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (Sw12 ∷ Sb⁻4-0-31-2 ∷ []) (Sb⁻4-0-32-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨4·0·31·2⟩ (lit c4))

-- F0d @12213443: 5 steps
lem-F0d-at12213443 : Ws → ⟪ (Sb⁻1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-32-1 ∷ []) ⟫ʷ
lem-F0d-at12213443 c4 = derive (Sb⁻1-0-32-4 ∷ []) (Sb⁻4-0-32-1 ∷ [])
  (rw⁻ 0 (q14 c4) ∷
   rw 1 (q15 c4) ∷
   rw 1 (q34 c4) ∷
   rw 0 (q35 c4) ∷
   rw 1 (q14 c4) ∷ []) Eq.refl

private
  q36 : Ws → Eqn
  q36 c4 = eqn (Sb⁻1-0-32-4 ∷ []) (Sb⁻4-0-32-1 ∷ []) (lem-F0d-at12213443 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (Sw23 ∷ Sb⁻4-0-32-1 ∷ []) (Sb⁻4-0-23-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·0·32·1⟩ (lit c4))

-- F0d @13213442: 5 steps
lem-F0d-at13213442 : Ws → ⟪ (Sb⁻1-0-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-23-1 ∷ []) ⟫ʷ
lem-F0d-at13213442 c4 = derive (Sb⁻1-0-23-4 ∷ []) (Sb⁻4-0-23-1 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q19 c4) ∷
   rw 1 (q36 c4) ∷
   rw 0 (q37 c4) ∷
   rw 1 (q18 c4) ∷ []) Eq.refl

private
  q38 : Ws → Eqn
  q38 c4 = eqn (Sb⁻1-0-23-4 ∷ []) (Sb⁻4-0-23-1 ∷ []) (lem-F0d-at13213442 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (Sw01 ∷ Sb⁻4-0-23-1 ∷ []) (Sb⁻4-1-23-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨4·0·23·1⟩ (lit c4))

-- F0d @0113203442: 5 steps
lem-F0d-at0113203442 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-1-23-0 ∷ []) ⟫ʷ
lem-F0d-at0113203442 c4 = derive (Sb⁻0-1-23-4 ∷ []) (Sb⁻4-1-23-0 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   rw 1 (q38 c4) ∷
   rw 0 (q39 c4) ∷
   rw 1 (q21 c4) ∷ []) Eq.refl

private
  q40 : Ws → Eqn
  q40 c4 = eqn (Sw01 ∷ Bx⁻1-0234 ∷ []) (Bx⁻0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0234⟩ (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wl0031 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (Bx⁻0-1234 ∷ K0 ∷ []) (K0 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wl0076 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (Sw01 ∷ Bx⁻0-1234 ∷ []) (Bx⁻1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·1234⟩ (lit c4))

-- auto BOXd(0;1234) | K0 @0110: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0-at0110 : Ws → ⟪ (Bx⁻1-0234 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Bx⁻1-0234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0-at0110 c4 = derive (Bx⁻1-0234 ∷ K1 ∷ []) (K1 ∷ Bx⁻1-0234 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q40 c4) ∷
   rw⁻ 2 (q41 c4) ∷
   rw 1 (q42 c4) ∷
   rw⁻ 0 (q43 c4) ∷
   rw 1 (q44 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q45 : Ws → Eqn
  q45 c4 = eqn (Sw12 ∷ Bx⁻2-0134 ∷ []) (Bx⁻1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0134⟩ (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (K1 ∷ Sw12 ∷ []) (Sw12 ∷ K2 ∷ []) (wl0062 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (Bx⁻1-0234 ∷ K1 ∷ []) (K1 ∷ Bx⁻1-0234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0-at0110 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wl0056 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (Sw12 ∷ Bx⁻1-0234 ∷ []) (Bx⁻2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·0234⟩ (lit c4))

-- auto BOXd(0;1234) | K0 @021021: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0-at021021 : Ws → ⟪ (Bx⁻2-0134 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Bx⁻2-0134 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0-at021021 c4 = derive (Bx⁻2-0134 ∷ K2 ∷ []) (K2 ∷ Bx⁻2-0134 ∷ [])
  (rw⁻ 0 (q14 c4) ∷
   rw 1 (q45 c4) ∷
   rw⁻ 2 (q46 c4) ∷
   rw 1 (q47 c4) ∷
   rw⁻ 0 (q48 c4) ∷
   rw 1 (q49 c4) ∷
   rw 2 (q14 c4) ∷ []) Eq.refl

private
  q50 : Ws → Eqn
  q50 c4 = eqn (Sw23 ∷ Bx⁻3-0124 ∷ []) (Bx⁻2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·0124⟩ (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (K2 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ []) (wl0058 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (Bx⁻2-0134 ∷ K2 ∷ []) (K2 ∷ Bx⁻2-0134 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0-at021021 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wl0057 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (Sw23 ∷ Bx⁻2-0134 ∷ []) (Bx⁻3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨2·0134⟩ (lit c4))

-- auto BOXd(0;1234) | K0 @03102132: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0-at03102132 : Ws → ⟪ (Bx⁻3-0124 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Bx⁻3-0124 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0-at03102132 c4 = derive (Bx⁻3-0124 ∷ K3 ∷ []) (K3 ∷ Bx⁻3-0124 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q50 c4) ∷
   rw⁻ 2 (q51 c4) ∷
   rw 1 (q52 c4) ∷
   rw⁻ 0 (q53 c4) ∷
   rw 1 (q54 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = eqn (Sw34 ∷ Bx⁻4-0123 ∷ []) (Bx⁻3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·0123⟩ (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (K3 ∷ Sw34 ∷ []) (Sw34 ∷ K4 ∷ []) (wl0068 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (Bx⁻3-0124 ∷ K3 ∷ []) (K3 ∷ Bx⁻3-0124 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0-at03102132 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (K4 ∷ Sw34 ∷ []) (Sw34 ∷ K3 ∷ []) (wl0067 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (Sw34 ∷ Bx⁻3-0124 ∷ []) (Bx⁻4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·0124⟩ (lit c4))

-- auto BOXd(0;1234) | K0 @0410213243: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0-at0410213243 : Ws → ⟪ (Bx⁻4-0123 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx⁻4-0123 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0-at0410213243 c4 = derive (Bx⁻4-0123 ∷ K4 ∷ []) (K4 ∷ Bx⁻4-0123 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q55 c4) ∷
   rw⁻ 2 (q56 c4) ∷
   rw 1 (q57 c4) ∷
   rw⁻ 0 (q58 c4) ∷
   rw 1 (q59 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = eqn (Sw23 ∷ Bx⁻4-0132 ∷ []) (Bx⁻4-0123 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·0132⟩ (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (Sw23 ∷ K4 ∷ []) (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K))
  q62 : Ws → Eqn
  q62 c4 = eqn (Bx⁻4-0123 ∷ K4 ∷ []) (K4 ∷ Bx⁻4-0123 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0-at0410213243 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (Sw23 ∷ Bx⁻4-0123 ∷ []) (Bx⁻4-0132 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·0123⟩ (lit c4))

-- auto BOXd(0;1234) | K0 @04102142: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0-at04102142 : Ws → ⟪ (Bx⁻4-0132 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx⁻4-0132 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0-at04102142 c4 = derive (Bx⁻4-0132 ∷ K4 ∷ []) (K4 ∷ Bx⁻4-0132 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q60 c4) ∷
   rw 2 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   rw 0 (q61 c4) ∷
   rw 1 (q63 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q64 : Ws → Eqn
  q64 c4 = eqn (Sw12 ∷ Bx⁻4-0231 ∷ []) (Bx⁻4-0132 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·0231⟩ (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (Sw12 ∷ K4 ∷ []) (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑))
  q66 : Ws → Eqn
  q66 c4 = eqn (Bx⁻4-0132 ∷ K4 ∷ []) (K4 ∷ Bx⁻4-0132 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0-at04102142 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (Sw12 ∷ Bx⁻4-0132 ∷ []) (Bx⁻4-0231 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·0132⟩ (lit c4))

-- auto BOXd(0;1234) | K0 @041041: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0-at041041 : Ws → ⟪ (Bx⁻4-0231 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx⁻4-0231 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0-at041041 c4 = derive (Bx⁻4-0231 ∷ K4 ∷ []) (K4 ∷ Bx⁻4-0231 ∷ [])
  (rw⁻ 0 (q14 c4) ∷
   rw 1 (q64 c4) ∷
   rw 2 (q65 c4) ∷
   rw 1 (q66 c4) ∷
   rw 0 (q65 c4) ∷
   rw 1 (q67 c4) ∷
   rw 2 (q14 c4) ∷ []) Eq.refl

private
  q68 : Ws → Eqn
  q68 c4 = eqn (Sw01 ∷ Bx⁻4-1230 ∷ []) (Bx⁻4-0231 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·1230⟩ (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (Sw01 ∷ K4 ∷ []) (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑))
  q70 : Ws → Eqn
  q70 c4 = eqn (Bx⁻4-0231 ∷ K4 ∷ []) (K4 ∷ Bx⁻4-0231 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0-at041041 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (Sw01 ∷ Bx⁻4-0231 ∷ []) (Bx⁻4-1230 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·0231⟩ (lit c4))

-- auto BOXd(0;1234) | K0 @0440: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0-at0440 : Ws → ⟪ (Bx⁻4-1230 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx⁻4-1230 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0-at0440 c4 = derive (Bx⁻4-1230 ∷ K4 ∷ []) (K4 ∷ Bx⁻4-1230 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q68 c4) ∷
   rw 2 (q69 c4) ∷
   rw 1 (q70 c4) ∷
   rw 0 (q69 c4) ∷
   rw 1 (q71 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = eqn (Sb⁻0-1-23-4 ∷ []) (Sb⁻4-1-23-0 ∷ []) (lem-F0d-at0113203442 c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (Bx⁻4-1230 ∷ K4 ∷ []) (K4 ∷ Bx⁻4-1230 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0-at0440 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (K4 ∷ Toff023 ∷ []) (Toff023 ∷ K4 ∷ []) (wp0094 c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (CS01⁻ ∷ K4 ∷ []) (K4 ∷ CS01⁻ ∷ []) (wl0301 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (CS01 ∷ K4 ∷ []) (K4 ∷ CS01 ∷ []) (wl0302 (lit c4))

-- auto SBOXd(0;1;23;4) | K4: 13 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4 c4 = derive (Sb⁻0-1-23-4 ∷ K4 ∷ []) (K4 ∷ Sb⁻0-1-23-4 ∷ [])
  (rw 0 (q72 c4) ∷
   re 0 1 (Sb4-1-0-3 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ Toff023 ∷ Bx⁻4-1230 ∷ []) ∷
   rw 4 (q73 c4) ∷
   rw⁻ 3 (q74 c4) ∷
   re 2 1 (CS01⁻ ∷ []) ∷
   rw 2 (q75 c4) ∷
   re 3 1 (Sb⁻4-1-0-3 ∷ []) ∷
   rw⁻ 1 (q74 c4) ∷
   re 0 1 (CS01 ∷ []) ∷
   rw 0 (q76 c4) ∷
   re 1 1 (Sb4-1-0-3 ∷ []) ∷
   re 1 5 (Sb⁻4-1-23-0 ∷ []) ∷
   rw⁻ 1 (q72 c4) ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = eqn (Bx0-1234 ∷ []) (Bx0-2134 ∷ []) (lem-sym12 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (Bx0-2134 ∷ []) (Bx0-2143 ∷ []) (lem-sym34-at1221 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (Bx0-2143 ∷ []) (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (CS24 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ CS24 ∷ []) (lem-CS12-beta-at12243143 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (Bx0-2413 ∷ []) (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (Bx0-2143 ∷ []) (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (Bx0-2134 ∷ []) (Bx0-1234 ∷ []) (lem-sym12-at1221 c4)

-- auto BOXd(0;1234) | CS24: 9 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS24 : Ws → ⟪ (Bx⁻0-1234 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS24 c4 = derive (Bx⁻0-1234 ∷ CS24 ∷ []) (CS24 ∷ Bx⁻0-1234 ∷ [])
  (rw 0 (q1 c4) ∷
   rw 0 (q77 c4) ∷
   rw 0 (q78 c4) ∷
   rw 0 (q79 c4) ∷
   rw⁻ 0 (q80 c4) ∷
   rw 1 (q81 c4) ∷
   rw 1 (q82 c4) ∷
   rw 1 (q83 c4) ∷
   rw⁻ 1 (q1 c4) ∷ []) Eq.refl

private
  q84 : Ws → Eqn
  q84 c4 = eqn (Bx⁻0-1234 ∷ CS24 ∷ []) (CS24 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS24 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (CS24 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CS24 ∷ []) (wl0327 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (CS14 ∷ CS24 ∷ []) (CS24 ∷ CS14 ∷ []) (wl0328 (lit c4))

-- auto SBOXd(0;1;23;4) | CS24: 9 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24 c4 = derive (Sb⁻0-1-23-4 ∷ CS24 ∷ []) (CS24 ∷ Sb⁻0-1-23-4 ∷ [])
  (re 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) ∷
   rw 4 (q84 c4) ∷
   re 2 1 (CS14⁻ ∷ []) ∷
   rw⁻ 1 (q85 c4) ∷
   re 3 1 (Sb⁻0-1-4-3 ∷ []) ∷
   re 0 1 (CS14 ∷ []) ∷
   rw 0 (q86 c4) ∷
   re 1 1 (Sb0-1-4-3 ∷ []) ∷
   re 1 5 (Sb⁻0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q87 : Ws → Eqn
  q87 c4 = eqn (K0⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0⁻ ∷ []) (lem-K0-pass-ci c4)

-- auto BOXd(0;1234) | Kd0: 3 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0 : Ws → ⟪ (Bx⁻0-1234 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0 c4 = derive (Bx⁻0-1234 ∷ K0⁻ ∷ []) (K0⁻ ∷ Bx⁻0-1234 ∷ [])
  (rw 0 (q1 c4) ∷
   rw⁻ 0 (q87 c4) ∷
   rw⁻ 1 (q1 c4) ∷ []) Eq.refl

private
  q88 : Ws → Eqn
  q88 c4 = eqn (K0⁻ ∷ Sw01 ∷ []) (Sw01 ∷ K1⁻ ∷ []) (wl0257 (lit c4))
  q89 : Ws → Eqn
  q89 c4 = eqn (Bx⁻0-1234 ∷ K0⁻ ∷ []) (K0⁻ ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (K1⁻ ∷ Sw01 ∷ []) (Sw01 ∷ K0⁻ ∷ []) (wl0306 (lit c4))

-- auto BOXd(0;1234) | Kd0 @0110: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0110 : Ws → ⟪ (Bx⁻1-0234 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ Bx⁻1-0234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0110 c4 = derive (Bx⁻1-0234 ∷ K1⁻ ∷ []) (K1⁻ ∷ Bx⁻1-0234 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q40 c4) ∷
   rw⁻ 2 (q88 c4) ∷
   rw 1 (q89 c4) ∷
   rw⁻ 0 (q90 c4) ∷
   rw 1 (q44 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q91 : Ws → Eqn
  q91 c4 = eqn (K1⁻ ∷ Sw12 ∷ []) (Sw12 ∷ K2⁻ ∷ []) (wl0307 (lit c4))
  q92 : Ws → Eqn
  q92 c4 = eqn (Bx⁻1-0234 ∷ K1⁻ ∷ []) (K1⁻ ∷ Bx⁻1-0234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0110 c4)
  q93 : Ws → Eqn
  q93 c4 = eqn (K2⁻ ∷ Sw12 ∷ []) (Sw12 ∷ K1⁻ ∷ []) (wl0308 (lit c4))

-- auto BOXd(0;1234) | Kd0 @021021: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at021021 : Ws → ⟪ (Bx⁻2-0134 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ Bx⁻2-0134 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at021021 c4 = derive (Bx⁻2-0134 ∷ K2⁻ ∷ []) (K2⁻ ∷ Bx⁻2-0134 ∷ [])
  (rw⁻ 0 (q14 c4) ∷
   rw 1 (q45 c4) ∷
   rw⁻ 2 (q91 c4) ∷
   rw 1 (q92 c4) ∷
   rw⁻ 0 (q93 c4) ∷
   rw 1 (q49 c4) ∷
   rw 2 (q14 c4) ∷ []) Eq.refl

private
  q94 : Ws → Eqn
  q94 c4 = eqn (K2⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K3⁻ ∷ []) (wl0309 (lit c4))
  q95 : Ws → Eqn
  q95 c4 = eqn (Bx⁻2-0134 ∷ K2⁻ ∷ []) (K2⁻ ∷ Bx⁻2-0134 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at021021 c4)
  q96 : Ws → Eqn
  q96 c4 = eqn (K3⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K2⁻ ∷ []) (wl0310 (lit c4))

-- auto BOXd(0;1234) | Kd0 @03102132: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at03102132 : Ws → ⟪ (Bx⁻3-0124 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Bx⁻3-0124 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at03102132 c4 = derive (Bx⁻3-0124 ∷ K3⁻ ∷ []) (K3⁻ ∷ Bx⁻3-0124 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q50 c4) ∷
   rw⁻ 2 (q94 c4) ∷
   rw 1 (q95 c4) ∷
   rw⁻ 0 (q96 c4) ∷
   rw 1 (q54 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q97 : Ws → Eqn
  q97 c4 = eqn (K3⁻ ∷ Sw34 ∷ []) (Sw34 ∷ K4⁻ ∷ []) (wl0311 (lit c4))
  q98 : Ws → Eqn
  q98 c4 = eqn (Bx⁻3-0124 ∷ K3⁻ ∷ []) (K3⁻ ∷ Bx⁻3-0124 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at03102132 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (K4⁻ ∷ Sw34 ∷ []) (Sw34 ∷ K3⁻ ∷ []) (wl0312 (lit c4))

-- auto BOXd(0;1234) | Kd0 @0410213243: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0410213243 : Ws → ⟪ (Bx⁻4-0123 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx⁻4-0123 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0410213243 c4 = derive (Bx⁻4-0123 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx⁻4-0123 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q55 c4) ∷
   rw⁻ 2 (q97 c4) ∷
   rw 1 (q98 c4) ∷
   rw⁻ 0 (q99 c4) ∷
   rw 1 (q59 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = eqn (Sw23 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K • iI))
  q101 : Ws → Eqn
  q101 c4 = eqn (Bx⁻4-0123 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx⁻4-0123 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0410213243 c4)

-- auto BOXd(0;1234) | Kd0 @04102142: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at04102142 : Ws → ⟪ (Bx⁻4-0132 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx⁻4-0132 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at04102142 c4 = derive (Bx⁻4-0132 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx⁻4-0132 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q60 c4) ∷
   rw 2 (q100 c4) ∷
   rw 1 (q101 c4) ∷
   rw 0 (q100 c4) ∷
   rw 1 (q63 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q102 : Ws → Eqn
  q102 c4 = eqn (Sw12 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) ((K • iI) ↑))
  q103 : Ws → Eqn
  q103 c4 = eqn (Bx⁻4-0132 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx⁻4-0132 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at04102142 c4)

-- auto BOXd(0;1234) | Kd0 @041041: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at041041 : Ws → ⟪ (Bx⁻4-0231 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx⁻4-0231 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at041041 c4 = derive (Bx⁻4-0231 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx⁻4-0231 ∷ [])
  (rw⁻ 0 (q14 c4) ∷
   rw 1 (q64 c4) ∷
   rw 2 (q102 c4) ∷
   rw 1 (q103 c4) ∷
   rw 0 (q102 c4) ∷
   rw 1 (q67 c4) ∷
   rw 2 (q14 c4) ∷ []) Eq.refl

private
  q104 : Ws → Eqn
  q104 c4 = eqn (Sw01 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((K • iI) ↑ ↑))
  q105 : Ws → Eqn
  q105 c4 = eqn (Bx⁻4-0231 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx⁻4-0231 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at041041 c4)

-- auto BOXd(0;1234) | Kd0 @0440: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0440 : Ws → ⟪ (Bx⁻4-1230 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx⁻4-1230 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0440 c4 = derive (Bx⁻4-1230 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx⁻4-1230 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q68 c4) ∷
   rw 2 (q104 c4) ∷
   rw 1 (q105 c4) ∷
   rw 0 (q104 c4) ∷
   rw 1 (q71 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q106 : Ws → Eqn
  q106 c4 = eqn (Bx⁻4-1230 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx⁻4-1230 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0440 c4)
  q107 : Ws → Eqn
  q107 c4 = eqn (K4⁻ ∷ Toff023 ∷ []) (Toff023 ∷ K4⁻ ∷ []) (wp0095 c4)
  q108 : Ws → Eqn
  q108 c4 = eqn (CS01⁻ ∷ K4⁻ ∷ []) (K4⁻ ∷ CS01⁻ ∷ []) (wl0313 (lit c4))
  q109 : Ws → Eqn
  q109 c4 = eqn (CS01 ∷ K4⁻ ∷ []) (K4⁻ ∷ CS01 ∷ []) (wl0314 (lit c4))

-- auto SBOXd(0;1;23;4) | Kd4: 13 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4 c4 = derive (Sb⁻0-1-23-4 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sb⁻0-1-23-4 ∷ [])
  (rw 0 (q72 c4) ∷
   re 0 1 (Sb4-1-0-3 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ Toff023 ∷ Bx⁻4-1230 ∷ []) ∷
   rw 4 (q106 c4) ∷
   rw⁻ 3 (q107 c4) ∷
   re 2 1 (CS01⁻ ∷ []) ∷
   rw 2 (q108 c4) ∷
   re 3 1 (Sb⁻4-1-0-3 ∷ []) ∷
   rw⁻ 1 (q107 c4) ∷
   re 0 1 (CS01 ∷ []) ∷
   rw 0 (q109 c4) ∷
   re 1 1 (Sb4-1-0-3 ∷ []) ∷
   re 1 5 (Sb⁻4-1-23-0 ∷ []) ∷
   rw⁻ 1 (q72 c4) ∷ []) Eq.refl

private
  q110 : Ws → Eqn
  q110 c4 = eqn (CS14⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS14⁻ ∷ []) (lem-CSd12-beta-at243243 c4)

-- auto BOXd(0;1234) | CSd14: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CSd14 : Ws → ⟪ (Bx⁻0-1234 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CSd14 c4 = derive (Bx⁻0-1234 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx⁻0-1234 ∷ [])
  (rw 0 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw 0 (q3 c4) ∷
   rw⁻ 0 (q110 c4) ∷
   rw 1 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw⁻ 1 (q1 c4) ∷ []) Eq.refl

private
  q111 : Ws → Eqn
  q111 c4 = eqn (Bx⁻0-1234 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CSd14 c4)
  q112 : Ws → Eqn
  q112 c4 = eqn (CS14⁻ ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CS14⁻ ∷ []) (wl0329 (lit c4))
  q113 : Ws → Eqn
  q113 c4 = eqn (CS14 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS14 ∷ []) (wl0299 (lit c4))

-- auto SBOXd(0;1;23;4) | CSd14: 9 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd14 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd14 c4 = derive (Sb⁻0-1-23-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb⁻0-1-23-4 ∷ [])
  (re 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) ∷
   rw 4 (q111 c4) ∷
   re 2 1 (CS14⁻ ∷ []) ∷
   rw⁻ 1 (q112 c4) ∷
   re 3 1 (Sb⁻0-1-4-3 ∷ []) ∷
   re 0 1 (CS14 ∷ []) ∷
   rw 0 (q113 c4) ∷
   re 1 1 (Sb0-1-4-3 ∷ []) ∷
   re 1 5 (Sb⁻0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q114 : Ws → Eqn
  q114 c4 = eqn (CS14⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS14⁻ ∷ []) (wl0033 (lit c4))
  q115 : Ws → Eqn
  q115 c4 = eqn (Sb⁻0-1-23-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd14 c4)

-- auto SBOXd(0;1;23;4) | CSd14 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd14-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd14-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q25 c4) ∷
   rw⁻ 2 (q114 c4) ∷
   rw 1 (q115 c4) ∷
   rw⁻ 0 (q114 c4) ∷
   rw 1 (q28 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q116 : Ws → Eqn
  q116 c4 = eqn (Sb⁻0-1-32-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd14-at2332 c4)

-- auto SBOXd(0;1;23;4) | SBOXd(0;1;4;3): 5 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩ : Ws → ⟪ (Sb⁻0-1-23-4 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-3 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩ c4 = derive (Sb⁻0-1-23-4 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-3 ∷ Sb⁻0-1-23-4 ∷ [])
  (re 1 1 (CS14⁻ ∷ []) ∷
   rw 0 (q29 c4) ∷
   rw 0 (q116 c4) ∷
   rw⁻ 1 (q29 c4) ∷
   re 0 1 (Sb⁻0-1-4-3 ∷ []) ∷ []) Eq.refl

private
  q117 : Ws → Eqn
  q117 c4 = eqn (K0 ∷ Toff423 ∷ []) (Toff423 ∷ K0 ∷ []) (wl0330 (lit c4))
  q118 : Ws → Eqn
  q118 c4 = eqn (CS14⁻ ∷ K0 ∷ []) (K0 ∷ CS14⁻ ∷ []) (wp0096 c4)
  q119 : Ws → Eqn
  q119 c4 = eqn (CS14 ∷ K0 ∷ []) (K0 ∷ CS14 ∷ []) (wp0097 c4)

-- auto SBOXd(0;1;23;4) | K0: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K0 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K0 c4 = derive (Sb⁻0-1-23-4 ∷ K0 ∷ []) (K0 ∷ Sb⁻0-1-23-4 ∷ [])
  (re 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) ∷
   rw 4 (q42 c4) ∷
   rw⁻ 3 (q117 c4) ∷
   re 2 1 (CS14⁻ ∷ []) ∷
   rw 2 (q118 c4) ∷
   re 3 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw⁻ 1 (q117 c4) ∷
   re 0 1 (CS14 ∷ []) ∷
   rw 0 (q119 c4) ∷
   re 1 1 (Sb0-1-4-3 ∷ []) ∷
   re 1 5 (Sb⁻0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q120 : Ws → Eqn
  q120 c4 = eqn (CS02 ∷ []) (CS02 ∷ []) (wl0331 (lit c4))
  q121 : Ws → Eqn
  q121 c4 = eqn (CS02 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02 ∷ []) (lem-CS20-beta-c c4)

-- auto BOXd(0;1234) | CS20: 5 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS20 : Ws → ⟪ (Bx⁻0-1234 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS20 c4 = derive (Bx⁻0-1234 ∷ CS02 ∷ []) (CS02 ∷ Bx⁻0-1234 ∷ [])
  (rw 0 (q1 c4) ∷
   rw 1 (q120 c4) ∷
   rw⁻ 0 (q121 c4) ∷
   rw 0 (q120 c4) ∷
   rw⁻ 1 (q1 c4) ∷ []) Eq.refl

private
  q122 : Ws → Eqn
  q122 c4 = eqn (Bx⁻0-1234 ∷ CS02 ∷ []) (CS02 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS20 c4)
  q123 : Ws → Eqn
  q123 c4 = eqn (CS02 ∷ Toff423 ∷ []) (Toff423 ∷ CS02 ∷ []) (wp0098 c4)
  q124 : Ws → Eqn
  q124 c4 = eqn (CS02 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS02 ∷ []) (wp0099 c4)
  q125 : Ws → Eqn
  q125 c4 = eqn (CS02 ∷ CS14 ∷ []) (CS14 ∷ CS02 ∷ []) (wp0100 c4)

-- auto SBOXd(0;1;23;4) | CS20: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20 c4 = derive (Sb⁻0-1-23-4 ∷ CS02 ∷ []) (CS02 ∷ Sb⁻0-1-23-4 ∷ [])
  (re 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) ∷
   rw 4 (q122 c4) ∷
   rw⁻ 3 (q123 c4) ∷
   re 2 1 (CS14⁻ ∷ []) ∷
   rw⁻ 2 (q124 c4) ∷
   re 3 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw⁻ 1 (q123 c4) ∷
   re 0 1 (CS14 ∷ []) ∷
   rw⁻ 0 (q125 c4) ∷
   re 1 1 (Sb0-1-4-3 ∷ []) ∷
   re 1 5 (Sb⁻0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = eqn (CS01 ∷ []) (CS01 ∷ []) (wl0332 (lit c4))
  q127 : Ws → Eqn
  q127 c4 = eqn (CS01 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CS01 ∷ []) (lem-CS20-beta-c-at1221 c4)

-- auto BOXd(0;1234) | CS10: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS10 : Ws → ⟪ (Bx⁻0-1234 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS10 c4 = derive (Bx⁻0-1234 ∷ CS01 ∷ []) (CS01 ∷ Bx⁻0-1234 ∷ [])
  (rw 0 (q1 c4) ∷
   rw 1 (q126 c4) ∷
   rw 0 (q77 c4) ∷
   rw⁻ 0 (q127 c4) ∷
   rw 1 (q83 c4) ∷
   rw 0 (q126 c4) ∷
   rw⁻ 1 (q1 c4) ∷ []) Eq.refl

private
  q128 : Ws → Eqn
  q128 c4 = eqn (Toff012 ∷ CS34 ∷ []) (CS34 ∷ Toff012 ∷ []) (c₃ (Toff) (CS))

-- auto TOFF012 | CS34: 1 steps
lem-auto-TOFF012-∣-CS34 : Ws → ⟪ (Toff012 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34 c4 = derive (Toff012 ∷ CS34 ∷ []) (CS34 ∷ Toff012 ∷ [])
  (rw 0 (q128 c4) ∷ []) Eq.refl

private
  q129 : Ws → Eqn
  q129 c4 = eqn (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) (wl0097 (lit c4))
  q130 : Ws → Eqn
  q130 c4 = eqn (Sw01 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q131 : Ws → Eqn
  q131 c4 = eqn (Toff012 ∷ CS34 ∷ []) (CS34 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-CS34 c4)
  q132 : Ws → Eqn
  q132 c4 = eqn (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) (wl0099 (lit c4))

-- auto TOFF012 | CS34 @0110: 7 steps
lem-auto-TOFF012-∣-CS34-at0110 : Ws → ⟪ (Toff102 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Toff102 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at0110 c4 = derive (Toff102 ∷ CS34 ∷ []) (CS34 ∷ Toff102 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q129 c4) ∷
   rw 2 (q130 c4) ∷
   rw 1 (q131 c4) ∷
   rw 0 (q130 c4) ∷
   rw 1 (q132 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q133 : Ws → Eqn
  q133 c4 = eqn (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) (wl0044 (lit c4))
  q134 : Ws → Eqn
  q134 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q135 : Ws → Eqn
  q135 c4 = eqn (Toff102 ∷ CS34 ∷ []) (CS34 ∷ Toff102 ∷ []) (lem-auto-TOFF012-∣-CS34-at0110 c4)
  q136 : Ws → Eqn
  q136 c4 = eqn (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) (wl0047 (lit c4))

-- auto TOFF012 | CS34 @021021: 7 steps
lem-auto-TOFF012-∣-CS34-at021021 : Ws → ⟪ (Toff201 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Toff201 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at021021 c4 = derive (Toff201 ∷ CS34 ∷ []) (CS34 ∷ Toff201 ∷ [])
  (rw⁻ 0 (q14 c4) ∷
   rw 1 (q133 c4) ∷
   rw 2 (q134 c4) ∷
   rw 1 (q135 c4) ∷
   rw 0 (q134 c4) ∷
   rw 1 (q136 c4) ∷
   rw 2 (q14 c4) ∷ []) Eq.refl

private
  q137 : Ws → Eqn
  q137 c4 = eqn (Sw23 ∷ Toff301 ∷ []) (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 (lit c4))
  q138 : Ws → Eqn
  q138 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0011 (lit c4))
  q139 : Ws → Eqn
  q139 c4 = eqn (Toff201 ∷ CS34 ∷ []) (CS34 ∷ Toff201 ∷ []) (lem-auto-TOFF012-∣-CS34-at021021 c4)
  q140 : Ws → Eqn
  q140 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0015 (lit c4))
  q141 : Ws → Eqn
  q141 c4 = eqn (Sw23 ∷ Toff201 ∷ []) (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 (lit c4))

-- auto TOFF012 | CS34 @03102132: 7 steps
lem-auto-TOFF012-∣-CS34-at03102132 : Ws → ⟪ (Toff301 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Toff301 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at03102132 c4 = derive (Toff301 ∷ CS24 ∷ []) (CS24 ∷ Toff301 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q137 c4) ∷
   rw⁻ 2 (q138 c4) ∷
   rw 1 (q139 c4) ∷
   rw⁻ 0 (q140 c4) ∷
   rw 1 (q141 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q142 : Ws → Eqn
  q142 c4 = eqn (Sw34 ∷ Toff401 ∷ []) (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 (lit c4))
  q143 : Ws → Eqn
  q143 c4 = eqn (Sw34 ∷ CS23 ∷ []) (CS24 ∷ Sw34 ∷ []) (lem-nat-3-CS23 (lit c4))
  q144 : Ws → Eqn
  q144 c4 = eqn (Toff301 ∷ CS24 ∷ []) (CS24 ∷ Toff301 ∷ []) (lem-auto-TOFF012-∣-CS34-at03102132 c4)
  q145 : Ws → Eqn
  q145 c4 = eqn (Sw34 ∷ CS24 ∷ []) (CS23 ∷ Sw34 ∷ []) (lem-nat-3-CS24 (lit c4))
  q146 : Ws → Eqn
  q146 c4 = eqn (Sw34 ∷ Toff301 ∷ []) (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 (lit c4))

-- auto TOFF012 | CS34 @0410213243: 7 steps
lem-auto-TOFF012-∣-CS34-at0410213243 : Ws → ⟪ (Toff401 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff401 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at0410213243 c4 = derive (Toff401 ∷ CS23 ∷ []) (CS23 ∷ Toff401 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q142 c4) ∷
   rw 2 (q143 c4) ∷
   rw 1 (q144 c4) ∷
   rw 0 (q145 c4) ∷
   rw 1 (q146 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q147 : Ws → Eqn
  q147 c4 = eqn (Sw12 ∷ Toff402 ∷ []) (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 (lit c4))
  q148 : Ws → Eqn
  q148 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl0025 (lit c4))
  q149 : Ws → Eqn
  q149 c4 = eqn (Toff401 ∷ CS23 ∷ []) (CS23 ∷ Toff401 ∷ []) (lem-auto-TOFF012-∣-CS34-at0410213243 c4)
  q150 : Ws → Eqn
  q150 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl0024 (lit c4))
  q151 : Ws → Eqn
  q151 c4 = eqn (Sw12 ∷ Toff401 ∷ []) (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 (lit c4))

-- auto TOFF012 | CS34 @04103143: 7 steps
lem-auto-TOFF012-∣-CS34-at04103143 : Ws → ⟪ (Toff402 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff402 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at04103143 c4 = derive (Toff402 ∷ CS13 ∷ []) (CS13 ∷ Toff402 ∷ [])
  (rw⁻ 0 (q14 c4) ∷
   rw 1 (q147 c4) ∷
   rw⁻ 2 (q148 c4) ∷
   rw 1 (q149 c4) ∷
   rw⁻ 0 (q150 c4) ∷
   rw 1 (q151 c4) ∷
   rw 2 (q14 c4) ∷ []) Eq.refl

private
  q152 : Ws → Eqn
  q152 c4 = eqn (Sw23 ∷ Toff403 ∷ []) (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 (lit c4))
  q153 : Ws → Eqn
  q153 c4 = eqn (Sw23 ∷ CS12 ∷ []) (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 (lit c4))
  q154 : Ws → Eqn
  q154 c4 = eqn (Toff402 ∷ CS13 ∷ []) (CS13 ∷ Toff402 ∷ []) (lem-auto-TOFF012-∣-CS34-at04103143 c4)
  q155 : Ws → Eqn
  q155 c4 = eqn (Sw23 ∷ CS13 ∷ []) (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 (lit c4))
  q156 : Ws → Eqn
  q156 c4 = eqn (Sw23 ∷ Toff402 ∷ []) (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 (lit c4))

-- auto TOFF012 | CS34 @0410233142: 7 steps
lem-auto-TOFF012-∣-CS34-at0410233142 : Ws → ⟪ (Toff403 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Toff403 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at0410233142 c4 = derive (Toff403 ∷ CS12 ∷ []) (CS12 ∷ Toff403 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q152 c4) ∷
   rw 2 (q153 c4) ∷
   rw 1 (q154 c4) ∷
   rw 0 (q155 c4) ∷
   rw 1 (q156 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q157 : Ws → Eqn
  q157 c4 = eqn (Sw01 ∷ Toff413 ∷ []) (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 (lit c4))
  q158 : Ws → Eqn
  q158 c4 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wl0138 (lit c4))
  q159 : Ws → Eqn
  q159 c4 = eqn (Toff403 ∷ CS12 ∷ []) (CS12 ∷ Toff403 ∷ []) (lem-auto-TOFF012-∣-CS34-at0410233142 c4)
  q160 : Ws → Eqn
  q160 c4 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wl0035 (lit c4))
  q161 : Ws → Eqn
  q161 c4 = eqn (Sw01 ∷ Toff403 ∷ []) (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 (lit c4))

-- auto TOFF012 | CS34 @04233042: 7 steps
lem-auto-TOFF012-∣-CS34-at04233042 : Ws → ⟪ (Toff413 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff413 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at04233042 c4 = derive (Toff413 ∷ CS02 ∷ []) (CS02 ∷ Toff413 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q157 c4) ∷
   rw⁻ 2 (q158 c4) ∷
   rw 1 (q159 c4) ∷
   rw⁻ 0 (q160 c4) ∷
   rw 1 (q161 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q162 : Ws → Eqn
  q162 c4 = eqn (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) (wl0091 (lit c4))
  q163 : Ws → Eqn
  q163 c4 = eqn (Sw12 ∷ CS01 ∷ []) (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4))
  q164 : Ws → Eqn
  q164 c4 = eqn (Toff413 ∷ CS02 ∷ []) (CS02 ∷ Toff413 ∷ []) (lem-auto-TOFF012-∣-CS34-at04233042 c4)
  q165 : Ws → Eqn
  q165 c4 = eqn (Sw12 ∷ CS02 ∷ []) (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4))
  q166 : Ws → Eqn
  q166 c4 = eqn (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) (wl0085 (lit c4))

-- auto TOFF012 | CS34 @0412233041: 7 steps
lem-auto-TOFF012-∣-CS34-at0412233041 : Ws → ⟪ (Toff423 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff423 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at0412233041 c4 = derive (Toff423 ∷ CS01 ∷ []) (CS01 ∷ Toff423 ∷ [])
  (rw⁻ 0 (q14 c4) ∷
   rw 1 (q162 c4) ∷
   rw 2 (q163 c4) ∷
   rw 1 (q164 c4) ∷
   rw 0 (q165 c4) ∷
   rw 1 (q166 c4) ∷
   rw 2 (q14 c4) ∷ []) Eq.refl

private
  q167 : Ws → Eqn
  q167 c4 = eqn (Sw01 ∷ Toff423 ∷ []) (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ))
  q168 : Ws → Eqn
  q168 c4 = eqn (CS01 ∷ Sw01 ∷ []) (Sw01 ∷ CS01 ∷ []) (wl0132 (lit c4))
  q169 : Ws → Eqn
  q169 c4 = eqn (Toff423 ∷ CS01 ∷ []) (CS01 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-CS34-at0412233041 c4)

-- auto TOFF012 | CS34 @0412233140: 7 steps
lem-auto-TOFF012-∣-CS34-at0412233140 : Ws → ⟪ (Toff423 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff423 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at0412233140 c4 = derive (Toff423 ∷ CS01 ∷ []) (CS01 ∷ Toff423 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q167 c4) ∷
   rw⁻ 2 (q168 c4) ∷
   rw 1 (q169 c4) ∷
   rw⁻ 0 (q168 c4) ∷
   rw 1 (q167 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q170 : Ws → Eqn
  q170 c4 = eqn (Bx⁻0-1234 ∷ CS01 ∷ []) (CS01 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS10 c4)
  q171 : Ws → Eqn
  q171 c4 = eqn (Toff423 ∷ CS01 ∷ []) (CS01 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-CS34-at0412233140 c4)
  q172 : Ws → Eqn
  q172 c4 = eqn (CS01 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS01 ∷ []) (wp0101 c4)
  q173 : Ws → Eqn
  q173 c4 = eqn (CS01 ∷ CS14 ∷ []) (CS14 ∷ CS01 ∷ []) (wp0102 c4)

-- auto SBOXd(0;1;23;4) | CS10: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS10 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS10 c4 = derive (Sb⁻0-1-23-4 ∷ CS01 ∷ []) (CS01 ∷ Sb⁻0-1-23-4 ∷ [])
  (re 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) ∷
   rw 4 (q170 c4) ∷
   rw 3 (q171 c4) ∷
   re 2 1 (CS14⁻ ∷ []) ∷
   rw⁻ 2 (q172 c4) ∷
   re 3 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw 1 (q171 c4) ∷
   re 0 1 (CS14 ∷ []) ∷
   rw⁻ 0 (q173 c4) ∷
   re 1 1 (Sb0-1-4-3 ∷ []) ∷
   re 1 5 (Sb⁻0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q174 : Ws → Eqn
  q174 c4 = eqn (Sw23 ∷ CS03 ∷ []) (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 (lit c4))
  q175 : Ws → Eqn
  q175 c4 = eqn (Sb⁻0-1-23-4 ∷ CS02 ∷ []) (CS02 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20 c4)
  q176 : Ws → Eqn
  q176 c4 = eqn (Sw23 ∷ CS02 ∷ []) (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4))

-- auto SBOXd(0;1;23;4) | CS20 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ CS03 ∷ []) (CS03 ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q174 c4) ∷
   rw 1 (q175 c4) ∷
   rw 0 (q176 c4) ∷
   rw 1 (q28 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q177 : Ws → Eqn
  q177 c4 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (c₂ (CS) (Swap))
  q178 : Ws → Eqn
  q178 c4 = eqn (Sb⁻0-1-23-4 ∷ CS01 ∷ []) (CS01 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS10 c4)

-- auto SBOXd(0;1;23;4) | CS10 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS10-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS10-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ CS01 ∷ []) (CS01 ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q25 c4) ∷
   rw⁻ 2 (q177 c4) ∷
   rw 1 (q178 c4) ∷
   rw⁻ 0 (q177 c4) ∷
   rw 1 (q28 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q179 : Ws → Eqn
  q179 c4 = eqn (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0333 (lit c4))
  q180 : Ws → Eqn
  q180 c4 = eqn (Sb⁻0-1-32-4 ∷ CS03 ∷ []) (CS03 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20-at2332 c4)
  q181 : Ws → Eqn
  q181 c4 = eqn (Bx⁻0-1324 ∷ []) (Bx0-1324 ∷ []) (lem-BOXd-BOX-at2332 c4)
  q182 : Ws → Eqn
  q182 c4 = eqn (Bx0-1324 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at2332 c4)
  q183 : Ws → Eqn
  q183 c4 = eqn (CCZ024 ∷ CX13 ∷ []) (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4))
  q184 : Ws → Eqn
  q184 c4 = eqn (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ []) (wp0103 c4)
  q185 : Ws → Eqn
  q185 c4 = eqn (CX13 ∷ CS03⁻ ∷ CX13 ∷ Toff013 ∷ []) (Toff013 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (wl0334 (lit c4))
  q186 : Ws → Eqn
  q186 c4 = eqn (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (Toff423 ∷ []) (wl0335 (lit c4))
  q187 : Ws → Eqn
  q187 c4 = eqn (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4⁻ ∷ []) (K4⁻ ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (wp0104 c4)
  q188 : Ws → Eqn
  q188 c4 = eqn (CCZ234 ∷ []) (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (wl0336 (lit c4))
  q189 : Ws → Eqn
  q189 c4 = eqn (CS34 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS34 ∷ []) (wp0105 c4)
  q190 : Ws → Eqn
  q190 c4 = eqn (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) (CX32 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (wl0337 (lit c4))
  q191 : Ws → Eqn
  q191 c4 = eqn (CS24⁻ ∷ CX13 ∷ []) (CX13 ∷ CS24⁻ ∷ []) (wl0338 (lit c4))
  q192 : Ws → Eqn
  q192 c4 = eqn (CS03⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS03⁻ ∷ []) (wp0106 c4)
  q193 : Ws → Eqn
  q193 c4 = eqn (CS24 ∷ CX13 ∷ []) (CX13 ∷ CS24 ∷ []) (wl0339 (lit c4))
  q194 : Ws → Eqn
  q194 c4 = eqn (CS03⁻ ∷ CS24 ∷ []) (CS24 ∷ CS03⁻ ∷ []) (wp0107 c4)
  q195 : Ws → Eqn
  q195 c4 = eqn (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4 ∷ []) (K4 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (wp0108 c4)
  q196 : Ws → Eqn
  q196 c4 = eqn (CS14⁻ ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS14⁻ ∷ []) (wp0109 c4)
  q197 : Ws → Eqn
  q197 c4 = eqn (CS14 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS14 ∷ []) (wp0110 c4)
  q198 : Ws → Eqn
  q198 c4 = eqn (Sb⁻0-1-32-4 ∷ CS01 ∷ []) (CS01 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS10-at2332 c4)

-- auto SBOXd(0;1;23;4) | CCZ013: 56 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ013 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ013 c4 = derive (Sb⁻0-1-23-4 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sb⁻0-1-23-4 ∷ [])
  (rw 1 (q179 c4) ∷
   rw 0 (q29 c4) ∷
   rw 0 (q180 c4) ∷
   re 1 1 (Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ []) ∷
   rw 5 (q181 c4) ∷
   rw 5 (q182 c4) ∷
   rw 8 (q183 c4) ∷
   rw 9 (q184 c4) ∷
   rw 10 (q183 c4) ∷
   rw⁻ 7 (q185 c4) ∷
   rw 6 (q183 c4) ∷
   rw 7 (q184 c4) ∷
   rw 8 (q183 c4) ∷
   rw⁻ 5 (q185 c4) ∷
   rw⁻ 8 (q182 c4) ∷
   rw⁻ 8 (q181 c4) ∷
   rw⁻ 4 (q186 c4) ∷
   rw⁻ 6 (q187 c4) ∷
   rw 5 (q188 c4) ∷
   rw 9 (q189 c4) ∷
   rw⁻ 8 (q190 c4) ∷
   rw 7 (q191 c4) ∷
   rw⁻ 8 (q192 c4) ∷
   rw 9 (q191 c4) ∷
   rw⁻ 6 (q190 c4) ∷
   rw 5 (q193 c4) ∷
   rw⁻ 6 (q194 c4) ∷
   rw 7 (q193 c4) ∷
   rw⁻ 8 (q188 c4) ∷
   rw⁻ 4 (q195 c4) ∷
   rw 7 (q186 c4) ∷
   re 3 1 (CS14⁻ ∷ []) ∷
   rw 3 (q196 c4) ∷
   re 6 1 (Sb⁻0-1-4-2 ∷ []) ∷
   rw⁻ 2 (q186 c4) ∷
   rw⁻ 4 (q187 c4) ∷
   rw 3 (q188 c4) ∷
   rw 7 (q189 c4) ∷
   rw⁻ 6 (q190 c4) ∷
   rw 5 (q191 c4) ∷
   rw⁻ 6 (q192 c4) ∷
   rw 7 (q191 c4) ∷
   rw⁻ 4 (q190 c4) ∷
   rw 3 (q193 c4) ∷
   rw⁻ 4 (q194 c4) ∷
   rw 5 (q193 c4) ∷
   rw⁻ 6 (q188 c4) ∷
   rw⁻ 2 (q195 c4) ∷
   rw 5 (q186 c4) ∷
   re 1 1 (CS14 ∷ []) ∷
   rw 1 (q197 c4) ∷
   re 4 1 (Sb0-1-4-2 ∷ []) ∷
   re 4 5 (Sb⁻0-1-32-4 ∷ []) ∷
   rw 4 (q198 c4) ∷
   rw⁻ 5 (q29 c4) ∷
   rw⁻ 0 (q179 c4) ∷ []) Eq.refl

private
  q199 : Ws → Eqn
  q199 c4 = eqn (K0⁻ ∷ Toff423 ∷ []) (Toff423 ∷ K0⁻ ∷ []) (wl0340 (lit c4))
  q200 : Ws → Eqn
  q200 c4 = eqn (CS14⁻ ∷ K0⁻ ∷ []) (K0⁻ ∷ CS14⁻ ∷ []) (wp0111 c4)
  q201 : Ws → Eqn
  q201 c4 = eqn (CS14 ∷ K0⁻ ∷ []) (K0⁻ ∷ CS14 ∷ []) (wp0112 c4)

-- auto SBOXd(0;1;23;4) | Kd0: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd0 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd0 c4 = derive (Sb⁻0-1-23-4 ∷ K0⁻ ∷ []) (K0⁻ ∷ Sb⁻0-1-23-4 ∷ [])
  (re 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) ∷
   rw 4 (q89 c4) ∷
   rw⁻ 3 (q199 c4) ∷
   re 2 1 (CS14⁻ ∷ []) ∷
   rw 2 (q200 c4) ∷
   re 3 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw⁻ 1 (q199 c4) ∷
   re 0 1 (CS14 ∷ []) ∷
   rw 0 (q201 c4) ∷
   re 1 1 (Sb0-1-4-3 ∷ []) ∷
   re 1 5 (Sb⁻0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q202 : Ws → Eqn
  q202 c4 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (c₁ (K) (Swap ↑))
  q203 : Ws → Eqn
  q203 c4 = eqn (Sb⁻0-1-23-4 ∷ K0 ∷ []) (K0 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K0 c4)

-- auto SBOXd(0;1;23;4) | K0 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K0-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K0-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ K0 ∷ []) (K0 ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q25 c4) ∷
   rw⁻ 2 (q202 c4) ∷
   rw 1 (q203 c4) ∷
   rw⁻ 0 (q202 c4) ∷
   rw 1 (q28 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q204 : Ws → Eqn
  q204 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4))
  q205 : Ws → Eqn
  q205 c4 = eqn (Sb⁻0-1-23-4 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ013 c4)
  q206 : Ws → Eqn
  q206 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4))

-- auto SBOXd(0;1;23;4) | CCZ013 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ013-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ013-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q204 c4) ∷
   rw 1 (q205 c4) ∷
   rw 0 (q206 c4) ∷
   rw 1 (q28 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q207 : Ws → Eqn
  q207 c4 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑))
  q208 : Ws → Eqn
  q208 c4 = eqn (Sb⁻0-1-23-4 ∷ K0⁻ ∷ []) (K0⁻ ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd0 c4)

-- auto SBOXd(0;1;23;4) | Kd0 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd0-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd0-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ K0⁻ ∷ []) (K0⁻ ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q25 c4) ∷
   rw⁻ 2 (q207 c4) ∷
   rw 1 (q208 c4) ∷
   rw⁻ 0 (q207 c4) ∷
   rw 1 (q28 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q209 : Ws → Eqn
  q209 c4 = eqn (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) (wl0341 (lit c4))
  q210 : Ws → Eqn
  q210 c4 = eqn (Sb⁻0-1-32-4 ∷ K0 ∷ []) (K0 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K0-at2332 c4)
  q211 : Ws → Eqn
  q211 c4 = eqn (Sb⁻0-1-32-4 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ013-at2332 c4)
  q212 : Ws → Eqn
  q212 c4 = eqn (Sb⁻0-1-32-4 ∷ K0⁻ ∷ []) (K0⁻ ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd0-at2332 c4)

-- auto SBOXd(0;1;23;4) | TOFF012: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012 c4 = derive (Sb⁻0-1-23-4 ∷ Toff012 ∷ []) (Toff012 ∷ Sb⁻0-1-23-4 ∷ [])
  (rw⁻ 1 (q209 c4) ∷
   rw 0 (q29 c4) ∷
   rw 0 (q210 c4) ∷
   rw 1 (q211 c4) ∷
   rw 2 (q212 c4) ∷
   rw⁻ 3 (q29 c4) ∷
   rw 0 (q209 c4) ∷ []) Eq.refl

private
  q213 : Ws → Eqn
  q213 c4 = eqn (Sw23 ∷ Bx0-1324 ∷ []) (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4))
  q214 : Ws → Eqn
  q214 c4 = eqn (Sw23 ∷ Bx0-1234 ∷ []) (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4))

-- CS20-beta-c @2332: 7 steps
lem-CS20-beta-c-at2332 : Ws → ⟪ (CS03 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CS03 ∷ []) ⟫ʷ
lem-CS20-beta-c-at2332 c4 = derive (CS03 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS03 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q174 c4) ∷
   rw 2 (q213 c4) ∷
   rw 1 (q121 c4) ∷
   rw 0 (q214 c4) ∷
   rw 1 (q176 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q215 : Ws → Eqn
  q215 c4 = eqn (Sw34 ∷ CS04 ∷ []) (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 (lit c4))
  q216 : Ws → Eqn
  q216 c4 = eqn (Sw34 ∷ Bx0-1423 ∷ []) (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4))
  q217 : Ws → Eqn
  q217 c4 = eqn (CS03 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS03 ∷ []) (lem-CS20-beta-c-at2332 c4)
  q218 : Ws → Eqn
  q218 c4 = eqn (Sw34 ∷ Bx0-1324 ∷ []) (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4))
  q219 : Ws → Eqn
  q219 c4 = eqn (Sw34 ∷ CS03 ∷ []) (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 (lit c4))

-- CS20-beta-c @243243: 7 steps
lem-CS20-beta-c-at243243 : Ws → ⟪ (CS04 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS04 ∷ []) ⟫ʷ
lem-CS20-beta-c-at243243 c4 = derive (CS04 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS04 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q215 c4) ∷
   rw 2 (q216 c4) ∷
   rw 1 (q217 c4) ∷
   rw 0 (q218 c4) ∷
   rw 1 (q219 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q220 : Ws → Eqn
  q220 c4 = eqn (CS04 ∷ []) (CS04 ∷ []) (wp0113 c4)
  q221 : Ws → Eqn
  q221 c4 = eqn (CS04 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS04 ∷ []) (lem-CS20-beta-c-at243243 c4)

-- auto BOXd(0;1234) | CS40: 9 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS40 : Ws → ⟪ (Bx⁻0-1234 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS40 c4 = derive (Bx⁻0-1234 ∷ CS04 ∷ []) (CS04 ∷ Bx⁻0-1234 ∷ [])
  (rw 0 (q1 c4) ∷
   rw 1 (q220 c4) ∷
   rw 0 (q2 c4) ∷
   rw 0 (q3 c4) ∷
   rw⁻ 0 (q221 c4) ∷
   rw 1 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw 0 (q220 c4) ∷
   rw⁻ 1 (q1 c4) ∷ []) Eq.refl

private
  q222 : Ws → Eqn
  q222 c4 = eqn (Sw23 ∷ CS03⁻ ∷ []) (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 (lit c4))
  q223 : Ws → Eqn
  q223 c4 = eqn (CS02⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CS20-beta-ci c4)
  q224 : Ws → Eqn
  q224 c4 = eqn (Sw23 ∷ CS02⁻ ∷ []) (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 (lit c4))

-- CS20-beta-ci @2332: 7 steps
lem-CS20-beta-ci-at2332 : Ws → ⟪ (CS03⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-CS20-beta-ci-at2332 c4 = derive (CS03⁻ ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS03⁻ ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q222 c4) ∷
   rw 2 (q213 c4) ∷
   rw 1 (q223 c4) ∷
   rw 0 (q214 c4) ∷
   rw 1 (q224 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q225 : Ws → Eqn
  q225 c4 = eqn (Sw34 ∷ CS04⁻ ∷ []) (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 (lit c4))
  q226 : Ws → Eqn
  q226 c4 = eqn (CS03⁻ ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS03⁻ ∷ []) (lem-CS20-beta-ci-at2332 c4)
  q227 : Ws → Eqn
  q227 c4 = eqn (Sw34 ∷ CS03⁻ ∷ []) (CS04⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd03 (lit c4))

-- CS20-beta-ci @243243: 7 steps
lem-CS20-beta-ci-at243243 : Ws → ⟪ (CS04⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-CS20-beta-ci-at243243 c4 = derive (CS04⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS04⁻ ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q225 c4) ∷
   rw 2 (q216 c4) ∷
   rw 1 (q226 c4) ∷
   rw 0 (q218 c4) ∷
   rw 1 (q227 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q228 : Ws → Eqn
  q228 c4 = eqn (CS04⁻ ∷ []) (CS04⁻ ∷ []) (wp0114 c4)
  q229 : Ws → Eqn
  q229 c4 = eqn (CS04⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS04⁻ ∷ []) (lem-CS20-beta-ci-at243243 c4)

-- auto BOXd(0;1234) | CSd40: 9 steps
lem-auto-BOXd⟨0·1234⟩-∣-CSd40 : Ws → ⟪ (Bx⁻0-1234 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CSd40 c4 = derive (Bx⁻0-1234 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx⁻0-1234 ∷ [])
  (rw 0 (q1 c4) ∷
   rw 1 (q228 c4) ∷
   rw 0 (q2 c4) ∷
   rw 0 (q3 c4) ∷
   rw⁻ 0 (q229 c4) ∷
   rw 1 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw 0 (q228 c4) ∷
   rw⁻ 1 (q1 c4) ∷ []) Eq.refl

private
  q230 : Ws → Eqn
  q230 c4 = eqn (CCZ012 ∷ Bx3-0142 ∷ []) (Bx3-0142 ∷ CCZ012 ∷ []) (lem-c124-beta-at0310213442 c4)

-- auto CCZ012 | BOX(3;0142): 1 steps
lem-auto-CCZ012-∣-BOX⟨3·0142⟩ : Ws → ⟪ (CCZ012 ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0142⟩ c4 = derive (CCZ012 ∷ Bx3-0142 ∷ []) (Bx3-0142 ∷ CCZ012 ∷ [])
  (rw 0 (q230 c4) ∷ []) Eq.refl

private
  q231 : Ws → Eqn
  q231 c4 = eqn (Bx0-1234 ∷ K0 ∷ []) (K0 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0 c4)

-- auto SBOX(0;1;23;4) | K0: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0 : Ws → ⟪ (Sb0-1-23-4 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0 c4 = derive (Sb0-1-23-4 ∷ K0 ∷ []) (K0 ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw 4 (q118 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw⁻ 3 (q117 c4) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw 2 (q119 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw⁻ 1 (q117 c4) ∷
   rw 0 (q231 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q232 : Ws → Eqn
  q232 c4 = eqn (CS03 ∷ []) (CS03 ∷ []) (wl0342 (lit c4))
  q233 : Ws → Eqn
  q233 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1324 ∷ []) (lem-sym23 c4)
  q234 : Ws → Eqn
  q234 c4 = eqn (Bx0-1324 ∷ []) (Bx0-1234 ∷ []) (lem-sym23-at2332 c4)

-- auto BOX(0;1234) | CS30: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CS30 : Ws → ⟪ (Bx0-1234 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS30 c4 = derive (Bx0-1234 ∷ CS03 ∷ []) (CS03 ∷ Bx0-1234 ∷ [])
  (rw 1 (q232 c4) ∷
   rw 0 (q233 c4) ∷
   rw⁻ 0 (q217 c4) ∷
   rw 1 (q234 c4) ∷
   rw 0 (q232 c4) ∷ []) Eq.refl

private
  q235 : Ws → Eqn
  q235 c4 = eqn (CS03 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS03 ∷ []) (wp0115 c4)
  q236 : Ws → Eqn
  q236 c4 = eqn (CS03 ∷ Toff423 ∷ []) (Toff423 ∷ CS03 ∷ []) (wp0116 c4)
  q237 : Ws → Eqn
  q237 c4 = eqn (CS03 ∷ CS14 ∷ []) (CS14 ∷ CS03 ∷ []) (wp0117 c4)
  q238 : Ws → Eqn
  q238 c4 = eqn (Bx0-1234 ∷ CS03 ∷ []) (CS03 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS30 c4)

-- auto SBOX(0;1;23;4) | CS30: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30 : Ws → ⟪ (Sb0-1-23-4 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30 c4 = derive (Sb0-1-23-4 ∷ CS03 ∷ []) (CS03 ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q235 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw⁻ 3 (q236 c4) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw⁻ 2 (q237 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw⁻ 1 (q236 c4) ∷
   rw 0 (q238 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q239 : Ws → Eqn
  q239 c4 = eqn (CCZ124 ∷ []) (CCZ124 ∷ []) (wl0343 (lit c4))
  q240 : Ws → Eqn
  q240 c4 = eqn (CCZ124 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ []) (lem-c124-beta c4)

-- auto BOX(0;1234) | CCZ214: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ214 : Ws → ⟪ (Bx0-1234 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ214 c4 = derive (Bx0-1234 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1234 ∷ [])
  (rw 1 (q239 c4) ∷
   rw⁻ 0 (q240 c4) ∷
   rw 0 (q239 c4) ∷ []) Eq.refl

-- auto BOX(0;1234) | CS10: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CS10 : Ws → ⟪ (Bx0-1234 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS10 c4 = derive (Bx0-1234 ∷ CS01 ∷ []) (CS01 ∷ Bx0-1234 ∷ [])
  (rw 1 (q126 c4) ∷
   rw 0 (q77 c4) ∷
   rw⁻ 0 (q127 c4) ∷
   rw 1 (q83 c4) ∷
   rw 0 (q126 c4) ∷ []) Eq.refl

private
  q241 : Ws → Eqn
  q241 c4 = eqn (Bx0-1234 ∷ CS01 ∷ []) (CS01 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS10 c4)

-- auto SBOX(0;1;23;4) | CS10: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10 : Ws → ⟪ (Sb0-1-23-4 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10 c4 = derive (Sb0-1-23-4 ∷ CS01 ∷ []) (CS01 ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q172 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw 3 (q171 c4) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw⁻ 2 (q173 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw 1 (q171 c4) ∷
   rw 0 (q241 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q242 : Ws → Eqn
  q242 c4 = eqn (Sw23 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4))
  q243 : Ws → Eqn
  q243 c4 = eqn (Sb0-1-23-4 ∷ CS03 ∷ []) (CS03 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30 c4)
  q244 : Ws → Eqn
  q244 c4 = eqn (Sw23 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | CS30 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-at2332 c4 = derive (Sb0-1-32-4 ∷ CS02 ∷ []) (CS02 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q242 c4) ∷
   rw 2 (q176 c4) ∷
   rw 1 (q243 c4) ∷
   rw 0 (q174 c4) ∷
   rw 1 (q244 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q245 : Ws → Eqn
  q245 c4 = eqn (CX23 ∷ Sw12 ∷ []) (Sw12 ∷ CX13 ∷ []) (wl0052 (lit c4))
  q246 : Ws → Eqn
  q246 c4 = eqn (Sw12 ∷ Bx0-2134 ∷ []) (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4))
  q247 : Ws → Eqn
  q247 c4 = eqn (CX23 ∷ Bx0-1234 ∷ CX23 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CX23-beta c4)
  q248 : Ws → Eqn
  q248 c4 = eqn (Sw12 ∷ Bx0-1234 ∷ []) (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4))
  q249 : Ws → Eqn
  q249 c4 = eqn (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) (wl0078 (lit c4))

-- CX23-beta @1221: 8 steps
lem-CX23-beta-at1221 : Ws → ⟪ (CX13 ∷ Bx0-2134 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CX23-beta-at1221 c4 = derive (CX13 ∷ Bx0-2134 ∷ CX13 ∷ []) (Bx0-2134 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q14 c4) ∷
   rw⁻ 1 (q245 c4) ∷
   rw 2 (q246 c4) ∷
   rw⁻ 3 (q245 c4) ∷
   rw 1 (q247 c4) ∷
   rw 0 (q248 c4) ∷
   rw⁻ 1 (q249 c4) ∷
   rw 2 (q14 c4) ∷ []) Eq.refl

private
  q250 : Ws → Eqn
  q250 c4 = eqn (Sw23 ∷ CCZ134 ∷ []) (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4))
  q251 : Ws → Eqn
  q251 c4 = eqn (Bx0-1234 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214 c4)
  q252 : Ws → Eqn
  q252 c4 = eqn (Sw23 ∷ CCZ124 ∷ []) (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4))

-- auto BOX(0;1234) | CCZ214 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at2332 c4 = derive (Bx0-1324 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q213 c4) ∷
   rw 2 (q250 c4) ∷
   rw 1 (q251 c4) ∷
   rw 0 (q252 c4) ∷
   rw 1 (q214 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q253 : Ws → Eqn
  q253 c4 = eqn (Sb0-1-23-4 ∷ CS01 ∷ []) (CS01 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10 c4)

-- auto SBOX(0;1;23;4) | CS10 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-at2332 c4 = derive (Sb0-1-32-4 ∷ CS01 ∷ []) (CS01 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q242 c4) ∷
   rw⁻ 2 (q177 c4) ∷
   rw 1 (q253 c4) ∷
   rw⁻ 0 (q177 c4) ∷
   rw 1 (q244 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q254 : Ws → Eqn
  q254 c4 = eqn (Bx0-1234 ∷ K0⁻ ∷ []) (K0⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0 c4)

-- auto SBOX(0;1;23;4) | Kd0: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0 : Ws → ⟪ (Sb0-1-23-4 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0 c4 = derive (Sb0-1-23-4 ∷ K0⁻ ∷ []) (K0⁻ ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw 4 (q200 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw⁻ 3 (q199 c4) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw 2 (q201 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw⁻ 1 (q199 c4) ∷
   rw 0 (q254 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q255 : Ws → Eqn
  q255 c4 = eqn (Sb0-1-23-4 ∷ K0 ∷ []) (K0 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0 c4)

-- auto SBOX(0;1;23;4) | K0 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 c4 = derive (Sb0-1-32-4 ∷ K0 ∷ []) (K0 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q242 c4) ∷
   rw⁻ 2 (q202 c4) ∷
   rw 1 (q255 c4) ∷
   rw⁻ 0 (q202 c4) ∷
   rw 1 (q244 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q256 : Ws → Eqn
  q256 c4 = eqn (Sb0-1-23-4 ∷ K0⁻ ∷ []) (K0⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0 c4)

-- auto SBOX(0;1;23;4) | Kd0 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332 c4 = derive (Sb0-1-32-4 ∷ K0⁻ ∷ []) (K0⁻ ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q242 c4) ∷
   rw⁻ 2 (q207 c4) ∷
   rw 1 (q256 c4) ∷
   rw⁻ 0 (q207 c4) ∷
   rw 1 (q244 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q257 : Ws → Eqn
  q257 c4 = eqn (Sw23 ∷ Bx0-3412 ∷ []) (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4))
  q258 : Ws → Eqn
  q258 c4 = eqn (Sw23 ∷ Bx0-2413 ∷ []) (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ (lit c4))

-- CS12-beta @13243142: 7 steps
lem-CS12-beta-at13243142 : Ws → ⟪ (CS34 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ CS34 ∷ []) ⟫ʷ
lem-CS12-beta-at13243142 c4 = derive (CS34 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ CS34 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw⁻ 1 (q140 c4) ∷
   rw 2 (q257 c4) ∷
   rw 1 (q80 c4) ∷
   rw 0 (q258 c4) ∷
   rw⁻ 1 (q138 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q259 : Ws → Eqn
  q259 c4 = eqn (CS34 ∷ []) (CS34 ∷ []) (wl0344 (lit c4))
  q260 : Ws → Eqn
  q260 c4 = eqn (Bx0-1324 ∷ []) (Bx0-1342 ∷ []) (lem-sym34-at2332 c4)
  q261 : Ws → Eqn
  q261 c4 = eqn (Bx0-1342 ∷ []) (Bx0-3142 ∷ []) (lem-sym12-at233442 c4)
  q262 : Ws → Eqn
  q262 c4 = eqn (Bx0-3142 ∷ []) (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4)
  q263 : Ws → Eqn
  q263 c4 = eqn (CS34 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ CS34 ∷ []) (lem-CS12-beta-at13243142 c4)
  q264 : Ws → Eqn
  q264 c4 = eqn (Bx0-3412 ∷ []) (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4)
  q265 : Ws → Eqn
  q265 c4 = eqn (Bx0-3142 ∷ []) (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4)
  q266 : Ws → Eqn
  q266 c4 = eqn (Bx0-3124 ∷ []) (Bx0-1324 ∷ []) (lem-sym12-at132132 c4)

-- auto BOX(0;1234) | CS43: 11 steps
lem-auto-BOX⟨0·1234⟩-∣-CS43 : Ws → ⟪ (Bx0-1234 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS43 c4 = derive (Bx0-1234 ∷ CS34 ∷ []) (CS34 ∷ Bx0-1234 ∷ [])
  (rw 1 (q259 c4) ∷
   rw 0 (q233 c4) ∷
   rw 0 (q260 c4) ∷
   rw 0 (q261 c4) ∷
   rw 0 (q262 c4) ∷
   rw⁻ 0 (q263 c4) ∷
   rw 1 (q264 c4) ∷
   rw 1 (q265 c4) ∷
   rw 1 (q266 c4) ∷
   rw 1 (q234 c4) ∷
   rw 0 (q259 c4) ∷ []) Eq.refl

private
  q267 : Ws → Eqn
  q267 c4 = eqn (CS14⁻ ∷ CS34 ∷ []) (CS34 ∷ CS14⁻ ∷ []) (wl0345 (lit c4))
  q268 : Ws → Eqn
  q268 c4 = eqn (CS34 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS34 ∷ []) (wl0346 (lit c4))
  q269 : Ws → Eqn
  q269 c4 = eqn (Bx0-1234 ∷ CS34 ∷ []) (CS34 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS43 c4)

-- auto SBOX(0;1;23;4) | CS43: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS43 : Ws → ⟪ (Sb0-1-23-4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS43 c4 = derive (Sb0-1-23-4 ∷ CS34 ∷ []) (CS34 ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw 4 (q267 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw⁻ 1 (q268 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw 0 (q269 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

-- auto BOX(0;1234) | CS34: 9 steps
lem-auto-BOX⟨0·1234⟩-∣-CS34 : Ws → ⟪ (Bx0-1234 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS34 c4 = derive (Bx0-1234 ∷ CS34 ∷ []) (CS34 ∷ Bx0-1234 ∷ [])
  (rw 0 (q233 c4) ∷
   rw 0 (q260 c4) ∷
   rw 0 (q261 c4) ∷
   rw 0 (q262 c4) ∷
   rw⁻ 0 (q263 c4) ∷
   rw 1 (q264 c4) ∷
   rw 1 (q265 c4) ∷
   rw 1 (q266 c4) ∷
   rw 1 (q234 c4) ∷ []) Eq.refl

private
  q270 : Ws → Eqn
  q270 c4 = eqn (Bx0-1234 ∷ CS34 ∷ []) (CS34 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS34 c4)

-- auto SBOX(0;1;23;4) | CS34: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34 : Ws → ⟪ (Sb0-1-23-4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34 c4 = derive (Sb0-1-23-4 ∷ CS34 ∷ []) (CS34 ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw 4 (q267 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw⁻ 1 (q268 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw 0 (q270 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

-- auto BOX(0;1234) | CS20: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CS20 : Ws → ⟪ (Bx0-1234 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS20 c4 = derive (Bx0-1234 ∷ CS02 ∷ []) (CS02 ∷ Bx0-1234 ∷ [])
  (rw 1 (q120 c4) ∷
   rw⁻ 0 (q121 c4) ∷
   rw 0 (q120 c4) ∷ []) Eq.refl

private
  q271 : Ws → Eqn
  q271 c4 = eqn (Bx0-1234 ∷ CS02 ∷ []) (CS02 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS20 c4)

-- auto SBOX(0;1;23;4) | CS20: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20 : Ws → ⟪ (Sb0-1-23-4 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20 c4 = derive (Sb0-1-23-4 ∷ CS02 ∷ []) (CS02 ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q124 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw⁻ 3 (q123 c4) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw⁻ 2 (q125 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw⁻ 1 (q123 c4) ∷
   rw 0 (q271 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q272 : Ws → Eqn
  q272 c4 = eqn (CCZ134 ∷ []) (CCZ134 ∷ []) (wl0347 (lit c4))
  q273 : Ws → Eqn
  q273 c4 = eqn (CCZ134 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CCZ134 ∷ []) (lem-c124-beta-at2332 c4)

-- auto BOX(0;1234) | CCZ314: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ314 : Ws → ⟪ (Bx0-1234 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ314 c4 = derive (Bx0-1234 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1234 ∷ [])
  (rw 1 (q272 c4) ∷
   rw 0 (q233 c4) ∷
   rw⁻ 0 (q273 c4) ∷
   rw 1 (q234 c4) ∷
   rw 0 (q272 c4) ∷ []) Eq.refl

private
  q274 : Ws → Eqn
  q274 c4 = eqn (CS02⁻ ∷ []) (CS02⁻ ∷ []) (wl0348 (lit c4))

-- auto BOX(0;1234) | CSd20: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd20 : Ws → ⟪ (Bx0-1234 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd20 c4 = derive (Bx0-1234 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx0-1234 ∷ [])
  (rw 1 (q274 c4) ∷
   rw⁻ 0 (q223 c4) ∷
   rw 0 (q274 c4) ∷ []) Eq.refl

private
  q275 : Ws → Eqn
  q275 c4 = eqn (Sb0-1-23-4 ∷ CS02 ∷ []) (CS02 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20 c4)

-- auto SBOX(0;1;23;4) | CS20 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-at2332 c4 = derive (Sb0-1-32-4 ∷ CS03 ∷ []) (CS03 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q242 c4) ∷
   rw 2 (q174 c4) ∷
   rw 1 (q275 c4) ∷
   rw 0 (q176 c4) ∷
   rw 1 (q244 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q276 : Ws → Eqn
  q276 c4 = eqn (Bx0-1234 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ314 c4)

-- auto BOX(0;1234) | CCZ314 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ314-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ314-at2332 c4 = derive (Bx0-1324 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q213 c4) ∷
   rw 2 (q252 c4) ∷
   rw 1 (q276 c4) ∷
   rw 0 (q250 c4) ∷
   rw 1 (q214 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q277 : Ws → Eqn
  q277 c4 = eqn (Bx0-1234 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd20 c4)

-- auto BOX(0;1234) | CSd20 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd20-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd20-at2332 c4 = derive (Bx0-1324 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q213 c4) ∷
   rw 2 (q222 c4) ∷
   rw 1 (q277 c4) ∷
   rw 0 (q224 c4) ∷
   rw 1 (q214 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q278 : Ws → Eqn
  q278 c4 = eqn (Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4)
  q279 : Ws → Eqn
  q279 c4 = eqn (Sb0-1-32-4 ∷ CS03 ∷ []) (CS03 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-at2332 c4)
  q280 : Ws → Eqn
  q280 c4 = eqn (CX13 ∷ CX13 ∷ []) [] (wl0349 (lit c4))
  q281 : Ws → Eqn
  q281 c4 = eqn (CX13 ∷ Bx0-2134 ∷ CX13 ∷ []) (Bx0-2134 ∷ CCZ124 ∷ []) (lem-CX23-beta-at1221 c4)
  q282 : Ws → Eqn
  q282 c4 = eqn (Bx0-1324 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ314-at2332 c4)
  q283 : Ws → Eqn
  q283 c4 = eqn (Bx0-1324 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd20-at2332 c4)
  q284 : Ws → Eqn
  q284 c4 = eqn (CCZ124 ∷ CX13 ∷ []) (CX13 ∷ CCZ124 ∷ []) (wl0350 (lit c4))
  q285 : Ws → Eqn
  q285 c4 = eqn (CS03⁻ ∷ CCZ124 ∷ []) (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4))
  q286 : Ws → Eqn
  q286 c4 = eqn (CCZ124 ∷ CCZ124 ∷ []) [] (wl0351 (lit c4))
  q287 : Ws → Eqn
  q287 c4 = eqn (Sb0-1-32-4 ∷ CS01 ∷ []) (CS01 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-at2332 c4)

-- auto SBOX(0;1;23;4) | CCZ013: 64 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ013 : Ws → ⟪ (Sb0-1-23-4 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ013 c4 = derive (Sb0-1-23-4 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sb0-1-23-4 ∷ [])
  (rw 1 (q179 c4) ∷
   rw 0 (q278 c4) ∷
   rw 0 (q279 c4) ∷
   re 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) ∷
   re 5 1 (CS14⁻ ∷ []) ∷
   rw 5 (q196 c4) ∷
   re 8 1 (Sb⁻0-1-4-2 ∷ []) ∷
   rw⁻ 4 (q186 c4) ∷
   rw⁻ 6 (q187 c4) ∷
   rw 5 (q188 c4) ∷
   rw 9 (q189 c4) ∷
   rw⁻ 8 (q190 c4) ∷
   rw 7 (q191 c4) ∷
   rw⁻ 8 (q192 c4) ∷
   rw 9 (q191 c4) ∷
   rw⁻ 6 (q190 c4) ∷
   rw 5 (q193 c4) ∷
   rw⁻ 6 (q194 c4) ∷
   rw 7 (q193 c4) ∷
   rw⁻ 8 (q188 c4) ∷
   rw⁻ 4 (q195 c4) ∷
   rw 7 (q186 c4) ∷
   re 3 1 (CS14 ∷ []) ∷
   rw 3 (q197 c4) ∷
   re 6 1 (Sb0-1-4-2 ∷ []) ∷
   rw⁻ 2 (q186 c4) ∷
   rw⁻ 4 (q187 c4) ∷
   rw 3 (q188 c4) ∷
   rw 7 (q189 c4) ∷
   rw⁻ 6 (q190 c4) ∷
   rw 5 (q191 c4) ∷
   rw⁻ 6 (q192 c4) ∷
   rw 7 (q191 c4) ∷
   rw⁻ 4 (q190 c4) ∷
   rw 3 (q193 c4) ∷
   rw⁻ 4 (q194 c4) ∷
   rw 5 (q193 c4) ∷
   rw⁻ 6 (q188 c4) ∷
   rw⁻ 2 (q195 c4) ∷
   rw 5 (q186 c4) ∷
   rw⁻ 1 (q280 c4) ∷
   rw 3 (q234 c4) ∷
   rw 3 (q77 c4) ∷
   rw 2 (q281 c4) ∷
   rw 2 (q83 c4) ∷
   rw 2 (q233 c4) ∷
   rw 2 (q282 c4) ∷
   rw 3 (q283 c4) ∷
   rw⁻ 4 (q280 c4) ∷
   rw 6 (q234 c4) ∷
   rw 6 (q77 c4) ∷
   rw 5 (q281 c4) ∷
   rw 5 (q83 c4) ∷
   rw 5 (q233 c4) ∷
   rw 5 (q282 c4) ∷
   rw⁻ 1 (q284 c4) ∷
   rw⁻ 4 (q284 c4) ∷
   rw 3 (q285 c4) ∷
   rw⁻ 2 (q284 c4) ∷
   rw 1 (q286 c4) ∷
   re 4 5 (Sb0-1-32-4 ∷ []) ∷
   rw 4 (q287 c4) ∷
   rw⁻ 5 (q278 c4) ∷
   rw⁻ 0 (q179 c4) ∷ []) Eq.refl

private
  q288 : Ws → Eqn
  q288 c4 = eqn (Sb0-1-23-4 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ013 c4)

-- auto SBOX(0;1;23;4) | CCZ013 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ013-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ013-at2332 c4 = derive (Sb0-1-32-4 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q242 c4) ∷
   rw 2 (q204 c4) ∷
   rw 1 (q288 c4) ∷
   rw 0 (q206 c4) ∷
   rw 1 (q244 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q289 : Ws → Eqn
  q289 c4 = eqn (Sb0-1-32-4 ∷ K0 ∷ []) (K0 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 c4)
  q290 : Ws → Eqn
  q290 c4 = eqn (Sb0-1-32-4 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ013-at2332 c4)
  q291 : Ws → Eqn
  q291 c4 = eqn (Sb0-1-32-4 ∷ K0⁻ ∷ []) (K0⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332 c4)

-- auto SBOX(0;1;23;4) | TOFF012: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012 : Ws → ⟪ (Sb0-1-23-4 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012 c4 = derive (Sb0-1-23-4 ∷ Toff012 ∷ []) (Toff012 ∷ Sb0-1-23-4 ∷ [])
  (rw⁻ 1 (q209 c4) ∷
   rw 0 (q278 c4) ∷
   rw 0 (q289 c4) ∷
   rw 1 (q290 c4) ∷
   rw 2 (q291 c4) ∷
   rw⁻ 3 (q278 c4) ∷
   rw 0 (q209 c4) ∷ []) Eq.refl

private
  q292 : Ws → Eqn
  q292 c4 = eqn (CS24 ∷ []) (CS24 ∷ []) (wl0352 (lit c4))

-- auto BOX(0;1234) | CS42: 9 steps
lem-auto-BOX⟨0·1234⟩-∣-CS42 : Ws → ⟪ (Bx0-1234 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS42 c4 = derive (Bx0-1234 ∷ CS24 ∷ []) (CS24 ∷ Bx0-1234 ∷ [])
  (rw 1 (q292 c4) ∷
   rw 0 (q77 c4) ∷
   rw 0 (q78 c4) ∷
   rw 0 (q79 c4) ∷
   rw⁻ 0 (q80 c4) ∷
   rw 1 (q81 c4) ∷
   rw 1 (q82 c4) ∷
   rw 1 (q83 c4) ∷
   rw 0 (q292 c4) ∷ []) Eq.refl

private
  q293 : Ws → Eqn
  q293 c4 = eqn (CS14⁻ ∷ CS24 ∷ []) (CS24 ∷ CS14⁻ ∷ []) (wl0303 (lit c4))
  q294 : Ws → Eqn
  q294 c4 = eqn (CS24 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS24 ∷ []) (wl0304 (lit c4))
  q295 : Ws → Eqn
  q295 c4 = eqn (Bx0-1234 ∷ CS24 ∷ []) (CS24 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS42 c4)

-- auto SBOX(0;1;23;4) | CS42: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42 : Ws → ⟪ (Sb0-1-23-4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42 c4 = derive (Sb0-1-23-4 ∷ CS24 ∷ []) (CS24 ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw 4 (q293 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw⁻ 1 (q294 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw 0 (q295 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

-- auto BOX(0;1234) | CS02: 1 steps
lem-auto-BOX⟨0·1234⟩-∣-CS02 : Ws → ⟪ (Bx0-1234 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS02 c4 = derive (Bx0-1234 ∷ CS02 ∷ []) (CS02 ∷ Bx0-1234 ∷ [])
  (rw⁻ 0 (q121 c4) ∷ []) Eq.refl

private
  q296 : Ws → Eqn
  q296 c4 = eqn (Bx0-1234 ∷ CS02 ∷ []) (CS02 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS02 c4)

-- auto SBOX(0;1;23;4) | CS02: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS02 : Ws → ⟪ (Sb0-1-23-4 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS02 c4 = derive (Sb0-1-23-4 ∷ CS02 ∷ []) (CS02 ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q124 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw⁻ 3 (q123 c4) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw⁻ 2 (q125 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw⁻ 1 (q123 c4) ∷
   rw 0 (q296 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q297 : Ws → Eqn
  q297 c4 = eqn (CS14 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14 ∷ []) (wl0300 (lit c4))
  q298 : Ws → Eqn
  q298 c4 = eqn (Bx0-1234 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14 c4)

-- auto SBOX(0;1;23;4) | CS14: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14 : Ws → ⟪ (Sb0-1-23-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14 c4 = derive (Sb0-1-23-4 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q113 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw⁻ 1 (q297 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw 0 (q298 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q299 : Ws → Eqn
  q299 c4 = eqn (CCZ023 ∷ []) (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0353 (lit c4))
  q300 : Ws → Eqn
  q300 c4 = eqn (CS14⁻ ∷ CX23 ∷ []) (CX23 ∷ CS14⁻ ∷ []) (wl0354 (lit c4))
  q301 : Ws → Eqn
  q301 c4 = eqn (CS03⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS03⁻ ∷ []) (wp0118 c4)
  q302 : Ws → Eqn
  q302 c4 = eqn (CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ []) (Toff423 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ []) (wp0119 c4)
  q303 : Ws → Eqn
  q303 c4 = eqn (CS14 ∷ CX23 ∷ []) (CX23 ∷ CS14 ∷ []) (wl0355 (lit c4))
  q304 : Ws → Eqn
  q304 c4 = eqn (CS03⁻ ∷ CS14 ∷ []) (CS14 ∷ CS03⁻ ∷ []) (wp0120 c4)
  q305 : Ws → Eqn
  q305 c4 = eqn (CX23 ∷ CX23 ∷ []) [] (wl0218 (lit c4))
  q306 : Ws → Eqn
  q306 c4 = eqn (Bx0-1324 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332 c4)
  q307 : Ws → Eqn
  q307 c4 = eqn (CCZ124 ∷ CX23 ∷ []) (CX23 ∷ CCZ124 ∷ []) (wl0356 (lit c4))
  q308 : Ws → Eqn
  q308 c4 = eqn (Sb0-1-32-4 ∷ CS02 ∷ []) (CS02 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-at2332 c4)

-- auto SBOX(0;1;23;4) | CCZ023: 44 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023 : Ws → ⟪ (Sb0-1-23-4 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023 c4 = derive (Sb0-1-23-4 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb0-1-23-4 ∷ [])
  (rw 1 (q299 c4) ∷
   rw 0 (q278 c4) ∷
   rw 0 (q279 c4) ∷
   re 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) ∷
   re 5 1 (CS14⁻ ∷ []) ∷
   rw 5 (q300 c4) ∷
   re 6 1 (Sb⁻0-1-4-2 ∷ []) ∷
   re 6 1 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q301 c4) ∷
   re 7 1 (Sb⁻0-1-4-2 ∷ []) ∷
   re 7 1 (CS14⁻ ∷ []) ∷
   rw 7 (q300 c4) ∷
   re 8 1 (Sb⁻0-1-4-2 ∷ []) ∷
   rw⁻ 4 (q302 c4) ∷
   re 3 1 (CS14 ∷ []) ∷
   rw 3 (q303 c4) ∷
   re 4 1 (Sb0-1-4-2 ∷ []) ∷
   re 4 1 (CS14 ∷ []) ∷
   rw⁻ 4 (q304 c4) ∷
   re 5 1 (Sb0-1-4-2 ∷ []) ∷
   re 5 1 (CS14 ∷ []) ∷
   rw 5 (q303 c4) ∷
   re 6 1 (Sb0-1-4-2 ∷ []) ∷
   rw⁻ 2 (q302 c4) ∷
   rw⁻ 1 (q305 c4) ∷
   rw 3 (q234 c4) ∷
   rw 2 (q247 c4) ∷
   rw 2 (q233 c4) ∷
   rw 2 (q306 c4) ∷
   rw 3 (q283 c4) ∷
   rw⁻ 4 (q305 c4) ∷
   rw 6 (q234 c4) ∷
   rw 5 (q247 c4) ∷
   rw 5 (q233 c4) ∷
   rw 5 (q306 c4) ∷
   rw⁻ 1 (q307 c4) ∷
   rw⁻ 4 (q307 c4) ∷
   rw 3 (q285 c4) ∷
   rw⁻ 2 (q307 c4) ∷
   rw 1 (q286 c4) ∷
   re 4 5 (Sb0-1-32-4 ∷ []) ∷
   rw 4 (q308 c4) ∷
   rw⁻ 5 (q278 c4) ∷
   rw⁻ 0 (q299 c4) ∷ []) Eq.refl

private
  q309 : Ws → Eqn
  q309 c4 = eqn (CCZ023 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ023 ∷ []) (wl0065 (lit c4))
  q310 : Ws → Eqn
  q310 c4 = eqn (Sb0-1-23-4 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023 c4)

-- auto SBOX(0;1;23;4) | CCZ023 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at2332 c4 = derive (Sb0-1-32-4 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q242 c4) ∷
   rw⁻ 2 (q309 c4) ∷
   rw 1 (q310 c4) ∷
   rw⁻ 0 (q309 c4) ∷
   rw 1 (q244 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q311 : Ws → Eqn
  q311 c4 = eqn (Sw23 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ (lit c4))
  q312 : Ws → Eqn
  q312 c4 = eqn (Sw23 ∷ Bx0-1423 ∷ []) (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ (lit c4))
  q313 : Ws → Eqn
  q313 c4 = eqn (Sb⁻0-1-2-3 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ c4)
  q314 : Ws → Eqn
  q314 c4 = eqn (Sw23 ∷ Bx0-1432 ∷ []) (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4))
  q315 : Ws → Eqn
  q315 c4 = eqn (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ (lit c4))

-- auto SBOXd(0;1;2;3) | BOX(0;1432) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2332 : Ws → ⟪ (Sb⁻0-1-3-2 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2332 c4 = derive (Sb⁻0-1-3-2 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Sb⁻0-1-3-2 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q311 c4) ∷
   rw 2 (q312 c4) ∷
   rw 1 (q313 c4) ∷
   rw 0 (q314 c4) ∷
   rw 1 (q315 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q316 : Ws → Eqn
  q316 c4 = eqn (Sw34 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ (lit c4))
  q317 : Ws → Eqn
  q317 c4 = eqn (Sb⁻0-1-3-2 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2332 c4)
  q318 : Ws → Eqn
  q318 c4 = eqn (Sw34 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ (lit c4))

-- auto SBOXd(0;1;2;3) | BOX(0;1432) @243243: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at243243 : Ws → ⟪ (Sb⁻0-1-4-2 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at243243 c4 = derive (Sb⁻0-1-4-2 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ Sb⁻0-1-4-2 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q316 c4) ∷
   rw 2 (q218 c4) ∷
   rw 1 (q317 c4) ∷
   rw 0 (q216 c4) ∷
   rw 1 (q318 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q319 : Ws → Eqn
  q319 c4 = eqn (Sw23 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ (lit c4))
  q320 : Ws → Eqn
  q320 c4 = eqn (Sb⁻0-1-4-2 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ Sb⁻0-1-4-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at243243 c4)
  q321 : Ws → Eqn
  q321 c4 = eqn (Sw23 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ (lit c4))

-- auto SBOXd(0;1;2;3) | BOX(0;1432) @2442: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2442 : Ws → ⟪ (Sb⁻0-1-4-3 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2442 c4 = derive (Sb⁻0-1-4-3 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Sb⁻0-1-4-3 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q319 c4) ∷
   rw 2 (q214 c4) ∷
   rw 1 (q320 c4) ∷
   rw 0 (q213 c4) ∷
   rw 1 (q321 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q322 : Ws → Eqn
  q322 c4 = eqn (Sw23 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ (lit c4))
  q323 : Ws → Eqn
  q323 c4 = eqn (Sb0-1-2-3 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ c4)
  q324 : Ws → Eqn
  q324 c4 = eqn (Sw23 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ (lit c4))

-- auto SBOX(0;1;2;3) | BOX(0;1432) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2332 : Ws → ⟪ (Sb0-1-3-2 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2332 c4 = derive (Sb0-1-3-2 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Sb0-1-3-2 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q322 c4) ∷
   rw 2 (q312 c4) ∷
   rw 1 (q323 c4) ∷
   rw 0 (q314 c4) ∷
   rw 1 (q324 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q325 : Ws → Eqn
  q325 c4 = eqn (Sw34 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ (lit c4))
  q326 : Ws → Eqn
  q326 c4 = eqn (Sb0-1-3-2 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2332 c4)
  q327 : Ws → Eqn
  q327 c4 = eqn (Sw34 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ (lit c4))

-- auto SBOX(0;1;2;3) | BOX(0;1432) @243243: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at243243 : Ws → ⟪ (Sb0-1-4-2 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at243243 c4 = derive (Sb0-1-4-2 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ Sb0-1-4-2 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q325 c4) ∷
   rw 2 (q218 c4) ∷
   rw 1 (q326 c4) ∷
   rw 0 (q216 c4) ∷
   rw 1 (q327 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q328 : Ws → Eqn
  q328 c4 = eqn (Sw23 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ (lit c4))
  q329 : Ws → Eqn
  q329 c4 = eqn (Sb0-1-4-2 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ Sb0-1-4-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at243243 c4)
  q330 : Ws → Eqn
  q330 c4 = eqn (Sw23 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ (lit c4))

-- auto SBOX(0;1;2;3) | BOX(0;1432) @2442: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2442 : Ws → ⟪ (Sb0-1-4-3 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2442 c4 = derive (Sb0-1-4-3 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Sb0-1-4-3 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q328 c4) ∷
   rw 2 (q214 c4) ∷
   rw 1 (q329 c4) ∷
   rw 0 (q213 c4) ∷
   rw 1 (q330 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q331 : Ws → Eqn
  q331 c4 = eqn (Sb⁻0-1-4-3 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2442 c4)
  q332 : Ws → Eqn
  q332 c4 = eqn (Toff423 ∷ Toff423 ∷ []) [] (wl0296 (lit c4))
  q333 : Ws → Eqn
  q333 c4 = eqn (Bx0-2134 ∷ []) (Bx0-2314 ∷ []) (lem-sym23-at1221 c4)
  q334 : Ws → Eqn
  q334 c4 = eqn (Bx0-2314 ∷ []) (Bx0-2341 ∷ []) (lem-sym34-at122331 c4)
  q335 : Ws → Eqn
  q335 c4 = eqn (Toff423 ∷ Bx0-2341 ∷ Toff423 ∷ []) (Bx0-2341 ∷ CCZ123 ∷ []) (lem-T312-beta-at12233441 c4)
  q336 : Ws → Eqn
  q336 c4 = eqn (Bx0-2341 ∷ []) (Bx0-2314 ∷ []) (lem-sym34-at12233441 c4)
  q337 : Ws → Eqn
  q337 c4 = eqn (Bx0-2314 ∷ []) (Bx0-2134 ∷ []) (lem-sym23-at122331 c4)
  q338 : Ws → Eqn
  q338 c4 = eqn (Sb0-1-4-3 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2442 c4)
  q339 : Ws → Eqn
  q339 c4 = eqn (Bx0-1234 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·1234⟩ c4)
  q340 : Ws → Eqn
  q340 c4 = eqn (CCZ123 ∷ Toff423 ∷ CS14⁻ ∷ []) (Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) (wl0357 (lit c4))
  q341 : Ws → Eqn
  q341 c4 = eqn (CCZ123 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) (wl0358 (lit c4))
  q342 : Ws → Eqn
  q342 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl0212 (lit c4))

-- auto SBOX(0;1;23;4) | BOX(0;1234): 30 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩ c4 = derive (Sb0-1-23-4 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   rw 4 (q331 c4) ∷
   rw⁻ 5 (q332 c4) ∷
   rw 4 (q77 c4) ∷
   rw 4 (q333 c4) ∷
   rw 4 (q334 c4) ∷
   rw 3 (q335 c4) ∷
   rw 3 (q336 c4) ∷
   rw 3 (q337 c4) ∷
   rw 3 (q83 c4) ∷
   rw 2 (q338 c4) ∷
   rw⁻ 3 (q332 c4) ∷
   rw 2 (q77 c4) ∷
   rw 2 (q333 c4) ∷
   rw 2 (q334 c4) ∷
   rw 1 (q335 c4) ∷
   rw 1 (q336 c4) ∷
   rw 1 (q337 c4) ∷
   rw 1 (q83 c4) ∷
   rw 0 (q339 c4) ∷
   re 7 1 (CS14⁻ ∷ []) ∷
   rw 5 (q340 c4) ∷
   re 6 1 (Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14 ∷ []) ∷
   re 6 1 (CS14⁻ ∷ []) ∷
   rw 2 (q341 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw 6 (q342 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q343 : Ws → Eqn
  q343 c4 = eqn (CCZ012 ∷ Bx3-0142 ∷ []) (Bx3-0142 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0142⟩ c4)
  q344 : Ws → Eqn
  q344 c4 = eqn (CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CCZ012 ∷ []) (wp0121 c4)
  q345 : Ws → Eqn
  q345 c4 = eqn (CCZ012 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ012 ∷ []) (wl0359 (lit c4))

-- auto CCZ012 | SBOX(3;0;14;2): 9 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩ : Ws → ⟪ (CCZ012 ∷ Sb3-0-14-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-14-2 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩ c4 = derive (CCZ012 ∷ Sb3-0-14-2 ∷ []) (Sb3-0-14-2 ∷ CCZ012 ∷ [])
  (re 1 1 (Bx3-0142 ∷ Toff214 ∷ Sb3-0-2-4 ∷ Toff214 ∷ Sb⁻3-0-2-4 ∷ []) ∷
   rw 0 (q343 c4) ∷
   re 3 1 (CS02 ∷ []) ∷
   rw 1 (q344 c4) ∷
   re 2 1 (Sb3-0-2-4 ∷ []) ∷
   re 5 1 (CS02⁻ ∷ []) ∷
   rw 4 (q345 c4) ∷
   re 4 1 (Sb⁻3-0-2-4 ∷ []) ∷
   re 0 5 (Sb3-0-14-2 ∷ []) ∷ []) Eq.refl

private
  q346 : Ws → Eqn
  q346 c4 = eqn (Sb0-1-23-4 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14 c4)

-- auto SBOX(0;1;23;4) | CS14 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-at2332 c4 = derive (Sb0-1-32-4 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q242 c4) ∷
   rw⁻ 2 (q26 c4) ∷
   rw 1 (q346 c4) ∷
   rw⁻ 0 (q26 c4) ∷
   rw 1 (q244 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q347 : Ws → Eqn
  q347 c4 = eqn (Sb0-1-32-4 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-at2332 c4)

-- auto SBOX(0;1;23;4) | SBOX(0;1;4;3): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-3 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩ c4 = derive (Sb0-1-23-4 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-3 ∷ Sb0-1-23-4 ∷ [])
  (re 1 1 (CS14 ∷ []) ∷
   rw 0 (q278 c4) ∷
   rw 0 (q347 c4) ∷
   rw⁻ 1 (q278 c4) ∷
   re 0 1 (Sb0-1-4-3 ∷ []) ∷ []) Eq.refl

private
  q348 : Ws → Eqn
  q348 c4 = eqn (CS14⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS14⁻ ∷ []) (wl0317 (lit c4))
  q349 : Ws → Eqn
  q349 c4 = eqn (CS14⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ []) (wl0318 (lit c4))
  q350 : Ws → Eqn
  q350 c4 = eqn (Bx0-1234 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14 c4)

-- auto SBOX(0;1;23;4) | CSd14: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd14 : Ws → ⟪ (Sb0-1-23-4 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd14 c4 = derive (Sb0-1-23-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw 4 (q348 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw⁻ 1 (q349 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw 0 (q350 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q351 : Ws → Eqn
  q351 c4 = eqn (Sb0-1-23-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd14 c4)

-- auto SBOX(0;1;23;4) | CSd14 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd14-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd14-at2332 c4 = derive (Sb0-1-32-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q242 c4) ∷
   rw⁻ 2 (q114 c4) ∷
   rw 1 (q351 c4) ∷
   rw⁻ 0 (q114 c4) ∷
   rw 1 (q244 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q352 : Ws → Eqn
  q352 c4 = eqn (Sb0-1-32-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd14-at2332 c4)

-- auto SBOX(0;1;23;4) | SBOXd(0;1;4;3): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-3 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩ c4 = derive (Sb0-1-23-4 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-3 ∷ Sb0-1-23-4 ∷ [])
  (re 1 1 (CS14⁻ ∷ []) ∷
   rw 0 (q278 c4) ∷
   rw 0 (q352 c4) ∷
   rw⁻ 1 (q278 c4) ∷
   re 0 1 (Sb⁻0-1-4-3 ∷ []) ∷ []) Eq.refl

private
  q353 : Ws → Eqn
  q353 c4 = eqn (Sw01 ∷ Bx1-3024 ∷ []) (Bx0-3124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3024⟩ (lit c4))
  q354 : Ws → Eqn
  q354 c4 = eqn (Sw01 ∷ Bx0-1324 ∷ []) (Bx1-0324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1324⟩ (lit c4))

-- sym12 @01132032: 5 steps
lem-sym12-at01132032 : Ws → ⟪ (Bx1-3024 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ []) ⟫ʷ
lem-sym12-at01132032 c4 = derive (Bx1-3024 ∷ []) (Bx1-0324 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q353 c4) ∷
   rw 1 (q266 c4) ∷
   rw 0 (q354 c4) ∷
   rw 1 (q21 c4) ∷ []) Eq.refl

private
  q355 : Ws → Eqn
  q355 c4 = eqn (Sw12 ∷ Bx2-3014 ∷ []) (Bx1-3024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3014⟩ (lit c4))
  q356 : Ws → Eqn
  q356 c4 = eqn (Bx1-3024 ∷ []) (Bx1-0324 ∷ []) (lem-sym12-at01132032 c4)
  q357 : Ws → Eqn
  q357 c4 = eqn (Sw12 ∷ Bx1-0324 ∷ []) (Bx2-0314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0324⟩ (lit c4))

-- sym12 @02132031: 5 steps
lem-sym12-at02132031 : Ws → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-sym12-at02132031 c4 = derive (Bx2-3014 ∷ []) (Bx2-0314 ∷ [])
  (rw⁻ 0 (q14 c4) ∷
   rw 1 (q355 c4) ∷
   rw 1 (q356 c4) ∷
   rw 0 (q357 c4) ∷
   rw 1 (q14 c4) ∷ []) Eq.refl

private
  q358 : Ws → Eqn
  q358 c4 = eqn (Sw01 ∷ Bx2-3104 ∷ []) (Bx2-3014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3104⟩ (lit c4))
  q359 : Ws → Eqn
  q359 c4 = eqn (Bx2-3014 ∷ []) (Bx2-0314 ∷ []) (lem-sym12-at02132031 c4)
  q360 : Ws → Eqn
  q360 c4 = eqn (Sw01 ∷ Bx2-0314 ∷ []) (Bx2-1304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0314⟩ (lit c4))

-- sym12 @02132130: 5 steps
lem-sym12-at02132130 : Ws → ⟪ (Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-sym12-at02132130 c4 = derive (Bx2-3104 ∷ []) (Bx2-1304 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q358 c4) ∷
   rw 1 (q359 c4) ∷
   rw 0 (q360 c4) ∷
   rw 1 (q21 c4) ∷ []) Eq.refl

private
  q361 : Ws → Eqn
  q361 c4 = eqn (Sw01 ∷ Bx2-1304 ∷ []) (Bx2-0314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1304⟩ (lit c4))
  q362 : Ws → Eqn
  q362 c4 = eqn (Bx2-0314 ∷ []) (Bx2-0134 ∷ []) (lem-sym23-at02102331 c4)
  q363 : Ws → Eqn
  q363 c4 = eqn (Sw01 ∷ Bx2-0134 ∷ []) (Bx2-1034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0134⟩ (lit c4))

-- sym23 @022330: 5 steps
lem-sym23-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-sym23-at022330 c4 = derive (Bx2-1304 ∷ []) (Bx2-1034 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q361 c4) ∷
   rw 1 (q362 c4) ∷
   rw 0 (q363 c4) ∷
   rw 1 (q21 c4) ∷ []) Eq.refl

private
  q364 : Ws → Eqn
  q364 c4 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wl0139 (lit c4))
  q365 : Ws → Eqn
  q365 c4 = eqn (Sw01 ∷ Bx1-0234 ∷ []) (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4))
  q366 : Ws → Eqn
  q366 c4 = eqn (CS12⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS12⁻ ∷ []) (lem-CSd12-beta c4)
  q367 : Ws → Eqn
  q367 c4 = eqn (Sw01 ∷ Bx0-1234 ∷ []) (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4))
  q368 : Ws → Eqn
  q368 c4 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wl0036 (lit c4))

-- CSd12-beta @0110: 7 steps
lem-CSd12-beta-at0110 : Ws → ⟪ (CS02⁻ ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-CSd12-beta-at0110 c4 = derive (CS02⁻ ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CS02⁻ ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw⁻ 1 (q364 c4) ∷
   rw 2 (q365 c4) ∷
   rw 1 (q366 c4) ∷
   rw 0 (q367 c4) ∷
   rw⁻ 1 (q368 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q369 : Ws → Eqn
  q369 c4 = eqn (Sw12 ∷ CS01⁻ ∷ []) (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 (lit c4))
  q370 : Ws → Eqn
  q370 c4 = eqn (Sw12 ∷ Bx2-0134 ∷ []) (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4))
  q371 : Ws → Eqn
  q371 c4 = eqn (CS02⁻ ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CS02⁻ ∷ []) (lem-CSd12-beta-at0110 c4)
  q372 : Ws → Eqn
  q372 c4 = eqn (Sw12 ∷ Bx1-0234 ∷ []) (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4))
  q373 : Ws → Eqn
  q373 c4 = eqn (Sw12 ∷ CS02⁻ ∷ []) (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 (lit c4))

-- CSd12-beta @021021: 7 steps
lem-CSd12-beta-at021021 : Ws → ⟪ (CS01⁻ ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CSd12-beta-at021021 c4 = derive (CS01⁻ ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ CS01⁻ ∷ [])
  (rw⁻ 0 (q14 c4) ∷
   rw 1 (q369 c4) ∷
   rw 2 (q370 c4) ∷
   rw 1 (q371 c4) ∷
   rw 0 (q372 c4) ∷
   rw 1 (q373 c4) ∷
   rw 2 (q14 c4) ∷ []) Eq.refl

private
  q374 : Ws → Eqn
  q374 c4 = eqn (CS01⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS01⁻ ∷ []) (wl0133 (lit c4))
  q375 : Ws → Eqn
  q375 c4 = eqn (Sw01 ∷ Bx2-1034 ∷ []) (Bx2-0134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1034⟩ (lit c4))
  q376 : Ws → Eqn
  q376 c4 = eqn (CS01⁻ ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ CS01⁻ ∷ []) (lem-CSd12-beta-at021021 c4)

-- CSd12-beta @0220: 7 steps
lem-CSd12-beta-at0220 : Ws → ⟪ (CS01⁻ ∷ Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CSd12-beta-at0220 c4 = derive (CS01⁻ ∷ Bx2-1034 ∷ []) (Bx2-1034 ∷ CS01⁻ ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw⁻ 1 (q374 c4) ∷
   rw 2 (q375 c4) ∷
   rw 1 (q376 c4) ∷
   rw 0 (q363 c4) ∷
   rw⁻ 1 (q374 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q377 : Ws → Eqn
  q377 c4 = eqn (Bx2-0134 ∷ []) (Bx2-0314 ∷ []) (lem-sym23-at021021 c4)

-- sym23 @0220: 5 steps
lem-sym23-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-sym23-at0220 c4 = derive (Bx2-1034 ∷ []) (Bx2-1304 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q375 c4) ∷
   rw 1 (q377 c4) ∷
   rw 0 (q360 c4) ∷
   rw 1 (q21 c4) ∷ []) Eq.refl

private
  q378 : Ws → Eqn
  q378 c4 = eqn (Sw01 ∷ Bx1-0324 ∷ []) (Bx0-1324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0324⟩ (lit c4))
  q379 : Ws → Eqn
  q379 c4 = eqn (Bx0-1324 ∷ []) (Bx0-3124 ∷ []) (lem-sym12-at2332 c4)
  q380 : Ws → Eqn
  q380 c4 = eqn (Sw01 ∷ Bx0-3124 ∷ []) (Bx1-3024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3124⟩ (lit c4))

-- sym12 @01102332: 5 steps
lem-sym12-at01102332 : Ws → ⟪ (Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3024 ∷ []) ⟫ʷ
lem-sym12-at01102332 c4 = derive (Bx1-0324 ∷ []) (Bx1-3024 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q378 c4) ∷
   rw 1 (q379 c4) ∷
   rw 0 (q380 c4) ∷
   rw 1 (q21 c4) ∷ []) Eq.refl

private
  q381 : Ws → Eqn
  q381 c4 = eqn (Sw12 ∷ Bx2-0314 ∷ []) (Bx1-0324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0314⟩ (lit c4))
  q382 : Ws → Eqn
  q382 c4 = eqn (Bx1-0324 ∷ []) (Bx1-3024 ∷ []) (lem-sym12-at01102332 c4)
  q383 : Ws → Eqn
  q383 c4 = eqn (Sw12 ∷ Bx1-3024 ∷ []) (Bx2-3014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3024⟩ (lit c4))

-- sym12 @02102331: 5 steps
lem-sym12-at02102331 : Ws → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-sym12-at02102331 c4 = derive (Bx2-0314 ∷ []) (Bx2-3014 ∷ [])
  (rw⁻ 0 (q14 c4) ∷
   rw 1 (q381 c4) ∷
   rw 1 (q382 c4) ∷
   rw 0 (q383 c4) ∷
   rw 1 (q14 c4) ∷ []) Eq.refl

private
  q384 : Ws → Eqn
  q384 c4 = eqn (Bx2-0314 ∷ []) (Bx2-3014 ∷ []) (lem-sym12-at02102331 c4)
  q385 : Ws → Eqn
  q385 c4 = eqn (Sw01 ∷ Bx2-3014 ∷ []) (Bx2-3104 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3014⟩ (lit c4))

-- sym12 @022330: 5 steps
lem-sym12-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-sym12-at022330 c4 = derive (Bx2-1304 ∷ []) (Bx2-3104 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q361 c4) ∷
   rw 1 (q384 c4) ∷
   rw 0 (q385 c4) ∷
   rw 1 (q21 c4) ∷ []) Eq.refl

private
  q386 : Ws → Eqn
  q386 c4 = eqn (CS01⁻ ∷ []) (CS01⁻ ∷ []) (wl0360 (lit c4))
  q387 : Ws → Eqn
  q387 c4 = eqn (Bx2-3104 ∷ []) (Bx2-1304 ∷ []) (lem-sym12-at02132130 c4)
  q388 : Ws → Eqn
  q388 c4 = eqn (Bx2-1304 ∷ []) (Bx2-1034 ∷ []) (lem-sym23-at022330 c4)
  q389 : Ws → Eqn
  q389 c4 = eqn (CS01⁻ ∷ Bx2-1034 ∷ []) (Bx2-1034 ∷ CS01⁻ ∷ []) (lem-CSd12-beta-at0220 c4)
  q390 : Ws → Eqn
  q390 c4 = eqn (Bx2-1034 ∷ []) (Bx2-1304 ∷ []) (lem-sym23-at0220 c4)
  q391 : Ws → Eqn
  q391 c4 = eqn (Bx2-1304 ∷ []) (Bx2-3104 ∷ []) (lem-sym12-at022330 c4)

-- auto CSd01 | BOX(2;3104): 7 steps
lem-auto-CSd01-∣-BOX⟨2·3104⟩ : Ws → ⟪ (CS01⁻ ∷ Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·3104⟩ c4 = derive (CS01⁻ ∷ Bx2-3104 ∷ []) (Bx2-3104 ∷ CS01⁻ ∷ [])
  (rw 0 (q386 c4) ∷
   rw 1 (q387 c4) ∷
   rw 1 (q388 c4) ∷
   rw 0 (q389 c4) ∷
   rw 0 (q390 c4) ∷
   rw 0 (q391 c4) ∷
   rw 1 (q386 c4) ∷ []) Eq.refl

private
  q392 : Ws → Eqn
  q392 c4 = eqn (Sw01 ∷ Bx1-2304 ∷ []) (Bx0-2314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2304⟩ (lit c4))
  q393 : Ws → Eqn
  q393 c4 = eqn (Bx0-2314 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-beta-T-at122331 c4)
  q394 : Ws → Eqn
  q394 c4 = eqn (Sw01 ∷ Toff023 ∷ []) (Toff123 ∷ Sw01 ∷ []) (wl0108 (lit c4))
  q395 : Ws → Eqn
  q395 c4 = eqn (Sw01 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 (lit c4))

-- beta-T @01122330: 8 steps
lem-beta-T-at01122330 : Ws → ⟪ (Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ []) ⟫ʷ
lem-beta-T-at01122330 c4 = derive (Bx1-2304 ∷ []) (Toff123 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw 1 (q392 c4) ∷
   rw 1 (q393 c4) ∷
   rw 0 (q394 c4) ∷
   rw 1 (q395 c4) ∷
   rw 2 (q394 c4) ∷
   rw 3 (q395 c4) ∷
   rw 4 (q21 c4) ∷ []) Eq.refl

private
  q396 : Ws → Eqn
  q396 c4 = eqn (Bx1-2304 ∷ []) (Toff123 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ []) (lem-beta-T-at01122330 c4)
  q397 : Ws → Eqn
  q397 c4 = eqn (S0 ∷ Toff123 ∷ []) (Toff123 ∷ S0 ∷ []) (c₁ (S) (Toff))
  q398 : Ws → Eqn
  q398 c4 = eqn (CCZ014 ∷ S0 ∷ []) (S0 ∷ CCZ014 ∷ []) (wp0122 c4)

-- auto S0 | BOX(1;2304): 6 steps
lem-auto-S0-∣-BOX⟨1·2304⟩ : Ws → ⟪ (S0 ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2304⟩ c4 = derive (S0 ∷ Bx1-2304 ∷ []) (Bx1-2304 ∷ S0 ∷ [])
  (rw 1 (q396 c4) ∷
   rw 0 (q397 c4) ∷
   rw⁻ 1 (q398 c4) ∷
   rw 2 (q397 c4) ∷
   rw⁻ 3 (q398 c4) ∷
   rw⁻ 0 (q396 c4) ∷ []) Eq.refl

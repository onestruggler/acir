{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D003 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0008 ; wl0011 ; wl0015 ; wl0017 ; wl0021 ; wl0027 ; wl0028 ; wl0031 ; wl0033 ; wl0034 ; wl0035 ; wl0050 ; wl0051 ; wl0056 ; wl0057 ; wl0058 ; wl0062 ; wl0065 ; wl0067 ; wl0068 ; wl0076 ; wl0084 ; wl0091 ; wl0103 ; wl0111 ; wl0113 ; wl0138 ; wl0152 ; wl0154 ; wl0155 ; wl0212 ; wl0247 ; wl0248 ; wl0249 ; wl0250 ; wl0257 ; wl0278 ; wl0279 ; wl0280 ; wl0281 ; wl0282 ; wl0283 ; wl0284 ; wl0285 ; wl0286 ; wl0287 ; wl0288 ; wl0289 ; wl0290 ; wl0291 ; wl0292 ; wl0293 ; wl0294 ; wl0295 ; wl0296 ; wl0297 ; wl0298 ; wl0299 ; wl0300 ; wl0301 ; wl0302 ; wl0303 ; wl0304 ; wl0305 ; wl0306 ; wl0307 ; wl0308 ; wl0309 ; wl0310 ; wl0311 ; wl0312 ; wl0313 ; wl0314 ; wl0315 ; wl0316 ; wl0317 ; wl0318 ; wl0319 ; wl0320 ; wl0321 ; wl0322 ; wl0323 ; wl0324 ; wp0034 ; wp0055 ; wp0059 ; wp0077 ; wp0079 ; wp0080 ; wp0081 ; wp0082 ; wp0083 ; wp0084 ; wp0085 ; wp0086 ; wp0087 ; wp0088 ; wp0089 ; wp0090 ; wp0091 ; wp0092 ; wp0093 ; wp0094 ; wp0095)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-CS12-beta ; lem-F0 ; lem-K0-pass-c ; lem-K0-pass-ci ; lem-T312-beta ; lem-beta-T ; lem-beta-T-at243243 ; lem-beta-inv-at0210243143 ; lem-c124-beta ; lem-sym12 ; lem-sym12-at0214203143 ; lem-sym12-at1221 ; lem-sym23 ; lem-sym23-at0214203143 ; lem-sym23-at0214213043 ; lem-sym23-at1221 ; lem-sym34 ; lem-sym34-at1221 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-CS12-beta-at2332 ; lem-CS12-beta-at243243 ; lem-CSd12-beta-at243243 ; lem-CX23-beta-at0210243143 ; lem-CX23-beta-at02243043 ; lem-SB2 ; lem-SBsym ; lem-T312-beta-at02142140 ; lem-X1-beta ; lem-auto-BOX⟨0·1234⟩-∣-CCZ034 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at2332 ; lem-auto-BOX⟨0·1234⟩-∣-CS14 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-CS21 ; lem-auto-BOX⟨0·1234⟩-∣-CS23 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-TOFF012 ; lem-c124-beta-at2332 ; lem-sym12-at0210243143 ; lem-sym12-at0214213043 ; lem-sym12-at02243043 ; lem-sym12-at12213443 ; lem-sym12-at233442 ; lem-sym23-at021021 ; lem-sym23-at12213443 ; lem-sym23-at122331 ; lem-sym23-at12243143 ; lem-sym23-at2332 ; lem-sym23-at243243 ; lem-sym23-at3443 ; lem-sym34-at0214213043 ; lem-sym34-at02142140 ; lem-sym34-at12213443 ; lem-sym34-at122331 ; lem-sym34-at12233441 ; lem-sym34-at2332 ; lem-sym34-at233442)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-1-CCZ023 ; lem-nat-1-CCZ034 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-3-BOX⟨0·1243⟩ ; lem-nat-3-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·1423⟩ ; lem-nat-1-CCZ013 ; lem-nat-2-BOX⟨0·3124⟩ ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-3-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-BOX⟨1·4023⟩ ; lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-1-BOX⟨2·4013⟩ ; lem-nat-2-TOFF413 ; lem-nat-3-BOX⟨0·4123⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-BOX⟨0·4123⟩ ; lem-nat-1-BOX⟨0·1234⟩ ; lem-nat-1-BOX⟨1·4023⟩ ; lem-nat-2-BOX⟨0·2134⟩ ; lem-nat-3-BOX⟨0·3124⟩)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨3·0124⟩ ; lem-nat-3-BOX⟨0·1234⟩ ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨0·1324⟩ ; lem-nat-1-BOX⟨0·1342⟩ ; lem-nat-1-BOX⟨0·2341⟩ ; lem-nat-1-BOX⟨1·0324⟩ ; lem-nat-1-CS01 ; lem-nat-1-CS02 ; lem-nat-2-BOX⟨0·1243⟩ ; lem-nat-2-BOX⟨0·1342⟩ ; lem-nat-2-BOX⟨0·3142⟩ ; lem-nat-2-CS12 ; lem-nat-2-CS13 ; lem-nat-3-CS13 ; lem-nat-3-CS14)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨0·1342⟩ ; lem-nat-0-CS04 ; lem-nat-0-CS14 ; lem-nat-0-SBOX⟨0·1·34·2⟩ ; lem-nat-0-SBOX⟨2·0·34·1⟩ ; lem-nat-1-CS04 ; lem-nat-1-SBOX⟨0·2·34·1⟩ ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨3·0·41·2⟩ ; lem-nat-2-BOX⟨0·1432⟩ ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨1·0·43·2⟩ ; lem-nat-2-SBOX⟨3·0·42·1⟩ ; lem-nat-2-TOFF014 ; lem-nat-3-CS23 ; lem-nat-3-CS24 ; lem-nat-3-SBOX⟨1·0·34·2⟩ ; lem-nat-3-SBOX⟨2·0·43·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨0·3142⟩ ; lem-nat-0-BOX⟨1·0324⟩ ; lem-nat-0-BOX⟨1·0342⟩ ; lem-nat-0-BOX⟨1·3042⟩ ; lem-nat-0-BOX⟨4·0231⟩ ; lem-nat-0-SBOX⟨0·1·23·4⟩ ; lem-nat-0-SBOX⟨1·2·34·0⟩ ; lem-nat-0-SBOX⟨4·0·23·1⟩ ; lem-nat-1-BOX⟨1·0342⟩ ; lem-nat-1-BOX⟨1·3042⟩ ; lem-nat-1-BOX⟨2·0314⟩ ; lem-nat-1-BOX⟨2·0341⟩ ; lem-nat-1-BOX⟨2·3041⟩ ; lem-nat-1-SBOX⟨1·0·32·4⟩ ; lem-nat-1-SBOX⟨2·1·34·0⟩ ; lem-nat-1-SBOX⟨4·0·31·2⟩ ; lem-nat-2-SBOX⟨1·0·23·4⟩ ; lem-nat-2-SBOX⟨4·0·32·1⟩ ; lem-nat-3-BOX⟨3·0124⟩ ; lem-nat-3-BOX⟨4·0123⟩ ; lem-nat-3-SBOX⟨2·0·31·4⟩ ; lem-nat-3-SBOX⟨3·0·41·2⟩ ; lem-nat-3-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨4·1230⟩ ; lem-nat-0-SBOX⟨1·0·32·4⟩ ; lem-nat-1-BOX⟨4·0132⟩ ; lem-nat-1-BOX⟨4·0231⟩ ; lem-nat-1-SBOX⟨2·0·13·4⟩ ; lem-nat-2-BOX⟨4·0123⟩ ; lem-nat-2-BOX⟨4·0132⟩ ; lem-nat-3-SBOX⟨2·0·14·3⟩)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Sw34 ∷ Bx0-1423 ∷ []) (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (CCZ234 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ234 ∷ []) (wl0155 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (Bx0-1324 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at2332 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Sw34 ∷ Bx0-1324 ∷ []) (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4))

-- auto BOX(0;1234) | CCZ324 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at243243 : Ws → ⟪ (Bx0-1423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at243243 c4 = derive (Bx0-1423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 1 (q4 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q6 : Ws → Eqn
  q6 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (Sw01 ∷ Bx1-0423 ∷ []) (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Sw01 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ))
  q9 : Ws → Eqn
  q9 c4 = eqn (Bx0-1423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at243243 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (Sw01 ∷ Bx0-1423 ∷ []) (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4))

-- auto BOX(0;1234) | CCZ324 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at0110243243 c4 = derive (Bx1-0423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q7 c4) ∷
   rw 2 (q8 c4) ∷
   rw 1 (q9 c4) ∷
   rw 0 (q8 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q6 c4) ∷ []) Eq.refl

private
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw12 ∷ Bx2-0413 ∷ []) (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl0084 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx1-0423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at0110243243 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (Sw12 ∷ Bx1-0423 ∷ []) (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4))

-- auto BOX(0;1234) | CCZ324 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at0210243143 c4 = derive (Bx2-0413 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q12 c4) ∷
   rw⁻ 2 (q13 c4) ∷
   rw 1 (q14 c4) ∷
   rw⁻ 0 (q15 c4) ∷
   rw 1 (q16 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Sw23 ∷ Bx0-1324 ∷ []) (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (CS23 ∷ Sw23 ∷ []) (Sw23 ∷ CS23 ∷ []) (wl0152 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (Bx0-1234 ∷ CS23 ∷ []) (CS23 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS23 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (Sw23 ∷ Bx0-1234 ∷ []) (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4))

-- auto BOX(0;1234) | CS23 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS23-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS23-at2332 c4 = derive (Bx0-1324 ∷ CS23 ∷ []) (CS23 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q18 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   rw 1 (q20 c4) ∷
   rw⁻ 0 (q19 c4) ∷
   rw 1 (q21 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q22 : Ws → Eqn
  q22 c4 = eqn (Sw34 ∷ CS24 ∷ []) (CS23 ∷ Sw34 ∷ []) (lem-nat-3-CS24 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Bx0-1324 ∷ CS23 ∷ []) (CS23 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS23-at2332 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (Sw34 ∷ CS23 ∷ []) (CS24 ∷ Sw34 ∷ []) (lem-nat-3-CS23 (lit c4))

-- auto BOX(0;1234) | CS23 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS23-at243243 : Ws → ⟪ (Bx0-1423 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS23-at243243 c4 = derive (Bx0-1423 ∷ CS24 ∷ []) (CS24 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q22 c4) ∷
   rw 1 (q23 c4) ∷
   rw 0 (q24 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q25 : Ws → Eqn
  q25 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q26 : Ws → Eqn
  q26 c4 = eqn (Bx0-1423 ∷ CS24 ∷ []) (CS24 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS23-at243243 c4)

-- auto BOX(0;1234) | CS23 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS23-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS23-at0110243243 c4 = derive (Bx1-0423 ∷ CS24 ∷ []) (CS24 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q7 c4) ∷
   rw 2 (q25 c4) ∷
   rw 1 (q26 c4) ∷
   rw 0 (q25 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q6 c4) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (Bx1-0423 ∷ CS24 ∷ []) (CS24 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS23-at0110243243 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0017 (lit c4))

-- auto BOX(0;1234) | CS23 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS23-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS23-at0210243143 c4 = derive (Bx2-0413 ∷ CS14 ∷ []) (CS14 ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q12 c4) ∷
   rw⁻ 2 (q27 c4) ∷
   rw 1 (q28 c4) ∷
   rw⁻ 0 (q29 c4) ∷
   rw 1 (q16 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q30 : Ws → Eqn
  q30 c4 = eqn (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (CCZ014 ∷ []) (lem-SB2 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) (CX40 ∷ []) (wp0079 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Toff314 ∷ Toff314 ∷ []) [] (wl0248 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx2-0413 ∷ []) (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (Bx2-4013 ∷ []) (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (Bx2-4103 ∷ []) (Bx2-4130 ∷ []) (lem-sym34-at0214213043 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Toff314 ∷ Bx2-4130 ∷ Toff314 ∷ []) (Bx2-4130 ∷ CCZ014 ∷ []) (lem-T312-beta-at02142140 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (Bx2-4130 ∷ []) (Bx2-4103 ∷ []) (lem-sym34-at02142140 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Bx2-4103 ∷ []) (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (Bx2-4013 ∷ []) (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (Bx2-0413 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (Bx2-0413 ∷ CS03 ∷ []) (CS03 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (Bx2-0413 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (CX40 ∷ CX40 ∷ []) [] (wp0080 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (Bx2-4103 ∷ []) (Bx2-1403 ∷ []) (lem-sym12-at0214213043 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (CX40 ∷ Bx2-1403 ∷ CX40 ∷ []) (Bx2-1403 ∷ CCZ134 ∷ []) (lem-CX23-beta-at02243043 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (Bx2-1403 ∷ []) (Bx2-4103 ∷ []) (lem-sym12-at02243043 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (Bx2-0413 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at0210243143 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (Bx2-0413 ∷ CS14 ∷ []) (CS14 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS23-at0210243143 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ014 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ014 ∷ []) (wp0077 c4)

-- F1 X-CS0 [nf of rhs]: 36 steps
lem-F1-X-CS0-nf-of-rhs : Ws → ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ CX40 ∷ CCZ134 ∷ CS14 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-F1-X-CS0-nf-of-rhs c4 = derive (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ CX40 ∷ CCZ134 ∷ CS14 ∷ Bx2-0413 ∷ [])
  (rw 0 (q30 c4) ∷
   rw 2 (q31 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw⁻ 1 (q32 c4) ∷
   rw 3 (q33 c4) ∷
   rw 3 (q34 c4) ∷
   rw 3 (q35 c4) ∷
   rw 2 (q36 c4) ∷
   rw 2 (q37 c4) ∷
   rw 2 (q38 c4) ∷
   rw 2 (q39 c4) ∷
   rw 2 (q40 c4) ∷
   rw 3 (q41 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 6 (q33 c4) ∷
   rw 6 (q34 c4) ∷
   rw 6 (q35 c4) ∷
   rw 5 (q36 c4) ∷
   rw 5 (q37 c4) ∷
   rw 5 (q38 c4) ∷
   rw 5 (q39 c4) ∷
   rw 5 (q40 c4) ∷
   rw 6 (q42 c4) ∷
   rw⁻ 7 (q43 c4) ∷
   rw 9 (q33 c4) ∷
   rw 9 (q34 c4) ∷
   rw 9 (q44 c4) ∷
   rw 8 (q45 c4) ∷
   rw 8 (q46 c4) ∷
   rw 8 (q38 c4) ∷
   rw 8 (q39 c4) ∷
   rw 8 (q47 c4) ∷
   rw 9 (q48 c4) ∷
   rw 0 (q49 c4) ∷ []) Eq.refl

private
  q50 : Ws → Eqn
  q50 c4 = eqn (CX40 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ []) (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ CX40 ∷ CCZ134 ∷ CS14 ∷ []) (wp0081 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ CX40 ∷ CCZ134 ∷ CS14 ∷ Bx2-0413 ∷ []) (lem-F1-X-CS0-nf-of-rhs c4)

-- F1 X-CS0: 26 steps
lem-F1-X-CS0 : Ws → ⟪ (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ
lem-F1-X-CS0 c4 = derive (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ [])
  (rw 0 (q31 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw⁻ 1 (q32 c4) ∷
   rw 3 (q33 c4) ∷
   rw 3 (q34 c4) ∷
   rw 3 (q35 c4) ∷
   rw 2 (q36 c4) ∷
   rw 2 (q37 c4) ∷
   rw 2 (q38 c4) ∷
   rw 2 (q39 c4) ∷
   rw 2 (q40 c4) ∷
   rw 3 (q41 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 6 (q33 c4) ∷
   rw 6 (q34 c4) ∷
   rw 6 (q35 c4) ∷
   rw 5 (q36 c4) ∷
   rw 5 (q37 c4) ∷
   rw 5 (q38 c4) ∷
   rw 5 (q39 c4) ∷
   rw 5 (q40 c4) ∷
   rw 6 (q42 c4) ∷
   rw 0 (q50 c4) ∷
   rw⁻ 0 (q51 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = eqn (CCZ124 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ []) (lem-c124-beta c4)

-- auto BOX(0;1234) | CCZ124: 1 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124 : Ws → ⟪ (Bx0-1234 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124 c4 = derive (Bx0-1234 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1234 ∷ [])
  (rw⁻ 0 (q52 c4) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = eqn (Sw23 ∷ CCZ134 ∷ []) (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (Bx0-1234 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (Sw23 ∷ CCZ124 ∷ []) (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4))

-- auto BOX(0;1234) | CCZ124 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2332 c4 = derive (Bx0-1324 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q18 c4) ∷
   rw 2 (q53 c4) ∷
   rw 1 (q54 c4) ∷
   rw 0 (q55 c4) ∷
   rw 1 (q21 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q56 : Ws → Eqn
  q56 c4 = eqn (CCZ134 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ134 ∷ []) (wl0154 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (Bx0-1324 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2332 c4)

-- auto BOX(0;1234) | CCZ124 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at243243 : Ws → ⟪ (Bx0-1423 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at243243 c4 = derive (Bx0-1423 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw⁻ 2 (q56 c4) ∷
   rw 1 (q57 c4) ∷
   rw⁻ 0 (q56 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q58 : Ws → Eqn
  q58 c4 = eqn (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (Bx0-1423 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at243243 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4))

-- auto BOX(0;1234) | CCZ124 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0110243243 c4 = derive (Bx1-0423 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q7 c4) ∷
   rw 2 (q58 c4) ∷
   rw 1 (q59 c4) ∷
   rw 0 (q60 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q6 c4) ∷ []) Eq.refl

private
  q61 : Ws → Eqn
  q61 c4 = eqn (Sw12 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (Bx1-0423 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0110243243 c4)

-- auto BOX(0;1234) | CCZ124 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0210243143 c4 = derive (Bx2-0413 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q12 c4) ∷
   rw 2 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   rw 0 (q61 c4) ∷
   rw 1 (q16 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = eqn (Sw23 ∷ CS13 ∷ []) (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (Bx0-1234 ∷ CS12 ∷ []) (CS12 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS21 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (Sw23 ∷ CS12 ∷ []) (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 (lit c4))

-- auto BOX(0;1234) | CS21 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS21-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS21-at2332 c4 = derive (Bx0-1324 ∷ CS13 ∷ []) (CS13 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q18 c4) ∷
   rw 2 (q63 c4) ∷
   rw 1 (q64 c4) ∷
   rw 0 (q65 c4) ∷
   rw 1 (q21 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = eqn (Sw34 ∷ CS14 ∷ []) (CS13 ∷ Sw34 ∷ []) (lem-nat-3-CS14 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (Bx0-1324 ∷ CS13 ∷ []) (CS13 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS21-at2332 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (Sw34 ∷ CS13 ∷ []) (CS14 ∷ Sw34 ∷ []) (lem-nat-3-CS13 (lit c4))

-- auto BOX(0;1234) | CS21 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS21-at243243 : Ws → ⟪ (Bx0-1423 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS21-at243243 c4 = derive (Bx0-1423 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q66 c4) ∷
   rw 1 (q67 c4) ∷
   rw 0 (q68 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q69 : Ws → Eqn
  q69 c4 = eqn (Sw01 ∷ CS04 ∷ []) (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (Bx0-1423 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS21-at243243 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (Sw01 ∷ CS14 ∷ []) (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4))

-- auto BOX(0;1234) | CS21 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS21-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS21-at0110243243 c4 = derive (Bx1-0423 ∷ CS04 ∷ []) (CS04 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q7 c4) ∷
   rw 2 (q69 c4) ∷
   rw 1 (q70 c4) ∷
   rw 0 (q71 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q6 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = eqn (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4))
  q73 : Ws → Eqn
  q73 c4 = eqn (Bx1-0423 ∷ CS04 ∷ []) (CS04 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS21-at0110243243 c4)

-- auto BOX(0;1234) | CS21 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS21-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS21-at0210243143 c4 = derive (Bx2-0413 ∷ CS04 ∷ []) (CS04 ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q12 c4) ∷
   rw 2 (q72 c4) ∷
   rw 1 (q73 c4) ∷
   rw 0 (q72 c4) ∷
   rw 1 (q16 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q74 : Ws → Eqn
  q74 c4 = eqn (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ []) (CX41 ∷ []) (wl0278 (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (CX41 ∷ CX41 ∷ []) [] (wl0279 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (CX41 ∷ Bx2-0413 ∷ CX41 ∷ []) (Bx2-0413 ∷ CCZ034 ∷ []) (lem-CX23-beta-at0210243143 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (Bx2-0413 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0210243143 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (Bx2-0413 ∷ CS04 ∷ []) (CS04 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS21-at0210243143 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (CS03⁻ ∷ CX41 ∷ []) (CX41 ∷ CS03⁻ ∷ []) (wp0082 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (CCZ014 ∷ CX41 ∷ []) (CX41 ∷ CZ04 ∷ CCZ014 ∷ []) (wp0083 c4)

-- F1 X-CS1 [nf of rhs]: 32 steps
lem-F1-X-CS1-nf-of-rhs : Ws → ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CX41 ∷ CZ04 ∷ CCZ014 ∷ CS03⁻ ∷ CCZ034 ∷ CS04 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-F1-X-CS1-nf-of-rhs c4 = derive (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CX41 ∷ CZ04 ∷ CCZ014 ∷ CS03⁻ ∷ CCZ034 ∷ CS04 ∷ Bx2-0413 ∷ [])
  (rw 0 (q30 c4) ∷
   rw 2 (q74 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw⁻ 1 (q32 c4) ∷
   rw 3 (q33 c4) ∷
   rw 3 (q34 c4) ∷
   rw 3 (q35 c4) ∷
   rw 2 (q36 c4) ∷
   rw 2 (q37 c4) ∷
   rw 2 (q38 c4) ∷
   rw 2 (q39 c4) ∷
   rw 2 (q40 c4) ∷
   rw 3 (q41 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 6 (q33 c4) ∷
   rw 6 (q34 c4) ∷
   rw 6 (q35 c4) ∷
   rw 5 (q36 c4) ∷
   rw 5 (q37 c4) ∷
   rw 5 (q38 c4) ∷
   rw 5 (q39 c4) ∷
   rw 5 (q40 c4) ∷
   rw 6 (q42 c4) ∷
   rw⁻ 7 (q75 c4) ∷
   rw 8 (q76 c4) ∷
   rw 8 (q77 c4) ∷
   rw 9 (q78 c4) ∷
   rw 6 (q79 c4) ∷
   rw 5 (q80 c4) ∷
   rw 0 (q49 c4) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = eqn (CX41 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ []) (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CX41 ∷ CZ04 ∷ CCZ014 ∷ CS03⁻ ∷ CCZ034 ∷ CS04 ∷ []) (wp0084 c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CX41 ∷ CZ04 ∷ CCZ014 ∷ CS03⁻ ∷ CCZ034 ∷ CS04 ∷ Bx2-0413 ∷ []) (lem-F1-X-CS1-nf-of-rhs c4)

-- F1 X-CS1: 26 steps
lem-F1-X-CS1 : Ws → ⟪ (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) ⟫ʷ
lem-F1-X-CS1 c4 = derive (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ [])
  (rw 0 (q74 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw⁻ 1 (q32 c4) ∷
   rw 3 (q33 c4) ∷
   rw 3 (q34 c4) ∷
   rw 3 (q35 c4) ∷
   rw 2 (q36 c4) ∷
   rw 2 (q37 c4) ∷
   rw 2 (q38 c4) ∷
   rw 2 (q39 c4) ∷
   rw 2 (q40 c4) ∷
   rw 3 (q41 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 6 (q33 c4) ∷
   rw 6 (q34 c4) ∷
   rw 6 (q35 c4) ∷
   rw 5 (q36 c4) ∷
   rw 5 (q37 c4) ∷
   rw 5 (q38 c4) ∷
   rw 5 (q39 c4) ∷
   rw 5 (q40 c4) ∷
   rw 6 (q42 c4) ∷
   rw 0 (q81 c4) ∷
   rw⁻ 0 (q82 c4) ∷ []) Eq.refl

private
  q83 : Ws → Eqn
  q83 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1324 ∷ []) (lem-sym23 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (CS13 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS13 ∷ []) (lem-CS12-beta-at2332 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (Bx0-1324 ∷ []) (Bx0-1234 ∷ []) (lem-sym23-at2332 c4)

-- auto BOX(0;1234) | CS13: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CS13 : Ws → ⟪ (Bx0-1234 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS13 c4 = derive (Bx0-1234 ∷ CS13 ∷ []) (CS13 ∷ Bx0-1234 ∷ [])
  (rw 0 (q83 c4) ∷
   rw⁻ 0 (q84 c4) ∷
   rw 1 (q85 c4) ∷ []) Eq.refl

private
  q86 : Ws → Eqn
  q86 c4 = eqn (CCZ134 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CCZ134 ∷ []) (lem-c124-beta-at2332 c4)

-- auto BOX(0;1234) | CCZ134: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134 : Ws → ⟪ (Bx0-1234 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134 c4 = derive (Bx0-1234 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1234 ∷ [])
  (rw 0 (q83 c4) ∷
   rw⁻ 0 (q86 c4) ∷
   rw 1 (q85 c4) ∷ []) Eq.refl

private
  q87 : Ws → Eqn
  q87 c4 = eqn (Sw12 ∷ X2 ∷ []) (X1 ∷ Sw12 ∷ []) (wl0280 (lit c4))
  q88 : Ws → Eqn
  q88 c4 = eqn (Sw12 ∷ Bx0-2134 ∷ []) (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4))
  q89 : Ws → Eqn
  q89 c4 = eqn (X1 ∷ Bx0-1234 ∷ X1 ∷ []) (CCZ234 ∷ Bx0-1234 ∷ []) (lem-X1-beta c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (Sw12 ∷ Bx0-1234 ∷ []) (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4))

-- X1-beta @1221: 8 steps
lem-X1-beta-at1221 : Ws → ⟪ (X2 ∷ Bx0-2134 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-2134 ∷ []) ⟫ʷ
lem-X1-beta-at1221 c4 = derive (X2 ∷ Bx0-2134 ∷ X2 ∷ []) (CCZ134 ∷ Bx0-2134 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q87 c4) ∷
   rw 2 (q88 c4) ∷
   rw 3 (q87 c4) ∷
   rw 1 (q89 c4) ∷
   rw⁻ 0 (q15 c4) ∷
   rw 1 (q90 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q91 : Ws → Eqn
  q91 c4 = eqn (Sw23 ∷ X3 ∷ []) (X2 ∷ Sw23 ∷ []) (wl0281 (lit c4))
  q92 : Ws → Eqn
  q92 c4 = eqn (Sw23 ∷ Bx0-3124 ∷ []) (Bx0-2134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3124⟩ (lit c4))
  q93 : Ws → Eqn
  q93 c4 = eqn (X2 ∷ Bx0-2134 ∷ X2 ∷ []) (CCZ134 ∷ Bx0-2134 ∷ []) (lem-X1-beta-at1221 c4)
  q94 : Ws → Eqn
  q94 c4 = eqn (Sw23 ∷ Bx0-2134 ∷ []) (Bx0-3124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2134⟩ (lit c4))

-- X1-beta @132132: 8 steps
lem-X1-beta-at132132 : Ws → ⟪ (X3 ∷ Bx0-3124 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-3124 ∷ []) ⟫ʷ
lem-X1-beta-at132132 c4 = derive (X3 ∷ Bx0-3124 ∷ X3 ∷ []) (CCZ124 ∷ Bx0-3124 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q91 c4) ∷
   rw 2 (q92 c4) ∷
   rw 3 (q91 c4) ∷
   rw 1 (q93 c4) ∷
   rw 0 (q53 c4) ∷
   rw 1 (q94 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q95 : Ws → Eqn
  q95 c4 = eqn (Sw34 ∷ X4 ∷ []) (X3 ∷ Sw34 ∷ []) (wl0282 (lit c4))
  q96 : Ws → Eqn
  q96 c4 = eqn (Sw34 ∷ Bx0-4123 ∷ []) (Bx0-3124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4123⟩ (lit c4))
  q97 : Ws → Eqn
  q97 c4 = eqn (X3 ∷ Bx0-3124 ∷ X3 ∷ []) (CCZ124 ∷ Bx0-3124 ∷ []) (lem-X1-beta-at132132 c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (Sw34 ∷ CCZ124 ∷ []) (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 (lit c4))
  q99 : Ws → Eqn
  q99 c4 = eqn (Sw34 ∷ Bx0-3124 ∷ []) (Bx0-4123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3124⟩ (lit c4))

-- X1-beta @14213243: 8 steps
lem-X1-beta-at14213243 : Ws → ⟪ (X4 ∷ Bx0-4123 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-4123 ∷ []) ⟫ʷ
lem-X1-beta-at14213243 c4 = derive (X4 ∷ Bx0-4123 ∷ X4 ∷ []) (CCZ123 ∷ Bx0-4123 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q95 c4) ∷
   rw 2 (q96 c4) ∷
   rw 3 (q95 c4) ∷
   rw 1 (q97 c4) ∷
   rw 0 (q98 c4) ∷
   rw 1 (q99 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = eqn (Sw01 ∷ X4 ∷ []) (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑))
  q101 : Ws → Eqn
  q101 c4 = eqn (Sw01 ∷ Bx1-4023 ∷ []) (Bx0-4123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4023⟩ (lit c4))
  q102 : Ws → Eqn
  q102 c4 = eqn (X4 ∷ Bx0-4123 ∷ X4 ∷ []) (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4)
  q103 : Ws → Eqn
  q103 c4 = eqn (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ []) (wl0003 (lit c4))
  q104 : Ws → Eqn
  q104 c4 = eqn (Sw01 ∷ Bx0-4123 ∷ []) (Bx1-4023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4123⟩ (lit c4))

-- X1-beta @0114203243: 8 steps
lem-X1-beta-at0114203243 : Ws → ⟪ (X4 ∷ Bx1-4023 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Bx1-4023 ∷ []) ⟫ʷ
lem-X1-beta-at0114203243 c4 = derive (X4 ∷ Bx1-4023 ∷ X4 ∷ []) (CCZ023 ∷ Bx1-4023 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q100 c4) ∷
   rw 2 (q101 c4) ∷
   rw 3 (q100 c4) ∷
   rw 1 (q102 c4) ∷
   rw⁻ 0 (q103 c4) ∷
   rw 1 (q104 c4) ∷
   rw 2 (q6 c4) ∷ []) Eq.refl

private
  q105 : Ws → Eqn
  q105 c4 = eqn (Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑))
  q106 : Ws → Eqn
  q106 c4 = eqn (Sw12 ∷ Bx2-4013 ∷ []) (Bx1-4023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4013⟩ (lit c4))
  q107 : Ws → Eqn
  q107 c4 = eqn (X4 ∷ Bx1-4023 ∷ X4 ∷ []) (CCZ023 ∷ Bx1-4023 ∷ []) (lem-X1-beta-at0114203243 c4)
  q108 : Ws → Eqn
  q108 c4 = eqn (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4))
  q109 : Ws → Eqn
  q109 c4 = eqn (Sw12 ∷ Bx1-4023 ∷ []) (Bx2-4013 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4023⟩ (lit c4))

-- X1-beta @0214203143: 8 steps
lem-X1-beta-at0214203143 : Ws → ⟪ (X4 ∷ Bx2-4013 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Bx2-4013 ∷ []) ⟫ʷ
lem-X1-beta-at0214203143 c4 = derive (X4 ∷ Bx2-4013 ∷ X4 ∷ []) (CCZ013 ∷ Bx2-4013 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q105 c4) ∷
   rw 2 (q106 c4) ∷
   rw 3 (q105 c4) ∷
   rw 1 (q107 c4) ∷
   rw 0 (q108 c4) ∷
   rw 1 (q109 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q110 : Ws → Eqn
  q110 c4 = eqn (Bx0-1234 ∷ CS13 ∷ []) (CS13 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13 c4)

-- auto BOX(0;1234) | CS13 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS13-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS13-at2332 c4 = derive (Bx0-1324 ∷ CS12 ∷ []) (CS12 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q18 c4) ∷
   rw 2 (q65 c4) ∷
   rw 1 (q110 c4) ∷
   rw 0 (q63 c4) ∷
   rw 1 (q21 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q111 : Ws → Eqn
  q111 c4 = eqn (CS12 ∷ Sw34 ∷ []) (Sw34 ∷ CS12 ∷ []) (c₃ (CS ↑) (Swap))
  q112 : Ws → Eqn
  q112 c4 = eqn (Bx0-1324 ∷ CS12 ∷ []) (CS12 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at2332 c4)

-- auto BOX(0;1234) | CS13 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS13-at243243 : Ws → ⟪ (Bx0-1423 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS13-at243243 c4 = derive (Bx0-1423 ∷ CS12 ∷ []) (CS12 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw⁻ 2 (q111 c4) ∷
   rw 1 (q112 c4) ∷
   rw⁻ 0 (q111 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q113 : Ws → Eqn
  q113 c4 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wl0138 (lit c4))
  q114 : Ws → Eqn
  q114 c4 = eqn (Bx0-1423 ∷ CS12 ∷ []) (CS12 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at243243 c4)
  q115 : Ws → Eqn
  q115 c4 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wl0035 (lit c4))

-- auto BOX(0;1234) | CS13 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS13-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS13-at0110243243 c4 = derive (Bx1-0423 ∷ CS02 ∷ []) (CS02 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q7 c4) ∷
   rw⁻ 2 (q113 c4) ∷
   rw 1 (q114 c4) ∷
   rw⁻ 0 (q115 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q6 c4) ∷ []) Eq.refl

private
  q116 : Ws → Eqn
  q116 c4 = eqn (Sw12 ∷ CS01 ∷ []) (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4))
  q117 : Ws → Eqn
  q117 c4 = eqn (Bx1-0423 ∷ CS02 ∷ []) (CS02 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at0110243243 c4)
  q118 : Ws → Eqn
  q118 c4 = eqn (Sw12 ∷ CS02 ∷ []) (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4))

-- auto BOX(0;1234) | CS13 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS13-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS13-at0210243143 c4 = derive (Bx2-0413 ∷ CS01 ∷ []) (CS01 ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q12 c4) ∷
   rw 2 (q116 c4) ∷
   rw 1 (q117 c4) ∷
   rw 0 (q118 c4) ∷
   rw 1 (q16 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q119 : Ws → Eqn
  q119 c4 = eqn (Bx0-1234 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134 c4)

-- auto BOX(0;1234) | CCZ134 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332 c4 = derive (Bx0-1324 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q18 c4) ∷
   rw 2 (q55 c4) ∷
   rw 1 (q119 c4) ∷
   rw 0 (q53 c4) ∷
   rw 1 (q21 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q120 : Ws → Eqn
  q120 c4 = eqn (Sw34 ∷ CCZ123 ∷ []) (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 (lit c4))
  q121 : Ws → Eqn
  q121 c4 = eqn (Bx0-1324 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332 c4)

-- auto BOX(0;1234) | CCZ134 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at243243 : Ws → ⟪ (Bx0-1423 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at243243 c4 = derive (Bx0-1423 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q120 c4) ∷
   rw 1 (q121 c4) ∷
   rw 0 (q98 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q122 : Ws → Eqn
  q122 c4 = eqn (CCZ123 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ []) (wl0103 (lit c4))
  q123 : Ws → Eqn
  q123 c4 = eqn (Bx0-1423 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at243243 c4)

-- auto BOX(0;1234) | CCZ134 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0110243243 c4 = derive (Bx1-0423 ∷ CCZ023 ∷ []) (CCZ023 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q7 c4) ∷
   rw⁻ 2 (q122 c4) ∷
   rw 1 (q123 c4) ∷
   rw⁻ 0 (q103 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q6 c4) ∷ []) Eq.refl

private
  q124 : Ws → Eqn
  q124 c4 = eqn (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4))
  q125 : Ws → Eqn
  q125 c4 = eqn (Bx1-0423 ∷ CCZ023 ∷ []) (CCZ023 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0110243243 c4)

-- auto BOX(0;1234) | CCZ134 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0210243143 c4 = derive (Bx2-0413 ∷ CCZ013 ∷ []) (CCZ013 ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q12 c4) ∷
   rw 2 (q124 c4) ∷
   rw 1 (q125 c4) ∷
   rw 0 (q108 c4) ∷
   rw 1 (q16 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = eqn (X4 ∷ X4 ∷ []) [] (wl0283 (lit c4))
  q127 : Ws → Eqn
  q127 c4 = eqn (X4 ∷ Bx2-4013 ∷ X4 ∷ []) (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4)
  q128 : Ws → Eqn
  q128 c4 = eqn (CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) (X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (wp0085 c4)
  q129 : Ws → Eqn
  q129 c4 = eqn (Bx2-0413 ∷ CS01 ∷ []) (CS01 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at0210243143 c4)
  q130 : Ws → Eqn
  q130 c4 = eqn (Bx2-0413 ∷ CCZ013 ∷ []) (CCZ013 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0210243143 c4)
  q131 : Ws → Eqn
  q131 c4 = eqn (CCZ014 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ []) (CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ []) (wp0086 c4)
  q132 : Ws → Eqn
  q132 c4 = eqn (CCZ014 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) (CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CCZ014 ∷ []) (wp0087 c4)
  q133 : Ws → Eqn
  q133 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp0055 c4)
  q134 : Ws → Eqn
  q134 c4 = eqn (Bx2-0413 ∷ Bx2-0413 ∷ []) [] (lem-beta-inv-at0210243143 c4)
  q135 : Ws → Eqn
  q135 c4 = eqn (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS01 ∷ []) (wp0088 c4)

-- F5 CS01: 38 steps
lem-F5-CS01 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
lem-F5-CS01 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CS01 ∷ [])
  (re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw⁻ 2 (q126 c4) ∷
   rw 1 (q33 c4) ∷
   rw 0 (q127 c4) ∷
   rw 1 (q39 c4) ∷
   re 8 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 10 1 (CS03 ∷ []) ∷
   re 12 1 (CS03⁻ ∷ []) ∷
   rw⁻ 2 (q128 c4) ∷
   rw 1 (q129 c4) ∷
   rw 2 (q130 c4) ∷
   rw 3 (q41 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 6 (q33 c4) ∷
   rw 6 (q34 c4) ∷
   rw 6 (q35 c4) ∷
   rw 5 (q36 c4) ∷
   rw 5 (q37 c4) ∷
   rw 5 (q38 c4) ∷
   rw 5 (q39 c4) ∷
   rw 5 (q40 c4) ∷
   rw 6 (q42 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   rw 9 (q33 c4) ∷
   rw 9 (q34 c4) ∷
   rw 9 (q35 c4) ∷
   rw 8 (q36 c4) ∷
   rw 8 (q37 c4) ∷
   rw 8 (q38 c4) ∷
   rw 8 (q39 c4) ∷
   rw 8 (q40 c4) ∷
   rw⁻ 1 (q131 c4) ∷
   rw⁻ 2 (q132 c4) ∷
   rw 1 (q133 c4) ∷
   rw 7 (q134 c4) ∷
   rw 0 (q135 c4) ∷ []) Eq.refl

private
  q136 : Ws → Eqn
  q136 c4 = eqn (Sw23 ∷ Bx0-1432 ∷ []) (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4))
  q137 : Ws → Eqn
  q137 c4 = eqn (Bx0-1423 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4)
  q138 : Ws → Eqn
  q138 c4 = eqn (Sw23 ∷ Toff014 ∷ []) (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 (lit c4))
  q139 : Ws → Eqn
  q139 c4 = eqn (CCZ023 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ023 ∷ []) (wl0065 (lit c4))

-- beta-T @2442: 8 steps
lem-beta-T-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-beta-T-at2442 c4 = derive (Bx0-1432 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q136 c4) ∷
   rw 1 (q137 c4) ∷
   rw 0 (q138 c4) ∷
   rw⁻ 1 (q139 c4) ∷
   rw 2 (q138 c4) ∷
   rw⁻ 3 (q139 c4) ∷
   rw 4 (q17 c4) ∷ []) Eq.refl

private
  q140 : Ws → Eqn
  q140 c4 = eqn (Bx0-1432 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4)
  q141 : Ws → Eqn
  q141 c4 = eqn (CS12⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS12⁻ ∷ []) (wp0089 c4)
  q142 : Ws → Eqn
  q142 c4 = eqn (CCZ023 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ023 ∷ []) (wl0284 (lit c4))

-- auto SBOXd(0;1;2;3) | BOX(0;1432): 14 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ : Ws → ⟪ (Sb⁻0-1-2-3 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ c4 = derive (Sb⁻0-1-2-3 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ Sb⁻0-1-2-3 ∷ [])
  (rw 1 (q140 c4) ∷
   re 0 1 (CS12⁻ ∷ []) ∷
   rw 0 (q141 c4) ∷
   re 1 1 (Sb⁻0-1-2-3 ∷ []) ∷
   re 1 1 (CS12⁻ ∷ []) ∷
   rw⁻ 1 (q142 c4) ∷
   re 2 1 (Sb⁻0-1-2-3 ∷ []) ∷
   re 2 1 (CS12⁻ ∷ []) ∷
   rw 2 (q141 c4) ∷
   re 3 1 (Sb⁻0-1-2-3 ∷ []) ∷
   re 3 1 (CS12⁻ ∷ []) ∷
   rw⁻ 3 (q142 c4) ∷
   re 4 1 (Sb⁻0-1-2-3 ∷ []) ∷
   rw⁻ 0 (q140 c4) ∷ []) Eq.refl

private
  q143 : Ws → Eqn
  q143 c4 = eqn (Sb⁻0-1-2-3 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ c4)
  q144 : Ws → Eqn
  q144 c4 = eqn (CS12⁻ ∷ Toff234 ∷ CS12 ∷ Toff234 ∷ []) (Toff234 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ []) (wl0285 (lit c4))
  q145 : Ws → Eqn
  q145 c4 = eqn (CS12⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS12⁻ ∷ []) (wl0286 (lit c4))

-- auto SBOXd(0;1;2;3) | SBOX(0;1;43;2): 13 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩ : Ws → ⟪ (Sb⁻0-1-2-3 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩ c4 = derive (Sb⁻0-1-2-3 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ Sb⁻0-1-2-3 ∷ [])
  (re 1 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) ∷
   rw 0 (q143 c4) ∷
   re 1 1 (CS12⁻ ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   rw 1 (q144 c4) ∷
   re 2 1 (Sb0-1-2-3 ∷ []) ∷
   re 4 1 (Sb⁻0-1-2-3 ∷ []) ∷
   re 4 1 (CS12⁻ ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw 4 (q145 c4) ∷
   re 4 1 (Sb⁻0-1-2-3 ∷ []) ∷
   re 5 1 (Sb⁻0-1-2-3 ∷ []) ∷
   re 0 5 (Sb0-1-43-2 ∷ []) ∷ []) Eq.refl

private
  q146 : Ws → Eqn
  q146 c4 = eqn (K0⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0⁻ ∷ []) (lem-K0-pass-ci c4)

-- auto Kd0 | BOX(0;1234): 1 steps
lem-auto-Kd0-∣-BOX⟨0·1234⟩ : Ws → ⟪ (K0⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-BOX⟨0·1234⟩ c4 = derive (K0⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0⁻ ∷ [])
  (rw 0 (q146 c4) ∷ []) Eq.refl

private
  q147 : Ws → Eqn
  q147 c4 = eqn (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4))
  q148 : Ws → Eqn
  q148 c4 = eqn (Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ []) (lem-F0 c4)
  q149 : Ws → Eqn
  q149 c4 = eqn (Sw12 ∷ Sb3-0-41-2 ∷ []) (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ (lit c4))

-- F0 @1221: 5 steps
lem-F0-at1221 : Ws → ⟪ (Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-42-1 ∷ []) ⟫ʷ
lem-F0-at1221 c4 = derive (Sb1-0-42-3 ∷ []) (Sb3-0-42-1 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q147 c4) ∷
   rw 1 (q148 c4) ∷
   rw 0 (q149 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q150 : Ws → Eqn
  q150 c4 = eqn (Sw23 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4))
  q151 : Ws → Eqn
  q151 c4 = eqn (Sb1-0-42-3 ∷ []) (Sb3-0-42-1 ∷ []) (lem-F0-at1221 c4)
  q152 : Ws → Eqn
  q152 c4 = eqn (Sw23 ∷ Sb3-0-42-1 ∷ []) (Sb2-0-43-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·42·1⟩ (lit c4))

-- F0 @132132: 5 steps
lem-F0-at132132 : Ws → ⟪ (Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-43-1 ∷ []) ⟫ʷ
lem-F0-at132132 c4 = derive (Sb1-0-43-2 ∷ []) (Sb2-0-43-1 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q150 c4) ∷
   rw 1 (q151 c4) ∷
   rw 0 (q152 c4) ∷
   rw 1 (q17 c4) ∷ []) Eq.refl

private
  q153 : Ws → Eqn
  q153 c4 = eqn (Sw34 ∷ Sb1-0-34-2 ∷ []) (Sb1-0-43-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·34·2⟩ (lit c4))
  q154 : Ws → Eqn
  q154 c4 = eqn (Sb1-0-43-2 ∷ []) (Sb2-0-43-1 ∷ []) (lem-F0-at132132 c4)
  q155 : Ws → Eqn
  q155 c4 = eqn (Sw34 ∷ Sb2-0-43-1 ∷ []) (Sb2-0-34-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·43·1⟩ (lit c4))

-- F0 @14213243: 5 steps
lem-F0-at14213243 : Ws → ⟪ (Sb1-0-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-34-1 ∷ []) ⟫ʷ
lem-F0-at14213243 c4 = derive (Sb1-0-34-2 ∷ []) (Sb2-0-34-1 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q153 c4) ∷
   rw 1 (q154 c4) ∷
   rw 0 (q155 c4) ∷
   rw 1 (q1 c4) ∷ []) Eq.refl

private
  q156 : Ws → Eqn
  q156 c4 = eqn (Sw01 ∷ Sb0-1-34-2 ∷ []) (Sb1-0-34-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·34·2⟩ (lit c4))
  q157 : Ws → Eqn
  q157 c4 = eqn (Sb1-0-34-2 ∷ []) (Sb2-0-34-1 ∷ []) (lem-F0-at14213243 c4)
  q158 : Ws → Eqn
  q158 c4 = eqn (Sw01 ∷ Sb2-0-34-1 ∷ []) (Sb2-1-34-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·34·1⟩ (lit c4))

-- F0 @0114203243: 5 steps
lem-F0-at0114203243 : Ws → ⟪ (Sb0-1-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-34-0 ∷ []) ⟫ʷ
lem-F0-at0114203243 c4 = derive (Sb0-1-34-2 ∷ []) (Sb2-1-34-0 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q156 c4) ∷
   rw 1 (q157 c4) ∷
   rw 0 (q158 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q159 : Ws → Eqn
  q159 c4 = eqn (Sw12 ∷ Sb0-2-34-1 ∷ []) (Sb0-1-34-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·34·1⟩ (lit c4))
  q160 : Ws → Eqn
  q160 c4 = eqn (Sb0-1-34-2 ∷ []) (Sb2-1-34-0 ∷ []) (lem-F0-at0114203243 c4)
  q161 : Ws → Eqn
  q161 c4 = eqn (Sw12 ∷ Sb2-1-34-0 ∷ []) (Sb1-2-34-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·34·0⟩ (lit c4))

-- F0 @0214203143: 5 steps
lem-F0-at0214203143 : Ws → ⟪ (Sb0-2-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-34-0 ∷ []) ⟫ʷ
lem-F0-at0214203143 c4 = derive (Sb0-2-34-1 ∷ []) (Sb1-2-34-0 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q159 c4) ∷
   rw 1 (q160 c4) ∷
   rw 0 (q161 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q162 : Ws → Eqn
  q162 c4 = eqn (Sw01 ∷ Sb1-2-34-0 ∷ []) (Sb0-2-34-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·34·0⟩ (lit c4))
  q163 : Ws → Eqn
  q163 c4 = eqn (Sb0-2-34-1 ∷ []) (Sb1-2-34-0 ∷ []) (lem-F0-at0214203143 c4)

-- F0 @0214213043: 5 steps
lem-F0-at0214213043 : Ws → ⟪ (Sb1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-34-1 ∷ []) ⟫ʷ
lem-F0-at0214213043 c4 = derive (Sb1-2-34-0 ∷ []) (Sb0-2-34-1 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q162 c4) ∷
   rw 1 (q163 c4) ∷
   rw 0 (q162 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q164 : Ws → Eqn
  q164 c4 = eqn (K0⁻ ∷ Sw34 ∷ []) (Sw34 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ ↑))
  q165 : Ws → Eqn
  q165 c4 = eqn (Sw34 ∷ Bx0-1243 ∷ []) (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ (lit c4))
  q166 : Ws → Eqn
  q166 c4 = eqn (K0⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-BOX⟨0·1234⟩ c4)
  q167 : Ws → Eqn
  q167 c4 = eqn (Sw34 ∷ Bx0-1234 ∷ []) (Bx0-1243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1234⟩ (lit c4))

-- auto Kd0 | BOX(0;1234) @3443: 7 steps
lem-auto-Kd0-∣-BOX⟨0·1234⟩-at3443 : Ws → ⟪ (K0⁻ ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-BOX⟨0·1234⟩-at3443 c4 = derive (K0⁻ ∷ Bx0-1243 ∷ []) (Bx0-1243 ∷ K0⁻ ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q164 c4) ∷
   rw 2 (q165 c4) ∷
   rw 1 (q166 c4) ∷
   rw 0 (q167 c4) ∷
   rw⁻ 1 (q164 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q168 : Ws → Eqn
  q168 c4 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑))
  q169 : Ws → Eqn
  q169 c4 = eqn (Sw23 ∷ Bx0-1342 ∷ []) (Bx0-1243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1342⟩ (lit c4))
  q170 : Ws → Eqn
  q170 c4 = eqn (K0⁻ ∷ Bx0-1243 ∷ []) (Bx0-1243 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-BOX⟨0·1234⟩-at3443 c4)
  q171 : Ws → Eqn
  q171 c4 = eqn (Sw23 ∷ Bx0-1243 ∷ []) (Bx0-1342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1243⟩ (lit c4))

-- auto Kd0 | BOX(0;1234) @233442: 7 steps
lem-auto-Kd0-∣-BOX⟨0·1234⟩-at233442 : Ws → ⟪ (K0⁻ ∷ Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-BOX⟨0·1234⟩-at233442 c4 = derive (K0⁻ ∷ Bx0-1342 ∷ []) (Bx0-1342 ∷ K0⁻ ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw⁻ 1 (q168 c4) ∷
   rw 2 (q169 c4) ∷
   rw 1 (q170 c4) ∷
   rw 0 (q171 c4) ∷
   rw⁻ 1 (q168 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q172 : Ws → Eqn
  q172 c4 = eqn (K0⁻ ∷ Sw12 ∷ []) (Sw12 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap))
  q173 : Ws → Eqn
  q173 c4 = eqn (Sw12 ∷ Bx0-2341 ∷ []) (Bx0-1342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2341⟩ (lit c4))
  q174 : Ws → Eqn
  q174 c4 = eqn (K0⁻ ∷ Bx0-1342 ∷ []) (Bx0-1342 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-BOX⟨0·1234⟩-at233442 c4)
  q175 : Ws → Eqn
  q175 c4 = eqn (Sw12 ∷ Bx0-1342 ∷ []) (Bx0-2341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1342⟩ (lit c4))

-- auto Kd0 | BOX(0;1234) @12233441: 7 steps
lem-auto-Kd0-∣-BOX⟨0·1234⟩-at12233441 : Ws → ⟪ (K0⁻ ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-BOX⟨0·1234⟩-at12233441 c4 = derive (K0⁻ ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ K0⁻ ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw⁻ 1 (q172 c4) ∷
   rw 2 (q173 c4) ∷
   rw 1 (q174 c4) ∷
   rw 0 (q175 c4) ∷
   rw⁻ 1 (q172 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q176 : Ws → Eqn
  q176 c4 = eqn (Sb1-2-34-0 ∷ []) (Sb0-2-34-1 ∷ []) (lem-F0-at0214213043 c4)
  q177 : Ws → Eqn
  q177 c4 = eqn (K0⁻ ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-BOX⟨0·1234⟩-at12233441 c4)
  q178 : Ws → Eqn
  q178 c4 = eqn (K0⁻ ∷ Toff134 ∷ []) (Toff134 ∷ K0⁻ ∷ []) (wp0090 c4)
  q179 : Ws → Eqn
  q179 c4 = eqn (CS12 ∷ K0⁻ ∷ []) (K0⁻ ∷ CS12 ∷ []) (wl0287 (lit c4))
  q180 : Ws → Eqn
  q180 c4 = eqn (CS12⁻ ∷ K0⁻ ∷ []) (K0⁻ ∷ CS12⁻ ∷ []) (wl0288 (lit c4))

-- auto Kd0 | SBOX(1;2;34;0): 13 steps
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩ : Ws → ⟪ (K0⁻ ∷ Sb1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-34-0 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩ c4 = derive (K0⁻ ∷ Sb1-2-34-0 ∷ []) (Sb1-2-34-0 ∷ K0⁻ ∷ [])
  (rw 1 (q176 c4) ∷
   re 1 1 (Bx0-2341 ∷ Toff134 ∷ Sb0-2-1-4 ∷ Toff134 ∷ Sb⁻0-2-1-4 ∷ []) ∷
   rw 0 (q177 c4) ∷
   rw 1 (q178 c4) ∷
   re 3 1 (CS12 ∷ []) ∷
   rw⁻ 2 (q179 c4) ∷
   re 2 1 (Sb0-2-1-4 ∷ []) ∷
   rw 3 (q178 c4) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw⁻ 4 (q180 c4) ∷
   re 4 1 (Sb⁻0-2-1-4 ∷ []) ∷
   re 0 5 (Sb0-2-34-1 ∷ []) ∷
   rw⁻ 0 (q176 c4) ∷ []) Eq.refl

private
  q181 : Ws → Eqn
  q181 c4 = eqn (Sw23 ∷ Bx0-3142 ∷ []) (Bx0-2143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3142⟩ (lit c4))
  q182 : Ws → Eqn
  q182 c4 = eqn (Bx0-2143 ∷ []) (Bx0-1243 ∷ []) (lem-sym12-at12213443 c4)

-- sym12 @13213442: 5 steps
lem-sym12-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-sym12-at13213442 c4 = derive (Bx0-3142 ∷ []) (Bx0-1342 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q181 c4) ∷
   rw 1 (q182 c4) ∷
   rw 0 (q171 c4) ∷
   rw 1 (q17 c4) ∷ []) Eq.refl

private
  q183 : Ws → Eqn
  q183 c4 = eqn (Sw01 ∷ Bx1-3042 ∷ []) (Bx0-3142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3042⟩ (lit c4))
  q184 : Ws → Eqn
  q184 c4 = eqn (Bx0-3142 ∷ []) (Bx0-1342 ∷ []) (lem-sym12-at13213442 c4)
  q185 : Ws → Eqn
  q185 c4 = eqn (Sw01 ∷ Bx0-1342 ∷ []) (Bx1-0342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1342⟩ (lit c4))

-- sym12 @0113203442: 5 steps
lem-sym12-at0113203442 : Ws → ⟪ (Bx1-3042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ []) ⟫ʷ
lem-sym12-at0113203442 c4 = derive (Bx1-3042 ∷ []) (Bx1-0342 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q183 c4) ∷
   rw 1 (q184 c4) ∷
   rw 0 (q185 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q186 : Ws → Eqn
  q186 c4 = eqn (Sw12 ∷ Bx2-3041 ∷ []) (Bx1-3042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3041⟩ (lit c4))
  q187 : Ws → Eqn
  q187 c4 = eqn (Bx1-3042 ∷ []) (Bx1-0342 ∷ []) (lem-sym12-at0113203442 c4)
  q188 : Ws → Eqn
  q188 c4 = eqn (Sw12 ∷ Bx1-0342 ∷ []) (Bx2-0341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0342⟩ (lit c4))

-- sym12 @0213203441: 5 steps
lem-sym12-at0213203441 : Ws → ⟪ (Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-sym12-at0213203441 c4 = derive (Bx2-3041 ∷ []) (Bx2-0341 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q186 c4) ∷
   rw 1 (q187 c4) ∷
   rw 0 (q188 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q189 : Ws → Eqn
  q189 c4 = eqn (Sw01 ∷ Bx1-0342 ∷ []) (Bx0-1342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0342⟩ (lit c4))
  q190 : Ws → Eqn
  q190 c4 = eqn (Bx0-1342 ∷ []) (Bx0-1324 ∷ []) (lem-sym34-at233442 c4)
  q191 : Ws → Eqn
  q191 c4 = eqn (Sw01 ∷ Bx0-1324 ∷ []) (Bx1-0324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1324⟩ (lit c4))

-- sym34 @0110233442: 5 steps
lem-sym34-at0110233442 : Ws → ⟪ (Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ []) ⟫ʷ
lem-sym34-at0110233442 c4 = derive (Bx1-0342 ∷ []) (Bx1-0324 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q189 c4) ∷
   rw 1 (q190 c4) ∷
   rw 0 (q191 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q192 : Ws → Eqn
  q192 c4 = eqn (Sw12 ∷ Bx2-0341 ∷ []) (Bx1-0342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0341⟩ (lit c4))
  q193 : Ws → Eqn
  q193 c4 = eqn (Bx1-0342 ∷ []) (Bx1-0324 ∷ []) (lem-sym34-at0110233442 c4)
  q194 : Ws → Eqn
  q194 c4 = eqn (Sw12 ∷ Bx1-0324 ∷ []) (Bx2-0314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0324⟩ (lit c4))

-- sym34 @0210233441: 5 steps
lem-sym34-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-sym34-at0210233441 c4 = derive (Bx2-0341 ∷ []) (Bx2-0314 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q192 c4) ∷
   rw 1 (q193 c4) ∷
   rw 0 (q194 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q195 : Ws → Eqn
  q195 c4 = eqn (Sw01 ∷ Bx1-0324 ∷ []) (Bx0-1324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0324⟩ (lit c4))
  q196 : Ws → Eqn
  q196 c4 = eqn (Sw01 ∷ Bx0-1234 ∷ []) (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4))

-- sym23 @01102332: 5 steps
lem-sym23-at01102332 : Ws → ⟪ (Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ []) ⟫ʷ
lem-sym23-at01102332 c4 = derive (Bx1-0324 ∷ []) (Bx1-0234 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q195 c4) ∷
   rw 1 (q85 c4) ∷
   rw 0 (q196 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q197 : Ws → Eqn
  q197 c4 = eqn (Sw12 ∷ Bx2-0314 ∷ []) (Bx1-0324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0314⟩ (lit c4))
  q198 : Ws → Eqn
  q198 c4 = eqn (Bx1-0324 ∷ []) (Bx1-0234 ∷ []) (lem-sym23-at01102332 c4)
  q199 : Ws → Eqn
  q199 c4 = eqn (Sw12 ∷ Bx1-0234 ∷ []) (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4))

-- sym23 @02102331: 5 steps
lem-sym23-at02102331 : Ws → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-sym23-at02102331 c4 = derive (Bx2-0314 ∷ []) (Bx2-0134 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q197 c4) ∷
   rw 1 (q198 c4) ∷
   rw 0 (q199 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q200 : Ws → Eqn
  q200 c4 = eqn (Sw01 ∷ Bx1-0234 ∷ []) (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4))
  q201 : Ws → Eqn
  q201 c4 = eqn (CS12 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS12 ∷ []) (lem-CS12-beta c4)

-- CS12-beta @0110: 7 steps
lem-CS12-beta-at0110 : Ws → ⟪ (CS02 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CS02 ∷ []) ⟫ʷ
lem-CS12-beta-at0110 c4 = derive (CS02 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CS02 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw⁻ 1 (q113 c4) ∷
   rw 2 (q200 c4) ∷
   rw 1 (q201 c4) ∷
   rw 0 (q196 c4) ∷
   rw⁻ 1 (q115 c4) ∷
   rw 2 (q6 c4) ∷ []) Eq.refl

private
  q202 : Ws → Eqn
  q202 c4 = eqn (Sw12 ∷ Bx2-0134 ∷ []) (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4))
  q203 : Ws → Eqn
  q203 c4 = eqn (CS02 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CS02 ∷ []) (lem-CS12-beta-at0110 c4)

-- CS12-beta @021021: 7 steps
lem-CS12-beta-at021021 : Ws → ⟪ (CS01 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ CS01 ∷ []) ⟫ʷ
lem-CS12-beta-at021021 c4 = derive (CS01 ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ CS01 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q202 c4) ∷
   rw 1 (q203 c4) ∷
   rw 0 (q199 c4) ∷
   rw 1 (q118 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q204 : Ws → Eqn
  q204 c4 = eqn (Bx0-1324 ∷ []) (Bx0-1342 ∷ []) (lem-sym34-at2332 c4)

-- sym34 @01102332: 5 steps
lem-sym34-at01102332 : Ws → ⟪ (Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ []) ⟫ʷ
lem-sym34-at01102332 c4 = derive (Bx1-0324 ∷ []) (Bx1-0342 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q195 c4) ∷
   rw 1 (q204 c4) ∷
   rw 0 (q185 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q205 : Ws → Eqn
  q205 c4 = eqn (Bx1-0324 ∷ []) (Bx1-0342 ∷ []) (lem-sym34-at01102332 c4)

-- sym34 @02102331: 5 steps
lem-sym34-at02102331 : Ws → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-sym34-at02102331 c4 = derive (Bx2-0314 ∷ []) (Bx2-0341 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q197 c4) ∷
   rw 1 (q205 c4) ∷
   rw 0 (q188 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q206 : Ws → Eqn
  q206 c4 = eqn (Bx0-1342 ∷ []) (Bx0-3142 ∷ []) (lem-sym12-at233442 c4)
  q207 : Ws → Eqn
  q207 c4 = eqn (Sw01 ∷ Bx0-3142 ∷ []) (Bx1-3042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3142⟩ (lit c4))

-- sym12 @0110233442: 5 steps
lem-sym12-at0110233442 : Ws → ⟪ (Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3042 ∷ []) ⟫ʷ
lem-sym12-at0110233442 c4 = derive (Bx1-0342 ∷ []) (Bx1-3042 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q189 c4) ∷
   rw 1 (q206 c4) ∷
   rw 0 (q207 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q208 : Ws → Eqn
  q208 c4 = eqn (Bx1-0342 ∷ []) (Bx1-3042 ∷ []) (lem-sym12-at0110233442 c4)
  q209 : Ws → Eqn
  q209 c4 = eqn (Sw12 ∷ Bx1-3042 ∷ []) (Bx2-3041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3042⟩ (lit c4))

-- sym12 @0210233441: 5 steps
lem-sym12-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ []) ⟫ʷ
lem-sym12-at0210233441 c4 = derive (Bx2-0341 ∷ []) (Bx2-3041 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q192 c4) ∷
   rw 1 (q208 c4) ∷
   rw 0 (q209 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q210 : Ws → Eqn
  q210 c4 = eqn (Bx2-3041 ∷ []) (Bx2-0341 ∷ []) (lem-sym12-at0213203441 c4)
  q211 : Ws → Eqn
  q211 c4 = eqn (Bx2-0341 ∷ []) (Bx2-0314 ∷ []) (lem-sym34-at0210233441 c4)
  q212 : Ws → Eqn
  q212 c4 = eqn (Bx2-0314 ∷ []) (Bx2-0134 ∷ []) (lem-sym23-at02102331 c4)
  q213 : Ws → Eqn
  q213 c4 = eqn (CS01 ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ CS01 ∷ []) (lem-CS12-beta-at021021 c4)
  q214 : Ws → Eqn
  q214 c4 = eqn (Bx2-0134 ∷ []) (Bx2-0314 ∷ []) (lem-sym23-at021021 c4)
  q215 : Ws → Eqn
  q215 c4 = eqn (Bx2-0314 ∷ []) (Bx2-0341 ∷ []) (lem-sym34-at02102331 c4)
  q216 : Ws → Eqn
  q216 c4 = eqn (Bx2-0341 ∷ []) (Bx2-3041 ∷ []) (lem-sym12-at0210233441 c4)

-- auto CS01 | BOX(2;3041): 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩ : Ws → ⟪ (CS01 ∷ Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩ c4 = derive (CS01 ∷ Bx2-3041 ∷ []) (Bx2-3041 ∷ CS01 ∷ [])
  (rw 1 (q210 c4) ∷
   rw 1 (q211 c4) ∷
   rw 1 (q212 c4) ∷
   rw 0 (q213 c4) ∷
   rw 0 (q214 c4) ∷
   rw 0 (q215 c4) ∷
   rw 0 (q216 c4) ∷ []) Eq.refl

private
  q217 : Ws → Eqn
  q217 c4 = eqn (CS01 ∷ Bx2-3041 ∷ []) (Bx2-3041 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩ c4)
  q218 : Ws → Eqn
  q218 c4 = eqn (CS01 ∷ Toff104 ∷ CS13 ∷ Toff104 ∷ []) (Toff104 ∷ CS13 ∷ Toff104 ∷ CS01 ∷ []) (wp0091 c4)
  q219 : Ws → Eqn
  q219 c4 = eqn (CS01 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS01 ∷ []) (wl0289 (lit c4))

-- auto CS01 | SBOX(2;3;04;1): 9 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩ : Ws → ⟪ (CS01 ∷ Sb2-3-04-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-04-1 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩ c4 = derive (CS01 ∷ Sb2-3-04-1 ∷ []) (Sb2-3-04-1 ∷ CS01 ∷ [])
  (re 1 1 (Bx2-3041 ∷ Toff104 ∷ Sb2-3-1-4 ∷ Toff104 ∷ Sb⁻2-3-1-4 ∷ []) ∷
   rw 0 (q217 c4) ∷
   re 3 1 (CS13 ∷ []) ∷
   rw 1 (q218 c4) ∷
   re 2 1 (Sb2-3-1-4 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 4 (q219 c4) ∷
   re 4 1 (Sb⁻2-3-1-4 ∷ []) ∷
   re 0 5 (Sb2-3-04-1 ∷ []) ∷ []) Eq.refl

private
  q220 : Ws → Eqn
  q220 c4 = eqn (K0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0 ∷ []) (lem-K0-pass-c c4)

-- auto K0 | BOX(0;1234): 1 steps
lem-auto-K0-∣-BOX⟨0·1234⟩ : Ws → ⟪ (K0 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ K0 ∷ []) ⟫ʷ
lem-auto-K0-∣-BOX⟨0·1234⟩ c4 = derive (K0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0 ∷ [])
  (rw 0 (q220 c4) ∷ []) Eq.refl

private
  q221 : Ws → Eqn
  q221 c4 = eqn (K0 ∷ Sw34 ∷ []) (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑))
  q222 : Ws → Eqn
  q222 c4 = eqn (K0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩ c4)

-- auto K0 | BOX(0;1234) @3443: 7 steps
lem-auto-K0-∣-BOX⟨0·1234⟩-at3443 : Ws → ⟪ (K0 ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ K0 ∷ []) ⟫ʷ
lem-auto-K0-∣-BOX⟨0·1234⟩-at3443 c4 = derive (K0 ∷ Bx0-1243 ∷ []) (Bx0-1243 ∷ K0 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q221 c4) ∷
   rw 2 (q165 c4) ∷
   rw 1 (q222 c4) ∷
   rw 0 (q167 c4) ∷
   rw⁻ 1 (q221 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q223 : Ws → Eqn
  q223 c4 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (c₁ (K) (Swap ↑))
  q224 : Ws → Eqn
  q224 c4 = eqn (K0 ∷ Bx0-1243 ∷ []) (Bx0-1243 ∷ K0 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩-at3443 c4)

-- auto K0 | BOX(0;1234) @233442: 7 steps
lem-auto-K0-∣-BOX⟨0·1234⟩-at233442 : Ws → ⟪ (K0 ∷ Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ K0 ∷ []) ⟫ʷ
lem-auto-K0-∣-BOX⟨0·1234⟩-at233442 c4 = derive (K0 ∷ Bx0-1342 ∷ []) (Bx0-1342 ∷ K0 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw⁻ 1 (q223 c4) ∷
   rw 2 (q169 c4) ∷
   rw 1 (q224 c4) ∷
   rw 0 (q171 c4) ∷
   rw⁻ 1 (q223 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q225 : Ws → Eqn
  q225 c4 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap))
  q226 : Ws → Eqn
  q226 c4 = eqn (K0 ∷ Bx0-1342 ∷ []) (Bx0-1342 ∷ K0 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩-at233442 c4)

-- auto K0 | BOX(0;1234) @12233441: 7 steps
lem-auto-K0-∣-BOX⟨0·1234⟩-at12233441 : Ws → ⟪ (K0 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ K0 ∷ []) ⟫ʷ
lem-auto-K0-∣-BOX⟨0·1234⟩-at12233441 c4 = derive (K0 ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ K0 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw⁻ 1 (q225 c4) ∷
   rw 2 (q173 c4) ∷
   rw 1 (q226 c4) ∷
   rw 0 (q175 c4) ∷
   rw⁻ 1 (q225 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q227 : Ws → Eqn
  q227 c4 = eqn (K0 ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ K0 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩-at12233441 c4)
  q228 : Ws → Eqn
  q228 c4 = eqn (K0 ∷ Toff134 ∷ []) (Toff134 ∷ K0 ∷ []) (wp0092 c4)
  q229 : Ws → Eqn
  q229 c4 = eqn (CS12 ∷ K0 ∷ []) (K0 ∷ CS12 ∷ []) (wl0290 (lit c4))
  q230 : Ws → Eqn
  q230 c4 = eqn (CS12⁻ ∷ K0 ∷ []) (K0 ∷ CS12⁻ ∷ []) (wl0291 (lit c4))

-- auto K0 | SBOX(1;2;34;0): 13 steps
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩ : Ws → ⟪ (K0 ∷ Sb1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-34-0 ∷ K0 ∷ []) ⟫ʷ
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩ c4 = derive (K0 ∷ Sb1-2-34-0 ∷ []) (Sb1-2-34-0 ∷ K0 ∷ [])
  (rw 1 (q176 c4) ∷
   re 1 1 (Bx0-2341 ∷ Toff134 ∷ Sb0-2-1-4 ∷ Toff134 ∷ Sb⁻0-2-1-4 ∷ []) ∷
   rw 0 (q227 c4) ∷
   rw 1 (q228 c4) ∷
   re 3 1 (CS12 ∷ []) ∷
   rw⁻ 2 (q229 c4) ∷
   re 2 1 (Sb0-2-1-4 ∷ []) ∷
   rw 3 (q228 c4) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw⁻ 4 (q230 c4) ∷
   re 4 1 (Sb⁻0-2-1-4 ∷ []) ∷
   re 0 5 (Sb0-2-34-1 ∷ []) ∷
   rw⁻ 0 (q176 c4) ∷ []) Eq.refl

private
  q231 : Ws → Eqn
  q231 c4 = eqn (CS12 ∷ Toff014 ∷ []) (Toff014 ∷ CS12 ∷ []) (wp0093 c4)
  q232 : Ws → Eqn
  q232 c4 = eqn (CCZ023 ∷ CS12 ∷ []) (CS12 ∷ CCZ023 ∷ []) (wl0292 (lit c4))

-- auto SBOX(0;1;2;3) | BOX(0;1432): 14 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ : Ws → ⟪ (Sb0-1-2-3 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ c4 = derive (Sb0-1-2-3 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ Sb0-1-2-3 ∷ [])
  (rw 1 (q140 c4) ∷
   re 0 1 (CS12 ∷ []) ∷
   rw 0 (q231 c4) ∷
   re 1 1 (Sb0-1-2-3 ∷ []) ∷
   re 1 1 (CS12 ∷ []) ∷
   rw⁻ 1 (q232 c4) ∷
   re 2 1 (Sb0-1-2-3 ∷ []) ∷
   re 2 1 (CS12 ∷ []) ∷
   rw 2 (q231 c4) ∷
   re 3 1 (Sb0-1-2-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   rw⁻ 3 (q232 c4) ∷
   re 4 1 (Sb0-1-2-3 ∷ []) ∷
   rw⁻ 0 (q140 c4) ∷ []) Eq.refl

private
  q233 : Ws → Eqn
  q233 c4 = eqn (Sb0-1-2-3 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ c4)
  q234 : Ws → Eqn
  q234 c4 = eqn (CS12 ∷ Toff234 ∷ CS12 ∷ Toff234 ∷ []) (Toff234 ∷ CS12 ∷ Toff234 ∷ CS12 ∷ []) (wl0293 (lit c4))
  q235 : Ws → Eqn
  q235 c4 = eqn (CS12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS12 ∷ []) (wl0294 (lit c4))

-- auto SBOX(0;1;2;3) | SBOX(0;1;43;2): 13 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩ : Ws → ⟪ (Sb0-1-2-3 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩ c4 = derive (Sb0-1-2-3 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ Sb0-1-2-3 ∷ [])
  (re 1 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) ∷
   rw 0 (q233 c4) ∷
   re 1 1 (CS12 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   rw 1 (q234 c4) ∷
   re 2 1 (Sb0-1-2-3 ∷ []) ∷
   re 4 1 (Sb0-1-2-3 ∷ []) ∷
   re 4 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw 4 (q235 c4) ∷
   re 4 1 (Sb⁻0-1-2-3 ∷ []) ∷
   re 5 1 (Sb0-1-2-3 ∷ []) ∷
   re 0 5 (Sb0-1-43-2 ∷ []) ∷ []) Eq.refl

private
  q236 : Ws → Eqn
  q236 c4 = eqn (Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T c4)
  q237 : Ws → Eqn
  q237 c4 = eqn (Bx0-1234 ∷ Toff012 ∷ []) (Toff012 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012 c4)
  q238 : Ws → Eqn
  q238 c4 = eqn (Bx0-1234 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ034 c4)

-- auto BOX(0;1234) | BOX(0;1234): 6 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·1234⟩ : Ws → ⟪ (Bx0-1234 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·1234⟩ c4 = derive (Bx0-1234 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Bx0-1234 ∷ [])
  (rw 1 (q236 c4) ∷
   rw 0 (q237 c4) ∷
   rw 1 (q238 c4) ∷
   rw 2 (q237 c4) ∷
   rw 3 (q238 c4) ∷
   rw⁻ 0 (q236 c4) ∷ []) Eq.refl

private
  q239 : Ws → Eqn
  q239 c4 = eqn (Bx0-1234 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14 c4)

-- auto BOX(0;1234) | SBOX(0;1;4;3): 3 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·4·3⟩ : Ws → ⟪ (Bx0-1234 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-3 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·4·3⟩ c4 = derive (Bx0-1234 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-3 ∷ Bx0-1234 ∷ [])
  (re 1 1 (CS14 ∷ []) ∷
   rw 0 (q239 c4) ∷
   re 0 1 (Sb0-1-4-3 ∷ []) ∷ []) Eq.refl

private
  q240 : Ws → Eqn
  q240 c4 = eqn (Bx0-1234 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14 c4)

-- auto BOX(0;1234) | SBOXd(0;1;4;3): 3 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOXd⟨0·1·4·3⟩ : Ws → ⟪ (Bx0-1234 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-3 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOXd⟨0·1·4·3⟩ c4 = derive (Bx0-1234 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-3 ∷ Bx0-1234 ∷ [])
  (re 1 1 (CS14⁻ ∷ []) ∷
   rw 0 (q240 c4) ∷
   re 0 1 (Sb⁻0-1-4-3 ∷ []) ∷ []) Eq.refl

private
  q241 : Ws → Eqn
  q241 c4 = eqn (CCZ123 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ123 ∷ []) (wl0295 (lit c4))
  q242 : Ws → Eqn
  q242 c4 = eqn (Bx0-1234 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231 c4)

-- auto BOX(0;1234) TOFF423 | CCZ231: 2 steps
lem-auto-BOX⟨0·1234⟩-TOFF423-∣-CCZ231 : Ws → ⟪ (Bx0-1234 ∷ Toff423 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1234 ∷ Toff423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-TOFF423-∣-CCZ231 c4 = derive (Bx0-1234 ∷ Toff423 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1234 ∷ Toff423 ∷ [])
  (rw⁻ 1 (q241 c4) ∷
   rw 0 (q242 c4) ∷ []) Eq.refl

private
  q243 : Ws → Eqn
  q243 c4 = eqn (Sw34 ∷ Toff412 ∷ []) (Toff312 ∷ Sw34 ∷ []) (lem-nat-3-TOFF412 (lit c4))
  q244 : Ws → Eqn
  q244 c4 = eqn (Toff312 ∷ Bx0-1234 ∷ Toff312 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ []) (lem-T312-beta c4)

-- T312-beta @3443: 8 steps
lem-T312-beta-at3443 : Ws → ⟪ (Toff412 ∷ Bx0-1243 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ CCZ123 ∷ []) ⟫ʷ
lem-T312-beta-at3443 c4 = derive (Toff412 ∷ Bx0-1243 ∷ Toff412 ∷ []) (Bx0-1243 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q243 c4) ∷
   rw 2 (q165 c4) ∷
   rw 3 (q243 c4) ∷
   rw 1 (q244 c4) ∷
   rw 0 (q167 c4) ∷
   rw 1 (q98 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q245 : Ws → Eqn
  q245 c4 = eqn (Sw23 ∷ Toff413 ∷ []) (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 (lit c4))
  q246 : Ws → Eqn
  q246 c4 = eqn (Toff412 ∷ Bx0-1243 ∷ Toff412 ∷ []) (Bx0-1243 ∷ CCZ123 ∷ []) (lem-T312-beta-at3443 c4)
  q247 : Ws → Eqn
  q247 c4 = eqn (CCZ123 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ123 ∷ []) (wl0113 (lit c4))

-- T312-beta @233442: 8 steps
lem-T312-beta-at233442 : Ws → ⟪ (Toff413 ∷ Bx0-1342 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ CCZ123 ∷ []) ⟫ʷ
lem-T312-beta-at233442 c4 = derive (Toff413 ∷ Bx0-1342 ∷ Toff413 ∷ []) (Bx0-1342 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q245 c4) ∷
   rw 2 (q169 c4) ∷
   rw 3 (q245 c4) ∷
   rw 1 (q246 c4) ∷
   rw 0 (q171 c4) ∷
   rw⁻ 1 (q247 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q248 : Ws → Eqn
  q248 c4 = eqn (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) (wl0091 (lit c4))
  q249 : Ws → Eqn
  q249 c4 = eqn (Toff413 ∷ Bx0-1342 ∷ Toff413 ∷ []) (Bx0-1342 ∷ CCZ123 ∷ []) (lem-T312-beta-at233442 c4)
  q250 : Ws → Eqn
  q250 c4 = eqn (CCZ123 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ123 ∷ []) (wl0111 (lit c4))

-- T312-beta @12233441: 8 steps
lem-T312-beta-at12233441 : Ws → ⟪ (Toff423 ∷ Bx0-2341 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ CCZ123 ∷ []) ⟫ʷ
lem-T312-beta-at12233441 c4 = derive (Toff423 ∷ Bx0-2341 ∷ Toff423 ∷ []) (Bx0-2341 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q248 c4) ∷
   rw 2 (q173 c4) ∷
   rw 3 (q248 c4) ∷
   rw 1 (q249 c4) ∷
   rw 0 (q175 c4) ∷
   rw⁻ 1 (q250 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q251 : Ws → Eqn
  q251 c4 = eqn (Bx0-1234 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·1234⟩ c4)
  q252 : Ws → Eqn
  q252 c4 = eqn (Toff423 ∷ Toff423 ∷ []) [] (wl0296 (lit c4))
  q253 : Ws → Eqn
  q253 c4 = eqn (Bx0-1234 ∷ []) (Bx0-2134 ∷ []) (lem-sym12 c4)
  q254 : Ws → Eqn
  q254 c4 = eqn (Bx0-2134 ∷ []) (Bx0-2314 ∷ []) (lem-sym23-at1221 c4)
  q255 : Ws → Eqn
  q255 c4 = eqn (Bx0-2314 ∷ []) (Bx0-2341 ∷ []) (lem-sym34-at122331 c4)
  q256 : Ws → Eqn
  q256 c4 = eqn (Toff423 ∷ Bx0-2341 ∷ Toff423 ∷ []) (Bx0-2341 ∷ CCZ123 ∷ []) (lem-T312-beta-at12233441 c4)
  q257 : Ws → Eqn
  q257 c4 = eqn (Bx0-2341 ∷ []) (Bx0-2314 ∷ []) (lem-sym34-at12233441 c4)
  q258 : Ws → Eqn
  q258 c4 = eqn (Bx0-2314 ∷ []) (Bx0-2134 ∷ []) (lem-sym23-at122331 c4)
  q259 : Ws → Eqn
  q259 c4 = eqn (Bx0-2134 ∷ []) (Bx0-1234 ∷ []) (lem-sym12-at1221 c4)
  q260 : Ws → Eqn
  q260 c4 = eqn (Bx0-1234 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-3 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·4·3⟩ c4)
  q261 : Ws → Eqn
  q261 c4 = eqn (Bx0-1234 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-3 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOXd⟨0·1·4·3⟩ c4)
  q262 : Ws → Eqn
  q262 c4 = eqn (Bx0-1234 ∷ Toff423 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1234 ∷ Toff423 ∷ []) (lem-auto-BOX⟨0·1234⟩-TOFF423-∣-CCZ231 c4)
  q263 : Ws → Eqn
  q263 c4 = eqn (CCZ123 ∷ CS14 ∷ []) (CS14 ∷ CCZ123 ∷ []) (wl0297 (lit c4))
  q264 : Ws → Eqn
  q264 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl0212 (lit c4))

-- auto BOX(0;1234) | SBOX(0;1;23;4): 31 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩ : Ws → ⟪ (Bx0-1234 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩ c4 = derive (Bx0-1234 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-23-4 ∷ Bx0-1234 ∷ [])
  (re 1 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   rw 0 (q251 c4) ∷
   rw⁻ 1 (q252 c4) ∷
   rw 3 (q253 c4) ∷
   rw 3 (q254 c4) ∷
   rw 3 (q255 c4) ∷
   rw 2 (q256 c4) ∷
   rw 2 (q257 c4) ∷
   rw 2 (q258 c4) ∷
   rw 2 (q259 c4) ∷
   rw 2 (q242 c4) ∷
   rw 3 (q260 c4) ∷
   rw⁻ 4 (q252 c4) ∷
   rw 6 (q253 c4) ∷
   rw 6 (q254 c4) ∷
   rw 6 (q255 c4) ∷
   rw 5 (q256 c4) ∷
   rw 5 (q257 c4) ∷
   rw 5 (q258 c4) ∷
   rw 5 (q259 c4) ∷
   rw 5 (q242 c4) ∷
   rw 6 (q261 c4) ∷
   rw 0 (q262 c4) ∷
   rw⁻ 4 (q241 c4) ∷
   re 3 1 (CS14 ∷ []) ∷
   rw⁻ 3 (q263 c4) ∷
   re 4 1 (Sb0-1-4-3 ∷ []) ∷
   rw⁻ 2 (q241 c4) ∷
   rw 1 (q242 c4) ∷
   rw 0 (q264 c4) ∷
   re 0 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q265 : Ws → Eqn
  q265 c4 = eqn (CS14 ∷ []) (CS14 ∷ []) (wl0298 (lit c4))
  q266 : Ws → Eqn
  q266 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1243 ∷ []) (lem-sym34 c4)
  q267 : Ws → Eqn
  q267 c4 = eqn (Bx0-1243 ∷ []) (Bx0-1423 ∷ []) (lem-sym23-at3443 c4)
  q268 : Ws → Eqn
  q268 c4 = eqn (CS14 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS14 ∷ []) (lem-CS12-beta-at243243 c4)
  q269 : Ws → Eqn
  q269 c4 = eqn (Bx0-1423 ∷ []) (Bx0-1243 ∷ []) (lem-sym23-at243243 c4)
  q270 : Ws → Eqn
  q270 c4 = eqn (Bx0-1243 ∷ []) (Bx0-1234 ∷ []) (lem-sym34-at3443 c4)

-- auto BOX(0;1234) | CS41: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS41 : Ws → ⟪ (Bx0-1234 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS41 c4 = derive (Bx0-1234 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1234 ∷ [])
  (rw 1 (q265 c4) ∷
   rw 0 (q266 c4) ∷
   rw 0 (q267 c4) ∷
   rw⁻ 0 (q268 c4) ∷
   rw 1 (q269 c4) ∷
   rw 1 (q270 c4) ∷
   rw 0 (q265 c4) ∷ []) Eq.refl

private
  q271 : Ws → Eqn
  q271 c4 = eqn (CS14 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS14 ∷ []) (wl0299 (lit c4))
  q272 : Ws → Eqn
  q272 c4 = eqn (CS14 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14 ∷ []) (wl0300 (lit c4))
  q273 : Ws → Eqn
  q273 c4 = eqn (Bx0-1234 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS41 c4)

-- auto SBOX(0;1;23;4) | CS41: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41 : Ws → ⟪ (Sb0-1-23-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41 c4 = derive (Sb0-1-23-4 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q271 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw⁻ 1 (q272 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw 0 (q273 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

-- auto BOX(0;1234) | K0: 1 steps
lem-auto-BOX⟨0·1234⟩-∣-K0 : Ws → ⟪ (Bx0-1234 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0 c4 = derive (Bx0-1234 ∷ K0 ∷ []) (K0 ∷ Bx0-1234 ∷ [])
  (rw⁻ 0 (q220 c4) ∷ []) Eq.refl

private
  q274 : Ws → Eqn
  q274 c4 = eqn (Sw34 ∷ Sb2-0-31-4 ∷ []) (Sb2-0-41-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·31·4⟩ (lit c4))
  q275 : Ws → Eqn
  q275 c4 = eqn (Sw34 ∷ Sb3-0-41-2 ∷ []) (Sb4-0-31-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨3·0·41·2⟩ (lit c4))

-- F0 @3443: 5 steps
lem-F0-at3443 : Ws → ⟪ (Sb2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-31-2 ∷ []) ⟫ʷ
lem-F0-at3443 c4 = derive (Sb2-0-31-4 ∷ []) (Sb4-0-31-2 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q274 c4) ∷
   rw 1 (q148 c4) ∷
   rw 0 (q275 c4) ∷
   rw 1 (q1 c4) ∷ []) Eq.refl

private
  q276 : Ws → Eqn
  q276 c4 = eqn (Sw12 ∷ Sb1-0-32-4 ∷ []) (Sb2-0-31-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·32·4⟩ (lit c4))
  q277 : Ws → Eqn
  q277 c4 = eqn (Sb2-0-31-4 ∷ []) (Sb4-0-31-2 ∷ []) (lem-F0-at3443 c4)
  q278 : Ws → Eqn
  q278 c4 = eqn (Sw12 ∷ Sb4-0-31-2 ∷ []) (Sb4-0-32-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨4·0·31·2⟩ (lit c4))

-- F0 @12213443: 5 steps
lem-F0-at12213443 : Ws → ⟪ (Sb1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-32-1 ∷ []) ⟫ʷ
lem-F0-at12213443 c4 = derive (Sb1-0-32-4 ∷ []) (Sb4-0-32-1 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q276 c4) ∷
   rw 1 (q277 c4) ∷
   rw 0 (q278 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q279 : Ws → Eqn
  q279 c4 = eqn (Sw23 ∷ Sb1-0-23-4 ∷ []) (Sb1-0-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·23·4⟩ (lit c4))
  q280 : Ws → Eqn
  q280 c4 = eqn (Sb1-0-32-4 ∷ []) (Sb4-0-32-1 ∷ []) (lem-F0-at12213443 c4)
  q281 : Ws → Eqn
  q281 c4 = eqn (Sw23 ∷ Sb4-0-32-1 ∷ []) (Sb4-0-23-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·0·32·1⟩ (lit c4))

-- F0 @13213442: 5 steps
lem-F0-at13213442 : Ws → ⟪ (Sb1-0-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-23-1 ∷ []) ⟫ʷ
lem-F0-at13213442 c4 = derive (Sb1-0-23-4 ∷ []) (Sb4-0-23-1 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q279 c4) ∷
   rw 1 (q280 c4) ∷
   rw 0 (q281 c4) ∷
   rw 1 (q17 c4) ∷ []) Eq.refl

private
  q282 : Ws → Eqn
  q282 c4 = eqn (Sw01 ∷ Sb0-1-23-4 ∷ []) (Sb1-0-23-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·23·4⟩ (lit c4))
  q283 : Ws → Eqn
  q283 c4 = eqn (Sb1-0-23-4 ∷ []) (Sb4-0-23-1 ∷ []) (lem-F0-at13213442 c4)
  q284 : Ws → Eqn
  q284 c4 = eqn (Sw01 ∷ Sb4-0-23-1 ∷ []) (Sb4-1-23-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨4·0·23·1⟩ (lit c4))

-- F0 @0113203442: 5 steps
lem-F0-at0113203442 : Ws → ⟪ (Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-23-0 ∷ []) ⟫ʷ
lem-F0-at0113203442 c4 = derive (Sb0-1-23-4 ∷ []) (Sb4-1-23-0 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q282 c4) ∷
   rw 1 (q283 c4) ∷
   rw 0 (q284 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q285 : Ws → Eqn
  q285 c4 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wl0031 (lit c4))
  q286 : Ws → Eqn
  q286 c4 = eqn (Bx0-1234 ∷ K0 ∷ []) (K0 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0 c4)
  q287 : Ws → Eqn
  q287 c4 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wl0076 (lit c4))

-- auto BOX(0;1234) | K0 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at0110 : Ws → ⟪ (Bx1-0234 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at0110 c4 = derive (Bx1-0234 ∷ K1 ∷ []) (K1 ∷ Bx1-0234 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q200 c4) ∷
   rw⁻ 2 (q285 c4) ∷
   rw 1 (q286 c4) ∷
   rw⁻ 0 (q287 c4) ∷
   rw 1 (q196 c4) ∷
   rw 2 (q6 c4) ∷ []) Eq.refl

private
  q288 : Ws → Eqn
  q288 c4 = eqn (K1 ∷ Sw12 ∷ []) (Sw12 ∷ K2 ∷ []) (wl0062 (lit c4))
  q289 : Ws → Eqn
  q289 c4 = eqn (Bx1-0234 ∷ K1 ∷ []) (K1 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at0110 c4)
  q290 : Ws → Eqn
  q290 c4 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wl0056 (lit c4))

-- auto BOX(0;1234) | K0 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at021021 : Ws → ⟪ (Bx2-0134 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at021021 c4 = derive (Bx2-0134 ∷ K2 ∷ []) (K2 ∷ Bx2-0134 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q202 c4) ∷
   rw⁻ 2 (q288 c4) ∷
   rw 1 (q289 c4) ∷
   rw⁻ 0 (q290 c4) ∷
   rw 1 (q199 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q291 : Ws → Eqn
  q291 c4 = eqn (Sw23 ∷ Bx3-0124 ∷ []) (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ (lit c4))
  q292 : Ws → Eqn
  q292 c4 = eqn (K2 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ []) (wl0058 (lit c4))
  q293 : Ws → Eqn
  q293 c4 = eqn (Bx2-0134 ∷ K2 ∷ []) (K2 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at021021 c4)
  q294 : Ws → Eqn
  q294 c4 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wl0057 (lit c4))
  q295 : Ws → Eqn
  q295 c4 = eqn (Sw23 ∷ Bx2-0134 ∷ []) (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ (lit c4))

-- auto BOX(0;1234) | K0 @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at03102132 : Ws → ⟪ (Bx3-0124 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at03102132 c4 = derive (Bx3-0124 ∷ K3 ∷ []) (K3 ∷ Bx3-0124 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q291 c4) ∷
   rw⁻ 2 (q292 c4) ∷
   rw 1 (q293 c4) ∷
   rw⁻ 0 (q294 c4) ∷
   rw 1 (q295 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q296 : Ws → Eqn
  q296 c4 = eqn (Sw34 ∷ Bx4-0123 ∷ []) (Bx3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0123⟩ (lit c4))
  q297 : Ws → Eqn
  q297 c4 = eqn (K3 ∷ Sw34 ∷ []) (Sw34 ∷ K4 ∷ []) (wl0068 (lit c4))
  q298 : Ws → Eqn
  q298 c4 = eqn (Bx3-0124 ∷ K3 ∷ []) (K3 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at03102132 c4)
  q299 : Ws → Eqn
  q299 c4 = eqn (K4 ∷ Sw34 ∷ []) (Sw34 ∷ K3 ∷ []) (wl0067 (lit c4))
  q300 : Ws → Eqn
  q300 c4 = eqn (Sw34 ∷ Bx3-0124 ∷ []) (Bx4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0124⟩ (lit c4))

-- auto BOX(0;1234) | K0 @0410213243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx4-0123 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at0410213243 c4 = derive (Bx4-0123 ∷ K4 ∷ []) (K4 ∷ Bx4-0123 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q296 c4) ∷
   rw⁻ 2 (q297 c4) ∷
   rw 1 (q298 c4) ∷
   rw⁻ 0 (q299 c4) ∷
   rw 1 (q300 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q301 : Ws → Eqn
  q301 c4 = eqn (Sw23 ∷ Bx4-0132 ∷ []) (Bx4-0123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0132⟩ (lit c4))
  q302 : Ws → Eqn
  q302 c4 = eqn (Sw23 ∷ K4 ∷ []) (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K))
  q303 : Ws → Eqn
  q303 c4 = eqn (Bx4-0123 ∷ K4 ∷ []) (K4 ∷ Bx4-0123 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at0410213243 c4)
  q304 : Ws → Eqn
  q304 c4 = eqn (Sw23 ∷ Bx4-0123 ∷ []) (Bx4-0132 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0123⟩ (lit c4))

-- auto BOX(0;1234) | K0 @04102142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at04102142 : Ws → ⟪ (Bx4-0132 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx4-0132 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at04102142 c4 = derive (Bx4-0132 ∷ K4 ∷ []) (K4 ∷ Bx4-0132 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q301 c4) ∷
   rw 2 (q302 c4) ∷
   rw 1 (q303 c4) ∷
   rw 0 (q302 c4) ∷
   rw 1 (q304 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q305 : Ws → Eqn
  q305 c4 = eqn (Sw12 ∷ Bx4-0231 ∷ []) (Bx4-0132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0231⟩ (lit c4))
  q306 : Ws → Eqn
  q306 c4 = eqn (Sw12 ∷ K4 ∷ []) (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑))
  q307 : Ws → Eqn
  q307 c4 = eqn (Bx4-0132 ∷ K4 ∷ []) (K4 ∷ Bx4-0132 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at04102142 c4)
  q308 : Ws → Eqn
  q308 c4 = eqn (Sw12 ∷ Bx4-0132 ∷ []) (Bx4-0231 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0132⟩ (lit c4))

-- auto BOX(0;1234) | K0 @041041: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at041041 : Ws → ⟪ (Bx4-0231 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx4-0231 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at041041 c4 = derive (Bx4-0231 ∷ K4 ∷ []) (K4 ∷ Bx4-0231 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q305 c4) ∷
   rw 2 (q306 c4) ∷
   rw 1 (q307 c4) ∷
   rw 0 (q306 c4) ∷
   rw 1 (q308 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q309 : Ws → Eqn
  q309 c4 = eqn (Sw01 ∷ Bx4-1230 ∷ []) (Bx4-0231 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1230⟩ (lit c4))
  q310 : Ws → Eqn
  q310 c4 = eqn (Sw01 ∷ K4 ∷ []) (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑))
  q311 : Ws → Eqn
  q311 c4 = eqn (Bx4-0231 ∷ K4 ∷ []) (K4 ∷ Bx4-0231 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at041041 c4)
  q312 : Ws → Eqn
  q312 c4 = eqn (Sw01 ∷ Bx4-0231 ∷ []) (Bx4-1230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0231⟩ (lit c4))

-- auto BOX(0;1234) | K0 @0440: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at0440 : Ws → ⟪ (Bx4-1230 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx4-1230 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at0440 c4 = derive (Bx4-1230 ∷ K4 ∷ []) (K4 ∷ Bx4-1230 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q309 c4) ∷
   rw 2 (q310 c4) ∷
   rw 1 (q311 c4) ∷
   rw 0 (q310 c4) ∷
   rw 1 (q312 c4) ∷
   rw 2 (q6 c4) ∷ []) Eq.refl

private
  q313 : Ws → Eqn
  q313 c4 = eqn (Sb0-1-23-4 ∷ []) (Sb4-1-23-0 ∷ []) (lem-F0-at0113203442 c4)
  q314 : Ws → Eqn
  q314 c4 = eqn (CS01⁻ ∷ K4 ∷ []) (K4 ∷ CS01⁻ ∷ []) (wl0301 (lit c4))
  q315 : Ws → Eqn
  q315 c4 = eqn (K4 ∷ Toff023 ∷ []) (Toff023 ∷ K4 ∷ []) (wp0094 c4)
  q316 : Ws → Eqn
  q316 c4 = eqn (CS01 ∷ K4 ∷ []) (K4 ∷ CS01 ∷ []) (wl0302 (lit c4))
  q317 : Ws → Eqn
  q317 c4 = eqn (Bx4-1230 ∷ K4 ∷ []) (K4 ∷ Bx4-1230 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at0440 c4)

-- auto SBOX(0;1;23;4) | K4: 13 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4 : Ws → ⟪ (Sb0-1-23-4 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4 c4 = derive (Sb0-1-23-4 ∷ K4 ∷ []) (K4 ∷ Sb0-1-23-4 ∷ [])
  (rw 0 (q313 c4) ∷
   re 0 1 (Bx4-1230 ∷ Toff023 ∷ Sb4-1-0-3 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ []) ∷
   re 4 1 (CS01⁻ ∷ []) ∷
   rw 4 (q314 c4) ∷
   re 5 1 (Sb⁻4-1-0-3 ∷ []) ∷
   rw⁻ 3 (q315 c4) ∷
   re 2 1 (CS01 ∷ []) ∷
   rw 2 (q316 c4) ∷
   re 3 1 (Sb4-1-0-3 ∷ []) ∷
   rw⁻ 1 (q315 c4) ∷
   rw 0 (q317 c4) ∷
   re 1 5 (Sb4-1-23-0 ∷ []) ∷
   rw⁻ 1 (q313 c4) ∷ []) Eq.refl

private
  q318 : Ws → Eqn
  q318 c4 = eqn (Sw12 ∷ Bx0-2413 ∷ []) (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4))
  q319 : Ws → Eqn
  q319 c4 = eqn (Sw12 ∷ Bx0-1423 ∷ []) (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4))

-- CS12-beta @12243143: 7 steps
lem-CS12-beta-at12243143 : Ws → ⟪ (CS24 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ CS24 ∷ []) ⟫ʷ
lem-CS12-beta-at12243143 c4 = derive (CS24 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ CS24 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw⁻ 1 (q29 c4) ∷
   rw 2 (q318 c4) ∷
   rw 1 (q268 c4) ∷
   rw 0 (q319 c4) ∷
   rw⁻ 1 (q27 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q320 : Ws → Eqn
  q320 c4 = eqn (Bx0-2134 ∷ []) (Bx0-2143 ∷ []) (lem-sym34-at1221 c4)
  q321 : Ws → Eqn
  q321 c4 = eqn (Bx0-2143 ∷ []) (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4)
  q322 : Ws → Eqn
  q322 c4 = eqn (CS24 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ CS24 ∷ []) (lem-CS12-beta-at12243143 c4)
  q323 : Ws → Eqn
  q323 c4 = eqn (Bx0-2413 ∷ []) (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4)
  q324 : Ws → Eqn
  q324 c4 = eqn (Bx0-2143 ∷ []) (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4)

-- auto BOX(0;1234) | CS24: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS24 : Ws → ⟪ (Bx0-1234 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS24 c4 = derive (Bx0-1234 ∷ CS24 ∷ []) (CS24 ∷ Bx0-1234 ∷ [])
  (rw 0 (q253 c4) ∷
   rw 0 (q320 c4) ∷
   rw 0 (q321 c4) ∷
   rw⁻ 0 (q322 c4) ∷
   rw 1 (q323 c4) ∷
   rw 1 (q324 c4) ∷
   rw 1 (q259 c4) ∷ []) Eq.refl

private
  q325 : Ws → Eqn
  q325 c4 = eqn (CS14⁻ ∷ CS24 ∷ []) (CS24 ∷ CS14⁻ ∷ []) (wl0303 (lit c4))
  q326 : Ws → Eqn
  q326 c4 = eqn (CS24 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS24 ∷ []) (wl0304 (lit c4))
  q327 : Ws → Eqn
  q327 c4 = eqn (Bx0-1234 ∷ CS24 ∷ []) (CS24 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS24 c4)

-- auto SBOX(0;1;23;4) | CS24: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24 : Ws → ⟪ (Sb0-1-23-4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24 c4 = derive (Sb0-1-23-4 ∷ CS24 ∷ []) (CS24 ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw 4 (q325 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw⁻ 1 (q326 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw 0 (q327 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q328 : Ws → Eqn
  q328 c4 = eqn (Sb2-0-41-3 ∷ []) (Sb2-0-14-3 ∷ []) (lem-SBsym c4)
  q329 : Ws → Eqn
  q329 c4 = eqn (Sw34 ∷ Sb2-0-14-3 ∷ []) (Sb2-0-13-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·14·3⟩ (lit c4))

-- SBsym @3443: 5 steps
lem-SBsym-at3443 : Ws → ⟪ (Sb2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-13-4 ∷ []) ⟫ʷ
lem-SBsym-at3443 c4 = derive (Sb2-0-31-4 ∷ []) (Sb2-0-13-4 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q274 c4) ∷
   rw 1 (q328 c4) ∷
   rw 0 (q329 c4) ∷
   rw 1 (q1 c4) ∷ []) Eq.refl

private
  q330 : Ws → Eqn
  q330 c4 = eqn (Sb2-0-31-4 ∷ []) (Sb2-0-13-4 ∷ []) (lem-SBsym-at3443 c4)
  q331 : Ws → Eqn
  q331 c4 = eqn (Sw12 ∷ Sb2-0-13-4 ∷ []) (Sb1-0-23-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·13·4⟩ (lit c4))

-- SBsym @12213443: 5 steps
lem-SBsym-at12213443 : Ws → ⟪ (Sb1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-23-4 ∷ []) ⟫ʷ
lem-SBsym-at12213443 c4 = derive (Sb1-0-32-4 ∷ []) (Sb1-0-23-4 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q276 c4) ∷
   rw 1 (q330 c4) ∷
   rw 0 (q331 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q332 : Ws → Eqn
  q332 c4 = eqn (Sb1-0-32-4 ∷ []) (Sb1-0-23-4 ∷ []) (lem-SBsym-at12213443 c4)

-- SBsym @13213442: 5 steps
lem-SBsym-at13213442 : Ws → ⟪ (Sb1-0-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-32-4 ∷ []) ⟫ʷ
lem-SBsym-at13213442 c4 = derive (Sb1-0-23-4 ∷ []) (Sb1-0-32-4 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q279 c4) ∷
   rw 1 (q332 c4) ∷
   rw 0 (q279 c4) ∷
   rw 1 (q17 c4) ∷ []) Eq.refl

private
  q333 : Ws → Eqn
  q333 c4 = eqn (Sb1-0-23-4 ∷ []) (Sb1-0-32-4 ∷ []) (lem-SBsym-at13213442 c4)
  q334 : Ws → Eqn
  q334 c4 = eqn (Sw01 ∷ Sb1-0-32-4 ∷ []) (Sb0-1-32-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·32·4⟩ (lit c4))

-- SBsym @0113203442: 5 steps
lem-SBsym-at0113203442 : Ws → ⟪ (Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ []) ⟫ʷ
lem-SBsym-at0113203442 c4 = derive (Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q282 c4) ∷
   rw 1 (q333 c4) ∷
   rw 0 (q334 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q335 : Ws → Eqn
  q335 c4 = eqn (Sw23 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4))
  q336 : Ws → Eqn
  q336 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0015 (lit c4))
  q337 : Ws → Eqn
  q337 c4 = eqn (Sb0-1-23-4 ∷ CS24 ∷ []) (CS24 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24 c4)
  q338 : Ws → Eqn
  q338 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0011 (lit c4))
  q339 : Ws → Eqn
  q339 c4 = eqn (Sw23 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | CS24 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 c4 = derive (Sb0-1-32-4 ∷ CS34 ∷ []) (CS34 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q335 c4) ∷
   rw⁻ 2 (q336 c4) ∷
   rw 1 (q337 c4) ∷
   rw⁻ 0 (q338 c4) ∷
   rw 1 (q339 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q340 : Ws → Eqn
  q340 c4 = eqn (Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4)
  q341 : Ws → Eqn
  q341 c4 = eqn (Sb0-1-32-4 ∷ CS34 ∷ []) (CS34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 c4)

-- auto SBOX(0;1;23;4) | CS34 CS34: 6 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-CS34 : Ws → ⟪ (Sb0-1-23-4 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS34 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-CS34 c4 = derive (Sb0-1-23-4 ∷ CS34 ∷ CS34 ∷ []) (CS34 ∷ CS34 ∷ Sb0-1-23-4 ∷ [])
  (rw 0 (q340 c4) ∷
   rw 0 (q341 c4) ∷
   rw⁻ 1 (q340 c4) ∷
   rw 1 (q340 c4) ∷
   rw 1 (q341 c4) ∷
   rw⁻ 2 (q340 c4) ∷ []) Eq.refl

private
  q342 : Ws → Eqn
  q342 c4 = eqn (Sb0-1-23-4 ∷ CS34 ∷ CS34 ∷ []) (CS34 ∷ CS34 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-CS34 c4)

-- auto SBOX(0;1;23;4) | CS34 CS34 @2332: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-CS34-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS24 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-CS34-at2332 c4 = derive (Sb0-1-32-4 ∷ CS24 ∷ CS24 ∷ []) (CS24 ∷ CS24 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q335 c4) ∷
   rw⁻ 2 (q338 c4) ∷
   rw⁻ 3 (q338 c4) ∷
   rw 1 (q342 c4) ∷
   rw⁻ 0 (q336 c4) ∷
   rw⁻ 1 (q336 c4) ∷
   rw 2 (q339 c4) ∷
   rw 3 (q17 c4) ∷ []) Eq.refl

private
  q343 : Ws → Eqn
  q343 c4 = eqn (CS24 ∷ CS24 ∷ []) (CZ24 ∷ []) (wl0305 (lit c4))
  q344 : Ws → Eqn
  q344 c4 = eqn (Sb0-1-32-4 ∷ CS24 ∷ CS24 ∷ []) (CS24 ∷ CS24 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-CS34-at2332 c4)

-- auto SBOX(0;1;23;4) | CZ24: 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ24 : Ws → ⟪ (Sb0-1-23-4 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (CZ24 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ24 c4 = derive (Sb0-1-23-4 ∷ CZ24 ∷ []) (CZ24 ∷ Sb0-1-23-4 ∷ [])
  (rw⁻ 1 (q343 c4) ∷
   rw 0 (q340 c4) ∷
   rw 0 (q344 c4) ∷
   rw⁻ 2 (q340 c4) ∷
   rw 0 (q343 c4) ∷ []) Eq.refl

-- auto BOX(0;1234) | Kd0: 1 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0 : Ws → ⟪ (Bx0-1234 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0 c4 = derive (Bx0-1234 ∷ K0⁻ ∷ []) (K0⁻ ∷ Bx0-1234 ∷ [])
  (rw⁻ 0 (q146 c4) ∷ []) Eq.refl

private
  q345 : Ws → Eqn
  q345 c4 = eqn (K0⁻ ∷ Sw01 ∷ []) (Sw01 ∷ K1⁻ ∷ []) (wl0257 (lit c4))
  q346 : Ws → Eqn
  q346 c4 = eqn (Bx0-1234 ∷ K0⁻ ∷ []) (K0⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0 c4)
  q347 : Ws → Eqn
  q347 c4 = eqn (K1⁻ ∷ Sw01 ∷ []) (Sw01 ∷ K0⁻ ∷ []) (wl0306 (lit c4))

-- auto BOX(0;1234) | Kd0 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0110 : Ws → ⟪ (Bx1-0234 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0110 c4 = derive (Bx1-0234 ∷ K1⁻ ∷ []) (K1⁻ ∷ Bx1-0234 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q200 c4) ∷
   rw⁻ 2 (q345 c4) ∷
   rw 1 (q346 c4) ∷
   rw⁻ 0 (q347 c4) ∷
   rw 1 (q196 c4) ∷
   rw 2 (q6 c4) ∷ []) Eq.refl

private
  q348 : Ws → Eqn
  q348 c4 = eqn (K1⁻ ∷ Sw12 ∷ []) (Sw12 ∷ K2⁻ ∷ []) (wl0307 (lit c4))
  q349 : Ws → Eqn
  q349 c4 = eqn (Bx1-0234 ∷ K1⁻ ∷ []) (K1⁻ ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0110 c4)
  q350 : Ws → Eqn
  q350 c4 = eqn (K2⁻ ∷ Sw12 ∷ []) (Sw12 ∷ K1⁻ ∷ []) (wl0308 (lit c4))

-- auto BOX(0;1234) | Kd0 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at021021 : Ws → ⟪ (Bx2-0134 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at021021 c4 = derive (Bx2-0134 ∷ K2⁻ ∷ []) (K2⁻ ∷ Bx2-0134 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q202 c4) ∷
   rw⁻ 2 (q348 c4) ∷
   rw 1 (q349 c4) ∷
   rw⁻ 0 (q350 c4) ∷
   rw 1 (q199 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q351 : Ws → Eqn
  q351 c4 = eqn (K2⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K3⁻ ∷ []) (wl0309 (lit c4))
  q352 : Ws → Eqn
  q352 c4 = eqn (Bx2-0134 ∷ K2⁻ ∷ []) (K2⁻ ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at021021 c4)
  q353 : Ws → Eqn
  q353 c4 = eqn (K3⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K2⁻ ∷ []) (wl0310 (lit c4))

-- auto BOX(0;1234) | Kd0 @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at03102132 : Ws → ⟪ (Bx3-0124 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at03102132 c4 = derive (Bx3-0124 ∷ K3⁻ ∷ []) (K3⁻ ∷ Bx3-0124 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q291 c4) ∷
   rw⁻ 2 (q351 c4) ∷
   rw 1 (q352 c4) ∷
   rw⁻ 0 (q353 c4) ∷
   rw 1 (q295 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q354 : Ws → Eqn
  q354 c4 = eqn (K3⁻ ∷ Sw34 ∷ []) (Sw34 ∷ K4⁻ ∷ []) (wl0311 (lit c4))
  q355 : Ws → Eqn
  q355 c4 = eqn (Bx3-0124 ∷ K3⁻ ∷ []) (K3⁻ ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at03102132 c4)
  q356 : Ws → Eqn
  q356 c4 = eqn (K4⁻ ∷ Sw34 ∷ []) (Sw34 ∷ K3⁻ ∷ []) (wl0312 (lit c4))

-- auto BOX(0;1234) | Kd0 @0410213243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx4-0123 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0410213243 c4 = derive (Bx4-0123 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx4-0123 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q296 c4) ∷
   rw⁻ 2 (q354 c4) ∷
   rw 1 (q355 c4) ∷
   rw⁻ 0 (q356 c4) ∷
   rw 1 (q300 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q357 : Ws → Eqn
  q357 c4 = eqn (Sw23 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K • iI))
  q358 : Ws → Eqn
  q358 c4 = eqn (Bx4-0123 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx4-0123 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0410213243 c4)

-- auto BOX(0;1234) | Kd0 @04102142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at04102142 : Ws → ⟪ (Bx4-0132 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx4-0132 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at04102142 c4 = derive (Bx4-0132 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx4-0132 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q301 c4) ∷
   rw 2 (q357 c4) ∷
   rw 1 (q358 c4) ∷
   rw 0 (q357 c4) ∷
   rw 1 (q304 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q359 : Ws → Eqn
  q359 c4 = eqn (Sw12 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) ((K • iI) ↑))
  q360 : Ws → Eqn
  q360 c4 = eqn (Bx4-0132 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx4-0132 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at04102142 c4)

-- auto BOX(0;1234) | Kd0 @041041: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at041041 : Ws → ⟪ (Bx4-0231 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx4-0231 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at041041 c4 = derive (Bx4-0231 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx4-0231 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q305 c4) ∷
   rw 2 (q359 c4) ∷
   rw 1 (q360 c4) ∷
   rw 0 (q359 c4) ∷
   rw 1 (q308 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q361 : Ws → Eqn
  q361 c4 = eqn (Sw01 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((K • iI) ↑ ↑))
  q362 : Ws → Eqn
  q362 c4 = eqn (Bx4-0231 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx4-0231 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at041041 c4)

-- auto BOX(0;1234) | Kd0 @0440: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0440 : Ws → ⟪ (Bx4-1230 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx4-1230 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0440 c4 = derive (Bx4-1230 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx4-1230 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q309 c4) ∷
   rw 2 (q361 c4) ∷
   rw 1 (q362 c4) ∷
   rw 0 (q361 c4) ∷
   rw 1 (q312 c4) ∷
   rw 2 (q6 c4) ∷ []) Eq.refl

private
  q363 : Ws → Eqn
  q363 c4 = eqn (CS01⁻ ∷ K4⁻ ∷ []) (K4⁻ ∷ CS01⁻ ∷ []) (wl0313 (lit c4))
  q364 : Ws → Eqn
  q364 c4 = eqn (K4⁻ ∷ Toff023 ∷ []) (Toff023 ∷ K4⁻ ∷ []) (wp0095 c4)
  q365 : Ws → Eqn
  q365 c4 = eqn (CS01 ∷ K4⁻ ∷ []) (K4⁻ ∷ CS01 ∷ []) (wl0314 (lit c4))
  q366 : Ws → Eqn
  q366 c4 = eqn (Bx4-1230 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx4-1230 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0440 c4)

-- auto SBOX(0;1;23;4) | Kd4: 13 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4 : Ws → ⟪ (Sb0-1-23-4 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4 c4 = derive (Sb0-1-23-4 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sb0-1-23-4 ∷ [])
  (rw 0 (q313 c4) ∷
   re 0 1 (Bx4-1230 ∷ Toff023 ∷ Sb4-1-0-3 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ []) ∷
   re 4 1 (CS01⁻ ∷ []) ∷
   rw 4 (q363 c4) ∷
   re 5 1 (Sb⁻4-1-0-3 ∷ []) ∷
   rw⁻ 3 (q364 c4) ∷
   re 2 1 (CS01 ∷ []) ∷
   rw 2 (q365 c4) ∷
   re 3 1 (Sb4-1-0-3 ∷ []) ∷
   rw⁻ 1 (q364 c4) ∷
   rw 0 (q366 c4) ∷
   re 1 5 (Sb4-1-23-0 ∷ []) ∷
   rw⁻ 1 (q313 c4) ∷ []) Eq.refl

private
  q367 : Ws → Eqn
  q367 c4 = eqn (Sb0-1-23-4 ∷ K4 ∷ []) (K4 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4 c4)

-- auto SBOX(0;1;23;4) | K4 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 c4 = derive (Sb0-1-32-4 ∷ K4 ∷ []) (K4 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q335 c4) ∷
   rw 2 (q302 c4) ∷
   rw 1 (q367 c4) ∷
   rw 0 (q302 c4) ∷
   rw 1 (q339 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q368 : Ws → Eqn
  q368 c4 = eqn (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) (wl0027 (lit c4))
  q369 : Ws → Eqn
  q369 c4 = eqn (Sb0-1-23-4 ∷ CZ24 ∷ []) (CZ24 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ24 c4)
  q370 : Ws → Eqn
  q370 c4 = eqn (CZ34 ∷ Sw23 ∷ []) (Sw23 ∷ CZ24 ∷ []) (wl0028 (lit c4))

-- auto SBOX(0;1;23;4) | CZ24 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ24-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (CZ34 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ24-at2332 c4 = derive (Sb0-1-32-4 ∷ CZ34 ∷ []) (CZ34 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q335 c4) ∷
   rw⁻ 2 (q368 c4) ∷
   rw 1 (q369 c4) ∷
   rw⁻ 0 (q370 c4) ∷
   rw 1 (q339 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q371 : Ws → Eqn
  q371 c4 = eqn (Sb0-1-23-4 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4 c4)

-- auto SBOX(0;1;23;4) | Kd4 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 c4 = derive (Sb0-1-32-4 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q335 c4) ∷
   rw 2 (q357 c4) ∷
   rw 1 (q371 c4) ∷
   rw 0 (q357 c4) ∷
   rw 1 (q339 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q372 : Ws → Eqn
  q372 c4 = eqn (CX34 ∷ []) (K4 ∷ CZ34 ∷ K4⁻ ∷ []) (wl0315 (lit c4))
  q373 : Ws → Eqn
  q373 c4 = eqn (Sb0-1-32-4 ∷ K4 ∷ []) (K4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 c4)
  q374 : Ws → Eqn
  q374 c4 = eqn (Sb0-1-32-4 ∷ CZ34 ∷ []) (CZ34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ24-at2332 c4)
  q375 : Ws → Eqn
  q375 c4 = eqn (Sb0-1-32-4 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 c4)

-- auto SBOX(0;1;23;4) | CX34: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34 : Ws → ⟪ (Sb0-1-23-4 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34 c4 = derive (Sb0-1-23-4 ∷ CX34 ∷ []) (CX34 ∷ Sb0-1-23-4 ∷ [])
  (rw 1 (q372 c4) ∷
   rw 0 (q340 c4) ∷
   rw 0 (q373 c4) ∷
   rw 1 (q374 c4) ∷
   rw 2 (q375 c4) ∷
   rw⁻ 3 (q340 c4) ∷
   rw⁻ 0 (q372 c4) ∷ []) Eq.refl

private
  q376 : Ws → Eqn
  q376 c4 = eqn (CS14⁻ ∷ []) (CS14⁻ ∷ []) (wl0316 (lit c4))
  q377 : Ws → Eqn
  q377 c4 = eqn (CS14⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS14⁻ ∷ []) (lem-CSd12-beta-at243243 c4)

-- auto BOX(0;1234) | CSd41: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd41 : Ws → ⟪ (Bx0-1234 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd41 c4 = derive (Bx0-1234 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx0-1234 ∷ [])
  (rw 1 (q376 c4) ∷
   rw 0 (q266 c4) ∷
   rw 0 (q267 c4) ∷
   rw⁻ 0 (q377 c4) ∷
   rw 1 (q269 c4) ∷
   rw 1 (q270 c4) ∷
   rw 0 (q376 c4) ∷ []) Eq.refl

private
  q378 : Ws → Eqn
  q378 c4 = eqn (CS14⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS14⁻ ∷ []) (wl0317 (lit c4))
  q379 : Ws → Eqn
  q379 c4 = eqn (CS14⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ []) (wl0318 (lit c4))
  q380 : Ws → Eqn
  q380 c4 = eqn (Bx0-1234 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd41 c4)

-- auto SBOX(0;1;23;4) | CSd41: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41 : Ws → ⟪ (Sb0-1-23-4 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41 c4 = derive (Sb0-1-23-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw 4 (q378 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw⁻ 1 (q379 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw 0 (q380 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q381 : Ws → Eqn
  q381 c4 = eqn (CS13 ∷ []) (CS13 ∷ []) (wl0319 (lit c4))

-- auto BOX(0;1234) | CS31: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CS31 : Ws → ⟪ (Bx0-1234 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS31 c4 = derive (Bx0-1234 ∷ CS13 ∷ []) (CS13 ∷ Bx0-1234 ∷ [])
  (rw 1 (q381 c4) ∷
   rw 0 (q83 c4) ∷
   rw⁻ 0 (q84 c4) ∷
   rw 1 (q85 c4) ∷
   rw 0 (q381 c4) ∷ []) Eq.refl

private
  q382 : Ws → Eqn
  q382 c4 = eqn (CS13 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS13 ∷ []) (wl0320 (lit c4))
  q383 : Ws → Eqn
  q383 c4 = eqn (CS13 ∷ Toff423 ∷ []) (Toff423 ∷ CS13 ∷ []) (wl0321 (lit c4))
  q384 : Ws → Eqn
  q384 c4 = eqn (CS13 ∷ CS14 ∷ []) (CS14 ∷ CS13 ∷ []) (wl0322 (lit c4))
  q385 : Ws → Eqn
  q385 c4 = eqn (Bx0-1234 ∷ CS13 ∷ []) (CS13 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS31 c4)

-- auto SBOX(0;1;23;4) | CS31: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31 : Ws → ⟪ (Sb0-1-23-4 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31 c4 = derive (Sb0-1-23-4 ∷ CS13 ∷ []) (CS13 ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q382 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw⁻ 3 (q383 c4) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw⁻ 2 (q384 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw⁻ 1 (q383 c4) ∷
   rw 0 (q385 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q386 : Ws → Eqn
  q386 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl0021 (lit c4))
  q387 : Ws → Eqn
  q387 c4 = eqn (Sb0-1-23-4 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41 c4)

-- auto SBOX(0;1;23;4) | CS41 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41-at2332 c4 = derive (Sb0-1-32-4 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q335 c4) ∷
   rw⁻ 2 (q386 c4) ∷
   rw 1 (q387 c4) ∷
   rw⁻ 0 (q386 c4) ∷
   rw 1 (q339 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q388 : Ws → Eqn
  q388 c4 = eqn (CX34 ∷ Sw23 ∷ []) (Sw23 ∷ CX24 ∷ []) (wl0051 (lit c4))
  q389 : Ws → Eqn
  q389 c4 = eqn (Sb0-1-23-4 ∷ CX34 ∷ []) (CX34 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34 c4)
  q390 : Ws → Eqn
  q390 c4 = eqn (CX24 ∷ Sw23 ∷ []) (Sw23 ∷ CX34 ∷ []) (wl0050 (lit c4))

-- auto SBOX(0;1;23;4) | CX34 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34-at2332 c4 = derive (Sb0-1-32-4 ∷ CX24 ∷ []) (CX24 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q335 c4) ∷
   rw⁻ 2 (q388 c4) ∷
   rw 1 (q389 c4) ∷
   rw⁻ 0 (q390 c4) ∷
   rw 1 (q339 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q391 : Ws → Eqn
  q391 c4 = eqn (CS14⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS14⁻ ∷ []) (wl0033 (lit c4))
  q392 : Ws → Eqn
  q392 c4 = eqn (Sb0-1-23-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41 c4)

-- auto SBOX(0;1;23;4) | CSd41 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41-at2332 c4 = derive (Sb0-1-32-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q335 c4) ∷
   rw⁻ 2 (q391 c4) ∷
   rw 1 (q392 c4) ∷
   rw⁻ 0 (q391 c4) ∷
   rw 1 (q339 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q393 : Ws → Eqn
  q393 c4 = eqn (Sb0-1-23-4 ∷ CS13 ∷ []) (CS13 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31 c4)

-- auto SBOX(0;1;23;4) | CS31 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31-at2332 c4 = derive (Sb0-1-32-4 ∷ CS12 ∷ []) (CS12 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q335 c4) ∷
   rw 2 (q65 c4) ∷
   rw 1 (q393 c4) ∷
   rw 0 (q63 c4) ∷
   rw 1 (q339 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q394 : Ws → Eqn
  q394 c4 = eqn (CCZ124 ∷ []) (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) (wl0323 (lit c4))
  q395 : Ws → Eqn
  q395 c4 = eqn (Sb0-1-32-4 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41-at2332 c4)
  q396 : Ws → Eqn
  q396 c4 = eqn (Sb0-1-32-4 ∷ CX24 ∷ []) (CX24 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34-at2332 c4)
  q397 : Ws → Eqn
  q397 c4 = eqn (Sb0-1-32-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41-at2332 c4)
  q398 : Ws → Eqn
  q398 c4 = eqn (Sb0-1-32-4 ∷ CS12 ∷ []) (CS12 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31-at2332 c4)

-- auto SBOX(0;1;23;4) | CCZ124: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124 : Ws → ⟪ (Sb0-1-23-4 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124 c4 = derive (Sb0-1-23-4 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb0-1-23-4 ∷ [])
  (rw 1 (q394 c4) ∷
   rw 0 (q340 c4) ∷
   rw 0 (q395 c4) ∷
   rw 1 (q396 c4) ∷
   rw 2 (q397 c4) ∷
   rw 3 (q396 c4) ∷
   rw 4 (q398 c4) ∷
   rw⁻ 5 (q340 c4) ∷
   rw⁻ 0 (q394 c4) ∷ []) Eq.refl

private
  q399 : Ws → Eqn
  q399 c4 = eqn (CS03 ∷ CS03⁻ ∷ []) [] (wl0250 (lit c4))
  q400 : Ws → Eqn
  q400 c4 = eqn (CS03⁻ ∷ CS03 ∷ []) [] (wl0249 (lit c4))
  q401 : Ws → Eqn
  q401 c4 = eqn (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) [] (wl0247 (lit c4))
  q402 : Ws → Eqn
  q402 c4 = eqn (CCZ024 ∷ CCZ024 ∷ []) [] (wp0034 c4)
  q403 : Ws → Eqn
  q403 c4 = eqn (Toff204 ∷ Toff204 ∷ []) [] (wp0059 c4)
  q404 : Ws → Eqn
  q404 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CS01 ∷ []) (lem-F5-CS01 c4)
  q405 : Ws → Eqn
  q405 c4 = eqn (CS01 ∷ CS01⁻ ∷ []) [] (wl0324 (lit c4))

-- F5d CS01: 64 steps
lem-F5d-CS01 : Ws → ⟪ (CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-41-3 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F5d-CS01 c4 = derive (CS01⁻ ∷ []) (Sb⁻2-0-41-3 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ [])
  (rw⁻ 0 (q399 c4) ∷
   re 0 1 (Sb2-0-3-1 ∷ []) ∷
   re 1 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 1 (q32 c4) ∷
   rw⁻ 2 (q400 c4) ∷
   re 2 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 3 (q32 c4) ∷
   rw⁻ 4 (q401 c4) ∷
   re 4 1 (Bx⁻2-03 ∷ []) ∷
   re 7 1 (Bx⁻2-03 ∷ []) ∷
   re 4 6 (Bx⁻0-213 ∷ []) ∷
   re 7 1 (Bx2-03 ∷ []) ∷
   re 10 1 (Bx2-03 ∷ []) ∷
   re 5 6 (Bx0-213 ∷ []) ∷
   rw⁻ 5 (q402 c4) ∷
   rw⁻ 6 (q403 c4) ∷
   rw⁻ 7 (q401 c4) ∷
   re 7 1 (Bx⁻2-03 ∷ []) ∷
   re 10 1 (Bx⁻2-03 ∷ []) ∷
   re 7 6 (Bx⁻0-213 ∷ []) ∷
   re 10 1 (Bx2-03 ∷ []) ∷
   re 13 1 (Bx2-03 ∷ []) ∷
   re 8 6 (Bx0-213 ∷ []) ∷
   rw⁻ 8 (q403 c4) ∷
   rw⁻ 9 (q402 c4) ∷
   re 4 6 (Bx⁻2-0413 ∷ []) ∷
   re 5 6 (Bx2-0413 ∷ []) ∷
   re 0 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 1 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 1 (q126 c4) ∷
   rw⁻ 2 (q399 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 3 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 3 (q32 c4) ∷
   rw⁻ 4 (q400 c4) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 5 (q32 c4) ∷
   rw⁻ 6 (q401 c4) ∷
   re 6 1 (Bx⁻2-03 ∷ []) ∷
   re 9 1 (Bx⁻2-03 ∷ []) ∷
   re 6 6 (Bx⁻0-213 ∷ []) ∷
   re 9 1 (Bx2-03 ∷ []) ∷
   re 12 1 (Bx2-03 ∷ []) ∷
   re 7 6 (Bx0-213 ∷ []) ∷
   rw⁻ 7 (q402 c4) ∷
   rw⁻ 8 (q403 c4) ∷
   rw⁻ 9 (q401 c4) ∷
   re 9 1 (Bx⁻2-03 ∷ []) ∷
   re 12 1 (Bx⁻2-03 ∷ []) ∷
   re 9 6 (Bx⁻0-213 ∷ []) ∷
   re 12 1 (Bx2-03 ∷ []) ∷
   re 15 1 (Bx2-03 ∷ []) ∷
   re 10 6 (Bx0-213 ∷ []) ∷
   rw⁻ 10 (q403 c4) ∷
   rw⁻ 11 (q402 c4) ∷
   re 6 6 (Bx⁻2-0413 ∷ []) ∷
   re 7 6 (Bx2-0413 ∷ []) ∷
   re 2 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 3 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 3 (q126 c4) ∷
   rw 4 (q404 c4) ∷
   rw 4 (q405 c4) ∷ []) Eq.refl

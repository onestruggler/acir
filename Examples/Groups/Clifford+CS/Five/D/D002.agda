{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D002 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0008 ; wl0010 ; wl0017 ; wl0019 ; wl0021 ; wl0022 ; wl0023 ; wl0024 ; wl0025 ; wl0031 ; wl0033 ; wl0034 ; wl0047 ; wl0061 ; wl0070 ; wl0084 ; wl0086 ; wl0096 ; wl0099 ; wl0103 ; wl0108 ; wl0111 ; wl0113 ; wl0116 ; wl0121 ; wl0130 ; wl0146 ; wl0149 ; wl0152 ; wl0154 ; wl0155 ; wl0158 ; wl0183 ; wl0212 ; wl0247 ; wl0248 ; wl0249 ; wl0250 ; wl0251 ; wl0252 ; wl0253 ; wl0254 ; wl0255 ; wl0256 ; wl0257 ; wl0258 ; wl0259 ; wl0260 ; wl0261 ; wl0262 ; wl0263 ; wl0264 ; wl0265 ; wl0266 ; wl0267 ; wl0268 ; wl0269 ; wl0270 ; wl0271 ; wl0272 ; wl0273 ; wl0274 ; wl0275 ; wl0276 ; wl0277 ; wp0011 ; wp0012 ; wp0024 ; wp0034 ; wp0055 ; wp0056 ; wp0059 ; wp0060 ; wp0061 ; wp0062 ; wp0063 ; wp0064 ; wp0065 ; wp0066 ; wp0067 ; wp0068 ; wp0069 ; wp0070 ; wp0071 ; wp0072 ; wp0073 ; wp0074 ; wp0075 ; wp0076 ; wp0077 ; wp0078)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-BOXd-BOX ; lem-CS12-beta ; lem-CS20-beta-c ; lem-CSd12-beta ; lem-CX23-beta ; lem-CZ10-beta-c-at011220 ; lem-Cz-beta ; lem-K0-pass ; lem-T-beta ; lem-T312-beta ; lem-T312-beta-at14213243 ; lem-auto-CCZ012-∣-CCZ314-at2332 ; lem-auto-CX01-∣-BOX⟨1·2034⟩ ; lem-beta-T ; lem-beta-T-at2332 ; lem-beta-T-at243243 ; lem-beta-form ; lem-beta-inv-at0210243143 ; lem-beta-mirror ; lem-c124-beta ; lem-c124-beta-at3443 ; lem-sym12 ; lem-sym12-at0110 ; lem-sym12-at0214203143 ; lem-sym12-at1221 ; lem-sym12-at132132 ; lem-sym23 ; lem-sym23-at0214203143 ; lem-sym23-at0214213043 ; lem-sym23-at1221 ; lem-sym34 ; lem-sym34-at01103443 ; lem-sym34-at0214203143 ; lem-sym34-at03102132 ; lem-sym34-at0310213442 ; lem-sym34-at1221 ; lem-sym34-at14213243 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-BOX⟨0·3412⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-3-BOX⟨0·1243⟩ ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-BOX⟨0·1423⟩ ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF301 ; lem-nat-2-BOX⟨0·2413⟩ ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF201 ; lem-nat-2-TOFF204 ; lem-nat-3-BOX⟨0·1324⟩ ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ014 ; lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF104 ; lem-nat-0-TOFF304 ; lem-nat-0-TOFF314 ; lem-nat-1-BOX⟨0·1243⟩ ; lem-nat-1-TOFF104 ; lem-nat-2-BOX⟨0·2143⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-BOX⟨0·4123⟩ ; lem-nat-0-BOX⟨0·4132⟩ ; lem-nat-1-BOX⟨0·1234⟩ ; lem-nat-1-BOX⟨0·1324⟩ ; lem-nat-1-BOX⟨1·4023⟩ ; lem-nat-1-BOX⟨1·4032⟩ ; lem-nat-1-TOFF013 ; lem-nat-1-TOFF304 ; lem-nat-2-BOX⟨0·2134⟩ ; lem-nat-3-BOX⟨0·3124⟩)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨0·1243⟩ ; lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-0-BOX⟨1·0243⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-0-BOX⟨2·4103⟩ ; lem-nat-1-BOX⟨1·0243⟩ ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-BOX⟨2·0143⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-1-BOX⟨3·0214⟩ ; lem-nat-2-BOX⟨2·0143⟩ ; lem-nat-2-BOX⟨2·0314⟩ ; lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0124⟩ ; lem-nat-2-BOX⟨3·0142⟩ ; lem-nat-2-BOX⟨3·0412⟩ ; lem-nat-3-BOX⟨0·1234⟩ ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-CKd40-CCZ123 ; lem-nat-0-BOX⟨0·1324⟩ ; lem-nat-0-BOX⟨0·2134⟩ ; lem-nat-0-BOX⟨0·2143⟩ ; lem-nat-0-BOX⟨0·2314⟩ ; lem-nat-0-BOX⟨1·2034⟩ ; lem-nat-0-BOX⟨1·2043⟩ ; lem-nat-0-BOX⟨1·2304⟩ ; lem-nat-0-BOX⟨2·4031⟩ ; lem-nat-0-BOX⟨3·0214⟩ ; lem-nat-0-BOX⟨3·1024⟩ ; lem-nat-0-BOX⟨3·1204⟩ ; lem-nat-0-BOXd⟨1·0423⟩ ; lem-nat-0-BOXd⟨1·4023⟩ ; lem-nat-1-BOX⟨0·1342⟩ ; lem-nat-1-BOX⟨0·2143⟩ ; lem-nat-1-BOX⟨0·2314⟩ ; lem-nat-1-BOX⟨0·2341⟩ ; lem-nat-1-BOX⟨1·0324⟩ ; lem-nat-1-BOX⟨1·2034⟩ ; lem-nat-1-BOXd⟨0·2134⟩ ; lem-nat-1-BOXd⟨2·0413⟩ ; lem-nat-1-BOXd⟨2·4013⟩ ; lem-nat-1-CS01 ; lem-nat-1-CS02 ; lem-nat-1-CX10 ; lem-nat-1-CX20 ; lem-nat-1-CZ01 ; lem-nat-1-CZ02 ; lem-nat-2-BOX⟨0·1243⟩ ; lem-nat-2-BOX⟨0·1342⟩ ; lem-nat-2-BOX⟨0·3142⟩ ; lem-nat-2-BOX⟨2·1034⟩ ; lem-nat-2-BOXd⟨0·1324⟩ ; lem-nat-2-BOXd⟨0·3124⟩ ; lem-nat-2-CS12 ; lem-nat-2-CS13 ; lem-nat-2-CSd12 ; lem-nat-2-CSd13 ; lem-nat-2-TOFF314 ; lem-nat-3-BOX⟨0·2134⟩ ; lem-nat-3-BOXd⟨0·1423⟩ ; lem-nat-3-BOXd⟨0·4123⟩ ; lem-nat-3-CS13 ; lem-nat-3-CS14 ; lem-nat-3-CSd13 ; lem-nat-3-CSd14)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨1·4032⟩ ; lem-nat-0-BOX⟨2·0413⟩ ; lem-nat-0-BOX⟨2·1403⟩ ; lem-nat-0-BOX⟨2·4013⟩ ; lem-nat-0-BOX⟨2·4130⟩ ; lem-nat-0-CS04 ; lem-nat-0-CS14 ; lem-nat-0-CX40 ; lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-BOX⟨2·4031⟩ ; lem-nat-1-CS04 ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-2-BOX⟨0·4123⟩ ; lem-nat-2-BOX⟨0·4132⟩ ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-3-CS23 ; lem-nat-3-CS24 ; lem-nat-3-CX42 ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CZ01 ∷ []) (CZ01 ∷ []) (wl0252 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (CZ01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CZ01 ∷ []) (lem-CZ10-beta-c-at011220 c4)

-- auto CZ01 | BOX(1;2034): 3 steps
lem-auto-CZ01-∣-BOX⟨1·2034⟩ : Ws → ⟪ (CZ01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CZ01 ∷ []) ⟫ʷ
lem-auto-CZ01-∣-BOX⟨1·2034⟩ c4 = derive (CZ01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CZ01 ∷ [])
  (rw 0 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw 1 (q1 c4) ∷ []) Eq.refl

private
  q3 : Ws → Eqn
  q3 c4 = eqn (CX01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CX01 ∷ []) (lem-auto-CX01-∣-BOX⟨1·2034⟩ c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CZ01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CZ01 ∷ []) (lem-auto-CZ01-∣-BOX⟨1·2034⟩ c4)

-- auto CZ01 CX01 | BOX(1;2034): 2 steps
lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩ : Ws → ⟪ (CZ01 ∷ CX01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CZ01 ∷ CX01 ∷ []) ⟫ʷ
lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩ c4 = derive (CZ01 ∷ CX01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CZ01 ∷ CX01 ∷ [])
  (rw 1 (q3 c4) ∷
   rw 0 (q4 c4) ∷ []) Eq.refl

private
  q5 : Ws → Eqn
  q5 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (Sw23 ∷ CCZ134 ∷ []) (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (Sw23 ∷ Bx0-1324 ∷ []) (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ124 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ []) (lem-c124-beta c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (Sw23 ∷ Bx0-1234 ∷ []) (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Sw23 ∷ CCZ124 ∷ []) (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4))

-- c124-beta @2332: 7 steps
lem-c124-beta-at2332 : Ws → ⟪ (CCZ134 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ134 ∷ []) ⟫ʷ
lem-c124-beta-at2332 c4 = derive (CCZ134 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CCZ134 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   rw 0 (q9 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (Sw12 ∷ Bx0-2314 ∷ []) (Bx0-1324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2314⟩ (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CCZ134 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CCZ134 ∷ []) (lem-c124-beta-at2332 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (Sw12 ∷ Bx0-1324 ∷ []) (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl0084 (lit c4))

-- c124-beta @122331: 7 steps
lem-c124-beta-at122331 : Ws → ⟪ (CCZ234 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CCZ234 ∷ []) ⟫ʷ
lem-c124-beta-at122331 c4 = derive (CCZ234 ∷ Bx0-2314 ∷ []) (Bx0-2314 ∷ CCZ234 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw⁻ 1 (q12 c4) ∷
   rw 2 (q13 c4) ∷
   rw 1 (q14 c4) ∷
   rw 0 (q15 c4) ∷
   rw⁻ 1 (q16 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1324 ∷ []) (lem-sym23 c4)

-- sym23 @2332: 5 steps
lem-sym23-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-sym23-at2332 c4 = derive (Bx0-1324 ∷ []) (Bx0-1234 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q7 c4) ∷
   rw 1 (q17 c4) ∷
   rw 0 (q7 c4) ∷
   rw 1 (q5 c4) ∷ []) Eq.refl

private
  q18 : Ws → Eqn
  q18 c4 = eqn (Bx0-1324 ∷ []) (Bx0-1234 ∷ []) (lem-sym23-at2332 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw12 ∷ Bx0-1234 ∷ []) (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4))

-- sym23 @122331: 5 steps
lem-sym23-at122331 : Ws → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-sym23-at122331 c4 = derive (Bx0-2314 ∷ []) (Bx0-2134 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q13 c4) ∷
   rw 1 (q18 c4) ∷
   rw 0 (q19 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q20 : Ws → Eqn
  q20 c4 = eqn (Bx0-1234 ∷ []) (Bx0-2134 ∷ []) (lem-sym12 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (Bx0-2134 ∷ []) (Bx0-2314 ∷ []) (lem-sym23-at1221 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ234 ∷ Bx0-2314 ∷ []) (Bx0-2314 ∷ CCZ234 ∷ []) (lem-c124-beta-at122331 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (Bx0-2314 ∷ []) (Bx0-2134 ∷ []) (lem-sym23-at122331 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (Bx0-2134 ∷ []) (Bx0-1234 ∷ []) (lem-sym12-at1221 c4)

-- auto BOX(0;1234) | CCZ234: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ234 : Ws → ⟪ (Bx0-1234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ234 c4 = derive (Bx0-1234 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1234 ∷ [])
  (rw 0 (q20 c4) ∷
   rw 0 (q21 c4) ∷
   rw⁻ 0 (q22 c4) ∷
   rw 1 (q23 c4) ∷
   rw 1 (q24 c4) ∷ []) Eq.refl

private
  q25 : Ws → Eqn
  q25 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CZ01 ∷ Sw01 ∷ []) (Sw01 ∷ CZ01 ∷ []) (wl0130 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wl0251 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (Sw01 ∷ Bx0-2134 ∷ []) (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CZ01 ∷ CX01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CZ01 ∷ CX01 ∷ []) (lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩ c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (Sw01 ∷ Bx1-2034 ∷ []) (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CX10 ∷ Sw01 ∷ []) (Sw01 ∷ CX01 ∷ []) (wl0070 (lit c4))

-- auto CZ01 CX01 | BOX(1;2034) @0110: 9 steps
lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩-at0110 : Ws → ⟪ (CZ01 ∷ CX10 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CZ01 ∷ CX10 ∷ []) ⟫ʷ
lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩-at0110 c4 = derive (CZ01 ∷ CX10 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CZ01 ∷ CX10 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw⁻ 1 (q26 c4) ∷
   rw⁻ 2 (q27 c4) ∷
   rw 3 (q28 c4) ∷
   rw 1 (q29 c4) ∷
   rw 0 (q30 c4) ∷
   rw⁻ 1 (q26 c4) ∷
   rw⁻ 2 (q31 c4) ∷
   rw 3 (q25 c4) ∷ []) Eq.refl

private
  q32 : Ws → Eqn
  q32 c4 = eqn (Sw12 ∷ CZ02 ∷ []) (CZ01 ∷ Sw12 ∷ []) (lem-nat-1-CZ02 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (Sw12 ∷ CX20 ∷ []) (CX10 ∷ Sw12 ∷ []) (lem-nat-1-CX20 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (CZ01 ∷ CX10 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CZ01 ∷ CX10 ∷ []) (lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩-at0110 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (Sw12 ∷ Bx0-2134 ∷ []) (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (Sw12 ∷ CZ01 ∷ []) (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (Sw12 ∷ CX10 ∷ []) (CX20 ∷ Sw12 ∷ []) (lem-nat-1-CX10 (lit c4))

-- auto CZ01 CX01 | BOX(1;2034) @021021: 9 steps
lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩-at021021 : Ws → ⟪ (CZ02 ∷ CX20 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CZ02 ∷ CX20 ∷ []) ⟫ʷ
lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩-at021021 c4 = derive (CZ02 ∷ CX20 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CZ02 ∷ CX20 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q32 c4) ∷
   rw 2 (q33 c4) ∷
   rw 3 (q19 c4) ∷
   rw 1 (q34 c4) ∷
   rw 0 (q35 c4) ∷
   rw 1 (q36 c4) ∷
   rw 2 (q37 c4) ∷
   rw 3 (q11 c4) ∷ []) Eq.refl

private
  q38 : Ws → Eqn
  q38 c4 = eqn (Bx0-1234 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (CZ02 ∷ CX20 ∷ Toff012 ∷ CCZ012 ∷ X1 ∷ []) (X1 ∷ CCZ012 ∷ Toff012 ∷ []) (wl0253 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ034 ∷ X1 ∷ []) (X1 ∷ CCZ034 ∷ []) (wp0060 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ012 ∷ Toff012 ∷ CX20 ∷ CZ02 ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CCZ012 ∷ []) (wl0254 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ034 ∷ []) (X1 ∷ CCZ034 ∷ X1 ∷ []) (wp0061 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ034 ∷ CCZ034 ∷ []) [] (wp0024 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (Bx0-1234 ∷ []) (Toff012 ∷ CCZ012 ∷ CCZ034 ∷ CCZ012 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-mirror c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (CZ02 ∷ CX20 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CZ02 ∷ CX20 ∷ []) (lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩-at021021 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ234 ∷ []) (CZ02 ∷ CX20 ∷ CCZ034 ∷ CX20 ∷ CZ02 ∷ CCZ034 ∷ []) (wp0062 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (Bx0-1234 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234 c4)

-- X1-beta: 10 steps
lem-X1-beta : Ws → ⟪ (X1 ∷ Bx0-1234 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-X1-beta c4 = derive (X1 ∷ Bx0-1234 ∷ X1 ∷ []) (CCZ234 ∷ Bx0-1234 ∷ [])
  (rw 1 (q38 c4) ∷
   rw⁻ 0 (q39 c4) ∷
   rw⁻ 4 (q40 c4) ∷
   rw⁻ 5 (q41 c4) ∷
   rw⁻ 9 (q42 c4) ∷
   rw⁻ 7 (q43 c4) ∷
   rw⁻ 2 (q44 c4) ∷
   rw 0 (q45 c4) ∷
   rw⁻ 1 (q46 c4) ∷
   rw 0 (q47 c4) ∷ []) Eq.refl

private
  q48 : Ws → Eqn
  q48 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1243 ∷ []) (lem-sym34 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (Sw23 ∷ Bx0-1243 ∷ []) (Bx0-1342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1243⟩ (lit c4))

-- sym34 @2332: 5 steps
lem-sym34-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-sym34-at2332 c4 = derive (Bx0-1324 ∷ []) (Bx0-1342 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q7 c4) ∷
   rw 1 (q48 c4) ∷
   rw 0 (q49 c4) ∷
   rw 1 (q5 c4) ∷ []) Eq.refl

private
  q50 : Ws → Eqn
  q50 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (Sw34 ∷ Bx0-1243 ∷ []) (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (Sw34 ∷ Bx0-2134 ∷ []) (Bx0-2143 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2134⟩ (lit c4))

-- sym12 @3443: 5 steps
lem-sym12-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-sym12-at3443 c4 = derive (Bx0-1243 ∷ []) (Bx0-2143 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q51 c4) ∷
   rw 1 (q20 c4) ∷
   rw 0 (q52 c4) ∷
   rw 1 (q50 c4) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = eqn (Sw23 ∷ Bx0-1342 ∷ []) (Bx0-1243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1342⟩ (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (Bx0-1243 ∷ []) (Bx0-2143 ∷ []) (lem-sym12-at3443 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (Sw23 ∷ Bx0-2143 ∷ []) (Bx0-3142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2143⟩ (lit c4))

-- sym12 @233442: 5 steps
lem-sym12-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-sym12-at233442 c4 = derive (Bx0-1342 ∷ []) (Bx0-3142 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q53 c4) ∷
   rw 1 (q54 c4) ∷
   rw 0 (q55 c4) ∷
   rw 1 (q5 c4) ∷ []) Eq.refl

private
  q56 : Ws → Eqn
  q56 c4 = eqn (Sw34 ∷ Bx0-1324 ∷ []) (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4))

-- sym23 @3443: 5 steps
lem-sym23-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-sym23-at3443 c4 = derive (Bx0-1243 ∷ []) (Bx0-1423 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q51 c4) ∷
   rw 1 (q17 c4) ∷
   rw 0 (q56 c4) ∷
   rw 1 (q50 c4) ∷ []) Eq.refl

private
  q57 : Ws → Eqn
  q57 c4 = eqn (Sw12 ∷ Bx0-2143 ∷ []) (Bx0-1243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2143⟩ (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (Bx0-1243 ∷ []) (Bx0-1423 ∷ []) (lem-sym23-at3443 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (Sw12 ∷ Bx0-1423 ∷ []) (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4))

-- sym23 @12213443: 5 steps
lem-sym23-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-sym23-at12213443 c4 = derive (Bx0-2143 ∷ []) (Bx0-2413 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q57 c4) ∷
   rw 1 (q58 c4) ∷
   rw 0 (q59 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = eqn (Sw23 ∷ Bx0-3142 ∷ []) (Bx0-2143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3142⟩ (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (Bx0-2143 ∷ []) (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (Sw23 ∷ Bx0-2413 ∷ []) (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ (lit c4))

-- sym23 @13213442: 5 steps
lem-sym23-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-sym23-at13213442 c4 = derive (Bx0-3142 ∷ []) (Bx0-3412 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q60 c4) ∷
   rw 1 (q61 c4) ∷
   rw 0 (q62 c4) ∷
   rw 1 (q5 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (CCZ012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ012 ∷ []) (lem-Cz-beta c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4))

-- Cz-beta @2332: 7 steps
lem-Cz-beta-at2332 : Ws → ⟪ (CCZ013 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ013 ∷ []) ⟫ʷ
lem-Cz-beta-at2332 c4 = derive (CCZ013 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q63 c4) ∷
   rw 2 (q7 c4) ∷
   rw 1 (q64 c4) ∷
   rw 0 (q9 c4) ∷
   rw 1 (q65 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = eqn (Sw34 ∷ CCZ014 ∷ []) (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (Sw34 ∷ Bx0-1423 ∷ []) (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (CCZ013 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CCZ013 ∷ []) (lem-Cz-beta-at2332 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (Sw34 ∷ CCZ013 ∷ []) (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 (lit c4))

-- Cz-beta @243243: 7 steps
lem-Cz-beta-at243243 : Ws → ⟪ (CCZ014 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ014 ∷ []) ⟫ʷ
lem-Cz-beta-at243243 c4 = derive (CCZ014 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q66 c4) ∷
   rw 2 (q67 c4) ∷
   rw 1 (q68 c4) ∷
   rw 0 (q56 c4) ∷
   rw 1 (q69 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q70 : Ws → Eqn
  q70 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (Sw12 ∷ Bx0-2413 ∷ []) (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (CCZ014 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ []) (lem-Cz-beta-at243243 c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4))

-- Cz-beta @12243143: 7 steps
lem-Cz-beta-at12243143 : Ws → ⟪ (CCZ024 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ CCZ024 ∷ []) ⟫ʷ
lem-Cz-beta-at12243143 c4 = derive (CCZ024 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q70 c4) ∷
   rw 2 (q71 c4) ∷
   rw 1 (q72 c4) ∷
   rw 0 (q59 c4) ∷
   rw 1 (q73 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q74 : Ws → Eqn
  q74 c4 = eqn (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (Sw23 ∷ Bx0-3412 ∷ []) (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (CCZ024 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ CCZ024 ∷ []) (lem-Cz-beta-at12243143 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 (lit c4))

-- Cz-beta @13243142: 7 steps
lem-Cz-beta-at13243142 : Ws → ⟪ (CCZ034 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ CCZ034 ∷ []) ⟫ʷ
lem-Cz-beta-at13243142 c4 = derive (CCZ034 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q74 c4) ∷
   rw 2 (q75 c4) ∷
   rw 1 (q76 c4) ∷
   rw 0 (q62 c4) ∷
   rw 1 (q77 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q78 : Ws → Eqn
  q78 c4 = eqn (Sw34 ∷ Bx0-1234 ∷ []) (Bx0-1243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1234⟩ (lit c4))

-- sym23 @243243: 5 steps
lem-sym23-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-sym23-at243243 c4 = derive (Bx0-1423 ∷ []) (Bx0-1243 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q67 c4) ∷
   rw 1 (q18 c4) ∷
   rw 0 (q78 c4) ∷
   rw 1 (q50 c4) ∷ []) Eq.refl

private
  q79 : Ws → Eqn
  q79 c4 = eqn (Bx0-1423 ∷ []) (Bx0-1243 ∷ []) (lem-sym23-at243243 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (Sw12 ∷ Bx0-1243 ∷ []) (Bx0-2143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1243⟩ (lit c4))

-- sym23 @12243143: 5 steps
lem-sym23-at12243143 : Ws → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-sym23-at12243143 c4 = derive (Bx0-2413 ∷ []) (Bx0-2143 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q71 c4) ∷
   rw 1 (q79 c4) ∷
   rw 0 (q80 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = eqn (Bx0-2413 ∷ []) (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4)

-- sym23 @13243142: 5 steps
lem-sym23-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-sym23-at13243142 c4 = derive (Bx0-3412 ∷ []) (Bx0-3142 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q75 c4) ∷
   rw 1 (q81 c4) ∷
   rw 0 (q55 c4) ∷
   rw 1 (q5 c4) ∷ []) Eq.refl

private
  q82 : Ws → Eqn
  q82 c4 = eqn (Bx0-1243 ∷ []) (Bx0-1234 ∷ []) (lem-sym34-at3443 c4)

-- sym34 @12213443: 5 steps
lem-sym34-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-sym34-at12213443 c4 = derive (Bx0-2143 ∷ []) (Bx0-2134 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q57 c4) ∷
   rw 1 (q82 c4) ∷
   rw 0 (q19 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q83 : Ws → Eqn
  q83 c4 = eqn (Bx0-2143 ∷ []) (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (Sw23 ∷ Bx0-2134 ∷ []) (Bx0-3124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2134⟩ (lit c4))

-- sym34 @13213442: 5 steps
lem-sym34-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-sym34-at13213442 c4 = derive (Bx0-3142 ∷ []) (Bx0-3124 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q60 c4) ∷
   rw 1 (q83 c4) ∷
   rw 0 (q84 c4) ∷
   rw 1 (q5 c4) ∷ []) Eq.refl

private
  q85 : Ws → Eqn
  q85 c4 = eqn (Bx0-1324 ∷ []) (Bx0-1342 ∷ []) (lem-sym34-at2332 c4)
  q86 : Ws → Eqn
  q86 c4 = eqn (Bx0-1342 ∷ []) (Bx0-3142 ∷ []) (lem-sym12-at233442 c4)
  q87 : Ws → Eqn
  q87 c4 = eqn (Bx0-3142 ∷ []) (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (CCZ034 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ CCZ034 ∷ []) (lem-Cz-beta-at13243142 c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (Bx0-3412 ∷ []) (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (Bx0-3142 ∷ []) (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4)
  q91 : Ws → Eqn
  q91 c4 = eqn (Bx0-3124 ∷ []) (Bx0-1324 ∷ []) (lem-sym12-at132132 c4)

-- auto BOX(0;1234) | CCZ034: 9 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ034 : Ws → ⟪ (Bx0-1234 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ034 c4 = derive (Bx0-1234 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx0-1234 ∷ [])
  (rw 0 (q17 c4) ∷
   rw 0 (q85 c4) ∷
   rw 0 (q86 c4) ∷
   rw 0 (q87 c4) ∷
   rw⁻ 0 (q88 c4) ∷
   rw 1 (q89 c4) ∷
   rw 1 (q90 c4) ∷
   rw 1 (q91 c4) ∷
   rw 1 (q18 c4) ∷ []) Eq.refl

private
  q92 : Ws → Eqn
  q92 c4 = eqn (CCZ234 ∷ []) (CCZ234 ∷ []) (wl0255 (lit c4))

-- auto BOX(0;1234) | CCZ342: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342 : Ws → ⟪ (Bx0-1234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342 c4 = derive (Bx0-1234 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1234 ∷ [])
  (rw 1 (q92 c4) ∷
   rw 0 (q20 c4) ∷
   rw 0 (q21 c4) ∷
   rw⁻ 0 (q22 c4) ∷
   rw 1 (q23 c4) ∷
   rw 1 (q24 c4) ∷
   rw 0 (q92 c4) ∷ []) Eq.refl

private
  q93 : Ws → Eqn
  q93 c4 = eqn (Toff012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Toff012 ∷ []) (lem-T-beta c4)

-- auto BOX(0;1234) | TOFF012: 1 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF012 : Ws → ⟪ (Bx0-1234 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF012 c4 = derive (Bx0-1234 ∷ Toff012 ∷ []) (Toff012 ∷ Bx0-1234 ∷ [])
  (rw⁻ 0 (q93 c4) ∷ []) Eq.refl

private
  q94 : Ws → Eqn
  q94 c4 = eqn (CCZ013 ∷ []) (CCZ013 ∷ []) (wl0256 (lit c4))

-- auto BOX(0;1234) | CCZ103: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ103 : Ws → ⟪ (Bx0-1234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ103 c4 = derive (Bx0-1234 ∷ CCZ013 ∷ []) (CCZ013 ∷ Bx0-1234 ∷ [])
  (rw 1 (q94 c4) ∷
   rw 0 (q17 c4) ∷
   rw⁻ 0 (q68 c4) ∷
   rw 1 (q18 c4) ∷
   rw 0 (q94 c4) ∷ []) Eq.refl

private
  q95 : Ws → Eqn
  q95 c4 = eqn (Bx0-1324 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at2332 c4)
  q96 : Ws → Eqn
  q96 c4 = eqn (Sw12 ∷ Toff013 ∷ []) (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 (lit c4))

-- beta-T @122331: 8 steps
lem-beta-T-at122331 : Ws → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-beta-T-at122331 c4 = derive (Bx0-2314 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q13 c4) ∷
   rw 1 (q95 c4) ∷
   rw 0 (q96 c4) ∷
   rw 1 (q70 c4) ∷
   rw 2 (q96 c4) ∷
   rw 3 (q70 c4) ∷
   rw 4 (q11 c4) ∷ []) Eq.refl

private
  q97 : Ws → Eqn
  q97 c4 = eqn (Sw01 ∷ Bx1-0423 ∷ []) (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4))
  q98 : Ws → Eqn
  q98 c4 = eqn (Bx0-1423 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (Sw01 ∷ Toff014 ∷ []) (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 (lit c4))
  q100 : Ws → Eqn
  q100 c4 = eqn (CCZ123 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ []) (wl0103 (lit c4))

-- beta-T @0110243243: 8 steps
lem-beta-T-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) ⟫ʷ
lem-beta-T-at0110243243 c4 = derive (Bx1-0423 ∷ []) (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q97 c4) ∷
   rw 1 (q98 c4) ∷
   rw 0 (q99 c4) ∷
   rw⁻ 1 (q100 c4) ∷
   rw 2 (q99 c4) ∷
   rw⁻ 3 (q100 c4) ∷
   rw 4 (q25 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = eqn (Sw01 ∷ Bx0-1243 ∷ []) (Bx1-0243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1243⟩ (lit c4))

-- sym23 @0110243243: 5 steps
lem-sym23-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ []) ⟫ʷ
lem-sym23-at0110243243 c4 = derive (Bx1-0423 ∷ []) (Bx1-0243 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q97 c4) ∷
   rw 1 (q79 c4) ∷
   rw 0 (q101 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

private
  q102 : Ws → Eqn
  q102 c4 = eqn (Sw01 ∷ Bx0-2314 ∷ []) (Bx1-2304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2314⟩ (lit c4))

-- sym23 @011220: 5 steps
lem-sym23-at011220 : Ws → ⟪ (Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ []) ⟫ʷ
lem-sym23-at011220 c4 = derive (Bx1-2034 ∷ []) (Bx1-2304 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q30 c4) ∷
   rw 1 (q21 c4) ∷
   rw 0 (q102 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

private
  q103 : Ws → Eqn
  q103 c4 = eqn (Sw23 ∷ Toff213 ∷ []) (Toff312 ∷ Sw23 ∷ []) (wl0158 (lit c4))
  q104 : Ws → Eqn
  q104 c4 = eqn (Toff312 ∷ Bx0-1234 ∷ Toff312 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ []) (lem-T312-beta c4)

-- T312-beta @2332: 8 steps
lem-T312-beta-at2332 : Ws → ⟪ (Toff213 ∷ Bx0-1324 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ134 ∷ []) ⟫ʷ
lem-T312-beta-at2332 c4 = derive (Toff213 ∷ Bx0-1324 ∷ Toff213 ∷ []) (Bx0-1324 ∷ CCZ134 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q103 c4) ∷
   rw 2 (q7 c4) ∷
   rw 3 (q103 c4) ∷
   rw 1 (q104 c4) ∷
   rw 0 (q9 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q105 : Ws → Eqn
  q105 c4 = eqn (Sw12 ∷ Toff123 ∷ []) (Toff213 ∷ Sw12 ∷ []) (wl0146 (lit c4))
  q106 : Ws → Eqn
  q106 c4 = eqn (Toff213 ∷ Bx0-1324 ∷ Toff213 ∷ []) (Bx0-1324 ∷ CCZ134 ∷ []) (lem-T312-beta-at2332 c4)

-- T312-beta @122331: 8 steps
lem-T312-beta-at122331 : Ws → ⟪ (Toff123 ∷ Bx0-2314 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CCZ234 ∷ []) ⟫ʷ
lem-T312-beta-at122331 c4 = derive (Toff123 ∷ Bx0-2314 ∷ Toff123 ∷ []) (Bx0-2314 ∷ CCZ234 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q105 c4) ∷
   rw 2 (q13 c4) ∷
   rw 3 (q105 c4) ∷
   rw 1 (q106 c4) ∷
   rw 0 (q15 c4) ∷
   rw⁻ 1 (q16 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q107 : Ws → Eqn
  q107 c4 = eqn (Sw01 ∷ Toff023 ∷ []) (Toff123 ∷ Sw01 ∷ []) (wl0108 (lit c4))
  q108 : Ws → Eqn
  q108 c4 = eqn (Sw01 ∷ Bx1-2304 ∷ []) (Bx0-2314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2304⟩ (lit c4))
  q109 : Ws → Eqn
  q109 c4 = eqn (Toff123 ∷ Bx0-2314 ∷ Toff123 ∷ []) (Bx0-2314 ∷ CCZ234 ∷ []) (lem-T312-beta-at122331 c4)
  q110 : Ws → Eqn
  q110 c4 = eqn (Sw01 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ))

-- T312-beta @01122330: 8 steps
lem-T312-beta-at01122330 : Ws → ⟪ (Toff023 ∷ Bx1-2304 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ CCZ234 ∷ []) ⟫ʷ
lem-T312-beta-at01122330 c4 = derive (Toff023 ∷ Bx1-2304 ∷ Toff023 ∷ []) (Bx1-2304 ∷ CCZ234 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q107 c4) ∷
   rw 2 (q108 c4) ∷
   rw 3 (q107 c4) ∷
   rw 1 (q109 c4) ∷
   rw 0 (q102 c4) ∷
   rw 1 (q110 c4) ∷
   rw 2 (q25 c4) ∷ []) Eq.refl

-- sym23 @01122330: 5 steps
lem-sym23-at01122330 : Ws → ⟪ (Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ []) ⟫ʷ
lem-sym23-at01122330 c4 = derive (Bx1-2304 ∷ []) (Bx1-2034 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q108 c4) ∷
   rw 1 (q23 c4) ∷
   rw 0 (q28 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

private
  q111 : Ws → Eqn
  q111 c4 = eqn (Bx0-2134 ∷ []) (Bx0-2143 ∷ []) (lem-sym34-at1221 c4)
  q112 : Ws → Eqn
  q112 c4 = eqn (Sw01 ∷ Bx0-2143 ∷ []) (Bx1-2043 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2143⟩ (lit c4))

-- sym34 @011220: 5 steps
lem-sym34-at011220 : Ws → ⟪ (Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2043 ∷ []) ⟫ʷ
lem-sym34-at011220 c4 = derive (Bx1-2034 ∷ []) (Bx1-2043 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q30 c4) ∷
   rw 1 (q111 c4) ∷
   rw 0 (q112 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

-- sym12 @12213443: 5 steps
lem-sym12-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-sym12-at12213443 c4 = derive (Bx0-2143 ∷ []) (Bx0-1243 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q57 c4) ∷
   rw 1 (q54 c4) ∷
   rw 0 (q57 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q113 : Ws → Eqn
  q113 c4 = eqn (Sw01 ∷ Bx1-2043 ∷ []) (Bx0-2143 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2043⟩ (lit c4))
  q114 : Ws → Eqn
  q114 c4 = eqn (Bx0-2143 ∷ []) (Bx0-1243 ∷ []) (lem-sym12-at12213443 c4)

-- sym12 @0112203443: 5 steps
lem-sym12-at0112203443 : Ws → ⟪ (Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ []) ⟫ʷ
lem-sym12-at0112203443 c4 = derive (Bx1-2043 ∷ []) (Bx1-0243 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q113 c4) ∷
   rw 1 (q114 c4) ∷
   rw 0 (q101 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

private
  q115 : Ws → Eqn
  q115 c4 = eqn (Sw01 ∷ Bx1-0243 ∷ []) (Bx0-1243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0243⟩ (lit c4))
  q116 : Ws → Eqn
  q116 c4 = eqn (Sw01 ∷ Bx0-1423 ∷ []) (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4))

-- sym23 @01103443: 5 steps
lem-sym23-at01103443 : Ws → ⟪ (Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ []) ⟫ʷ
lem-sym23-at01103443 c4 = derive (Bx1-0243 ∷ []) (Bx1-0423 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q115 c4) ∷
   rw 1 (q58 c4) ∷
   rw 0 (q116 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

private
  q117 : Ws → Eqn
  q117 c4 = eqn (Bx0-1234 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ034 c4)

-- auto BOX(0;1234) | CCZ034 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at2332 c4 = derive (Bx0-1324 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q7 c4) ∷
   rw 2 (q77 c4) ∷
   rw 1 (q117 c4) ∷
   rw 0 (q74 c4) ∷
   rw 1 (q9 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q118 : Ws → Eqn
  q118 c4 = eqn (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 (lit c4))
  q119 : Ws → Eqn
  q119 c4 = eqn (Bx0-1324 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at2332 c4)
  q120 : Ws → Eqn
  q120 c4 = eqn (Sw34 ∷ CCZ024 ∷ []) (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 (lit c4))

-- auto BOX(0;1234) | CCZ034 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at243243 : Ws → ⟪ (Bx0-1423 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at243243 c4 = derive (Bx0-1423 ∷ CCZ023 ∷ []) (CCZ023 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q67 c4) ∷
   rw 2 (q118 c4) ∷
   rw 1 (q119 c4) ∷
   rw 0 (q120 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q121 : Ws → Eqn
  q121 c4 = eqn (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ []) (wl0003 (lit c4))
  q122 : Ws → Eqn
  q122 c4 = eqn (Bx0-1423 ∷ CCZ023 ∷ []) (CCZ023 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at243243 c4)

-- auto BOX(0;1234) | CCZ034 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at0110243243 c4 = derive (Bx1-0423 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q97 c4) ∷
   rw⁻ 2 (q121 c4) ∷
   rw 1 (q122 c4) ∷
   rw⁻ 0 (q100 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q25 c4) ∷ []) Eq.refl

private
  q123 : Ws → Eqn
  q123 c4 = eqn (Sw34 ∷ CCZ123 ∷ []) (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 (lit c4))
  q124 : Ws → Eqn
  q124 c4 = eqn (CCZ013 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at2332 c4)
  q125 : Ws → Eqn
  q125 c4 = eqn (Sw34 ∷ CCZ124 ∷ []) (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 (lit c4))

-- auto CCZ012 | CCZ314 @243243: 7 steps
lem-auto-CCZ012-∣-CCZ314-at243243 : Ws → ⟪ (CCZ014 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ314-at243243 c4 = derive (CCZ014 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q66 c4) ∷
   rw 2 (q123 c4) ∷
   rw 1 (q124 c4) ∷
   rw 0 (q125 c4) ∷
   rw 1 (q69 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = eqn (CCZ123 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ123 ∷ []) (wl0111 (lit c4))
  q127 : Ws → Eqn
  q127 c4 = eqn (CCZ014 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at243243 c4)

-- auto CCZ012 | CCZ314 @12243143: 7 steps
lem-auto-CCZ012-∣-CCZ314-at12243143 : Ws → ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ314-at12243143 c4 = derive (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q70 c4) ∷
   rw⁻ 2 (q126 c4) ∷
   rw 1 (q127 c4) ∷
   rw⁻ 0 (q126 c4) ∷
   rw 1 (q73 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q128 : Ws → Eqn
  q128 c4 = eqn (CCZ234 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ234 ∷ []) (wl0086 (lit c4))
  q129 : Ws → Eqn
  q129 c4 = eqn (Bx0-1234 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342 c4)

-- auto BOX(0;1234) | CCZ342 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at2332 c4 = derive (Bx0-1324 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q7 c4) ∷
   rw⁻ 2 (q128 c4) ∷
   rw 1 (q129 c4) ∷
   rw⁻ 0 (q128 c4) ∷
   rw 1 (q9 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q130 : Ws → Eqn
  q130 c4 = eqn (CCZ234 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ234 ∷ []) (wl0155 (lit c4))
  q131 : Ws → Eqn
  q131 c4 = eqn (Bx0-1324 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at2332 c4)

-- auto BOX(0;1234) | CCZ342 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at243243 : Ws → ⟪ (Bx0-1423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at243243 c4 = derive (Bx0-1423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q67 c4) ∷
   rw⁻ 2 (q130 c4) ∷
   rw 1 (q131 c4) ∷
   rw⁻ 0 (q130 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q132 : Ws → Eqn
  q132 c4 = eqn (Bx0-1423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at243243 c4)

-- auto BOX(0;1234) | CCZ342 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at0110243243 c4 = derive (Bx1-0423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q97 c4) ∷
   rw 2 (q110 c4) ∷
   rw 1 (q132 c4) ∷
   rw 0 (q110 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q25 c4) ∷ []) Eq.refl

private
  q133 : Ws → Eqn
  q133 c4 = eqn (Sw23 ∷ Toff013 ∷ []) (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 (lit c4))
  q134 : Ws → Eqn
  q134 c4 = eqn (Bx0-1234 ∷ Toff012 ∷ []) (Toff012 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012 c4)
  q135 : Ws → Eqn
  q135 c4 = eqn (Sw23 ∷ Toff012 ∷ []) (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4))

-- auto BOX(0;1234) | TOFF012 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at2332 : Ws → ⟪ (Bx0-1324 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at2332 c4 = derive (Bx0-1324 ∷ Toff013 ∷ []) (Toff013 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q7 c4) ∷
   rw 2 (q133 c4) ∷
   rw 1 (q134 c4) ∷
   rw 0 (q135 c4) ∷
   rw 1 (q9 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q136 : Ws → Eqn
  q136 c4 = eqn (Sw34 ∷ Toff014 ∷ []) (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 (lit c4))
  q137 : Ws → Eqn
  q137 c4 = eqn (Bx0-1324 ∷ Toff013 ∷ []) (Toff013 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at2332 c4)
  q138 : Ws → Eqn
  q138 c4 = eqn (Sw34 ∷ Toff013 ∷ []) (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 (lit c4))

-- auto BOX(0;1234) | TOFF012 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at243243 : Ws → ⟪ (Bx0-1423 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at243243 c4 = derive (Bx0-1423 ∷ Toff014 ∷ []) (Toff014 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q67 c4) ∷
   rw 2 (q136 c4) ∷
   rw 1 (q137 c4) ∷
   rw 0 (q138 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q139 : Ws → Eqn
  q139 c4 = eqn (Sw01 ∷ Toff104 ∷ []) (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 (lit c4))
  q140 : Ws → Eqn
  q140 c4 = eqn (Bx0-1423 ∷ Toff014 ∷ []) (Toff014 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at243243 c4)

-- auto BOX(0;1234) | TOFF012 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at0110243243 c4 = derive (Bx1-0423 ∷ Toff104 ∷ []) (Toff104 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q97 c4) ∷
   rw 2 (q139 c4) ∷
   rw 1 (q140 c4) ∷
   rw 0 (q99 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q25 c4) ∷ []) Eq.refl

private
  q141 : Ws → Eqn
  q141 c4 = eqn (Bx0-1234 ∷ CCZ013 ∷ []) (CCZ013 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ103 c4)

-- auto BOX(0;1234) | CCZ103 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at2332 c4 = derive (Bx0-1324 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q7 c4) ∷
   rw 2 (q65 c4) ∷
   rw 1 (q141 c4) ∷
   rw 0 (q63 c4) ∷
   rw 1 (q9 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q142 : Ws → Eqn
  q142 c4 = eqn (CCZ012 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (Swap))
  q143 : Ws → Eqn
  q143 c4 = eqn (Bx0-1324 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at2332 c4)

-- auto BOX(0;1234) | CCZ103 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at243243 : Ws → ⟪ (Bx0-1423 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at243243 c4 = derive (Bx0-1423 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q67 c4) ∷
   rw⁻ 2 (q142 c4) ∷
   rw 1 (q143 c4) ∷
   rw⁻ 0 (q142 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q144 : Ws → Eqn
  q144 c4 = eqn (CCZ012 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ012 ∷ []) (wl0096 (lit c4))
  q145 : Ws → Eqn
  q145 c4 = eqn (Bx0-1423 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at243243 c4)

-- auto BOX(0;1234) | CCZ103 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at0110243243 c4 = derive (Bx1-0423 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q97 c4) ∷
   rw⁻ 2 (q144 c4) ∷
   rw 1 (q145 c4) ∷
   rw⁻ 0 (q144 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q25 c4) ∷ []) Eq.refl

private
  q146 : Ws → Eqn
  q146 c4 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wl0031 (lit c4))
  q147 : Ws → Eqn
  q147 c4 = eqn (Sw01 ∷ Bx1-0234 ∷ []) (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4))
  q148 : Ws → Eqn
  q148 c4 = eqn (K0⁻ ∷ Sw01 ∷ []) (Sw01 ∷ K1⁻ ∷ []) (wl0257 (lit c4))
  q149 : Ws → Eqn
  q149 c4 = eqn (K0 ∷ Bx0-1234 ∷ K0⁻ ∷ []) (Bx0-1234 ∷ []) (lem-K0-pass c4)
  q150 : Ws → Eqn
  q150 c4 = eqn (Sw01 ∷ Bx0-1234 ∷ []) (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4))

-- K0-pass @0110: 7 steps
lem-K0-pass-at0110 : Ws → ⟪ (K1 ∷ Bx1-0234 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ []) ⟫ʷ
lem-K0-pass-at0110 c4 = derive (K1 ∷ Bx1-0234 ∷ K1⁻ ∷ []) (Bx1-0234 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw⁻ 1 (q146 c4) ∷
   rw 2 (q147 c4) ∷
   rw⁻ 3 (q148 c4) ∷
   rw 1 (q149 c4) ∷
   rw 0 (q150 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

private
  q151 : Ws → Eqn
  q151 c4 = eqn (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (Toff102 ∷ []) (wl0258 (lit c4))
  q152 : Ws → Eqn
  q152 c4 = eqn (Bx0-2314 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-beta-T-at122331 c4)
  q153 : Ws → Eqn
  q153 c4 = eqn (K1⁻ ∷ Toff023 ∷ []) (Toff023 ∷ K1⁻ ∷ []) (wl0259 (lit c4))
  q154 : Ws → Eqn
  q154 c4 = eqn (K1⁻ ∷ CCZ014 ∷ []) (Toff104 ∷ K1⁻ ∷ []) (wp0063 c4)
  q155 : Ws → Eqn
  q155 c4 = eqn (K1⁻ ∷ K1 ∷ []) [] (wl0260 (lit c4))
  q156 : Ws → Eqn
  q156 c4 = eqn (CCZ012 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ012 ∷ CCZ123 ∷ []) (wl0261 (lit c4))
  q157 : Ws → Eqn
  q157 c4 = eqn (Toff104 ∷ Toff104 ∷ []) [] (wp0064 c4)
  q158 : Ws → Eqn
  q158 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl0212 (lit c4))
  q159 : Ws → Eqn
  q159 c4 = eqn (Bx1-0423 ∷ []) (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) (lem-beta-T-at0110243243 c4)
  q160 : Ws → Eqn
  q160 c4 = eqn (CCZ012 ∷ Toff104 ∷ []) (Toff104 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp0065 c4)
  q161 : Ws → Eqn
  q161 c4 = eqn (CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ123 ∷ []) (wl0262 (lit c4))
  q162 : Ws → Eqn
  q162 c4 = eqn (Toff023 ∷ Toff023 ∷ []) [] (wl0263 (lit c4))
  q163 : Ws → Eqn
  q163 c4 = eqn (Bx1-0423 ∷ []) (Bx1-0243 ∷ []) (lem-sym23-at0110243243 c4)
  q164 : Ws → Eqn
  q164 c4 = eqn (Bx1-0243 ∷ []) (Bx1-0234 ∷ []) (lem-sym34-at01103443 c4)
  q165 : Ws → Eqn
  q165 c4 = eqn (Bx1-0234 ∷ []) (Bx1-2034 ∷ []) (lem-sym12-at0110 c4)
  q166 : Ws → Eqn
  q166 c4 = eqn (Bx1-2034 ∷ []) (Bx1-2304 ∷ []) (lem-sym23-at011220 c4)
  q167 : Ws → Eqn
  q167 c4 = eqn (Toff023 ∷ Bx1-2304 ∷ Toff023 ∷ []) (Bx1-2304 ∷ CCZ234 ∷ []) (lem-T312-beta-at01122330 c4)
  q168 : Ws → Eqn
  q168 c4 = eqn (Bx1-2304 ∷ []) (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4)
  q169 : Ws → Eqn
  q169 c4 = eqn (Bx1-2034 ∷ []) (Bx1-2043 ∷ []) (lem-sym34-at011220 c4)
  q170 : Ws → Eqn
  q170 c4 = eqn (Bx1-2043 ∷ []) (Bx1-0243 ∷ []) (lem-sym12-at0112203443 c4)
  q171 : Ws → Eqn
  q171 c4 = eqn (Bx1-0243 ∷ []) (Bx1-0423 ∷ []) (lem-sym23-at01103443 c4)
  q172 : Ws → Eqn
  q172 c4 = eqn (CCZ024 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp0066 c4)
  q173 : Ws → Eqn
  q173 c4 = eqn (CCZ123 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ123 ∷ []) (wl0264 (lit c4))
  q174 : Ws → Eqn
  q174 c4 = eqn (Bx1-0423 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at0110243243 c4)
  q175 : Ws → Eqn
  q175 c4 = eqn (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at12243143 c4)
  q176 : Ws → Eqn
  q176 c4 = eqn (Bx1-0423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at0110243243 c4)
  q177 : Ws → Eqn
  q177 c4 = eqn (CCZ234 ∷ CCZ234 ∷ []) [] (wl0265 (lit c4))
  q178 : Ws → Eqn
  q178 c4 = eqn (Bx1-0423 ∷ Toff104 ∷ []) (Toff104 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at0110243243 c4)
  q179 : Ws → Eqn
  q179 c4 = eqn (CCZ024 ∷ Toff104 ∷ []) (Toff104 ∷ CCZ024 ∷ []) (wp0067 c4)
  q180 : Ws → Eqn
  q180 c4 = eqn (Bx1-0423 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at0110243243 c4)
  q181 : Ws → Eqn
  q181 c4 = eqn (CCZ012 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ012 ∷ []) (wp0068 c4)
  q182 : Ws → Eqn
  q182 c4 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wl0183 (lit c4))
  q183 : Ws → Eqn
  q183 c4 = eqn (CCZ024 ∷ CCZ024 ∷ []) [] (wp0034 c4)
  q184 : Ws → Eqn
  q184 c4 = eqn (K1 ∷ Toff023 ∷ []) (Toff023 ∷ K1 ∷ []) (wl0266 (lit c4))
  q185 : Ws → Eqn
  q185 c4 = eqn (CCZ014 ∷ K1 ∷ []) (K1 ∷ Toff104 ∷ []) (wp0069 c4)
  q186 : Ws → Eqn
  q186 c4 = eqn (CCZ014 ∷ []) (K1 ∷ Toff104 ∷ K1⁻ ∷ []) (wp0070 c4)
  q187 : Ws → Eqn
  q187 c4 = eqn (K1 ∷ Bx1-0234 ∷ K1⁻ ∷ []) (Bx1-0234 ∷ []) (lem-K0-pass-at0110 c4)

-- TW: 54 steps
lem-TW : Ws → ⟪ (Toff102 ∷ Bx0-1234 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-TW c4 = derive (Toff102 ∷ Bx0-1234 ∷ Toff102 ∷ []) (Bx0-1234 ∷ Bx1-0234 ∷ [])
  (rw⁻ 0 (q151 c4) ∷
   rw⁻ 4 (q151 c4) ∷
   rw 3 (q20 c4) ∷
   rw 3 (q21 c4) ∷
   rw 3 (q152 c4) ∷
   rw 2 (q153 c4) ∷
   rw 3 (q154 c4) ∷
   rw 4 (q153 c4) ∷
   rw 5 (q154 c4) ∷
   rw 6 (q155 c4) ∷
   rw 1 (q156 c4) ∷
   rw⁻ 3 (q157 c4) ∷
   rw⁻ 7 (q158 c4) ∷
   rw⁻ 4 (q159 c4) ∷
   rw 2 (q160 c4) ∷
   rw 6 (q161 c4) ∷
   rw⁻ 5 (q162 c4) ∷
   rw 7 (q163 c4) ∷
   rw 7 (q164 c4) ∷
   rw 7 (q165 c4) ∷
   rw 7 (q166 c4) ∷
   rw 6 (q167 c4) ∷
   rw 6 (q168 c4) ∷
   rw 6 (q169 c4) ∷
   rw 6 (q170 c4) ∷
   rw 6 (q171 c4) ∷
   rw 4 (q172 c4) ∷
   rw 3 (q156 c4) ∷
   rw⁻ 9 (q173 c4) ∷
   rw 8 (q174 c4) ∷
   rw⁻ 7 (q173 c4) ∷
   rw 6 (q175 c4) ∷
   rw 5 (q158 c4) ∷
   rw 7 (q176 c4) ∷
   rw 6 (q177 c4) ∷
   rw 6 (q178 c4) ∷
   rw 5 (q179 c4) ∷
   rw 4 (q160 c4) ∷
   rw 8 (q180 c4) ∷
   rw⁻ 7 (q181 c4) ∷
   rw⁻ 6 (q181 c4) ∷
   rw 5 (q182 c4) ∷
   rw 5 (q183 c4) ∷
   rw⁻ 5 (q155 c4) ∷
   rw 0 (q184 c4) ∷
   rw⁻ 1 (q185 c4) ∷
   rw 2 (q184 c4) ∷
   rw⁻ 3 (q186 c4) ∷
   rw⁻ 0 (q152 c4) ∷
   rw 0 (q23 c4) ∷
   rw 0 (q24 c4) ∷
   rw 2 (q163 c4) ∷
   rw 2 (q164 c4) ∷
   rw 1 (q187 c4) ∷ []) Eq.refl

-- sym34 @233442: 5 steps
lem-sym34-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-sym34-at233442 c4 = derive (Bx0-1342 ∷ []) (Bx0-1324 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q53 c4) ∷
   rw 1 (q82 c4) ∷
   rw 0 (q9 c4) ∷
   rw 1 (q5 c4) ∷ []) Eq.refl

private
  q188 : Ws → Eqn
  q188 c4 = eqn (Sw12 ∷ Bx0-2341 ∷ []) (Bx0-1342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2341⟩ (lit c4))
  q189 : Ws → Eqn
  q189 c4 = eqn (Bx0-1342 ∷ []) (Bx0-1324 ∷ []) (lem-sym34-at233442 c4)

-- sym34 @12233441: 5 steps
lem-sym34-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-sym34-at12233441 c4 = derive (Bx0-2341 ∷ []) (Bx0-2314 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q188 c4) ∷
   rw 1 (q189 c4) ∷
   rw 0 (q15 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q190 : Ws → Eqn
  q190 c4 = eqn (Sw12 ∷ CS01 ∷ []) (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4))
  q191 : Ws → Eqn
  q191 c4 = eqn (CS02 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02 ∷ []) (lem-CS20-beta-c c4)
  q192 : Ws → Eqn
  q192 c4 = eqn (Sw12 ∷ CS02 ∷ []) (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4))

-- CS20-beta-c @1221: 7 steps
lem-CS20-beta-c-at1221 : Ws → ⟪ (CS01 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CS01 ∷ []) ⟫ʷ
lem-CS20-beta-c-at1221 c4 = derive (CS01 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CS01 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q190 c4) ∷
   rw 2 (q35 c4) ∷
   rw 1 (q191 c4) ∷
   rw 0 (q19 c4) ∷
   rw 1 (q192 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q193 : Ws → Eqn
  q193 c4 = eqn (Sw12 ∷ Bx0-1342 ∷ []) (Bx0-2341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1342⟩ (lit c4))

-- sym34 @122331: 5 steps
lem-sym34-at122331 : Ws → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-sym34-at122331 c4 = derive (Bx0-2314 ∷ []) (Bx0-2341 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q13 c4) ∷
   rw 1 (q85 c4) ∷
   rw 0 (q193 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q194 : Ws → Eqn
  q194 c4 = eqn (Bx0-2341 ∷ []) (Bx0-2314 ∷ []) (lem-sym34-at12233441 c4)
  q195 : Ws → Eqn
  q195 c4 = eqn (CS01 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CS01 ∷ []) (lem-CS20-beta-c-at1221 c4)
  q196 : Ws → Eqn
  q196 c4 = eqn (Bx0-2314 ∷ []) (Bx0-2341 ∷ []) (lem-sym34-at122331 c4)

-- auto CS01 | BOX(0;2341): 5 steps
lem-auto-CS01-∣-BOX⟨0·2341⟩ : Ws → ⟪ (CS01 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨0·2341⟩ c4 = derive (CS01 ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ CS01 ∷ [])
  (rw 1 (q194 c4) ∷
   rw 1 (q23 c4) ∷
   rw 0 (q195 c4) ∷
   rw 0 (q21 c4) ∷
   rw 0 (q196 c4) ∷ []) Eq.refl

private
  q197 : Ws → Eqn
  q197 c4 = eqn (CS01 ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨0·2341⟩ c4)
  q198 : Ws → Eqn
  q198 c4 = eqn (CS01 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS01 ∷ []) (axAX)

-- AX-SB: 8 steps
lem-AX-SB : Ws → ⟪ (CS01 ∷ Sb0-2-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-34-1 ∷ CS01 ∷ []) ⟫ʷ
lem-AX-SB c4 = derive (CS01 ∷ Sb0-2-34-1 ∷ []) (Sb0-2-34-1 ∷ CS01 ∷ [])
  (re 1 1 (Bx0-2341 ∷ Toff134 ∷ Sb0-2-1-4 ∷ Toff134 ∷ Sb⁻0-2-1-4 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw 0 (q197 c4) ∷
   rw 1 (q198 c4) ∷
   re 2 1 (Sb0-2-1-4 ∷ []) ∷
   re 4 1 (Sb⁻0-2-1-4 ∷ []) ∷
   re 0 5 (Sb0-2-34-1 ∷ []) ∷ []) Eq.refl

private
  q199 : Ws → Eqn
  q199 c4 = eqn (Sw12 ∷ Bx2-0413 ∷ []) (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4))
  q200 : Ws → Eqn
  q200 c4 = eqn (Sw12 ∷ Bx1-0243 ∷ []) (Bx2-0143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0243⟩ (lit c4))

-- sym23 @0210243143: 5 steps
lem-sym23-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-sym23-at0210243143 c4 = derive (Bx2-0413 ∷ []) (Bx2-0143 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q199 c4) ∷
   rw 1 (q163 c4) ∷
   rw 0 (q200 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q201 : Ws → Eqn
  q201 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q202 : Ws → Eqn
  q202 c4 = eqn (Toff314 ∷ []) (Toff314 ∷ []) (wl0267 (lit c4))

-- SBsym: 9 steps
lem-SBsym : Ws → ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-14-3 ∷ []) ⟫ʷ
lem-SBsym c4 = derive (Sb2-0-41-3 ∷ []) (Sb2-0-14-3 ∷ [])
  (re 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 2 1 (CS03 ∷ []) ∷
   re 4 1 (CS03⁻ ∷ []) ∷
   rw 0 (q201 c4) ∷
   rw 1 (q202 c4) ∷
   rw 3 (q202 c4) ∷
   re 2 1 (Sb2-0-3-4 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-4 ∷ []) ∷
   re 0 5 (Sb2-0-14-3 ∷ []) ∷ []) Eq.refl

private
  q203 : Ws → Eqn
  q203 c4 = eqn (Toff201 ∷ Toff201 ∷ []) [] (wl0268 (lit c4))
  q204 : Ws → Eqn
  q204 c4 = eqn (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ CZ03 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ []) [] (wp0071 c4)
  q205 : Ws → Eqn
  q205 c4 = eqn (Toff314 ∷ Toff314 ∷ []) [] (wl0248 (lit c4))
  q206 : Ws → Eqn
  q206 c4 = eqn (CS03 ∷ CS03⁻ ∷ []) [] (wl0250 (lit c4))
  q207 : Ws → Eqn
  q207 c4 = eqn (CS03⁻ ∷ CS03 ∷ []) [] (wl0249 (lit c4))
  q208 : Ws → Eqn
  q208 c4 = eqn (Sb2-0-41-3 ∷ []) (Sb2-0-14-3 ∷ []) (lem-SBsym c4)
  q209 : Ws → Eqn
  q209 c4 = eqn (Toff204 ∷ Toff204 ∷ []) [] (wp0059 c4)
  q210 : Ws → Eqn
  q210 c4 = eqn (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) [] (wl0247 (lit c4))

-- SBsymd: 61 steps
lem-SBsymd : Ws → ⟪ (Sb⁻2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-14-3 ∷ []) ⟫ʷ
lem-SBsymd c4 = derive (Sb⁻2-0-41-3 ∷ []) (Sb⁻2-0-14-3 ∷ [])
  (rw⁻ 1 (q182 c4) ∷
   rw⁻ 2 (q203 c4) ∷
   rw⁻ 3 (q204 c4) ∷
   re 5 1 (Bx2-03 ∷ []) ∷
   re 8 1 (Bx2-03 ∷ []) ∷
   re 3 6 (Bx0-243 ∷ []) ∷
   re 4 1 (Bx⁻2-03 ∷ []) ∷
   re 7 1 (Bx⁻2-03 ∷ []) ∷
   re 4 6 (Bx⁻0-243 ∷ []) ∷
   rw⁻ 4 (q203 c4) ∷
   rw⁻ 5 (q182 c4) ∷
   rw⁻ 6 (q204 c4) ∷
   re 8 1 (Bx2-03 ∷ []) ∷
   re 11 1 (Bx2-03 ∷ []) ∷
   re 6 6 (Bx0-243 ∷ []) ∷
   re 7 1 (Bx⁻2-03 ∷ []) ∷
   re 10 1 (Bx⁻2-03 ∷ []) ∷
   re 7 6 (Bx⁻0-243 ∷ []) ∷
   re 1 6 (Bx2-0143 ∷ []) ∷
   re 2 6 (Bx⁻2-0143 ∷ []) ∷
   rw⁻ 2 (q205 c4) ∷
   rw⁻ 3 (q206 c4) ∷
   re 3 1 (Sb2-0-3-4 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-4 ∷ []) ∷
   rw⁻ 4 (q205 c4) ∷
   rw⁻ 5 (q207 c4) ∷
   re 5 1 (Sb⁻2-0-3-4 ∷ []) ∷
   re 6 1 (Sb2-0-3-4 ∷ []) ∷
   re 1 5 (Sb2-0-14-3 ∷ []) ∷
   re 2 5 (Sb⁻2-0-14-3 ∷ []) ∷
   rw⁻ 1 (q208 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 0 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   re 4 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) ∷
   rw 9 (q183 c4) ∷
   rw 8 (q209 c4) ∷
   re 7 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   re 13 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 15 1 (CZ03 ∷ []) ∷
   re 18 1 (CZ03 ∷ []) ∷
   rw 7 (q210 c4) ∷
   rw 6 (q209 c4) ∷
   rw 5 (q183 c4) ∷
   re 4 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 12 1 (CZ03 ∷ []) ∷
   re 15 1 (CZ03 ∷ []) ∷
   rw 4 (q210 c4) ∷
   rw 3 (q205 c4) ∷
   re 2 1 (CS03⁻ ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   rw 2 (q207 c4) ∷
   rw 1 (q205 c4) ∷
   re 0 1 (CS03 ∷ []) ∷
   re 1 1 (CS03⁻ ∷ []) ∷
   rw 0 (q206 c4) ∷ []) Eq.refl

-- sym12 @2332: 5 steps
lem-sym12-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-sym12-at2332 c4 = derive (Bx0-1324 ∷ []) (Bx0-3124 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q7 c4) ∷
   rw 1 (q20 c4) ∷
   rw 0 (q84 c4) ∷
   rw 1 (q5 c4) ∷ []) Eq.refl

private
  q211 : Ws → Eqn
  q211 c4 = eqn (Bx0-1324 ∷ []) (Bx0-3124 ∷ []) (lem-sym12-at2332 c4)
  q212 : Ws → Eqn
  q212 c4 = eqn (Sw34 ∷ Bx0-3124 ∷ []) (Bx0-4123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3124⟩ (lit c4))

-- sym12 @243243: 5 steps
lem-sym12-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-sym12-at243243 c4 = derive (Bx0-1423 ∷ []) (Bx0-4123 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q67 c4) ∷
   rw 1 (q211 c4) ∷
   rw 0 (q212 c4) ∷
   rw 1 (q50 c4) ∷ []) Eq.refl

private
  q213 : Ws → Eqn
  q213 c4 = eqn (Bx0-1423 ∷ []) (Bx0-4123 ∷ []) (lem-sym12-at243243 c4)
  q214 : Ws → Eqn
  q214 c4 = eqn (Sw01 ∷ Bx0-4123 ∷ []) (Bx1-4023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4123⟩ (lit c4))

-- sym12 @0110243243: 5 steps
lem-sym12-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4023 ∷ []) ⟫ʷ
lem-sym12-at0110243243 c4 = derive (Bx1-0423 ∷ []) (Bx1-4023 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q97 c4) ∷
   rw 1 (q213 c4) ∷
   rw 0 (q214 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

private
  q215 : Ws → Eqn
  q215 c4 = eqn (Bx1-0423 ∷ []) (Bx1-4023 ∷ []) (lem-sym12-at0110243243 c4)
  q216 : Ws → Eqn
  q216 c4 = eqn (Sw12 ∷ Bx1-4023 ∷ []) (Bx2-4013 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4023⟩ (lit c4))

-- sym12 @0210243143: 5 steps
lem-sym12-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-sym12-at0210243143 c4 = derive (Bx2-0413 ∷ []) (Bx2-4013 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q199 c4) ∷
   rw 1 (q215 c4) ∷
   rw 0 (q216 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q217 : Ws → Eqn
  q217 c4 = eqn (Bx2-0413 ∷ []) (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4)
  q218 : Ws → Eqn
  q218 c4 = eqn (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp0072 c4)

-- SBtgt: 8 steps
lem-SBtgt : Ws → ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ []) ⟫ʷ
lem-SBtgt c4 = derive (Sb2-0-41-3 ∷ []) (Sb2-4-01-3 ∷ [])
  (re 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 2 1 (CS03 ∷ []) ∷
   re 4 1 (CS03⁻ ∷ []) ∷
   rw 0 (q217 c4) ∷
   rw⁻ 1 (q218 c4) ∷
   re 2 1 (Sb2-4-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 0 5 (Sb2-4-01-3 ∷ []) ∷ []) Eq.refl

private
  q219 : Ws → Eqn
  q219 c4 = eqn (Sw23 ∷ Bx⁻0-1324 ∷ []) (Bx⁻0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1324⟩ (lit c4))
  q220 : Ws → Eqn
  q220 c4 = eqn (Bx⁻0-1234 ∷ []) (Bx0-1234 ∷ []) (lem-BOXd-BOX c4)

-- BOXd-BOX @2332: 5 steps
lem-BOXd-BOX-at2332 : Ws → ⟪ (Bx⁻0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-BOXd-BOX-at2332 c4 = derive (Bx⁻0-1324 ∷ []) (Bx0-1324 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q219 c4) ∷
   rw 1 (q220 c4) ∷
   rw 0 (q9 c4) ∷
   rw 1 (q5 c4) ∷ []) Eq.refl

private
  q221 : Ws → Eqn
  q221 c4 = eqn (Sw34 ∷ Bx⁻0-1423 ∷ []) (Bx⁻0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·1423⟩ (lit c4))
  q222 : Ws → Eqn
  q222 c4 = eqn (Bx⁻0-1324 ∷ []) (Bx0-1324 ∷ []) (lem-BOXd-BOX-at2332 c4)

-- BOXd-BOX @243243: 5 steps
lem-BOXd-BOX-at243243 : Ws → ⟪ (Bx⁻0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-BOXd-BOX-at243243 c4 = derive (Bx⁻0-1423 ∷ []) (Bx0-1423 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q221 c4) ∷
   rw 1 (q222 c4) ∷
   rw 0 (q56 c4) ∷
   rw 1 (q50 c4) ∷ []) Eq.refl

private
  q223 : Ws → Eqn
  q223 c4 = eqn (Sw01 ∷ Bx⁻1-0423 ∷ []) (Bx⁻0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0423⟩ (lit c4))
  q224 : Ws → Eqn
  q224 c4 = eqn (Bx⁻0-1423 ∷ []) (Bx0-1423 ∷ []) (lem-BOXd-BOX-at243243 c4)

-- BOXd-BOX @0110243243: 5 steps
lem-BOXd-BOX-at0110243243 : Ws → ⟪ (Bx⁻1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ []) ⟫ʷ
lem-BOXd-BOX-at0110243243 c4 = derive (Bx⁻1-0423 ∷ []) (Bx1-0423 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q223 c4) ∷
   rw 1 (q224 c4) ∷
   rw 0 (q116 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

private
  q225 : Ws → Eqn
  q225 c4 = eqn (Sw12 ∷ Bx⁻2-0413 ∷ []) (Bx⁻1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0413⟩ (lit c4))
  q226 : Ws → Eqn
  q226 c4 = eqn (Bx⁻1-0423 ∷ []) (Bx1-0423 ∷ []) (lem-BOXd-BOX-at0110243243 c4)
  q227 : Ws → Eqn
  q227 c4 = eqn (Sw12 ∷ Bx1-0423 ∷ []) (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4))

-- BOXd-BOX @0210243143: 5 steps
lem-BOXd-BOX-at0210243143 : Ws → ⟪ (Bx⁻2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-BOXd-BOX-at0210243143 c4 = derive (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q225 c4) ∷
   rw 1 (q226 c4) ∷
   rw 0 (q227 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q228 : Ws → Eqn
  q228 c4 = eqn (Sw12 ∷ Bx⁻0-2134 ∷ []) (Bx⁻0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·2134⟩ (lit c4))

-- BOXd-BOX @1221: 5 steps
lem-BOXd-BOX-at1221 : Ws → ⟪ (Bx⁻0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-BOXd-BOX-at1221 c4 = derive (Bx⁻0-2134 ∷ []) (Bx0-2134 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q228 c4) ∷
   rw 1 (q220 c4) ∷
   rw 0 (q19 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q229 : Ws → Eqn
  q229 c4 = eqn (Sw23 ∷ Bx⁻0-3124 ∷ []) (Bx⁻0-2134 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·3124⟩ (lit c4))
  q230 : Ws → Eqn
  q230 c4 = eqn (Bx⁻0-2134 ∷ []) (Bx0-2134 ∷ []) (lem-BOXd-BOX-at1221 c4)

-- BOXd-BOX @132132: 5 steps
lem-BOXd-BOX-at132132 : Ws → ⟪ (Bx⁻0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-BOXd-BOX-at132132 c4 = derive (Bx⁻0-3124 ∷ []) (Bx0-3124 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q229 c4) ∷
   rw 1 (q230 c4) ∷
   rw 0 (q84 c4) ∷
   rw 1 (q5 c4) ∷ []) Eq.refl

private
  q231 : Ws → Eqn
  q231 c4 = eqn (Sw34 ∷ Bx⁻0-4123 ∷ []) (Bx⁻0-3124 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·4123⟩ (lit c4))
  q232 : Ws → Eqn
  q232 c4 = eqn (Bx⁻0-3124 ∷ []) (Bx0-3124 ∷ []) (lem-BOXd-BOX-at132132 c4)

-- BOXd-BOX @14213243: 5 steps
lem-BOXd-BOX-at14213243 : Ws → ⟪ (Bx⁻0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-BOXd-BOX-at14213243 c4 = derive (Bx⁻0-4123 ∷ []) (Bx0-4123 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q231 c4) ∷
   rw 1 (q232 c4) ∷
   rw 0 (q212 c4) ∷
   rw 1 (q50 c4) ∷ []) Eq.refl

private
  q233 : Ws → Eqn
  q233 c4 = eqn (Sw01 ∷ Bx⁻1-4023 ∷ []) (Bx⁻0-4123 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·4023⟩ (lit c4))
  q234 : Ws → Eqn
  q234 c4 = eqn (Bx⁻0-4123 ∷ []) (Bx0-4123 ∷ []) (lem-BOXd-BOX-at14213243 c4)

-- BOXd-BOX @0114203243: 5 steps
lem-BOXd-BOX-at0114203243 : Ws → ⟪ (Bx⁻1-4023 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4023 ∷ []) ⟫ʷ
lem-BOXd-BOX-at0114203243 c4 = derive (Bx⁻1-4023 ∷ []) (Bx1-4023 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q233 c4) ∷
   rw 1 (q234 c4) ∷
   rw 0 (q214 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

private
  q235 : Ws → Eqn
  q235 c4 = eqn (Sw12 ∷ Bx⁻2-4013 ∷ []) (Bx⁻1-4023 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·4013⟩ (lit c4))
  q236 : Ws → Eqn
  q236 c4 = eqn (Bx⁻1-4023 ∷ []) (Bx1-4023 ∷ []) (lem-BOXd-BOX-at0114203243 c4)

-- BOXd-BOX @0214203143: 5 steps
lem-BOXd-BOX-at0214203143 : Ws → ⟪ (Bx⁻2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-BOXd-BOX-at0214203143 c4 = derive (Bx⁻2-4013 ∷ []) (Bx2-4013 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q235 c4) ∷
   rw 1 (q236 c4) ∷
   rw 0 (q216 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q237 : Ws → Eqn
  q237 c4 = eqn (CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) (CS34 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ []) (wp0073 c4)
  q238 : Ws → Eqn
  q238 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q239 : Ws → Eqn
  q239 c4 = eqn (Bx⁻2-4013 ∷ []) (Bx2-4013 ∷ []) (lem-BOXd-BOX-at0214203143 c4)

-- SBtgtd: 10 steps
lem-SBtgtd : Ws → ⟪ (Sb⁻2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-01-3 ∷ []) ⟫ʷ
lem-SBtgtd c4 = derive (Sb⁻2-0-41-3 ∷ []) (Sb⁻2-4-01-3 ∷ [])
  (re 0 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 0 1 (CS03 ∷ []) ∷
   re 2 1 (CS03⁻ ∷ []) ∷
   rw 0 (q237 c4) ∷
   rw 4 (q238 c4) ∷
   rw 4 (q217 c4) ∷
   rw⁻ 4 (q239 c4) ∷
   re 0 1 (Sb2-4-3-1 ∷ []) ∷
   re 2 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 0 5 (Sb⁻2-4-01-3 ∷ []) ∷ []) Eq.refl

private
  q240 : Ws → Eqn
  q240 c4 = eqn (Sw12 ∷ Bx2-0134 ∷ []) (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4))
  q241 : Ws → Eqn
  q241 c4 = eqn (Sw12 ∷ Bx1-2034 ∷ []) (Bx2-1034 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2034⟩ (lit c4))

-- sym12 @021021: 5 steps
lem-sym12-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-sym12-at021021 c4 = derive (Bx2-0134 ∷ []) (Bx2-1034 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q240 c4) ∷
   rw 1 (q165 c4) ∷
   rw 0 (q241 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q242 : Ws → Eqn
  q242 c4 = eqn (Sw23 ∷ Bx3-0124 ∷ []) (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ (lit c4))
  q243 : Ws → Eqn
  q243 c4 = eqn (Bx2-0134 ∷ []) (Bx2-1034 ∷ []) (lem-sym12-at021021 c4)
  q244 : Ws → Eqn
  q244 c4 = eqn (Sw23 ∷ Bx2-1034 ∷ []) (Bx3-1024 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·1034⟩ (lit c4))

-- sym12 @03102132: 5 steps
lem-sym12-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-sym12-at03102132 c4 = derive (Bx3-0124 ∷ []) (Bx3-1024 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q242 c4) ∷
   rw 1 (q243 c4) ∷
   rw 0 (q244 c4) ∷
   rw 1 (q5 c4) ∷ []) Eq.refl

private
  q245 : Ws → Eqn
  q245 c4 = eqn (Sw01 ∷ Bx0-1324 ∷ []) (Bx1-0324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1324⟩ (lit c4))

-- sym23 @0110: 5 steps
lem-sym23-at0110 : Ws → ⟪ (Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ []) ⟫ʷ
lem-sym23-at0110 c4 = derive (Bx1-0234 ∷ []) (Bx1-0324 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q147 c4) ∷
   rw 1 (q17 c4) ∷
   rw 0 (q245 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

private
  q246 : Ws → Eqn
  q246 c4 = eqn (Bx1-0234 ∷ []) (Bx1-0324 ∷ []) (lem-sym23-at0110 c4)
  q247 : Ws → Eqn
  q247 c4 = eqn (Sw12 ∷ Bx1-0324 ∷ []) (Bx2-0314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0324⟩ (lit c4))

-- sym23 @021021: 5 steps
lem-sym23-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-sym23-at021021 c4 = derive (Bx2-0134 ∷ []) (Bx2-0314 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q240 c4) ∷
   rw 1 (q246 c4) ∷
   rw 0 (q247 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q248 : Ws → Eqn
  q248 c4 = eqn (Bx2-0134 ∷ []) (Bx2-0314 ∷ []) (lem-sym23-at021021 c4)
  q249 : Ws → Eqn
  q249 c4 = eqn (Sw23 ∷ Bx2-0314 ∷ []) (Bx3-0214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0314⟩ (lit c4))

-- sym23 @03102132: 5 steps
lem-sym23-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-sym23-at03102132 c4 = derive (Bx3-0124 ∷ []) (Bx3-0214 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q242 c4) ∷
   rw 1 (q248 c4) ∷
   rw 0 (q249 c4) ∷
   rw 1 (q5 c4) ∷ []) Eq.refl

private
  q250 : Ws → Eqn
  q250 c4 = eqn (Sw01 ∷ Bx3-1024 ∷ []) (Bx3-0124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1024⟩ (lit c4))
  q251 : Ws → Eqn
  q251 c4 = eqn (Bx3-0124 ∷ []) (Bx3-0214 ∷ []) (lem-sym23-at03102132 c4)
  q252 : Ws → Eqn
  q252 c4 = eqn (Sw01 ∷ Bx3-0214 ∷ []) (Bx3-1204 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0214⟩ (lit c4))

-- sym23 @032032: 5 steps
lem-sym23-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-sym23-at032032 c4 = derive (Bx3-1024 ∷ []) (Bx3-1204 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q250 c4) ∷
   rw 1 (q251 c4) ∷
   rw 0 (q252 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

private
  q253 : Ws → Eqn
  q253 c4 = eqn (Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T c4)
  q254 : Ws → Eqn
  q254 c4 = eqn (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) (wl0099 (lit c4))
  q255 : Ws → Eqn
  q255 c4 = eqn (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 (lit c4))

-- beta-T @0110: 8 steps
lem-beta-T-at0110 : Ws → ⟪ (Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) ⟫ʷ
lem-beta-T-at0110 c4 = derive (Bx1-0234 ∷ []) (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q147 c4) ∷
   rw 1 (q253 c4) ∷
   rw 0 (q254 c4) ∷
   rw 1 (q255 c4) ∷
   rw 2 (q254 c4) ∷
   rw 3 (q255 c4) ∷
   rw 4 (q25 c4) ∷ []) Eq.refl

private
  q256 : Ws → Eqn
  q256 c4 = eqn (Bx1-0234 ∷ []) (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) (lem-beta-T-at0110 c4)
  q257 : Ws → Eqn
  q257 c4 = eqn (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) (wl0047 (lit c4))

-- beta-T @021021: 8 steps
lem-beta-T-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) ⟫ʷ
lem-beta-T-at021021 c4 = derive (Bx2-0134 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q240 c4) ∷
   rw 1 (q256 c4) ∷
   rw 0 (q257 c4) ∷
   rw⁻ 1 (q16 c4) ∷
   rw 2 (q257 c4) ∷
   rw⁻ 3 (q16 c4) ∷
   rw 4 (q11 c4) ∷ []) Eq.refl

private
  q258 : Ws → Eqn
  q258 c4 = eqn (Bx2-0134 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at021021 c4)
  q259 : Ws → Eqn
  q259 c4 = eqn (Sw23 ∷ Toff201 ∷ []) (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 (lit c4))

-- beta-T @03102132: 8 steps
lem-beta-T-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) ⟫ʷ
lem-beta-T-at03102132 c4 = derive (Bx3-0124 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q242 c4) ∷
   rw 1 (q258 c4) ∷
   rw 0 (q259 c4) ∷
   rw⁻ 1 (q128 c4) ∷
   rw 2 (q259 c4) ∷
   rw⁻ 3 (q128 c4) ∷
   rw 4 (q5 c4) ∷ []) Eq.refl

private
  q260 : Ws → Eqn
  q260 c4 = eqn (Sw12 ∷ Bx3-0214 ∷ []) (Bx3-0124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0214⟩ (lit c4))
  q261 : Ws → Eqn
  q261 c4 = eqn (Bx3-0124 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-beta-T-at03102132 c4)
  q262 : Ws → Eqn
  q262 c4 = eqn (Sw12 ∷ Toff301 ∷ []) (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 (lit c4))

-- beta-T @031031: 8 steps
lem-beta-T-at031031 : Ws → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) ⟫ʷ
lem-beta-T-at031031 c4 = derive (Bx3-0214 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q260 c4) ∷
   rw 1 (q261 c4) ∷
   rw 0 (q262 c4) ∷
   rw⁻ 1 (q12 c4) ∷
   rw 2 (q262 c4) ∷
   rw⁻ 3 (q12 c4) ∷
   rw 4 (q11 c4) ∷ []) Eq.refl

private
  q263 : Ws → Eqn
  q263 c4 = eqn (Sw01 ∷ Bx3-1204 ∷ []) (Bx3-0214 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1204⟩ (lit c4))
  q264 : Ws → Eqn
  q264 c4 = eqn (Bx3-0214 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-beta-T-at031031 c4)
  q265 : Ws → Eqn
  q265 c4 = eqn (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) (wl0116 (lit c4))
  q266 : Ws → Eqn
  q266 c4 = eqn (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4))

-- beta-T @0330: 8 steps
lem-beta-T-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-T-at0330 c4 = derive (Bx3-1204 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q263 c4) ∷
   rw 1 (q264 c4) ∷
   rw 0 (q265 c4) ∷
   rw 1 (q266 c4) ∷
   rw 2 (q265 c4) ∷
   rw 3 (q266 c4) ∷
   rw 4 (q25 c4) ∷ []) Eq.refl

private
  q267 : Ws → Eqn
  q267 c4 = eqn (Bx3-0124 ∷ []) (Bx3-1024 ∷ []) (lem-sym12-at03102132 c4)
  q268 : Ws → Eqn
  q268 c4 = eqn (Bx3-1024 ∷ []) (Bx3-1204 ∷ []) (lem-sym23-at032032 c4)
  q269 : Ws → Eqn
  q269 c4 = eqn (Bx3-1204 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-beta-T-at0330 c4)
  q270 : Ws → Eqn
  q270 c4 = eqn (K0 ∷ Toff312 ∷ []) (Toff312 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ))
  q271 : Ws → Eqn
  q271 c4 = eqn (K0 ∷ CCZ034 ∷ []) (Toff034 ∷ K0 ∷ []) (wp0011 c4)
  q272 : Ws → Eqn
  q272 c4 = eqn (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (Toff034 ∷ []) (wp0012 c4)

-- KB-form: 7 steps
lem-KB-form : Ws → ⟪ (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) ⟫ʷ
lem-KB-form c4 = derive (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ [])
  (rw 1 (q267 c4) ∷
   rw 1 (q268 c4) ∷
   rw 1 (q269 c4) ∷
   rw 0 (q270 c4) ∷
   rw 1 (q271 c4) ∷
   rw 2 (q270 c4) ∷
   rw 3 (q272 c4) ∷ []) Eq.refl

private
  q273 : Ws → Eqn
  q273 c4 = eqn (Sw12 ∷ Bx2-0143 ∷ []) (Bx1-0243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0143⟩ (lit c4))

-- sym23 @0210213443: 5 steps
lem-sym23-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-sym23-at0210213443 c4 = derive (Bx2-0143 ∷ []) (Bx2-0413 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q273 c4) ∷
   rw 1 (q171 c4) ∷
   rw 0 (q227 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q274 : Ws → Eqn
  q274 c4 = eqn (Sw23 ∷ Bx3-0142 ∷ []) (Bx2-0143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0142⟩ (lit c4))
  q275 : Ws → Eqn
  q275 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q276 : Ws → Eqn
  q276 c4 = eqn (Sw23 ∷ Bx2-0413 ∷ []) (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4))

-- sym23 @0310213442: 5 steps
lem-sym23-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-sym23-at0310213442 c4 = derive (Bx3-0142 ∷ []) (Bx3-0412 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q274 c4) ∷
   rw 1 (q275 c4) ∷
   rw 0 (q276 c4) ∷
   rw 1 (q5 c4) ∷ []) Eq.refl

private
  q277 : Ws → Eqn
  q277 c4 = eqn (Sw12 ∷ Toff104 ∷ []) (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 (lit c4))

-- beta-T @0210243143: 8 steps
lem-beta-T-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) ⟫ʷ
lem-beta-T-at0210243143 c4 = derive (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q199 c4) ∷
   rw 1 (q159 c4) ∷
   rw 0 (q277 c4) ∷
   rw⁻ 1 (q126 c4) ∷
   rw 2 (q277 c4) ∷
   rw⁻ 3 (q126 c4) ∷
   rw 4 (q11 c4) ∷ []) Eq.refl

private
  q278 : Ws → Eqn
  q278 c4 = eqn (Sw23 ∷ Bx3-0412 ∷ []) (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4))
  q279 : Ws → Eqn
  q279 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q280 : Ws → Eqn
  q280 c4 = eqn (Sw23 ∷ Toff204 ∷ []) (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 (lit c4))
  q281 : Ws → Eqn
  q281 c4 = eqn (CCZ123 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ123 ∷ []) (wl0113 (lit c4))

-- beta-T @0310243142: 8 steps
lem-beta-T-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) ⟫ʷ
lem-beta-T-at0310243142 c4 = derive (Bx3-0412 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q278 c4) ∷
   rw 1 (q279 c4) ∷
   rw 0 (q280 c4) ∷
   rw⁻ 1 (q281 c4) ∷
   rw 2 (q280 c4) ∷
   rw⁻ 3 (q281 c4) ∷
   rw 4 (q5 c4) ∷ []) Eq.refl

private
  q282 : Ws → Eqn
  q282 c4 = eqn (Sw23 ∷ Bx2-0143 ∷ []) (Bx3-0142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0143⟩ (lit c4))

-- sym23 @0310243142: 5 steps
lem-sym23-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-sym23-at0310243142 c4 = derive (Bx3-0412 ∷ []) (Bx3-0142 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q278 c4) ∷
   rw 1 (q201 c4) ∷
   rw 0 (q282 c4) ∷
   rw 1 (q5 c4) ∷ []) Eq.refl

private
  q283 : Ws → Eqn
  q283 c4 = eqn (CK40 ∷ []) (K0 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ []) (wp0074 c4)
  q284 : Ws → Eqn
  q284 c4 = eqn (Bx3-0124 ∷ []) (Bx3-0142 ∷ []) (lem-sym34-at03102132 c4)
  q285 : Ws → Eqn
  q285 c4 = eqn (Bx3-0142 ∷ []) (Bx3-0412 ∷ []) (lem-sym23-at0310213442 c4)
  q286 : Ws → Eqn
  q286 c4 = eqn (Bx3-0412 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-beta-T-at0310243142 c4)
  q287 : Ws → Eqn
  q287 c4 = eqn (Toff304 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ []) (X4 ∷ CK40⁻ ∷ X4 ∷ Toff304 ∷ []) (wp0075 c4)
  q288 : Ws → Eqn
  q288 c4 = eqn (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) (c₄ (CCZ ↑) (X))
  q289 : Ws → Eqn
  q289 c4 = eqn (CK40⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CK40⁻ ∷ []) (lem-comm-CKd40-CCZ123 (lit c4))
  q290 : Ws → Eqn
  q290 c4 = eqn (Bx3-0412 ∷ []) (Bx3-0142 ∷ []) (lem-sym23-at0310243142 c4)
  q291 : Ws → Eqn
  q291 c4 = eqn (Bx3-0142 ∷ []) (Bx3-0124 ∷ []) (lem-sym34-at0310213442 c4)
  q292 : Ws → Eqn
  q292 c4 = eqn (K0⁻ ∷ []) (X4 ∷ CK40⁻ ∷ X4 ∷ K0 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ S4 ∷ []) (wp0076 c4)

-- CKbox: 17 steps
lem-CKbox : Ws → ⟪ (CK40 ∷ Bx3-0124 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ []) ⟫ʷ
lem-CKbox c4 = derive (CK40 ∷ Bx3-0124 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ [])
  (rw 0 (q283 c4) ∷
   rw 5 (q283 c4) ∷
   rw 4 (q284 c4) ∷
   rw 4 (q285 c4) ∷
   rw 4 (q286 c4) ∷
   rw⁻ 1 (q287 c4) ∷
   rw⁻ 4 (q288 c4) ∷
   rw 3 (q289 c4) ∷
   rw⁻ 2 (q288 c4) ∷
   rw⁻ 3 (q287 c4) ∷
   rw⁻ 6 (q288 c4) ∷
   rw 5 (q289 c4) ∷
   rw⁻ 4 (q288 c4) ∷
   rw⁻ 1 (q286 c4) ∷
   rw 1 (q290 c4) ∷
   rw 1 (q291 c4) ∷
   rw⁻ 2 (q292 c4) ∷ []) Eq.refl

private
  q293 : Ws → Eqn
  q293 c4 = eqn (CCZ123 ∷ []) (CCZ123 ∷ []) (wl0269 (lit c4))
  q294 : Ws → Eqn
  q294 c4 = eqn (CCZ123 ∷ Bx0-1243 ∷ []) (Bx0-1243 ∷ CCZ123 ∷ []) (lem-c124-beta-at3443 c4)

-- auto BOX(0;1234) | CCZ231: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231 : Ws → ⟪ (Bx0-1234 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231 c4 = derive (Bx0-1234 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1234 ∷ [])
  (rw 1 (q293 c4) ∷
   rw 0 (q48 c4) ∷
   rw⁻ 0 (q294 c4) ∷
   rw 1 (q82 c4) ∷
   rw 0 (q293 c4) ∷ []) Eq.refl

private
  q295 : Ws → Eqn
  q295 c4 = eqn (Sw23 ∷ CS13 ∷ []) (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 (lit c4))
  q296 : Ws → Eqn
  q296 c4 = eqn (CS12 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS12 ∷ []) (lem-CS12-beta c4)
  q297 : Ws → Eqn
  q297 c4 = eqn (Sw23 ∷ CS12 ∷ []) (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 (lit c4))

-- CS12-beta @2332: 7 steps
lem-CS12-beta-at2332 : Ws → ⟪ (CS13 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CS13 ∷ []) ⟫ʷ
lem-CS12-beta-at2332 c4 = derive (CS13 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS13 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q295 c4) ∷
   rw 2 (q7 c4) ∷
   rw 1 (q296 c4) ∷
   rw 0 (q9 c4) ∷
   rw 1 (q297 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q298 : Ws → Eqn
  q298 c4 = eqn (Sw34 ∷ CS14 ∷ []) (CS13 ∷ Sw34 ∷ []) (lem-nat-3-CS14 (lit c4))
  q299 : Ws → Eqn
  q299 c4 = eqn (CS13 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS13 ∷ []) (lem-CS12-beta-at2332 c4)
  q300 : Ws → Eqn
  q300 c4 = eqn (Sw34 ∷ CS13 ∷ []) (CS14 ∷ Sw34 ∷ []) (lem-nat-3-CS13 (lit c4))

-- CS12-beta @243243: 7 steps
lem-CS12-beta-at243243 : Ws → ⟪ (CS14 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS14 ∷ []) ⟫ʷ
lem-CS12-beta-at243243 c4 = derive (CS14 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS14 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q298 c4) ∷
   rw 2 (q67 c4) ∷
   rw 1 (q299 c4) ∷
   rw 0 (q56 c4) ∷
   rw 1 (q300 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q301 : Ws → Eqn
  q301 c4 = eqn (CS14 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS14 ∷ []) (lem-CS12-beta-at243243 c4)

-- auto BOX(0;1234) | CS14: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14 : Ws → ⟪ (Bx0-1234 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14 c4 = derive (Bx0-1234 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1234 ∷ [])
  (rw 0 (q48 c4) ∷
   rw 0 (q58 c4) ∷
   rw⁻ 0 (q301 c4) ∷
   rw 1 (q79 c4) ∷
   rw 1 (q82 c4) ∷ []) Eq.refl

private
  q302 : Ws → Eqn
  q302 c4 = eqn (Sw23 ∷ CS13⁻ ∷ []) (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 (lit c4))
  q303 : Ws → Eqn
  q303 c4 = eqn (CS12⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS12⁻ ∷ []) (lem-CSd12-beta c4)
  q304 : Ws → Eqn
  q304 c4 = eqn (Sw23 ∷ CS12⁻ ∷ []) (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 (lit c4))

-- CSd12-beta @2332: 7 steps
lem-CSd12-beta-at2332 : Ws → ⟪ (CS13⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-CSd12-beta-at2332 c4 = derive (CS13⁻ ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS13⁻ ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q302 c4) ∷
   rw 2 (q7 c4) ∷
   rw 1 (q303 c4) ∷
   rw 0 (q9 c4) ∷
   rw 1 (q304 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q305 : Ws → Eqn
  q305 c4 = eqn (Sw34 ∷ CS14⁻ ∷ []) (CS13⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd14 (lit c4))
  q306 : Ws → Eqn
  q306 c4 = eqn (CS13⁻ ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS13⁻ ∷ []) (lem-CSd12-beta-at2332 c4)
  q307 : Ws → Eqn
  q307 c4 = eqn (Sw34 ∷ CS13⁻ ∷ []) (CS14⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd13 (lit c4))

-- CSd12-beta @243243: 7 steps
lem-CSd12-beta-at243243 : Ws → ⟪ (CS14⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS14⁻ ∷ []) ⟫ʷ
lem-CSd12-beta-at243243 c4 = derive (CS14⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS14⁻ ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q305 c4) ∷
   rw 2 (q67 c4) ∷
   rw 1 (q306 c4) ∷
   rw 0 (q56 c4) ∷
   rw 1 (q307 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q308 : Ws → Eqn
  q308 c4 = eqn (CS14⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS14⁻ ∷ []) (lem-CSd12-beta-at243243 c4)

-- auto BOX(0;1234) | CSd14: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14 : Ws → ⟪ (Bx0-1234 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14 c4 = derive (Bx0-1234 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx0-1234 ∷ [])
  (rw 0 (q48 c4) ∷
   rw 0 (q58 c4) ∷
   rw⁻ 0 (q308 c4) ∷
   rw 1 (q79 c4) ∷
   rw 1 (q82 c4) ∷ []) Eq.refl

private
  q309 : Ws → Eqn
  q309 c4 = eqn (Sw01 ∷ Bx2-4103 ∷ []) (Bx2-4013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4103⟩ (lit c4))
  q310 : Ws → Eqn
  q310 c4 = eqn (Bx2-4013 ∷ []) (Bx2-4031 ∷ []) (lem-sym34-at0214203143 c4)
  q311 : Ws → Eqn
  q311 c4 = eqn (Sw01 ∷ Bx2-4031 ∷ []) (Bx2-4130 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4031⟩ (lit c4))

-- sym34 @0214213043: 5 steps
lem-sym34-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4130 ∷ []) ⟫ʷ
lem-sym34-at0214213043 c4 = derive (Bx2-4103 ∷ []) (Bx2-4130 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q309 c4) ∷
   rw 1 (q310 c4) ∷
   rw 0 (q311 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

private
  q312 : Ws → Eqn
  q312 c4 = eqn (Sw23 ∷ Toff314 ∷ []) (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 (lit c4))
  q313 : Ws → Eqn
  q313 c4 = eqn (Sw23 ∷ Bx0-4132 ∷ []) (Bx0-4123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4132⟩ (lit c4))
  q314 : Ws → Eqn
  q314 c4 = eqn (Toff214 ∷ Bx0-4123 ∷ Toff214 ∷ []) (Bx0-4123 ∷ CCZ134 ∷ []) (lem-T312-beta-at14213243 c4)
  q315 : Ws → Eqn
  q315 c4 = eqn (Sw23 ∷ Bx0-4123 ∷ []) (Bx0-4132 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4123⟩ (lit c4))

-- T312-beta @142142: 8 steps
lem-T312-beta-at142142 : Ws → ⟪ (Toff314 ∷ Bx0-4132 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ CCZ124 ∷ []) ⟫ʷ
lem-T312-beta-at142142 c4 = derive (Toff314 ∷ Bx0-4132 ∷ Toff314 ∷ []) (Bx0-4132 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q312 c4) ∷
   rw 2 (q313 c4) ∷
   rw 3 (q312 c4) ∷
   rw 1 (q314 c4) ∷
   rw 0 (q315 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q316 : Ws → Eqn
  q316 c4 = eqn (Sw01 ∷ Toff304 ∷ []) (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 (lit c4))
  q317 : Ws → Eqn
  q317 c4 = eqn (Sw01 ∷ Bx1-4032 ∷ []) (Bx0-4132 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4032⟩ (lit c4))
  q318 : Ws → Eqn
  q318 c4 = eqn (Toff314 ∷ Bx0-4132 ∷ Toff314 ∷ []) (Bx0-4132 ∷ CCZ124 ∷ []) (lem-T312-beta-at142142 c4)
  q319 : Ws → Eqn
  q319 c4 = eqn (Sw01 ∷ Bx0-4132 ∷ []) (Bx1-4032 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4132⟩ (lit c4))
  q320 : Ws → Eqn
  q320 c4 = eqn (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4))

-- T312-beta @01142042: 8 steps
lem-T312-beta-at01142042 : Ws → ⟪ (Toff304 ∷ Bx1-4032 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4032 ∷ CCZ024 ∷ []) ⟫ʷ
lem-T312-beta-at01142042 c4 = derive (Toff304 ∷ Bx1-4032 ∷ Toff304 ∷ []) (Bx1-4032 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q316 c4) ∷
   rw 2 (q317 c4) ∷
   rw 3 (q316 c4) ∷
   rw 1 (q318 c4) ∷
   rw 0 (q319 c4) ∷
   rw 1 (q320 c4) ∷
   rw 2 (q25 c4) ∷ []) Eq.refl

private
  q321 : Ws → Eqn
  q321 c4 = eqn (Sw12 ∷ Toff304 ∷ []) (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 (lit c4))
  q322 : Ws → Eqn
  q322 c4 = eqn (Sw12 ∷ Bx2-4031 ∷ []) (Bx1-4032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4031⟩ (lit c4))
  q323 : Ws → Eqn
  q323 c4 = eqn (Toff304 ∷ Bx1-4032 ∷ Toff304 ∷ []) (Bx1-4032 ∷ CCZ024 ∷ []) (lem-T312-beta-at01142042 c4)
  q324 : Ws → Eqn
  q324 c4 = eqn (Sw12 ∷ Bx1-4032 ∷ []) (Bx2-4031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4032⟩ (lit c4))

-- T312-beta @02142041: 8 steps
lem-T312-beta-at02142041 : Ws → ⟪ (Toff304 ∷ Bx2-4031 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ CCZ014 ∷ []) ⟫ʷ
lem-T312-beta-at02142041 c4 = derive (Toff304 ∷ Bx2-4031 ∷ Toff304 ∷ []) (Bx2-4031 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q321 c4) ∷
   rw 2 (q322 c4) ∷
   rw 3 (q321 c4) ∷
   rw 1 (q323 c4) ∷
   rw 0 (q324 c4) ∷
   rw 1 (q70 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q325 : Ws → Eqn
  q325 c4 = eqn (Sw01 ∷ Toff314 ∷ []) (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 (lit c4))
  q326 : Ws → Eqn
  q326 c4 = eqn (Sw01 ∷ Bx2-4130 ∷ []) (Bx2-4031 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4130⟩ (lit c4))
  q327 : Ws → Eqn
  q327 c4 = eqn (Toff304 ∷ Bx2-4031 ∷ Toff304 ∷ []) (Bx2-4031 ∷ CCZ014 ∷ []) (lem-T312-beta-at02142041 c4)
  q328 : Ws → Eqn
  q328 c4 = eqn (Sw01 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 (lit c4))

-- T312-beta @02142140: 8 steps
lem-T312-beta-at02142140 : Ws → ⟪ (Toff314 ∷ Bx2-4130 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4130 ∷ CCZ014 ∷ []) ⟫ʷ
lem-T312-beta-at02142140 c4 = derive (Toff314 ∷ Bx2-4130 ∷ Toff314 ∷ []) (Bx2-4130 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q325 c4) ∷
   rw 2 (q326 c4) ∷
   rw 3 (q325 c4) ∷
   rw 1 (q327 c4) ∷
   rw 0 (q311 c4) ∷
   rw 1 (q328 c4) ∷
   rw 2 (q25 c4) ∷ []) Eq.refl

private
  q329 : Ws → Eqn
  q329 c4 = eqn (Bx0-4123 ∷ []) (Bx0-4132 ∷ []) (lem-sym34-at14213243 c4)

-- sym34 @142142: 5 steps
lem-sym34-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-sym34-at142142 c4 = derive (Bx0-4132 ∷ []) (Bx0-4123 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q313 c4) ∷
   rw 1 (q329 c4) ∷
   rw 0 (q313 c4) ∷
   rw 1 (q5 c4) ∷ []) Eq.refl

private
  q330 : Ws → Eqn
  q330 c4 = eqn (Bx0-4132 ∷ []) (Bx0-4123 ∷ []) (lem-sym34-at142142 c4)

-- sym34 @01142042: 5 steps
lem-sym34-at01142042 : Ws → ⟪ (Bx1-4032 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4023 ∷ []) ⟫ʷ
lem-sym34-at01142042 c4 = derive (Bx1-4032 ∷ []) (Bx1-4023 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q317 c4) ∷
   rw 1 (q330 c4) ∷
   rw 0 (q214 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

private
  q331 : Ws → Eqn
  q331 c4 = eqn (Bx1-4032 ∷ []) (Bx1-4023 ∷ []) (lem-sym34-at01142042 c4)

-- sym34 @02142041: 5 steps
lem-sym34-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-sym34-at02142041 c4 = derive (Bx2-4031 ∷ []) (Bx2-4013 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q322 c4) ∷
   rw 1 (q331 c4) ∷
   rw 0 (q216 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q332 : Ws → Eqn
  q332 c4 = eqn (Bx2-4031 ∷ []) (Bx2-4013 ∷ []) (lem-sym34-at02142041 c4)
  q333 : Ws → Eqn
  q333 c4 = eqn (Sw01 ∷ Bx2-4013 ∷ []) (Bx2-4103 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4013⟩ (lit c4))

-- sym34 @02142140: 5 steps
lem-sym34-at02142140 : Ws → ⟪ (Bx2-4130 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-sym34-at02142140 c4 = derive (Bx2-4130 ∷ []) (Bx2-4103 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q326 c4) ∷
   rw 1 (q332 c4) ∷
   rw 0 (q333 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

private
  q334 : Ws → Eqn
  q334 c4 = eqn (Bx0-1234 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231 c4)

-- auto BOX(0;1234) | CCZ231 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at2332 c4 = derive (Bx0-1324 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q7 c4) ∷
   rw⁻ 2 (q281 c4) ∷
   rw 1 (q334 c4) ∷
   rw⁻ 0 (q281 c4) ∷
   rw 1 (q9 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q335 : Ws → Eqn
  q335 c4 = eqn (Bx0-1324 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at2332 c4)

-- auto BOX(0;1234) | CCZ231 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 : Ws → ⟪ (Bx0-1423 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 c4 = derive (Bx0-1423 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q67 c4) ∷
   rw 2 (q125 c4) ∷
   rw 1 (q335 c4) ∷
   rw 0 (q123 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q336 : Ws → Eqn
  q336 c4 = eqn (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4))
  q337 : Ws → Eqn
  q337 c4 = eqn (Bx0-1423 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 c4)

-- auto BOX(0;1234) | CCZ231 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0110243243 c4 = derive (Bx1-0423 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q97 c4) ∷
   rw 2 (q336 c4) ∷
   rw 1 (q337 c4) ∷
   rw 0 (q320 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q25 c4) ∷ []) Eq.refl

private
  q338 : Ws → Eqn
  q338 c4 = eqn (Bx1-0423 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0110243243 c4)

-- auto BOX(0;1234) | CCZ231 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4 = derive (Bx2-0413 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q199 c4) ∷
   rw 2 (q73 c4) ∷
   rw 1 (q338 c4) ∷
   rw 0 (q70 c4) ∷
   rw 1 (q227 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q339 : Ws → Eqn
  q339 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl0021 (lit c4))
  q340 : Ws → Eqn
  q340 c4 = eqn (Bx0-1234 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14 c4)

-- auto BOX(0;1234) | CS14 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14-at2332 c4 = derive (Bx0-1324 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q7 c4) ∷
   rw⁻ 2 (q339 c4) ∷
   rw 1 (q340 c4) ∷
   rw⁻ 0 (q339 c4) ∷
   rw 1 (q9 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q341 : Ws → Eqn
  q341 c4 = eqn (Bx0-1324 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at2332 c4)

-- auto BOX(0;1234) | CS14 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14-at243243 : Ws → ⟪ (Bx0-1423 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14-at243243 c4 = derive (Bx0-1423 ∷ CS13 ∷ []) (CS13 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q67 c4) ∷
   rw 2 (q300 c4) ∷
   rw 1 (q341 c4) ∷
   rw 0 (q298 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q342 : Ws → Eqn
  q342 c4 = eqn (CS13 ∷ Sw01 ∷ []) (Sw01 ∷ CS03 ∷ []) (wl0061 (lit c4))
  q343 : Ws → Eqn
  q343 c4 = eqn (Bx0-1423 ∷ CS13 ∷ []) (CS13 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at243243 c4)
  q344 : Ws → Eqn
  q344 c4 = eqn (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) (wl0019 (lit c4))

-- auto BOX(0;1234) | CS14 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0110243243 c4 = derive (Bx1-0423 ∷ CS03 ∷ []) (CS03 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q97 c4) ∷
   rw⁻ 2 (q342 c4) ∷
   rw 1 (q343 c4) ∷
   rw⁻ 0 (q344 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q25 c4) ∷ []) Eq.refl

private
  q345 : Ws → Eqn
  q345 c4 = eqn (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) (wl0010 (lit c4))
  q346 : Ws → Eqn
  q346 c4 = eqn (Bx1-0423 ∷ CS03 ∷ []) (CS03 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0110243243 c4)

-- auto BOX(0;1234) | CS14 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 c4 = derive (Bx2-0413 ∷ CS03 ∷ []) (CS03 ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q199 c4) ∷
   rw⁻ 2 (q345 c4) ∷
   rw 1 (q346 c4) ∷
   rw⁻ 0 (q345 c4) ∷
   rw 1 (q227 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q347 : Ws → Eqn
  q347 c4 = eqn (CS14⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS14⁻ ∷ []) (wl0033 (lit c4))
  q348 : Ws → Eqn
  q348 c4 = eqn (Bx0-1234 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14 c4)

-- auto BOX(0;1234) | CSd14 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at2332 c4 = derive (Bx0-1324 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q7 c4) ∷
   rw⁻ 2 (q347 c4) ∷
   rw 1 (q348 c4) ∷
   rw⁻ 0 (q347 c4) ∷
   rw 1 (q9 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q349 : Ws → Eqn
  q349 c4 = eqn (Bx0-1324 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at2332 c4)

-- auto BOX(0;1234) | CSd14 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at243243 : Ws → ⟪ (Bx0-1423 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at243243 c4 = derive (Bx0-1423 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q67 c4) ∷
   rw 2 (q307 c4) ∷
   rw 1 (q349 c4) ∷
   rw 0 (q305 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q350 : Ws → Eqn
  q350 c4 = eqn (CS13⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS03⁻ ∷ []) (wl0121 (lit c4))
  q351 : Ws → Eqn
  q351 c4 = eqn (Bx0-1423 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at243243 c4)
  q352 : Ws → Eqn
  q352 c4 = eqn (CS03⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS13⁻ ∷ []) (wl0022 (lit c4))

-- auto BOX(0;1234) | CSd14 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0110243243 c4 = derive (Bx1-0423 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q97 c4) ∷
   rw⁻ 2 (q350 c4) ∷
   rw 1 (q351 c4) ∷
   rw⁻ 0 (q352 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q25 c4) ∷ []) Eq.refl

private
  q353 : Ws → Eqn
  q353 c4 = eqn (CS03⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS03⁻ ∷ []) (wl0023 (lit c4))
  q354 : Ws → Eqn
  q354 c4 = eqn (Bx1-0423 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0110243243 c4)

-- auto BOX(0;1234) | CSd14 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 c4 = derive (Bx2-0413 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q199 c4) ∷
   rw⁻ 2 (q353 c4) ∷
   rw 1 (q354 c4) ∷
   rw⁻ 0 (q353 c4) ∷
   rw 1 (q227 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q355 : Ws → Eqn
  q355 c4 = eqn (Bx2-4013 ∷ []) (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4)
  q356 : Ws → Eqn
  q356 c4 = eqn (Bx2-4103 ∷ []) (Bx2-4130 ∷ []) (lem-sym34-at0214213043 c4)
  q357 : Ws → Eqn
  q357 c4 = eqn (Toff314 ∷ Bx2-4130 ∷ Toff314 ∷ []) (Bx2-4130 ∷ CCZ014 ∷ []) (lem-T312-beta-at02142140 c4)
  q358 : Ws → Eqn
  q358 c4 = eqn (Bx2-4130 ∷ []) (Bx2-4103 ∷ []) (lem-sym34-at02142140 c4)
  q359 : Ws → Eqn
  q359 c4 = eqn (Bx2-4103 ∷ []) (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4)
  q360 : Ws → Eqn
  q360 c4 = eqn (Bx2-4013 ∷ []) (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4)
  q361 : Ws → Eqn
  q361 c4 = eqn (Bx2-0413 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4)
  q362 : Ws → Eqn
  q362 c4 = eqn (Bx2-0413 ∷ CS03 ∷ []) (CS03 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 c4)
  q363 : Ws → Eqn
  q363 c4 = eqn (Bx2-0413 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 c4)
  q364 : Ws → Eqn
  q364 c4 = eqn (CCZ014 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ014 ∷ []) (wp0077 c4)
  q365 : Ws → Eqn
  q365 c4 = eqn (CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ []) (wp0078 c4)
  q366 : Ws → Eqn
  q366 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp0055 c4)
  q367 : Ws → Eqn
  q367 c4 = eqn (Bx2-0413 ∷ Bx2-0413 ∷ []) [] (lem-beta-inv-at0210243143 c4)
  q368 : Ws → Eqn
  q368 c4 = eqn (CCZ014 ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp0056 c4)

-- SB2: 31 steps
lem-SB2 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
lem-SB2 c4 = derive (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (CCZ014 ∷ [])
  (re 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 2 1 (CS03 ∷ []) ∷
   re 4 1 (CS03⁻ ∷ []) ∷
   re 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 7 1 (CS03 ∷ []) ∷
   re 9 1 (CS03⁻ ∷ []) ∷
   rw⁻ 0 (q205 c4) ∷
   rw 2 (q217 c4) ∷
   rw 2 (q355 c4) ∷
   rw 2 (q356 c4) ∷
   rw 1 (q357 c4) ∷
   rw 1 (q358 c4) ∷
   rw 1 (q359 c4) ∷
   rw 1 (q360 c4) ∷
   rw 1 (q361 c4) ∷
   rw 2 (q362 c4) ∷
   rw⁻ 3 (q205 c4) ∷
   rw 5 (q217 c4) ∷
   rw 5 (q355 c4) ∷
   rw 5 (q356 c4) ∷
   rw 4 (q357 c4) ∷
   rw 4 (q358 c4) ∷
   rw 4 (q359 c4) ∷
   rw 4 (q360 c4) ∷
   rw 4 (q361 c4) ∷
   rw 5 (q363 c4) ∷
   rw⁻ 0 (q364 c4) ∷
   rw⁻ 1 (q365 c4) ∷
   rw 0 (q366 c4) ∷
   rw 4 (q367 c4) ∷
   rw⁻ 0 (q368 c4) ∷ []) Eq.refl

-- F1 order-CS [nf of rhs]: 0 steps
lem-F1-order-CS-nf-of-rhs : Ws → ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CS-nf-of-rhs c4 = refl

private
  q369 : Ws → Eqn
  q369 c4 = eqn (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (CCZ014 ∷ []) (lem-SB2 c4)
  q370 : Ws → Eqn
  q370 c4 = eqn [] [] (lem-F1-order-CS-nf-of-rhs c4)

-- F1 order-CS: 4 steps
lem-F1-order-CS : Ws → ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CS c4 = derive (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) []
  (rw 0 (q369 c4) ∷
   rw 1 (q369 c4) ∷
   rw 0 (q366 c4) ∷
   rw⁻ 0 (q370 c4) ∷ []) Eq.refl

private
  q371 : Ws → Eqn
  q371 c4 = eqn (CS12 ∷ []) (CS12 ∷ []) (wl0270 (lit c4))

-- auto BOX(0;1234) | CS21: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CS21 : Ws → ⟪ (Bx0-1234 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS21 c4 = derive (Bx0-1234 ∷ CS12 ∷ []) (CS12 ∷ Bx0-1234 ∷ [])
  (rw 1 (q371 c4) ∷
   rw⁻ 0 (q296 c4) ∷
   rw 0 (q371 c4) ∷ []) Eq.refl

private
  q372 : Ws → Eqn
  q372 c4 = eqn (CS12 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS12 ∷ []) (wl0271 (lit c4))
  q373 : Ws → Eqn
  q373 c4 = eqn (CS12 ∷ Toff423 ∷ []) (Toff423 ∷ CS12 ∷ []) (wl0272 (lit c4))
  q374 : Ws → Eqn
  q374 c4 = eqn (CS12 ∷ CS14 ∷ []) (CS14 ∷ CS12 ∷ []) (wl0273 (lit c4))
  q375 : Ws → Eqn
  q375 c4 = eqn (Bx0-1234 ∷ CS12 ∷ []) (CS12 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS21 c4)

-- auto SBOX(0;1;23;4) | CS21: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21 : Ws → ⟪ (Sb0-1-23-4 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21 c4 = derive (Sb0-1-23-4 ∷ CS12 ∷ []) (CS12 ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q372 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw⁻ 3 (q373 c4) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw⁻ 2 (q374 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw⁻ 1 (q373 c4) ∷
   rw 0 (q375 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q376 : Ws → Eqn
  q376 c4 = eqn (Sw23 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4))
  q377 : Ws → Eqn
  q377 c4 = eqn (Sb0-1-23-4 ∷ CS12 ∷ []) (CS12 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21 c4)
  q378 : Ws → Eqn
  q378 c4 = eqn (Sw23 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | CS21 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 c4 = derive (Sb0-1-32-4 ∷ CS13 ∷ []) (CS13 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q376 c4) ∷
   rw 2 (q295 c4) ∷
   rw 1 (q377 c4) ∷
   rw 0 (q297 c4) ∷
   rw 1 (q378 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q379 : Ws → Eqn
  q379 c4 = eqn (Sw34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4))
  q380 : Ws → Eqn
  q380 c4 = eqn (Sb0-1-32-4 ∷ CS13 ∷ []) (CS13 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 c4)
  q381 : Ws → Eqn
  q381 c4 = eqn (Sw34 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | CS21 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at243243 c4 = derive (Sb0-1-42-3 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q379 c4) ∷
   rw 2 (q298 c4) ∷
   rw 1 (q380 c4) ∷
   rw 0 (q300 c4) ∷
   rw 1 (q381 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q382 : Ws → Eqn
  q382 c4 = eqn (Sw01 ∷ Sb1-0-42-3 ∷ []) (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4))
  q383 : Ws → Eqn
  q383 c4 = eqn (Sw01 ∷ CS04 ∷ []) (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4))
  q384 : Ws → Eqn
  q384 c4 = eqn (Sb0-1-42-3 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at243243 c4)
  q385 : Ws → Eqn
  q385 c4 = eqn (Sw01 ∷ CS14 ∷ []) (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4))
  q386 : Ws → Eqn
  q386 c4 = eqn (Sw01 ∷ Sb0-1-42-3 ∷ []) (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4))

-- auto SBOX(0;1;23;4) | CS21 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at0110243243 c4 = derive (Sb1-0-42-3 ∷ CS04 ∷ []) (CS04 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q382 c4) ∷
   rw 2 (q383 c4) ∷
   rw 1 (q384 c4) ∷
   rw 0 (q385 c4) ∷
   rw 1 (q386 c4) ∷
   rw 2 (q25 c4) ∷ []) Eq.refl

private
  q387 : Ws → Eqn
  q387 c4 = eqn (Sw12 ∷ Sb2-0-41-3 ∷ []) (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4))
  q388 : Ws → Eqn
  q388 c4 = eqn (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4))
  q389 : Ws → Eqn
  q389 c4 = eqn (Sb1-0-42-3 ∷ CS04 ∷ []) (CS04 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at0110243243 c4)
  q390 : Ws → Eqn
  q390 c4 = eqn (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4))

-- auto SBOX(0;1;23;4) | CS21 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at0210243143 c4 = derive (Sb2-0-41-3 ∷ CS04 ∷ []) (CS04 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q387 c4) ∷
   rw 2 (q388 c4) ∷
   rw 1 (q389 c4) ∷
   rw 0 (q388 c4) ∷
   rw 1 (q390 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q391 : Ws → Eqn
  q391 c4 = eqn (Sb2-0-41-3 ∷ CS04 ∷ []) (CS04 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at0210243143 c4)

-- F1 comm-CS-S0: 1 steps
lem-F1-comm-CS-S0 : Ws → ⟪ (Sb2-0-41-3 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-S0 c4 = derive (Sb2-0-41-3 ∷ CS04 ∷ []) (CS04 ∷ Sb2-0-41-3 ∷ [])
  (rw 0 (q391 c4) ∷ []) Eq.refl

private
  q392 : Ws → Eqn
  q392 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl0024 (lit c4))
  q393 : Ws → Eqn
  q393 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl0025 (lit c4))

-- CS12-beta @122331: 7 steps
lem-CS12-beta-at122331 : Ws → ⟪ (CS23 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CS23 ∷ []) ⟫ʷ
lem-CS12-beta-at122331 c4 = derive (CS23 ∷ Bx0-2314 ∷ []) (Bx0-2314 ∷ CS23 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw⁻ 1 (q392 c4) ∷
   rw 2 (q13 c4) ∷
   rw 1 (q299 c4) ∷
   rw 0 (q15 c4) ∷
   rw⁻ 1 (q393 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q394 : Ws → Eqn
  q394 c4 = eqn (CS23 ∷ Bx0-2314 ∷ []) (Bx0-2314 ∷ CS23 ∷ []) (lem-CS12-beta-at122331 c4)

-- auto BOX(0;1234) | CS23: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CS23 : Ws → ⟪ (Bx0-1234 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS23 c4 = derive (Bx0-1234 ∷ CS23 ∷ []) (CS23 ∷ Bx0-1234 ∷ [])
  (rw 0 (q20 c4) ∷
   rw 0 (q21 c4) ∷
   rw⁻ 0 (q394 c4) ∷
   rw 1 (q23 c4) ∷
   rw 1 (q24 c4) ∷ []) Eq.refl

private
  q395 : Ws → Eqn
  q395 c4 = eqn (CS14⁻ ∷ CS23 ∷ []) (CS23 ∷ CS14⁻ ∷ []) (wl0274 (lit c4))
  q396 : Ws → Eqn
  q396 c4 = eqn (CS23 ∷ Toff423 ∷ []) (Toff423 ∷ CS23 ∷ []) (wl0275 (lit c4))
  q397 : Ws → Eqn
  q397 c4 = eqn (CS14 ∷ CS23 ∷ []) (CS23 ∷ CS14 ∷ []) (wl0276 (lit c4))
  q398 : Ws → Eqn
  q398 c4 = eqn (Bx0-1234 ∷ CS23 ∷ []) (CS23 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS23 c4)

-- auto SBOX(0;1;23;4) | CS23: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23 : Ws → ⟪ (Sb0-1-23-4 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23 c4 = derive (Sb0-1-23-4 ∷ CS23 ∷ []) (CS23 ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw 4 (q395 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw⁻ 3 (q396 c4) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw 2 (q397 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw⁻ 1 (q396 c4) ∷
   rw 0 (q398 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q399 : Ws → Eqn
  q399 c4 = eqn (CS23 ∷ Sw23 ∷ []) (Sw23 ∷ CS23 ∷ []) (wl0152 (lit c4))
  q400 : Ws → Eqn
  q400 c4 = eqn (Sb0-1-23-4 ∷ CS23 ∷ []) (CS23 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23 c4)

-- auto SBOX(0;1;23;4) | CS23 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at2332 c4 = derive (Sb0-1-32-4 ∷ CS23 ∷ []) (CS23 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q376 c4) ∷
   rw⁻ 2 (q399 c4) ∷
   rw 1 (q400 c4) ∷
   rw⁻ 0 (q399 c4) ∷
   rw 1 (q378 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q401 : Ws → Eqn
  q401 c4 = eqn (Sw34 ∷ CS24 ∷ []) (CS23 ∷ Sw34 ∷ []) (lem-nat-3-CS24 (lit c4))
  q402 : Ws → Eqn
  q402 c4 = eqn (Sb0-1-32-4 ∷ CS23 ∷ []) (CS23 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at2332 c4)
  q403 : Ws → Eqn
  q403 c4 = eqn (Sw34 ∷ CS23 ∷ []) (CS24 ∷ Sw34 ∷ []) (lem-nat-3-CS23 (lit c4))

-- auto SBOX(0;1;23;4) | CS23 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at243243 c4 = derive (Sb0-1-42-3 ∷ CS24 ∷ []) (CS24 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q379 c4) ∷
   rw 2 (q401 c4) ∷
   rw 1 (q402 c4) ∷
   rw 0 (q403 c4) ∷
   rw 1 (q381 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q404 : Ws → Eqn
  q404 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q405 : Ws → Eqn
  q405 c4 = eqn (Sb0-1-42-3 ∷ CS24 ∷ []) (CS24 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at243243 c4)

-- auto SBOX(0;1;23;4) | CS23 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at0110243243 c4 = derive (Sb1-0-42-3 ∷ CS24 ∷ []) (CS24 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q382 c4) ∷
   rw 2 (q404 c4) ∷
   rw 1 (q405 c4) ∷
   rw 0 (q404 c4) ∷
   rw 1 (q386 c4) ∷
   rw 2 (q25 c4) ∷ []) Eq.refl

private
  q406 : Ws → Eqn
  q406 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 (lit c4))
  q407 : Ws → Eqn
  q407 c4 = eqn (Sb1-0-42-3 ∷ CS24 ∷ []) (CS24 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at0110243243 c4)
  q408 : Ws → Eqn
  q408 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0017 (lit c4))

-- auto SBOX(0;1;23;4) | CS23 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at0210243143 c4 = derive (Sb2-0-41-3 ∷ CS14 ∷ []) (CS14 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q387 c4) ∷
   rw⁻ 2 (q406 c4) ∷
   rw 1 (q407 c4) ∷
   rw⁻ 0 (q408 c4) ∷
   rw 1 (q390 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q409 : Ws → Eqn
  q409 c4 = eqn (Sb2-0-41-3 ∷ CS14 ∷ []) (CS14 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at0210243143 c4)

-- F1 comm-CS-S1: 1 steps
lem-F1-comm-CS-S1 : Ws → ⟪ (Sb2-0-41-3 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-S1 c4 = derive (Sb2-0-41-3 ∷ CS14 ∷ []) (CS14 ∷ Sb2-0-41-3 ∷ [])
  (rw 0 (q409 c4) ∷ []) Eq.refl

-- auto BOX(0;1234) | CCZ324: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ324 : Ws → ⟪ (Bx0-1234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ324 c4 = derive (Bx0-1234 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1234 ∷ [])
  (rw 1 (q92 c4) ∷
   rw 0 (q20 c4) ∷
   rw 0 (q21 c4) ∷
   rw⁻ 0 (q22 c4) ∷
   rw 1 (q23 c4) ∷
   rw 1 (q24 c4) ∷
   rw 0 (q92 c4) ∷ []) Eq.refl

private
  q410 : Ws → Eqn
  q410 c4 = eqn (Sw01 ∷ Bx2-0413 ∷ []) (Bx2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0413⟩ (lit c4))

-- sym12 @0214213043: 5 steps
lem-sym12-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ []) ⟫ʷ
lem-sym12-at0214213043 c4 = derive (Bx2-4103 ∷ []) (Bx2-1403 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q309 c4) ∷
   rw 1 (q360 c4) ∷
   rw 0 (q410 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

private
  q411 : Ws → Eqn
  q411 c4 = eqn (CX23 ∷ Sw23 ∷ []) (Sw23 ∷ CX32 ∷ []) (wl0277 (lit c4))
  q412 : Ws → Eqn
  q412 c4 = eqn (CX23 ∷ Bx0-1234 ∷ CX23 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CX23-beta c4)

-- CX23-beta @2332: 8 steps
lem-CX23-beta-at2332 : Ws → ⟪ (CX32 ∷ Bx0-1324 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CX23-beta-at2332 c4 = derive (CX32 ∷ Bx0-1324 ∷ CX32 ∷ []) (Bx0-1324 ∷ CCZ134 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw⁻ 1 (q411 c4) ∷
   rw 2 (q7 c4) ∷
   rw⁻ 3 (q411 c4) ∷
   rw 1 (q412 c4) ∷
   rw 0 (q9 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q413 : Ws → Eqn
  q413 c4 = eqn (Sw34 ∷ CX42 ∷ []) (CX32 ∷ Sw34 ∷ []) (lem-nat-3-CX42 (lit c4))
  q414 : Ws → Eqn
  q414 c4 = eqn (CX32 ∷ Bx0-1324 ∷ CX32 ∷ []) (Bx0-1324 ∷ CCZ134 ∷ []) (lem-CX23-beta-at2332 c4)
  q415 : Ws → Eqn
  q415 c4 = eqn (CCZ134 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ134 ∷ []) (wl0154 (lit c4))

-- CX23-beta @243243: 8 steps
lem-CX23-beta-at243243 : Ws → ⟪ (CX42 ∷ Bx0-1423 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CX23-beta-at243243 c4 = derive (CX42 ∷ Bx0-1423 ∷ CX42 ∷ []) (Bx0-1423 ∷ CCZ134 ∷ [])
  (rw⁻ 0 (q50 c4) ∷
   rw 1 (q413 c4) ∷
   rw 2 (q67 c4) ∷
   rw 3 (q413 c4) ∷
   rw 1 (q414 c4) ∷
   rw 0 (q56 c4) ∷
   rw⁻ 1 (q415 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

private
  q416 : Ws → Eqn
  q416 c4 = eqn (Sw01 ∷ CX42 ∷ []) (CX42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CX₁₀ • Swap ↑))
  q417 : Ws → Eqn
  q417 c4 = eqn (CX42 ∷ Bx0-1423 ∷ CX42 ∷ []) (Bx0-1423 ∷ CCZ134 ∷ []) (lem-CX23-beta-at243243 c4)

-- CX23-beta @0110243243: 8 steps
lem-CX23-beta-at0110243243 : Ws → ⟪ (CX42 ∷ Bx1-0423 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CX23-beta-at0110243243 c4 = derive (CX42 ∷ Bx1-0423 ∷ CX42 ∷ []) (Bx1-0423 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q416 c4) ∷
   rw 2 (q97 c4) ∷
   rw 3 (q416 c4) ∷
   rw 1 (q417 c4) ∷
   rw 0 (q116 c4) ∷
   rw 1 (q266 c4) ∷
   rw 2 (q25 c4) ∷ []) Eq.refl

private
  q418 : Ws → Eqn
  q418 c4 = eqn (CX42 ∷ Sw12 ∷ []) (Sw12 ∷ CX41 ∷ []) (wl0149 (lit c4))
  q419 : Ws → Eqn
  q419 c4 = eqn (CX42 ∷ Bx1-0423 ∷ CX42 ∷ []) (Bx1-0423 ∷ CCZ034 ∷ []) (lem-CX23-beta-at0110243243 c4)
  q420 : Ws → Eqn
  q420 c4 = eqn (Sw12 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4))

-- CX23-beta @0210243143: 8 steps
lem-CX23-beta-at0210243143 : Ws → ⟪ (CX41 ∷ Bx2-0413 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CX23-beta-at0210243143 c4 = derive (CX41 ∷ Bx2-0413 ∷ CX41 ∷ []) (Bx2-0413 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw⁻ 1 (q418 c4) ∷
   rw 2 (q199 c4) ∷
   rw⁻ 3 (q418 c4) ∷
   rw 1 (q419 c4) ∷
   rw 0 (q227 c4) ∷
   rw 1 (q420 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q421 : Ws → Eqn
  q421 c4 = eqn (Sw01 ∷ CX40 ∷ []) (CX41 ∷ Sw01 ∷ []) (lem-nat-0-CX40 (lit c4))
  q422 : Ws → Eqn
  q422 c4 = eqn (Sw01 ∷ Bx2-1403 ∷ []) (Bx2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1403⟩ (lit c4))
  q423 : Ws → Eqn
  q423 c4 = eqn (CX41 ∷ Bx2-0413 ∷ CX41 ∷ []) (Bx2-0413 ∷ CCZ034 ∷ []) (lem-CX23-beta-at0210243143 c4)

-- CX23-beta @02243043: 8 steps
lem-CX23-beta-at02243043 : Ws → ⟪ (CX40 ∷ Bx2-1403 ∷ CX40 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CX23-beta-at02243043 c4 = derive (CX40 ∷ Bx2-1403 ∷ CX40 ∷ []) (Bx2-1403 ∷ CCZ134 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q421 c4) ∷
   rw 2 (q422 c4) ∷
   rw 3 (q421 c4) ∷
   rw 1 (q423 c4) ∷
   rw 0 (q410 c4) ∷
   rw 1 (q255 c4) ∷
   rw 2 (q25 c4) ∷ []) Eq.refl

-- sym12 @02243043: 5 steps
lem-sym12-at02243043 : Ws → ⟪ (Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-sym12-at02243043 c4 = derive (Bx2-1403 ∷ []) (Bx2-4103 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 1 (q422 c4) ∷
   rw 1 (q217 c4) ∷
   rw 0 (q333 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

private
  q424 : Ws → Eqn
  q424 c4 = eqn (Bx0-1234 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ324 c4)

-- auto BOX(0;1234) | CCZ324 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at2332 c4 = derive (Bx0-1324 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q7 c4) ∷
   rw⁻ 2 (q128 c4) ∷
   rw 1 (q424 c4) ∷
   rw⁻ 0 (q128 c4) ∷
   rw 1 (q9 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

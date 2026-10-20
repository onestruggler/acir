{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D005 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0008 ; wl0011 ; wl0015 ; wl0017 ; wl0019 ; wl0022 ; wl0024 ; wl0025 ; wl0031 ; wl0034 ; wl0037 ; wl0039 ; wl0043 ; wl0046 ; wl0047 ; wl0056 ; wl0057 ; wl0058 ; wl0061 ; wl0062 ; wl0067 ; wl0068 ; wl0076 ; wl0078 ; wl0084 ; wl0099 ; wl0101 ; wl0104 ; wl0119 ; wl0120 ; wl0121 ; wl0132 ; wl0133 ; wl0154 ; wl0155 ; wl0257 ; wl0280 ; wl0281 ; wl0282 ; wl0306 ; wl0307 ; wl0308 ; wl0309 ; wl0310 ; wl0311 ; wl0312 ; wl0332 ; wl0360 ; wl0361 ; wl0362 ; wl0363 ; wl0364 ; wl0365 ; wl0366 ; wl0367 ; wl0368 ; wl0369 ; wl0370 ; wl0371 ; wp0045 ; wp0046 ; wp0113 ; wp0114 ; wp0123)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-CS20-beta-ci ; lem-T-beta ; lem-auto-TOFF012-∣-CCZ324 ; lem-beta-T ; lem-beta-T-at1221 ; lem-beta-T-at2332 ; lem-sym34 ; lem-sym34-at021021 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-CS20-beta-c-at1221 ; lem-SBsym ; lem-SBsymd ; lem-X1-beta ; lem-sym12-at3443 ; lem-sym23-at011220 ; lem-sym23-at01122330 ; lem-sym23-at243243 ; lem-sym23-at3443 ; lem-sym34-at122331 ; lem-sym34-at12233441 ; lem-sym34-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F5-CS01 ; lem-F5d-CS01 ; lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩ ; lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩ ; lem-auto-K0-∣-SBOX⟨1·2·34·0⟩ ; lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩ ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 ; lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩ ; lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-CS20-beta-c-at243243 ; lem-CS20-beta-ci-at243243 ; lem-auto-BOXd⟨0·1234⟩-∣-CS40 ; lem-auto-BOXd⟨0·1234⟩-∣-CSd40 ; lem-auto-CCZ012-∣-BOX⟨3·0142⟩ ; lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩ ; lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩ ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩ ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩ ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-3-BOX⟨0·1243⟩ ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ034 ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF103 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-3-BOX⟨0·1324⟩ ; lem-nat-3-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF104 ; lem-nat-1-TOFF104 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-1-BOX⟨0·1234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1243⟩ ; lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨1·0243⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·0243⟩ ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0143⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-3-BOX⟨0·1234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨0·2134⟩ ; lem-nat-0-BOX⟨0·2143⟩ ; lem-nat-0-BOX⟨0·2314⟩ ; lem-nat-0-BOX⟨1·2034⟩ ; lem-nat-0-BOX⟨1·2304⟩ ; lem-nat-0-BOXd⟨1·0423⟩ ; lem-nat-1-BOXd⟨2·0413⟩ ; lem-nat-1-CS01 ; lem-nat-1-CS02 ; lem-nat-2-BOX⟨0·1243⟩ ; lem-nat-2-BOX⟨0·1342⟩ ; lem-nat-2-BOXd⟨0·1324⟩ ; lem-nat-3-BOXd⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨0·1342⟩ ; lem-nat-0-CS04 ; lem-nat-0-CS14 ; lem-nat-0-SBOX⟨0·1·3·2⟩ ; lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·3·2⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-0-SBOXd⟨0·1·3·2⟩ ; lem-nat-0-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-CS04 ; lem-nat-1-CSd02 ; lem-nat-1-SBOX⟨1·0·3·2⟩ ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·3·1⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-1-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-SBOXd⟨2·0·3·1⟩ ; lem-nat-2-BOX⟨0·1432⟩ ; lem-nat-2-BOX⟨1·0432⟩ ; lem-nat-2-CS02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOX⟨1·0·43·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-3-BOX⟨2·0431⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOX⟨1·0·34·2⟩ ; lem-nat-3-SBOX⟨2·0·43·1⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨1·0324⟩ ; lem-nat-0-BOX⟨1·0342⟩ ; lem-nat-0-BOX⟨1·2340⟩ ; lem-nat-1-BOX⟨1·0342⟩ ; lem-nat-1-BOX⟨2·0314⟩ ; lem-nat-1-BOX⟨2·0341⟩ ; lem-nat-1-CSd01 ; lem-nat-1-CSd04 ; lem-nat-2-CS04 ; lem-nat-2-CSd04 ; lem-nat-3-CS04 ; lem-nat-3-CSd04)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨2·1034⟩ ; lem-nat-0-BOX⟨2·1304⟩ ; lem-nat-2-BOX⟨0·1423⟩ ; lem-nat-2-BOXd⟨0·1234⟩ ; lem-nat-2-CS03 ; lem-nat-2-CSd03 ; lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·23·4⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·32·4⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-CS03 ; lem-nat-3-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨0·2341⟩ ; lem-nat-0-SBOX⟨0·2·43·1⟩ ; lem-nat-0-SBOX⟨1·2·43·0⟩ ; lem-nat-0-SBOX⟨2·3·04·1⟩ ; lem-nat-0-SBOX⟨2·3·14·0⟩ ; lem-nat-1-SBOX⟨0·1·43·2⟩ ; lem-nat-1-SBOX⟨0·2·43·1⟩ ; lem-nat-1-SBOX⟨1·3·24·0⟩ ; lem-nat-1-SBOX⟨2·0·14·3⟩ ; lem-nat-2-SBOX⟨0·1·42·3⟩ ; lem-nat-2-SBOX⟨0·1·43·2⟩ ; lem-nat-2-SBOX⟨1·0·24·3⟩ ; lem-nat-3-SBOX⟨1·2·34·0⟩ ; lem-nat-3-SBOX⟨1·2·43·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-0-BOX⟨0·1432⟩ ; lem-nat-0-BOX⟨1·0432⟩ ; lem-nat-0-BOX⟨2·0143⟩ ; lem-nat-0-BOX⟨2·1043⟩ ; lem-nat-0-BOXd⟨0·1423⟩ ; lem-nat-0-SBOXd⟨0·1·42·3⟩ ; lem-nat-0-SBOXd⟨1·0·42·3⟩ ; lem-nat-1-BOX⟨1·0432⟩ ; lem-nat-1-BOX⟨1·2043⟩ ; lem-nat-1-BOX⟨2·0431⟩ ; lem-nat-1-BOX⟨3·0142⟩ ; lem-nat-1-BOX⟨3·0241⟩ ; lem-nat-1-BOXd⟨1·0423⟩ ; lem-nat-1-SBOX⟨1·0·43·2⟩ ; lem-nat-1-SBOX⟨2·0·43·1⟩ ; lem-nat-1-SBOX⟨2·3·14·0⟩ ; lem-nat-1-SBOX⟨3·0·14·2⟩ ; lem-nat-1-SBOX⟨3·0·24·1⟩ ; lem-nat-1-SBOXd⟨1·0·24·3⟩ ; lem-nat-1-SBOXd⟨1·0·42·3⟩ ; lem-nat-1-SBOXd⟨2·0·14·3⟩ ; lem-nat-1-SBOXd⟨2·0·41·3⟩ ; lem-nat-2-BOX⟨1·0423⟩ ; lem-nat-2-BOX⟨2·0341⟩ ; lem-nat-2-BOX⟨3·0241⟩ ; lem-nat-2-SBOX⟨1·0·42·3⟩ ; lem-nat-2-SBOX⟨1·2·34·0⟩ ; lem-nat-2-SBOX⟨1·3·24·0⟩ ; lem-nat-2-SBOX⟨2·0·34·1⟩ ; lem-nat-2-SBOX⟨3·0·24·1⟩ ; lem-nat-2-SBOXd⟨1·0·24·3⟩ ; lem-nat-2-SBOXd⟨1·0·34·2⟩ ; lem-nat-2-SBOXd⟨1·0·42·3⟩ ; lem-nat-2-SBOXd⟨1·0·43·2⟩ ; lem-nat-3-BOX⟨0·1342⟩ ; lem-nat-3-BOX⟨2·0341⟩ ; lem-nat-3-BOXd⟨0·1324⟩ ; lem-nat-3-SBOX⟨2·0·34·1⟩ ; lem-nat-3-SBOXd⟨0·1·32·4⟩ ; lem-nat-3-SBOXd⟨0·1·42·3⟩ ; lem-nat-3-SBOXd⟨1·0·34·2⟩ ; lem-nat-3-SBOXd⟨1·0·43·2⟩)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CS04 ∷ []) (CS04 ∷ []) (wp0113 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1243 ∷ []) (lem-sym34 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx0-1243 ∷ []) (Bx0-1423 ∷ []) (lem-sym23-at3443 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CS04 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS04 ∷ []) (lem-CS20-beta-c-at243243 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Bx0-1423 ∷ []) (Bx0-1243 ∷ []) (lem-sym23-at243243 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Bx0-1243 ∷ []) (Bx0-1234 ∷ []) (lem-sym34-at3443 c4)

-- auto BOX(0;1234) | CS40: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS40 : Ws → ⟪ (Bx0-1234 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS40 c4 = derive (Bx0-1234 ∷ CS04 ∷ []) (CS04 ∷ Bx0-1234 ∷ [])
  (rw 1 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw 0 (q3 c4) ∷
   rw⁻ 0 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw 0 (q1 c4) ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = eqn (CS04⁻ ∷ []) (CS04⁻ ∷ []) (wp0114 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CS04⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS04⁻ ∷ []) (lem-CS20-beta-ci-at243243 c4)

-- auto BOX(0;1234) | CSd40: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd40 : Ws → ⟪ (Bx0-1234 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd40 c4 = derive (Bx0-1234 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx0-1234 ∷ [])
  (rw 1 (q7 c4) ∷
   rw 0 (q2 c4) ∷
   rw 0 (q3 c4) ∷
   rw⁻ 0 (q8 c4) ∷
   rw 1 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw 0 (q7 c4) ∷ []) Eq.refl

private
  q9 : Ws → Eqn
  q9 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Sw01 ∷ Bx1-2034 ∷ []) (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Bx0-2134 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at1221 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) (wl0099 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 (lit c4))

-- beta-T @011220: 8 steps
lem-beta-T-at011220 : Ws → ⟪ (Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) ⟫ʷ
lem-beta-T-at011220 c4 = derive (Bx1-2034 ∷ []) (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q10 c4) ∷
   rw 1 (q11 c4) ∷
   rw 0 (q12 c4) ∷
   rw 1 (q13 c4) ∷
   rw 2 (q12 c4) ∷
   rw 3 (q13 c4) ∷
   rw 4 (q9 c4) ∷ []) Eq.refl

private
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx1-2034 ∷ []) (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) (lem-beta-T-at011220 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (S0⁻ ∷ Toff102 ∷ []) (Toff102 ∷ S0⁻ ∷ []) (wl0361 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (S0⁻ ∷ CCZ134 ∷ []) (CCZ134 ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))

-- auto Sd0 | BOX(1;2034): 6 steps
lem-auto-Sd0-∣-BOX⟨1·2034⟩ : Ws → ⟪ (S0⁻ ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ S0⁻ ∷ []) ⟫ʷ
lem-auto-Sd0-∣-BOX⟨1·2034⟩ c4 = derive (S0⁻ ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ S0⁻ ∷ [])
  (rw 1 (q14 c4) ∷
   rw 0 (q15 c4) ∷
   rw 1 (q16 c4) ∷
   rw 2 (q15 c4) ∷
   rw 3 (q16 c4) ∷
   rw⁻ 0 (q14 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = eqn (S0⁻ ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ S0⁻ ∷ []) (lem-auto-Sd0-∣-BOX⟨1·2034⟩ c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (S0⁻ ∷ Toff403 ∷ []) (Toff403 ∷ S0⁻ ∷ []) (wp0123 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CS24 ∷ S0⁻ ∷ []) (S0⁻ ∷ CS24 ∷ []) (wl0362 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CS24⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ CS24⁻ ∷ []) (wl0363 (lit c4))

-- auto Sd0 | SBOX(1;2;03;4): 11 steps
lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩ : Ws → ⟪ (S0⁻ ∷ Sb1-2-03-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-03-4 ∷ S0⁻ ∷ []) ⟫ʷ
lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩ c4 = derive (S0⁻ ∷ Sb1-2-03-4 ∷ []) (Sb1-2-03-4 ∷ S0⁻ ∷ [])
  (re 1 1 (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ Sb⁻1-2-4-3 ∷ []) ∷
   rw 0 (q17 c4) ∷
   rw 1 (q18 c4) ∷
   re 3 1 (CS24 ∷ []) ∷
   rw⁻ 2 (q19 c4) ∷
   re 2 1 (Sb1-2-4-3 ∷ []) ∷
   rw 3 (q18 c4) ∷
   re 5 1 (CS24⁻ ∷ []) ∷
   rw⁻ 4 (q20 c4) ∷
   re 4 1 (Sb⁻1-2-4-3 ∷ []) ∷
   re 0 5 (Sb1-2-03-4 ∷ []) ∷ []) Eq.refl

private
  q21 : Ws → Eqn
  q21 c4 = eqn (Sw01 ∷ Bx1-2340 ∷ []) (Bx0-2341 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2340⟩ (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (Bx0-2341 ∷ []) (Bx0-2314 ∷ []) (lem-sym34-at12233441 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw01 ∷ Bx0-2314 ∷ []) (Bx1-2304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2314⟩ (lit c4))

-- sym34 @0112233440: 5 steps
lem-sym34-at0112233440 : Ws → ⟪ (Bx1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ []) ⟫ʷ
lem-sym34-at0112233440 c4 = derive (Bx1-2340 ∷ []) (Bx1-2304 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   rw 0 (q23 c4) ∷
   rw 1 (q9 c4) ∷ []) Eq.refl

private
  q24 : Ws → Eqn
  q24 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (Sw12 ∷ CS01⁻ ∷ []) (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (Sw12 ∷ Bx0-2134 ∷ []) (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CS02⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CS20-beta-ci c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (Sw12 ∷ Bx0-1234 ∷ []) (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (Sw12 ∷ CS02⁻ ∷ []) (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 (lit c4))

-- CS20-beta-ci @1221: 7 steps
lem-CS20-beta-ci-at1221 : Ws → ⟪ (CS01⁻ ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CS20-beta-ci-at1221 c4 = derive (CS01⁻ ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CS01⁻ ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q26 c4) ∷
   rw 1 (q27 c4) ∷
   rw 0 (q28 c4) ∷
   rw 1 (q29 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q30 : Ws → Eqn
  q30 c4 = eqn (CS01⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS01⁻ ∷ []) (wl0133 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CS01⁻ ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CS01⁻ ∷ []) (lem-CS20-beta-ci-at1221 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Sw01 ∷ Bx0-2134 ∷ []) (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ (lit c4))

-- CS20-beta-ci @011220: 7 steps
lem-CS20-beta-ci-at011220 : Ws → ⟪ (CS01⁻ ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CS20-beta-ci-at011220 c4 = derive (CS01⁻ ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CS01⁻ ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw⁻ 1 (q30 c4) ∷
   rw 2 (q10 c4) ∷
   rw 1 (q31 c4) ∷
   rw 0 (q32 c4) ∷
   rw⁻ 1 (q30 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q33 : Ws → Eqn
  q33 c4 = eqn (Sw01 ∷ Bx1-2304 ∷ []) (Bx0-2314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2304⟩ (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (Bx0-2314 ∷ []) (Bx0-2341 ∷ []) (lem-sym34-at122331 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (Sw01 ∷ Bx0-2341 ∷ []) (Bx1-2340 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2341⟩ (lit c4))

-- sym34 @01122330: 5 steps
lem-sym34-at01122330 : Ws → ⟪ (Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ []) ⟫ʷ
lem-sym34-at01122330 c4 = derive (Bx1-2304 ∷ []) (Bx1-2340 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q33 c4) ∷
   rw 1 (q34 c4) ∷
   rw 0 (q35 c4) ∷
   rw 1 (q9 c4) ∷ []) Eq.refl

private
  q36 : Ws → Eqn
  q36 c4 = eqn (CS01⁻ ∷ []) (CS01⁻ ∷ []) (wl0360 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (Bx1-2340 ∷ []) (Bx1-2304 ∷ []) (lem-sym34-at0112233440 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Bx1-2304 ∷ []) (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (CS01⁻ ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CS01⁻ ∷ []) (lem-CS20-beta-ci-at011220 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (Bx1-2034 ∷ []) (Bx1-2304 ∷ []) (lem-sym23-at011220 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (Bx1-2304 ∷ []) (Bx1-2340 ∷ []) (lem-sym34-at01122330 c4)

-- auto CSd01 | BOX(1;2340): 7 steps
lem-auto-CSd01-∣-BOX⟨1·2340⟩ : Ws → ⟪ (CS01⁻ ∷ Bx1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2340⟩ c4 = derive (CS01⁻ ∷ Bx1-2340 ∷ []) (Bx1-2340 ∷ CS01⁻ ∷ [])
  (rw 0 (q36 c4) ∷
   rw 1 (q37 c4) ∷
   rw 1 (q38 c4) ∷
   rw 0 (q39 c4) ∷
   rw 0 (q40 c4) ∷
   rw 0 (q41 c4) ∷
   rw 1 (q36 c4) ∷ []) Eq.refl

private
  q42 : Ws → Eqn
  q42 c4 = eqn (CS01 ∷ Sw01 ∷ []) (Sw01 ∷ CS01 ∷ []) (wl0132 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CS01 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CS01 ∷ []) (lem-CS20-beta-c-at1221 c4)

-- CS20-beta-c @011220: 7 steps
lem-CS20-beta-c-at011220 : Ws → ⟪ (CS01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CS01 ∷ []) ⟫ʷ
lem-CS20-beta-c-at011220 c4 = derive (CS01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CS01 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw⁻ 1 (q42 c4) ∷
   rw 2 (q10 c4) ∷
   rw 1 (q43 c4) ∷
   rw 0 (q32 c4) ∷
   rw⁻ 1 (q42 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q44 : Ws → Eqn
  q44 c4 = eqn (CS01 ∷ []) (CS01 ∷ []) (wl0332 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CS01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CS01 ∷ []) (lem-CS20-beta-c-at011220 c4)

-- auto CS01 | BOX(1;2340): 7 steps
lem-auto-CS01-∣-BOX⟨1·2340⟩ : Ws → ⟪ (CS01 ∷ Bx1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2340⟩ c4 = derive (CS01 ∷ Bx1-2340 ∷ []) (Bx1-2340 ∷ CS01 ∷ [])
  (rw 0 (q44 c4) ∷
   rw 1 (q37 c4) ∷
   rw 1 (q38 c4) ∷
   rw 0 (q45 c4) ∷
   rw 0 (q40 c4) ∷
   rw 0 (q41 c4) ∷
   rw 1 (q44 c4) ∷ []) Eq.refl

private
  q46 : Ws → Eqn
  q46 c4 = eqn (Toff012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Toff012 ∷ []) (lem-T-beta c4)

-- auto TOFF012 | BOX(0;1234): 1 steps
lem-auto-TOFF012-∣-BOX⟨0·1234⟩ : Ws → ⟪ (Toff012 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·1234⟩ c4 = derive (Toff012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Toff012 ∷ [])
  (rw 0 (q46 c4) ∷ []) Eq.refl

private
  q47 : Ws → Eqn
  q47 c4 = eqn (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (Toff324 ∷ []) (wl0364 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (K3 ∷ Toff012 ∷ []) (Toff012 ∷ K3 ∷ []) (wl0365 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (Toff012 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-CCZ324 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (K3⁻ ∷ Toff012 ∷ []) (Toff012 ∷ K3⁻ ∷ []) (wl0366 (lit c4))

-- auto TOFF012 | TOFF324: 5 steps
lem-auto-TOFF012-∣-TOFF324 : Ws → ⟪ (Toff012 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-TOFF324 c4 = derive (Toff012 ∷ Toff324 ∷ []) (Toff324 ∷ Toff012 ∷ [])
  (rw⁻ 1 (q47 c4) ∷
   rw⁻ 0 (q48 c4) ∷
   rw 1 (q49 c4) ∷
   rw⁻ 2 (q50 c4) ∷
   rw 0 (q47 c4) ∷ []) Eq.refl

private
  q51 : Ws → Eqn
  q51 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (Toff012 ∷ Sw34 ∷ []) (Sw34 ∷ Toff012 ∷ []) (c₃ (Toff) (Swap))
  q53 : Ws → Eqn
  q53 c4 = eqn (Sw34 ∷ Toff423 ∷ []) (Toff324 ∷ Sw34 ∷ []) (wl0120 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (Toff012 ∷ Toff324 ∷ []) (Toff324 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-TOFF324 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (Sw34 ∷ Toff324 ∷ []) (Toff423 ∷ Sw34 ∷ []) (wl0119 (lit c4))

-- auto TOFF012 | TOFF324 @3443: 7 steps
lem-auto-TOFF012-∣-TOFF324-at3443 : Ws → ⟪ (Toff012 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-TOFF324-at3443 c4 = derive (Toff012 ∷ Toff423 ∷ []) (Toff423 ∷ Toff012 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw⁻ 1 (q52 c4) ∷
   rw 2 (q53 c4) ∷
   rw 1 (q54 c4) ∷
   rw 0 (q55 c4) ∷
   rw⁻ 1 (q52 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q56 : Ws → Eqn
  q56 c4 = eqn (Toff012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·1234⟩ c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (Toff012 ∷ Toff423 ∷ []) (Toff423 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-TOFF324-at3443 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (CS14 ∷ Toff012 ∷ []) (Toff012 ∷ CS14 ∷ []) (wp0046 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (CS14⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS14⁻ ∷ []) (wp0045 c4)

-- auto TOFF012 | SBOX(0;1;23;4): 11 steps
lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩ : Ws → ⟪ (Toff012 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩ c4 = derive (Toff012 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-23-4 ∷ Toff012 ∷ [])
  (re 1 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   rw 0 (q56 c4) ∷
   rw 1 (q57 c4) ∷
   re 3 1 (CS14 ∷ []) ∷
   rw⁻ 2 (q58 c4) ∷
   re 2 1 (Sb0-1-4-3 ∷ []) ∷
   rw 3 (q57 c4) ∷
   re 5 1 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q59 c4) ∷
   re 4 1 (Sb⁻0-1-4-3 ∷ []) ∷
   re 0 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = eqn (Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑))
  q61 : Ws → Eqn
  q61 c4 = eqn (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CS01 ∷ []) (lem-F5-CS01 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (Sw12 ∷ CS01 ∷ []) (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4))

-- F5 CS01 @1221: 8 steps
lem-F5-CS01-at1221 : Ws → ⟪ (X4 ∷ Sb1-0-42-3 ∷ X4 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
lem-F5-CS01-at1221 c4 = derive (X4 ∷ Sb1-0-42-3 ∷ X4 ∷ Sb1-0-42-3 ∷ []) (CS02 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q60 c4) ∷
   rw 2 (q61 c4) ∷
   rw 3 (q60 c4) ∷
   rw 4 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   rw 0 (q63 c4) ∷
   rw 1 (q24 c4) ∷ []) Eq.refl

private
  q64 : Ws → Eqn
  q64 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (Sw23 ∷ X4 ∷ []) (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X))
  q66 : Ws → Eqn
  q66 c4 = eqn (Sw23 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (X4 ∷ Sb1-0-42-3 ∷ X4 ∷ Sb1-0-42-3 ∷ []) (CS02 ∷ []) (lem-F5-CS01-at1221 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (Sw23 ∷ CS02 ∷ []) (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4))

-- F5 CS01 @132132: 8 steps
lem-F5-CS01-at132132 : Ws → ⟪ (X4 ∷ Sb1-0-43-2 ∷ X4 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ []) ⟫ʷ
lem-F5-CS01-at132132 c4 = derive (X4 ∷ Sb1-0-43-2 ∷ X4 ∷ Sb1-0-43-2 ∷ []) (CS03 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q65 c4) ∷
   rw 2 (q66 c4) ∷
   rw 3 (q65 c4) ∷
   rw 4 (q66 c4) ∷
   rw 1 (q67 c4) ∷
   rw 0 (q68 c4) ∷
   rw 1 (q64 c4) ∷ []) Eq.refl

private
  q69 : Ws → Eqn
  q69 c4 = eqn (Sw34 ∷ X3 ∷ []) (X4 ∷ Sw34 ∷ []) (wl0367 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (Sw34 ∷ Sb1-0-34-2 ∷ []) (Sb1-0-43-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·34·2⟩ (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (X4 ∷ Sb1-0-43-2 ∷ X4 ∷ Sb1-0-43-2 ∷ []) (CS03 ∷ []) (lem-F5-CS01-at132132 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (Sw34 ∷ CS03 ∷ []) (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 (lit c4))

-- F5 CS01 @14213243: 8 steps
lem-F5-CS01-at14213243 : Ws → ⟪ (X3 ∷ Sb1-0-34-2 ∷ X3 ∷ Sb1-0-34-2 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
lem-F5-CS01-at14213243 c4 = derive (X3 ∷ Sb1-0-34-2 ∷ X3 ∷ Sb1-0-34-2 ∷ []) (CS04 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q69 c4) ∷
   rw 2 (q70 c4) ∷
   rw 3 (q69 c4) ∷
   rw 4 (q70 c4) ∷
   rw 1 (q71 c4) ∷
   rw 0 (q72 c4) ∷
   rw 1 (q51 c4) ∷ []) Eq.refl

private
  q73 : Ws → Eqn
  q73 c4 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wl0368 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (Sw23 ∷ Sb1-0-24-3 ∷ []) (Sb1-0-34-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·24·3⟩ (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (X3 ∷ Sb1-0-34-2 ∷ X3 ∷ Sb1-0-34-2 ∷ []) (CS04 ∷ []) (lem-F5-CS01-at14213243 c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (Sw23 ∷ CS04 ∷ []) (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4))

-- F5 CS01 @142142: 8 steps
lem-F5-CS01-at142142 : Ws → ⟪ (X2 ∷ Sb1-0-24-3 ∷ X2 ∷ Sb1-0-24-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
lem-F5-CS01-at142142 c4 = derive (X2 ∷ Sb1-0-24-3 ∷ X2 ∷ Sb1-0-24-3 ∷ []) (CS04 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q73 c4) ∷
   rw 2 (q74 c4) ∷
   rw 3 (q73 c4) ∷
   rw 4 (q74 c4) ∷
   rw 1 (q75 c4) ∷
   rw 0 (q76 c4) ∷
   rw 1 (q64 c4) ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = eqn (Sw12 ∷ X1 ∷ []) (X2 ∷ Sw12 ∷ []) (wl0369 (lit c4))
  q78 : Ws → Eqn
  q78 c4 = eqn (Sw12 ∷ Sb2-0-14-3 ∷ []) (Sb1-0-24-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·14·3⟩ (lit c4))
  q79 : Ws → Eqn
  q79 c4 = eqn (X2 ∷ Sb1-0-24-3 ∷ X2 ∷ Sb1-0-24-3 ∷ []) (CS04 ∷ []) (lem-F5-CS01-at142142 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4))

-- F5 CS01 @1441: 8 steps
lem-F5-CS01-at1441 : Ws → ⟪ (X1 ∷ Sb2-0-14-3 ∷ X1 ∷ Sb2-0-14-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
lem-F5-CS01-at1441 c4 = derive (X1 ∷ Sb2-0-14-3 ∷ X1 ∷ Sb2-0-14-3 ∷ []) (CS04 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q77 c4) ∷
   rw 2 (q78 c4) ∷
   rw 3 (q77 c4) ∷
   rw 4 (q78 c4) ∷
   rw 1 (q79 c4) ∷
   rw 0 (q80 c4) ∷
   rw 1 (q24 c4) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = eqn (Sb2-0-41-3 ∷ []) (Sb2-0-14-3 ∷ []) (lem-SBsym c4)

-- SBsym @1221: 5 steps
lem-SBsym-at1221 : Ws → ⟪ (Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-24-3 ∷ []) ⟫ʷ
lem-SBsym-at1221 c4 = derive (Sb1-0-42-3 ∷ []) (Sb1-0-24-3 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q61 c4) ∷
   rw 1 (q81 c4) ∷
   rw 0 (q78 c4) ∷
   rw 1 (q24 c4) ∷ []) Eq.refl

private
  q82 : Ws → Eqn
  q82 c4 = eqn (Sb1-0-42-3 ∷ []) (Sb1-0-24-3 ∷ []) (lem-SBsym-at1221 c4)

-- SBsym @132132: 5 steps
lem-SBsym-at132132 : Ws → ⟪ (Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-34-2 ∷ []) ⟫ʷ
lem-SBsym-at132132 c4 = derive (Sb1-0-43-2 ∷ []) (Sb1-0-34-2 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q66 c4) ∷
   rw 1 (q82 c4) ∷
   rw 0 (q74 c4) ∷
   rw 1 (q64 c4) ∷ []) Eq.refl

private
  q83 : Ws → Eqn
  q83 c4 = eqn (Sb1-0-43-2 ∷ []) (Sb1-0-34-2 ∷ []) (lem-SBsym-at132132 c4)

-- SBsym @14213243: 5 steps
lem-SBsym-at14213243 : Ws → ⟪ (Sb1-0-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ []) ⟫ʷ
lem-SBsym-at14213243 c4 = derive (Sb1-0-34-2 ∷ []) (Sb1-0-43-2 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q70 c4) ∷
   rw 1 (q83 c4) ∷
   rw 0 (q70 c4) ∷
   rw 1 (q51 c4) ∷ []) Eq.refl

private
  q84 : Ws → Eqn
  q84 c4 = eqn (Sb1-0-34-2 ∷ []) (Sb1-0-43-2 ∷ []) (lem-SBsym-at14213243 c4)

-- SBsym @142142: 5 steps
lem-SBsym-at142142 : Ws → ⟪ (Sb1-0-24-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ []) ⟫ʷ
lem-SBsym-at142142 c4 = derive (Sb1-0-24-3 ∷ []) (Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q74 c4) ∷
   rw 1 (q84 c4) ∷
   rw 0 (q66 c4) ∷
   rw 1 (q64 c4) ∷ []) Eq.refl

private
  q85 : Ws → Eqn
  q85 c4 = eqn (Sb1-0-24-3 ∷ []) (Sb1-0-42-3 ∷ []) (lem-SBsym-at142142 c4)

-- SBsym @1441: 5 steps
lem-SBsym-at1441 : Ws → ⟪ (Sb2-0-14-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ
lem-SBsym-at1441 c4 = derive (Sb2-0-14-3 ∷ []) (Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q78 c4) ∷
   rw 1 (q85 c4) ∷
   rw 0 (q61 c4) ∷
   rw 1 (q24 c4) ∷ []) Eq.refl

private
  q86 : Ws → Eqn
  q86 c4 = eqn (Sw34 ∷ Bx0-1243 ∷ []) (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ (lit c4))
  q87 : Ws → Eqn
  q87 c4 = eqn (Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (Sw34 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 (lit c4))

-- beta-T @3443: 8 steps
lem-beta-T-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-T-at3443 c4 = derive (Bx0-1243 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q86 c4) ∷
   rw 1 (q87 c4) ∷
   rw⁻ 0 (q52 c4) ∷
   rw 1 (q88 c4) ∷
   rw⁻ 2 (q52 c4) ∷
   rw 3 (q88 c4) ∷
   rw 4 (q51 c4) ∷ []) Eq.refl

private
  q89 : Ws → Eqn
  q89 c4 = eqn (Sw01 ∷ Bx1-0243 ∷ []) (Bx0-1243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0243⟩ (lit c4))
  q90 : Ws → Eqn
  q90 c4 = eqn (Bx0-1243 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at3443 c4)

-- beta-T @01103443: 8 steps
lem-beta-T-at01103443 : Ws → ⟪ (Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) ⟫ʷ
lem-beta-T-at01103443 c4 = derive (Bx1-0243 ∷ []) (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q89 c4) ∷
   rw 1 (q90 c4) ∷
   rw 0 (q12 c4) ∷
   rw 1 (q13 c4) ∷
   rw 2 (q12 c4) ∷
   rw 3 (q13 c4) ∷
   rw 4 (q9 c4) ∷ []) Eq.refl

private
  q91 : Ws → Eqn
  q91 c4 = eqn (Sw12 ∷ Bx2-0143 ∷ []) (Bx1-0243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0143⟩ (lit c4))
  q92 : Ws → Eqn
  q92 c4 = eqn (Bx1-0243 ∷ []) (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) (lem-beta-T-at01103443 c4)
  q93 : Ws → Eqn
  q93 c4 = eqn (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) (wl0047 (lit c4))
  q94 : Ws → Eqn
  q94 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl0084 (lit c4))

-- beta-T @0210213443: 8 steps
lem-beta-T-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) ⟫ʷ
lem-beta-T-at0210213443 c4 = derive (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q91 c4) ∷
   rw 1 (q92 c4) ∷
   rw 0 (q93 c4) ∷
   rw⁻ 1 (q94 c4) ∷
   rw 2 (q93 c4) ∷
   rw⁻ 3 (q94 c4) ∷
   rw 4 (q24 c4) ∷ []) Eq.refl

private
  q95 : Ws → Eqn
  q95 c4 = eqn (Sw23 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ (lit c4))
  q96 : Ws → Eqn
  q96 c4 = eqn (Sw23 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4))
  q97 : Ws → Eqn
  q97 c4 = eqn (Sb⁻0-1-2-3 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩ c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (Sw23 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4))
  q99 : Ws → Eqn
  q99 c4 = eqn (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ (lit c4))

-- auto SBOXd(0;1;2;3) | SBOX(0;1;43;2) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at2332 : Ws → ⟪ (Sb⁻0-1-3-2 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at2332 c4 = derive (Sb⁻0-1-3-2 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb⁻0-1-3-2 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q95 c4) ∷
   rw 2 (q96 c4) ∷
   rw 1 (q97 c4) ∷
   rw 0 (q98 c4) ∷
   rw 1 (q99 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = eqn (Sw01 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4))
  q101 : Ws → Eqn
  q101 c4 = eqn (Sw01 ∷ Sb1-0-42-3 ∷ []) (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4))
  q102 : Ws → Eqn
  q102 c4 = eqn (Sb⁻0-1-3-2 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at2332 c4)
  q103 : Ws → Eqn
  q103 c4 = eqn (Sw01 ∷ Sb0-1-42-3 ∷ []) (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4))
  q104 : Ws → Eqn
  q104 c4 = eqn (Sw01 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·3·2⟩ (lit c4))

-- auto SBOXd(0;1;2;3) | SBOX(0;1;43;2) @01102332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at01102332 : Ws → ⟪ (Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at01102332 c4 = derive (Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ Sb⁻1-0-3-2 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q100 c4) ∷
   rw 2 (q101 c4) ∷
   rw 1 (q102 c4) ∷
   rw 0 (q103 c4) ∷
   rw 1 (q104 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q105 : Ws → Eqn
  q105 c4 = eqn (Sw12 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4))
  q106 : Ws → Eqn
  q106 c4 = eqn (Sw12 ∷ Sb2-0-41-3 ∷ []) (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4))
  q107 : Ws → Eqn
  q107 c4 = eqn (Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ Sb⁻1-0-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at01102332 c4)
  q108 : Ws → Eqn
  q108 c4 = eqn (Sw12 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·3·2⟩ (lit c4))

-- auto SBOXd(0;1;2;3) | SBOX(0;1;43;2) @02102331: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 : Ws → ⟪ (Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 c4 = derive (Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q105 c4) ∷
   rw 2 (q106 c4) ∷
   rw 1 (q107 c4) ∷
   rw 0 (q61 c4) ∷
   rw 1 (q108 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q109 : Ws → Eqn
  q109 c4 = eqn (K0⁻ ∷ Sw34 ∷ []) (Sw34 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ ↑))
  q110 : Ws → Eqn
  q110 c4 = eqn (Sw34 ∷ Sb1-2-43-0 ∷ []) (Sb1-2-34-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·43·0⟩ (lit c4))
  q111 : Ws → Eqn
  q111 c4 = eqn (K0⁻ ∷ Sb1-2-34-0 ∷ []) (Sb1-2-34-0 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩ c4)
  q112 : Ws → Eqn
  q112 c4 = eqn (Sw34 ∷ Sb1-2-34-0 ∷ []) (Sb1-2-43-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·34·0⟩ (lit c4))

-- auto Kd0 | SBOX(1;2;34;0) @3443: 7 steps
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at3443 : Ws → ⟪ (K0⁻ ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at3443 c4 = derive (K0⁻ ∷ Sb1-2-43-0 ∷ []) (Sb1-2-43-0 ∷ K0⁻ ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw⁻ 1 (q109 c4) ∷
   rw 2 (q110 c4) ∷
   rw 1 (q111 c4) ∷
   rw 0 (q112 c4) ∷
   rw⁻ 1 (q109 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q113 : Ws → Eqn
  q113 c4 = eqn (K0⁻ ∷ Sw01 ∷ []) (Sw01 ∷ K1⁻ ∷ []) (wl0257 (lit c4))
  q114 : Ws → Eqn
  q114 c4 = eqn (Sw01 ∷ Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4))
  q115 : Ws → Eqn
  q115 c4 = eqn (K0⁻ ∷ Sb1-2-43-0 ∷ []) (Sb1-2-43-0 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at3443 c4)
  q116 : Ws → Eqn
  q116 c4 = eqn (Sw01 ∷ Sb1-2-43-0 ∷ []) (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4))
  q117 : Ws → Eqn
  q117 c4 = eqn (K1⁻ ∷ Sw01 ∷ []) (Sw01 ∷ K0⁻ ∷ []) (wl0306 (lit c4))

-- auto Kd0 | SBOX(1;2;34;0) @01103443: 7 steps
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at01103443 : Ws → ⟪ (K1⁻ ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ K1⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at01103443 c4 = derive (K1⁻ ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ K1⁻ ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw⁻ 1 (q113 c4) ∷
   rw 2 (q114 c4) ∷
   rw 1 (q115 c4) ∷
   rw 0 (q116 c4) ∷
   rw⁻ 1 (q117 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q118 : Ws → Eqn
  q118 c4 = eqn (K1⁻ ∷ Sw12 ∷ []) (Sw12 ∷ K2⁻ ∷ []) (wl0307 (lit c4))
  q119 : Ws → Eqn
  q119 c4 = eqn (Sw12 ∷ Sb0-1-43-2 ∷ []) (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4))
  q120 : Ws → Eqn
  q120 c4 = eqn (K1⁻ ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ K1⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at01103443 c4)
  q121 : Ws → Eqn
  q121 c4 = eqn (Sw12 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4))
  q122 : Ws → Eqn
  q122 c4 = eqn (K2⁻ ∷ Sw12 ∷ []) (Sw12 ∷ K1⁻ ∷ []) (wl0308 (lit c4))

-- auto Kd0 | SBOX(1;2;34;0) @0210213443: 7 steps
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0210213443 : Ws → ⟪ (K2⁻ ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ K2⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0210213443 c4 = derive (K2⁻ ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ K2⁻ ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw⁻ 1 (q118 c4) ∷
   rw 2 (q119 c4) ∷
   rw 1 (q120 c4) ∷
   rw 0 (q121 c4) ∷
   rw⁻ 1 (q122 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q123 : Ws → Eqn
  q123 c4 = eqn (K2⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K3⁻ ∷ []) (wl0309 (lit c4))
  q124 : Ws → Eqn
  q124 c4 = eqn (K2⁻ ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ K2⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0210213443 c4)
  q125 : Ws → Eqn
  q125 c4 = eqn (K3⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K2⁻ ∷ []) (wl0310 (lit c4))

-- auto Kd0 | SBOX(1;2;34;0) @0310213442: 7 steps
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0310213442 : Ws → ⟪ (K3⁻ ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ K3⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0310213442 c4 = derive (K3⁻ ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ K3⁻ ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw⁻ 1 (q123 c4) ∷
   rw 2 (q96 c4) ∷
   rw 1 (q124 c4) ∷
   rw 0 (q98 c4) ∷
   rw⁻ 1 (q125 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = eqn (Sw01 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((K • iI) ↑))
  q127 : Ws → Eqn
  q127 c4 = eqn (K3⁻ ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ K3⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0310213442 c4)

-- auto Kd0 | SBOX(1;2;34;0) @03203442: 7 steps
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at03203442 : Ws → ⟪ (K3⁻ ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ K3⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at03203442 c4 = derive (K3⁻ ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ K3⁻ ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q126 c4) ∷
   rw 2 (q101 c4) ∷
   rw 1 (q127 c4) ∷
   rw 0 (q103 c4) ∷
   rw 1 (q126 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q128 : Ws → Eqn
  q128 c4 = eqn (Sw12 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K • iI))
  q129 : Ws → Eqn
  q129 c4 = eqn (K3⁻ ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ K3⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at03203442 c4)

-- auto Kd0 | SBOX(1;2;34;0) @0312203441: 7 steps
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0312203441 : Ws → ⟪ (K3⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ K3⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4 = derive (K3⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ K3⁻ ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q128 c4) ∷
   rw 2 (q106 c4) ∷
   rw 1 (q129 c4) ∷
   rw 0 (q61 c4) ∷
   rw 1 (q128 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q130 : Ws → Eqn
  q130 c4 = eqn (Sw01 ∷ Sb2-3-14-0 ∷ []) (Sb2-3-04-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·14·0⟩ (lit c4))
  q131 : Ws → Eqn
  q131 c4 = eqn (CS01 ∷ Sb2-3-04-1 ∷ []) (Sb2-3-04-1 ∷ CS01 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩ c4)
  q132 : Ws → Eqn
  q132 c4 = eqn (Sw01 ∷ Sb2-3-04-1 ∷ []) (Sb2-3-14-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·04·1⟩ (lit c4))

-- auto CS01 | SBOX(2;3;04;1) @0110: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0110 : Ws → ⟪ (CS01 ∷ Sb2-3-14-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-14-0 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0110 c4 = derive (CS01 ∷ Sb2-3-14-0 ∷ []) (Sb2-3-14-0 ∷ CS01 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw⁻ 1 (q42 c4) ∷
   rw 2 (q130 c4) ∷
   rw 1 (q131 c4) ∷
   rw 0 (q132 c4) ∷
   rw⁻ 1 (q42 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q133 : Ws → Eqn
  q133 c4 = eqn (Sw12 ∷ CS02 ∷ []) (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4))
  q134 : Ws → Eqn
  q134 c4 = eqn (Sw12 ∷ Sb1-3-24-0 ∷ []) (Sb2-3-14-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·3·24·0⟩ (lit c4))
  q135 : Ws → Eqn
  q135 c4 = eqn (CS01 ∷ Sb2-3-14-0 ∷ []) (Sb2-3-14-0 ∷ CS01 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0110 c4)
  q136 : Ws → Eqn
  q136 c4 = eqn (Sw12 ∷ Sb2-3-14-0 ∷ []) (Sb1-3-24-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·3·14·0⟩ (lit c4))

-- auto CS01 | SBOX(2;3;04;1) @021021: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at021021 : Ws → ⟪ (CS02 ∷ Sb1-3-24-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-24-0 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at021021 c4 = derive (CS02 ∷ Sb1-3-24-0 ∷ []) (Sb1-3-24-0 ∷ CS02 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q133 c4) ∷
   rw 2 (q134 c4) ∷
   rw 1 (q135 c4) ∷
   rw 0 (q136 c4) ∷
   rw 1 (q63 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q137 : Ws → Eqn
  q137 c4 = eqn (Sw23 ∷ CS03 ∷ []) (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 (lit c4))
  q138 : Ws → Eqn
  q138 c4 = eqn (Sw23 ∷ Sb1-2-34-0 ∷ []) (Sb1-3-24-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·2·34·0⟩ (lit c4))
  q139 : Ws → Eqn
  q139 c4 = eqn (CS02 ∷ Sb1-3-24-0 ∷ []) (Sb1-3-24-0 ∷ CS02 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at021021 c4)
  q140 : Ws → Eqn
  q140 c4 = eqn (Sw23 ∷ Sb1-3-24-0 ∷ []) (Sb1-2-34-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·24·0⟩ (lit c4))

-- auto CS01 | SBOX(2;3;04;1) @03102132: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at03102132 : Ws → ⟪ (CS03 ∷ Sb1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-34-0 ∷ CS03 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at03102132 c4 = derive (CS03 ∷ Sb1-2-34-0 ∷ []) (Sb1-2-34-0 ∷ CS03 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q137 c4) ∷
   rw 2 (q138 c4) ∷
   rw 1 (q139 c4) ∷
   rw 0 (q140 c4) ∷
   rw 1 (q68 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q141 : Ws → Eqn
  q141 c4 = eqn (Sw34 ∷ CS04 ∷ []) (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 (lit c4))
  q142 : Ws → Eqn
  q142 c4 = eqn (CS03 ∷ Sb1-2-34-0 ∷ []) (Sb1-2-34-0 ∷ CS03 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at03102132 c4)

-- auto CS01 | SBOX(2;3;04;1) @0410213243: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0410213243 : Ws → ⟪ (CS04 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0410213243 c4 = derive (CS04 ∷ Sb1-2-43-0 ∷ []) (Sb1-2-43-0 ∷ CS04 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q141 c4) ∷
   rw 2 (q110 c4) ∷
   rw 1 (q142 c4) ∷
   rw 0 (q112 c4) ∷
   rw 1 (q72 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q143 : Ws → Eqn
  q143 c4 = eqn (Sw01 ∷ CS14 ∷ []) (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4))
  q144 : Ws → Eqn
  q144 c4 = eqn (CS04 ∷ Sb1-2-43-0 ∷ []) (Sb1-2-43-0 ∷ CS04 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0410213243 c4)
  q145 : Ws → Eqn
  q145 c4 = eqn (Sw01 ∷ CS04 ∷ []) (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4))

-- auto CS01 | SBOX(2;3;04;1) @04203243: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04203243 : Ws → ⟪ (CS14 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS14 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04203243 c4 = derive (CS14 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS14 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q143 c4) ∷
   rw 2 (q114 c4) ∷
   rw 1 (q144 c4) ∷
   rw 0 (q116 c4) ∷
   rw 1 (q145 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q146 : Ws → Eqn
  q146 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0017 (lit c4))
  q147 : Ws → Eqn
  q147 c4 = eqn (CS14 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS14 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04203243 c4)
  q148 : Ws → Eqn
  q148 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 (lit c4))

-- auto CS01 | SBOX(2;3;04;1) @0412203143: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0412203143 : Ws → ⟪ (CS24 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CS24 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0412203143 c4 = derive (CS24 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CS24 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw⁻ 1 (q146 c4) ∷
   rw 2 (q119 c4) ∷
   rw 1 (q147 c4) ∷
   rw 0 (q121 c4) ∷
   rw⁻ 1 (q148 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q149 : Ws → Eqn
  q149 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0015 (lit c4))
  q150 : Ws → Eqn
  q150 c4 = eqn (CS24 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CS24 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0412203143 c4)
  q151 : Ws → Eqn
  q151 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0011 (lit c4))

-- auto CS01 | SBOX(2;3;04;1) @0413203142: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413203142 : Ws → ⟪ (CS34 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413203142 c4 = derive (CS34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS34 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw⁻ 1 (q149 c4) ∷
   rw 2 (q96 c4) ∷
   rw 1 (q150 c4) ∷
   rw 0 (q98 c4) ∷
   rw⁻ 1 (q151 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q152 : Ws → Eqn
  q152 c4 = eqn (Sw01 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q153 : Ws → Eqn
  q153 c4 = eqn (CS34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS34 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413203142 c4)

-- auto CS01 | SBOX(2;3;04;1) @0413213042: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413213042 : Ws → ⟪ (CS34 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413213042 c4 = derive (CS34 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CS34 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q152 c4) ∷
   rw 2 (q101 c4) ∷
   rw 1 (q153 c4) ∷
   rw 0 (q103 c4) ∷
   rw 1 (q152 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q154 : Ws → Eqn
  q154 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q155 : Ws → Eqn
  q155 c4 = eqn (CS34 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CS34 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413213042 c4)

-- auto CS01 | SBOX(2;3;04;1) @04133041: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 : Ws → ⟪ (CS34 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 c4 = derive (CS34 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS34 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q154 c4) ∷
   rw 2 (q106 c4) ∷
   rw 1 (q155 c4) ∷
   rw 0 (q61 c4) ∷
   rw 1 (q154 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q156 : Ws → Eqn
  q156 c4 = eqn (Sw34 ∷ Bx0-1423 ∷ []) (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4))
  q157 : Ws → Eqn
  q157 c4 = eqn (Bx0-1324 ∷ []) (Bx0-1342 ∷ []) (lem-sym34-at2332 c4)
  q158 : Ws → Eqn
  q158 c4 = eqn (Sw34 ∷ Bx0-1342 ∷ []) (Bx0-1432 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1342⟩ (lit c4))

-- sym34 @243243: 5 steps
lem-sym34-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-sym34-at243243 c4 = derive (Bx0-1423 ∷ []) (Bx0-1432 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q156 c4) ∷
   rw 1 (q157 c4) ∷
   rw 0 (q158 c4) ∷
   rw 1 (q51 c4) ∷ []) Eq.refl

private
  q159 : Ws → Eqn
  q159 c4 = eqn (Sw01 ∷ Bx1-0423 ∷ []) (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4))
  q160 : Ws → Eqn
  q160 c4 = eqn (Bx0-1423 ∷ []) (Bx0-1432 ∷ []) (lem-sym34-at243243 c4)
  q161 : Ws → Eqn
  q161 c4 = eqn (Sw01 ∷ Bx0-1432 ∷ []) (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ (lit c4))

-- sym34 @0110243243: 5 steps
lem-sym34-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ []) ⟫ʷ
lem-sym34-at0110243243 c4 = derive (Bx1-0423 ∷ []) (Bx1-0432 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q159 c4) ∷
   rw 1 (q160 c4) ∷
   rw 0 (q161 c4) ∷
   rw 1 (q9 c4) ∷ []) Eq.refl

private
  q162 : Ws → Eqn
  q162 c4 = eqn (Sw12 ∷ Bx2-0413 ∷ []) (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4))
  q163 : Ws → Eqn
  q163 c4 = eqn (Bx1-0423 ∷ []) (Bx1-0432 ∷ []) (lem-sym34-at0110243243 c4)
  q164 : Ws → Eqn
  q164 c4 = eqn (Sw12 ∷ Bx1-0432 ∷ []) (Bx2-0431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0432⟩ (lit c4))

-- sym34 @0210243143: 5 steps
lem-sym34-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-sym34-at0210243143 c4 = derive (Bx2-0413 ∷ []) (Bx2-0431 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q162 c4) ∷
   rw 1 (q163 c4) ∷
   rw 0 (q164 c4) ∷
   rw 1 (q24 c4) ∷ []) Eq.refl

private
  q165 : Ws → Eqn
  q165 c4 = eqn (Sw23 ∷ Bx0-1432 ∷ []) (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4))
  q166 : Ws → Eqn
  q166 c4 = eqn (Sw23 ∷ Bx0-1243 ∷ []) (Bx0-1342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1243⟩ (lit c4))

-- sym23 @2442: 5 steps
lem-sym23-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-sym23-at2442 c4 = derive (Bx0-1432 ∷ []) (Bx0-1342 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q165 c4) ∷
   rw 1 (q5 c4) ∷
   rw 0 (q166 c4) ∷
   rw 1 (q64 c4) ∷ []) Eq.refl

private
  q167 : Ws → Eqn
  q167 c4 = eqn (Sw01 ∷ Bx1-0432 ∷ []) (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ (lit c4))
  q168 : Ws → Eqn
  q168 c4 = eqn (Bx0-1432 ∷ []) (Bx0-1342 ∷ []) (lem-sym23-at2442 c4)
  q169 : Ws → Eqn
  q169 c4 = eqn (Sw01 ∷ Bx0-1342 ∷ []) (Bx1-0342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1342⟩ (lit c4))

-- sym23 @01102442: 5 steps
lem-sym23-at01102442 : Ws → ⟪ (Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ []) ⟫ʷ
lem-sym23-at01102442 c4 = derive (Bx1-0432 ∷ []) (Bx1-0342 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q167 c4) ∷
   rw 1 (q168 c4) ∷
   rw 0 (q169 c4) ∷
   rw 1 (q9 c4) ∷ []) Eq.refl

private
  q170 : Ws → Eqn
  q170 c4 = eqn (Sw12 ∷ Bx2-0431 ∷ []) (Bx1-0432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0431⟩ (lit c4))
  q171 : Ws → Eqn
  q171 c4 = eqn (Bx1-0432 ∷ []) (Bx1-0342 ∷ []) (lem-sym23-at01102442 c4)
  q172 : Ws → Eqn
  q172 c4 = eqn (Sw12 ∷ Bx1-0342 ∷ []) (Bx2-0341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0342⟩ (lit c4))

-- sym23 @02102441: 5 steps
lem-sym23-at02102441 : Ws → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-sym23-at02102441 c4 = derive (Bx2-0431 ∷ []) (Bx2-0341 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q170 c4) ∷
   rw 1 (q171 c4) ∷
   rw 0 (q172 c4) ∷
   rw 1 (q24 c4) ∷ []) Eq.refl

private
  q173 : Ws → Eqn
  q173 c4 = eqn (Sw23 ∷ Bx0-1342 ∷ []) (Bx0-1243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1342⟩ (lit c4))
  q174 : Ws → Eqn
  q174 c4 = eqn (Sw23 ∷ Toff012 ∷ []) (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4))
  q175 : Ws → Eqn
  q175 c4 = eqn (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4))

-- beta-T @233442: 8 steps
lem-beta-T-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-beta-T-at233442 c4 = derive (Bx0-1342 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q173 c4) ∷
   rw 1 (q90 c4) ∷
   rw 0 (q174 c4) ∷
   rw 1 (q175 c4) ∷
   rw 2 (q174 c4) ∷
   rw 3 (q175 c4) ∷
   rw 4 (q64 c4) ∷ []) Eq.refl

private
  q176 : Ws → Eqn
  q176 c4 = eqn (Sw01 ∷ Bx1-0342 ∷ []) (Bx0-1342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0342⟩ (lit c4))
  q177 : Ws → Eqn
  q177 c4 = eqn (Bx0-1342 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4)
  q178 : Ws → Eqn
  q178 c4 = eqn (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) (wl0101 (lit c4))
  q179 : Ws → Eqn
  q179 c4 = eqn (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4))

-- beta-T @0110233442: 8 steps
lem-beta-T-at0110233442 : Ws → ⟪ (Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CCZ124 ∷ Toff103 ∷ CCZ124 ∷ []) ⟫ʷ
lem-beta-T-at0110233442 c4 = derive (Bx1-0342 ∷ []) (Toff103 ∷ CCZ124 ∷ Toff103 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q176 c4) ∷
   rw 1 (q177 c4) ∷
   rw 0 (q178 c4) ∷
   rw 1 (q179 c4) ∷
   rw 2 (q178 c4) ∷
   rw 3 (q179 c4) ∷
   rw 4 (q9 c4) ∷ []) Eq.refl

private
  q180 : Ws → Eqn
  q180 c4 = eqn (Sw12 ∷ Bx2-0341 ∷ []) (Bx1-0342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0341⟩ (lit c4))
  q181 : Ws → Eqn
  q181 c4 = eqn (Bx1-0342 ∷ []) (Toff103 ∷ CCZ124 ∷ Toff103 ∷ CCZ124 ∷ []) (lem-beta-T-at0110233442 c4)
  q182 : Ws → Eqn
  q182 c4 = eqn (Sw12 ∷ Toff103 ∷ []) (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 (lit c4))
  q183 : Ws → Eqn
  q183 c4 = eqn (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) (wl0078 (lit c4))

-- beta-T @0210233441: 8 steps
lem-beta-T-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) ⟫ʷ
lem-beta-T-at0210233441 c4 = derive (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q180 c4) ∷
   rw 1 (q181 c4) ∷
   rw 0 (q182 c4) ∷
   rw⁻ 1 (q183 c4) ∷
   rw 2 (q182 c4) ∷
   rw⁻ 3 (q183 c4) ∷
   rw 4 (q24 c4) ∷ []) Eq.refl

private
  q184 : Ws → Eqn
  q184 c4 = eqn (Sw23 ∷ Bx0-1423 ∷ []) (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ (lit c4))

-- sym23 @233442: 5 steps
lem-sym23-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-sym23-at233442 c4 = derive (Bx0-1342 ∷ []) (Bx0-1432 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q173 c4) ∷
   rw 1 (q3 c4) ∷
   rw 0 (q184 c4) ∷
   rw 1 (q64 c4) ∷ []) Eq.refl

private
  q185 : Ws → Eqn
  q185 c4 = eqn (Bx0-1342 ∷ []) (Bx0-1432 ∷ []) (lem-sym23-at233442 c4)

-- sym23 @0110233442: 5 steps
lem-sym23-at0110233442 : Ws → ⟪ (Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ []) ⟫ʷ
lem-sym23-at0110233442 c4 = derive (Bx1-0342 ∷ []) (Bx1-0432 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q176 c4) ∷
   rw 1 (q185 c4) ∷
   rw 0 (q161 c4) ∷
   rw 1 (q9 c4) ∷ []) Eq.refl

private
  q186 : Ws → Eqn
  q186 c4 = eqn (Bx1-0342 ∷ []) (Bx1-0432 ∷ []) (lem-sym23-at0110233442 c4)

-- sym23 @0210233441: 5 steps
lem-sym23-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-sym23-at0210233441 c4 = derive (Bx2-0341 ∷ []) (Bx2-0431 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q180 c4) ∷
   rw 1 (q186 c4) ∷
   rw 0 (q164 c4) ∷
   rw 1 (q24 c4) ∷ []) Eq.refl

-- sym34 @2442: 5 steps
lem-sym34-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-sym34-at2442 c4 = derive (Bx0-1432 ∷ []) (Bx0-1423 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q165 c4) ∷
   rw 1 (q160 c4) ∷
   rw 0 (q165 c4) ∷
   rw 1 (q64 c4) ∷ []) Eq.refl

private
  q187 : Ws → Eqn
  q187 c4 = eqn (Bx0-1432 ∷ []) (Bx0-1423 ∷ []) (lem-sym34-at2442 c4)
  q188 : Ws → Eqn
  q188 c4 = eqn (Sw01 ∷ Bx0-1423 ∷ []) (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4))

-- sym34 @01102442: 5 steps
lem-sym34-at01102442 : Ws → ⟪ (Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ []) ⟫ʷ
lem-sym34-at01102442 c4 = derive (Bx1-0432 ∷ []) (Bx1-0423 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q167 c4) ∷
   rw 1 (q187 c4) ∷
   rw 0 (q188 c4) ∷
   rw 1 (q9 c4) ∷ []) Eq.refl

private
  q189 : Ws → Eqn
  q189 c4 = eqn (Bx1-0432 ∷ []) (Bx1-0423 ∷ []) (lem-sym34-at01102442 c4)
  q190 : Ws → Eqn
  q190 c4 = eqn (Sw12 ∷ Bx1-0423 ∷ []) (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4))

-- sym34 @02102441: 5 steps
lem-sym34-at02102441 : Ws → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-sym34-at02102441 c4 = derive (Bx2-0431 ∷ []) (Bx2-0413 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q170 c4) ∷
   rw 1 (q189 c4) ∷
   rw 0 (q190 c4) ∷
   rw 1 (q24 c4) ∷ []) Eq.refl

private
  q191 : Ws → Eqn
  q191 c4 = eqn (K0 ∷ Sw34 ∷ []) (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑))
  q192 : Ws → Eqn
  q192 c4 = eqn (K0 ∷ Sb1-2-34-0 ∷ []) (Sb1-2-34-0 ∷ K0 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩ c4)

-- auto K0 | SBOX(1;2;34;0) @3443: 7 steps
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at3443 : Ws → ⟪ (K0 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ K0 ∷ []) ⟫ʷ
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at3443 c4 = derive (K0 ∷ Sb1-2-43-0 ∷ []) (Sb1-2-43-0 ∷ K0 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw⁻ 1 (q191 c4) ∷
   rw 2 (q110 c4) ∷
   rw 1 (q192 c4) ∷
   rw 0 (q112 c4) ∷
   rw⁻ 1 (q191 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q193 : Ws → Eqn
  q193 c4 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wl0031 (lit c4))
  q194 : Ws → Eqn
  q194 c4 = eqn (K0 ∷ Sb1-2-43-0 ∷ []) (Sb1-2-43-0 ∷ K0 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at3443 c4)
  q195 : Ws → Eqn
  q195 c4 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wl0076 (lit c4))

-- auto K0 | SBOX(1;2;34;0) @01103443: 7 steps
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at01103443 : Ws → ⟪ (K1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ K1 ∷ []) ⟫ʷ
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at01103443 c4 = derive (K1 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ K1 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw⁻ 1 (q193 c4) ∷
   rw 2 (q114 c4) ∷
   rw 1 (q194 c4) ∷
   rw 0 (q116 c4) ∷
   rw⁻ 1 (q195 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q196 : Ws → Eqn
  q196 c4 = eqn (K1 ∷ Sw12 ∷ []) (Sw12 ∷ K2 ∷ []) (wl0062 (lit c4))
  q197 : Ws → Eqn
  q197 c4 = eqn (K1 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ K1 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at01103443 c4)
  q198 : Ws → Eqn
  q198 c4 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wl0056 (lit c4))

-- auto K0 | SBOX(1;2;34;0) @0210213443: 7 steps
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0210213443 : Ws → ⟪ (K2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ K2 ∷ []) ⟫ʷ
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0210213443 c4 = derive (K2 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ K2 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw⁻ 1 (q196 c4) ∷
   rw 2 (q119 c4) ∷
   rw 1 (q197 c4) ∷
   rw 0 (q121 c4) ∷
   rw⁻ 1 (q198 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q199 : Ws → Eqn
  q199 c4 = eqn (K2 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ []) (wl0058 (lit c4))
  q200 : Ws → Eqn
  q200 c4 = eqn (K2 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ K2 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0210213443 c4)
  q201 : Ws → Eqn
  q201 c4 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wl0057 (lit c4))

-- auto K0 | SBOX(1;2;34;0) @0310213442: 7 steps
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0310213442 : Ws → ⟪ (K3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ K3 ∷ []) ⟫ʷ
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0310213442 c4 = derive (K3 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ K3 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw⁻ 1 (q199 c4) ∷
   rw 2 (q96 c4) ∷
   rw 1 (q200 c4) ∷
   rw 0 (q98 c4) ∷
   rw⁻ 1 (q201 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q202 : Ws → Eqn
  q202 c4 = eqn (Sw01 ∷ K3 ∷ []) (K3 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑))
  q203 : Ws → Eqn
  q203 c4 = eqn (K3 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ K3 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0310213442 c4)

-- auto K0 | SBOX(1;2;34;0) @03203442: 7 steps
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at03203442 : Ws → ⟪ (K3 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ K3 ∷ []) ⟫ʷ
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at03203442 c4 = derive (K3 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ K3 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q202 c4) ∷
   rw 2 (q101 c4) ∷
   rw 1 (q203 c4) ∷
   rw 0 (q103 c4) ∷
   rw 1 (q202 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q204 : Ws → Eqn
  q204 c4 = eqn (Sw12 ∷ K3 ∷ []) (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K))
  q205 : Ws → Eqn
  q205 c4 = eqn (K3 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ K3 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at03203442 c4)

-- auto K0 | SBOX(1;2;34;0) @0312203441: 7 steps
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 : Ws → ⟪ (K3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ K3 ∷ []) ⟫ʷ
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4 = derive (K3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ K3 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q204 c4) ∷
   rw 2 (q106 c4) ∷
   rw 1 (q205 c4) ∷
   rw 0 (q61 c4) ∷
   rw 1 (q204 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q206 : Ws → Eqn
  q206 c4 = eqn (Sw23 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ (lit c4))
  q207 : Ws → Eqn
  q207 c4 = eqn (Sb0-1-2-3 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩ c4)
  q208 : Ws → Eqn
  q208 c4 = eqn (Sw23 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ (lit c4))

-- auto SBOX(0;1;2;3) | SBOX(0;1;43;2) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at2332 : Ws → ⟪ (Sb0-1-3-2 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at2332 c4 = derive (Sb0-1-3-2 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb0-1-3-2 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q206 c4) ∷
   rw 2 (q96 c4) ∷
   rw 1 (q207 c4) ∷
   rw 0 (q98 c4) ∷
   rw 1 (q208 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q209 : Ws → Eqn
  q209 c4 = eqn (Sw01 ∷ Sb1-0-3-2 ∷ []) (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4))
  q210 : Ws → Eqn
  q210 c4 = eqn (Sb0-1-3-2 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at2332 c4)
  q211 : Ws → Eqn
  q211 c4 = eqn (Sw01 ∷ Sb0-1-3-2 ∷ []) (Sb1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·3·2⟩ (lit c4))

-- auto SBOX(0;1;2;3) | SBOX(0;1;43;2) @01102332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at01102332 : Ws → ⟪ (Sb1-0-3-2 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at01102332 c4 = derive (Sb1-0-3-2 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ Sb1-0-3-2 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q209 c4) ∷
   rw 2 (q101 c4) ∷
   rw 1 (q210 c4) ∷
   rw 0 (q103 c4) ∷
   rw 1 (q211 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q212 : Ws → Eqn
  q212 c4 = eqn (Sw12 ∷ Sb2-0-3-1 ∷ []) (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4))
  q213 : Ws → Eqn
  q213 c4 = eqn (Sb1-0-3-2 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ Sb1-0-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at01102332 c4)
  q214 : Ws → Eqn
  q214 c4 = eqn (Sw12 ∷ Sb1-0-3-2 ∷ []) (Sb2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·3·2⟩ (lit c4))

-- auto SBOX(0;1;2;3) | SBOX(0;1;43;2) @02102331: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 : Ws → ⟪ (Sb2-0-3-1 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 c4 = derive (Sb2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q212 c4) ∷
   rw 2 (q106 c4) ∷
   rw 1 (q213 c4) ∷
   rw 0 (q61 c4) ∷
   rw 1 (q214 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q215 : Ws → Eqn
  q215 c4 = eqn (Bx0-1243 ∷ []) (Bx0-2143 ∷ []) (lem-sym12-at3443 c4)
  q216 : Ws → Eqn
  q216 c4 = eqn (Sw01 ∷ Bx0-2143 ∷ []) (Bx1-2043 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2143⟩ (lit c4))

-- sym12 @01103443: 5 steps
lem-sym12-at01103443 : Ws → ⟪ (Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2043 ∷ []) ⟫ʷ
lem-sym12-at01103443 c4 = derive (Bx1-0243 ∷ []) (Bx1-2043 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q89 c4) ∷
   rw 1 (q215 c4) ∷
   rw 0 (q216 c4) ∷
   rw 1 (q9 c4) ∷ []) Eq.refl

private
  q217 : Ws → Eqn
  q217 c4 = eqn (Bx1-0243 ∷ []) (Bx1-2043 ∷ []) (lem-sym12-at01103443 c4)
  q218 : Ws → Eqn
  q218 c4 = eqn (Sw12 ∷ Bx1-2043 ∷ []) (Bx2-1043 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2043⟩ (lit c4))

-- sym12 @0210213443: 5 steps
lem-sym12-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1043 ∷ []) ⟫ʷ
lem-sym12-at0210213443 c4 = derive (Bx2-0143 ∷ []) (Bx2-1043 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q91 c4) ∷
   rw 1 (q217 c4) ∷
   rw 0 (q218 c4) ∷
   rw 1 (q24 c4) ∷ []) Eq.refl

private
  q219 : Ws → Eqn
  q219 c4 = eqn (X1 ∷ Sw34 ∷ []) (Sw34 ∷ X1 ∷ []) (c₂ (X ↑) (Swap ↑))
  q220 : Ws → Eqn
  q220 c4 = eqn (X1 ∷ Bx0-1234 ∷ X1 ∷ []) (CCZ234 ∷ Bx0-1234 ∷ []) (lem-X1-beta c4)
  q221 : Ws → Eqn
  q221 c4 = eqn (CCZ234 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ234 ∷ []) (wl0155 (lit c4))
  q222 : Ws → Eqn
  q222 c4 = eqn (Sw34 ∷ Bx0-1234 ∷ []) (Bx0-1243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1234⟩ (lit c4))

-- X1-beta @3443: 8 steps
lem-X1-beta-at3443 : Ws → ⟪ (X1 ∷ Bx0-1243 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1243 ∷ []) ⟫ʷ
lem-X1-beta-at3443 c4 = derive (X1 ∷ Bx0-1243 ∷ X1 ∷ []) (CCZ234 ∷ Bx0-1243 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw⁻ 1 (q219 c4) ∷
   rw 2 (q86 c4) ∷
   rw⁻ 3 (q219 c4) ∷
   rw 1 (q220 c4) ∷
   rw⁻ 0 (q221 c4) ∷
   rw 1 (q222 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q223 : Ws → Eqn
  q223 c4 = eqn (Sw01 ∷ X0 ∷ []) (X1 ∷ Sw01 ∷ []) (wl0370 (lit c4))
  q224 : Ws → Eqn
  q224 c4 = eqn (X1 ∷ Bx0-1243 ∷ X1 ∷ []) (CCZ234 ∷ Bx0-1243 ∷ []) (lem-X1-beta-at3443 c4)
  q225 : Ws → Eqn
  q225 c4 = eqn (Sw01 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ))
  q226 : Ws → Eqn
  q226 c4 = eqn (Sw01 ∷ Bx0-1243 ∷ []) (Bx1-0243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1243⟩ (lit c4))

-- X1-beta @01103443: 8 steps
lem-X1-beta-at01103443 : Ws → ⟪ (X0 ∷ Bx1-0243 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx1-0243 ∷ []) ⟫ʷ
lem-X1-beta-at01103443 c4 = derive (X0 ∷ Bx1-0243 ∷ X0 ∷ []) (CCZ234 ∷ Bx1-0243 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q223 c4) ∷
   rw 2 (q89 c4) ∷
   rw 3 (q223 c4) ∷
   rw 1 (q224 c4) ∷
   rw 0 (q225 c4) ∷
   rw 1 (q226 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q227 : Ws → Eqn
  q227 c4 = eqn (X0 ∷ Sw12 ∷ []) (Sw12 ∷ X0 ∷ []) (c₁ (X) (Swap))
  q228 : Ws → Eqn
  q228 c4 = eqn (X0 ∷ Bx1-0243 ∷ X0 ∷ []) (CCZ234 ∷ Bx1-0243 ∷ []) (lem-X1-beta-at01103443 c4)
  q229 : Ws → Eqn
  q229 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 (lit c4))
  q230 : Ws → Eqn
  q230 c4 = eqn (Sw12 ∷ Bx1-0243 ∷ []) (Bx2-0143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0243⟩ (lit c4))

-- X1-beta @0210213443: 8 steps
lem-X1-beta-at0210213443 : Ws → ⟪ (X0 ∷ Bx2-0143 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx2-0143 ∷ []) ⟫ʷ
lem-X1-beta-at0210213443 c4 = derive (X0 ∷ Bx2-0143 ∷ X0 ∷ []) (CCZ134 ∷ Bx2-0143 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw⁻ 1 (q227 c4) ∷
   rw 2 (q91 c4) ∷
   rw⁻ 3 (q227 c4) ∷
   rw 1 (q228 c4) ∷
   rw⁻ 0 (q229 c4) ∷
   rw 1 (q230 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q231 : Ws → Eqn
  q231 c4 = eqn (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) (wl0371 (lit c4))
  q232 : Ws → Eqn
  q232 c4 = eqn (Sw01 ∷ Bx2-1043 ∷ []) (Bx2-0143 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1043⟩ (lit c4))
  q233 : Ws → Eqn
  q233 c4 = eqn (X0 ∷ Bx2-0143 ∷ X0 ∷ []) (CCZ134 ∷ Bx2-0143 ∷ []) (lem-X1-beta-at0210213443 c4)
  q234 : Ws → Eqn
  q234 c4 = eqn (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4))
  q235 : Ws → Eqn
  q235 c4 = eqn (Sw01 ∷ Bx2-0143 ∷ []) (Bx2-1043 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0143⟩ (lit c4))

-- X1-beta @02203443: 8 steps
lem-X1-beta-at02203443 : Ws → ⟪ (X1 ∷ Bx2-1043 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx2-1043 ∷ []) ⟫ʷ
lem-X1-beta-at02203443 c4 = derive (X1 ∷ Bx2-1043 ∷ X1 ∷ []) (CCZ034 ∷ Bx2-1043 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q231 c4) ∷
   rw 2 (q232 c4) ∷
   rw 3 (q231 c4) ∷
   rw 1 (q233 c4) ∷
   rw 0 (q234 c4) ∷
   rw 1 (q235 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q236 : Ws → Eqn
  q236 c4 = eqn (Bx2-0143 ∷ []) (Bx2-1043 ∷ []) (lem-sym12-at0210213443 c4)

-- sym12 @02203443: 5 steps
lem-sym12-at02203443 : Ws → ⟪ (Bx2-1043 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-sym12-at02203443 c4 = derive (Bx2-1043 ∷ []) (Bx2-0143 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q232 c4) ∷
   rw 1 (q236 c4) ∷
   rw 0 (q232 c4) ∷
   rw 1 (q9 c4) ∷ []) Eq.refl

private
  q237 : Ws → Eqn
  q237 c4 = eqn (Sw23 ∷ Bx0-1324 ∷ []) (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4))
  q238 : Ws → Eqn
  q238 c4 = eqn (Sw23 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4))
  q239 : Ws → Eqn
  q239 c4 = eqn (Bx0-1234 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-23-4 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩ c4)
  q240 : Ws → Eqn
  q240 c4 = eqn (Sw23 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4))
  q241 : Ws → Eqn
  q241 c4 = eqn (Sw23 ∷ Bx0-1234 ∷ []) (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4))

-- auto BOX(0;1234) | SBOX(0;1;23;4) @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at2332 : Ws → ⟪ (Bx0-1324 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at2332 c4 = derive (Bx0-1324 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-32-4 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q237 c4) ∷
   rw 2 (q238 c4) ∷
   rw 1 (q239 c4) ∷
   rw 0 (q240 c4) ∷
   rw 1 (q241 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q242 : Ws → Eqn
  q242 c4 = eqn (Sw34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4))
  q243 : Ws → Eqn
  q243 c4 = eqn (Bx0-1324 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-32-4 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at2332 c4)
  q244 : Ws → Eqn
  q244 c4 = eqn (Sw34 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4))
  q245 : Ws → Eqn
  q245 c4 = eqn (Sw34 ∷ Bx0-1324 ∷ []) (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4))

-- auto BOX(0;1234) | SBOX(0;1;23;4) @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at243243 : Ws → ⟪ (Bx0-1423 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at243243 c4 = derive (Bx0-1423 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q156 c4) ∷
   rw 2 (q242 c4) ∷
   rw 1 (q243 c4) ∷
   rw 0 (q244 c4) ∷
   rw 1 (q245 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q246 : Ws → Eqn
  q246 c4 = eqn (Bx0-1423 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at243243 c4)

-- auto BOX(0;1234) | SBOX(0;1;23;4) @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0110243243 c4 = derive (Bx1-0423 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q159 c4) ∷
   rw 2 (q101 c4) ∷
   rw 1 (q246 c4) ∷
   rw 0 (q103 c4) ∷
   rw 1 (q188 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q247 : Ws → Eqn
  q247 c4 = eqn (Bx1-0423 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0110243243 c4)

-- auto BOX(0;1234) | SBOX(0;1;23;4) @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 c4 = derive (Bx2-0413 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q162 c4) ∷
   rw 2 (q106 c4) ∷
   rw 1 (q247 c4) ∷
   rw 0 (q61 c4) ∷
   rw 1 (q190 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q248 : Ws → Eqn
  q248 c4 = eqn (Sw23 ∷ CCZ134 ∷ []) (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4))
  q249 : Ws → Eqn
  q249 c4 = eqn (Sb0-1-23-4 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124 c4)
  q250 : Ws → Eqn
  q250 c4 = eqn (Sw23 ∷ CCZ124 ∷ []) (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4))

-- auto SBOX(0;1;23;4) | CCZ124 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at2332 c4 = derive (Sb0-1-32-4 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q238 c4) ∷
   rw 2 (q248 c4) ∷
   rw 1 (q249 c4) ∷
   rw 0 (q250 c4) ∷
   rw 1 (q240 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q251 : Ws → Eqn
  q251 c4 = eqn (CCZ134 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ134 ∷ []) (wl0154 (lit c4))
  q252 : Ws → Eqn
  q252 c4 = eqn (Sb0-1-32-4 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at2332 c4)

-- auto SBOX(0;1;23;4) | CCZ124 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at243243 c4 = derive (Sb0-1-42-3 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q242 c4) ∷
   rw⁻ 2 (q251 c4) ∷
   rw 1 (q252 c4) ∷
   rw⁻ 0 (q251 c4) ∷
   rw 1 (q244 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q253 : Ws → Eqn
  q253 c4 = eqn (Sb0-1-42-3 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at243243 c4)

-- auto SBOX(0;1;23;4) | CCZ124 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0110243243 c4 = derive (Sb1-0-42-3 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q101 c4) ∷
   rw 2 (q13 c4) ∷
   rw 1 (q253 c4) ∷
   rw 0 (q234 c4) ∷
   rw 1 (q103 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q254 : Ws → Eqn
  q254 c4 = eqn (Sw12 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4))
  q255 : Ws → Eqn
  q255 c4 = eqn (Sb1-0-42-3 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0110243243 c4)

-- auto SBOX(0;1;23;4) | CCZ124 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0210243143 c4 = derive (Sb2-0-41-3 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q106 c4) ∷
   rw 2 (q254 c4) ∷
   rw 1 (q255 c4) ∷
   rw 0 (q254 c4) ∷
   rw 1 (q61 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q256 : Ws → Eqn
  q256 c4 = eqn (CS01⁻ ∷ []) (Sb⁻2-0-41-3 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ []) (lem-F5d-CS01 c4)
  q257 : Ws → Eqn
  q257 c4 = eqn (Sw12 ∷ Sb⁻2-0-41-3 ∷ []) (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ (lit c4))

-- F5d CS01 @1221: 8 steps
lem-F5d-CS01-at1221 : Ws → ⟪ (CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-42-3 ∷ X4 ∷ Sb⁻1-0-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F5d-CS01-at1221 c4 = derive (CS02⁻ ∷ []) (Sb⁻1-0-42-3 ∷ X4 ∷ Sb⁻1-0-42-3 ∷ X4 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q29 c4) ∷
   rw 1 (q256 c4) ∷
   rw 0 (q257 c4) ∷
   rw 1 (q60 c4) ∷
   rw 2 (q257 c4) ∷
   rw 3 (q60 c4) ∷
   rw 4 (q24 c4) ∷ []) Eq.refl

private
  q258 : Ws → Eqn
  q258 c4 = eqn (Sw23 ∷ CS03⁻ ∷ []) (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 (lit c4))
  q259 : Ws → Eqn
  q259 c4 = eqn (CS02⁻ ∷ []) (Sb⁻1-0-42-3 ∷ X4 ∷ Sb⁻1-0-42-3 ∷ X4 ∷ []) (lem-F5d-CS01-at1221 c4)
  q260 : Ws → Eqn
  q260 c4 = eqn (Sw23 ∷ Sb⁻1-0-42-3 ∷ []) (Sb⁻1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·42·3⟩ (lit c4))

-- F5d CS01 @132132: 8 steps
lem-F5d-CS01-at132132 : Ws → ⟪ (CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-43-2 ∷ X4 ∷ Sb⁻1-0-43-2 ∷ X4 ∷ []) ⟫ʷ
lem-F5d-CS01-at132132 c4 = derive (CS03⁻ ∷ []) (Sb⁻1-0-43-2 ∷ X4 ∷ Sb⁻1-0-43-2 ∷ X4 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q258 c4) ∷
   rw 1 (q259 c4) ∷
   rw 0 (q260 c4) ∷
   rw 1 (q65 c4) ∷
   rw 2 (q260 c4) ∷
   rw 3 (q65 c4) ∷
   rw 4 (q64 c4) ∷ []) Eq.refl

private
  q261 : Ws → Eqn
  q261 c4 = eqn (Sw34 ∷ CS04⁻ ∷ []) (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 (lit c4))
  q262 : Ws → Eqn
  q262 c4 = eqn (CS03⁻ ∷ []) (Sb⁻1-0-43-2 ∷ X4 ∷ Sb⁻1-0-43-2 ∷ X4 ∷ []) (lem-F5d-CS01-at132132 c4)
  q263 : Ws → Eqn
  q263 c4 = eqn (Sw34 ∷ Sb⁻1-0-43-2 ∷ []) (Sb⁻1-0-34-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·43·2⟩ (lit c4))
  q264 : Ws → Eqn
  q264 c4 = eqn (Sw34 ∷ X4 ∷ []) (X3 ∷ Sw34 ∷ []) (wl0282 (lit c4))

-- F5d CS01 @14213243: 8 steps
lem-F5d-CS01-at14213243 : Ws → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-34-2 ∷ X3 ∷ Sb⁻1-0-34-2 ∷ X3 ∷ []) ⟫ʷ
lem-F5d-CS01-at14213243 c4 = derive (CS04⁻ ∷ []) (Sb⁻1-0-34-2 ∷ X3 ∷ Sb⁻1-0-34-2 ∷ X3 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q261 c4) ∷
   rw 1 (q262 c4) ∷
   rw 0 (q263 c4) ∷
   rw 1 (q264 c4) ∷
   rw 2 (q263 c4) ∷
   rw 3 (q264 c4) ∷
   rw 4 (q51 c4) ∷ []) Eq.refl

private
  q265 : Ws → Eqn
  q265 c4 = eqn (Sw23 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 (lit c4))
  q266 : Ws → Eqn
  q266 c4 = eqn (CS04⁻ ∷ []) (Sb⁻1-0-34-2 ∷ X3 ∷ Sb⁻1-0-34-2 ∷ X3 ∷ []) (lem-F5d-CS01-at14213243 c4)
  q267 : Ws → Eqn
  q267 c4 = eqn (Sw23 ∷ Sb⁻1-0-34-2 ∷ []) (Sb⁻1-0-24-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·34·2⟩ (lit c4))
  q268 : Ws → Eqn
  q268 c4 = eqn (Sw23 ∷ X3 ∷ []) (X2 ∷ Sw23 ∷ []) (wl0281 (lit c4))

-- F5d CS01 @142142: 8 steps
lem-F5d-CS01-at142142 : Ws → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-24-3 ∷ X2 ∷ Sb⁻1-0-24-3 ∷ X2 ∷ []) ⟫ʷ
lem-F5d-CS01-at142142 c4 = derive (CS04⁻ ∷ []) (Sb⁻1-0-24-3 ∷ X2 ∷ Sb⁻1-0-24-3 ∷ X2 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q265 c4) ∷
   rw 1 (q266 c4) ∷
   rw 0 (q267 c4) ∷
   rw 1 (q268 c4) ∷
   rw 2 (q267 c4) ∷
   rw 3 (q268 c4) ∷
   rw 4 (q64 c4) ∷ []) Eq.refl

private
  q269 : Ws → Eqn
  q269 c4 = eqn (Sw12 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd04 (lit c4))
  q270 : Ws → Eqn
  q270 c4 = eqn (CS04⁻ ∷ []) (Sb⁻1-0-24-3 ∷ X2 ∷ Sb⁻1-0-24-3 ∷ X2 ∷ []) (lem-F5d-CS01-at142142 c4)
  q271 : Ws → Eqn
  q271 c4 = eqn (Sw12 ∷ Sb⁻1-0-24-3 ∷ []) (Sb⁻2-0-14-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·24·3⟩ (lit c4))
  q272 : Ws → Eqn
  q272 c4 = eqn (Sw12 ∷ X2 ∷ []) (X1 ∷ Sw12 ∷ []) (wl0280 (lit c4))

-- F5d CS01 @1441: 8 steps
lem-F5d-CS01-at1441 : Ws → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-14-3 ∷ X1 ∷ Sb⁻2-0-14-3 ∷ X1 ∷ []) ⟫ʷ
lem-F5d-CS01-at1441 c4 = derive (CS04⁻ ∷ []) (Sb⁻2-0-14-3 ∷ X1 ∷ Sb⁻2-0-14-3 ∷ X1 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q269 c4) ∷
   rw 1 (q270 c4) ∷
   rw 0 (q271 c4) ∷
   rw 1 (q272 c4) ∷
   rw 2 (q271 c4) ∷
   rw 3 (q272 c4) ∷
   rw 4 (q24 c4) ∷ []) Eq.refl

private
  q273 : Ws → Eqn
  q273 c4 = eqn (Sw12 ∷ Sb⁻1-0-42-3 ∷ []) (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ (lit c4))
  q274 : Ws → Eqn
  q274 c4 = eqn (Sb⁻2-0-41-3 ∷ []) (Sb⁻2-0-14-3 ∷ []) (lem-SBsymd c4)
  q275 : Ws → Eqn
  q275 c4 = eqn (Sw12 ∷ Sb⁻2-0-14-3 ∷ []) (Sb⁻1-0-24-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·14·3⟩ (lit c4))

-- SBsymd @1221: 5 steps
lem-SBsymd-at1221 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-24-3 ∷ []) ⟫ʷ
lem-SBsymd-at1221 c4 = derive (Sb⁻1-0-42-3 ∷ []) (Sb⁻1-0-24-3 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q273 c4) ∷
   rw 1 (q274 c4) ∷
   rw 0 (q275 c4) ∷
   rw 1 (q24 c4) ∷ []) Eq.refl

private
  q276 : Ws → Eqn
  q276 c4 = eqn (Sw23 ∷ Sb⁻1-0-43-2 ∷ []) (Sb⁻1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·43·2⟩ (lit c4))
  q277 : Ws → Eqn
  q277 c4 = eqn (Sb⁻1-0-42-3 ∷ []) (Sb⁻1-0-24-3 ∷ []) (lem-SBsymd-at1221 c4)
  q278 : Ws → Eqn
  q278 c4 = eqn (Sw23 ∷ Sb⁻1-0-24-3 ∷ []) (Sb⁻1-0-34-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·24·3⟩ (lit c4))

-- SBsymd @132132: 5 steps
lem-SBsymd-at132132 : Ws → ⟪ (Sb⁻1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-34-2 ∷ []) ⟫ʷ
lem-SBsymd-at132132 c4 = derive (Sb⁻1-0-43-2 ∷ []) (Sb⁻1-0-34-2 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q276 c4) ∷
   rw 1 (q277 c4) ∷
   rw 0 (q278 c4) ∷
   rw 1 (q64 c4) ∷ []) Eq.refl

private
  q279 : Ws → Eqn
  q279 c4 = eqn (Sw34 ∷ Sb⁻1-0-34-2 ∷ []) (Sb⁻1-0-43-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·34·2⟩ (lit c4))
  q280 : Ws → Eqn
  q280 c4 = eqn (Sb⁻1-0-43-2 ∷ []) (Sb⁻1-0-34-2 ∷ []) (lem-SBsymd-at132132 c4)

-- SBsymd @14213243: 5 steps
lem-SBsymd-at14213243 : Ws → ⟪ (Sb⁻1-0-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-43-2 ∷ []) ⟫ʷ
lem-SBsymd-at14213243 c4 = derive (Sb⁻1-0-34-2 ∷ []) (Sb⁻1-0-43-2 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q279 c4) ∷
   rw 1 (q280 c4) ∷
   rw 0 (q279 c4) ∷
   rw 1 (q51 c4) ∷ []) Eq.refl

private
  q281 : Ws → Eqn
  q281 c4 = eqn (Sb⁻1-0-34-2 ∷ []) (Sb⁻1-0-43-2 ∷ []) (lem-SBsymd-at14213243 c4)

-- SBsymd @142142: 5 steps
lem-SBsymd-at142142 : Ws → ⟪ (Sb⁻1-0-24-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-SBsymd-at142142 c4 = derive (Sb⁻1-0-24-3 ∷ []) (Sb⁻1-0-42-3 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q278 c4) ∷
   rw 1 (q281 c4) ∷
   rw 0 (q276 c4) ∷
   rw 1 (q64 c4) ∷ []) Eq.refl

private
  q282 : Ws → Eqn
  q282 c4 = eqn (Sb⁻1-0-24-3 ∷ []) (Sb⁻1-0-42-3 ∷ []) (lem-SBsymd-at142142 c4)

-- SBsymd @1441: 5 steps
lem-SBsymd-at1441 : Ws → ⟪ (Sb⁻2-0-14-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-SBsymd-at1441 c4 = derive (Sb⁻2-0-14-3 ∷ []) (Sb⁻2-0-41-3 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q275 c4) ∷
   rw 1 (q282 c4) ∷
   rw 0 (q273 c4) ∷
   rw 1 (q24 c4) ∷ []) Eq.refl

private
  q283 : Ws → Eqn
  q283 c4 = eqn (Sw23 ∷ Sb⁻0-1-32-4 ∷ []) (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4))
  q284 : Ws → Eqn
  q284 c4 = eqn (Sw23 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ (lit c4))
  q285 : Ws → Eqn
  q285 c4 = eqn (Sb⁻0-1-23-4 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-3 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩ c4)
  q286 : Ws → Eqn
  q286 c4 = eqn (Sw23 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ (lit c4))
  q287 : Ws → Eqn
  q287 c4 = eqn (Sw23 ∷ Sb⁻0-1-23-4 ∷ []) (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | SBOX(0;1;4;3) @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-2 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-4-2 ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q283 c4) ∷
   rw 2 (q284 c4) ∷
   rw 1 (q285 c4) ∷
   rw 0 (q286 c4) ∷
   rw 1 (q287 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q288 : Ws → Eqn
  q288 c4 = eqn (Sw34 ∷ Sb⁻0-1-42-3 ∷ []) (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ (lit c4))
  q289 : Ws → Eqn
  q289 c4 = eqn (Sw34 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ (lit c4))
  q290 : Ws → Eqn
  q290 c4 = eqn (Sb⁻0-1-32-4 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-4-2 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at2332 c4)
  q291 : Ws → Eqn
  q291 c4 = eqn (Sw34 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ (lit c4))
  q292 : Ws → Eqn
  q292 c4 = eqn (Sw34 ∷ Sb⁻0-1-32-4 ∷ []) (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | SBOX(0;1;4;3) @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at243243 : Ws → ⟪ (Sb⁻0-1-42-3 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at243243 c4 = derive (Sb⁻0-1-42-3 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-3-2 ∷ Sb⁻0-1-42-3 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q288 c4) ∷
   rw 2 (q289 c4) ∷
   rw 1 (q290 c4) ∷
   rw 0 (q291 c4) ∷
   rw 1 (q292 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q293 : Ws → Eqn
  q293 c4 = eqn (Sw01 ∷ Sb⁻1-0-42-3 ∷ []) (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ (lit c4))
  q294 : Ws → Eqn
  q294 c4 = eqn (Sb⁻0-1-42-3 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-3-2 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at243243 c4)
  q295 : Ws → Eqn
  q295 c4 = eqn (Sw01 ∷ Sb⁻0-1-42-3 ∷ []) (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | SBOX(0;1;4;3) @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0110243243 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-2 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0110243243 c4 = derive (Sb⁻1-0-42-3 ∷ Sb1-0-3-2 ∷ []) (Sb1-0-3-2 ∷ Sb⁻1-0-42-3 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q293 c4) ∷
   rw 2 (q209 c4) ∷
   rw 1 (q294 c4) ∷
   rw 0 (q211 c4) ∷
   rw 1 (q295 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q296 : Ws → Eqn
  q296 c4 = eqn (Sb⁻1-0-42-3 ∷ Sb1-0-3-2 ∷ []) (Sb1-0-3-2 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0110243243 c4)

-- auto SBOXd(0;1;23;4) | SBOX(0;1;4;3) @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 : Ws → ⟪ (Sb⁻2-0-41-3 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 c4 = derive (Sb⁻2-0-41-3 ∷ Sb2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q257 c4) ∷
   rw 2 (q212 c4) ∷
   rw 1 (q296 c4) ∷
   rw 0 (q214 c4) ∷
   rw 1 (q273 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q297 : Ws → Eqn
  q297 c4 = eqn (Sw23 ∷ K4 ∷ []) (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K))
  q298 : Ws → Eqn
  q298 c4 = eqn (Sb⁻0-1-23-4 ∷ K4 ∷ []) (K4 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4 c4)

-- auto SBOXd(0;1;23;4) | K4 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ K4 ∷ []) (K4 ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q283 c4) ∷
   rw 2 (q297 c4) ∷
   rw 1 (q298 c4) ∷
   rw 0 (q297 c4) ∷
   rw 1 (q287 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q299 : Ws → Eqn
  q299 c4 = eqn (K4 ∷ Sw34 ∷ []) (Sw34 ∷ K3 ∷ []) (wl0067 (lit c4))
  q300 : Ws → Eqn
  q300 c4 = eqn (Sb⁻0-1-32-4 ∷ K4 ∷ []) (K4 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at2332 c4)
  q301 : Ws → Eqn
  q301 c4 = eqn (K3 ∷ Sw34 ∷ []) (Sw34 ∷ K4 ∷ []) (wl0068 (lit c4))

-- auto SBOXd(0;1;23;4) | K4 @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at243243 : Ws → ⟪ (Sb⁻0-1-42-3 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at243243 c4 = derive (Sb⁻0-1-42-3 ∷ K3 ∷ []) (K3 ∷ Sb⁻0-1-42-3 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q288 c4) ∷
   rw⁻ 2 (q299 c4) ∷
   rw 1 (q300 c4) ∷
   rw⁻ 0 (q301 c4) ∷
   rw 1 (q292 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q302 : Ws → Eqn
  q302 c4 = eqn (Sb⁻0-1-42-3 ∷ K3 ∷ []) (K3 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at243243 c4)

-- auto SBOXd(0;1;23;4) | K4 @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0110243243 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0110243243 c4 = derive (Sb⁻1-0-42-3 ∷ K3 ∷ []) (K3 ∷ Sb⁻1-0-42-3 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q293 c4) ∷
   rw 2 (q202 c4) ∷
   rw 1 (q302 c4) ∷
   rw 0 (q202 c4) ∷
   rw 1 (q295 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q303 : Ws → Eqn
  q303 c4 = eqn (Sb⁻1-0-42-3 ∷ K3 ∷ []) (K3 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0110243243 c4)

-- auto SBOXd(0;1;23;4) | K4 @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0210243143 : Ws → ⟪ (Sb⁻2-0-41-3 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0210243143 c4 = derive (Sb⁻2-0-41-3 ∷ K3 ∷ []) (K3 ∷ Sb⁻2-0-41-3 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q257 c4) ∷
   rw 2 (q204 c4) ∷
   rw 1 (q303 c4) ∷
   rw 0 (q204 c4) ∷
   rw 1 (q273 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q304 : Ws → Eqn
  q304 c4 = eqn (Sb⁻0-1-23-4 ∷ CS24 ∷ []) (CS24 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24 c4)

-- auto SBOXd(0;1;23;4) | CS24 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ CS34 ∷ []) (CS34 ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q283 c4) ∷
   rw⁻ 2 (q149 c4) ∷
   rw 1 (q304 c4) ∷
   rw⁻ 0 (q151 c4) ∷
   rw 1 (q287 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q305 : Ws → Eqn
  q305 c4 = eqn (CS34 ∷ Sw34 ∷ []) (Sw34 ∷ CS34 ∷ []) (wl0039 (lit c4))
  q306 : Ws → Eqn
  q306 c4 = eqn (Sb⁻0-1-32-4 ∷ CS34 ∷ []) (CS34 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at2332 c4)

-- auto SBOXd(0;1;23;4) | CS24 @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at243243 : Ws → ⟪ (Sb⁻0-1-42-3 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at243243 c4 = derive (Sb⁻0-1-42-3 ∷ CS34 ∷ []) (CS34 ∷ Sb⁻0-1-42-3 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q288 c4) ∷
   rw⁻ 2 (q305 c4) ∷
   rw 1 (q306 c4) ∷
   rw⁻ 0 (q305 c4) ∷
   rw 1 (q292 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q307 : Ws → Eqn
  q307 c4 = eqn (Sb⁻0-1-42-3 ∷ CS34 ∷ []) (CS34 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at243243 c4)

-- auto SBOXd(0;1;23;4) | CS24 @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at0110243243 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at0110243243 c4 = derive (Sb⁻1-0-42-3 ∷ CS34 ∷ []) (CS34 ∷ Sb⁻1-0-42-3 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q293 c4) ∷
   rw 2 (q152 c4) ∷
   rw 1 (q307 c4) ∷
   rw 0 (q152 c4) ∷
   rw 1 (q295 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q308 : Ws → Eqn
  q308 c4 = eqn (Sb⁻1-0-42-3 ∷ CS34 ∷ []) (CS34 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at0110243243 c4)

-- auto SBOXd(0;1;23;4) | CS24 @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at0210243143 : Ws → ⟪ (Sb⁻2-0-41-3 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at0210243143 c4 = derive (Sb⁻2-0-41-3 ∷ CS34 ∷ []) (CS34 ∷ Sb⁻2-0-41-3 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q257 c4) ∷
   rw 2 (q154 c4) ∷
   rw 1 (q308 c4) ∷
   rw 0 (q154 c4) ∷
   rw 1 (q273 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q309 : Ws → Eqn
  q309 c4 = eqn (Sw23 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K • iI))
  q310 : Ws → Eqn
  q310 c4 = eqn (Sb⁻0-1-23-4 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4 c4)

-- auto SBOXd(0;1;23;4) | Kd4 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q283 c4) ∷
   rw 2 (q309 c4) ∷
   rw 1 (q310 c4) ∷
   rw 0 (q309 c4) ∷
   rw 1 (q287 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q311 : Ws → Eqn
  q311 c4 = eqn (K4⁻ ∷ Sw34 ∷ []) (Sw34 ∷ K3⁻ ∷ []) (wl0312 (lit c4))
  q312 : Ws → Eqn
  q312 c4 = eqn (Sb⁻0-1-32-4 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at2332 c4)
  q313 : Ws → Eqn
  q313 c4 = eqn (K3⁻ ∷ Sw34 ∷ []) (Sw34 ∷ K4⁻ ∷ []) (wl0311 (lit c4))

-- auto SBOXd(0;1;23;4) | Kd4 @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at243243 : Ws → ⟪ (Sb⁻0-1-42-3 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at243243 c4 = derive (Sb⁻0-1-42-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb⁻0-1-42-3 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q288 c4) ∷
   rw⁻ 2 (q311 c4) ∷
   rw 1 (q312 c4) ∷
   rw⁻ 0 (q313 c4) ∷
   rw 1 (q292 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q314 : Ws → Eqn
  q314 c4 = eqn (Sb⁻0-1-42-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at243243 c4)

-- auto SBOXd(0;1;23;4) | Kd4 @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at0110243243 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at0110243243 c4 = derive (Sb⁻1-0-42-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb⁻1-0-42-3 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q293 c4) ∷
   rw 2 (q126 c4) ∷
   rw 1 (q314 c4) ∷
   rw 0 (q126 c4) ∷
   rw 1 (q295 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q315 : Ws → Eqn
  q315 c4 = eqn (Sb⁻1-0-42-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at0110243243 c4)

-- auto SBOXd(0;1;23;4) | Kd4 @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at0210243143 : Ws → ⟪ (Sb⁻2-0-41-3 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at0210243143 c4 = derive (Sb⁻2-0-41-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb⁻2-0-41-3 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q257 c4) ∷
   rw 2 (q128 c4) ∷
   rw 1 (q315 c4) ∷
   rw 0 (q128 c4) ∷
   rw 1 (q273 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q316 : Ws → Eqn
  q316 c4 = eqn (Sw23 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ (lit c4))
  q317 : Ws → Eqn
  q317 c4 = eqn (Sb⁻0-1-23-4 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-3 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩ c4)
  q318 : Ws → Eqn
  q318 c4 = eqn (Sw23 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | SBOXd(0;1;4;3) @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-2 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-4-2 ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q283 c4) ∷
   rw 2 (q316 c4) ∷
   rw 1 (q317 c4) ∷
   rw 0 (q318 c4) ∷
   rw 1 (q287 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q319 : Ws → Eqn
  q319 c4 = eqn (Sw34 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ (lit c4))
  q320 : Ws → Eqn
  q320 c4 = eqn (Sb⁻0-1-32-4 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-4-2 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at2332 c4)
  q321 : Ws → Eqn
  q321 c4 = eqn (Sw34 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ (lit c4))

-- auto SBOXd(0;1;23;4) | SBOXd(0;1;4;3) @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at243243 : Ws → ⟪ (Sb⁻0-1-42-3 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at243243 c4 = derive (Sb⁻0-1-42-3 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sb⁻0-1-42-3 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q288 c4) ∷
   rw 2 (q319 c4) ∷
   rw 1 (q320 c4) ∷
   rw 0 (q321 c4) ∷
   rw 1 (q292 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q322 : Ws → Eqn
  q322 c4 = eqn (Sb⁻0-1-42-3 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at243243 c4)

-- auto SBOXd(0;1;23;4) | SBOXd(0;1;4;3) @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0110243243 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-2 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0110243243 c4 = derive (Sb⁻1-0-42-3 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻1-0-3-2 ∷ Sb⁻1-0-42-3 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q293 c4) ∷
   rw 2 (q100 c4) ∷
   rw 1 (q322 c4) ∷
   rw 0 (q104 c4) ∷
   rw 1 (q295 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q323 : Ws → Eqn
  q323 c4 = eqn (Sb⁻1-0-42-3 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻1-0-3-2 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0110243243 c4)

-- auto SBOXd(0;1;23;4) | SBOXd(0;1;4;3) @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0210243143 : Ws → ⟪ (Sb⁻2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0210243143 c4 = derive (Sb⁻2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q257 c4) ∷
   rw 2 (q105 c4) ∷
   rw 1 (q323 c4) ∷
   rw 0 (q108 c4) ∷
   rw 1 (q273 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q324 : Ws → Eqn
  q324 c4 = eqn (Sw23 ∷ Toff013 ∷ []) (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 (lit c4))
  q325 : Ws → Eqn
  q325 c4 = eqn (Sb⁻0-1-23-4 ∷ Toff012 ∷ []) (Toff012 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012 c4)

-- auto SBOXd(0;1;23;4) | TOFF012 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at2332 c4 = derive (Sb⁻0-1-32-4 ∷ Toff013 ∷ []) (Toff013 ∷ Sb⁻0-1-32-4 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q283 c4) ∷
   rw 2 (q324 c4) ∷
   rw 1 (q325 c4) ∷
   rw 0 (q174 c4) ∷
   rw 1 (q287 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q326 : Ws → Eqn
  q326 c4 = eqn (Sw34 ∷ Toff014 ∷ []) (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 (lit c4))
  q327 : Ws → Eqn
  q327 c4 = eqn (Sb⁻0-1-32-4 ∷ Toff013 ∷ []) (Toff013 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at2332 c4)
  q328 : Ws → Eqn
  q328 c4 = eqn (Sw34 ∷ Toff013 ∷ []) (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 (lit c4))

-- auto SBOXd(0;1;23;4) | TOFF012 @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at243243 : Ws → ⟪ (Sb⁻0-1-42-3 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at243243 c4 = derive (Sb⁻0-1-42-3 ∷ Toff014 ∷ []) (Toff014 ∷ Sb⁻0-1-42-3 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q288 c4) ∷
   rw 2 (q326 c4) ∷
   rw 1 (q327 c4) ∷
   rw 0 (q328 c4) ∷
   rw 1 (q292 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q329 : Ws → Eqn
  q329 c4 = eqn (Sw01 ∷ Toff104 ∷ []) (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 (lit c4))
  q330 : Ws → Eqn
  q330 c4 = eqn (Sb⁻0-1-42-3 ∷ Toff014 ∷ []) (Toff014 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at243243 c4)
  q331 : Ws → Eqn
  q331 c4 = eqn (Sw01 ∷ Toff014 ∷ []) (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 (lit c4))

-- auto SBOXd(0;1;23;4) | TOFF012 @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0110243243 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0110243243 c4 = derive (Sb⁻1-0-42-3 ∷ Toff104 ∷ []) (Toff104 ∷ Sb⁻1-0-42-3 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q293 c4) ∷
   rw 2 (q329 c4) ∷
   rw 1 (q330 c4) ∷
   rw 0 (q331 c4) ∷
   rw 1 (q295 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q332 : Ws → Eqn
  q332 c4 = eqn (Sw12 ∷ Toff204 ∷ []) (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 (lit c4))
  q333 : Ws → Eqn
  q333 c4 = eqn (Sb⁻1-0-42-3 ∷ Toff104 ∷ []) (Toff104 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0110243243 c4)
  q334 : Ws → Eqn
  q334 c4 = eqn (Sw12 ∷ Toff104 ∷ []) (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 (lit c4))

-- auto SBOXd(0;1;23;4) | TOFF012 @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0210243143 : Ws → ⟪ (Sb⁻2-0-41-3 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0210243143 c4 = derive (Sb⁻2-0-41-3 ∷ Toff204 ∷ []) (Toff204 ∷ Sb⁻2-0-41-3 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q257 c4) ∷
   rw 2 (q332 c4) ∷
   rw 1 (q333 c4) ∷
   rw 0 (q334 c4) ∷
   rw 1 (q273 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q335 : Ws → Eqn
  q335 c4 = eqn (Sw23 ∷ Bx⁻0-1324 ∷ []) (Bx⁻0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1324⟩ (lit c4))
  q336 : Ws → Eqn
  q336 c4 = eqn (Bx⁻0-1234 ∷ CS04 ∷ []) (CS04 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS40 c4)
  q337 : Ws → Eqn
  q337 c4 = eqn (Sw23 ∷ Bx⁻0-1234 ∷ []) (Bx⁻0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1234⟩ (lit c4))

-- auto BOXd(0;1234) | CS40 @2332: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at2332 : Ws → ⟪ (Bx⁻0-1324 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx⁻0-1324 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at2332 c4 = derive (Bx⁻0-1324 ∷ CS04 ∷ []) (CS04 ∷ Bx⁻0-1324 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q335 c4) ∷
   rw 2 (q76 c4) ∷
   rw 1 (q336 c4) ∷
   rw 0 (q76 c4) ∷
   rw 1 (q337 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q338 : Ws → Eqn
  q338 c4 = eqn (Sw34 ∷ Bx⁻0-1423 ∷ []) (Bx⁻0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·1423⟩ (lit c4))
  q339 : Ws → Eqn
  q339 c4 = eqn (Bx⁻0-1324 ∷ CS04 ∷ []) (CS04 ∷ Bx⁻0-1324 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS40-at2332 c4)
  q340 : Ws → Eqn
  q340 c4 = eqn (Sw34 ∷ Bx⁻0-1324 ∷ []) (Bx⁻0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·1324⟩ (lit c4))

-- auto BOXd(0;1234) | CS40 @243243: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at243243 : Ws → ⟪ (Bx⁻0-1423 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Bx⁻0-1423 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at243243 c4 = derive (Bx⁻0-1423 ∷ CS03 ∷ []) (CS03 ∷ Bx⁻0-1423 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q338 c4) ∷
   rw 2 (q72 c4) ∷
   rw 1 (q339 c4) ∷
   rw 0 (q141 c4) ∷
   rw 1 (q340 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q341 : Ws → Eqn
  q341 c4 = eqn (Sw01 ∷ Bx⁻1-0423 ∷ []) (Bx⁻0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0423⟩ (lit c4))
  q342 : Ws → Eqn
  q342 c4 = eqn (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) (wl0019 (lit c4))
  q343 : Ws → Eqn
  q343 c4 = eqn (Bx⁻0-1423 ∷ CS03 ∷ []) (CS03 ∷ Bx⁻0-1423 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS40-at243243 c4)
  q344 : Ws → Eqn
  q344 c4 = eqn (CS13 ∷ Sw01 ∷ []) (Sw01 ∷ CS03 ∷ []) (wl0061 (lit c4))
  q345 : Ws → Eqn
  q345 c4 = eqn (Sw01 ∷ Bx⁻0-1423 ∷ []) (Bx⁻1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·1423⟩ (lit c4))

-- auto BOXd(0;1234) | CS40 @0110243243: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0110243243 : Ws → ⟪ (Bx⁻1-0423 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx⁻1-0423 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0110243243 c4 = derive (Bx⁻1-0423 ∷ CS13 ∷ []) (CS13 ∷ Bx⁻1-0423 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q341 c4) ∷
   rw⁻ 2 (q342 c4) ∷
   rw 1 (q343 c4) ∷
   rw⁻ 0 (q344 c4) ∷
   rw 1 (q345 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q346 : Ws → Eqn
  q346 c4 = eqn (Sw12 ∷ Bx⁻2-0413 ∷ []) (Bx⁻1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0413⟩ (lit c4))
  q347 : Ws → Eqn
  q347 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl0024 (lit c4))
  q348 : Ws → Eqn
  q348 c4 = eqn (Bx⁻1-0423 ∷ CS13 ∷ []) (CS13 ∷ Bx⁻1-0423 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0110243243 c4)
  q349 : Ws → Eqn
  q349 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl0025 (lit c4))
  q350 : Ws → Eqn
  q350 c4 = eqn (Sw12 ∷ Bx⁻1-0423 ∷ []) (Bx⁻2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·0423⟩ (lit c4))

-- auto BOXd(0;1234) | CS40 @0210243143: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0210243143 : Ws → ⟪ (Bx⁻2-0413 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Bx⁻2-0413 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0210243143 c4 = derive (Bx⁻2-0413 ∷ CS23 ∷ []) (CS23 ∷ Bx⁻2-0413 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q346 c4) ∷
   rw⁻ 2 (q347 c4) ∷
   rw 1 (q348 c4) ∷
   rw⁻ 0 (q349 c4) ∷
   rw 1 (q350 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q351 : Ws → Eqn
  q351 c4 = eqn (Sw01 ∷ Bx1-0324 ∷ []) (Bx0-1324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0324⟩ (lit c4))
  q352 : Ws → Eqn
  q352 c4 = eqn (Bx0-1324 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at2332 c4)

-- beta-T @01102332: 8 steps
lem-beta-T-at01102332 : Ws → ⟪ (Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CCZ124 ∷ Toff103 ∷ CCZ124 ∷ []) ⟫ʷ
lem-beta-T-at01102332 c4 = derive (Bx1-0324 ∷ []) (Toff103 ∷ CCZ124 ∷ Toff103 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q351 c4) ∷
   rw 1 (q352 c4) ∷
   rw 0 (q178 c4) ∷
   rw 1 (q179 c4) ∷
   rw 2 (q178 c4) ∷
   rw 3 (q179 c4) ∷
   rw 4 (q9 c4) ∷ []) Eq.refl

private
  q353 : Ws → Eqn
  q353 c4 = eqn (Sw12 ∷ Bx2-0314 ∷ []) (Bx1-0324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0314⟩ (lit c4))
  q354 : Ws → Eqn
  q354 c4 = eqn (Bx1-0324 ∷ []) (Toff103 ∷ CCZ124 ∷ Toff103 ∷ CCZ124 ∷ []) (lem-beta-T-at01102332 c4)

-- beta-T @02102331: 8 steps
lem-beta-T-at02102331 : Ws → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) ⟫ʷ
lem-beta-T-at02102331 c4 = derive (Bx2-0314 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q353 c4) ∷
   rw 1 (q354 c4) ∷
   rw 0 (q182 c4) ∷
   rw⁻ 1 (q183 c4) ∷
   rw 2 (q182 c4) ∷
   rw⁻ 3 (q183 c4) ∷
   rw 4 (q24 c4) ∷ []) Eq.refl

private
  q355 : Ws → Eqn
  q355 c4 = eqn (Sw01 ∷ Bx2-1304 ∷ []) (Bx2-0314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1304⟩ (lit c4))
  q356 : Ws → Eqn
  q356 c4 = eqn (Bx2-0314 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at02102331 c4)
  q357 : Ws → Eqn
  q357 c4 = eqn (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) (wl0104 (lit c4))
  q358 : Ws → Eqn
  q358 c4 = eqn (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4))

-- beta-T @022330: 8 steps
lem-beta-T-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) ⟫ʷ
lem-beta-T-at022330 c4 = derive (Bx2-1304 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q355 c4) ∷
   rw 1 (q356 c4) ∷
   rw 0 (q357 c4) ∷
   rw 1 (q358 c4) ∷
   rw 2 (q357 c4) ∷
   rw 3 (q358 c4) ∷
   rw 4 (q9 c4) ∷ []) Eq.refl

private
  q359 : Ws → Eqn
  q359 c4 = eqn (Sw01 ∷ Bx2-1034 ∷ []) (Bx2-0134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1034⟩ (lit c4))
  q360 : Ws → Eqn
  q360 c4 = eqn (Bx2-0134 ∷ []) (Bx2-0143 ∷ []) (lem-sym34-at021021 c4)

-- sym34 @0220: 5 steps
lem-sym34-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1043 ∷ []) ⟫ʷ
lem-sym34-at0220 c4 = derive (Bx2-1034 ∷ []) (Bx2-1043 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q359 c4) ∷
   rw 1 (q360 c4) ∷
   rw 0 (q235 c4) ∷
   rw 1 (q9 c4) ∷ []) Eq.refl

private
  q361 : Ws → Eqn
  q361 c4 = eqn (Bx⁻0-1234 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CSd40 c4)

-- auto BOXd(0;1234) | CSd40 @2332: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at2332 : Ws → ⟪ (Bx⁻0-1324 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Bx⁻0-1324 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at2332 c4 = derive (Bx⁻0-1324 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx⁻0-1324 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q335 c4) ∷
   rw 2 (q265 c4) ∷
   rw 1 (q361 c4) ∷
   rw 0 (q265 c4) ∷
   rw 1 (q337 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q362 : Ws → Eqn
  q362 c4 = eqn (Sw34 ∷ CS03⁻ ∷ []) (CS04⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd03 (lit c4))
  q363 : Ws → Eqn
  q363 c4 = eqn (Bx⁻0-1324 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx⁻0-1324 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at2332 c4)

-- auto BOXd(0;1234) | CSd40 @243243: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at243243 : Ws → ⟪ (Bx⁻0-1423 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx⁻0-1423 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at243243 c4 = derive (Bx⁻0-1423 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx⁻0-1423 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q338 c4) ∷
   rw 2 (q362 c4) ∷
   rw 1 (q363 c4) ∷
   rw 0 (q261 c4) ∷
   rw 1 (q340 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q364 : Ws → Eqn
  q364 c4 = eqn (CS03⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS13⁻ ∷ []) (wl0022 (lit c4))
  q365 : Ws → Eqn
  q365 c4 = eqn (Bx⁻0-1423 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx⁻0-1423 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at243243 c4)
  q366 : Ws → Eqn
  q366 c4 = eqn (CS13⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS03⁻ ∷ []) (wl0121 (lit c4))

-- auto BOXd(0;1234) | CSd40 @0110243243: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at0110243243 : Ws → ⟪ (Bx⁻1-0423 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Bx⁻1-0423 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at0110243243 c4 = derive (Bx⁻1-0423 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx⁻1-0423 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q341 c4) ∷
   rw⁻ 2 (q364 c4) ∷
   rw 1 (q365 c4) ∷
   rw⁻ 0 (q366 c4) ∷
   rw 1 (q345 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q367 : Ws → Eqn
  q367 c4 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wl0043 (lit c4))
  q368 : Ws → Eqn
  q368 c4 = eqn (Bx⁻1-0423 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx⁻1-0423 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at0110243243 c4)
  q369 : Ws → Eqn
  q369 c4 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wl0046 (lit c4))

-- auto BOXd(0;1234) | CSd40 @0210243143: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at0210243143 : Ws → ⟪ (Bx⁻2-0413 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Bx⁻2-0413 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at0210243143 c4 = derive (Bx⁻2-0413 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx⁻2-0413 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q346 c4) ∷
   rw⁻ 2 (q367 c4) ∷
   rw 1 (q368 c4) ∷
   rw⁻ 0 (q369 c4) ∷
   rw 1 (q350 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q370 : Ws → Eqn
  q370 c4 = eqn (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ []) (wl0037 (lit c4))
  q371 : Ws → Eqn
  q371 c4 = eqn (Sw12 ∷ Bx3-0241 ∷ []) (Bx3-0142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0241⟩ (lit c4))
  q372 : Ws → Eqn
  q372 c4 = eqn (CCZ012 ∷ Bx3-0142 ∷ []) (Bx3-0142 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0142⟩ c4)
  q373 : Ws → Eqn
  q373 c4 = eqn (Sw12 ∷ Bx3-0142 ∷ []) (Bx3-0241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0142⟩ (lit c4))

-- auto CCZ012 | BOX(3;0142) @1221: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at1221 : Ws → ⟪ (CCZ012 ∷ Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at1221 c4 = derive (CCZ012 ∷ Bx3-0241 ∷ []) (Bx3-0241 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw⁻ 1 (q370 c4) ∷
   rw 2 (q371 c4) ∷
   rw 1 (q372 c4) ∷
   rw 0 (q373 c4) ∷
   rw⁻ 1 (q370 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q374 : Ws → Eqn
  q374 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4))
  q375 : Ws → Eqn
  q375 c4 = eqn (Sw23 ∷ Bx2-0341 ∷ []) (Bx3-0241 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0341⟩ (lit c4))
  q376 : Ws → Eqn
  q376 c4 = eqn (CCZ012 ∷ Bx3-0241 ∷ []) (Bx3-0241 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at1221 c4)
  q377 : Ws → Eqn
  q377 c4 = eqn (Sw23 ∷ Bx3-0241 ∷ []) (Bx2-0341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0241⟩ (lit c4))
  q378 : Ws → Eqn
  q378 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4))

-- auto CCZ012 | BOX(3;0142) @132132: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at132132 : Ws → ⟪ (CCZ013 ∷ Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at132132 c4 = derive (CCZ013 ∷ Bx2-0341 ∷ []) (Bx2-0341 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q374 c4) ∷
   rw 2 (q375 c4) ∷
   rw 1 (q376 c4) ∷
   rw 0 (q377 c4) ∷
   rw 1 (q378 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q379 : Ws → Eqn
  q379 c4 = eqn (Sw34 ∷ CCZ014 ∷ []) (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 (lit c4))
  q380 : Ws → Eqn
  q380 c4 = eqn (Sw34 ∷ Bx2-0431 ∷ []) (Bx2-0341 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·0431⟩ (lit c4))
  q381 : Ws → Eqn
  q381 c4 = eqn (CCZ013 ∷ Bx2-0341 ∷ []) (Bx2-0341 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at132132 c4)
  q382 : Ws → Eqn
  q382 c4 = eqn (Sw34 ∷ Bx2-0341 ∷ []) (Bx2-0431 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·0341⟩ (lit c4))
  q383 : Ws → Eqn
  q383 c4 = eqn (Sw34 ∷ CCZ013 ∷ []) (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 (lit c4))

-- auto CCZ012 | BOX(3;0142) @14213243: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14213243 : Ws → ⟪ (CCZ014 ∷ Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14213243 c4 = derive (CCZ014 ∷ Bx2-0431 ∷ []) (Bx2-0431 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q379 c4) ∷
   rw 2 (q380 c4) ∷
   rw 1 (q381 c4) ∷
   rw 0 (q382 c4) ∷
   rw 1 (q383 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q384 : Ws → Eqn
  q384 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4))
  q385 : Ws → Eqn
  q385 c4 = eqn (CCZ014 ∷ Bx2-0431 ∷ []) (Bx2-0431 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14213243 c4)
  q386 : Ws → Eqn
  q386 c4 = eqn (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4))

-- auto CCZ012 | BOX(3;0142) @143143: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at143143 : Ws → ⟪ (CCZ024 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at143143 c4 = derive (CCZ024 ∷ Bx1-0432 ∷ []) (Bx1-0432 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q384 c4) ∷
   rw 2 (q164 c4) ∷
   rw 1 (q385 c4) ∷
   rw 0 (q170 c4) ∷
   rw 1 (q386 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q387 : Ws → Eqn
  q387 c4 = eqn (Sw23 ∷ Bx1-0423 ∷ []) (Bx1-0432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0423⟩ (lit c4))
  q388 : Ws → Eqn
  q388 c4 = eqn (CCZ024 ∷ Bx1-0432 ∷ []) (Bx1-0432 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at143143 c4)
  q389 : Ws → Eqn
  q389 c4 = eqn (Sw23 ∷ Bx1-0432 ∷ []) (Bx1-0423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0432⟩ (lit c4))
  q390 : Ws → Eqn
  q390 c4 = eqn (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 (lit c4))

-- auto CCZ012 | BOX(3;0142) @14233142: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14233142 : Ws → ⟪ (CCZ034 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14233142 c4 = derive (CCZ034 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q175 c4) ∷
   rw 2 (q387 c4) ∷
   rw 1 (q388 c4) ∷
   rw 0 (q389 c4) ∷
   rw 1 (q390 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q391 : Ws → Eqn
  q391 c4 = eqn (CCZ034 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14233142 c4)

-- auto CCZ012 | BOX(3;0142) @14233241: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14233241 : Ws → ⟪ (CCZ034 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14233241 c4 = derive (CCZ034 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q254 c4) ∷
   rw 2 (q162 c4) ∷
   rw 1 (q391 c4) ∷
   rw 0 (q190 c4) ∷
   rw 1 (q254 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q392 : Ws → Eqn
  q392 c4 = eqn (Sb0-1-23-4 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩ c4)

-- auto SBOX(0;1;23;4) | BOX(0;1234) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at2332 c4 = derive (Sb0-1-32-4 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q238 c4) ∷
   rw 2 (q237 c4) ∷
   rw 1 (q392 c4) ∷
   rw 0 (q241 c4) ∷
   rw 1 (q240 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q393 : Ws → Eqn
  q393 c4 = eqn (Sb0-1-32-4 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at2332 c4)

-- auto SBOX(0;1;23;4) | BOX(0;1234) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at243243 c4 = derive (Sb0-1-42-3 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q242 c4) ∷
   rw 2 (q156 c4) ∷
   rw 1 (q393 c4) ∷
   rw 0 (q245 c4) ∷
   rw 1 (q244 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q394 : Ws → Eqn
  q394 c4 = eqn (Sb0-1-42-3 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at243243 c4)

-- auto SBOX(0;1;23;4) | BOX(0;1234) @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0110243243 c4 = derive (Sb1-0-42-3 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q101 c4) ∷
   rw 2 (q159 c4) ∷
   rw 1 (q394 c4) ∷
   rw 0 (q188 c4) ∷
   rw 1 (q103 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q395 : Ws → Eqn
  q395 c4 = eqn (Sb1-0-42-3 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0110243243 c4)

-- auto SBOX(0;1;23;4) | BOX(0;1234) @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0210243143 c4 = derive (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q106 c4) ∷
   rw 2 (q162 c4) ∷
   rw 1 (q395 c4) ∷
   rw 0 (q190 c4) ∷
   rw 1 (q61 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q396 : Ws → Eqn
  q396 c4 = eqn (Sw12 ∷ Sb3-0-24-1 ∷ []) (Sb3-0-14-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·24·1⟩ (lit c4))
  q397 : Ws → Eqn
  q397 c4 = eqn (CCZ012 ∷ Sb3-0-14-2 ∷ []) (Sb3-0-14-2 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩ c4)
  q398 : Ws → Eqn
  q398 c4 = eqn (Sw12 ∷ Sb3-0-14-2 ∷ []) (Sb3-0-24-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·14·2⟩ (lit c4))

-- auto CCZ012 | SBOX(3;0;14;2) @1221: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at1221 : Ws → ⟪ (CCZ012 ∷ Sb3-0-24-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-24-1 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at1221 c4 = derive (CCZ012 ∷ Sb3-0-24-1 ∷ []) (Sb3-0-24-1 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw⁻ 1 (q370 c4) ∷
   rw 2 (q396 c4) ∷
   rw 1 (q397 c4) ∷
   rw 0 (q398 c4) ∷
   rw⁻ 1 (q370 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q399 : Ws → Eqn
  q399 c4 = eqn (Sw23 ∷ Sb2-0-34-1 ∷ []) (Sb3-0-24-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·34·1⟩ (lit c4))
  q400 : Ws → Eqn
  q400 c4 = eqn (CCZ012 ∷ Sb3-0-24-1 ∷ []) (Sb3-0-24-1 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at1221 c4)
  q401 : Ws → Eqn
  q401 c4 = eqn (Sw23 ∷ Sb3-0-24-1 ∷ []) (Sb2-0-34-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·24·1⟩ (lit c4))

-- auto CCZ012 | SBOX(3;0;14;2) @132132: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at132132 : Ws → ⟪ (CCZ013 ∷ Sb2-0-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-34-1 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at132132 c4 = derive (CCZ013 ∷ Sb2-0-34-1 ∷ []) (Sb2-0-34-1 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q374 c4) ∷
   rw 2 (q399 c4) ∷
   rw 1 (q400 c4) ∷
   rw 0 (q401 c4) ∷
   rw 1 (q378 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q402 : Ws → Eqn
  q402 c4 = eqn (Sw34 ∷ Sb2-0-43-1 ∷ []) (Sb2-0-34-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·43·1⟩ (lit c4))
  q403 : Ws → Eqn
  q403 c4 = eqn (CCZ013 ∷ Sb2-0-34-1 ∷ []) (Sb2-0-34-1 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at132132 c4)
  q404 : Ws → Eqn
  q404 c4 = eqn (Sw34 ∷ Sb2-0-34-1 ∷ []) (Sb2-0-43-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·34·1⟩ (lit c4))

-- auto CCZ012 | SBOX(3;0;14;2) @14213243: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14213243 : Ws → ⟪ (CCZ014 ∷ Sb2-0-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-43-1 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14213243 c4 = derive (CCZ014 ∷ Sb2-0-43-1 ∷ []) (Sb2-0-43-1 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q379 c4) ∷
   rw 2 (q402 c4) ∷
   rw 1 (q403 c4) ∷
   rw 0 (q404 c4) ∷
   rw 1 (q383 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q405 : Ws → Eqn
  q405 c4 = eqn (Sw12 ∷ Sb1-0-43-2 ∷ []) (Sb2-0-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·43·2⟩ (lit c4))
  q406 : Ws → Eqn
  q406 c4 = eqn (CCZ014 ∷ Sb2-0-43-1 ∷ []) (Sb2-0-43-1 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14213243 c4)
  q407 : Ws → Eqn
  q407 c4 = eqn (Sw12 ∷ Sb2-0-43-1 ∷ []) (Sb1-0-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·43·1⟩ (lit c4))

-- auto CCZ012 | SBOX(3;0;14;2) @143143: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at143143 : Ws → ⟪ (CCZ024 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at143143 c4 = derive (CCZ024 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q384 c4) ∷
   rw 2 (q405 c4) ∷
   rw 1 (q406 c4) ∷
   rw 0 (q407 c4) ∷
   rw 1 (q386 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q408 : Ws → Eqn
  q408 c4 = eqn (Sw23 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·42·3⟩ (lit c4))
  q409 : Ws → Eqn
  q409 c4 = eqn (CCZ024 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at143143 c4)

-- auto CCZ012 | SBOX(3;0;14;2) @14233142: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14233142 : Ws → ⟪ (CCZ034 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14233142 c4 = derive (CCZ034 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q64 c4) ∷
   rw 1 (q175 c4) ∷
   rw 2 (q408 c4) ∷
   rw 1 (q409 c4) ∷
   rw 0 (q66 c4) ∷
   rw 1 (q390 c4) ∷
   rw 2 (q64 c4) ∷ []) Eq.refl

private
  q410 : Ws → Eqn
  q410 c4 = eqn (CCZ034 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14233142 c4)

-- auto CCZ012 | SBOX(3;0;14;2) @14233241: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14233241 : Ws → ⟪ (CCZ034 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14233241 c4 = derive (CCZ034 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q254 c4) ∷
   rw 2 (q106 c4) ∷
   rw 1 (q410 c4) ∷
   rw 0 (q61 c4) ∷
   rw 1 (q254 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q411 : Ws → Eqn
  q411 c4 = eqn (Sb0-1-32-4 ∷ K4 ∷ []) (K4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 c4)

-- auto SBOX(0;1;23;4) | K4 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at243243 c4 = derive (Sb0-1-42-3 ∷ K3 ∷ []) (K3 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q242 c4) ∷
   rw⁻ 2 (q299 c4) ∷
   rw 1 (q411 c4) ∷
   rw⁻ 0 (q301 c4) ∷
   rw 1 (q244 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q412 : Ws → Eqn
  q412 c4 = eqn (Sb0-1-42-3 ∷ K3 ∷ []) (K3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at243243 c4)

-- auto SBOX(0;1;23;4) | K4 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0110243243 c4 = derive (Sb1-0-42-3 ∷ K3 ∷ []) (K3 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q101 c4) ∷
   rw 2 (q202 c4) ∷
   rw 1 (q412 c4) ∷
   rw 0 (q202 c4) ∷
   rw 1 (q103 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q413 : Ws → Eqn
  q413 c4 = eqn (Sb1-0-42-3 ∷ K3 ∷ []) (K3 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0110243243 c4)

-- auto SBOX(0;1;23;4) | K4 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 c4 = derive (Sb2-0-41-3 ∷ K3 ∷ []) (K3 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q106 c4) ∷
   rw 2 (q204 c4) ∷
   rw 1 (q413 c4) ∷
   rw 0 (q204 c4) ∷
   rw 1 (q61 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q414 : Ws → Eqn
  q414 c4 = eqn (Sb0-1-32-4 ∷ CS34 ∷ []) (CS34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 c4)

-- auto SBOX(0;1;23;4) | CS24 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at243243 c4 = derive (Sb0-1-42-3 ∷ CS34 ∷ []) (CS34 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q242 c4) ∷
   rw⁻ 2 (q305 c4) ∷
   rw 1 (q414 c4) ∷
   rw⁻ 0 (q305 c4) ∷
   rw 1 (q244 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q415 : Ws → Eqn
  q415 c4 = eqn (Sb0-1-42-3 ∷ CS34 ∷ []) (CS34 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at243243 c4)

-- auto SBOX(0;1;23;4) | CS24 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at0110243243 c4 = derive (Sb1-0-42-3 ∷ CS34 ∷ []) (CS34 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q101 c4) ∷
   rw 2 (q152 c4) ∷
   rw 1 (q415 c4) ∷
   rw 0 (q152 c4) ∷
   rw 1 (q103 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q416 : Ws → Eqn
  q416 c4 = eqn (Sb1-0-42-3 ∷ CS34 ∷ []) (CS34 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at0110243243 c4)

-- auto SBOX(0;1;23;4) | CS24 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at0210243143 c4 = derive (Sb2-0-41-3 ∷ CS34 ∷ []) (CS34 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw 1 (q106 c4) ∷
   rw 2 (q154 c4) ∷
   rw 1 (q416 c4) ∷
   rw 0 (q154 c4) ∷
   rw 1 (q61 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q417 : Ws → Eqn
  q417 c4 = eqn (Sb0-1-32-4 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 c4)

-- auto SBOX(0;1;23;4) | Kd4 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at243243 c4 = derive (Sb0-1-42-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q51 c4) ∷
   rw 1 (q242 c4) ∷
   rw⁻ 2 (q311 c4) ∷
   rw 1 (q417 c4) ∷
   rw⁻ 0 (q313 c4) ∷
   rw 1 (q244 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q418 : Ws → Eqn
  q418 c4 = eqn (Sb0-1-42-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at243243 c4)

-- auto SBOX(0;1;23;4) | Kd4 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0110243243 c4 = derive (Sb1-0-42-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q101 c4) ∷
   rw 2 (q126 c4) ∷
   rw 1 (q418 c4) ∷
   rw 0 (q126 c4) ∷
   rw 1 (q103 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D174 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0012 ; wl0016 ; wl0019 ; wl0022 ; wl0024 ; wl0025 ; wl0031 ; wl0043 ; wl0046 ; wl0056 ; wl0061 ; wl0062 ; wl0076 ; wl0103 ; wl0121 ; wl0190 ; wl0257 ; wl0306 ; wl0307 ; wl0308 ; wl0597 ; wl0598 ; wp0370 ; wp0371 ; wp0372)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-beta-T-at14213243 ; lem-sym34 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 ; lem-sym23-at243243 ; lem-sym23-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-SBsym-at0113203442 ; lem-auto-BOX⟨0·1234⟩-∣-K0 ; lem-auto-BOX⟨0·1234⟩-∣-Kd0 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-CS20-beta-c-at243243 ; lem-CS20-beta-ci-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D089 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX24-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D161 using (lem-auto-BOX⟨0·1234⟩-∣-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.D173 using (lem-auto-BOX⟨0·1234⟩-∣-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023 ; lem-nat-1-TOFF014 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-3-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ013 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-3-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-2-CSd02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-2-CS04 ; lem-nat-2-CSd04 ; lem-nat-3-CS04 ; lem-nat-3-CSd04)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-2-CSd03 ; lem-nat-3-CS03 ; lem-nat-3-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-BOX⟨0·4213⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-SBOX⟨0·2·3·1⟩ ; lem-nat-0-SBOX⟨1·2·3·0⟩ ; lem-nat-0-SBOXd⟨0·2·3·1⟩ ; lem-nat-0-SBOXd⟨1·2·3·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-1-SBOX⟨0·1·3·2⟩ ; lem-nat-1-SBOX⟨0·2·3·1⟩ ; lem-nat-1-SBOXd⟨0·1·3·2⟩ ; lem-nat-1-SBOXd⟨0·2·3·1⟩ ; lem-nat-2-SBOX⟨1·2·4·0⟩ ; lem-nat-2-SBOX⟨1·3·4·0⟩ ; lem-nat-2-SBOXd⟨1·2·4·0⟩ ; lem-nat-2-SBOXd⟨1·3·4·0⟩ ; lem-nat-3-SBOX⟨1·2·3·0⟩ ; lem-nat-3-SBOX⟨1·2·4·0⟩ ; lem-nat-3-SBOXd⟨1·2·3·0⟩ ; lem-nat-3-SBOXd⟨1·2·4·0⟩)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CS02⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS02⁻ ∷ []) (wp0370 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (CS02⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS02⁻ ∷ []) (wp0371 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CS02⁻ ∷ CS14 ∷ []) (CS14 ∷ CS02⁻ ∷ []) (wp0372 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Bx0-1234 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd02 c4)

-- auto SBOX(0;1;23;4) | CSd02: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02 : Ws → ⟪ (Sb0-1-23-4 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02 c4 = derive (Sb0-1-23-4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q1 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw⁻ 2 (q3 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw⁻ 1 (q2 c4) ∷
   rw 0 (q4 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q5 : Ws → Eqn
  q5 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (Sw23 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (Sw23 ∷ CS03⁻ ∷ []) (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Sb0-1-23-4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (Sw23 ∷ CS02⁻ ∷ []) (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Sw23 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | CSd02 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02-at2332 c4 = derive (Sb0-1-32-4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   rw 0 (q9 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q11 : Ws → Eqn
  q11 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1243 ∷ []) (lem-sym34 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Bx0-1243 ∷ []) (Bx0-1423 ∷ []) (lem-sym23-at3443 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (CS04 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS04 ∷ []) (lem-CS20-beta-c-at243243 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx0-1423 ∷ []) (Bx0-1243 ∷ []) (lem-sym23-at243243 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (Bx0-1243 ∷ []) (Bx0-1234 ∷ []) (lem-sym34-at3443 c4)

-- auto BOX(0;1234) | CS04: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CS04 : Ws → ⟪ (Bx0-1234 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS04 c4 = derive (Bx0-1234 ∷ CS04 ∷ []) (CS04 ∷ Bx0-1234 ∷ [])
  (rw 0 (q11 c4) ∷
   rw 0 (q12 c4) ∷
   rw⁻ 0 (q13 c4) ∷
   rw 1 (q14 c4) ∷
   rw 1 (q15 c4) ∷ []) Eq.refl

private
  q16 : Ws → Eqn
  q16 c4 = eqn (CS04⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS04⁻ ∷ []) (lem-CS20-beta-ci-at243243 c4)

-- auto BOX(0;1234) | CSd04: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd04 : Ws → ⟪ (Bx0-1234 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd04 c4 = derive (Bx0-1234 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx0-1234 ∷ [])
  (rw 0 (q11 c4) ∷
   rw 0 (q12 c4) ∷
   rw⁻ 0 (q16 c4) ∷
   rw 1 (q14 c4) ∷
   rw 1 (q15 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Sw12 ∷ Bx0-4213 ∷ []) (Bx0-4123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·4213⟩ (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Bx0-4123 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at14213243 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Sw12 ∷ Toff014 ∷ []) (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4))

-- beta-T @143143: 8 steps
lem-beta-T-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-beta-T-at143143 c4 = derive (Bx0-4213 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q18 c4) ∷
   rw 1 (q19 c4) ∷
   rw 0 (q20 c4) ∷
   rw 1 (q21 c4) ∷
   rw 2 (q20 c4) ∷
   rw 3 (q21 c4) ∷
   rw 4 (q17 c4) ∷ []) Eq.refl

private
  q22 : Ws → Eqn
  q22 c4 = eqn (Sw23 ∷ Bx0-1324 ∷ []) (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw23 ∷ CS04 ∷ []) (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (Bx0-1234 ∷ CS04 ∷ []) (CS04 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS04 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Sw23 ∷ Bx0-1234 ∷ []) (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4))

-- auto BOX(0;1234) | CS04 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS04-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS04-at2332 c4 = derive (Bx0-1324 ∷ CS04 ∷ []) (CS04 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q22 c4) ∷
   rw 2 (q23 c4) ∷
   rw 1 (q24 c4) ∷
   rw 0 (q23 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q26 : Ws → Eqn
  q26 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (Sw34 ∷ Bx0-1423 ∷ []) (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (Sw34 ∷ CS03 ∷ []) (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (Bx0-1324 ∷ CS04 ∷ []) (CS04 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS04-at2332 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (Sw34 ∷ CS04 ∷ []) (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (Sw34 ∷ Bx0-1324 ∷ []) (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4))

-- auto BOX(0;1234) | CS04 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS04-at243243 : Ws → ⟪ (Bx0-1423 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS04-at243243 c4 = derive (Bx0-1423 ∷ CS03 ∷ []) (CS03 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q27 c4) ∷
   rw 2 (q28 c4) ∷
   rw 1 (q29 c4) ∷
   rw 0 (q30 c4) ∷
   rw 1 (q31 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q32 : Ws → Eqn
  q32 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (Sw01 ∷ Bx1-0423 ∷ []) (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) (wl0019 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (Bx0-1423 ∷ CS03 ∷ []) (CS03 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS04-at243243 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (CS13 ∷ Sw01 ∷ []) (Sw01 ∷ CS03 ∷ []) (wl0061 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (Sw01 ∷ Bx0-1423 ∷ []) (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4))

-- auto BOX(0;1234) | CS04 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS04-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS04-at0110243243 c4 = derive (Bx1-0423 ∷ CS13 ∷ []) (CS13 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw⁻ 2 (q34 c4) ∷
   rw 1 (q35 c4) ∷
   rw⁻ 0 (q36 c4) ∷
   rw 1 (q37 c4) ∷
   rw 2 (q32 c4) ∷ []) Eq.refl

private
  q38 : Ws → Eqn
  q38 c4 = eqn (Sw12 ∷ Bx2-0413 ∷ []) (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl0024 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (Bx1-0423 ∷ CS13 ∷ []) (CS13 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS04-at0110243243 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl0025 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (Sw12 ∷ Bx1-0423 ∷ []) (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4))

-- auto BOX(0;1234) | CS04 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS04-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS04-at0210243143 c4 = derive (Bx2-0413 ∷ CS23 ∷ []) (CS23 ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q38 c4) ∷
   rw⁻ 2 (q39 c4) ∷
   rw 1 (q40 c4) ∷
   rw⁻ 0 (q41 c4) ∷
   rw 1 (q42 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q43 : Ws → Eqn
  q43 c4 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (c₁ (K) (Swap ↑))
  q44 : Ws → Eqn
  q44 c4 = eqn (Bx0-1234 ∷ K0 ∷ []) (K0 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0 c4)

-- auto BOX(0;1234) | K0 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at2332 : Ws → ⟪ (Bx0-1324 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at2332 c4 = derive (Bx0-1324 ∷ K0 ∷ []) (K0 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q22 c4) ∷
   rw⁻ 2 (q43 c4) ∷
   rw 1 (q44 c4) ∷
   rw⁻ 0 (q43 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q45 : Ws → Eqn
  q45 c4 = eqn (K0 ∷ Sw34 ∷ []) (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑))
  q46 : Ws → Eqn
  q46 c4 = eqn (Bx0-1324 ∷ K0 ∷ []) (K0 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at2332 c4)

-- auto BOX(0;1234) | K0 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at243243 : Ws → ⟪ (Bx0-1423 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at243243 c4 = derive (Bx0-1423 ∷ K0 ∷ []) (K0 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q27 c4) ∷
   rw⁻ 2 (q45 c4) ∷
   rw 1 (q46 c4) ∷
   rw⁻ 0 (q45 c4) ∷
   rw 1 (q31 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q47 : Ws → Eqn
  q47 c4 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wl0031 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (Bx0-1423 ∷ K0 ∷ []) (K0 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at243243 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wl0076 (lit c4))

-- auto BOX(0;1234) | K0 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at0110243243 c4 = derive (Bx1-0423 ∷ K1 ∷ []) (K1 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw⁻ 2 (q47 c4) ∷
   rw 1 (q48 c4) ∷
   rw⁻ 0 (q49 c4) ∷
   rw 1 (q37 c4) ∷
   rw 2 (q32 c4) ∷ []) Eq.refl

private
  q50 : Ws → Eqn
  q50 c4 = eqn (K1 ∷ Sw12 ∷ []) (Sw12 ∷ K2 ∷ []) (wl0062 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (Bx1-0423 ∷ K1 ∷ []) (K1 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at0110243243 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wl0056 (lit c4))

-- auto BOX(0;1234) | K0 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at0210243143 c4 = derive (Bx2-0413 ∷ K2 ∷ []) (K2 ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q38 c4) ∷
   rw⁻ 2 (q50 c4) ∷
   rw 1 (q51 c4) ∷
   rw⁻ 0 (q52 c4) ∷
   rw 1 (q42 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑))
  q54 : Ws → Eqn
  q54 c4 = eqn (Bx0-1234 ∷ K0⁻ ∷ []) (K0⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0 c4)

-- auto BOX(0;1234) | Kd0 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at2332 : Ws → ⟪ (Bx0-1324 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at2332 c4 = derive (Bx0-1324 ∷ K0⁻ ∷ []) (K0⁻ ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q22 c4) ∷
   rw⁻ 2 (q53 c4) ∷
   rw 1 (q54 c4) ∷
   rw⁻ 0 (q53 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = eqn (K0⁻ ∷ Sw34 ∷ []) (Sw34 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ ↑))
  q56 : Ws → Eqn
  q56 c4 = eqn (Bx0-1324 ∷ K0⁻ ∷ []) (K0⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at2332 c4)

-- auto BOX(0;1234) | Kd0 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at243243 : Ws → ⟪ (Bx0-1423 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at243243 c4 = derive (Bx0-1423 ∷ K0⁻ ∷ []) (K0⁻ ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q27 c4) ∷
   rw⁻ 2 (q55 c4) ∷
   rw 1 (q56 c4) ∷
   rw⁻ 0 (q55 c4) ∷
   rw 1 (q31 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q57 : Ws → Eqn
  q57 c4 = eqn (K0⁻ ∷ Sw01 ∷ []) (Sw01 ∷ K1⁻ ∷ []) (wl0257 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (Bx0-1423 ∷ K0⁻ ∷ []) (K0⁻ ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at243243 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (K1⁻ ∷ Sw01 ∷ []) (Sw01 ∷ K0⁻ ∷ []) (wl0306 (lit c4))

-- auto BOX(0;1234) | Kd0 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0110243243 c4 = derive (Bx1-0423 ∷ K1⁻ ∷ []) (K1⁻ ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw⁻ 2 (q57 c4) ∷
   rw 1 (q58 c4) ∷
   rw⁻ 0 (q59 c4) ∷
   rw 1 (q37 c4) ∷
   rw 2 (q32 c4) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = eqn (K1⁻ ∷ Sw12 ∷ []) (Sw12 ∷ K2⁻ ∷ []) (wl0307 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (Bx1-0423 ∷ K1⁻ ∷ []) (K1⁻ ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0110243243 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (K2⁻ ∷ Sw12 ∷ []) (Sw12 ∷ K1⁻ ∷ []) (wl0308 (lit c4))

-- auto BOX(0;1234) | Kd0 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0210243143 c4 = derive (Bx2-0413 ∷ K2⁻ ∷ []) (K2⁻ ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q38 c4) ∷
   rw⁻ 2 (q60 c4) ∷
   rw 1 (q61 c4) ∷
   rw⁻ 0 (q62 c4) ∷
   rw 1 (q42 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = eqn (Sw23 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (Bx0-1234 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd04 c4)

-- auto BOX(0;1234) | CSd04 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at2332 c4 = derive (Bx0-1324 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q22 c4) ∷
   rw 2 (q63 c4) ∷
   rw 1 (q64 c4) ∷
   rw 0 (q63 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = eqn (Sw34 ∷ CS03⁻ ∷ []) (CS04⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd03 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (Bx0-1324 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd04-at2332 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (Sw34 ∷ CS04⁻ ∷ []) (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 (lit c4))

-- auto BOX(0;1234) | CSd04 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at243243 : Ws → ⟪ (Bx0-1423 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at243243 c4 = derive (Bx0-1423 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q27 c4) ∷
   rw 2 (q65 c4) ∷
   rw 1 (q66 c4) ∷
   rw 0 (q67 c4) ∷
   rw 1 (q31 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q68 : Ws → Eqn
  q68 c4 = eqn (CS03⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS13⁻ ∷ []) (wl0022 (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (Bx0-1423 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd04-at243243 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (CS13⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS03⁻ ∷ []) (wl0121 (lit c4))

-- auto BOX(0;1234) | CSd04 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at0110243243 c4 = derive (Bx1-0423 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw⁻ 2 (q68 c4) ∷
   rw 1 (q69 c4) ∷
   rw⁻ 0 (q70 c4) ∷
   rw 1 (q37 c4) ∷
   rw 2 (q32 c4) ∷ []) Eq.refl

private
  q71 : Ws → Eqn
  q71 c4 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wl0043 (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (Bx1-0423 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd04-at0110243243 c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wl0046 (lit c4))

-- auto BOX(0;1234) | CSd04 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at0210243143 c4 = derive (Bx2-0413 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q38 c4) ∷
   rw⁻ 2 (q71 c4) ∷
   rw 1 (q72 c4) ∷
   rw⁻ 0 (q73 c4) ∷
   rw 1 (q42 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q74 : Ws → Eqn
  q74 c4 = eqn (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl0190 (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (Sb0-1-32-4 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41-at2332 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (Sb0-1-32-4 ∷ CX34 ∷ []) (CX34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX24-at2332 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (Sb0-1-32-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41-at2332 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (Sb0-1-32-4 ∷ CS13 ∷ []) (CS13 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 c4)

-- auto SBOX(0;1;23;4) | CCZ134: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134 : Ws → ⟪ (Sb0-1-23-4 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134 c4 = derive (Sb0-1-23-4 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sb0-1-23-4 ∷ [])
  (rw 1 (q74 c4) ∷
   rw 0 (q75 c4) ∷
   rw 0 (q76 c4) ∷
   rw 1 (q77 c4) ∷
   rw 2 (q78 c4) ∷
   rw 3 (q77 c4) ∷
   rw 4 (q79 c4) ∷
   rw⁻ 5 (q75 c4) ∷
   rw⁻ 0 (q74 c4) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = eqn (Sb0-1-32-4 ∷ CS34 ∷ []) (CS34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 c4)

-- auto SBOX(0;1;23;4) | SBOX(1;3;4;0): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb1-3-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-4-0 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩ c4 = derive (Sb0-1-23-4 ∷ Sb1-3-4-0 ∷ []) (Sb1-3-4-0 ∷ Sb0-1-23-4 ∷ [])
  (re 1 1 (CS34 ∷ []) ∷
   rw 0 (q75 c4) ∷
   rw 0 (q80 c4) ∷
   rw⁻ 1 (q75 c4) ∷
   re 0 1 (Sb1-3-4-0 ∷ []) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = eqn (CS14⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS14⁻ ∷ []) (wl0597 (lit c4))
  q82 : Ws → Eqn
  q82 c4 = eqn (CS24⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS24⁻ ∷ []) (wl0598 (lit c4))
  q83 : Ws → Eqn
  q83 c4 = eqn (Bx0-1234 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd24 c4)

-- auto SBOX(0;1;23;4) | CSd24: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd24 : Ws → ⟪ (Sb0-1-23-4 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd24 c4 = derive (Sb0-1-23-4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   re 4 1 (CS14⁻ ∷ []) ∷
   rw 4 (q81 c4) ∷
   re 5 1 (Sb⁻0-1-4-3 ∷ []) ∷
   re 2 1 (CS14 ∷ []) ∷
   rw⁻ 1 (q82 c4) ∷
   re 3 1 (Sb0-1-4-3 ∷ []) ∷
   rw 0 (q83 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q84 : Ws → Eqn
  q84 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl0016 (lit c4))
  q85 : Ws → Eqn
  q85 c4 = eqn (Sb0-1-23-4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd24 c4)
  q86 : Ws → Eqn
  q86 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl0012 (lit c4))

-- auto SBOX(0;1;23;4) | CSd24 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd24-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd24-at2332 c4 = derive (Sb0-1-32-4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw⁻ 2 (q84 c4) ∷
   rw 1 (q85 c4) ∷
   rw⁻ 0 (q86 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q87 : Ws → Eqn
  q87 c4 = eqn (Sb0-1-32-4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd24-at2332 c4)

-- auto SBOX(0;1;23;4) | SBOXd(1;3;4;0): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb⁻1-3-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-4-0 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩ c4 = derive (Sb0-1-23-4 ∷ Sb⁻1-3-4-0 ∷ []) (Sb⁻1-3-4-0 ∷ Sb0-1-23-4 ∷ [])
  (re 1 1 (CS34⁻ ∷ []) ∷
   rw 0 (q75 c4) ∷
   rw 0 (q87 c4) ∷
   rw⁻ 1 (q75 c4) ∷
   re 0 1 (Sb⁻1-3-4-0 ∷ []) ∷ []) Eq.refl

private
  q88 : Ws → Eqn
  q88 c4 = eqn (Sw23 ∷ CCZ124 ∷ []) (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4))
  q89 : Ws → Eqn
  q89 c4 = eqn (Sb0-1-23-4 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (Sw23 ∷ CCZ134 ∷ []) (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4))

-- auto SBOX(0;1;23;4) | CCZ134 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at2332 c4 = derive (Sb0-1-32-4 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q88 c4) ∷
   rw 1 (q89 c4) ∷
   rw 0 (q90 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q91 : Ws → Eqn
  q91 c4 = eqn (Sw34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4))
  q92 : Ws → Eqn
  q92 c4 = eqn (Sw34 ∷ CCZ123 ∷ []) (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 (lit c4))
  q93 : Ws → Eqn
  q93 c4 = eqn (Sb0-1-32-4 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at2332 c4)
  q94 : Ws → Eqn
  q94 c4 = eqn (Sw34 ∷ CCZ124 ∷ []) (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 (lit c4))
  q95 : Ws → Eqn
  q95 c4 = eqn (Sw34 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | CCZ134 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at243243 c4 = derive (Sb0-1-42-3 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q91 c4) ∷
   rw 2 (q92 c4) ∷
   rw 1 (q93 c4) ∷
   rw 0 (q94 c4) ∷
   rw 1 (q95 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q96 : Ws → Eqn
  q96 c4 = eqn (Sw01 ∷ Sb1-0-42-3 ∷ []) (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4))
  q97 : Ws → Eqn
  q97 c4 = eqn (CCZ123 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ []) (wl0103 (lit c4))
  q98 : Ws → Eqn
  q98 c4 = eqn (Sb0-1-42-3 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at243243 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ []) (wl0003 (lit c4))
  q100 : Ws → Eqn
  q100 c4 = eqn (Sw01 ∷ Sb0-1-42-3 ∷ []) (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4))

-- auto SBOX(0;1;23;4) | CCZ134 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at0110243243 c4 = derive (Sb1-0-42-3 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q32 c4) ∷
   rw 1 (q96 c4) ∷
   rw⁻ 2 (q97 c4) ∷
   rw 1 (q98 c4) ∷
   rw⁻ 0 (q99 c4) ∷
   rw 1 (q100 c4) ∷
   rw 2 (q32 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = eqn (Sw12 ∷ Sb2-0-41-3 ∷ []) (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4))
  q102 : Ws → Eqn
  q102 c4 = eqn (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4))
  q103 : Ws → Eqn
  q103 c4 = eqn (Sb1-0-42-3 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at0110243243 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4))

-- auto SBOX(0;1;23;4) | CCZ134 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at0210243143 c4 = derive (Sb2-0-41-3 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q101 c4) ∷
   rw 2 (q102 c4) ∷
   rw 1 (q103 c4) ∷
   rw 0 (q21 c4) ∷
   rw 1 (q104 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q105 : Ws → Eqn
  q105 c4 = eqn (Sw23 ∷ Sb1-2-4-0 ∷ []) (Sb1-3-4-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·2·4·0⟩ (lit c4))
  q106 : Ws → Eqn
  q106 c4 = eqn (Sb0-1-23-4 ∷ Sb1-3-4-0 ∷ []) (Sb1-3-4-0 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩ c4)
  q107 : Ws → Eqn
  q107 c4 = eqn (Sw23 ∷ Sb1-3-4-0 ∷ []) (Sb1-2-4-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·4·0⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(1;3;4;0) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb1-2-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-4-0 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at2332 c4 = derive (Sb0-1-32-4 ∷ Sb1-2-4-0 ∷ []) (Sb1-2-4-0 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q105 c4) ∷
   rw 1 (q106 c4) ∷
   rw 0 (q107 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = eqn (Sw34 ∷ Sb1-2-3-0 ∷ []) (Sb1-2-4-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·3·0⟩ (lit c4))
  q109 : Ws → Eqn
  q109 c4 = eqn (Sb0-1-32-4 ∷ Sb1-2-4-0 ∷ []) (Sb1-2-4-0 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at2332 c4)
  q110 : Ws → Eqn
  q110 c4 = eqn (Sw34 ∷ Sb1-2-4-0 ∷ []) (Sb1-2-3-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·4·0⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(1;3;4;0) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-3-0 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at243243 c4 = derive (Sb0-1-42-3 ∷ Sb1-2-3-0 ∷ []) (Sb1-2-3-0 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q91 c4) ∷
   rw 2 (q108 c4) ∷
   rw 1 (q109 c4) ∷
   rw 0 (q110 c4) ∷
   rw 1 (q95 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q111 : Ws → Eqn
  q111 c4 = eqn (Sw01 ∷ Sb0-2-3-1 ∷ []) (Sb1-2-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·3·1⟩ (lit c4))
  q112 : Ws → Eqn
  q112 c4 = eqn (Sb0-1-42-3 ∷ Sb1-2-3-0 ∷ []) (Sb1-2-3-0 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at243243 c4)
  q113 : Ws → Eqn
  q113 c4 = eqn (Sw01 ∷ Sb1-2-3-0 ∷ []) (Sb0-2-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·3·0⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(1;3;4;0) @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ Sb0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-3-1 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at0110243243 c4 = derive (Sb1-0-42-3 ∷ Sb0-2-3-1 ∷ []) (Sb0-2-3-1 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q32 c4) ∷
   rw 1 (q96 c4) ∷
   rw 2 (q111 c4) ∷
   rw 1 (q112 c4) ∷
   rw 0 (q113 c4) ∷
   rw 1 (q100 c4) ∷
   rw 2 (q32 c4) ∷ []) Eq.refl

private
  q114 : Ws → Eqn
  q114 c4 = eqn (Sw12 ∷ Sb0-1-3-2 ∷ []) (Sb0-2-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·3·2⟩ (lit c4))
  q115 : Ws → Eqn
  q115 c4 = eqn (Sb1-0-42-3 ∷ Sb0-2-3-1 ∷ []) (Sb0-2-3-1 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at0110243243 c4)
  q116 : Ws → Eqn
  q116 c4 = eqn (Sw12 ∷ Sb0-2-3-1 ∷ []) (Sb0-1-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·3·1⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(1;3;4;0) @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at0210243143 c4 = derive (Sb2-0-41-3 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-3-2 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q101 c4) ∷
   rw 2 (q114 c4) ∷
   rw 1 (q115 c4) ∷
   rw 0 (q116 c4) ∷
   rw 1 (q104 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

private
  q117 : Ws → Eqn
  q117 c4 = eqn (Sw23 ∷ Sb⁻1-2-4-0 ∷ []) (Sb⁻1-3-4-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·2·4·0⟩ (lit c4))
  q118 : Ws → Eqn
  q118 c4 = eqn (Sb0-1-23-4 ∷ Sb⁻1-3-4-0 ∷ []) (Sb⁻1-3-4-0 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩ c4)
  q119 : Ws → Eqn
  q119 c4 = eqn (Sw23 ∷ Sb⁻1-3-4-0 ∷ []) (Sb⁻1-2-4-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·3·4·0⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(1;3;4;0) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb⁻1-2-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-4-0 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at2332 c4 = derive (Sb0-1-32-4 ∷ Sb⁻1-2-4-0 ∷ []) (Sb⁻1-2-4-0 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q117 c4) ∷
   rw 1 (q118 c4) ∷
   rw 0 (q119 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q120 : Ws → Eqn
  q120 c4 = eqn (Sw34 ∷ Sb⁻1-2-3-0 ∷ []) (Sb⁻1-2-4-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·2·3·0⟩ (lit c4))
  q121 : Ws → Eqn
  q121 c4 = eqn (Sb0-1-32-4 ∷ Sb⁻1-2-4-0 ∷ []) (Sb⁻1-2-4-0 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at2332 c4)
  q122 : Ws → Eqn
  q122 c4 = eqn (Sw34 ∷ Sb⁻1-2-4-0 ∷ []) (Sb⁻1-2-3-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·2·4·0⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(1;3;4;0) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb⁻1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-3-0 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at243243 c4 = derive (Sb0-1-42-3 ∷ Sb⁻1-2-3-0 ∷ []) (Sb⁻1-2-3-0 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 1 (q91 c4) ∷
   rw 2 (q120 c4) ∷
   rw 1 (q121 c4) ∷
   rw 0 (q122 c4) ∷
   rw 1 (q95 c4) ∷
   rw 2 (q26 c4) ∷ []) Eq.refl

private
  q123 : Ws → Eqn
  q123 c4 = eqn (Sw01 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻1-2-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·2·3·1⟩ (lit c4))
  q124 : Ws → Eqn
  q124 c4 = eqn (Sb0-1-42-3 ∷ Sb⁻1-2-3-0 ∷ []) (Sb⁻1-2-3-0 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at243243 c4)
  q125 : Ws → Eqn
  q125 c4 = eqn (Sw01 ∷ Sb⁻1-2-3-0 ∷ []) (Sb⁻0-2-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·2·3·0⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(1;3;4;0) @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ Sb⁻0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-3-1 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at0110243243 c4 = derive (Sb1-0-42-3 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻0-2-3-1 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q32 c4) ∷
   rw 1 (q96 c4) ∷
   rw 2 (q123 c4) ∷
   rw 1 (q124 c4) ∷
   rw 0 (q125 c4) ∷
   rw 1 (q100 c4) ∷
   rw 2 (q32 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = eqn (Sw12 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-2-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·1·3·2⟩ (lit c4))
  q127 : Ws → Eqn
  q127 c4 = eqn (Sb1-0-42-3 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻0-2-3-1 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at0110243243 c4)
  q128 : Ws → Eqn
  q128 c4 = eqn (Sw12 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻0-1-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·3·1⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(1;3;4;0) @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at0210243143 c4 = derive (Sb2-0-41-3 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q101 c4) ∷
   rw 2 (q126 c4) ∷
   rw 1 (q127 c4) ∷
   rw 0 (q128 c4) ∷
   rw 1 (q104 c4) ∷
   rw 2 (q17 c4) ∷ []) Eq.refl

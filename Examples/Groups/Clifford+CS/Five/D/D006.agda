{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D006 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0019 ; wl0022 ; wl0024 ; wl0025 ; wl0043 ; wl0046 ; wl0061 ; wl0121 ; wl0372 ; wl0373 ; wl0374 ; wl0375 ; wl0376 ; wl0377 ; wl0378 ; wl0379 ; wl0380 ; wl0381 ; wl0382 ; wl0383 ; wl0384 ; wl0385 ; wl0386 ; wl0387 ; wl0388 ; wl0389 ; wl0390 ; wl0391 ; wl0392 ; wl0393 ; wl0394 ; wl0395 ; wl0396 ; wl0397 ; wl0398 ; wl0399 ; wl0400 ; wl0401 ; wl0402 ; wl0403 ; wl0404 ; wl0405 ; wl0406 ; wl0407 ; wl0408 ; wl0409 ; wl0410 ; wl0411 ; wl0412 ; wl0413 ; wl0414 ; wl0415 ; wl0416 ; wl0417 ; wl0418 ; wl0419 ; wp0113 ; wp0124 ; wp0125 ; wp0126 ; wp0127 ; wp0128 ; wp0129 ; wp0130 ; wp0131 ; wp0132 ; wp0133 ; wp0134 ; wp0135 ; wp0136 ; wp0137 ; wp0138 ; wp0139 ; wp0140 ; wp0141 ; wp0142 ; wp0143 ; wp0144)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-auto-CSd01-∣-BOX⟨2·3104⟩ ; lem-auto-S0-∣-BOX⟨1·2304⟩ ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩ ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩ ; lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-F5-CS01-at1441 ; lem-SBsym-at1441 ; lem-auto-BOX⟨0·1234⟩-∣-CS40 ; lem-auto-BOX⟨0·1234⟩-∣-CSd40 ; lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 ; lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 ; lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0312203441 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0110243243 ; lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 ; lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 ; lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-3-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-TOFF014 ; lem-nat-0-TOFF104 ; lem-nat-1-TOFF104 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨2·0413⟩ ; lem-nat-0-BOX⟨2·1403⟩ ; lem-nat-0-SBOX⟨0·1·3·2⟩ ; lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·3·2⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-0-SBOXd⟨0·1·3·2⟩ ; lem-nat-0-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-CSd02 ; lem-nat-1-SBOX⟨1·0·3·2⟩ ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·3·1⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-1-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-SBOXd⟨2·0·3·1⟩ ; lem-nat-2-CSd02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-CSd14 ; lem-nat-1-CSd01 ; lem-nat-1-CSd04 ; lem-nat-2-CS04 ; lem-nat-2-CSd04 ; lem-nat-3-CS04 ; lem-nat-3-CSd04)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-CSd04 ; lem-nat-2-CSd03 ; lem-nat-3-CS03 ; lem-nat-3-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-CX41-TOFF203 ; lem-nat-1-BOX⟨1·3204⟩ ; lem-nat-1-BOX⟨2·3104⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-BOX⟨1·2403⟩ ; lem-nat-1-BOX⟨2·1403⟩ ; lem-nat-2-BOX⟨1·2304⟩ ; lem-nat-2-BOX⟨1·3204⟩ ; lem-nat-3-BOX⟨1·2304⟩ ; lem-nat-3-BOX⟨1·2403⟩)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Sw12 ∷ Sb2-0-41-3 ∷ []) (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (Sw12 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K • iI))
  q4 : Ws → Eqn
  q4 c4 = eqn (Sb1-0-42-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0110243243 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4))

-- auto SBOX(0;1;23;4) | Kd4 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0210243143 c4 = derive (Sb2-0-41-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q4 c4) ∷
   rw 0 (q3 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q6 : Ws → Eqn
  q6 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (Sw23 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Sw23 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (Sb0-1-23-4 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-3 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩ c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (Sw23 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw23 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(0;1;4;3) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-2 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at2332 c4 = derive (Sb0-1-32-4 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-4-2 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q7 c4) ∷
   rw 2 (q8 c4) ∷
   rw 1 (q9 c4) ∷
   rw 0 (q10 c4) ∷
   rw 1 (q11 c4) ∷
   rw 2 (q6 c4) ∷ []) Eq.refl

private
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (Sw34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (Sw34 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (Sb0-1-32-4 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-4-2 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at2332 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Sw34 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (Sw34 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(0;1;4;3) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at243243 c4 = derive (Sb0-1-42-3 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-3-2 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q13 c4) ∷
   rw 2 (q14 c4) ∷
   rw 1 (q15 c4) ∷
   rw 0 (q16 c4) ∷
   rw 1 (q17 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q18 : Ws → Eqn
  q18 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw01 ∷ Sb1-0-42-3 ∷ []) (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (Sw01 ∷ Sb1-0-3-2 ∷ []) (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Sb0-1-42-3 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-3-2 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at243243 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (Sw01 ∷ Sb0-1-3-2 ∷ []) (Sb1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·3·2⟩ (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw01 ∷ Sb0-1-42-3 ∷ []) (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(0;1;4;3) @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-2 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0110243243 c4 = derive (Sb1-0-42-3 ∷ Sb1-0-3-2 ∷ []) (Sb1-0-3-2 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q19 c4) ∷
   rw 2 (q20 c4) ∷
   rw 1 (q21 c4) ∷
   rw 0 (q22 c4) ∷
   rw 1 (q23 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q24 : Ws → Eqn
  q24 c4 = eqn (Sw12 ∷ Sb2-0-3-1 ∷ []) (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (Sb1-0-42-3 ∷ Sb1-0-3-2 ∷ []) (Sb1-0-3-2 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0110243243 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (Sw12 ∷ Sb1-0-3-2 ∷ []) (Sb2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·3·2⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(0;1;4;3) @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-1 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 c4 = derive (Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q24 c4) ∷
   rw 1 (q25 c4) ∷
   rw 0 (q26 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = eqn (Sw23 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (Sb0-1-23-4 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-3 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩ c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (Sw23 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(0;1;4;3) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-2 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at2332 c4 = derive (Sb0-1-32-4 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-4-2 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q7 c4) ∷
   rw 2 (q27 c4) ∷
   rw 1 (q28 c4) ∷
   rw 0 (q29 c4) ∷
   rw 1 (q11 c4) ∷
   rw 2 (q6 c4) ∷ []) Eq.refl

private
  q30 : Ws → Eqn
  q30 c4 = eqn (Sw34 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (Sb0-1-32-4 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-4-2 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at2332 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Sw34 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(0;1;4;3) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at243243 c4 = derive (Sb0-1-42-3 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q13 c4) ∷
   rw 2 (q30 c4) ∷
   rw 1 (q31 c4) ∷
   rw 0 (q32 c4) ∷
   rw 1 (q17 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q33 : Ws → Eqn
  q33 c4 = eqn (Sw01 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (Sb0-1-42-3 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at243243 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (Sw01 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·3·2⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(0;1;4;3) @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0110243243 c4 = derive (Sb1-0-42-3 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q19 c4) ∷
   rw 2 (q33 c4) ∷
   rw 1 (q34 c4) ∷
   rw 0 (q35 c4) ∷
   rw 1 (q23 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q36 : Ws → Eqn
  q36 c4 = eqn (Sw12 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (Sb1-0-42-3 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0110243243 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Sw12 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·3·2⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(0;1;4;3) @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0210243143 c4 = derive (Sb2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q36 c4) ∷
   rw 1 (q37 c4) ∷
   rw 0 (q38 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = eqn (Sw12 ∷ CS02⁻ ∷ []) (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (Sw12 ∷ Bx1-3204 ∷ []) (Bx2-3104 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3204⟩ (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CS01⁻ ∷ Bx2-3104 ∷ []) (Bx2-3104 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨2·3104⟩ c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (Sw12 ∷ Bx2-3104 ∷ []) (Bx1-3204 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3104⟩ (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (Sw12 ∷ CS01⁻ ∷ []) (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 (lit c4))

-- auto CSd01 | BOX(2;3104) @1221: 7 steps
lem-auto-CSd01-∣-BOX⟨2·3104⟩-at1221 : Ws → ⟪ (CS02⁻ ∷ Bx1-3204 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3204 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·3104⟩-at1221 c4 = derive (CS02⁻ ∷ Bx1-3204 ∷ []) (Bx1-3204 ∷ CS02⁻ ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q39 c4) ∷
   rw 2 (q40 c4) ∷
   rw 1 (q41 c4) ∷
   rw 0 (q42 c4) ∷
   rw 1 (q43 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q44 : Ws → Eqn
  q44 c4 = eqn (Sw23 ∷ CS03⁻ ∷ []) (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (Sw23 ∷ Bx1-2304 ∷ []) (Bx1-3204 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·2304⟩ (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (CS02⁻ ∷ Bx1-3204 ∷ []) (Bx1-3204 ∷ CS02⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨2·3104⟩-at1221 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (Sw23 ∷ Bx1-3204 ∷ []) (Bx1-2304 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·3204⟩ (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (Sw23 ∷ CS02⁻ ∷ []) (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 (lit c4))

-- auto CSd01 | BOX(2;3104) @132132: 7 steps
lem-auto-CSd01-∣-BOX⟨2·3104⟩-at132132 : Ws → ⟪ (CS03⁻ ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·3104⟩-at132132 c4 = derive (CS03⁻ ∷ Bx1-2304 ∷ []) (Bx1-2304 ∷ CS03⁻ ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q44 c4) ∷
   rw 2 (q45 c4) ∷
   rw 1 (q46 c4) ∷
   rw 0 (q47 c4) ∷
   rw 1 (q48 c4) ∷
   rw 2 (q6 c4) ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = eqn (Sw34 ∷ CS04⁻ ∷ []) (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (Sw34 ∷ Bx1-2403 ∷ []) (Bx1-2304 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2403⟩ (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CS03⁻ ∷ Bx1-2304 ∷ []) (Bx1-2304 ∷ CS03⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨2·3104⟩-at132132 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (Sw34 ∷ Bx1-2304 ∷ []) (Bx1-2403 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2304⟩ (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (Sw34 ∷ CS03⁻ ∷ []) (CS04⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd03 (lit c4))

-- auto CSd01 | BOX(2;3104) @14213243: 7 steps
lem-auto-CSd01-∣-BOX⟨2·3104⟩-at14213243 : Ws → ⟪ (CS04⁻ ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·3104⟩-at14213243 c4 = derive (CS04⁻ ∷ Bx1-2403 ∷ []) (Bx1-2403 ∷ CS04⁻ ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q49 c4) ∷
   rw 2 (q50 c4) ∷
   rw 1 (q51 c4) ∷
   rw 0 (q52 c4) ∷
   rw 1 (q53 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q54 : Ws → Eqn
  q54 c4 = eqn (Sw12 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd04 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (Sw12 ∷ Bx2-1403 ∷ []) (Bx1-2403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1403⟩ (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (CS04⁻ ∷ Bx1-2403 ∷ []) (Bx1-2403 ∷ CS04⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨2·3104⟩-at14213243 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (Sw12 ∷ Bx1-2403 ∷ []) (Bx2-1403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2403⟩ (lit c4))

-- auto CSd01 | BOX(2;3104) @143143: 7 steps
lem-auto-CSd01-∣-BOX⟨2·3104⟩-at143143 : Ws → ⟪ (CS04⁻ ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·3104⟩-at143143 c4 = derive (CS04⁻ ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ CS04⁻ ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q54 c4) ∷
   rw 2 (q55 c4) ∷
   rw 1 (q56 c4) ∷
   rw 0 (q57 c4) ∷
   rw 1 (q54 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q58 : Ws → Eqn
  q58 c4 = eqn (Sw01 ∷ CS14⁻ ∷ []) (CS04⁻ ∷ Sw01 ∷ []) (lem-nat-0-CSd14 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (Sw01 ∷ Bx2-0413 ∷ []) (Bx2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0413⟩ (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (CS04⁻ ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ CS04⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨2·3104⟩-at143143 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (Sw01 ∷ Bx2-1403 ∷ []) (Bx2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1403⟩ (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (Sw01 ∷ CS04⁻ ∷ []) (CS14⁻ ∷ Sw01 ∷ []) (lem-nat-0-CSd04 (lit c4))

-- auto CSd01 | BOX(2;3104) @01143043: 7 steps
lem-auto-CSd01-∣-BOX⟨2·3104⟩-at01143043 : Ws → ⟪ (CS14⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS14⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·3104⟩-at01143043 c4 = derive (CS14⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS14⁻ ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q58 c4) ∷
   rw 2 (q59 c4) ∷
   rw 1 (q60 c4) ∷
   rw 0 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = eqn (S0 ∷ Sw34 ∷ []) (Sw34 ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑))
  q64 : Ws → Eqn
  q64 c4 = eqn (S0 ∷ Bx1-2304 ∷ []) (Bx1-2304 ∷ S0 ∷ []) (lem-auto-S0-∣-BOX⟨1·2304⟩ c4)

-- auto S0 | BOX(1;2304) @3443: 7 steps
lem-auto-S0-∣-BOX⟨1·2304⟩-at3443 : Ws → ⟪ (S0 ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2304⟩-at3443 c4 = derive (S0 ∷ Bx1-2403 ∷ []) (Bx1-2403 ∷ S0 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw⁻ 1 (q63 c4) ∷
   rw 2 (q50 c4) ∷
   rw 1 (q64 c4) ∷
   rw 0 (q52 c4) ∷
   rw⁻ 1 (q63 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = eqn (S0 ∷ Sw12 ∷ []) (Sw12 ∷ S0 ∷ []) (c₁ (S) (Swap))
  q66 : Ws → Eqn
  q66 c4 = eqn (S0 ∷ Bx1-2403 ∷ []) (Bx1-2403 ∷ S0 ∷ []) (lem-auto-S0-∣-BOX⟨1·2304⟩-at3443 c4)

-- auto S0 | BOX(1;2304) @12213443: 7 steps
lem-auto-S0-∣-BOX⟨1·2304⟩-at12213443 : Ws → ⟪ (S0 ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2304⟩-at12213443 c4 = derive (S0 ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ S0 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q65 c4) ∷
   rw 2 (q55 c4) ∷
   rw 1 (q66 c4) ∷
   rw 0 (q57 c4) ∷
   rw⁻ 1 (q65 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q67 : Ws → Eqn
  q67 c4 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wl0372 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (S0 ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ S0 ∷ []) (lem-auto-S0-∣-BOX⟨1·2304⟩-at12213443 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (S1 ∷ Sw01 ∷ []) (Sw01 ∷ S0 ∷ []) (wl0373 (lit c4))

-- auto S0 | BOX(1;2304) @0112203443: 7 steps
lem-auto-S0-∣-BOX⟨1·2304⟩-at0112203443 : Ws → ⟪ (S1 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ S1 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2304⟩-at0112203443 c4 = derive (S1 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ S1 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw⁻ 1 (q67 c4) ∷
   rw 2 (q59 c4) ∷
   rw 1 (q68 c4) ∷
   rw 0 (q61 c4) ∷
   rw⁻ 1 (q69 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q70 : Ws → Eqn
  q70 c4 = eqn (Sw23 ∷ Toff013 ∷ []) (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (Sb0-1-23-4 ∷ Toff012 ∷ []) (Toff012 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (Sw23 ∷ Toff012 ∷ []) (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4))

-- auto SBOX(0;1;23;4) | TOFF012 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012-at2332 c4 = derive (Sb0-1-32-4 ∷ Toff013 ∷ []) (Toff013 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q7 c4) ∷
   rw 2 (q70 c4) ∷
   rw 1 (q71 c4) ∷
   rw 0 (q72 c4) ∷
   rw 1 (q11 c4) ∷
   rw 2 (q6 c4) ∷ []) Eq.refl

private
  q73 : Ws → Eqn
  q73 c4 = eqn (Sw34 ∷ Toff014 ∷ []) (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (Sb0-1-32-4 ∷ Toff013 ∷ []) (Toff013 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012-at2332 c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (Sw34 ∷ Toff013 ∷ []) (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 (lit c4))

-- auto SBOX(0;1;23;4) | TOFF012 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012-at243243 c4 = derive (Sb0-1-42-3 ∷ Toff014 ∷ []) (Toff014 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q13 c4) ∷
   rw 2 (q73 c4) ∷
   rw 1 (q74 c4) ∷
   rw 0 (q75 c4) ∷
   rw 1 (q17 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q76 : Ws → Eqn
  q76 c4 = eqn (Sw01 ∷ Toff104 ∷ []) (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 (lit c4))
  q77 : Ws → Eqn
  q77 c4 = eqn (Sb0-1-42-3 ∷ Toff014 ∷ []) (Toff014 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012-at243243 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (Sw01 ∷ Toff014 ∷ []) (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 (lit c4))

-- auto SBOX(0;1;23;4) | TOFF012 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012-at0110243243 c4 = derive (Sb1-0-42-3 ∷ Toff104 ∷ []) (Toff104 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q19 c4) ∷
   rw 2 (q76 c4) ∷
   rw 1 (q77 c4) ∷
   rw 0 (q78 c4) ∷
   rw 1 (q23 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q79 : Ws → Eqn
  q79 c4 = eqn (Sw12 ∷ Toff204 ∷ []) (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 (lit c4))
  q80 : Ws → Eqn
  q80 c4 = eqn (Sb1-0-42-3 ∷ Toff104 ∷ []) (Toff104 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012-at0110243243 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (Sw12 ∷ Toff104 ∷ []) (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 (lit c4))

-- auto SBOX(0;1;23;4) | TOFF012 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012-at0210243143 c4 = derive (Sb2-0-41-3 ∷ Toff204 ∷ []) (Toff204 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q79 c4) ∷
   rw 1 (q80 c4) ∷
   rw 0 (q81 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q82 : Ws → Eqn
  q82 c4 = eqn (Sw23 ∷ Bx0-1324 ∷ []) (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4))
  q83 : Ws → Eqn
  q83 c4 = eqn (Sw23 ∷ CS04 ∷ []) (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4))
  q84 : Ws → Eqn
  q84 c4 = eqn (Bx0-1234 ∷ CS04 ∷ []) (CS04 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS40 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (Sw23 ∷ Bx0-1234 ∷ []) (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4))

-- auto BOX(0;1234) | CS40 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS40-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS40-at2332 c4 = derive (Bx0-1324 ∷ CS04 ∷ []) (CS04 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q82 c4) ∷
   rw 2 (q83 c4) ∷
   rw 1 (q84 c4) ∷
   rw 0 (q83 c4) ∷
   rw 1 (q85 c4) ∷
   rw 2 (q6 c4) ∷ []) Eq.refl

private
  q86 : Ws → Eqn
  q86 c4 = eqn (Sw34 ∷ Bx0-1423 ∷ []) (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4))
  q87 : Ws → Eqn
  q87 c4 = eqn (Sw34 ∷ CS03 ∷ []) (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 (lit c4))
  q88 : Ws → Eqn
  q88 c4 = eqn (Bx0-1324 ∷ CS04 ∷ []) (CS04 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS40-at2332 c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (Sw34 ∷ CS04 ∷ []) (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 (lit c4))
  q90 : Ws → Eqn
  q90 c4 = eqn (Sw34 ∷ Bx0-1324 ∷ []) (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4))

-- auto BOX(0;1234) | CS40 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS40-at243243 : Ws → ⟪ (Bx0-1423 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS40-at243243 c4 = derive (Bx0-1423 ∷ CS03 ∷ []) (CS03 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q86 c4) ∷
   rw 2 (q87 c4) ∷
   rw 1 (q88 c4) ∷
   rw 0 (q89 c4) ∷
   rw 1 (q90 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q91 : Ws → Eqn
  q91 c4 = eqn (Sw01 ∷ Bx1-0423 ∷ []) (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4))
  q92 : Ws → Eqn
  q92 c4 = eqn (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) (wl0019 (lit c4))
  q93 : Ws → Eqn
  q93 c4 = eqn (Bx0-1423 ∷ CS03 ∷ []) (CS03 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS40-at243243 c4)
  q94 : Ws → Eqn
  q94 c4 = eqn (CS13 ∷ Sw01 ∷ []) (Sw01 ∷ CS03 ∷ []) (wl0061 (lit c4))
  q95 : Ws → Eqn
  q95 c4 = eqn (Sw01 ∷ Bx0-1423 ∷ []) (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4))

-- auto BOX(0;1234) | CS40 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS40-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS40-at0110243243 c4 = derive (Bx1-0423 ∷ CS13 ∷ []) (CS13 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q91 c4) ∷
   rw⁻ 2 (q92 c4) ∷
   rw 1 (q93 c4) ∷
   rw⁻ 0 (q94 c4) ∷
   rw 1 (q95 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q96 : Ws → Eqn
  q96 c4 = eqn (Sw12 ∷ Bx2-0413 ∷ []) (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4))
  q97 : Ws → Eqn
  q97 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl0024 (lit c4))
  q98 : Ws → Eqn
  q98 c4 = eqn (Bx1-0423 ∷ CS13 ∷ []) (CS13 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS40-at0110243243 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl0025 (lit c4))
  q100 : Ws → Eqn
  q100 c4 = eqn (Sw12 ∷ Bx1-0423 ∷ []) (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4))

-- auto BOX(0;1234) | CS40 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS40-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS40-at0210243143 c4 = derive (Bx2-0413 ∷ CS23 ∷ []) (CS23 ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q96 c4) ∷
   rw⁻ 2 (q97 c4) ∷
   rw 1 (q98 c4) ∷
   rw⁻ 0 (q99 c4) ∷
   rw 1 (q100 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = eqn (Sw23 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 (lit c4))
  q102 : Ws → Eqn
  q102 c4 = eqn (Bx0-1234 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd40 c4)

-- auto BOX(0;1234) | CSd40 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd40-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd40-at2332 c4 = derive (Bx0-1324 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q6 c4) ∷
   rw 1 (q82 c4) ∷
   rw 2 (q101 c4) ∷
   rw 1 (q102 c4) ∷
   rw 0 (q101 c4) ∷
   rw 1 (q85 c4) ∷
   rw 2 (q6 c4) ∷ []) Eq.refl

private
  q103 : Ws → Eqn
  q103 c4 = eqn (Bx0-1324 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd40-at2332 c4)

-- auto BOX(0;1234) | CSd40 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd40-at243243 : Ws → ⟪ (Bx0-1423 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd40-at243243 c4 = derive (Bx0-1423 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 1 (q86 c4) ∷
   rw 2 (q53 c4) ∷
   rw 1 (q103 c4) ∷
   rw 0 (q49 c4) ∷
   rw 1 (q90 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q104 : Ws → Eqn
  q104 c4 = eqn (CS03⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS13⁻ ∷ []) (wl0022 (lit c4))
  q105 : Ws → Eqn
  q105 c4 = eqn (Bx0-1423 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd40-at243243 c4)
  q106 : Ws → Eqn
  q106 c4 = eqn (CS13⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS03⁻ ∷ []) (wl0121 (lit c4))

-- auto BOX(0;1234) | CSd40 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd40-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd40-at0110243243 c4 = derive (Bx1-0423 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q91 c4) ∷
   rw⁻ 2 (q104 c4) ∷
   rw 1 (q105 c4) ∷
   rw⁻ 0 (q106 c4) ∷
   rw 1 (q95 c4) ∷
   rw 2 (q18 c4) ∷ []) Eq.refl

private
  q107 : Ws → Eqn
  q107 c4 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wl0043 (lit c4))
  q108 : Ws → Eqn
  q108 c4 = eqn (Bx1-0423 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd40-at0110243243 c4)
  q109 : Ws → Eqn
  q109 c4 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wl0046 (lit c4))

-- auto BOX(0;1234) | CSd40 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd40-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd40-at0210243143 c4 = derive (Bx2-0413 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q96 c4) ∷
   rw⁻ 2 (q107 c4) ∷
   rw 1 (q108 c4) ∷
   rw⁻ 0 (q109 c4) ∷
   rw 1 (q100 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q110 : Ws → Eqn
  q110 c4 = eqn (CK40⁻ ∷ CK40 ∷ []) [] (wp0124 c4)
  q111 : Ws → Eqn
  q111 c4 = eqn (CK40 ∷ CK40 ∷ []) (S4⁻ ∷ []) (wp0125 c4)
  q112 : Ws → Eqn
  q112 c4 = eqn (CK40 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (wp0126 c4)
  q113 : Ws → Eqn
  q113 c4 = eqn (X1 ∷ S1 ∷ X1 ∷ S1 ∷ []) (ι ∷ []) (wl0374 (lit c4))
  q114 : Ws → Eqn
  q114 c4 = eqn (CS14⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (S4⁻ ∷ []) (wl0375 (lit c4))
  q115 : Ws → Eqn
  q115 c4 = eqn (CS04 ∷ []) (CS04 ∷ []) (wp0113 c4)
  q116 : Ws → Eqn
  q116 c4 = eqn (X1 ∷ Sb2-0-14-3 ∷ X1 ∷ Sb2-0-14-3 ∷ []) (CS04 ∷ []) (lem-F5-CS01-at1441 c4)
  q117 : Ws → Eqn
  q117 c4 = eqn (Sb2-0-14-3 ∷ []) (Sb2-0-41-3 ∷ []) (lem-SBsym-at1441 c4)
  q118 : Ws → Eqn
  q118 c4 = eqn (K0 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CK10 ∷ []) (wl0376 (lit c4))
  q119 : Ws → Eqn
  q119 c4 = eqn (CS14⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ CS14⁻ ∷ []) (wl0377 (lit c4))
  q120 : Ws → Eqn
  q120 c4 = eqn (S1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ []) (wl0378 (lit c4))
  q121 : Ws → Eqn
  q121 c4 = eqn (X1 ∷ X1 ∷ []) [] (wl0379 (lit c4))
  q122 : Ws → Eqn
  q122 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q123 : Ws → Eqn
  q123 c4 = eqn (CS14⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS14⁻ ∷ []) (wp0127 c4)
  q124 : Ws → Eqn
  q124 c4 = eqn (CS14⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS14⁻ ∷ []) (wl0380 (lit c4))
  q125 : Ws → Eqn
  q125 c4 = eqn (CS14⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS14⁻ ∷ []) (wl0381 (lit c4))
  q126 : Ws → Eqn
  q126 c4 = eqn (CS14⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS14⁻ ∷ []) (wp0128 c4)
  q127 : Ws → Eqn
  q127 c4 = eqn (CS14⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS14⁻ ∷ []) (wp0129 c4)
  q128 : Ws → Eqn
  q128 c4 = eqn (S1 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ S1 ∷ []) (wp0130 c4)
  q129 : Ws → Eqn
  q129 c4 = eqn (S1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ S1 ∷ []) (wl0382 (lit c4))
  q130 : Ws → Eqn
  q130 c4 = eqn (S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ S1 ∷ []) (wl0383 (lit c4))
  q131 : Ws → Eqn
  q131 c4 = eqn (S1 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ S1 ∷ []) (wl0384 (lit c4))
  q132 : Ws → Eqn
  q132 c4 = eqn (S1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ S1 ∷ []) (wl0385 (lit c4))
  q133 : Ws → Eqn
  q133 c4 = eqn (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp0131 c4)
  q134 : Ws → Eqn
  q134 c4 = eqn (Toff314 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ Toff314 ∷ []) (wp0132 c4)
  q135 : Ws → Eqn
  q135 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q136 : Ws → Eqn
  q136 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q137 : Ws → Eqn
  q137 c4 = eqn (X1 ∷ CCZ234 ∷ []) (CCZ234 ∷ X1 ∷ []) (c₂ (X ↑) (CCZ))
  q138 : Ws → Eqn
  q138 c4 = eqn (CK10 ∷ CCZ234 ∷ []) (CCZ234 ∷ CK10 ∷ []) (c₂ (CK₁₀) (CCZ))
  q139 : Ws → Eqn
  q139 c4 = eqn (Toff201 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ Toff201 ∷ []) (wl0386 (lit c4))
  q140 : Ws → Eqn
  q140 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q141 : Ws → Eqn
  q141 c4 = eqn (CS14⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CS14⁻ ∷ []) (wp0133 c4)
  q142 : Ws → Eqn
  q142 c4 = eqn (S1 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ S1 ∷ []) (wl0387 (lit c4))
  q143 : Ws → Eqn
  q143 c4 = eqn (CK10 ∷ []) (ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ []) (wl0388 (lit c4))
  q144 : Ws → Eqn
  q144 c4 = eqn (CS01 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ []) (wp0134 c4)
  q145 : Ws → Eqn
  q145 c4 = eqn (CS01 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ []) (wl0389 (lit c4))
  q146 : Ws → Eqn
  q146 c4 = eqn (CS01 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ []) (wp0135 c4)
  q147 : Ws → Eqn
  q147 c4 = eqn (CS01 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS01 ∷ []) (wl0390 (lit c4))
  q148 : Ws → Eqn
  q148 c4 = eqn (CS01 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ []) (wl0391 (lit c4))
  q149 : Ws → Eqn
  q149 c4 = eqn (K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) (wl0392 (lit c4))
  q150 : Ws → Eqn
  q150 c4 = eqn (K0 ∷ X1 ∷ []) (X1 ∷ K0 ∷ []) (c₁ (K) (X))
  q151 : Ws → Eqn
  q151 c4 = eqn (K0 ∷ CCZ234 ∷ []) (CCZ234 ∷ K0 ∷ []) (c₁ (K) (CCZ ↑))
  q152 : Ws → Eqn
  q152 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4))
  q153 : Ws → Eqn
  q153 c4 = eqn (CS01 ∷ X1 ∷ CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ X1 ∷ CS01 ∷ []) (wl0394 (lit c4))
  q154 : Ws → Eqn
  q154 c4 = eqn (CS01 ∷ X1 ∷ CX43 ∷ X1 ∷ []) (X1 ∷ CX43 ∷ X1 ∷ CS01 ∷ []) (wl0395 (lit c4))
  q155 : Ws → Eqn
  q155 c4 = eqn (CS01 ∷ X1 ∷ CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ X1 ∷ CS01 ∷ []) (wl0396 (lit c4))
  q156 : Ws → Eqn
  q156 c4 = eqn (CS01 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CS01 ∷ []) (wp0136 c4)
  q157 : Ws → Eqn
  q157 c4 = eqn (K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) (wp0137 c4)
  q158 : Ws → Eqn
  q158 c4 = eqn (K0 ∷ CS01 ∷ K0 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) (wp0138 c4)
  q159 : Ws → Eqn
  q159 c4 = eqn (S1⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ S1⁻ ∷ []) (wp0139 c4)
  q160 : Ws → Eqn
  q160 c4 = eqn (S1⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ S1⁻ ∷ []) (wl0397 (lit c4))
  q161 : Ws → Eqn
  q161 c4 = eqn (S1⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ S1⁻ ∷ []) (wl0398 (lit c4))
  q162 : Ws → Eqn
  q162 c4 = eqn (S1⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ S1⁻ ∷ []) (wl0399 (lit c4))
  q163 : Ws → Eqn
  q163 c4 = eqn (S1⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ S1⁻ ∷ []) (wl0400 (lit c4))
  q164 : Ws → Eqn
  q164 c4 = eqn (X1 ∷ ι ∷ []) (ι ∷ X1 ∷ []) zc
  q165 : Ws → Eqn
  q165 c4 = eqn (Sb2-0-41-3 ∷ ι ∷ []) (ι ∷ Sb2-0-41-3 ∷ []) zc
  q166 : Ws → Eqn
  q166 c4 = eqn (CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ []) (wl0401 (lit c4))
  q167 : Ws → Eqn
  q167 c4 = eqn (Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 c4)
  q168 : Ws → Eqn
  q168 c4 = eqn (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl0402 (lit c4))
  q169 : Ws → Eqn
  q169 c4 = eqn (K3⁻ ∷ X1 ∷ []) (X1 ∷ K3⁻ ∷ []) (wl0403 (lit c4))
  q170 : Ws → Eqn
  q170 c4 = eqn (K3⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ K3⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4)
  q171 : Ws → Eqn
  q171 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4))
  q172 : Ws → Eqn
  q172 c4 = eqn (CS34 ∷ X1 ∷ []) (X1 ∷ CS34 ∷ []) (wl0405 (lit c4))
  q173 : Ws → Eqn
  q173 c4 = eqn (CS34 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS34 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 c4)
  q174 : Ws → Eqn
  q174 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q175 : Ws → Eqn
  q175 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)
  q176 : Ws → Eqn
  q176 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q177 : Ws → Eqn
  q177 c4 = eqn (CX41 ∷ X1 ∷ []) (X1 ∷ CX41 ∷ []) (wl0406 (lit c4))
  q178 : Ws → Eqn
  q178 c4 = eqn (CX41 ∷ Toff203 ∷ []) (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4))
  q179 : Ws → Eqn
  q179 c4 = eqn (CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ []) (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) (wl0407 (lit c4))
  q180 : Ws → Eqn
  q180 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ []) (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wl0408 (lit c4))
  q181 : Ws → Eqn
  q181 c4 = eqn (Bx2-0341 ∷ []) (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4)
  q182 : Ws → Eqn
  q182 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4)
  q183 : Ws → Eqn
  q183 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0140 c4)
  q184 : Ws → Eqn
  q184 c4 = eqn (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0141 c4)
  q185 : Ws → Eqn
  q185 c4 = eqn (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (Toff204 ∷ []) (wp0142 c4)
  q186 : Ws → Eqn
  q186 c4 = eqn (CS13 ∷ X1 ∷ K2 ∷ X1 ∷ []) (X1 ∷ K2 ∷ X1 ∷ CS13 ∷ []) (wl0409 (lit c4))
  q187 : Ws → Eqn
  q187 c4 = eqn (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4)
  q188 : Ws → Eqn
  q188 c4 = eqn (CS13 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CS13 ∷ []) (wl0410 (lit c4))
  q189 : Ws → Eqn
  q189 c4 = eqn (CS13 ∷ X1 ∷ CX04 ∷ X1 ∷ []) (X1 ∷ CX04 ∷ X1 ∷ CS13 ∷ []) (wp0144 c4)
  q190 : Ws → Eqn
  q190 c4 = eqn (CS13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ []) (X1 ∷ CS24⁻ ∷ X1 ∷ CS13 ∷ []) (wl0411 (lit c4))
  q191 : Ws → Eqn
  q191 c4 = eqn (CS13 ∷ X1 ∷ CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ X1 ∷ CS13 ∷ []) (wl0412 (lit c4))
  q192 : Ws → Eqn
  q192 c4 = eqn (CS13 ∷ X1 ∷ K2⁻ ∷ X1 ∷ []) (X1 ∷ K2⁻ ∷ X1 ∷ CS13 ∷ []) (wl0413 (lit c4))
  q193 : Ws → Eqn
  q193 c4 = eqn (CS13 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS13 ∷ []) (wl0414 (lit c4))
  q194 : Ws → Eqn
  q194 c4 = eqn (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (wl0415 (lit c4))
  q195 : Ws → Eqn
  q195 c4 = eqn (CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) (wl0416 (lit c4))
  q196 : Ws → Eqn
  q196 c4 = eqn (CS13 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) (wl0417 (lit c4))
  q197 : Ws → Eqn
  q197 c4 = eqn (K3 ∷ X1 ∷ []) (X1 ∷ K3 ∷ []) (wl0418 (lit c4))
  q198 : Ws → Eqn
  q198 c4 = eqn (K3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ K3 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4)
  q199 : Ws → Eqn
  q199 c4 = eqn (CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ []) (wl0419 (lit c4))
  q200 : Ws → Eqn
  q200 c4 = eqn (Sb2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 c4)

-- F1 CS-K0 [rhs shape] part0: 500 steps
lem-F1-CS-K0-rhs-shape-part0 : Ws → ⟪ (CS04 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS13 ∷ X1 ∷ K2 ∷ CCZ024 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K0-rhs-shape-part0 c4 = derive (CS04 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS13 ∷ X1 ∷ K2 ∷ CCZ024 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 3 (q110 c4) ∷
   rw 4 (q111 c4) ∷
   rw 1 (q112 c4) ∷
   rw⁻ 1 (q113 c4) ∷
   rw⁻ 5 (q114 c4) ∷
   rw 9 (q115 c4) ∷
   rw⁻ 9 (q116 c4) ∷
   rw 10 (q117 c4) ∷
   rw 12 (q117 c4) ∷
   rw 13 (q118 c4) ∷
   rw 17 (q115 c4) ∷
   rw⁻ 17 (q116 c4) ∷
   rw 18 (q117 c4) ∷
   rw 20 (q117 c4) ∷
   rw 21 (q118 c4) ∷
   rw 25 (q115 c4) ∷
   rw⁻ 25 (q116 c4) ∷
   rw 26 (q117 c4) ∷
   rw 28 (q117 c4) ∷
   rw 5 (q119 c4) ∷
   rw 4 (q120 c4) ∷
   re 10 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 11 (q121 c4) ∷
   rw⁻ 14 (q121 c4) ∷
   rw⁻ 17 (q121 c4) ∷
   rw⁻ 20 (q121 c4) ∷
   rw 10 (q122 c4) ∷
   rw⁻ 11 (q121 c4) ∷
   rw⁻ 14 (q121 c4) ∷
   rw⁻ 17 (q121 c4) ∷
   rw 8 (q123 c4) ∷
   rw 11 (q124 c4) ∷
   rw 14 (q123 c4) ∷
   rw 17 (q124 c4) ∷
   rw 10 (q121 c4) ∷
   rw 11 (q121 c4) ∷
   rw 12 (q121 c4) ∷
   rw⁻ 9 (q122 c4) ∷
   rw 11 (q125 c4) ∷
   re 16 1 (CS03 ∷ []) ∷
   rw 14 (q126 c4) ∷
   re 15 1 (Sb2-0-3-1 ∷ []) ∷
   rw 17 (q125 c4) ∷
   re 22 1 (CS03⁻ ∷ []) ∷
   rw 20 (q127 c4) ∷
   re 21 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 10 (q121 c4) ∷
   rw 11 (q121 c4) ∷
   rw 12 (q121 c4) ∷
   rw 13 (q121 c4) ∷
   re 9 5 (Sb2-0-41-3 ∷ []) ∷
   re 9 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 10 (q121 c4) ∷
   rw⁻ 13 (q121 c4) ∷
   rw⁻ 16 (q121 c4) ∷
   rw⁻ 19 (q121 c4) ∷
   rw 9 (q122 c4) ∷
   rw⁻ 10 (q121 c4) ∷
   rw⁻ 13 (q121 c4) ∷
   rw⁻ 16 (q121 c4) ∷
   rw 7 (q128 c4) ∷
   rw 10 (q129 c4) ∷
   rw 13 (q128 c4) ∷
   rw 16 (q129 c4) ∷
   rw 9 (q121 c4) ∷
   rw 10 (q121 c4) ∷
   rw 11 (q121 c4) ∷
   rw⁻ 8 (q122 c4) ∷
   rw 10 (q130 c4) ∷
   re 15 1 (CS03 ∷ []) ∷
   rw 13 (q131 c4) ∷
   re 14 1 (Sb2-0-3-1 ∷ []) ∷
   rw 16 (q130 c4) ∷
   re 21 1 (CS03⁻ ∷ []) ∷
   rw 19 (q132 c4) ∷
   re 20 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 9 (q121 c4) ∷
   rw 10 (q121 c4) ∷
   rw 11 (q121 c4) ∷
   rw 12 (q121 c4) ∷
   re 8 5 (Sb2-0-41-3 ∷ []) ∷
   re 12 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 14 1 (CS03 ∷ []) ∷
   re 16 1 (CS03⁻ ∷ []) ∷
   rw 14 (q133 c4) ∷
   re 17 1 (Sb2-0-3-1 ∷ []) ∷
   re 19 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 13 (q134 c4) ∷
   rw 12 (q135 c4) ∷
   rw 12 (q136 c4) ∷
   rw⁻ 15 (q137 c4) ∷
   rw⁻ 16 (q138 c4) ∷
   rw⁻ 17 (q137 c4) ∷
   rw 14 (q139 c4) ∷
   rw⁻ 13 (q137 c4) ∷
   rw⁻ 14 (q138 c4) ∷
   rw⁻ 15 (q137 c4) ∷
   rw 12 (q139 c4) ∷
   rw⁻ 15 (q136 c4) ∷
   rw 15 (q140 c4) ∷
   re 15 5 (Sb2-0-41-3 ∷ []) ∷
   rw 11 (q141 c4) ∷
   rw 10 (q142 c4) ∷
   rw 16 (q143 c4) ∷
   re 24 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 25 (q121 c4) ∷
   rw⁻ 28 (q121 c4) ∷
   rw⁻ 31 (q121 c4) ∷
   rw⁻ 34 (q121 c4) ∷
   rw 24 (q122 c4) ∷
   rw⁻ 25 (q121 c4) ∷
   rw⁻ 28 (q121 c4) ∷
   rw⁻ 31 (q121 c4) ∷
   rw 22 (q144 c4) ∷
   rw 25 (q145 c4) ∷
   rw 28 (q144 c4) ∷
   rw 31 (q145 c4) ∷
   rw 24 (q121 c4) ∷
   rw 25 (q121 c4) ∷
   rw 26 (q121 c4) ∷
   rw⁻ 23 (q122 c4) ∷
   rw 25 (q146 c4) ∷
   re 30 1 (CS03 ∷ []) ∷
   rw 28 (q147 c4) ∷
   re 29 1 (Sb2-0-3-1 ∷ []) ∷
   rw 31 (q146 c4) ∷
   re 36 1 (CS03⁻ ∷ []) ∷
   rw 34 (q148 c4) ∷
   re 35 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 24 (q121 c4) ∷
   rw 25 (q121 c4) ∷
   rw 26 (q121 c4) ∷
   rw 27 (q121 c4) ∷
   re 23 5 (Sb2-0-41-3 ∷ []) ∷
   re 23 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 24 (q121 c4) ∷
   rw⁻ 27 (q121 c4) ∷
   rw⁻ 30 (q121 c4) ∷
   rw⁻ 33 (q121 c4) ∷
   rw 23 (q135 c4) ∷
   rw 23 (q136 c4) ∷
   rw⁻ 24 (q121 c4) ∷
   rw⁻ 27 (q121 c4) ∷
   rw⁻ 30 (q121 c4) ∷
   rw 19 (q149 c4) ∷
   rw 24 (q150 c4) ∷
   rw 25 (q151 c4) ∷
   rw 26 (q150 c4) ∷
   rw 25 (q152 c4) ∷
   rw⁻ 26 (q121 c4) ∷
   rw⁻ 29 (q121 c4) ∷
   rw⁻ 32 (q121 c4) ∷
   rw⁻ 35 (q121 c4) ∷
   rw 23 (q153 c4) ∷
   rw 26 (q154 c4) ∷
   rw 29 (q155 c4) ∷
   rw 32 (q154 c4) ∷
   rw 35 (q156 c4) ∷
   rw 25 (q121 c4) ∷
   rw 26 (q121 c4) ∷
   rw 27 (q121 c4) ∷
   rw 28 (q121 c4) ∷
   rw⁻ 24 (q152 c4) ∷
   rw 22 (q150 c4) ∷
   rw 23 (q151 c4) ∷
   rw 24 (q150 c4) ∷
   rw 25 (q149 c4) ∷
   rw 30 (q150 c4) ∷
   rw 31 (q151 c4) ∷
   rw 32 (q150 c4) ∷
   rw 31 (q152 c4) ∷
   rw⁻ 32 (q121 c4) ∷
   rw⁻ 35 (q121 c4) ∷
   rw⁻ 38 (q121 c4) ∷
   rw⁻ 41 (q121 c4) ∷
   rw 29 (q153 c4) ∷
   rw 32 (q154 c4) ∷
   rw 35 (q155 c4) ∷
   rw 38 (q154 c4) ∷
   rw 41 (q156 c4) ∷
   rw 31 (q121 c4) ∷
   rw 32 (q121 c4) ∷
   rw 33 (q121 c4) ∷
   rw 34 (q121 c4) ∷
   rw⁻ 30 (q152 c4) ∷
   rw 28 (q150 c4) ∷
   rw 29 (q151 c4) ∷
   rw 30 (q150 c4) ∷
   rw 21 (q121 c4) ∷
   rw 22 (q121 c4) ∷
   rw 23 (q121 c4) ∷
   rw⁻ 20 (q136 c4) ∷
   rw 20 (q140 c4) ∷
   rw 22 (q157 c4) ∷
   re 29 1 (CS03 ∷ []) ∷
   re 35 1 (CS03⁻ ∷ []) ∷
   rw 25 (q158 c4) ∷
   re 26 1 (Sb2-0-3-1 ∷ []) ∷
   re 32 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 21 (q121 c4) ∷
   rw 22 (q121 c4) ∷
   rw 23 (q121 c4) ∷
   rw 24 (q121 c4) ∷
   re 20 5 (Sb2-0-41-3 ∷ []) ∷
   re 20 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 21 (q121 c4) ∷
   rw⁻ 24 (q121 c4) ∷
   rw⁻ 27 (q121 c4) ∷
   rw⁻ 30 (q121 c4) ∷
   rw 20 (q122 c4) ∷
   rw⁻ 21 (q121 c4) ∷
   rw⁻ 24 (q121 c4) ∷
   rw⁻ 27 (q121 c4) ∷
   rw 18 (q144 c4) ∷
   rw 21 (q145 c4) ∷
   rw 24 (q144 c4) ∷
   rw 27 (q145 c4) ∷
   rw 20 (q121 c4) ∷
   rw 21 (q121 c4) ∷
   rw 22 (q121 c4) ∷
   rw⁻ 19 (q122 c4) ∷
   rw 21 (q146 c4) ∷
   re 26 1 (CS03 ∷ []) ∷
   rw 24 (q147 c4) ∷
   re 25 1 (Sb2-0-3-1 ∷ []) ∷
   rw 27 (q146 c4) ∷
   re 32 1 (CS03⁻ ∷ []) ∷
   rw 30 (q148 c4) ∷
   re 31 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 20 (q121 c4) ∷
   rw 21 (q121 c4) ∷
   rw 22 (q121 c4) ∷
   rw 23 (q121 c4) ∷
   re 19 5 (Sb2-0-41-3 ∷ []) ∷
   re 19 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 20 (q121 c4) ∷
   rw⁻ 23 (q121 c4) ∷
   rw⁻ 26 (q121 c4) ∷
   rw⁻ 29 (q121 c4) ∷
   rw 19 (q122 c4) ∷
   rw⁻ 20 (q121 c4) ∷
   rw⁻ 23 (q121 c4) ∷
   rw⁻ 26 (q121 c4) ∷
   rw 17 (q159 c4) ∷
   rw 20 (q160 c4) ∷
   rw 23 (q159 c4) ∷
   rw 26 (q160 c4) ∷
   rw 19 (q121 c4) ∷
   rw 20 (q121 c4) ∷
   rw 21 (q121 c4) ∷
   rw⁻ 18 (q122 c4) ∷
   rw 20 (q161 c4) ∷
   re 25 1 (CS03 ∷ []) ∷
   rw 23 (q162 c4) ∷
   re 24 1 (Sb2-0-3-1 ∷ []) ∷
   rw 26 (q161 c4) ∷
   re 31 1 (CS03⁻ ∷ []) ∷
   rw 29 (q163 c4) ∷
   re 30 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 19 (q121 c4) ∷
   rw 20 (q121 c4) ∷
   rw 21 (q121 c4) ∷
   rw 22 (q121 c4) ∷
   re 18 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 16 (q164 c4) ∷
   rw⁻ 17 (q165 c4) ∷
   rw⁻ 18 (q164 c4) ∷
   rw⁻ 19 (q143 c4) ∷
   re 15 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 19 1 (CS03⁻ ∷ []) ∷
   rw 19 (q166 c4) ∷
   re 20 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 20 (q167 c4) ∷
   re 21 1 (CS03⁻ ∷ []) ∷
   rw 21 (q166 c4) ∷
   re 22 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 18 (q168 c4) ∷
   rw 20 (q169 c4) ∷
   rw 21 (q170 c4) ∷
   rw 22 (q169 c4) ∷
   rw 19 (q171 c4) ∷
   rw 23 (q172 c4) ∷
   rw 24 (q173 c4) ∷
   rw 25 (q172 c4) ∷
   re 24 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 25 (q121 c4) ∷
   rw⁻ 28 (q121 c4) ∷
   rw⁻ 31 (q121 c4) ∷
   rw⁻ 34 (q121 c4) ∷
   rw 24 (q174 c4) ∷
   rw 24 (q175 c4) ∷
   rw 24 (q176 c4) ∷
   rw⁻ 25 (q121 c4) ∷
   rw⁻ 28 (q121 c4) ∷
   rw⁻ 31 (q121 c4) ∷
   rw 22 (q177 c4) ∷
   rw 23 (q178 c4) ∷
   rw 24 (q177 c4) ∷
   rw 21 (q179 c4) ∷
   rw 20 (q177 c4) ∷
   rw 21 (q178 c4) ∷
   rw 22 (q177 c4) ∷
   rw 23 (q180 c4) ∷
   rw 28 (q177 c4) ∷
   rw 29 (q178 c4) ∷
   rw 30 (q177 c4) ∷
   rw 27 (q179 c4) ∷
   rw 26 (q177 c4) ∷
   rw 27 (q178 c4) ∷
   rw 28 (q177 c4) ∷
   rw 29 (q180 c4) ∷
   rw 22 (q121 c4) ∷
   rw 23 (q121 c4) ∷
   rw 24 (q121 c4) ∷
   rw⁻ 21 (q176 c4) ∷
   rw 21 (q181 c4) ∷
   rw 21 (q182 c4) ∷
   re 30 1 (CS03 ∷ []) ∷
   rw 23 (q183 c4) ∷
   re 27 1 (Sb2-0-3-1 ∷ []) ∷
   re 36 1 (CS03⁻ ∷ []) ∷
   rw 32 (q184 c4) ∷
   re 33 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 22 (q121 c4) ∷
   rw 23 (q121 c4) ∷
   rw 24 (q121 c4) ∷
   rw 25 (q121 c4) ∷
   re 21 5 (Sb2-0-41-3 ∷ []) ∷
   re 21 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 22 (q121 c4) ∷
   rw⁻ 25 (q121 c4) ∷
   rw⁻ 28 (q121 c4) ∷
   rw⁻ 31 (q121 c4) ∷
   rw 21 (q122 c4) ∷
   rw⁻ 22 (q121 c4) ∷
   rw⁻ 25 (q121 c4) ∷
   rw⁻ 28 (q121 c4) ∷
   rw⁻ 21 (q185 c4) ∷
   rw⁻ 22 (q121 c4) ∷
   rw⁻ 25 (q121 c4) ∷
   rw 19 (q186 c4) ∷
   rw 24 (q187 c4) ∷
   rw⁻ 25 (q121 c4) ∷
   rw⁻ 28 (q121 c4) ∷
   rw⁻ 31 (q121 c4) ∷
   rw⁻ 34 (q121 c4) ∷
   rw 22 (q188 c4) ∷
   rw 25 (q189 c4) ∷
   rw 28 (q190 c4) ∷
   rw 31 (q189 c4) ∷
   rw 34 (q191 c4) ∷
   rw 24 (q121 c4) ∷
   rw 25 (q121 c4) ∷
   rw 26 (q121 c4) ∷
   rw 27 (q121 c4) ∷
   rw⁻ 23 (q187 c4) ∷
   rw 25 (q192 c4) ∷
   rw 21 (q121 c4) ∷
   rw 22 (q121 c4) ∷
   rw 20 (q185 c4) ∷
   rw 22 (q193 c4) ∷
   rw⁻ 27 (q185 c4) ∷
   rw⁻ 28 (q121 c4) ∷
   rw⁻ 31 (q121 c4) ∷
   rw 25 (q186 c4) ∷
   rw 30 (q187 c4) ∷
   rw⁻ 31 (q121 c4) ∷
   rw⁻ 34 (q121 c4) ∷
   rw⁻ 37 (q121 c4) ∷
   rw⁻ 40 (q121 c4) ∷
   rw 28 (q188 c4) ∷
   rw 31 (q189 c4) ∷
   rw 34 (q190 c4) ∷
   rw 37 (q189 c4) ∷
   rw 40 (q191 c4) ∷
   rw 30 (q121 c4) ∷
   rw 31 (q121 c4) ∷
   rw 32 (q121 c4) ∷
   rw 33 (q121 c4) ∷
   rw⁻ 29 (q187 c4) ∷
   rw 31 (q192 c4) ∷
   rw 27 (q121 c4) ∷
   rw 28 (q121 c4) ∷
   rw 26 (q185 c4) ∷
   rw 28 (q193 c4) ∷
   rw 21 (q121 c4) ∷
   rw 22 (q121 c4) ∷
   rw 23 (q121 c4) ∷
   rw⁻ 20 (q122 c4) ∷
   rw 22 (q194 c4) ∷
   re 27 1 (CS03 ∷ []) ∷
   rw 25 (q195 c4) ∷
   re 26 1 (Sb2-0-3-1 ∷ []) ∷
   rw 28 (q194 c4) ∷
   re 33 1 (CS03⁻ ∷ []) ∷
   rw 31 (q196 c4) ∷
   re 32 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 21 (q121 c4) ∷
   rw 22 (q121 c4) ∷
   rw 23 (q121 c4) ∷
   rw 24 (q121 c4) ∷
   re 20 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 22 (q171 c4) ∷
   rw 18 (q197 c4) ∷
   rw 19 (q198 c4) ∷
   rw 20 (q197 c4) ∷
   rw 21 (q168 c4) ∷
   re 17 1 (CS03 ∷ []) ∷
   rw 17 (q199 c4) ∷
   re 18 1 (Sb2-0-3-1 ∷ []) ∷
   rw 18 (q200 c4) ∷
   re 19 1 (CS03 ∷ []) ∷
   rw 19 (q199 c4) ∷
   re 20 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 16 (q168 c4) ∷
   rw 18 (q169 c4) ∷
   rw 19 (q170 c4) ∷
   rw 20 (q169 c4) ∷
   rw 17 (q171 c4) ∷
   rw 21 (q172 c4) ∷
   rw 22 (q173 c4) ∷
   rw 23 (q172 c4) ∷
   re 22 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 23 (q121 c4) ∷
   rw⁻ 26 (q121 c4) ∷
   rw⁻ 29 (q121 c4) ∷
   rw⁻ 32 (q121 c4) ∷
   rw 22 (q174 c4) ∷
   rw 22 (q175 c4) ∷
   rw 22 (q176 c4) ∷
   rw⁻ 23 (q121 c4) ∷
   rw⁻ 26 (q121 c4) ∷
   rw⁻ 29 (q121 c4) ∷
   rw 20 (q177 c4) ∷
   rw 21 (q178 c4) ∷
   rw 22 (q177 c4) ∷
   rw 19 (q179 c4) ∷
   rw 18 (q177 c4) ∷
   rw 19 (q178 c4) ∷
   rw 20 (q177 c4) ∷
   rw 21 (q180 c4) ∷
   rw 26 (q177 c4) ∷
   rw 27 (q178 c4) ∷
   rw 28 (q177 c4) ∷
   rw 25 (q179 c4) ∷
   rw 24 (q177 c4) ∷
   rw 25 (q178 c4) ∷
   rw 26 (q177 c4) ∷
   rw 27 (q180 c4) ∷
   rw 20 (q121 c4) ∷
   rw 21 (q121 c4) ∷
   rw 22 (q121 c4) ∷
   rw⁻ 19 (q176 c4) ∷
   rw 19 (q181 c4) ∷
   rw 19 (q182 c4) ∷
   re 28 1 (CS03 ∷ []) ∷
   rw 21 (q183 c4) ∷
   re 25 1 (Sb2-0-3-1 ∷ []) ∷
   re 34 1 (CS03⁻ ∷ []) ∷
   rw 30 (q184 c4) ∷
   re 31 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 20 (q121 c4) ∷
   rw 21 (q121 c4) ∷
   rw 22 (q121 c4) ∷
   rw 23 (q121 c4) ∷
   re 19 5 (Sb2-0-41-3 ∷ []) ∷
   re 19 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 20 (q121 c4) ∷
   rw⁻ 23 (q121 c4) ∷
   rw⁻ 26 (q121 c4) ∷
   rw⁻ 29 (q121 c4) ∷
   rw 19 (q122 c4) ∷
   rw⁻ 20 (q121 c4) ∷
   rw⁻ 23 (q121 c4) ∷
   rw⁻ 26 (q121 c4) ∷
   rw⁻ 19 (q185 c4) ∷
   rw⁻ 20 (q121 c4) ∷
   rw⁻ 23 (q121 c4) ∷
   rw 17 (q186 c4) ∷
   rw 22 (q187 c4) ∷
   rw⁻ 23 (q121 c4) ∷
   rw⁻ 26 (q121 c4) ∷
   rw⁻ 29 (q121 c4) ∷
   rw⁻ 32 (q121 c4) ∷
   rw 20 (q188 c4) ∷
   rw 23 (q189 c4) ∷
   rw 26 (q190 c4) ∷
   rw 29 (q189 c4) ∷
   rw 32 (q191 c4) ∷
   rw 22 (q121 c4) ∷
   rw 23 (q121 c4) ∷
   rw 24 (q121 c4) ∷
   rw 25 (q121 c4) ∷
   rw⁻ 21 (q187 c4) ∷
   rw 23 (q192 c4) ∷
   rw 19 (q121 c4) ∷
   rw 20 (q121 c4) ∷
   rw 18 (q185 c4) ∷
   rw 20 (q193 c4) ∷
   rw⁻ 25 (q185 c4) ∷ []) Eq.refl

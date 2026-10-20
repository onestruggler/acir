{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D171 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0008 ; wl0017 ; wl0030 ; wl0031 ; wl0034 ; wl0076 ; wl0078 ; wl0079 ; wl0084 ; wl0091 ; wl0111 ; wl0113 ; wl0127 ; wl0128 ; wl0132 ; wl0136 ; wl0140 ; wl0144 ; wl0147 ; wl0160 ; wl0162 ; wl0163 ; wl0164 ; wl0189 ; wl0230 ; wl0283 ; wl0332 ; wl0347 ; wl0351 ; wl0372 ; wl0373 ; wl0504 ; wl0516 ; wl0609 ; wl0612 ; wl0613 ; wl0625 ; wl0626 ; wl0637 ; wl0638 ; wl0639 ; wl0640 ; wl0641 ; wl0642 ; wl0643 ; wl0644 ; wl0645 ; wl0646 ; wl0647 ; wl0648 ; wl0649 ; wl0650 ; wl0651 ; wl0652 ; wl0653 ; wl0654 ; wl0655 ; wl0656 ; wl0657 ; wl0658 ; wl0659 ; wl0660 ; wp0267 ; wp0286 ; wp0287 ; wp0288 ; wp0289 ; wp0290 ; wp0291 ; wp0292 ; wp0293 ; wp0294 ; wp0295 ; wp0296 ; wp0297 ; wp0298 ; wp0299)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-CSd12-beta ; lem-T312-beta-at1221 ; lem-beta-inv ; lem-beta-inv-at243243 ; lem-c124-beta-at0310213442 ; lem-sym12-at0214203143 ; lem-sym12-at1221 ; lem-sym23 ; lem-sym23-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-CKbox ; lem-CX23-beta-at243243 ; lem-KB-form ; lem-SB2 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 ; lem-c124-beta-at2332 ; lem-sym12-at021021 ; lem-sym12-at0210243143 ; lem-sym23-at021021 ; lem-sym23-at0310213442 ; lem-sym23-at0310243142 ; lem-sym23-at122331 ; lem-sym23-at13213442 ; lem-sym23-at2332 ; lem-sym34-at122331 ; lem-sym34-at2332 ; lem-sym34-at233442)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F0-at0214203143 ; lem-SBsym-at0113203442 ; lem-T312-beta-at3443 ; lem-X1-beta-at0214203143 ; lem-auto-K0-∣-BOX⟨0·1234⟩ ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41-at2332 ; lem-sym12-at0210233441 ; lem-sym23-at02102331 ; lem-sym34-at02102331)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym12-at02132031 ; lem-sym12-at02132130 ; lem-sym12-at022330 ; lem-sym23-at0220 ; lem-sym23-at022330)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-CS20-beta-c-at011220 ; lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413203142 ; lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 ; lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04203243 ; lem-auto-Sd0-∣-BOX⟨1·2034⟩ ; lem-beta-T-at011220 ; lem-sym23-at233442 ; lem-sym23-at2442 ; lem-sym34-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-sym23-at0213203441 ; lem-sym23-at0213243041 ; lem-sym23-at0310243241 ; lem-sym23-at03103441 ; lem-sym34-at0213203441)
open import Examples.Groups.Clifford+CS.Five.D.D161 using (lem-SB2-at011220 ; lem-sym12-at12233441 ; lem-sym12-at1331)
open import Examples.Groups.Clifford+CS.Five.D.D165 using (lem-SB2-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D168 using (lem-boxify-10)
open import Examples.Groups.Clifford+CS.Five.D.D169 using (lem-boxify-11 ; lem-boxify-12 ; lem-boxify-13)
open import Examples.Groups.Clifford+CS.Five.D.D170 using (lem-F1-toff-ccz-nf-of-rhs ; lem-T312-beta-at0213243041 ; lem-TW-at02132130 ; lem-TW-at0310243241 ; lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0214⟩-at021021 ; lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03122130 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at03122130 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at13243241 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at021021 ; lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at03122130 ; lem-auto-CCZ012-∣-TOFF342 ; lem-boxify-14 ; lem-sym12-at0220 ; lem-sym12-at031031 ; lem-sym12-at0312203441 ; lem-sym23-at03122031 ; lem-sym23-at03122130 ; lem-sym23-at13243241 ; lem-sym34-at03103441 ; lem-sym34-at03122031 ; lem-sym34-at133441)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-1-CCZ024 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-BOX⟨0·3412⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF034 ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-BOX⟨0·1423⟩ ; lem-nat-1-CCZ014 ; lem-nat-2-BOX⟨0·2413⟩ ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-3-BOX⟨0·1324⟩ ; lem-nat-3-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ014 ; lem-nat-1-BOX⟨0·1243⟩ ; lem-nat-2-BOX⟨0·2143⟩ ; lem-nat-2-TOFF413)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-1-BOX⟨0·1234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0124⟩ ; lem-nat-2-BOX⟨3·0412⟩)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨0·2134⟩ ; lem-nat-0-BOX⟨1·2034⟩ ; lem-nat-0-BOX⟨3·1024⟩ ; lem-nat-1-BOX⟨0·2143⟩ ; lem-nat-1-CS01 ; lem-nat-1-CS02 ; lem-nat-2-BOX⟨0·3142⟩ ; lem-nat-2-CSd12 ; lem-nat-2-CSd13)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-CS04 ; lem-nat-0-CS14 ; lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-0-TOFF134 ; lem-nat-1-CS04 ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-2-BOX⟨0·1432⟩ ; lem-nat-2-CS02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-TOFF034 ; lem-nat-1-TOFF034 ; lem-nat-2-CS04 ; lem-nat-3-CS04)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-2-BOX⟨0·1423⟩ ; lem-nat-2-CS03 ; lem-nat-3-CS03)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-SBOX⟨0·2·43·1⟩ ; lem-nat-0-SBOX⟨1·2·43·0⟩ ; lem-nat-0-SBOX⟨2·3·04·1⟩ ; lem-nat-0-SBOX⟨2·3·14·0⟩ ; lem-nat-1-BOX⟨0·1432⟩ ; lem-nat-1-SBOX⟨0·1·43·2⟩ ; lem-nat-1-SBOX⟨0·2·43·1⟩ ; lem-nat-1-SBOX⟨1·3·24·0⟩ ; lem-nat-2-SBOX⟨0·1·42·3⟩ ; lem-nat-2-SBOX⟨0·1·43·2⟩ ; lem-nat-3-SBOX⟨1·2·34·0⟩ ; lem-nat-3-SBOX⟨1·2·43·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-SBOX⟨2·3·14·0⟩ ; lem-nat-2-SBOX⟨1·2·34·0⟩ ; lem-nat-2-SBOX⟨1·3·24·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-SBOX⟨0·2·13·4⟩ ; lem-nat-0-SBOX⟨1·2·03·4⟩ ; lem-nat-1-SBOX⟨0·1·23·4⟩ ; lem-nat-1-SBOX⟨0·2·13·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-BOX⟨0·3241⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-1-BOX⟨0·3142⟩ ; lem-nat-1-BOX⟨3·2014⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-BOX⟨3·2104⟩ ; lem-nat-0-CK40 ; lem-nat-0-CK41 ; lem-nat-0-SBOX⟨0·3·14·2⟩ ; lem-nat-0-SBOX⟨1·3·24·0⟩ ; lem-nat-1-BOX⟨0·3412⟩ ; lem-nat-1-BOX⟨0·3421⟩ ; lem-nat-1-CK10 ; lem-nat-1-CK20 ; lem-nat-1-CK40 ; lem-nat-1-SBOX⟨0·3·24·1⟩ ; lem-nat-2-BOX⟨1·2043⟩ ; lem-nat-2-BOX⟨1·3042⟩ ; lem-nat-2-CK20 ; lem-nat-2-CK30 ; lem-nat-2-CK40 ; lem-nat-2-SBOX⟨0·3·24·1⟩ ; lem-nat-3-BOX⟨1·2034⟩ ; lem-nat-3-BOX⟨1·2043⟩ ; lem-nat-3-CK30 ; lem-nat-3-CK40)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Sw12 ∷ Bx0-3241 ∷ []) (Bx0-3142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3241⟩ (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx0-3142 ∷ []) (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Sw12 ∷ Bx0-3412 ∷ []) (Bx0-3421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3412⟩ (lit c4))

-- sym23 @133441: 5 steps
lem-sym23-at133441 : Ws → ⟪ (Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-sym23-at133441 c4 = derive (Bx0-3241 ∷ []) (Bx0-3421 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 0 (q4 c4) ∷
   rw 1 (q1 c4) ∷ []) Eq.refl

private
  q5 : Ws → Eqn
  q5 c4 = eqn (Sw12 ∷ Bx0-2413 ∷ []) (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl0084 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (Bx0-1423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at243243 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (Sw12 ∷ Bx0-1423 ∷ []) (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4))

-- auto BOX(0;1234) | CCZ342 @12243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at12243143 : Ws → ⟪ (Bx0-2413 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-2413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at12243143 c4 = derive (Bx0-2413 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-2413 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q5 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 1 (q7 c4) ∷
   rw⁻ 0 (q8 c4) ∷
   rw 1 (q9 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q10 : Ws → Eqn
  q10 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw23 ∷ Bx0-3412 ∷ []) (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw23 ∷ CCZ124 ∷ []) (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (Bx0-2413 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-2413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at12243143 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Sw23 ∷ CCZ134 ∷ []) (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (Sw23 ∷ Bx0-2413 ∷ []) (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ (lit c4))

-- auto BOX(0;1234) | CCZ342 @13243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at13243142 : Ws → ⟪ (Bx0-3412 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-3412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at13243142 c4 = derive (Bx0-3412 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-3412 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q11 c4) ∷
   rw 2 (q12 c4) ∷
   rw 1 (q13 c4) ∷
   rw 0 (q14 c4) ∷
   rw 1 (q15 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q16 : Ws → Eqn
  q16 c4 = eqn (Sw12 ∷ Bx0-3421 ∷ []) (Bx0-3412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3421⟩ (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) (wl0078 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Bx0-3412 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-3412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at13243142 c4)

-- auto BOX(0;1234) | CCZ342 @13243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at13243241 : Ws → ⟪ (Bx0-3421 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-3421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at13243241 c4 = derive (Bx0-3421 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-3421 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q16 c4) ∷
   rw⁻ 2 (q17 c4) ∷
   rw 1 (q18 c4) ∷
   rw⁻ 0 (q17 c4) ∷
   rw 1 (q4 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw12 ∷ Toff024 ∷ []) (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (Bx0-1423 ∷ Toff014 ∷ []) (Toff014 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at243243 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (Sw12 ∷ Toff014 ∷ []) (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 (lit c4))

-- auto BOX(0;1234) | TOFF012 @12243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at12243143 : Ws → ⟪ (Bx0-2413 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Bx0-2413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at12243143 c4 = derive (Bx0-2413 ∷ Toff024 ∷ []) (Toff024 ∷ Bx0-2413 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q19 c4) ∷
   rw 1 (q20 c4) ∷
   rw 0 (q21 c4) ∷
   rw 1 (q9 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q22 : Ws → Eqn
  q22 c4 = eqn (Sw23 ∷ Toff034 ∷ []) (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Bx0-2413 ∷ Toff024 ∷ []) (Toff024 ∷ Bx0-2413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at12243143 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (Sw23 ∷ Toff024 ∷ []) (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 (lit c4))

-- auto BOX(0;1234) | TOFF012 @13243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at13243142 : Ws → ⟪ (Bx0-3412 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Bx0-3412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at13243142 c4 = derive (Bx0-3412 ∷ Toff034 ∷ []) (Toff034 ∷ Bx0-3412 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q11 c4) ∷
   rw 2 (q22 c4) ∷
   rw 1 (q23 c4) ∷
   rw 0 (q24 c4) ∷
   rw 1 (q15 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q25 : Ws → Eqn
  q25 c4 = eqn (Sw12 ∷ Toff034 ∷ []) (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (Bx0-3412 ∷ Toff034 ∷ []) (Toff034 ∷ Bx0-3412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at13243142 c4)

-- auto BOX(0;1234) | TOFF012 @13243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at13243241 : Ws → ⟪ (Bx0-3421 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Bx0-3421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at13243241 c4 = derive (Bx0-3421 ∷ Toff034 ∷ []) (Toff034 ∷ Bx0-3421 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q16 c4) ∷
   rw 2 (q25 c4) ∷
   rw 1 (q26 c4) ∷
   rw 0 (q25 c4) ∷
   rw 1 (q4 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = eqn (Bx0-1423 ∷ Bx0-1423 ∷ []) [] (lem-beta-inv-at243243 c4)

-- beta-inv @12243143: 5 steps
lem-beta-inv-at12243143 : Ws → ⟪ (Bx0-2413 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at12243143 c4 = derive (Bx0-2413 ∷ Bx0-2413 ∷ []) []
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q5 c4) ∷
   rw 1 (q27 c4) ∷
   rw 0 (q1 c4) ∷ []) Eq.refl

private
  q28 : Ws → Eqn
  q28 c4 = eqn (Bx0-2413 ∷ Bx0-2413 ∷ []) [] (lem-beta-inv-at12243143 c4)

-- beta-inv @13243142: 5 steps
lem-beta-inv-at13243142 : Ws → ⟪ (Bx0-3412 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at13243142 c4 = derive (Bx0-3412 ∷ Bx0-3412 ∷ []) []
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q11 c4) ∷
   rw 2 (q11 c4) ∷
   rw 1 (q28 c4) ∷
   rw 0 (q10 c4) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = eqn (Bx0-3412 ∷ Bx0-3412 ∷ []) [] (lem-beta-inv-at13243142 c4)

-- beta-inv @13243241: 5 steps
lem-beta-inv-at13243241 : Ws → ⟪ (Bx0-3421 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at13243241 c4 = derive (Bx0-3421 ∷ Bx0-3421 ∷ []) []
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q16 c4) ∷
   rw 2 (q16 c4) ∷
   rw 1 (q29 c4) ∷
   rw 0 (q1 c4) ∷ []) Eq.refl

private
  q30 : Ws → Eqn
  q30 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (Sw01 ∷ Bx1-0234 ∷ []) (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (Bx0-1234 ∷ Bx0-1234 ∷ []) [] (lem-beta-inv c4)

-- beta-inv @0110: 5 steps
lem-beta-inv-at0110 : Ws → ⟪ (Bx1-0234 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at0110 c4 = derive (Bx1-0234 ∷ Bx1-0234 ∷ []) []
  (rw⁻ 0 (q30 c4) ∷
   rw 1 (q31 c4) ∷
   rw 2 (q31 c4) ∷
   rw 1 (q32 c4) ∷
   rw 0 (q30 c4) ∷ []) Eq.refl

private
  q33 : Ws → Eqn
  q33 c4 = eqn (Sw12 ∷ Bx2-0134 ∷ []) (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (Bx1-0234 ∷ Bx1-0234 ∷ []) [] (lem-beta-inv-at0110 c4)

-- beta-inv @021021: 5 steps
lem-beta-inv-at021021 : Ws → ⟪ (Bx2-0134 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at021021 c4 = derive (Bx2-0134 ∷ Bx2-0134 ∷ []) []
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q33 c4) ∷
   rw 2 (q33 c4) ∷
   rw 1 (q34 c4) ∷
   rw 0 (q1 c4) ∷ []) Eq.refl

private
  q35 : Ws → Eqn
  q35 c4 = eqn (Sw23 ∷ Bx3-0124 ∷ []) (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (Bx2-0134 ∷ Bx2-0134 ∷ []) [] (lem-beta-inv-at021021 c4)

-- beta-inv @03102132: 5 steps
lem-beta-inv-at03102132 : Ws → ⟪ (Bx3-0124 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at03102132 c4 = derive (Bx3-0124 ∷ Bx3-0124 ∷ []) []
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q35 c4) ∷
   rw 2 (q35 c4) ∷
   rw 1 (q36 c4) ∷
   rw 0 (q10 c4) ∷ []) Eq.refl

private
  q37 : Ws → Eqn
  q37 c4 = eqn (Sw01 ∷ Bx3-1024 ∷ []) (Bx3-0124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1024⟩ (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (Bx3-0124 ∷ Bx3-0124 ∷ []) [] (lem-beta-inv-at03102132 c4)

-- beta-inv @032032: 5 steps
lem-beta-inv-at032032 : Ws → ⟪ (Bx3-1024 ∷ Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at032032 c4 = derive (Bx3-1024 ∷ Bx3-1024 ∷ []) []
  (rw⁻ 0 (q30 c4) ∷
   rw 1 (q37 c4) ∷
   rw 2 (q37 c4) ∷
   rw 1 (q38 c4) ∷
   rw 0 (q30 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = eqn (Sw12 ∷ Bx3-2014 ∷ []) (Bx3-1024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2014⟩ (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (Bx3-1024 ∷ Bx3-1024 ∷ []) [] (lem-beta-inv-at032032 c4)

-- beta-inv @03122031: 5 steps
lem-beta-inv-at03122031 : Ws → ⟪ (Bx3-2014 ∷ Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at03122031 c4 = derive (Bx3-2014 ∷ Bx3-2014 ∷ []) []
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q39 c4) ∷
   rw 2 (q39 c4) ∷
   rw 1 (q40 c4) ∷
   rw 0 (q1 c4) ∷ []) Eq.refl

private
  q41 : Ws → Eqn
  q41 c4 = eqn (Sw01 ∷ Bx3-2104 ∷ []) (Bx3-2014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2104⟩ (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (Bx3-2014 ∷ Bx3-2014 ∷ []) [] (lem-beta-inv-at03122031 c4)

-- beta-inv @03122130: 5 steps
lem-beta-inv-at03122130 : Ws → ⟪ (Bx3-2104 ∷ Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at03122130 c4 = derive (Bx3-2104 ∷ Bx3-2104 ∷ []) []
  (rw⁻ 0 (q30 c4) ∷
   rw 1 (q41 c4) ∷
   rw 2 (q41 c4) ∷
   rw 1 (q42 c4) ∷
   rw 0 (q30 c4) ∷ []) Eq.refl

private
  q43 : Ws → Eqn
  q43 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) (wl0127 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ012 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF342 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) (wl0144 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4))

-- auto CCZ012 | TOFF342 @2332: 7 steps
lem-auto-CCZ012-∣-TOFF342-at2332 : Ws → ⟪ (CCZ013 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at2332 c4 = derive (CCZ013 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q43 c4) ∷
   rw 2 (q44 c4) ∷
   rw 1 (q45 c4) ∷
   rw 0 (q46 c4) ∷
   rw 1 (q47 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q48 : Ws → Eqn
  q48 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (Sw34 ∷ CCZ014 ∷ []) (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) (wl0128 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CCZ013 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at2332 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (Sw34 ∷ CCZ013 ∷ []) (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 (lit c4))

-- auto CCZ012 | TOFF342 @243243: 7 steps
lem-auto-CCZ012-∣-TOFF342-at243243 : Ws → ⟪ (CCZ014 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at243243 c4 = derive (CCZ014 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q48 c4) ∷
   rw 1 (q49 c4) ∷
   rw 2 (q50 c4) ∷
   rw 1 (q51 c4) ∷
   rw 0 (q50 c4) ∷
   rw 1 (q52 c4) ∷
   rw 2 (q48 c4) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = eqn (Sw01 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (Sw01 ∷ Toff234 ∷ []) (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff))
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ014 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at243243 c4)

-- auto CCZ012 | TOFF342 @0110243243: 7 steps
lem-auto-CCZ012-∣-TOFF342-at0110243243 : Ws → ⟪ (CCZ014 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at0110243243 c4 = derive (CCZ014 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q30 c4) ∷
   rw 1 (q53 c4) ∷
   rw 2 (q54 c4) ∷
   rw 1 (q55 c4) ∷
   rw 0 (q54 c4) ∷
   rw 1 (q53 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

private
  q56 : Ws → Eqn
  q56 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) (wl0136 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (CCZ014 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at0110243243 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) (wl0140 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4))

-- auto CCZ012 | TOFF342 @0210243143: 7 steps
lem-auto-CCZ012-∣-TOFF342-at0210243143 : Ws → ⟪ (CCZ024 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at0210243143 c4 = derive (CCZ024 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q57 c4) ∷
   rw 1 (q58 c4) ∷
   rw 0 (q59 c4) ∷
   rw 1 (q60 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q61 : Ws → Eqn
  q61 c4 = eqn (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (Sw01 ∷ Toff034 ∷ []) (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (CCZ024 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at0210243143 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (Sw01 ∷ Toff134 ∷ []) (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4))

-- auto CCZ012 | TOFF342 @02243043: 7 steps
lem-auto-CCZ012-∣-TOFF342-at02243043 : Ws → ⟪ (CCZ124 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ124 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at02243043 c4 = derive (CCZ124 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q30 c4) ∷
   rw 1 (q61 c4) ∷
   rw 2 (q62 c4) ∷
   rw 1 (q63 c4) ∷
   rw 0 (q64 c4) ∷
   rw 1 (q65 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

-- auto CCZ012 | TOFF342 @12243143: 7 steps
lem-auto-CCZ012-∣-TOFF342-at12243143 : Ws → ⟪ (CCZ024 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at12243143 c4 = derive (CCZ024 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q57 c4) ∷
   rw 1 (q55 c4) ∷
   rw 0 (q59 c4) ∷
   rw 1 (q60 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ024 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at12243143 c4)

-- auto CCZ012 | TOFF342 @0112243043: 7 steps
lem-auto-CCZ012-∣-TOFF342-at0112243043 : Ws → ⟪ (CCZ124 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ124 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at0112243043 c4 = derive (CCZ124 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q30 c4) ∷
   rw 1 (q61 c4) ∷
   rw 2 (q62 c4) ∷
   rw 1 (q66 c4) ∷
   rw 0 (q64 c4) ∷
   rw 1 (q65 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

private
  q67 : Ws → Eqn
  q67 c4 = eqn (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (CCZ014 ∷ []) (lem-SB2 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (CCZ124 ∷ []) (lem-SB2-at011220 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CCZ234 ∷ []) (lem-SB2-at02132031 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Toff104 ∷ []) (wp0267 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ []) (wl0612 (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ []) (wl0613 (lit c4))
  q73 : Ws → Eqn
  q73 c4 = eqn (CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ []) (wl0625 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) (Toff234 ∷ []) (wl0626 (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-0124 ∷ []) (lem-boxify-10 c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-0124 ∷ []) (lem-boxify-11 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ []) (Bx3-0124 ∷ []) (lem-boxify-12 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (Toff324 ∷ Toff234 ∷ Bx3-0124 ∷ Toff234 ∷ Toff324 ∷ []) (Bx2-0134 ∷ []) (lem-boxify-13 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-0124 ∷ []) (lem-boxify-14 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (CK40 ∷ Bx3-0124 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ []) (lem-CKbox c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) (lem-KB-form c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (Toff312 ∷ Toff312 ∷ []) [] (wl0230 (lit c4))
  q83 : Ws → Eqn
  q83 c4 = eqn (Toff312 ∷ []) (Toff312 ∷ []) (wl0609 (lit c4))
  q84 : Ws → Eqn
  q84 c4 = eqn (Bx2-0134 ∷ []) (Bx2-1034 ∷ []) (lem-sym12-at021021 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (Bx2-1034 ∷ []) (Bx2-1304 ∷ []) (lem-sym23-at0220 c4)
  q86 : Ws → Eqn
  q86 c4 = eqn (Bx2-1304 ∷ []) (Bx2-3104 ∷ []) (lem-sym12-at022330 c4)
  q87 : Ws → Eqn
  q87 c4 = eqn (Toff312 ∷ Bx2-3104 ∷ Toff312 ∷ []) (Bx2-3104 ∷ Bx3-2104 ∷ []) (lem-TW-at02132130 c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (Bx2-3104 ∷ []) (Bx2-1304 ∷ []) (lem-sym12-at02132130 c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (Bx2-1304 ∷ []) (Bx2-1034 ∷ []) (lem-sym23-at022330 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (Bx2-1034 ∷ []) (Bx2-0134 ∷ []) (lem-sym12-at0220 c4)
  q91 : Ws → Eqn
  q91 c4 = eqn (Bx2-0134 ∷ Bx3-2104 ∷ []) (Bx3-2104 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0214⟩-at021021 c4)
  q92 : Ws → Eqn
  q92 c4 = eqn (Toff034 ∷ Toff034 ∷ []) [] (wp0286 c4)
  q93 : Ws → Eqn
  q93 c4 = eqn (Bx2-0134 ∷ []) (Bx2-0314 ∷ []) (lem-sym23-at021021 c4)
  q94 : Ws → Eqn
  q94 c4 = eqn (Bx2-0314 ∷ []) (Bx2-0341 ∷ []) (lem-sym34-at02102331 c4)
  q95 : Ws → Eqn
  q95 c4 = eqn (Bx2-0341 ∷ []) (Bx2-3041 ∷ []) (lem-sym12-at0210233441 c4)
  q96 : Ws → Eqn
  q96 c4 = eqn (Bx2-3041 ∷ []) (Bx2-3401 ∷ []) (lem-sym23-at0213203441 c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (Toff034 ∷ Bx2-3401 ∷ Toff034 ∷ []) (Bx2-3401 ∷ CCZ134 ∷ []) (lem-T312-beta-at0213243041 c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (Bx2-3401 ∷ []) (Bx2-3041 ∷ []) (lem-sym23-at0213243041 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (Bx2-3041 ∷ []) (Bx2-3014 ∷ []) (lem-sym34-at0213203441 c4)
  q100 : Ws → Eqn
  q100 c4 = eqn (Bx2-3014 ∷ []) (Bx2-0314 ∷ []) (lem-sym12-at02132031 c4)
  q101 : Ws → Eqn
  q101 c4 = eqn (Bx2-0314 ∷ []) (Bx2-0134 ∷ []) (lem-sym23-at02102331 c4)
  q102 : Ws → Eqn
  q102 c4 = eqn (Bx2-0134 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at021021 c4)
  q103 : Ws → Eqn
  q103 c4 = eqn (Bx3-2104 ∷ []) (Bx3-2014 ∷ []) (lem-sym23-at03122130 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (Bx3-2014 ∷ []) (Bx3-2041 ∷ []) (lem-sym34-at03122031 c4)
  q105 : Ws → Eqn
  q105 c4 = eqn (Bx3-2041 ∷ []) (Bx3-0241 ∷ []) (lem-sym12-at0312203441 c4)
  q106 : Ws → Eqn
  q106 c4 = eqn (Bx3-0241 ∷ []) (Bx3-0421 ∷ []) (lem-sym23-at03103441 c4)
  q107 : Ws → Eqn
  q107 c4 = eqn (Toff034 ∷ Bx3-0421 ∷ Toff034 ∷ []) (Bx3-0421 ∷ Bx0-3421 ∷ []) (lem-TW-at0310243241 c4)
  q108 : Ws → Eqn
  q108 c4 = eqn (Bx3-0421 ∷ []) (Bx3-0241 ∷ []) (lem-sym23-at0310243241 c4)
  q109 : Ws → Eqn
  q109 c4 = eqn (Bx3-0241 ∷ []) (Bx3-0214 ∷ []) (lem-sym34-at03103441 c4)
  q110 : Ws → Eqn
  q110 c4 = eqn (Bx3-0214 ∷ []) (Bx3-2014 ∷ []) (lem-sym12-at031031 c4)
  q111 : Ws → Eqn
  q111 c4 = eqn (Bx3-2014 ∷ []) (Bx3-2104 ∷ []) (lem-sym23-at03122031 c4)
  q112 : Ws → Eqn
  q112 c4 = eqn (Bx3-2104 ∷ Bx0-3421 ∷ []) (Bx0-3421 ∷ Bx3-2104 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03122130 c4)
  q113 : Ws → Eqn
  q113 c4 = eqn (Bx3-2104 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx3-2104 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at03122130 c4)
  q114 : Ws → Eqn
  q114 c4 = eqn (Bx0-3421 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-3421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at13243241 c4)
  q115 : Ws → Eqn
  q115 c4 = eqn (Bx3-2104 ∷ Toff312 ∷ []) (Toff312 ∷ Bx3-2104 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at03122130 c4)
  q116 : Ws → Eqn
  q116 c4 = eqn (Bx0-3421 ∷ []) (Bx0-3241 ∷ []) (lem-sym23-at13243241 c4)
  q117 : Ws → Eqn
  q117 c4 = eqn (Bx0-3241 ∷ []) (Bx0-3214 ∷ []) (lem-sym34-at133441 c4)
  q118 : Ws → Eqn
  q118 c4 = eqn (Bx0-3214 ∷ []) (Bx0-2314 ∷ []) (lem-sym12-at1331 c4)
  q119 : Ws → Eqn
  q119 c4 = eqn (Bx0-2314 ∷ []) (Bx0-2134 ∷ []) (lem-sym23-at122331 c4)
  q120 : Ws → Eqn
  q120 c4 = eqn (Toff312 ∷ Bx0-2134 ∷ Toff312 ∷ []) (Bx0-2134 ∷ CCZ124 ∷ []) (lem-T312-beta-at1221 c4)
  q121 : Ws → Eqn
  q121 c4 = eqn (Bx0-2134 ∷ []) (Bx0-2314 ∷ []) (lem-sym23-at1221 c4)
  q122 : Ws → Eqn
  q122 c4 = eqn (Bx0-2314 ∷ []) (Bx0-2341 ∷ []) (lem-sym34-at122331 c4)
  q123 : Ws → Eqn
  q123 c4 = eqn (Bx0-2341 ∷ []) (Bx0-3241 ∷ []) (lem-sym12-at12233441 c4)
  q124 : Ws → Eqn
  q124 c4 = eqn (Bx0-3241 ∷ []) (Bx0-3421 ∷ []) (lem-sym23-at133441 c4)
  q125 : Ws → Eqn
  q125 c4 = eqn (Bx0-3421 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-3421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at13243241 c4)
  q126 : Ws → Eqn
  q126 c4 = eqn (Bx0-3421 ∷ Toff034 ∷ []) (Toff034 ∷ Bx0-3421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at13243241 c4)
  q127 : Ws → Eqn
  q127 c4 = eqn (Bx0-3421 ∷ Bx0-3421 ∷ []) [] (lem-beta-inv-at13243241 c4)
  q128 : Ws → Eqn
  q128 c4 = eqn (Bx3-2104 ∷ Bx3-2104 ∷ []) [] (lem-beta-inv-at03122130 c4)
  q129 : Ws → Eqn
  q129 c4 = eqn (Bx0-2134 ∷ []) (Bx0-1234 ∷ []) (lem-sym12-at1221 c4)
  q130 : Ws → Eqn
  q130 c4 = eqn (CCZ124 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ124 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at02243043 c4)
  q131 : Ws → Eqn
  q131 c4 = eqn (CCZ134 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0637 (lit c4))
  q132 : Ws → Eqn
  q132 c4 = eqn (CCZ134 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ134 ∷ []) (wp0287 c4)
  q133 : Ws → Eqn
  q133 c4 = eqn (CCZ124 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ124 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at0112243043 c4)
  q134 : Ws → Eqn
  q134 c4 = eqn (K0⁻ ∷ K0 ∷ []) [] (wl0189 (lit c4))
  q135 : Ws → Eqn
  q135 c4 = eqn (K0 ∷ K0⁻ ∷ []) [] (wl0638 (lit c4))
  q136 : Ws → Eqn
  q136 c4 = eqn (CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ []) [] (wl0639 (lit c4))
  q137 : Ws → Eqn
  q137 c4 = eqn (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (Bx0-1234 ∷ Bx2-0134 ∷ []) (lem-F1-toff-ccz-nf-of-rhs c4)

-- F1 toff-ccz: 190 steps
lem-F1-toff-ccz : Ws → ⟪ (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-F1-toff-ccz c4 = derive (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  (rw 3 (q67 c4) ∷
   rw 6 (q68 c4) ∷
   rw 9 (q67 c4) ∷
   rw 13 (q68 c4) ∷
   rw 17 (q68 c4) ∷
   rw 21 (q68 c4) ∷
   rw 26 (q68 c4) ∷
   rw 30 (q68 c4) ∷
   rw 34 (q68 c4) ∷
   rw 40 (q69 c4) ∷
   rw 44 (q69 c4) ∷
   rw 48 (q69 c4) ∷
   rw 53 (q67 c4) ∷
   rw 56 (q68 c4) ∷
   rw 59 (q67 c4) ∷
   rw 63 (q68 c4) ∷
   rw 67 (q68 c4) ∷
   rw 71 (q68 c4) ∷
   rw 76 (q68 c4) ∷
   rw 80 (q68 c4) ∷
   rw 84 (q68 c4) ∷
   rw 88 (q69 c4) ∷
   rw 92 (q69 c4) ∷
   rw 96 (q69 c4) ∷
   rw 102 (q67 c4) ∷
   rw 105 (q68 c4) ∷
   rw 108 (q67 c4) ∷
   rw 112 (q68 c4) ∷
   rw 116 (q68 c4) ∷
   rw 120 (q68 c4) ∷
   rw 125 (q68 c4) ∷
   rw 129 (q68 c4) ∷
   rw 133 (q68 c4) ∷
   rw 2 (q70 c4) ∷
   rw 5 (q70 c4) ∷
   rw 6 (q71 c4) ∷
   rw 7 (q72 c4) ∷
   rw 8 (q71 c4) ∷
   rw 10 (q71 c4) ∷
   rw 11 (q72 c4) ∷
   rw 12 (q71 c4) ∷
   rw 15 (q73 c4) ∷
   rw 16 (q74 c4) ∷
   rw 17 (q73 c4) ∷
   rw 19 (q70 c4) ∷
   rw 22 (q70 c4) ∷
   rw 23 (q71 c4) ∷
   rw 24 (q72 c4) ∷
   rw 25 (q71 c4) ∷
   rw 27 (q71 c4) ∷
   rw 28 (q72 c4) ∷
   rw 29 (q71 c4) ∷
   rw 30 (q73 c4) ∷
   rw 31 (q74 c4) ∷
   rw 32 (q73 c4) ∷
   rw 35 (q70 c4) ∷
   rw 38 (q70 c4) ∷
   rw 39 (q71 c4) ∷
   rw 40 (q72 c4) ∷
   rw 41 (q71 c4) ∷
   rw 43 (q71 c4) ∷
   rw 44 (q72 c4) ∷
   rw 45 (q71 c4) ∷
   rw 1 (q75 c4) ∷
   rw 7 (q76 c4) ∷
   rw 6 (q77 c4) ∷
   rw 4 (q78 c4) ∷
   rw 6 (q79 c4) ∷
   rw 0 (q80 c4) ∷
   rw 0 (q81 c4) ∷
   rw 5 (q80 c4) ∷
   rw 5 (q81 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   rw 5 (q83 c4) ∷
   rw 7 (q83 c4) ∷
   rw 6 (q84 c4) ∷
   rw 6 (q85 c4) ∷
   rw 6 (q86 c4) ∷
   rw 5 (q87 c4) ∷
   rw 5 (q88 c4) ∷
   rw 5 (q89 c4) ∷
   rw 5 (q90 c4) ∷
   rw 5 (q91 c4) ∷
   rw⁻ 6 (q92 c4) ∷
   rw 8 (q93 c4) ∷
   rw 8 (q94 c4) ∷
   rw 8 (q95 c4) ∷
   rw 8 (q96 c4) ∷
   rw 7 (q97 c4) ∷
   rw 7 (q98 c4) ∷
   rw 7 (q99 c4) ∷
   rw 7 (q100 c4) ∷
   rw 7 (q101 c4) ∷
   rw 7 (q102 c4) ∷
   rw⁻ 8 (q82 c4) ∷
   rw 9 (q83 c4) ∷
   rw 11 (q83 c4) ∷
   rw 10 (q84 c4) ∷
   rw 10 (q85 c4) ∷
   rw 10 (q86 c4) ∷
   rw 9 (q87 c4) ∷
   rw 9 (q88 c4) ∷
   rw 9 (q89 c4) ∷
   rw 9 (q90 c4) ∷
   rw 9 (q91 c4) ∷
   rw⁻ 10 (q92 c4) ∷
   rw 12 (q93 c4) ∷
   rw 12 (q94 c4) ∷
   rw 12 (q95 c4) ∷
   rw 12 (q96 c4) ∷
   rw 11 (q97 c4) ∷
   rw 11 (q98 c4) ∷
   rw 11 (q99 c4) ∷
   rw 11 (q100 c4) ∷
   rw 11 (q101 c4) ∷
   rw 11 (q102 c4) ∷
   rw⁻ 9 (q92 c4) ∷
   rw 11 (q103 c4) ∷
   rw 11 (q104 c4) ∷
   rw 11 (q105 c4) ∷
   rw 11 (q106 c4) ∷
   rw 10 (q107 c4) ∷
   rw 10 (q108 c4) ∷
   rw 10 (q109 c4) ∷
   rw 10 (q110 c4) ∷
   rw 10 (q111 c4) ∷
   rw 10 (q112 c4) ∷
   rw 11 (q113 c4) ∷
   rw 10 (q114 c4) ∷
   rw⁻ 5 (q92 c4) ∷
   rw 7 (q103 c4) ∷
   rw 7 (q104 c4) ∷
   rw 7 (q105 c4) ∷
   rw 7 (q106 c4) ∷
   rw 6 (q107 c4) ∷
   rw 6 (q108 c4) ∷
   rw 6 (q109 c4) ∷
   rw 6 (q110 c4) ∷
   rw 6 (q111 c4) ∷
   rw 6 (q112 c4) ∷
   rw 7 (q113 c4) ∷
   rw 8 (q115 c4) ∷
   rw⁻ 9 (q92 c4) ∷
   rw 11 (q103 c4) ∷
   rw 11 (q104 c4) ∷
   rw 11 (q105 c4) ∷
   rw 11 (q106 c4) ∷
   rw 10 (q107 c4) ∷
   rw 10 (q108 c4) ∷
   rw 10 (q109 c4) ∷
   rw 10 (q110 c4) ∷
   rw 10 (q111 c4) ∷
   rw 10 (q112 c4) ∷
   rw 11 (q113 c4) ∷
   rw 10 (q114 c4) ∷
   rw 6 (q114 c4) ∷
   rw⁻ 7 (q82 c4) ∷
   rw 8 (q83 c4) ∷
   rw 10 (q83 c4) ∷
   rw 9 (q116 c4) ∷
   rw 9 (q117 c4) ∷
   rw 9 (q118 c4) ∷
   rw 9 (q119 c4) ∷
   rw 8 (q120 c4) ∷
   rw 8 (q121 c4) ∷
   rw 8 (q122 c4) ∷
   rw 8 (q123 c4) ∷
   rw 8 (q124 c4) ∷
   rw 8 (q125 c4) ∷
   rw 9 (q126 c4) ∷
   rw 10 (q114 c4) ∷
   rw 11 (q127 c4) ∷
   rw 11 (q112 c4) ∷
   rw 12 (q128 c4) ∷
   rw 11 (q116 c4) ∷
   rw 11 (q117 c4) ∷
   rw 11 (q118 c4) ∷
   rw 11 (q119 c4) ∷
   rw 11 (q129 c4) ∷
   rw 8 (q130 c4) ∷
   rw 6 (q131 c4) ∷
   rw 8 (q132 c4) ∷
   rw 7 (q133 c4) ∷
   rw⁻ 0 (q81 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   rw 2 (q134 c4) ∷
   rw 1 (q38 c4) ∷
   rw 0 (q135 c4) ∷
   rw 0 (q136 c4) ∷
   rw⁻ 0 (q137 c4) ∷ []) Eq.refl

private
  q138 : Ws → Eqn
  q138 c4 = eqn (Bx1-2034 ∷ []) (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) (lem-beta-T-at011220 c4)
  q139 : Ws → Eqn
  q139 c4 = eqn (S0 ∷ Toff102 ∷ []) (Toff102 ∷ S0 ∷ []) (wl0504 (lit c4))
  q140 : Ws → Eqn
  q140 c4 = eqn (S0 ∷ CCZ134 ∷ []) (CCZ134 ∷ S0 ∷ []) (c₁ (S) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))

-- auto S0 | BOX(1;2034): 6 steps
lem-auto-S0-∣-BOX⟨1·2034⟩ : Ws → ⟪ (S0 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩ c4 = derive (S0 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ S0 ∷ [])
  (rw 1 (q138 c4) ∷
   rw 0 (q139 c4) ∷
   rw 1 (q140 c4) ∷
   rw 2 (q139 c4) ∷
   rw 3 (q140 c4) ∷
   rw⁻ 0 (q138 c4) ∷ []) Eq.refl

private
  q141 : Ws → Eqn
  q141 c4 = eqn (S0 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ S0 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩ c4)
  q142 : Ws → Eqn
  q142 c4 = eqn (S0 ∷ Toff403 ∷ []) (Toff403 ∷ S0 ∷ []) (wp0288 c4)
  q143 : Ws → Eqn
  q143 c4 = eqn (CS24 ∷ S0 ∷ []) (S0 ∷ CS24 ∷ []) (wl0640 (lit c4))
  q144 : Ws → Eqn
  q144 c4 = eqn (CS24⁻ ∷ S0 ∷ []) (S0 ∷ CS24⁻ ∷ []) (wl0641 (lit c4))

-- auto S0 | SBOX(1;2;03;4): 11 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩ : Ws → ⟪ (S0 ∷ Sb1-2-03-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-03-4 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩ c4 = derive (S0 ∷ Sb1-2-03-4 ∷ []) (Sb1-2-03-4 ∷ S0 ∷ [])
  (re 1 1 (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ Sb⁻1-2-4-3 ∷ []) ∷
   rw 0 (q141 c4) ∷
   rw 1 (q142 c4) ∷
   re 3 1 (CS24 ∷ []) ∷
   rw⁻ 2 (q143 c4) ∷
   re 2 1 (Sb1-2-4-3 ∷ []) ∷
   rw 3 (q142 c4) ∷
   re 5 1 (CS24⁻ ∷ []) ∷
   rw⁻ 4 (q144 c4) ∷
   re 4 1 (Sb⁻1-2-4-3 ∷ []) ∷
   re 0 5 (Sb1-2-03-4 ∷ []) ∷ []) Eq.refl

private
  q145 : Ws → Eqn
  q145 c4 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wl0372 (lit c4))
  q146 : Ws → Eqn
  q146 c4 = eqn (Sw01 ∷ Sb0-2-13-4 ∷ []) (Sb1-2-03-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·13·4⟩ (lit c4))
  q147 : Ws → Eqn
  q147 c4 = eqn (S0 ∷ Sb1-2-03-4 ∷ []) (Sb1-2-03-4 ∷ S0 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩ c4)
  q148 : Ws → Eqn
  q148 c4 = eqn (Sw01 ∷ Sb1-2-03-4 ∷ []) (Sb0-2-13-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·03·4⟩ (lit c4))
  q149 : Ws → Eqn
  q149 c4 = eqn (S1 ∷ Sw01 ∷ []) (Sw01 ∷ S0 ∷ []) (wl0373 (lit c4))

-- auto S0 | SBOX(1;2;03;4) @0110: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0110 : Ws → ⟪ (S1 ∷ Sb0-2-13-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-13-4 ∷ S1 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0110 c4 = derive (S1 ∷ Sb0-2-13-4 ∷ []) (Sb0-2-13-4 ∷ S1 ∷ [])
  (rw⁻ 0 (q30 c4) ∷
   rw⁻ 1 (q145 c4) ∷
   rw 2 (q146 c4) ∷
   rw 1 (q147 c4) ∷
   rw 0 (q148 c4) ∷
   rw⁻ 1 (q149 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

private
  q150 : Ws → Eqn
  q150 c4 = eqn (S1 ∷ Sw12 ∷ []) (Sw12 ∷ S2 ∷ []) (wl0642 (lit c4))
  q151 : Ws → Eqn
  q151 c4 = eqn (Sw12 ∷ Sb0-1-23-4 ∷ []) (Sb0-2-13-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·23·4⟩ (lit c4))
  q152 : Ws → Eqn
  q152 c4 = eqn (S1 ∷ Sb0-2-13-4 ∷ []) (Sb0-2-13-4 ∷ S1 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0110 c4)
  q153 : Ws → Eqn
  q153 c4 = eqn (Sw12 ∷ Sb0-2-13-4 ∷ []) (Sb0-1-23-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·13·4⟩ (lit c4))
  q154 : Ws → Eqn
  q154 c4 = eqn (S2 ∷ Sw12 ∷ []) (Sw12 ∷ S1 ∷ []) (wl0643 (lit c4))

-- auto S0 | SBOX(1;2;03;4) @021021: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at021021 : Ws → ⟪ (S2 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ S2 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at021021 c4 = derive (S2 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-23-4 ∷ S2 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q150 c4) ∷
   rw 2 (q151 c4) ∷
   rw 1 (q152 c4) ∷
   rw 0 (q153 c4) ∷
   rw⁻ 1 (q154 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q155 : Ws → Eqn
  q155 c4 = eqn (S2 ∷ Sw23 ∷ []) (Sw23 ∷ S3 ∷ []) (wl0644 (lit c4))
  q156 : Ws → Eqn
  q156 c4 = eqn (Sw23 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4))
  q157 : Ws → Eqn
  q157 c4 = eqn (S2 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-23-4 ∷ S2 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at021021 c4)
  q158 : Ws → Eqn
  q158 c4 = eqn (Sw23 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4))
  q159 : Ws → Eqn
  q159 c4 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wl0645 (lit c4))

-- auto S0 | SBOX(1;2;03;4) @03102132: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at03102132 : Ws → ⟪ (S3 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ S3 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at03102132 c4 = derive (S3 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-32-4 ∷ S3 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw⁻ 1 (q155 c4) ∷
   rw 2 (q156 c4) ∷
   rw 1 (q157 c4) ∷
   rw 0 (q158 c4) ∷
   rw⁻ 1 (q159 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q160 : Ws → Eqn
  q160 c4 = eqn (S3 ∷ Sw34 ∷ []) (Sw34 ∷ S4 ∷ []) (wl0646 (lit c4))
  q161 : Ws → Eqn
  q161 c4 = eqn (Sw34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4))
  q162 : Ws → Eqn
  q162 c4 = eqn (S3 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-32-4 ∷ S3 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at03102132 c4)
  q163 : Ws → Eqn
  q163 c4 = eqn (Sw34 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4))
  q164 : Ws → Eqn
  q164 c4 = eqn (S4 ∷ Sw34 ∷ []) (Sw34 ∷ S3 ∷ []) (wl0647 (lit c4))

-- auto S0 | SBOX(1;2;03;4) @0410213243: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0410213243 : Ws → ⟪ (S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4 = derive (S4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ S4 ∷ [])
  (rw⁻ 0 (q48 c4) ∷
   rw⁻ 1 (q160 c4) ∷
   rw 2 (q161 c4) ∷
   rw 1 (q162 c4) ∷
   rw 0 (q163 c4) ∷
   rw⁻ 1 (q164 c4) ∷
   rw 2 (q48 c4) ∷ []) Eq.refl

private
  q165 : Ws → Eqn
  q165 c4 = eqn (Sw01 ∷ S4 ∷ []) (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑))
  q166 : Ws → Eqn
  q166 c4 = eqn (Sw01 ∷ Sb1-0-42-3 ∷ []) (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4))
  q167 : Ws → Eqn
  q167 c4 = eqn (S4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4)
  q168 : Ws → Eqn
  q168 c4 = eqn (Sw01 ∷ Sb0-1-42-3 ∷ []) (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4))

-- auto S0 | SBOX(1;2;03;4) @04203243: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at04203243 : Ws → ⟪ (S4 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at04203243 c4 = derive (S4 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ S4 ∷ [])
  (rw⁻ 0 (q30 c4) ∷
   rw 1 (q165 c4) ∷
   rw 2 (q166 c4) ∷
   rw 1 (q167 c4) ∷
   rw 0 (q168 c4) ∷
   rw 1 (q165 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

private
  q169 : Ws → Eqn
  q169 c4 = eqn (Sw12 ∷ S4 ∷ []) (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑))
  q170 : Ws → Eqn
  q170 c4 = eqn (Sw12 ∷ Sb2-0-41-3 ∷ []) (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4))
  q171 : Ws → Eqn
  q171 c4 = eqn (S4 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at04203243 c4)
  q172 : Ws → Eqn
  q172 c4 = eqn (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4))

-- auto S0 | SBOX(1;2;03;4) @0412203143: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0412203143 : Ws → ⟪ (S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0412203143 c4 = derive (S4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S4 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q169 c4) ∷
   rw 2 (q170 c4) ∷
   rw 1 (q171 c4) ∷
   rw 0 (q172 c4) ∷
   rw 1 (q169 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q173 : Ws → Eqn
  q173 c4 = eqn (S4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0412203143 c4)

-- F2 iI|CS01: 1 steps
lem-F2-iI∣CS01 : Ws → ⟪ (S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S4 ∷ []) ⟫ʷ
lem-F2-iI∣CS01 c4 = derive (S4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S4 ∷ [])
  (rw 0 (q173 c4) ∷ []) Eq.refl

private
  q174 : Ws → Eqn
  q174 c4 = eqn (Sw23 ∷ S4 ∷ []) (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S))
  q175 : Ws → Eqn
  q175 c4 = eqn (Sw23 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4))
  q176 : Ws → Eqn
  q176 c4 = eqn (Sw23 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4))

-- auto S0 | SBOX(1;2;03;4) @04102142: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at04102142 : Ws → ⟪ (S4 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at04102142 c4 = derive (S4 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ S4 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q174 c4) ∷
   rw 2 (q175 c4) ∷
   rw 1 (q167 c4) ∷
   rw 0 (q176 c4) ∷
   rw 1 (q174 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

-- F2 iI|CS12: 1 steps
lem-F2-iI∣CS12 : Ws → ⟪ (S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ S4 ∷ []) ⟫ʷ
lem-F2-iI∣CS12 c4 = derive (S4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ S4 ∷ [])
  (rw 0 (q167 c4) ∷ []) Eq.refl

private
  q177 : Ws → Eqn
  q177 c4 = eqn (Sw12 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4))
  q178 : Ws → Eqn
  q178 c4 = eqn (S4 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at04102142 c4)
  q179 : Ws → Eqn
  q179 c4 = eqn (Sw12 ∷ Sb0-1-43-2 ∷ []) (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4))

-- auto S0 | SBOX(1;2;03;4) @041041: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at041041 : Ws → ⟪ (S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at041041 c4 = derive (S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ S4 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q169 c4) ∷
   rw 2 (q177 c4) ∷
   rw 1 (q178 c4) ∷
   rw 0 (q179 c4) ∷
   rw 1 (q169 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q180 : Ws → Eqn
  q180 c4 = eqn (S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at041041 c4)

-- F2 iI|CS23: 1 steps
lem-F2-iI∣CS23 : Ws → ⟪ (S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ S4 ∷ []) ⟫ʷ
lem-F2-iI∣CS23 c4 = derive (S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ S4 ∷ [])
  (rw 0 (q180 c4) ∷ []) Eq.refl

private
  q181 : Ws → Eqn
  q181 c4 = eqn (CS01 ∷ []) (CS01 ∷ []) (wl0332 (lit c4))
  q182 : Ws → Eqn
  q182 c4 = eqn (CS01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CS01 ∷ []) (lem-CS20-beta-c-at011220 c4)

-- auto CS01 | BOX(1;2034): 3 steps
lem-auto-CS01-∣-BOX⟨1·2034⟩ : Ws → ⟪ (CS01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2034⟩ c4 = derive (CS01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CS01 ∷ [])
  (rw 0 (q181 c4) ∷
   rw 0 (q182 c4) ∷
   rw 1 (q181 c4) ∷ []) Eq.refl

private
  q183 : Ws → Eqn
  q183 c4 = eqn (CS01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩ c4)
  q184 : Ws → Eqn
  q184 c4 = eqn (CS01 ∷ Toff403 ∷ []) (Toff403 ∷ CS01 ∷ []) (wp0289 c4)
  q185 : Ws → Eqn
  q185 c4 = eqn (CS01 ∷ CS24 ∷ []) (CS24 ∷ CS01 ∷ []) (wp0290 c4)
  q186 : Ws → Eqn
  q186 c4 = eqn (CS01 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS01 ∷ []) (wp0291 c4)

-- auto CS01 | SBOX(1;2;03;4): 11 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩ : Ws → ⟪ (CS01 ∷ Sb1-2-03-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-03-4 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩ c4 = derive (CS01 ∷ Sb1-2-03-4 ∷ []) (Sb1-2-03-4 ∷ CS01 ∷ [])
  (re 1 1 (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ Sb⁻1-2-4-3 ∷ []) ∷
   rw 0 (q183 c4) ∷
   rw 1 (q184 c4) ∷
   re 3 1 (CS24 ∷ []) ∷
   rw 2 (q185 c4) ∷
   re 2 1 (Sb1-2-4-3 ∷ []) ∷
   rw 3 (q184 c4) ∷
   re 5 1 (CS24⁻ ∷ []) ∷
   rw 4 (q186 c4) ∷
   re 4 1 (Sb⁻1-2-4-3 ∷ []) ∷
   re 0 5 (Sb1-2-03-4 ∷ []) ∷ []) Eq.refl

private
  q187 : Ws → Eqn
  q187 c4 = eqn (CS01 ∷ Sw01 ∷ []) (Sw01 ∷ CS01 ∷ []) (wl0132 (lit c4))
  q188 : Ws → Eqn
  q188 c4 = eqn (CS01 ∷ Sb1-2-03-4 ∷ []) (Sb1-2-03-4 ∷ CS01 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩ c4)

-- auto CS01 | SBOX(1;2;03;4) @0110: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0110 : Ws → ⟪ (CS01 ∷ Sb0-2-13-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-13-4 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0110 c4 = derive (CS01 ∷ Sb0-2-13-4 ∷ []) (Sb0-2-13-4 ∷ CS01 ∷ [])
  (rw⁻ 0 (q30 c4) ∷
   rw⁻ 1 (q187 c4) ∷
   rw 2 (q146 c4) ∷
   rw 1 (q188 c4) ∷
   rw 0 (q148 c4) ∷
   rw⁻ 1 (q187 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

private
  q189 : Ws → Eqn
  q189 c4 = eqn (Sw12 ∷ CS02 ∷ []) (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4))
  q190 : Ws → Eqn
  q190 c4 = eqn (CS01 ∷ Sb0-2-13-4 ∷ []) (Sb0-2-13-4 ∷ CS01 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0110 c4)
  q191 : Ws → Eqn
  q191 c4 = eqn (Sw12 ∷ CS01 ∷ []) (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4))

-- auto CS01 | SBOX(1;2;03;4) @021021: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at021021 : Ws → ⟪ (CS02 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at021021 c4 = derive (CS02 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-23-4 ∷ CS02 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q189 c4) ∷
   rw 2 (q151 c4) ∷
   rw 1 (q190 c4) ∷
   rw 0 (q153 c4) ∷
   rw 1 (q191 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q192 : Ws → Eqn
  q192 c4 = eqn (Sw23 ∷ CS03 ∷ []) (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 (lit c4))
  q193 : Ws → Eqn
  q193 c4 = eqn (CS02 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-23-4 ∷ CS02 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at021021 c4)
  q194 : Ws → Eqn
  q194 c4 = eqn (Sw23 ∷ CS02 ∷ []) (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4))

-- auto CS01 | SBOX(1;2;03;4) @03102132: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at03102132 : Ws → ⟪ (CS03 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ CS03 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at03102132 c4 = derive (CS03 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-32-4 ∷ CS03 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q192 c4) ∷
   rw 2 (q156 c4) ∷
   rw 1 (q193 c4) ∷
   rw 0 (q158 c4) ∷
   rw 1 (q194 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q195 : Ws → Eqn
  q195 c4 = eqn (Sw34 ∷ CS04 ∷ []) (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 (lit c4))
  q196 : Ws → Eqn
  q196 c4 = eqn (CS03 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-32-4 ∷ CS03 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at03102132 c4)
  q197 : Ws → Eqn
  q197 c4 = eqn (Sw34 ∷ CS03 ∷ []) (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 (lit c4))

-- auto CS01 | SBOX(1;2;03;4) @0410213243: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0410213243 : Ws → ⟪ (CS04 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4 = derive (CS04 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS04 ∷ [])
  (rw⁻ 0 (q48 c4) ∷
   rw 1 (q195 c4) ∷
   rw 2 (q161 c4) ∷
   rw 1 (q196 c4) ∷
   rw 0 (q163 c4) ∷
   rw 1 (q197 c4) ∷
   rw 2 (q48 c4) ∷ []) Eq.refl

private
  q198 : Ws → Eqn
  q198 c4 = eqn (CS04 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS04 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4)

-- F2 S0|CS12: 1 steps
lem-F2-S0∣CS12 : Ws → ⟪ (CS04 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0∣CS12 c4 = derive (CS04 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS04 ∷ [])
  (rw 0 (q198 c4) ∷ []) Eq.refl

private
  q199 : Ws → Eqn
  q199 c4 = eqn (Sw23 ∷ CS04 ∷ []) (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4))

-- auto CS01 | SBOX(1;2;03;4) @04102142: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at04102142 : Ws → ⟪ (CS04 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at04102142 c4 = derive (CS04 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CS04 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q199 c4) ∷
   rw 2 (q175 c4) ∷
   rw 1 (q198 c4) ∷
   rw 0 (q176 c4) ∷
   rw 1 (q199 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q200 : Ws → Eqn
  q200 c4 = eqn (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4))
  q201 : Ws → Eqn
  q201 c4 = eqn (CS04 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CS04 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at04102142 c4)

-- auto CS01 | SBOX(1;2;03;4) @041041: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at041041 : Ws → ⟪ (CS04 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at041041 c4 = derive (CS04 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS04 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q200 c4) ∷
   rw 2 (q177 c4) ∷
   rw 1 (q201 c4) ∷
   rw 0 (q179 c4) ∷
   rw 1 (q200 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q202 : Ws → Eqn
  q202 c4 = eqn (CS04 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS04 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at041041 c4)

-- F2 S0|CS23: 1 steps
lem-F2-S0∣CS23 : Ws → ⟪ (CS04 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0∣CS23 c4 = derive (CS04 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS04 ∷ [])
  (rw 0 (q202 c4) ∷ []) Eq.refl

private
  q203 : Ws → Eqn
  q203 c4 = eqn (Sw01 ∷ CS14 ∷ []) (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4))
  q204 : Ws → Eqn
  q204 c4 = eqn (Sw01 ∷ CS04 ∷ []) (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4))

-- auto CS01 | SBOX(1;2;03;4) @04203243: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at04203243 : Ws → ⟪ (CS14 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CS14 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at04203243 c4 = derive (CS14 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CS14 ∷ [])
  (rw⁻ 0 (q30 c4) ∷
   rw 1 (q203 c4) ∷
   rw 2 (q166 c4) ∷
   rw 1 (q198 c4) ∷
   rw 0 (q168 c4) ∷
   rw 1 (q204 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

private
  q205 : Ws → Eqn
  q205 c4 = eqn (CS14 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS14 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04203243 c4)

-- F2 S1|CS23: 1 steps
lem-F2-S1∣CS23 : Ws → ⟪ (CS14 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1∣CS23 c4 = derive (CS14 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS14 ∷ [])
  (rw 0 (q205 c4) ∷ []) Eq.refl

private
  q206 : Ws → Eqn
  q206 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0017 (lit c4))
  q207 : Ws → Eqn
  q207 c4 = eqn (CS14 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CS14 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at04203243 c4)
  q208 : Ws → Eqn
  q208 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 (lit c4))

-- auto CS01 | SBOX(1;2;03;4) @0412203143: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0412203143 : Ws → ⟪ (CS24 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS24 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0412203143 c4 = derive (CS24 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS24 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q206 c4) ∷
   rw 2 (q170 c4) ∷
   rw 1 (q207 c4) ∷
   rw 0 (q172 c4) ∷
   rw⁻ 1 (q208 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q209 : Ws → Eqn
  q209 c4 = eqn (CS24 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS24 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0412203143 c4)

-- F2 S2|CS01: 1 steps
lem-F2-S2∣CS01 : Ws → ⟪ (CS24 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2∣CS01 c4 = derive (CS24 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS24 ∷ [])
  (rw 0 (q209 c4) ∷ []) Eq.refl

private
  q210 : Ws → Eqn
  q210 c4 = eqn (CS34 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS34 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 c4)

-- F2 S3|CS01: 1 steps
lem-F2-S3∣CS01 : Ws → ⟪ (CS34 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3∣CS01 c4 = derive (CS34 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS34 ∷ [])
  (rw 0 (q210 c4) ∷ []) Eq.refl

private
  q211 : Ws → Eqn
  q211 c4 = eqn (CS34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS34 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413203142 c4)

-- F2 S3|CS12: 1 steps
lem-F2-S3∣CS12 : Ws → ⟪ (CS34 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3∣CS12 c4 = derive (CS34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS34 ∷ [])
  (rw 0 (q211 c4) ∷ []) Eq.refl

private
  q212 : Ws → Eqn
  q212 c4 = eqn (Bx0-1234 ∷ ι ∷ []) (ι ∷ Bx0-1234 ∷ []) zc

-- auto iI | BOX(0;1234): 1 steps
lem-auto-iI-∣-BOX⟨0·1234⟩ : Ws → ⟪ (ι ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ ι ∷ []) ⟫ʷ
lem-auto-iI-∣-BOX⟨0·1234⟩ c4 = derive (ι ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ ι ∷ [])
  (rw⁻ 0 (q212 c4) ∷ []) Eq.refl

private
  q213 : Ws → Eqn
  q213 c4 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap))
  q214 : Ws → Eqn
  q214 c4 = eqn (Sw12 ∷ Bx0-2134 ∷ []) (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4))
  q215 : Ws → Eqn
  q215 c4 = eqn (K0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩ c4)
  q216 : Ws → Eqn
  q216 c4 = eqn (Sw12 ∷ Bx0-1234 ∷ []) (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4))

-- auto K0 | BOX(0;1234) @1221: 7 steps
lem-auto-K0-∣-BOX⟨0·1234⟩-at1221 : Ws → ⟪ (K0 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ K0 ∷ []) ⟫ʷ
lem-auto-K0-∣-BOX⟨0·1234⟩-at1221 c4 = derive (K0 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ K0 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q213 c4) ∷
   rw 2 (q214 c4) ∷
   rw 1 (q215 c4) ∷
   rw 0 (q216 c4) ∷
   rw⁻ 1 (q213 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q217 : Ws → Eqn
  q217 c4 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wl0031 (lit c4))
  q218 : Ws → Eqn
  q218 c4 = eqn (Sw01 ∷ Bx1-2034 ∷ []) (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ (lit c4))
  q219 : Ws → Eqn
  q219 c4 = eqn (K0 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ K0 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩-at1221 c4)
  q220 : Ws → Eqn
  q220 c4 = eqn (Sw01 ∷ Bx0-2134 ∷ []) (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ (lit c4))
  q221 : Ws → Eqn
  q221 c4 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wl0076 (lit c4))

-- auto K0 | BOX(0;1234) @011220: 7 steps
lem-auto-K0-∣-BOX⟨0·1234⟩-at011220 : Ws → ⟪ (K1 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ K1 ∷ []) ⟫ʷ
lem-auto-K0-∣-BOX⟨0·1234⟩-at011220 c4 = derive (K1 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ K1 ∷ [])
  (rw⁻ 0 (q30 c4) ∷
   rw⁻ 1 (q217 c4) ∷
   rw 2 (q218 c4) ∷
   rw 1 (q219 c4) ∷
   rw 0 (q220 c4) ∷
   rw⁻ 1 (q221 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

private
  q222 : Ws → Eqn
  q222 c4 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap))
  q223 : Ws → Eqn
  q223 c4 = eqn (ι ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ ι ∷ []) (lem-auto-iI-∣-BOX⟨0·1234⟩ c4)

-- auto iI | BOX(0;1234) @1221: 7 steps
lem-auto-iI-∣-BOX⟨0·1234⟩-at1221 : Ws → ⟪ (ι ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ ι ∷ []) ⟫ʷ
lem-auto-iI-∣-BOX⟨0·1234⟩-at1221 c4 = derive (ι ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ ι ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q222 c4) ∷
   rw 2 (q214 c4) ∷
   rw 1 (q223 c4) ∷
   rw 0 (q216 c4) ∷
   rw⁻ 1 (q222 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q224 : Ws → Eqn
  q224 c4 = eqn (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ []) (wl0030 (lit c4))
  q225 : Ws → Eqn
  q225 c4 = eqn (ι ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ ι ∷ []) (lem-auto-iI-∣-BOX⟨0·1234⟩-at1221 c4)

-- auto iI | BOX(0;1234) @011220: 7 steps
lem-auto-iI-∣-BOX⟨0·1234⟩-at011220 : Ws → ⟪ (ι ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ ι ∷ []) ⟫ʷ
lem-auto-iI-∣-BOX⟨0·1234⟩-at011220 c4 = derive (ι ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ ι ∷ [])
  (rw⁻ 0 (q30 c4) ∷
   rw 1 (q224 c4) ∷
   rw 2 (q218 c4) ∷
   rw 1 (q225 c4) ∷
   rw 0 (q220 c4) ∷
   rw 1 (q224 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

private
  q226 : Ws → Eqn
  q226 c4 = eqn (CK01 ∷ []) (ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) (wl0516 (lit c4))
  q227 : Ws → Eqn
  q227 c4 = eqn (K1 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ K1 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩-at011220 c4)
  q228 : Ws → Eqn
  q228 c4 = eqn (S0⁻ ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ S0⁻ ∷ []) (lem-auto-Sd0-∣-BOX⟨1·2034⟩ c4)
  q229 : Ws → Eqn
  q229 c4 = eqn (ι ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ ι ∷ []) (lem-auto-iI-∣-BOX⟨0·1234⟩-at011220 c4)

-- auto CK01 | BOX(1;2034): 9 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩ : Ws → ⟪ (CK01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CK01 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩ c4 = derive (CK01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CK01 ∷ [])
  (rw 0 (q226 c4) ∷
   rw 6 (q183 c4) ∷
   rw 5 (q227 c4) ∷
   rw 4 (q183 c4) ∷
   rw 3 (q227 c4) ∷
   rw 2 (q183 c4) ∷
   rw 1 (q228 c4) ∷
   rw 0 (q229 c4) ∷
   rw⁻ 1 (q226 c4) ∷ []) Eq.refl

private
  q230 : Ws → Eqn
  q230 c4 = eqn (CK01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CK01 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩ c4)
  q231 : Ws → Eqn
  q231 c4 = eqn (CK01 ∷ Toff403 ∷ []) (Toff403 ∷ CK01 ∷ []) (wp0292 c4)
  q232 : Ws → Eqn
  q232 c4 = eqn (CK01 ∷ CS24 ∷ []) (CS24 ∷ CK01 ∷ []) (wp0293 c4)
  q233 : Ws → Eqn
  q233 c4 = eqn (CK01 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CK01 ∷ []) (wp0294 c4)

-- auto CK01 | SBOX(1;2;03;4): 11 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩ : Ws → ⟪ (CK01 ∷ Sb1-2-03-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-03-4 ∷ CK01 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩ c4 = derive (CK01 ∷ Sb1-2-03-4 ∷ []) (Sb1-2-03-4 ∷ CK01 ∷ [])
  (re 1 1 (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ Sb⁻1-2-4-3 ∷ []) ∷
   rw 0 (q230 c4) ∷
   rw 1 (q231 c4) ∷
   re 3 1 (CS24 ∷ []) ∷
   rw 2 (q232 c4) ∷
   re 2 1 (Sb1-2-4-3 ∷ []) ∷
   rw 3 (q231 c4) ∷
   re 5 1 (CS24⁻ ∷ []) ∷
   rw 4 (q233 c4) ∷
   re 4 1 (Sb⁻1-2-4-3 ∷ []) ∷
   re 0 5 (Sb1-2-03-4 ∷ []) ∷ []) Eq.refl

private
  q234 : Ws → Eqn
  q234 c4 = eqn (CK01 ∷ Sw01 ∷ []) (Sw01 ∷ CK10 ∷ []) (wl0648 (lit c4))
  q235 : Ws → Eqn
  q235 c4 = eqn (CK01 ∷ Sb1-2-03-4 ∷ []) (Sb1-2-03-4 ∷ CK01 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩ c4)
  q236 : Ws → Eqn
  q236 c4 = eqn (CK10 ∷ Sw01 ∷ []) (Sw01 ∷ CK01 ∷ []) (wl0649 (lit c4))

-- auto CK01 | SBOX(1;2;03;4) @0110: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0110 : Ws → ⟪ (CK10 ∷ Sb0-2-13-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-13-4 ∷ CK10 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0110 c4 = derive (CK10 ∷ Sb0-2-13-4 ∷ []) (Sb0-2-13-4 ∷ CK10 ∷ [])
  (rw⁻ 0 (q30 c4) ∷
   rw⁻ 1 (q234 c4) ∷
   rw 2 (q146 c4) ∷
   rw 1 (q235 c4) ∷
   rw 0 (q148 c4) ∷
   rw⁻ 1 (q236 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

private
  q237 : Ws → Eqn
  q237 c4 = eqn (Sw12 ∷ CK20 ∷ []) (CK10 ∷ Sw12 ∷ []) (lem-nat-1-CK20 (lit c4))
  q238 : Ws → Eqn
  q238 c4 = eqn (CK10 ∷ Sb0-2-13-4 ∷ []) (Sb0-2-13-4 ∷ CK10 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0110 c4)
  q239 : Ws → Eqn
  q239 c4 = eqn (Sw12 ∷ CK10 ∷ []) (CK20 ∷ Sw12 ∷ []) (lem-nat-1-CK10 (lit c4))

-- auto CK01 | SBOX(1;2;03;4) @021021: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at021021 : Ws → ⟪ (CK20 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ CK20 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at021021 c4 = derive (CK20 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-23-4 ∷ CK20 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q237 c4) ∷
   rw 2 (q151 c4) ∷
   rw 1 (q238 c4) ∷
   rw 0 (q153 c4) ∷
   rw 1 (q239 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q240 : Ws → Eqn
  q240 c4 = eqn (Sw23 ∷ CK30 ∷ []) (CK20 ∷ Sw23 ∷ []) (lem-nat-2-CK30 (lit c4))
  q241 : Ws → Eqn
  q241 c4 = eqn (CK20 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-23-4 ∷ CK20 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at021021 c4)
  q242 : Ws → Eqn
  q242 c4 = eqn (Sw23 ∷ CK20 ∷ []) (CK30 ∷ Sw23 ∷ []) (lem-nat-2-CK20 (lit c4))

-- auto CK01 | SBOX(1;2;03;4) @03102132: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at03102132 : Ws → ⟪ (CK30 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ CK30 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at03102132 c4 = derive (CK30 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-32-4 ∷ CK30 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q240 c4) ∷
   rw 2 (q156 c4) ∷
   rw 1 (q241 c4) ∷
   rw 0 (q158 c4) ∷
   rw 1 (q242 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q243 : Ws → Eqn
  q243 c4 = eqn (Sw34 ∷ CK40 ∷ []) (CK30 ∷ Sw34 ∷ []) (lem-nat-3-CK40 (lit c4))
  q244 : Ws → Eqn
  q244 c4 = eqn (CK30 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-32-4 ∷ CK30 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at03102132 c4)
  q245 : Ws → Eqn
  q245 c4 = eqn (Sw34 ∷ CK30 ∷ []) (CK40 ∷ Sw34 ∷ []) (lem-nat-3-CK30 (lit c4))

-- auto CK01 | SBOX(1;2;03;4) @0410213243: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0410213243 : Ws → ⟪ (CK40 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK40 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4 = derive (CK40 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK40 ∷ [])
  (rw⁻ 0 (q48 c4) ∷
   rw 1 (q243 c4) ∷
   rw 2 (q161 c4) ∷
   rw 1 (q244 c4) ∷
   rw 0 (q163 c4) ∷
   rw 1 (q245 c4) ∷
   rw 2 (q48 c4) ∷ []) Eq.refl

private
  q246 : Ws → Eqn
  q246 c4 = eqn (CK40 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK40 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4)

-- F2 K0|CS12: 1 steps
lem-F2-K0∣CS12 : Ws → ⟪ (CK40 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0∣CS12 c4 = derive (CK40 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK40 ∷ [])
  (rw 0 (q246 c4) ∷ []) Eq.refl

private
  q247 : Ws → Eqn
  q247 c4 = eqn (Sw23 ∷ CK40 ∷ []) (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4))

-- auto CK01 | SBOX(1;2;03;4) @04102142: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at04102142 : Ws → ⟪ (CK40 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CK40 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at04102142 c4 = derive (CK40 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CK40 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q247 c4) ∷
   rw 2 (q175 c4) ∷
   rw 1 (q246 c4) ∷
   rw 0 (q176 c4) ∷
   rw 1 (q247 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q248 : Ws → Eqn
  q248 c4 = eqn (Sw12 ∷ CK40 ∷ []) (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4))
  q249 : Ws → Eqn
  q249 c4 = eqn (CK40 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CK40 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at04102142 c4)

-- auto CK01 | SBOX(1;2;03;4) @041041: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at041041 : Ws → ⟪ (CK40 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CK40 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at041041 c4 = derive (CK40 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CK40 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q248 c4) ∷
   rw 2 (q177 c4) ∷
   rw 1 (q249 c4) ∷
   rw 0 (q179 c4) ∷
   rw 1 (q248 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q250 : Ws → Eqn
  q250 c4 = eqn (CK40 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CK40 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at041041 c4)

-- F2 K0|CS23: 1 steps
lem-F2-K0∣CS23 : Ws → ⟪ (CK40 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0∣CS23 c4 = derive (CK40 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CK40 ∷ [])
  (rw 0 (q250 c4) ∷ []) Eq.refl

private
  q251 : Ws → Eqn
  q251 c4 = eqn (Sw01 ∷ CK41 ∷ []) (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4))
  q252 : Ws → Eqn
  q252 c4 = eqn (Sw01 ∷ CK40 ∷ []) (CK41 ∷ Sw01 ∷ []) (lem-nat-0-CK40 (lit c4))

-- auto CK01 | SBOX(1;2;03;4) @04203243: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at04203243 : Ws → ⟪ (CK41 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CK41 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at04203243 c4 = derive (CK41 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CK41 ∷ [])
  (rw⁻ 0 (q30 c4) ∷
   rw 1 (q251 c4) ∷
   rw 2 (q166 c4) ∷
   rw 1 (q246 c4) ∷
   rw 0 (q168 c4) ∷
   rw 1 (q252 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

private
  q253 : Ws → Eqn
  q253 c4 = eqn (Sw23 ∷ Sb0-3-24-1 ∷ []) (Sb0-2-34-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·3·24·1⟩ (lit c4))
  q254 : Ws → Eqn
  q254 c4 = eqn (Sb0-2-34-1 ∷ []) (Sb1-2-34-0 ∷ []) (lem-F0-at0214203143 c4)
  q255 : Ws → Eqn
  q255 c4 = eqn (Sw23 ∷ Sb1-2-34-0 ∷ []) (Sb1-3-24-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·2·34·0⟩ (lit c4))

-- F0 @0314203142: 5 steps
lem-F0-at0314203142 : Ws → ⟪ (Sb0-3-24-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-24-0 ∷ []) ⟫ʷ
lem-F0-at0314203142 c4 = derive (Sb0-3-24-1 ∷ []) (Sb1-3-24-0 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q253 c4) ∷
   rw 1 (q254 c4) ∷
   rw 0 (q255 c4) ∷
   rw 1 (q10 c4) ∷ []) Eq.refl

private
  q256 : Ws → Eqn
  q256 c4 = eqn (Sw01 ∷ Sb1-3-24-0 ∷ []) (Sb0-3-24-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·3·24·0⟩ (lit c4))
  q257 : Ws → Eqn
  q257 c4 = eqn (Sb0-3-24-1 ∷ []) (Sb1-3-24-0 ∷ []) (lem-F0-at0314203142 c4)

-- F0 @0314213042: 5 steps
lem-F0-at0314213042 : Ws → ⟪ (Sb1-3-24-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-24-1 ∷ []) ⟫ʷ
lem-F0-at0314213042 c4 = derive (Sb1-3-24-0 ∷ []) (Sb0-3-24-1 ∷ [])
  (rw⁻ 0 (q30 c4) ∷
   rw 1 (q256 c4) ∷
   rw 1 (q257 c4) ∷
   rw 0 (q256 c4) ∷
   rw 1 (q30 c4) ∷ []) Eq.refl

private
  q258 : Ws → Eqn
  q258 c4 = eqn (Sw12 ∷ Sb2-3-14-0 ∷ []) (Sb1-3-24-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·3·14·0⟩ (lit c4))
  q259 : Ws → Eqn
  q259 c4 = eqn (Sb1-3-24-0 ∷ []) (Sb0-3-24-1 ∷ []) (lem-F0-at0314213042 c4)
  q260 : Ws → Eqn
  q260 c4 = eqn (Sw12 ∷ Sb0-3-24-1 ∷ []) (Sb0-3-14-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·3·24·1⟩ (lit c4))

-- F0 @03143041: 5 steps
lem-F0-at03143041 : Ws → ⟪ (Sb2-3-14-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-14-2 ∷ []) ⟫ʷ
lem-F0-at03143041 c4 = derive (Sb2-3-14-0 ∷ []) (Sb0-3-14-2 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q258 c4) ∷
   rw 1 (q259 c4) ∷
   rw 0 (q260 c4) ∷
   rw 1 (q1 c4) ∷ []) Eq.refl

private
  q261 : Ws → Eqn
  q261 c4 = eqn (Sw01 ∷ Sb2-3-04-1 ∷ []) (Sb2-3-14-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·04·1⟩ (lit c4))
  q262 : Ws → Eqn
  q262 c4 = eqn (Sb2-3-14-0 ∷ []) (Sb0-3-14-2 ∷ []) (lem-F0-at03143041 c4)
  q263 : Ws → Eqn
  q263 c4 = eqn (Sw01 ∷ Sb0-3-14-2 ∷ []) (Sb1-3-04-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·3·14·2⟩ (lit c4))

-- F0 @03143140: 5 steps
lem-F0-at03143140 : Ws → ⟪ (Sb2-3-04-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-04-2 ∷ []) ⟫ʷ
lem-F0-at03143140 c4 = derive (Sb2-3-04-1 ∷ []) (Sb1-3-04-2 ∷ [])
  (rw⁻ 0 (q30 c4) ∷
   rw 1 (q261 c4) ∷
   rw 1 (q262 c4) ∷
   rw 0 (q263 c4) ∷
   rw 1 (q30 c4) ∷ []) Eq.refl

private
  q264 : Ws → Eqn
  q264 c4 = eqn (CK01 ∷ Sw34 ∷ []) (Sw34 ∷ CK01 ∷ []) (c₂ (CK₀₁) (Swap ↑))
  q265 : Ws → Eqn
  q265 c4 = eqn (Sw34 ∷ Bx1-2043 ∷ []) (Bx1-2034 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2043⟩ (lit c4))
  q266 : Ws → Eqn
  q266 c4 = eqn (Sw34 ∷ Bx1-2034 ∷ []) (Bx1-2043 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2034⟩ (lit c4))

-- auto CK01 | BOX(1;2034) @3443: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at3443 : Ws → ⟪ (CK01 ∷ Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2043 ∷ CK01 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at3443 c4 = derive (CK01 ∷ Bx1-2043 ∷ []) (Bx1-2043 ∷ CK01 ∷ [])
  (rw⁻ 0 (q48 c4) ∷
   rw⁻ 1 (q264 c4) ∷
   rw 2 (q265 c4) ∷
   rw 1 (q230 c4) ∷
   rw 0 (q266 c4) ∷
   rw⁻ 1 (q264 c4) ∷
   rw 2 (q48 c4) ∷ []) Eq.refl

private
  q267 : Ws → Eqn
  q267 c4 = eqn (CK01 ∷ Sw23 ∷ []) (Sw23 ∷ CK01 ∷ []) (c₂ (CK₀₁) (Swap))
  q268 : Ws → Eqn
  q268 c4 = eqn (Sw23 ∷ Bx1-3042 ∷ []) (Bx1-2043 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·3042⟩ (lit c4))
  q269 : Ws → Eqn
  q269 c4 = eqn (CK01 ∷ Bx1-2043 ∷ []) (Bx1-2043 ∷ CK01 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at3443 c4)
  q270 : Ws → Eqn
  q270 c4 = eqn (Sw23 ∷ Bx1-2043 ∷ []) (Bx1-3042 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·2043⟩ (lit c4))

-- auto CK01 | BOX(1;2034) @233442: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at233442 : Ws → ⟪ (CK01 ∷ Bx1-3042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3042 ∷ CK01 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at233442 c4 = derive (CK01 ∷ Bx1-3042 ∷ []) (Bx1-3042 ∷ CK01 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw⁻ 1 (q267 c4) ∷
   rw 2 (q268 c4) ∷
   rw 1 (q269 c4) ∷
   rw 0 (q270 c4) ∷
   rw⁻ 1 (q267 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q271 : Ws → Eqn
  q271 c4 = eqn (Sb2-3-04-1 ∷ []) (Sb1-3-04-2 ∷ []) (lem-F0-at03143140 c4)
  q272 : Ws → Eqn
  q272 c4 = eqn (CK01 ∷ Bx1-3042 ∷ []) (Bx1-3042 ∷ CK01 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at233442 c4)
  q273 : Ws → Eqn
  q273 c4 = eqn (CK01 ∷ Toff204 ∷ []) (Toff204 ∷ CK01 ∷ []) (wp0295 c4)
  q274 : Ws → Eqn
  q274 c4 = eqn (CK01 ∷ CS23 ∷ []) (CS23 ∷ CK01 ∷ []) (wl0650 (lit c4))
  q275 : Ws → Eqn
  q275 c4 = eqn (CK01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CK01 ∷ []) (wl0651 (lit c4))

-- auto CK01 | SBOX(2;3;04;1): 13 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩ : Ws → ⟪ (CK01 ∷ Sb2-3-04-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-04-1 ∷ CK01 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩ c4 = derive (CK01 ∷ Sb2-3-04-1 ∷ []) (Sb2-3-04-1 ∷ CK01 ∷ [])
  (rw 1 (q271 c4) ∷
   re 1 1 (Bx1-3042 ∷ Toff204 ∷ Sb1-3-2-4 ∷ Toff204 ∷ Sb⁻1-3-2-4 ∷ []) ∷
   rw 0 (q272 c4) ∷
   rw 1 (q273 c4) ∷
   re 3 1 (CS23 ∷ []) ∷
   rw 2 (q274 c4) ∷
   re 2 1 (Sb1-3-2-4 ∷ []) ∷
   rw 3 (q273 c4) ∷
   re 5 1 (CS23⁻ ∷ []) ∷
   rw 4 (q275 c4) ∷
   re 4 1 (Sb⁻1-3-2-4 ∷ []) ∷
   re 0 5 (Sb1-3-04-2 ∷ []) ∷
   rw⁻ 0 (q271 c4) ∷ []) Eq.refl

private
  q276 : Ws → Eqn
  q276 c4 = eqn (Sw01 ∷ Sb2-3-14-0 ∷ []) (Sb2-3-04-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·14·0⟩ (lit c4))
  q277 : Ws → Eqn
  q277 c4 = eqn (CK01 ∷ Sb2-3-04-1 ∷ []) (Sb2-3-04-1 ∷ CK01 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩ c4)

-- auto CK01 | SBOX(2;3;04;1) @0110: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0110 : Ws → ⟪ (CK10 ∷ Sb2-3-14-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-14-0 ∷ CK10 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0110 c4 = derive (CK10 ∷ Sb2-3-14-0 ∷ []) (Sb2-3-14-0 ∷ CK10 ∷ [])
  (rw⁻ 0 (q30 c4) ∷
   rw⁻ 1 (q234 c4) ∷
   rw 2 (q276 c4) ∷
   rw 1 (q277 c4) ∷
   rw 0 (q261 c4) ∷
   rw⁻ 1 (q236 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

private
  q278 : Ws → Eqn
  q278 c4 = eqn (Sw12 ∷ Sb1-3-24-0 ∷ []) (Sb2-3-14-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·3·24·0⟩ (lit c4))
  q279 : Ws → Eqn
  q279 c4 = eqn (CK10 ∷ Sb2-3-14-0 ∷ []) (Sb2-3-14-0 ∷ CK10 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0110 c4)

-- auto CK01 | SBOX(2;3;04;1) @021021: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at021021 : Ws → ⟪ (CK20 ∷ Sb1-3-24-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-24-0 ∷ CK20 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at021021 c4 = derive (CK20 ∷ Sb1-3-24-0 ∷ []) (Sb1-3-24-0 ∷ CK20 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q237 c4) ∷
   rw 2 (q278 c4) ∷
   rw 1 (q279 c4) ∷
   rw 0 (q258 c4) ∷
   rw 1 (q239 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q280 : Ws → Eqn
  q280 c4 = eqn (CK20 ∷ Sb1-3-24-0 ∷ []) (Sb1-3-24-0 ∷ CK20 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at021021 c4)
  q281 : Ws → Eqn
  q281 c4 = eqn (Sw23 ∷ Sb1-3-24-0 ∷ []) (Sb1-2-34-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·24·0⟩ (lit c4))

-- auto CK01 | SBOX(2;3;04;1) @03102132: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at03102132 : Ws → ⟪ (CK30 ∷ Sb1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-34-0 ∷ CK30 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at03102132 c4 = derive (CK30 ∷ Sb1-2-34-0 ∷ []) (Sb1-2-34-0 ∷ CK30 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q240 c4) ∷
   rw 2 (q255 c4) ∷
   rw 1 (q280 c4) ∷
   rw 0 (q281 c4) ∷
   rw 1 (q242 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q282 : Ws → Eqn
  q282 c4 = eqn (Sw34 ∷ Sb1-2-43-0 ∷ []) (Sb1-2-34-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·43·0⟩ (lit c4))
  q283 : Ws → Eqn
  q283 c4 = eqn (CK30 ∷ Sb1-2-34-0 ∷ []) (Sb1-2-34-0 ∷ CK30 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at03102132 c4)
  q284 : Ws → Eqn
  q284 c4 = eqn (Sw34 ∷ Sb1-2-34-0 ∷ []) (Sb1-2-43-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·34·0⟩ (lit c4))

-- auto CK01 | SBOX(2;3;04;1) @0410213243: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0410213243 : Ws → ⟪ (CK40 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ CK40 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0410213243 c4 = derive (CK40 ∷ Sb1-2-43-0 ∷ []) (Sb1-2-43-0 ∷ CK40 ∷ [])
  (rw⁻ 0 (q48 c4) ∷
   rw 1 (q243 c4) ∷
   rw 2 (q282 c4) ∷
   rw 1 (q283 c4) ∷
   rw 0 (q284 c4) ∷
   rw 1 (q245 c4) ∷
   rw 2 (q48 c4) ∷ []) Eq.refl

private
  q285 : Ws → Eqn
  q285 c4 = eqn (Sw01 ∷ Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4))
  q286 : Ws → Eqn
  q286 c4 = eqn (CK40 ∷ Sb1-2-43-0 ∷ []) (Sb1-2-43-0 ∷ CK40 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0410213243 c4)
  q287 : Ws → Eqn
  q287 c4 = eqn (Sw01 ∷ Sb1-2-43-0 ∷ []) (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4))

-- auto CK01 | SBOX(2;3;04;1) @04203243: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at04203243 : Ws → ⟪ (CK41 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CK41 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at04203243 c4 = derive (CK41 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CK41 ∷ [])
  (rw⁻ 0 (q30 c4) ∷
   rw 1 (q251 c4) ∷
   rw 2 (q285 c4) ∷
   rw 1 (q286 c4) ∷
   rw 0 (q287 c4) ∷
   rw 1 (q252 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

private
  q288 : Ws → Eqn
  q288 c4 = eqn (CK41 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CK41 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at04203243 c4)

-- F2 K1|CS23: 1 steps
lem-F2-K1∣CS23 : Ws → ⟪ (CK41 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CK41 ∷ []) ⟫ʷ
lem-F2-K1∣CS23 c4 = derive (CK41 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CK41 ∷ [])
  (rw 0 (q288 c4) ∷ []) Eq.refl

private
  q289 : Ws → Eqn
  q289 c4 = eqn (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) (wl0160 (lit c4))
  q290 : Ws → Eqn
  q290 c4 = eqn (CK41 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CK41 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at04203243 c4)
  q291 : Ws → Eqn
  q291 c4 = eqn (CK42 ∷ Sw12 ∷ []) (Sw12 ∷ CK41 ∷ []) (wl0164 (lit c4))

-- auto CK01 | SBOX(1;2;03;4) @0412203143: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0412203143 : Ws → ⟪ (CK42 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK42 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0412203143 c4 = derive (CK42 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK42 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q289 c4) ∷
   rw 2 (q170 c4) ∷
   rw 1 (q290 c4) ∷
   rw 0 (q172 c4) ∷
   rw⁻ 1 (q291 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q292 : Ws → Eqn
  q292 c4 = eqn (CK42 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK42 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0412203143 c4)

-- F2 K2|CS01: 1 steps
lem-F2-K2∣CS01 : Ws → ⟪ (CK42 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK42 ∷ []) ⟫ʷ
lem-F2-K2∣CS01 c4 = derive (CK42 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK42 ∷ [])
  (rw 0 (q292 c4) ∷ []) Eq.refl

-- auto CK01 | SBOX(2;3;04;1) @0412203143: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0412203143 : Ws → ⟪ (CK42 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CK42 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0412203143 c4 = derive (CK42 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CK42 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q289 c4) ∷
   rw 2 (q179 c4) ∷
   rw 1 (q288 c4) ∷
   rw 0 (q177 c4) ∷
   rw⁻ 1 (q291 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q293 : Ws → Eqn
  q293 c4 = eqn (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) (wl0162 (lit c4))
  q294 : Ws → Eqn
  q294 c4 = eqn (CK42 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CK42 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0412203143 c4)
  q295 : Ws → Eqn
  q295 c4 = eqn (CK43 ∷ Sw23 ∷ []) (Sw23 ∷ CK42 ∷ []) (wl0163 (lit c4))

-- auto CK01 | SBOX(2;3;04;1) @0413203142: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0413203142 : Ws → ⟪ (CK43 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK43 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0413203142 c4 = derive (CK43 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK43 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw⁻ 1 (q293 c4) ∷
   rw 2 (q176 c4) ∷
   rw 1 (q294 c4) ∷
   rw 0 (q175 c4) ∷
   rw⁻ 1 (q295 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q296 : Ws → Eqn
  q296 c4 = eqn (Sw01 ∷ CK43 ∷ []) (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑))
  q297 : Ws → Eqn
  q297 c4 = eqn (CK43 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK43 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0413203142 c4)

-- auto CK01 | SBOX(2;3;04;1) @0413213042: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0413213042 : Ws → ⟪ (CK43 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CK43 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0413213042 c4 = derive (CK43 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CK43 ∷ [])
  (rw⁻ 0 (q30 c4) ∷
   rw 1 (q296 c4) ∷
   rw 2 (q166 c4) ∷
   rw 1 (q297 c4) ∷
   rw 0 (q168 c4) ∷
   rw 1 (q296 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

private
  q298 : Ws → Eqn
  q298 c4 = eqn (Sw12 ∷ CK43 ∷ []) (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀))
  q299 : Ws → Eqn
  q299 c4 = eqn (CK43 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CK43 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0413213042 c4)

-- auto CK01 | SBOX(2;3;04;1) @04133041: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at04133041 : Ws → ⟪ (CK43 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK43 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at04133041 c4 = derive (CK43 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK43 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q298 c4) ∷
   rw 2 (q170 c4) ∷
   rw 1 (q299 c4) ∷
   rw 0 (q172 c4) ∷
   rw 1 (q298 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q300 : Ws → Eqn
  q300 c4 = eqn (CK43 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK43 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at04133041 c4)

-- F2 K3|CS01: 1 steps
lem-F2-K3∣CS01 : Ws → ⟪ (CK43 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK43 ∷ []) ⟫ʷ
lem-F2-K3∣CS01 c4 = derive (CK43 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK43 ∷ [])
  (rw 0 (q300 c4) ∷ []) Eq.refl

-- F2 K3|CS12: 1 steps
lem-F2-K3∣CS12 : Ws → ⟪ (CK43 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK43 ∷ []) ⟫ʷ
lem-F2-K3∣CS12 c4 = derive (CK43 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK43 ∷ [])
  (rw 0 (q297 c4) ∷ []) Eq.refl

private
  q301 : Ws → Eqn
  q301 c4 = eqn (CCZ134 ∷ []) (CCZ134 ∷ []) (wl0347 (lit c4))
  q302 : Ws → Eqn
  q302 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1324 ∷ []) (lem-sym23 c4)
  q303 : Ws → Eqn
  q303 c4 = eqn (CCZ134 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CCZ134 ∷ []) (lem-c124-beta-at2332 c4)
  q304 : Ws → Eqn
  q304 c4 = eqn (Bx0-1324 ∷ []) (Bx0-1234 ∷ []) (lem-sym23-at2332 c4)

-- auto BOX(0;1234) | CCZ143: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ143 : Ws → ⟪ (Bx0-1234 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ143 c4 = derive (Bx0-1234 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1234 ∷ [])
  (rw 1 (q301 c4) ∷
   rw 0 (q302 c4) ∷
   rw⁻ 0 (q303 c4) ∷
   rw 1 (q304 c4) ∷
   rw 0 (q301 c4) ∷ []) Eq.refl

private
  q305 : Ws → Eqn
  q305 c4 = eqn (CS12⁻ ∷ []) (CS12⁻ ∷ []) (wl0652 (lit c4))
  q306 : Ws → Eqn
  q306 c4 = eqn (CS12⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS12⁻ ∷ []) (lem-CSd12-beta c4)

-- auto BOX(0;1234) | CSd21: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd21 : Ws → ⟪ (Bx0-1234 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd21 c4 = derive (Bx0-1234 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Bx0-1234 ∷ [])
  (rw 1 (q305 c4) ∷
   rw⁻ 0 (q306 c4) ∷
   rw 0 (q305 c4) ∷ []) Eq.refl

private
  q307 : Ws → Eqn
  q307 c4 = eqn (Sw23 ∷ Bx0-1324 ∷ []) (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4))
  q308 : Ws → Eqn
  q308 c4 = eqn (Sw23 ∷ CS13⁻ ∷ []) (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 (lit c4))
  q309 : Ws → Eqn
  q309 c4 = eqn (Bx0-1234 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd21 c4)
  q310 : Ws → Eqn
  q310 c4 = eqn (Sw23 ∷ CS12⁻ ∷ []) (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 (lit c4))
  q311 : Ws → Eqn
  q311 c4 = eqn (Sw23 ∷ Bx0-1234 ∷ []) (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4))

-- auto BOX(0;1234) | CSd21 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd21-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd21-at2332 c4 = derive (Bx0-1324 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q307 c4) ∷
   rw 2 (q308 c4) ∷
   rw 1 (q309 c4) ∷
   rw 0 (q310 c4) ∷
   rw 1 (q311 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q312 : Ws → Eqn
  q312 c4 = eqn (CX42 ∷ Sw23 ∷ []) (Sw23 ∷ CX43 ∷ []) (wl0147 (lit c4))
  q313 : Ws → Eqn
  q313 c4 = eqn (Sw23 ∷ Bx0-1432 ∷ []) (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4))
  q314 : Ws → Eqn
  q314 c4 = eqn (CX42 ∷ Bx0-1423 ∷ CX42 ∷ []) (Bx0-1423 ∷ CCZ134 ∷ []) (lem-CX23-beta-at243243 c4)
  q315 : Ws → Eqn
  q315 c4 = eqn (Sw23 ∷ Bx0-1423 ∷ []) (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ (lit c4))

-- CX23-beta @2442: 8 steps
lem-CX23-beta-at2442 : Ws → ⟪ (CX43 ∷ Bx0-1432 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CX23-beta-at2442 c4 = derive (CX43 ∷ Bx0-1432 ∷ CX43 ∷ []) (Bx0-1432 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw⁻ 1 (q312 c4) ∷
   rw 2 (q313 c4) ∷
   rw⁻ 3 (q312 c4) ∷
   rw 1 (q314 c4) ∷
   rw 0 (q315 c4) ∷
   rw 1 (q14 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q316 : Ws → Eqn
  q316 c4 = eqn (Bx0-1234 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ143 c4)

-- auto BOX(0;1234) | CCZ143 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at2332 c4 = derive (Bx0-1324 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q307 c4) ∷
   rw 2 (q12 c4) ∷
   rw 1 (q316 c4) ∷
   rw 0 (q14 c4) ∷
   rw 1 (q311 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q317 : Ws → Eqn
  q317 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (wl0653 (lit c4))
  q318 : Ws → Eqn
  q318 c4 = eqn (Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4)
  q319 : Ws → Eqn
  q319 c4 = eqn (Sb0-1-32-4 ∷ CS13 ∷ []) (CS13 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 c4)
  q320 : Ws → Eqn
  q320 c4 = eqn (CS14⁻ ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) (CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14⁻ ∷ []) (wl0654 (lit c4))
  q321 : Ws → Eqn
  q321 c4 = eqn (CX43 ∷ CS13⁻ ∷ CX43 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) (wl0655 (lit c4))
  q322 : Ws → Eqn
  q322 c4 = eqn (CX43 ∷ CX43 ∷ []) [] (wl0656 (lit c4))
  q323 : Ws → Eqn
  q323 c4 = eqn (Bx0-1324 ∷ []) (Bx0-1342 ∷ []) (lem-sym34-at2332 c4)
  q324 : Ws → Eqn
  q324 c4 = eqn (Bx0-1342 ∷ []) (Bx0-1432 ∷ []) (lem-sym23-at233442 c4)
  q325 : Ws → Eqn
  q325 c4 = eqn (CX43 ∷ Bx0-1432 ∷ CX43 ∷ []) (Bx0-1432 ∷ CCZ124 ∷ []) (lem-CX23-beta-at2442 c4)
  q326 : Ws → Eqn
  q326 c4 = eqn (Bx0-1432 ∷ []) (Bx0-1342 ∷ []) (lem-sym23-at2442 c4)
  q327 : Ws → Eqn
  q327 c4 = eqn (Bx0-1342 ∷ []) (Bx0-1324 ∷ []) (lem-sym34-at233442 c4)
  q328 : Ws → Eqn
  q328 c4 = eqn (Bx0-1324 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at2332 c4)
  q329 : Ws → Eqn
  q329 c4 = eqn (Bx0-1324 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd21-at2332 c4)
  q330 : Ws → Eqn
  q330 c4 = eqn (CCZ124 ∷ CX43 ∷ []) (CX43 ∷ CCZ124 ∷ []) (wl0657 (lit c4))
  q331 : Ws → Eqn
  q331 c4 = eqn (CCZ124 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) (CX43 ∷ CS13⁻ ∷ CX43 ∷ CCZ124 ∷ []) (wl0658 (lit c4))
  q332 : Ws → Eqn
  q332 c4 = eqn (CCZ124 ∷ CCZ124 ∷ []) [] (wl0351 (lit c4))
  q333 : Ws → Eqn
  q333 c4 = eqn (Sb0-1-32-4 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41-at2332 c4)

-- auto SBOX(0;1;23;4) | CCZ143: 32 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143 : Ws → ⟪ (Sb0-1-23-4 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143 c4 = derive (Sb0-1-23-4 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sb0-1-23-4 ∷ [])
  (rw 1 (q317 c4) ∷
   rw 0 (q318 c4) ∷
   rw 0 (q319 c4) ∷
   re 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) ∷
   re 5 1 (CS14⁻ ∷ []) ∷
   rw 5 (q320 c4) ∷
   re 8 1 (Sb⁻0-1-4-2 ∷ []) ∷
   re 3 1 (CS14 ∷ []) ∷
   rw⁻ 2 (q321 c4) ∷
   re 6 1 (Sb0-1-4-2 ∷ []) ∷
   rw⁻ 1 (q322 c4) ∷
   rw 3 (q323 c4) ∷
   rw 3 (q324 c4) ∷
   rw 2 (q325 c4) ∷
   rw 2 (q326 c4) ∷
   rw 2 (q327 c4) ∷
   rw 2 (q328 c4) ∷
   rw 3 (q329 c4) ∷
   rw⁻ 4 (q322 c4) ∷
   rw 6 (q323 c4) ∷
   rw 6 (q324 c4) ∷
   rw 5 (q325 c4) ∷
   rw 5 (q326 c4) ∷
   rw 5 (q327 c4) ∷
   rw 5 (q328 c4) ∷
   rw⁻ 1 (q330 c4) ∷
   rw⁻ 2 (q331 c4) ∷
   rw 1 (q332 c4) ∷
   re 4 5 (Sb0-1-32-4 ∷ []) ∷
   rw 4 (q333 c4) ∷
   rw⁻ 5 (q318 c4) ∷
   rw⁻ 0 (q317 c4) ∷ []) Eq.refl

private
  q334 : Ws → Eqn
  q334 c4 = eqn (Bx0-1423 ∷ []) (Bx0-1432 ∷ []) (lem-sym34-at243243 c4)
  q335 : Ws → Eqn
  q335 c4 = eqn (Sw12 ∷ Bx0-1432 ∷ []) (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ (lit c4))

-- sym34 @12243143: 5 steps
lem-sym34-at12243143 : Ws → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-sym34-at12243143 c4 = derive (Bx0-2413 ∷ []) (Bx0-2431 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q5 c4) ∷
   rw 1 (q334 c4) ∷
   rw 0 (q335 c4) ∷
   rw 1 (q1 c4) ∷ []) Eq.refl

private
  q336 : Ws → Eqn
  q336 c4 = eqn (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ []) (wl0079 (lit c4))
  q337 : Ws → Eqn
  q337 c4 = eqn (Sw12 ∷ Bx0-2143 ∷ []) (Bx0-1243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2143⟩ (lit c4))
  q338 : Ws → Eqn
  q338 c4 = eqn (Toff412 ∷ Bx0-1243 ∷ Toff412 ∷ []) (Bx0-1243 ∷ CCZ123 ∷ []) (lem-T312-beta-at3443 c4)
  q339 : Ws → Eqn
  q339 c4 = eqn (Sw12 ∷ Bx0-1243 ∷ []) (Bx0-2143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1243⟩ (lit c4))
  q340 : Ws → Eqn
  q340 c4 = eqn (CCZ123 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ123 ∷ []) (wl0111 (lit c4))

-- T312-beta @12213443: 8 steps
lem-T312-beta-at12213443 : Ws → ⟪ (Toff412 ∷ Bx0-2143 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ CCZ123 ∷ []) ⟫ʷ
lem-T312-beta-at12213443 c4 = derive (Toff412 ∷ Bx0-2143 ∷ Toff412 ∷ []) (Bx0-2143 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q336 c4) ∷
   rw 2 (q337 c4) ∷
   rw 3 (q336 c4) ∷
   rw 1 (q338 c4) ∷
   rw 0 (q339 c4) ∷
   rw⁻ 1 (q340 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q341 : Ws → Eqn
  q341 c4 = eqn (Sw23 ∷ Toff413 ∷ []) (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 (lit c4))
  q342 : Ws → Eqn
  q342 c4 = eqn (Sw23 ∷ Bx0-3142 ∷ []) (Bx0-2143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3142⟩ (lit c4))
  q343 : Ws → Eqn
  q343 c4 = eqn (Toff412 ∷ Bx0-2143 ∷ Toff412 ∷ []) (Bx0-2143 ∷ CCZ123 ∷ []) (lem-T312-beta-at12213443 c4)
  q344 : Ws → Eqn
  q344 c4 = eqn (Sw23 ∷ Bx0-2143 ∷ []) (Bx0-3142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2143⟩ (lit c4))
  q345 : Ws → Eqn
  q345 c4 = eqn (CCZ123 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ123 ∷ []) (wl0113 (lit c4))

-- T312-beta @13213442: 8 steps
lem-T312-beta-at13213442 : Ws → ⟪ (Toff413 ∷ Bx0-3142 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ CCZ123 ∷ []) ⟫ʷ
lem-T312-beta-at13213442 c4 = derive (Toff413 ∷ Bx0-3142 ∷ Toff413 ∷ []) (Bx0-3142 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q341 c4) ∷
   rw 2 (q342 c4) ∷
   rw 3 (q341 c4) ∷
   rw 1 (q343 c4) ∷
   rw 0 (q344 c4) ∷
   rw⁻ 1 (q345 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q346 : Ws → Eqn
  q346 c4 = eqn (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) (wl0091 (lit c4))
  q347 : Ws → Eqn
  q347 c4 = eqn (Toff413 ∷ Bx0-3142 ∷ Toff413 ∷ []) (Bx0-3142 ∷ CCZ123 ∷ []) (lem-T312-beta-at13213442 c4)
  q348 : Ws → Eqn
  q348 c4 = eqn (Sw12 ∷ Bx0-3142 ∷ []) (Bx0-3241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3142⟩ (lit c4))

-- T312-beta @133441: 8 steps
lem-T312-beta-at133441 : Ws → ⟪ (Toff423 ∷ Bx0-3241 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ CCZ123 ∷ []) ⟫ʷ
lem-T312-beta-at133441 c4 = derive (Toff423 ∷ Bx0-3241 ∷ Toff423 ∷ []) (Bx0-3241 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q346 c4) ∷
   rw 2 (q2 c4) ∷
   rw 3 (q346 c4) ∷
   rw 1 (q347 c4) ∷
   rw 0 (q348 c4) ∷
   rw⁻ 1 (q340 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q349 : Ws → Eqn
  q349 c4 = eqn (Bx3-0412 ∷ []) (Bx3-0142 ∷ []) (lem-sym23-at0310243142 c4)
  q350 : Ws → Eqn
  q350 c4 = eqn (CCZ012 ∷ Bx3-0142 ∷ []) (Bx3-0142 ∷ CCZ012 ∷ []) (lem-c124-beta-at0310213442 c4)
  q351 : Ws → Eqn
  q351 c4 = eqn (Bx3-0142 ∷ []) (Bx3-0412 ∷ []) (lem-sym23-at0310213442 c4)

-- auto CCZ012 | BOX(3;0412): 3 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩ : Ws → ⟪ (CCZ012 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩ c4 = derive (CCZ012 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ CCZ012 ∷ [])
  (rw 1 (q349 c4) ∷
   rw 0 (q350 c4) ∷
   rw 0 (q351 c4) ∷ []) Eq.refl

private
  q352 : Ws → Eqn
  q352 c4 = eqn (Sw23 ∷ Bx2-0413 ∷ []) (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4))
  q353 : Ws → Eqn
  q353 c4 = eqn (CCZ012 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩ c4)
  q354 : Ws → Eqn
  q354 c4 = eqn (Sw23 ∷ Bx3-0412 ∷ []) (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4))

-- auto CCZ012 | BOX(3;0412) @2332: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 : Ws → ⟪ (CCZ013 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4 = derive (CCZ013 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q43 c4) ∷
   rw 2 (q352 c4) ∷
   rw 1 (q353 c4) ∷
   rw 0 (q354 c4) ∷
   rw 1 (q47 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

-- auto S0 | BOX(1;2034) @0110: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at0110 : Ws → ⟪ (S1 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ S1 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at0110 c4 = derive (S1 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ S1 ∷ [])
  (rw⁻ 0 (q30 c4) ∷
   rw⁻ 1 (q145 c4) ∷
   rw 2 (q220 c4) ∷
   rw 1 (q141 c4) ∷
   rw 0 (q218 c4) ∷
   rw⁻ 1 (q149 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

private
  q355 : Ws → Eqn
  q355 c4 = eqn (S1 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ S1 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at0110 c4)

-- auto S0 | BOX(1;2034) @021021: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at021021 : Ws → ⟪ (S2 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ S2 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at021021 c4 = derive (S2 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ S2 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q150 c4) ∷
   rw 2 (q216 c4) ∷
   rw 1 (q355 c4) ∷
   rw 0 (q214 c4) ∷
   rw⁻ 1 (q154 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q356 : Ws → Eqn
  q356 c4 = eqn (S2 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ S2 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at021021 c4)

-- auto S0 | BOX(1;2034) @03102132: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at03102132 : Ws → ⟪ (S3 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ S3 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at03102132 c4 = derive (S3 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ S3 ∷ [])
  (rw⁻ 0 (q10 c4) ∷
   rw⁻ 1 (q155 c4) ∷
   rw 2 (q307 c4) ∷
   rw 1 (q356 c4) ∷
   rw 0 (q311 c4) ∷
   rw⁻ 1 (q159 c4) ∷
   rw 2 (q10 c4) ∷ []) Eq.refl

private
  q357 : Ws → Eqn
  q357 c4 = eqn (Sw34 ∷ Bx0-1423 ∷ []) (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4))
  q358 : Ws → Eqn
  q358 c4 = eqn (S3 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ S3 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at03102132 c4)
  q359 : Ws → Eqn
  q359 c4 = eqn (Sw34 ∷ Bx0-1324 ∷ []) (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4))

-- auto S0 | BOX(1;2034) @0410213243: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at0410213243 : Ws → ⟪ (S4 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at0410213243 c4 = derive (S4 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ S4 ∷ [])
  (rw⁻ 0 (q48 c4) ∷
   rw⁻ 1 (q160 c4) ∷
   rw 2 (q357 c4) ∷
   rw 1 (q358 c4) ∷
   rw 0 (q359 c4) ∷
   rw⁻ 1 (q164 c4) ∷
   rw 2 (q48 c4) ∷ []) Eq.refl

private
  q360 : Ws → Eqn
  q360 c4 = eqn (Sw01 ∷ Bx1-0423 ∷ []) (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4))
  q361 : Ws → Eqn
  q361 c4 = eqn (S4 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at0410213243 c4)
  q362 : Ws → Eqn
  q362 c4 = eqn (Sw01 ∷ Bx0-1423 ∷ []) (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4))

-- auto S0 | BOX(1;2034) @04203243: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at04203243 : Ws → ⟪ (S4 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at04203243 c4 = derive (S4 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ S4 ∷ [])
  (rw⁻ 0 (q30 c4) ∷
   rw 1 (q165 c4) ∷
   rw 2 (q360 c4) ∷
   rw 1 (q361 c4) ∷
   rw 0 (q362 c4) ∷
   rw 1 (q165 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

private
  q363 : Ws → Eqn
  q363 c4 = eqn (Sw12 ∷ Bx2-0413 ∷ []) (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4))
  q364 : Ws → Eqn
  q364 c4 = eqn (S4 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at04203243 c4)
  q365 : Ws → Eqn
  q365 c4 = eqn (Sw12 ∷ Bx1-0423 ∷ []) (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4))

-- auto S0 | BOX(1;2034) @0412203143: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at0412203143 : Ws → ⟪ (S4 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at0412203143 c4 = derive (S4 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ S4 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q169 c4) ∷
   rw 2 (q363 c4) ∷
   rw 1 (q364 c4) ∷
   rw 0 (q365 c4) ∷
   rw 1 (q169 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q366 : Ws → Eqn
  q366 c4 = eqn (X4 ∷ X4 ∷ []) [] (wl0283 (lit c4))
  q367 : Ws → Eqn
  q367 c4 = eqn (Bx2-0413 ∷ []) (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4)
  q368 : Ws → Eqn
  q368 c4 = eqn (X4 ∷ Bx2-4013 ∷ X4 ∷ []) (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4)
  q369 : Ws → Eqn
  q369 c4 = eqn (Bx2-4013 ∷ []) (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4)
  q370 : Ws → Eqn
  q370 c4 = eqn (CCZ013 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4)
  q371 : Ws → Eqn
  q371 c4 = eqn (S4 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at0412203143 c4)
  q372 : Ws → Eqn
  q372 c4 = eqn (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) (wp0296 c4)
  q373 : Ws → Eqn
  q373 c4 = eqn (CCZ013 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CCZ013 ∷ []) (wp0297 c4)
  q374 : Ws → Eqn
  q374 c4 = eqn (CCZ013 ∷ CCZ013 ∷ []) [] (wl0659 (lit c4))
  q375 : Ws → Eqn
  q375 c4 = eqn (Toff314 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ Toff314 ∷ []) (wl0660 (lit c4))
  q376 : Ws → Eqn
  q376 c4 = eqn (CS03 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS03 ∷ []) (wp0298 c4)
  q377 : Ws → Eqn
  q377 c4 = eqn (CS03⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS03⁻ ∷ []) (wp0299 c4)

-- F4 iI^0|CS01^1: 24 steps
lem-F4-iIᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-iIᵖ0∣CS01ᵖ1 c4 = derive (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 4 (q366 c4) ∷
   rw 3 (q367 c4) ∷
   rw 2 (q368 c4) ∷
   rw 3 (q369 c4) ∷
   rw 2 (q370 c4) ∷
   rw 1 (q371 c4) ∷
   rw⁻ 2 (q366 c4) ∷
   rw 1 (q367 c4) ∷
   rw 0 (q368 c4) ∷
   rw 1 (q369 c4) ∷
   rw 0 (q370 c4) ∷
   rw 4 (q372 c4) ∷
   rw 1 (q373 c4) ∷
   rw 4 (q374 c4) ∷
   rw⁻ 1 (q375 c4) ∷
   re 5 1 (CS03 ∷ []) ∷
   rw⁻ 2 (q376 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 3 (q375 c4) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw⁻ 4 (q377 c4) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

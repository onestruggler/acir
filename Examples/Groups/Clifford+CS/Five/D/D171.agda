{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D171 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0008 ; wl0017 ; wl0030 ; wl0031 ; wl0034 ; wl0076 ; wl0078 ; wl0079 ; wl0084 ; wl0091 ; wl0111 ; wl0113 ; wl0127 ; wl0128 ; wl0132 ; wl0136 ; wl0140 ; wl0144 ; wl0147 ; wl0160 ; wl0162 ; wl0163 ; wl0164 ; wl0189 ; wl0230 ; wl0283 ; wl0332 ; wl0347 ; wl0351 ; wl0372 ; wl0373 ; wl0504 ; wl0516 ; wl0609 ; wl0612 ; wl0613 ; wl0625 ; wl0626 ; wl0637 ; wl0638 ; wl0639 ; wl0640 ; wl0641 ; wl0642 ; wl0643 ; wl0644 ; wl0645 ; wl0646 ; wl0647 ; wl0648 ; wl0649 ; wl0650 ; wl0651 ; wl0652 ; wl0653 ; wl0654 ; wl0655 ; wl0656 ; wl0657 ; wl0658 ; wl0659 ; wl0660 ; wp0267 ; wp0286 ; wp0287 ; wp0288 ; wp0289 ; wp0290 ; wp0291 ; wp0292 ; wp0293 ; wp0294 ; wp0295 ; wp0296 ; wp0297 ; wp0298 ; wp0299)
open import Examples.Groups.Clifford+CS.Five.Chain
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
-- sym23 @133441: 5 steps
lem-sym23-at133441 : Ws → ⟪ (Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-sym23-at133441 c4 = run b0
  where
  b0 : Chain (Bx0-3241 ∷ []) (Bx0-3421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-3142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3241⟩ (lit c4)) ▸
       at 1 1 (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4) ▸
       at 0 2 (Bx0-3421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3412⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ342 @12243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at12243143 : Ws → ⟪ (Bx0-2413 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-2413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-2413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at243243 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 1 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ342 @13243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at13243142 : Ws → ⟪ (Bx0-3412 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-3412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-3412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Bx0-2413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at12243143 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 1 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ342 @13243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at13243241 : Ws → ⟪ (Bx0-3421 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-3421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at13243241 c4 = run b0
  where
  b0 : Chain (Bx0-3421 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-3421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-3412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3421⟩ (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ Bx0-3412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at13243142 c4) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 1 2 (Bx0-3421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3412⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | TOFF012 @12243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at12243143 : Ws → ⟪ (Bx0-2413 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Bx0-2413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ Toff024 ∷ []) (Toff024 ∷ Bx0-2413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4)) ▸
       at 2 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 (lit c4)) ▸
       at 1 2 (Toff014 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at243243 c4) ▸
       at 0 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 (lit c4)) ▸
       at 1 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | TOFF012 @13243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at13243142 : Ws → ⟪ (Bx0-3412 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Bx0-3412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ Toff034 ∷ []) (Toff034 ∷ Bx0-3412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4)) ▸
       at 2 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 (lit c4)) ▸
       at 1 2 (Toff024 ∷ Bx0-2413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at12243143 c4) ▸
       at 0 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 (lit c4)) ▸
       at 1 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | TOFF012 @13243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at13243241 : Ws → ⟪ (Bx0-3421 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Bx0-3421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at13243241 c4 = run b0
  where
  b0 : Chain (Bx0-3421 ∷ Toff034 ∷ []) (Toff034 ∷ Bx0-3421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-3412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3421⟩ (lit c4)) ▸
       at 2 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 (lit c4)) ▸
       at 1 2 (Toff034 ∷ Bx0-3412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at13243142 c4) ▸
       at 0 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 (lit c4)) ▸
       at 1 2 (Bx0-3421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3412⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- beta-inv @12243143: 5 steps
lem-beta-inv-at12243143 : Ws → ⟪ (Bx0-2413 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ Bx0-2413 ∷ []) []
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4)) ▸
       at 2 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4)) ▸
       at 1 2 [] (lem-beta-inv-at243243 c4) ▸
       at 0 2 [] (wl0001 (lit c4)) ▸ done


-- beta-inv @13243142: 5 steps
lem-beta-inv-at13243142 : Ws → ⟪ (Bx0-3412 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ Bx0-3412 ∷ []) []
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4)) ▸
       at 2 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4)) ▸
       at 1 2 [] (lem-beta-inv-at12243143 c4) ▸
       at 0 2 [] (wl0006 (lit c4)) ▸ done


-- beta-inv @13243241: 5 steps
lem-beta-inv-at13243241 : Ws → ⟪ (Bx0-3421 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at13243241 c4 = run b0
  where
  b0 : Chain (Bx0-3421 ∷ Bx0-3421 ∷ []) []
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-3412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3421⟩ (lit c4)) ▸
       at 2 2 (Bx0-3412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3421⟩ (lit c4)) ▸
       at 1 2 [] (lem-beta-inv-at13243142 c4) ▸
       at 0 2 [] (wl0001 (lit c4)) ▸ done


-- beta-inv @0110: 5 steps
lem-beta-inv-at0110 : Ws → ⟪ (Bx1-0234 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ Bx1-0234 ∷ []) []
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4)) ▸
       at 1 2 [] (lem-beta-inv c4) ▸
       at 0 2 [] (wl0002 (lit c4)) ▸ done


-- beta-inv @021021: 5 steps
lem-beta-inv-at021021 : Ws → ⟪ (Bx2-0134 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ Bx2-0134 ∷ []) []
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4)) ▸
       at 2 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4)) ▸
       at 1 2 [] (lem-beta-inv-at0110 c4) ▸
       at 0 2 [] (wl0001 (lit c4)) ▸ done


-- beta-inv @03102132: 5 steps
lem-beta-inv-at03102132 : Ws → ⟪ (Bx3-0124 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ Bx3-0124 ∷ []) []
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ (lit c4)) ▸
       at 2 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ (lit c4)) ▸
       at 1 2 [] (lem-beta-inv-at021021 c4) ▸
       at 0 2 [] (wl0006 (lit c4)) ▸ done


-- beta-inv @032032: 5 steps
lem-beta-inv-at032032 : Ws → ⟪ (Bx3-1024 ∷ Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ Bx3-1024 ∷ []) []
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1024⟩ (lit c4)) ▸
       at 2 2 (Bx3-0124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1024⟩ (lit c4)) ▸
       at 1 2 [] (lem-beta-inv-at03102132 c4) ▸
       at 0 2 [] (wl0002 (lit c4)) ▸ done


-- beta-inv @03122031: 5 steps
lem-beta-inv-at03122031 : Ws → ⟪ (Bx3-2014 ∷ Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at03122031 c4 = run b0
  where
  b0 : Chain (Bx3-2014 ∷ Bx3-2014 ∷ []) []
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-1024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2014⟩ (lit c4)) ▸
       at 2 2 (Bx3-1024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2014⟩ (lit c4)) ▸
       at 1 2 [] (lem-beta-inv-at032032 c4) ▸
       at 0 2 [] (wl0001 (lit c4)) ▸ done


-- beta-inv @03122130: 5 steps
lem-beta-inv-at03122130 : Ws → ⟪ (Bx3-2104 ∷ Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at03122130 c4 = run b0
  where
  b0 : Chain (Bx3-2104 ∷ Bx3-2104 ∷ []) []
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-2014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2104⟩ (lit c4)) ▸
       at 2 2 (Bx3-2014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2104⟩ (lit c4)) ▸
       at 1 2 [] (lem-beta-inv-at03122031 c4) ▸
       at 0 2 [] (wl0002 (lit c4)) ▸ done


-- auto CCZ012 | TOFF342 @2332: 7 steps
lem-auto-CCZ012-∣-TOFF342-at2332 : Ws → ⟪ (CCZ013 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at2332 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 2 2 (Toff324 ∷ Sw23 ∷ []) (wl0127 (lit c4)) ▸
       at 1 2 (Toff324 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF342 c4) ▸
       at 0 2 (Toff234 ∷ Sw23 ∷ []) (wl0144 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CCZ012 | TOFF342 @243243: 7 steps
lem-auto-CCZ012-∣-TOFF342-at243243 : Ws → ⟪ (CCZ014 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at243243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 (lit c4)) ▸
       at 2 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 (lit c4)) ▸
       at 1 2 (Toff234 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at2332 c4) ▸
       at 0 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CCZ012 | TOFF342 @0110243243: 7 steps
lem-auto-CCZ012-∣-TOFF342-at0110243243 : Ws → ⟪ (CCZ014 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at0110243243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 (lit c4)) ▸
       at 2 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 1 2 (Toff234 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at243243 c4) ▸
       at 0 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CCZ012 | TOFF342 @0210243143: 7 steps
lem-auto-CCZ012-∣-TOFF342-at0210243143 : Ws → ⟪ (CCZ024 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at0210243143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 2 2 (Toff234 ∷ Sw12 ∷ []) (wl0136 (lit c4)) ▸
       at 1 2 (Toff234 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at0110243243 c4) ▸
       at 0 2 (Toff134 ∷ Sw12 ∷ []) (wl0140 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | TOFF342 @02243043: 7 steps
lem-auto-CCZ012-∣-TOFF342-at02243043 : Ws → ⟪ (CCZ124 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ124 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at02243043 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4)) ▸
       at 2 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 (lit c4)) ▸
       at 1 2 (Toff134 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at0210243143 c4) ▸
       at 0 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CCZ012 | TOFF342 @12243143: 7 steps
lem-auto-CCZ012-∣-TOFF342-at12243143 : Ws → ⟪ (CCZ024 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at12243143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 2 2 (Toff234 ∷ Sw12 ∷ []) (wl0136 (lit c4)) ▸
       at 1 2 (Toff234 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at243243 c4) ▸
       at 0 2 (Toff134 ∷ Sw12 ∷ []) (wl0140 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | TOFF342 @0112243043: 7 steps
lem-auto-CCZ012-∣-TOFF342-at0112243043 : Ws → ⟪ (CCZ124 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ124 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at0112243043 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4)) ▸
       at 2 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 (lit c4)) ▸
       at 1 2 (Toff134 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at12243143 c4) ▸
       at 0 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- F1 toff-ccz: 190 steps
lem-F1-toff-ccz : Ws → ⟪ (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-F1-toff-ccz c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (run b23)))))))))))))))))))))))
  where
  b0 : Chain (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ [])
  b0 = at 3 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 6 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 9 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 13 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 17 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 21 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 26 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 30 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸ done

  b1 : Chain (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ [])
  b1 = at 34 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 40 2 (CCZ234 ∷ []) (lem-SB2-at02132031 c4) ▸
       at 44 2 (CCZ234 ∷ []) (lem-SB2-at02132031 c4) ▸
       at 48 2 (CCZ234 ∷ []) (lem-SB2-at02132031 c4) ▸
       at 53 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 56 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 59 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 63 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸ done

  b2 : Chain (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ [])
  b2 = at 67 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 71 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 76 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 80 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 84 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 88 2 (CCZ234 ∷ []) (lem-SB2-at02132031 c4) ▸
       at 92 2 (CCZ234 ∷ []) (lem-SB2-at02132031 c4) ▸
       at 96 2 (CCZ234 ∷ []) (lem-SB2-at02132031 c4) ▸ done

  b3 : Chain (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ [])
  b3 = at 102 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 105 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 108 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 112 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 116 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 120 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 125 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 129 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸ done

  b4 : Chain (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ [])
  b4 = at 133 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 2 4 (Toff104 ∷ []) (wp0267 c4) ▸
       at 5 4 (Toff104 ∷ []) (wp0267 c4) ▸
       at 6 4 (Toff214 ∷ []) (wl0612 (lit c4)) ▸
       at 7 4 (Toff124 ∷ []) (wl0613 (lit c4)) ▸
       at 8 4 (Toff214 ∷ []) (wl0612 (lit c4)) ▸
       at 10 4 (Toff214 ∷ []) (wl0612 (lit c4)) ▸
       at 11 4 (Toff124 ∷ []) (wl0613 (lit c4)) ▸ done

  b5 : Chain (CK40 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CK40 ∷ S4 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ [])
  b5 = at 12 4 (Toff214 ∷ []) (wl0612 (lit c4)) ▸
       at 15 4 (Toff324 ∷ []) (wl0625 (lit c4)) ▸
       at 16 4 (Toff234 ∷ []) (wl0626 (lit c4)) ▸
       at 17 4 (Toff324 ∷ []) (wl0625 (lit c4)) ▸
       at 19 4 (Toff104 ∷ []) (wp0267 c4) ▸
       at 22 4 (Toff104 ∷ []) (wp0267 c4) ▸
       at 23 4 (Toff214 ∷ []) (wl0612 (lit c4)) ▸
       at 24 4 (Toff124 ∷ []) (wl0613 (lit c4)) ▸ done

  b6 : Chain (CK40 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CK40 ∷ S4 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CK40 ∷ S4 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CK40 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ [])
  b6 = at 25 4 (Toff214 ∷ []) (wl0612 (lit c4)) ▸
       at 27 4 (Toff214 ∷ []) (wl0612 (lit c4)) ▸
       at 28 4 (Toff124 ∷ []) (wl0613 (lit c4)) ▸
       at 29 4 (Toff214 ∷ []) (wl0612 (lit c4)) ▸
       at 30 4 (Toff324 ∷ []) (wl0625 (lit c4)) ▸
       at 31 4 (Toff234 ∷ []) (wl0626 (lit c4)) ▸
       at 32 4 (Toff324 ∷ []) (wl0625 (lit c4)) ▸
       at 35 4 (Toff104 ∷ []) (wp0267 c4) ▸ done

  b7 : Chain (CK40 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CK40 ∷ S4 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CK40 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ Bx3-0124 ∷ CK40 ∷ S4 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CK40 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CK40 ∷ S4 ∷ [])
  b7 = at 38 4 (Toff104 ∷ []) (wp0267 c4) ▸
       at 39 4 (Toff214 ∷ []) (wl0612 (lit c4)) ▸
       at 40 4 (Toff124 ∷ []) (wl0613 (lit c4)) ▸
       at 41 4 (Toff214 ∷ []) (wl0612 (lit c4)) ▸
       at 43 4 (Toff214 ∷ []) (wl0612 (lit c4)) ▸
       at 44 4 (Toff124 ∷ []) (wl0613 (lit c4)) ▸
       at 45 4 (Toff214 ∷ []) (wl0612 (lit c4)) ▸
       at 1 12 (Bx3-0124 ∷ []) (lem-boxify-10 c4) ▸ done

  b8 : Chain (CK40 ∷ Bx3-0124 ∷ CK40 ∷ S4 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CK40 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CK40 ∷ S4 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx2-0134 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ [])
  b8 = at 7 12 (Bx3-0124 ∷ []) (lem-boxify-11 c4) ▸
       at 6 3 (Bx3-0124 ∷ []) (lem-boxify-12 c4) ▸
       at 4 5 (Bx2-0134 ∷ []) (lem-boxify-13 c4) ▸
       at 6 12 (Bx3-0124 ∷ []) (lem-boxify-14 c4) ▸
       at 0 4 (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ []) (lem-CKbox c4) ▸
       at 0 3 (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) (lem-KB-form c4) ▸
       at 5 4 (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ []) (lem-CKbox c4) ▸
       at 5 3 (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) (lem-KB-form c4) ▸ done

  b9 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx2-0134 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx2-1304 ∷ Bx3-2104 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ [])
  b9 = at 4 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0230 (lit c4))) ▸
       at 5 1 (Toff312 ∷ []) (wl0609 (lit c4)) ▸
       at 7 1 (Toff312 ∷ []) (wl0609 (lit c4)) ▸
       at 6 1 (Bx2-1034 ∷ []) (lem-sym12-at021021 c4) ▸
       at 6 1 (Bx2-1304 ∷ []) (lem-sym23-at0220 c4) ▸
       at 6 1 (Bx2-3104 ∷ []) (lem-sym12-at022330 c4) ▸
       at 5 3 (Bx2-3104 ∷ Bx3-2104 ∷ []) (lem-TW-at02132130 c4) ▸
       at 5 1 (Bx2-1304 ∷ []) (lem-sym12-at02132130 c4) ▸ done

  b10 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx2-1304 ∷ Bx3-2104 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-2104 ∷ Toff034 ∷ Toff034 ∷ Bx2-3401 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ [])
  b10 = at 5 1 (Bx2-1034 ∷ []) (lem-sym23-at022330 c4) ▸
       at 5 1 (Bx2-0134 ∷ []) (lem-sym12-at0220 c4) ▸
       at 5 2 (Bx3-2104 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0214⟩-at021021 c4) ▸
       at 6 0 (Toff034 ∷ Toff034 ∷ []) (sym (wp0286 c4)) ▸
       at 8 1 (Bx2-0314 ∷ []) (lem-sym23-at021021 c4) ▸
       at 8 1 (Bx2-0341 ∷ []) (lem-sym34-at02102331 c4) ▸
       at 8 1 (Bx2-3041 ∷ []) (lem-sym12-at0210233441 c4) ▸
       at 8 1 (Bx2-3401 ∷ []) (lem-sym23-at0213203441 c4) ▸ done

  b11 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-2104 ∷ Toff034 ∷ Toff034 ∷ Bx2-3401 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-2104 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff312 ∷ Bx2-0134 ∷ Toff312 ∷ Toff034 ∷ [])
  b11 = at 7 3 (Bx2-3401 ∷ CCZ134 ∷ []) (lem-T312-beta-at0213243041 c4) ▸
       at 7 1 (Bx2-3041 ∷ []) (lem-sym23-at0213243041 c4) ▸
       at 7 1 (Bx2-3014 ∷ []) (lem-sym34-at0213203441 c4) ▸
       at 7 1 (Bx2-0314 ∷ []) (lem-sym12-at02132031 c4) ▸
       at 7 1 (Bx2-0134 ∷ []) (lem-sym23-at02102331 c4) ▸
       at 7 2 (CCZ134 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at021021 c4) ▸
       at 8 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0230 (lit c4))) ▸
       at 9 1 (Toff312 ∷ []) (wl0609 (lit c4)) ▸ done

  b12 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-2104 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff312 ∷ Bx2-0134 ∷ Toff312 ∷ Toff034 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-2104 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx2-0134 ∷ Bx3-2104 ∷ Toff034 ∷ [])
  b12 = at 11 1 (Toff312 ∷ []) (wl0609 (lit c4)) ▸
       at 10 1 (Bx2-1034 ∷ []) (lem-sym12-at021021 c4) ▸
       at 10 1 (Bx2-1304 ∷ []) (lem-sym23-at0220 c4) ▸
       at 10 1 (Bx2-3104 ∷ []) (lem-sym12-at022330 c4) ▸
       at 9 3 (Bx2-3104 ∷ Bx3-2104 ∷ []) (lem-TW-at02132130 c4) ▸
       at 9 1 (Bx2-1304 ∷ []) (lem-sym12-at02132130 c4) ▸
       at 9 1 (Bx2-1034 ∷ []) (lem-sym23-at022330 c4) ▸
       at 9 1 (Bx2-0134 ∷ []) (lem-sym12-at0220 c4) ▸ done

  b13 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-2104 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx2-0134 ∷ Bx3-2104 ∷ Toff034 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-2104 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx3-2104 ∷ Toff034 ∷ Bx2-3041 ∷ CCZ134 ∷ [])
  b13 = at 9 2 (Bx3-2104 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0214⟩-at021021 c4) ▸
       at 10 0 (Toff034 ∷ Toff034 ∷ []) (sym (wp0286 c4)) ▸
       at 12 1 (Bx2-0314 ∷ []) (lem-sym23-at021021 c4) ▸
       at 12 1 (Bx2-0341 ∷ []) (lem-sym34-at02102331 c4) ▸
       at 12 1 (Bx2-3041 ∷ []) (lem-sym12-at0210233441 c4) ▸
       at 12 1 (Bx2-3401 ∷ []) (lem-sym23-at0213203441 c4) ▸
       at 11 3 (Bx2-3401 ∷ CCZ134 ∷ []) (lem-T312-beta-at0213243041 c4) ▸
       at 11 1 (Bx2-3041 ∷ []) (lem-sym23-at0213243041 c4) ▸ done

  b14 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-2104 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx3-2104 ∷ Toff034 ∷ Bx2-3041 ∷ CCZ134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-2104 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Toff034 ∷ Bx3-0241 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ [])
  b14 = at 11 1 (Bx2-3014 ∷ []) (lem-sym34-at0213203441 c4) ▸
       at 11 1 (Bx2-0314 ∷ []) (lem-sym12-at02132031 c4) ▸
       at 11 1 (Bx2-0134 ∷ []) (lem-sym23-at02102331 c4) ▸
       at 11 2 (CCZ134 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at021021 c4) ▸
       at 9 0 (Toff034 ∷ Toff034 ∷ []) (sym (wp0286 c4)) ▸
       at 11 1 (Bx3-2014 ∷ []) (lem-sym23-at03122130 c4) ▸
       at 11 1 (Bx3-2041 ∷ []) (lem-sym34-at03122031 c4) ▸
       at 11 1 (Bx3-0241 ∷ []) (lem-sym12-at0312203441 c4) ▸ done

  b15 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-2104 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Toff034 ∷ Bx3-0241 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-2104 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-3421 ∷ CCZ134 ∷ Bx3-2104 ∷ Bx2-0134 ∷ [])
  b15 = at 11 1 (Bx3-0421 ∷ []) (lem-sym23-at03103441 c4) ▸
       at 10 3 (Bx3-0421 ∷ Bx0-3421 ∷ []) (lem-TW-at0310243241 c4) ▸
       at 10 1 (Bx3-0241 ∷ []) (lem-sym23-at0310243241 c4) ▸
       at 10 1 (Bx3-0214 ∷ []) (lem-sym34-at03103441 c4) ▸
       at 10 1 (Bx3-2014 ∷ []) (lem-sym12-at031031 c4) ▸
       at 10 1 (Bx3-2104 ∷ []) (lem-sym23-at03122031 c4) ▸
       at 10 2 (Bx0-3421 ∷ Bx3-2104 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03122130 c4) ▸
       at 11 2 (CCZ134 ∷ Bx3-2104 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at03122130 c4) ▸ done

  b16 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-2104 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-3421 ∷ CCZ134 ∷ Bx3-2104 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx3-0241 ∷ Bx0-3421 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx0-3421 ∷ Bx3-2104 ∷ Bx2-0134 ∷ [])
  b16 = at 10 2 (CCZ134 ∷ Bx0-3421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at13243241 c4) ▸
       at 5 0 (Toff034 ∷ Toff034 ∷ []) (sym (wp0286 c4)) ▸
       at 7 1 (Bx3-2014 ∷ []) (lem-sym23-at03122130 c4) ▸
       at 7 1 (Bx3-2041 ∷ []) (lem-sym34-at03122031 c4) ▸
       at 7 1 (Bx3-0241 ∷ []) (lem-sym12-at0312203441 c4) ▸
       at 7 1 (Bx3-0421 ∷ []) (lem-sym23-at03103441 c4) ▸
       at 6 3 (Bx3-0421 ∷ Bx0-3421 ∷ []) (lem-TW-at0310243241 c4) ▸
       at 6 1 (Bx3-0241 ∷ []) (lem-sym23-at0310243241 c4) ▸ done

  b17 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx3-0241 ∷ Bx0-3421 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx0-3421 ∷ Bx3-2104 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-3421 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Toff034 ∷ Bx3-2014 ∷ Toff034 ∷ CCZ134 ∷ Bx0-3421 ∷ Bx3-2104 ∷ Bx2-0134 ∷ [])
  b17 = at 6 1 (Bx3-0214 ∷ []) (lem-sym34-at03103441 c4) ▸
       at 6 1 (Bx3-2014 ∷ []) (lem-sym12-at031031 c4) ▸
       at 6 1 (Bx3-2104 ∷ []) (lem-sym23-at03122031 c4) ▸
       at 6 2 (Bx0-3421 ∷ Bx3-2104 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03122130 c4) ▸
       at 7 2 (CCZ134 ∷ Bx3-2104 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at03122130 c4) ▸
       at 8 2 (Toff312 ∷ Bx3-2104 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at03122130 c4) ▸
       at 9 0 (Toff034 ∷ Toff034 ∷ []) (sym (wp0286 c4)) ▸
       at 11 1 (Bx3-2014 ∷ []) (lem-sym23-at03122130 c4) ▸ done

  b18 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-3421 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Toff034 ∷ Bx3-2014 ∷ Toff034 ∷ CCZ134 ∷ Bx0-3421 ∷ Bx3-2104 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-3421 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx3-2104 ∷ Bx0-3421 ∷ CCZ134 ∷ Bx0-3421 ∷ Bx3-2104 ∷ Bx2-0134 ∷ [])
  b18 = at 11 1 (Bx3-2041 ∷ []) (lem-sym34-at03122031 c4) ▸
       at 11 1 (Bx3-0241 ∷ []) (lem-sym12-at0312203441 c4) ▸
       at 11 1 (Bx3-0421 ∷ []) (lem-sym23-at03103441 c4) ▸
       at 10 3 (Bx3-0421 ∷ Bx0-3421 ∷ []) (lem-TW-at0310243241 c4) ▸
       at 10 1 (Bx3-0241 ∷ []) (lem-sym23-at0310243241 c4) ▸
       at 10 1 (Bx3-0214 ∷ []) (lem-sym34-at03103441 c4) ▸
       at 10 1 (Bx3-2014 ∷ []) (lem-sym12-at031031 c4) ▸
       at 10 1 (Bx3-2104 ∷ []) (lem-sym23-at03122031 c4) ▸ done

  b19 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-3421 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx3-2104 ∷ Bx0-3421 ∷ CCZ134 ∷ Bx0-3421 ∷ Bx3-2104 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff312 ∷ Bx0-3241 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx0-3421 ∷ Bx3-2104 ∷ Bx0-3421 ∷ Bx3-2104 ∷ Bx2-0134 ∷ [])
  b19 = at 10 2 (Bx0-3421 ∷ Bx3-2104 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03122130 c4) ▸
       at 11 2 (CCZ134 ∷ Bx3-2104 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at03122130 c4) ▸
       at 10 2 (CCZ134 ∷ Bx0-3421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at13243241 c4) ▸
       at 6 2 (CCZ134 ∷ Bx0-3421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at13243241 c4) ▸
       at 7 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0230 (lit c4))) ▸
       at 8 1 (Toff312 ∷ []) (wl0609 (lit c4)) ▸
       at 10 1 (Toff312 ∷ []) (wl0609 (lit c4)) ▸
       at 9 1 (Bx0-3241 ∷ []) (lem-sym23-at13243241 c4) ▸ done

  b20 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff312 ∷ Bx0-3241 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx0-3421 ∷ Bx3-2104 ∷ Bx0-3421 ∷ Bx3-2104 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx0-3421 ∷ CCZ124 ∷ Toff034 ∷ CCZ134 ∷ Bx0-3421 ∷ Bx3-2104 ∷ Bx0-3421 ∷ Bx3-2104 ∷ Bx2-0134 ∷ [])
  b20 = at 9 1 (Bx0-3214 ∷ []) (lem-sym34-at133441 c4) ▸
       at 9 1 (Bx0-2314 ∷ []) (lem-sym12-at1331 c4) ▸
       at 9 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 8 3 (Bx0-2134 ∷ CCZ124 ∷ []) (lem-T312-beta-at1221 c4) ▸
       at 8 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 8 1 (Bx0-2341 ∷ []) (lem-sym34-at122331 c4) ▸
       at 8 1 (Bx0-3241 ∷ []) (lem-sym12-at12233441 c4) ▸
       at 8 1 (Bx0-3421 ∷ []) (lem-sym23-at133441 c4) ▸ done

  b21 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx0-3421 ∷ CCZ124 ∷ Toff034 ∷ CCZ134 ∷ Bx0-3421 ∷ Bx3-2104 ∷ Bx0-3421 ∷ Bx3-2104 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ CCZ124 ∷ Toff034 ∷ CCZ134 ∷ Bx0-3214 ∷ Bx2-0134 ∷ [])
  b21 = at 8 2 (CCZ124 ∷ Bx0-3421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at13243241 c4) ▸
       at 9 2 (Toff034 ∷ Bx0-3421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at13243241 c4) ▸
       at 10 2 (CCZ134 ∷ Bx0-3421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at13243241 c4) ▸
       at 11 2 [] (lem-beta-inv-at13243241 c4) ▸
       at 11 2 (Bx0-3421 ∷ Bx3-2104 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03122130 c4) ▸
       at 12 2 [] (lem-beta-inv-at03122130 c4) ▸
       at 11 1 (Bx0-3241 ∷ []) (lem-sym23-at13243241 c4) ▸
       at 11 1 (Bx0-3214 ∷ []) (lem-sym34-at133441 c4) ▸ done

  b22 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ CCZ124 ∷ Toff034 ∷ CCZ134 ∷ Bx0-3214 ∷ Bx2-0134 ∷ []) (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ Bx0-1234 ∷ Bx2-0134 ∷ [])
  b22 = at 11 1 (Bx0-2314 ∷ []) (lem-sym12-at1331 c4) ▸
       at 11 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 11 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 8 2 (Toff034 ∷ CCZ124 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at02243043 c4) ▸
       at 6 2 (Toff312 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0637 (lit c4)) ▸
       at 8 2 (Toff034 ∷ CCZ134 ∷ []) (wp0287 c4) ▸
       at 7 2 (Toff034 ∷ CCZ124 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at0112243043 c4) ▸
       at 0 4 (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ []) (sym (lem-KB-form c4)) ▸ done

  b23 : Chain (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ Bx0-1234 ∷ Bx2-0134 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  b23 = at 3 4 (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ []) (sym (lem-KB-form c4)) ▸
       at 2 2 [] (wl0189 (lit c4)) ▸
       at 1 2 [] (lem-beta-inv-at03102132 c4) ▸
       at 0 2 [] (wl0638 (lit c4)) ▸
       at 0 4 [] (wl0639 (lit c4)) ▸
       at 0 2 (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (sym (lem-F1-toff-ccz-nf-of-rhs c4)) ▸ done


-- auto S0 | BOX(1;2034): 6 steps
lem-auto-S0-∣-BOX⟨1·2034⟩ : Ws → ⟪ (S0 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩ c4 = run b0
  where
  b0 : Chain (S0 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ S0 ∷ [])
  b0 = at 1 1 (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) (lem-beta-T-at011220 c4) ▸
       at 0 2 (Toff102 ∷ S0 ∷ []) (wl0504 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ S0 ∷ []) (c₁ (S) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 2 2 (Toff102 ∷ S0 ∷ []) (wl0504 (lit c4)) ▸
       at 3 2 (CCZ134 ∷ S0 ∷ []) (c₁ (S) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 0 4 (Bx1-2034 ∷ []) (sym (lem-beta-T-at011220 c4)) ▸ done


-- auto S0 | SBOX(1;2;03;4): 11 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩ : Ws → ⟪ (S0 ∷ Sb1-2-03-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-03-4 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (S0 ∷ Sb1-2-03-4 ∷ []) (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ S0 ∷ CS24⁻ ∷ [])
  b0 = at 1 1 (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ Sb⁻1-2-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-2034 ∷ S0 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (Toff403 ∷ S0 ∷ []) (wp0288 c4) ▸
       at 3 1 (CS24 ∷ []) (refl) ▸
       at 2 2 (CS24 ∷ S0 ∷ []) (sym (wl0640 (lit c4))) ▸
       at 2 1 (Sb1-2-4-3 ∷ []) (refl) ▸
       at 3 2 (Toff403 ∷ S0 ∷ []) (wp0288 c4) ▸
       at 5 1 (CS24⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ S0 ∷ CS24⁻ ∷ []) (Sb1-2-03-4 ∷ S0 ∷ [])
  b1 = at 4 2 (CS24⁻ ∷ S0 ∷ []) (sym (wl0641 (lit c4))) ▸
       at 4 1 (Sb⁻1-2-4-3 ∷ []) (refl) ▸
       at 0 5 (Sb1-2-03-4 ∷ []) (refl) ▸ done


-- auto S0 | SBOX(1;2;03;4) @0110: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0110 : Ws → ⟪ (S1 ∷ Sb0-2-13-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-13-4 ∷ S1 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0110 c4 = run b0
  where
  b0 : Chain (S1 ∷ Sb0-2-13-4 ∷ []) (Sb0-2-13-4 ∷ S1 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (S0 ∷ Sw01 ∷ []) (sym (wl0372 (lit c4))) ▸
       at 2 2 (Sb1-2-03-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·13·4⟩ (lit c4)) ▸
       at 1 2 (Sb1-2-03-4 ∷ S0 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩ c4) ▸
       at 0 2 (Sb0-2-13-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·03·4⟩ (lit c4)) ▸
       at 1 2 (S1 ∷ Sw01 ∷ []) (sym (wl0373 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto S0 | SBOX(1;2;03;4) @021021: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at021021 : Ws → ⟪ (S2 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ S2 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at021021 c4 = run b0
  where
  b0 : Chain (S2 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-23-4 ∷ S2 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (S1 ∷ Sw12 ∷ []) (sym (wl0642 (lit c4))) ▸
       at 2 2 (Sb0-2-13-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 1 2 (Sb0-2-13-4 ∷ S1 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0110 c4) ▸
       at 0 2 (Sb0-1-23-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·13·4⟩ (lit c4)) ▸
       at 1 2 (S2 ∷ Sw12 ∷ []) (sym (wl0643 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto S0 | SBOX(1;2;03;4) @03102132: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at03102132 : Ws → ⟪ (S3 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ S3 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at03102132 c4 = run b0
  where
  b0 : Chain (S3 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-32-4 ∷ S3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (S2 ∷ Sw23 ∷ []) (sym (wl0644 (lit c4))) ▸
       at 2 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-23-4 ∷ S2 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at021021 c4) ▸
       at 0 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 1 2 (S3 ∷ Sw23 ∷ []) (sym (wl0645 (lit c4))) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto S0 | SBOX(1;2;03;4) @0410213243: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0410213243 : Ws → ⟪ (S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (S3 ∷ Sw34 ∷ []) (sym (wl0646 (lit c4))) ▸
       at 2 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ S3 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at03102132 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 1 2 (S4 ∷ Sw34 ∷ []) (sym (wl0647 (lit c4))) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto S0 | SBOX(1;2;03;4) @04203243: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at04203243 : Ws → ⟪ (S4 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at04203243 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto S0 | SBOX(1;2;03;4) @0412203143: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0412203143 : Ws → ⟪ (S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0412203143 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at04203243 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F2 iI|CS01: 1 steps
lem-F2-iI∣CS01 : Ws → ⟪ (S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S4 ∷ []) ⟫ʷ
lem-F2-iI∣CS01 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S4 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0412203143 c4) ▸ done


-- auto S0 | SBOX(1;2;03;4) @04102142: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at04102142 : Ws → ⟪ (S4 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at04102142 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4) ▸
       at 0 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- F2 iI|CS12: 1 steps
lem-F2-iI∣CS12 : Ws → ⟪ (S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ S4 ∷ []) ⟫ʷ
lem-F2-iI∣CS12 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ S4 ∷ [])
  b0 = at 0 2 (Sb0-1-42-3 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4) ▸ done


-- auto S0 | SBOX(1;2;03;4) @041041: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at041041 : Ws → ⟪ (S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at041041 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-43-2 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at04102142 c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F2 iI|CS23: 1 steps
lem-F2-iI∣CS23 : Ws → ⟪ (S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ S4 ∷ []) ⟫ʷ
lem-F2-iI∣CS23 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ S4 ∷ [])
  b0 = at 0 2 (Sb0-2-43-1 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at041041 c4) ▸ done


-- auto CS01 | BOX(1;2034): 3 steps
lem-auto-CS01-∣-BOX⟨1·2034⟩ : Ws → ⟪ (CS01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2034⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CS01 ∷ [])
  b0 = at 0 1 (CS01 ∷ []) (wl0332 (lit c4)) ▸
       at 0 2 (Bx1-2034 ∷ CS01 ∷ []) (lem-CS20-beta-c-at011220 c4) ▸
       at 1 1 (CS01 ∷ []) (wl0332 (lit c4)) ▸ done


-- auto CS01 | SBOX(1;2;03;4): 11 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩ : Ws → ⟪ (CS01 ∷ Sb1-2-03-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-03-4 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS01 ∷ Sb1-2-03-4 ∷ []) (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ CS01 ∷ CS24⁻ ∷ [])
  b0 = at 1 1 (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ Sb⁻1-2-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-2034 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (Toff403 ∷ CS01 ∷ []) (wp0289 c4) ▸
       at 3 1 (CS24 ∷ []) (refl) ▸
       at 2 2 (CS24 ∷ CS01 ∷ []) (wp0290 c4) ▸
       at 2 1 (Sb1-2-4-3 ∷ []) (refl) ▸
       at 3 2 (Toff403 ∷ CS01 ∷ []) (wp0289 c4) ▸
       at 5 1 (CS24⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ CS01 ∷ CS24⁻ ∷ []) (Sb1-2-03-4 ∷ CS01 ∷ [])
  b1 = at 4 2 (CS24⁻ ∷ CS01 ∷ []) (wp0291 c4) ▸
       at 4 1 (Sb⁻1-2-4-3 ∷ []) (refl) ▸
       at 0 5 (Sb1-2-03-4 ∷ []) (refl) ▸ done


-- auto CS01 | SBOX(1;2;03;4) @0110: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0110 : Ws → ⟪ (CS01 ∷ Sb0-2-13-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-13-4 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0110 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Sb0-2-13-4 ∷ []) (Sb0-2-13-4 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 2 2 (Sb1-2-03-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·13·4⟩ (lit c4)) ▸
       at 1 2 (Sb1-2-03-4 ∷ CS01 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩ c4) ▸
       at 0 2 (Sb0-2-13-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·03·4⟩ (lit c4)) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CS01 | SBOX(1;2;03;4) @021021: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at021021 : Ws → ⟪ (CS02 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at021021 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-23-4 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4)) ▸
       at 2 2 (Sb0-2-13-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 1 2 (Sb0-2-13-4 ∷ CS01 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0110 c4) ▸
       at 0 2 (Sb0-1-23-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·13·4⟩ (lit c4)) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CS01 | SBOX(1;2;03;4) @03102132: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at03102132 : Ws → ⟪ (CS03 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ CS03 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at03102132 c4 = run b0
  where
  b0 : Chain (CS03 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-32-4 ∷ CS03 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 (lit c4)) ▸
       at 2 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-23-4 ∷ CS02 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at021021 c4) ▸
       at 0 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 1 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CS01 | SBOX(1;2;03;4) @0410213243: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0410213243 : Ws → ⟪ (CS04 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS04 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 (lit c4)) ▸
       at 2 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ CS03 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at03102132 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 1 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- F2 S0|CS12: 1 steps
lem-F2-S0∣CS12 : Ws → ⟪ (CS04 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0∣CS12 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS04 ∷ [])
  b0 = at 0 2 (Sb0-1-42-3 ∷ CS04 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4) ▸ done


-- auto CS01 | SBOX(1;2;03;4) @04102142: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at04102142 : Ws → ⟪ (CS04 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at04102142 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CS04 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ CS04 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4) ▸
       at 0 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CS01 | SBOX(1;2;03;4) @041041: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at041041 : Ws → ⟪ (CS04 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at041041 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS04 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-43-2 ∷ CS04 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at04102142 c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F2 S0|CS23: 1 steps
lem-F2-S0∣CS23 : Ws → ⟪ (CS04 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0∣CS23 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS04 ∷ [])
  b0 = at 0 2 (Sb0-2-43-1 ∷ CS04 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at041041 c4) ▸ done


-- auto CS01 | SBOX(1;2;03;4) @04203243: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at04203243 : Ws → ⟪ (CS14 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CS14 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at04203243 c4 = run b0
  where
  b0 : Chain (CS14 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CS14 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ CS04 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- F2 S1|CS23: 1 steps
lem-F2-S1∣CS23 : Ws → ⟪ (CS14 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1∣CS23 c4 = run b0
  where
  b0 : Chain (CS14 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS14 ∷ [])
  b0 = at 0 2 (Sb0-2-43-1 ∷ CS14 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04203243 c4) ▸ done


-- auto CS01 | SBOX(1;2;03;4) @0412203143: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0412203143 : Ws → ⟪ (CS24 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS24 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0412203143 c4 = run b0
  where
  b0 : Chain (CS24 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS24 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ CS14 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at04203243 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F2 S2|CS01: 1 steps
lem-F2-S2∣CS01 : Ws → ⟪ (CS24 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2∣CS01 c4 = run b0
  where
  b0 : Chain (CS24 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS24 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ CS24 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0412203143 c4) ▸ done


-- F2 S3|CS01: 1 steps
lem-F2-S3∣CS01 : Ws → ⟪ (CS34 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3∣CS01 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS34 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ CS34 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 c4) ▸ done


-- F2 S3|CS12: 1 steps
lem-F2-S3∣CS12 : Ws → ⟪ (CS34 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3∣CS12 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS34 ∷ [])
  b0 = at 0 2 (Sb0-1-42-3 ∷ CS34 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413203142 c4) ▸ done


-- auto iI | BOX(0;1234): 1 steps
lem-auto-iI-∣-BOX⟨0·1234⟩ : Ws → ⟪ (ι ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ ι ∷ []) ⟫ʷ
lem-auto-iI-∣-BOX⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (ι ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ ι ∷ [])
  b0 = at 0 2 (Bx0-1234 ∷ ι ∷ []) (sym zc) ▸ done


-- auto K0 | BOX(0;1234) @1221: 7 steps
lem-auto-K0-∣-BOX⟨0·1234⟩-at1221 : Ws → ⟪ (K0 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ K0 ∷ []) ⟫ʷ
lem-auto-K0-∣-BOX⟨0·1234⟩-at1221 c4 = run b0
  where
  b0 : Chain (K0 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ K0 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ K0 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩ c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto K0 | BOX(0;1234) @011220: 7 steps
lem-auto-K0-∣-BOX⟨0·1234⟩-at011220 : Ws → ⟪ (K1 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ K1 ∷ []) ⟫ʷ
lem-auto-K0-∣-BOX⟨0·1234⟩-at011220 c4 = run b0
  where
  b0 : Chain (K1 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ K1 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (K0 ∷ Sw01 ∷ []) (sym (wl0031 (lit c4))) ▸
       at 2 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ (lit c4)) ▸
       at 1 2 (Bx0-2134 ∷ K0 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩-at1221 c4) ▸
       at 0 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 (K1 ∷ Sw01 ∷ []) (sym (wl0076 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto iI | BOX(0;1234) @1221: 7 steps
lem-auto-iI-∣-BOX⟨0·1234⟩-at1221 : Ws → ⟪ (ι ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ ι ∷ []) ⟫ʷ
lem-auto-iI-∣-BOX⟨0·1234⟩-at1221 c4 = run b0
  where
  b0 : Chain (ι ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ ι ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 2 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ ι ∷ []) (lem-auto-iI-∣-BOX⟨0·1234⟩ c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto iI | BOX(0;1234) @011220: 7 steps
lem-auto-iI-∣-BOX⟨0·1234⟩-at011220 : Ws → ⟪ (ι ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ ι ∷ []) ⟫ʷ
lem-auto-iI-∣-BOX⟨0·1234⟩-at011220 c4 = run b0
  where
  b0 : Chain (ι ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ ι ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (ι ∷ Sw01 ∷ []) (wl0030 (lit c4)) ▸
       at 2 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ (lit c4)) ▸
       at 1 2 (Bx0-2134 ∷ ι ∷ []) (lem-auto-iI-∣-BOX⟨0·1234⟩-at1221 c4) ▸
       at 0 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 (ι ∷ Sw01 ∷ []) (wl0030 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CK01 | BOX(1;2034): 9 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩ : Ws → ⟪ (CK01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CK01 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ [])
  b0 = at 0 1 (ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) (wl0516 (lit c4)) ▸
       at 6 2 (Bx1-2034 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩ c4) ▸
       at 5 2 (Bx1-2034 ∷ K1 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩-at011220 c4) ▸
       at 4 2 (Bx1-2034 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩ c4) ▸
       at 3 2 (Bx1-2034 ∷ K1 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩-at011220 c4) ▸
       at 2 2 (Bx1-2034 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (Bx1-2034 ∷ S0⁻ ∷ []) (lem-auto-Sd0-∣-BOX⟨1·2034⟩ c4) ▸
       at 0 2 (Bx1-2034 ∷ ι ∷ []) (lem-auto-iI-∣-BOX⟨0·1234⟩-at011220 c4) ▸ done

  b1 : Chain (Bx1-2034 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) (Bx1-2034 ∷ CK01 ∷ [])
  b1 = at 1 7 (CK01 ∷ []) (sym (wl0516 (lit c4))) ▸ done


-- auto CK01 | SBOX(1;2;03;4): 11 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩ : Ws → ⟪ (CK01 ∷ Sb1-2-03-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-03-4 ∷ CK01 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK01 ∷ Sb1-2-03-4 ∷ []) (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ CK01 ∷ CS24⁻ ∷ [])
  b0 = at 1 1 (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ Sb⁻1-2-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-2034 ∷ CK01 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (Toff403 ∷ CK01 ∷ []) (wp0292 c4) ▸
       at 3 1 (CS24 ∷ []) (refl) ▸
       at 2 2 (CS24 ∷ CK01 ∷ []) (wp0293 c4) ▸
       at 2 1 (Sb1-2-4-3 ∷ []) (refl) ▸
       at 3 2 (Toff403 ∷ CK01 ∷ []) (wp0292 c4) ▸
       at 5 1 (CS24⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ CK01 ∷ CS24⁻ ∷ []) (Sb1-2-03-4 ∷ CK01 ∷ [])
  b1 = at 4 2 (CS24⁻ ∷ CK01 ∷ []) (wp0294 c4) ▸
       at 4 1 (Sb⁻1-2-4-3 ∷ []) (refl) ▸
       at 0 5 (Sb1-2-03-4 ∷ []) (refl) ▸ done


-- auto CK01 | SBOX(1;2;03;4) @0110: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0110 : Ws → ⟪ (CK10 ∷ Sb0-2-13-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-13-4 ∷ CK10 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0110 c4 = run b0
  where
  b0 : Chain (CK10 ∷ Sb0-2-13-4 ∷ []) (Sb0-2-13-4 ∷ CK10 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CK01 ∷ Sw01 ∷ []) (sym (wl0648 (lit c4))) ▸
       at 2 2 (Sb1-2-03-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·13·4⟩ (lit c4)) ▸
       at 1 2 (Sb1-2-03-4 ∷ CK01 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩ c4) ▸
       at 0 2 (Sb0-2-13-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·03·4⟩ (lit c4)) ▸
       at 1 2 (CK10 ∷ Sw01 ∷ []) (sym (wl0649 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CK01 | SBOX(1;2;03;4) @021021: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at021021 : Ws → ⟪ (CK20 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ CK20 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at021021 c4 = run b0
  where
  b0 : Chain (CK20 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-23-4 ∷ CK20 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CK10 ∷ Sw12 ∷ []) (lem-nat-1-CK20 (lit c4)) ▸
       at 2 2 (Sb0-2-13-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 1 2 (Sb0-2-13-4 ∷ CK10 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0110 c4) ▸
       at 0 2 (Sb0-1-23-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·13·4⟩ (lit c4)) ▸
       at 1 2 (CK20 ∷ Sw12 ∷ []) (lem-nat-1-CK10 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CK01 | SBOX(1;2;03;4) @03102132: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at03102132 : Ws → ⟪ (CK30 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ CK30 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at03102132 c4 = run b0
  where
  b0 : Chain (CK30 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-32-4 ∷ CK30 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CK20 ∷ Sw23 ∷ []) (lem-nat-2-CK30 (lit c4)) ▸
       at 2 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-23-4 ∷ CK20 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at021021 c4) ▸
       at 0 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 1 2 (CK30 ∷ Sw23 ∷ []) (lem-nat-2-CK20 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CK01 | SBOX(1;2;03;4) @0410213243: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0410213243 : Ws → ⟪ (CK40 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK40 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK40 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CK30 ∷ Sw34 ∷ []) (lem-nat-3-CK40 (lit c4)) ▸
       at 2 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ CK30 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at03102132 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 1 2 (CK40 ∷ Sw34 ∷ []) (lem-nat-3-CK30 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- F2 K0|CS12: 1 steps
lem-F2-K0∣CS12 : Ws → ⟪ (CK40 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0∣CS12 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK40 ∷ [])
  b0 = at 0 2 (Sb0-1-42-3 ∷ CK40 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4) ▸ done


-- auto CK01 | SBOX(1;2;03;4) @04102142: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at04102142 : Ws → ⟪ (CK40 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CK40 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at04102142 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CK40 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ CK40 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4) ▸
       at 0 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CK01 | SBOX(1;2;03;4) @041041: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at041041 : Ws → ⟪ (CK40 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CK40 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at041041 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CK40 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4)) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-43-2 ∷ CK40 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at04102142 c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F2 K0|CS23: 1 steps
lem-F2-K0∣CS23 : Ws → ⟪ (CK40 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0∣CS23 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CK40 ∷ [])
  b0 = at 0 2 (Sb0-2-43-1 ∷ CK40 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at041041 c4) ▸ done


-- auto CK01 | SBOX(1;2;03;4) @04203243: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at04203243 : Ws → ⟪ (CK41 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CK41 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at04203243 c4 = run b0
  where
  b0 : Chain (CK41 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CK41 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ CK40 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (CK41 ∷ Sw01 ∷ []) (lem-nat-0-CK40 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- F0 @0314203142: 5 steps
lem-F0-at0314203142 : Ws → ⟪ (Sb0-3-24-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-24-0 ∷ []) ⟫ʷ
lem-F0-at0314203142 c4 = run b0
  where
  b0 : Chain (Sb0-3-24-1 ∷ []) (Sb1-3-24-0 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-2-34-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·3·24·1⟩ (lit c4)) ▸
       at 1 1 (Sb1-2-34-0 ∷ []) (lem-F0-at0214203143 c4) ▸
       at 0 2 (Sb1-3-24-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·2·34·0⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- F0 @0314213042: 5 steps
lem-F0-at0314213042 : Ws → ⟪ (Sb1-3-24-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-24-1 ∷ []) ⟫ʷ
lem-F0-at0314213042 c4 = run b0
  where
  b0 : Chain (Sb1-3-24-0 ∷ []) (Sb0-3-24-1 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-3-24-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·3·24·0⟩ (lit c4)) ▸
       at 1 1 (Sb1-3-24-0 ∷ []) (lem-F0-at0314203142 c4) ▸
       at 0 2 (Sb0-3-24-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·3·24·0⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- F0 @03143041: 5 steps
lem-F0-at03143041 : Ws → ⟪ (Sb2-3-14-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-14-2 ∷ []) ⟫ʷ
lem-F0-at03143041 c4 = run b0
  where
  b0 : Chain (Sb2-3-14-0 ∷ []) (Sb0-3-14-2 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb1-3-24-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·3·14·0⟩ (lit c4)) ▸
       at 1 1 (Sb0-3-24-1 ∷ []) (lem-F0-at0314213042 c4) ▸
       at 0 2 (Sb0-3-14-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·3·24·1⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- F0 @03143140: 5 steps
lem-F0-at03143140 : Ws → ⟪ (Sb2-3-04-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-04-2 ∷ []) ⟫ʷ
lem-F0-at03143140 c4 = run b0
  where
  b0 : Chain (Sb2-3-04-1 ∷ []) (Sb1-3-04-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb2-3-14-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·04·1⟩ (lit c4)) ▸
       at 1 1 (Sb0-3-14-2 ∷ []) (lem-F0-at03143041 c4) ▸
       at 0 2 (Sb1-3-04-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·3·14·2⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto CK01 | BOX(1;2034) @3443: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at3443 : Ws → ⟪ (CK01 ∷ Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2043 ∷ CK01 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at3443 c4 = run b0
  where
  b0 : Chain (CK01 ∷ Bx1-2043 ∷ []) (Bx1-2043 ∷ CK01 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CK01 ∷ Sw34 ∷ []) (sym (c₂ (CK₀₁) (Swap ↑))) ▸
       at 2 2 (Bx1-2034 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2043⟩ (lit c4)) ▸
       at 1 2 (Bx1-2034 ∷ CK01 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩ c4) ▸
       at 0 2 (Bx1-2043 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2034⟩ (lit c4)) ▸
       at 1 2 (CK01 ∷ Sw34 ∷ []) (sym (c₂ (CK₀₁) (Swap ↑))) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CK01 | BOX(1;2034) @233442: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at233442 : Ws → ⟪ (CK01 ∷ Bx1-3042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3042 ∷ CK01 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at233442 c4 = run b0
  where
  b0 : Chain (CK01 ∷ Bx1-3042 ∷ []) (Bx1-3042 ∷ CK01 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CK01 ∷ Sw23 ∷ []) (sym (c₂ (CK₀₁) (Swap))) ▸
       at 2 2 (Bx1-2043 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·3042⟩ (lit c4)) ▸
       at 1 2 (Bx1-2043 ∷ CK01 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at3443 c4) ▸
       at 0 2 (Bx1-3042 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·2043⟩ (lit c4)) ▸
       at 1 2 (CK01 ∷ Sw23 ∷ []) (sym (c₂ (CK₀₁) (Swap))) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CK01 | SBOX(2;3;04;1): 13 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩ : Ws → ⟪ (CK01 ∷ Sb2-3-04-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-04-1 ∷ CK01 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK01 ∷ Sb2-3-04-1 ∷ []) (Bx1-3042 ∷ Toff204 ∷ Sb1-3-2-4 ∷ Toff204 ∷ CK01 ∷ Sb⁻1-3-2-4 ∷ [])
  b0 = at 1 1 (Sb1-3-04-2 ∷ []) (lem-F0-at03143140 c4) ▸
       at 1 1 (Bx1-3042 ∷ Toff204 ∷ Sb1-3-2-4 ∷ Toff204 ∷ Sb⁻1-3-2-4 ∷ []) (refl) ▸
       at 0 2 (Bx1-3042 ∷ CK01 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at233442 c4) ▸
       at 1 2 (Toff204 ∷ CK01 ∷ []) (wp0295 c4) ▸
       at 3 1 (CS23 ∷ []) (refl) ▸
       at 2 2 (CS23 ∷ CK01 ∷ []) (wl0650 (lit c4)) ▸
       at 2 1 (Sb1-3-2-4 ∷ []) (refl) ▸
       at 3 2 (Toff204 ∷ CK01 ∷ []) (wp0295 c4) ▸ done

  b1 : Chain (Bx1-3042 ∷ Toff204 ∷ Sb1-3-2-4 ∷ Toff204 ∷ CK01 ∷ Sb⁻1-3-2-4 ∷ []) (Sb2-3-04-1 ∷ CK01 ∷ [])
  b1 = at 5 1 (CS23⁻ ∷ []) (refl) ▸
       at 4 2 (CS23⁻ ∷ CK01 ∷ []) (wl0651 (lit c4)) ▸
       at 4 1 (Sb⁻1-3-2-4 ∷ []) (refl) ▸
       at 0 5 (Sb1-3-04-2 ∷ []) (refl) ▸
       at 0 1 (Sb2-3-04-1 ∷ []) (sym (lem-F0-at03143140 c4)) ▸ done


-- auto CK01 | SBOX(2;3;04;1) @0110: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0110 : Ws → ⟪ (CK10 ∷ Sb2-3-14-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-14-0 ∷ CK10 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0110 c4 = run b0
  where
  b0 : Chain (CK10 ∷ Sb2-3-14-0 ∷ []) (Sb2-3-14-0 ∷ CK10 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CK01 ∷ Sw01 ∷ []) (sym (wl0648 (lit c4))) ▸
       at 2 2 (Sb2-3-04-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·14·0⟩ (lit c4)) ▸
       at 1 2 (Sb2-3-04-1 ∷ CK01 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩ c4) ▸
       at 0 2 (Sb2-3-14-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·04·1⟩ (lit c4)) ▸
       at 1 2 (CK10 ∷ Sw01 ∷ []) (sym (wl0649 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CK01 | SBOX(2;3;04;1) @021021: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at021021 : Ws → ⟪ (CK20 ∷ Sb1-3-24-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-24-0 ∷ CK20 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at021021 c4 = run b0
  where
  b0 : Chain (CK20 ∷ Sb1-3-24-0 ∷ []) (Sb1-3-24-0 ∷ CK20 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CK10 ∷ Sw12 ∷ []) (lem-nat-1-CK20 (lit c4)) ▸
       at 2 2 (Sb2-3-14-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·3·24·0⟩ (lit c4)) ▸
       at 1 2 (Sb2-3-14-0 ∷ CK10 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0110 c4) ▸
       at 0 2 (Sb1-3-24-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·3·14·0⟩ (lit c4)) ▸
       at 1 2 (CK20 ∷ Sw12 ∷ []) (lem-nat-1-CK10 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CK01 | SBOX(2;3;04;1) @03102132: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at03102132 : Ws → ⟪ (CK30 ∷ Sb1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-34-0 ∷ CK30 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at03102132 c4 = run b0
  where
  b0 : Chain (CK30 ∷ Sb1-2-34-0 ∷ []) (Sb1-2-34-0 ∷ CK30 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CK20 ∷ Sw23 ∷ []) (lem-nat-2-CK30 (lit c4)) ▸
       at 2 2 (Sb1-3-24-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·2·34·0⟩ (lit c4)) ▸
       at 1 2 (Sb1-3-24-0 ∷ CK20 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at021021 c4) ▸
       at 0 2 (Sb1-2-34-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·24·0⟩ (lit c4)) ▸
       at 1 2 (CK30 ∷ Sw23 ∷ []) (lem-nat-2-CK20 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CK01 | SBOX(2;3;04;1) @0410213243: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0410213243 : Ws → ⟪ (CK40 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ CK40 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sb1-2-43-0 ∷ []) (Sb1-2-43-0 ∷ CK40 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CK30 ∷ Sw34 ∷ []) (lem-nat-3-CK40 (lit c4)) ▸
       at 2 2 (Sb1-2-34-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 1 2 (Sb1-2-34-0 ∷ CK30 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at03102132 c4) ▸
       at 0 2 (Sb1-2-43-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·34·0⟩ (lit c4)) ▸
       at 1 2 (CK40 ∷ Sw34 ∷ []) (lem-nat-3-CK30 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CK01 | SBOX(2;3;04;1) @04203243: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at04203243 : Ws → ⟪ (CK41 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CK41 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at04203243 c4 = run b0
  where
  b0 : Chain (CK41 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CK41 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 (lit c4)) ▸
       at 2 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 1 2 (Sb1-2-43-0 ∷ CK40 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0410213243 c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 1 2 (CK41 ∷ Sw01 ∷ []) (lem-nat-0-CK40 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- F2 K1|CS23: 1 steps
lem-F2-K1∣CS23 : Ws → ⟪ (CK41 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CK41 ∷ []) ⟫ʷ
lem-F2-K1∣CS23 c4 = run b0
  where
  b0 : Chain (CK41 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CK41 ∷ [])
  b0 = at 0 2 (Sb0-2-43-1 ∷ CK41 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at04203243 c4) ▸ done


-- auto CK01 | SBOX(1;2;03;4) @0412203143: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0412203143 : Ws → ⟪ (CK42 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK42 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0412203143 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK42 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ CK41 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at04203243 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F2 K2|CS01: 1 steps
lem-F2-K2∣CS01 : Ws → ⟪ (CK42 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK42 ∷ []) ⟫ʷ
lem-F2-K2∣CS01 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK42 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ CK42 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0412203143 c4) ▸ done


-- auto CK01 | SBOX(2;3;04;1) @0412203143: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0412203143 : Ws → ⟪ (CK42 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CK42 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0412203143 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CK42 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0160 (lit c4))) ▸
       at 2 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 2 (Sb0-2-43-1 ∷ CK41 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at04203243 c4) ▸
       at 0 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 1 2 (CK42 ∷ Sw12 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CK01 | SBOX(2;3;04;1) @0413203142: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0413203142 : Ws → ⟪ (CK43 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK43 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0413203142 c4 = run b0
  where
  b0 : Chain (CK43 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK43 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0162 (lit c4))) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-43-2 ∷ CK42 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0412203143 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 2 (CK43 ∷ Sw23 ∷ []) (sym (wl0163 (lit c4))) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CK01 | SBOX(2;3;04;1) @0413213042: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0413213042 : Ws → ⟪ (CK43 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CK43 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0413213042 c4 = run b0
  where
  b0 : Chain (CK43 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CK43 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ CK43 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0413203142 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CK01 | SBOX(2;3;04;1) @04133041: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at04133041 : Ws → ⟪ (CK43 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK43 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at04133041 c4 = run b0
  where
  b0 : Chain (CK43 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK43 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ CK43 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0413213042 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F2 K3|CS01: 1 steps
lem-F2-K3∣CS01 : Ws → ⟪ (CK43 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK43 ∷ []) ⟫ʷ
lem-F2-K3∣CS01 c4 = run b0
  where
  b0 : Chain (CK43 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK43 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ CK43 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at04133041 c4) ▸ done


-- F2 K3|CS12: 1 steps
lem-F2-K3∣CS12 : Ws → ⟪ (CK43 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK43 ∷ []) ⟫ʷ
lem-F2-K3∣CS12 c4 = run b0
  where
  b0 : Chain (CK43 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK43 ∷ [])
  b0 = at 0 2 (Sb0-1-42-3 ∷ CK43 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0413203142 c4) ▸ done


-- auto BOX(0;1234) | CCZ143: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ143 : Ws → ⟪ (Bx0-1234 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ143 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ []) (wl0347 (lit c4)) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CCZ134 ∷ Bx0-1324 ∷ []) (sym (lem-c124-beta-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (CCZ134 ∷ []) (wl0347 (lit c4)) ▸ done


-- auto BOX(0;1234) | CSd21: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd21 : Ws → ⟪ (Bx0-1234 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd21 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (wl0652 (lit c4)) ▸
       at 0 2 (CS12⁻ ∷ Bx0-1234 ∷ []) (sym (lem-CSd12-beta c4)) ▸
       at 0 1 (CS12⁻ ∷ []) (wl0652 (lit c4)) ▸ done


-- auto BOX(0;1234) | CSd21 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd21-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd21-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 (lit c4)) ▸
       at 1 2 (CS12⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd21 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- CX23-beta @2442: 8 steps
lem-CX23-beta-at2442 : Ws → ⟪ (CX43 ∷ Bx0-1432 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CX23-beta-at2442 c4 = run b0
  where
  b0 : Chain (CX43 ∷ Bx0-1432 ∷ CX43 ∷ []) (Bx0-1432 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CX42 ∷ Sw23 ∷ []) (sym (wl0147 (lit c4))) ▸
       at 2 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4)) ▸
       at 3 2 (CX42 ∷ Sw23 ∷ []) (sym (wl0147 (lit c4))) ▸
       at 1 3 (Bx0-1423 ∷ CCZ134 ∷ []) (lem-CX23-beta-at243243 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ143 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ143 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ143: 32 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143 : Ws → ⟪ (Sb0-1-23-4 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ134 ∷ []) (CS13 ∷ Bx0-1324 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ [])
  b0 = at 1 1 (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (wl0653 (lit c4)) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS13 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 4 (CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14⁻ ∷ []) (wl0654 (lit c4)) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS13 ∷ Bx0-1324 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ []) (CS13 ∷ CX43 ∷ Bx0-1324 ∷ CCZ124 ∷ CS13⁻ ∷ CX43 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ [])
  b1 = at 2 6 (CX43 ∷ CS13⁻ ∷ CX43 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (sym (wl0655 (lit c4))) ▸
       at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 1 0 (CX43 ∷ CX43 ∷ []) (sym (wl0656 (lit c4))) ▸
       at 3 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 3 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 2 3 (Bx0-1432 ∷ CCZ124 ∷ []) (lem-CX23-beta-at2442 c4) ▸
       at 2 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym34-at233442 c4) ▸ done

  b2 : Chain (CS13 ∷ CX43 ∷ Bx0-1324 ∷ CCZ124 ∷ CS13⁻ ∷ CX43 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ []) (CS13 ∷ CX43 ∷ CCZ124 ∷ CS13⁻ ∷ CX43 ∷ Bx0-1324 ∷ CCZ124 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ [])
  b2 = at 2 2 (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at2332 c4) ▸
       at 3 2 (CS13⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd21-at2332 c4) ▸
       at 4 0 (CX43 ∷ CX43 ∷ []) (sym (wl0656 (lit c4))) ▸
       at 6 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 6 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 5 3 (Bx0-1432 ∷ CCZ124 ∷ []) (lem-CX23-beta-at2442 c4) ▸
       at 5 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-sym34-at233442 c4) ▸ done

  b3 : Chain (CS13 ∷ CX43 ∷ CCZ124 ∷ CS13⁻ ∷ CX43 ∷ Bx0-1324 ∷ CCZ124 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ []) (CCZ134 ∷ Sb0-1-23-4 ∷ [])
  b3 = at 5 2 (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at2332 c4) ▸
       at 1 2 (CCZ124 ∷ CX43 ∷ []) (sym (wl0657 (lit c4))) ▸
       at 2 4 (CCZ124 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) (sym (wl0658 (lit c4))) ▸
       at 1 2 [] (wl0351 (lit c4)) ▸
       at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ134 ∷ []) (sym (wl0653 (lit c4))) ▸ done


-- sym34 @12243143: 5 steps
lem-sym34-at12243143 : Ws → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-sym34-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4)) ▸
       at 1 1 (Bx0-1432 ∷ []) (lem-sym34-at243243 c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- T312-beta @12213443: 8 steps
lem-T312-beta-at12213443 : Ws → ⟪ (Toff412 ∷ Bx0-2143 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ CCZ123 ∷ []) ⟫ʷ
lem-T312-beta-at12213443 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ Bx0-2143 ∷ Toff412 ∷ []) (Bx0-2143 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff412 ∷ Sw12 ∷ []) (wl0079 (lit c4)) ▸
       at 2 2 (Bx0-1243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2143⟩ (lit c4)) ▸
       at 3 2 (Toff412 ∷ Sw12 ∷ []) (wl0079 (lit c4)) ▸
       at 1 3 (Bx0-1243 ∷ CCZ123 ∷ []) (lem-T312-beta-at3443 c4) ▸
       at 0 2 (Bx0-2143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1243⟩ (lit c4)) ▸
       at 1 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- T312-beta @13213442: 8 steps
lem-T312-beta-at13213442 : Ws → ⟪ (Toff413 ∷ Bx0-3142 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ CCZ123 ∷ []) ⟫ʷ
lem-T312-beta-at13213442 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ Bx0-3142 ∷ Toff413 ∷ []) (Bx0-3142 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 (lit c4)) ▸
       at 2 2 (Bx0-2143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3142⟩ (lit c4)) ▸
       at 3 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 (lit c4)) ▸
       at 1 3 (Bx0-2143 ∷ CCZ123 ∷ []) (lem-T312-beta-at12213443 c4) ▸
       at 0 2 (Bx0-3142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2143⟩ (lit c4)) ▸
       at 1 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 (lit c4))) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- T312-beta @133441: 8 steps
lem-T312-beta-at133441 : Ws → ⟪ (Toff423 ∷ Bx0-3241 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ CCZ123 ∷ []) ⟫ʷ
lem-T312-beta-at133441 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ Bx0-3241 ∷ Toff423 ∷ []) (Bx0-3241 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (wl0091 (lit c4)) ▸
       at 2 2 (Bx0-3142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3241⟩ (lit c4)) ▸
       at 3 2 (Toff413 ∷ Sw12 ∷ []) (wl0091 (lit c4)) ▸
       at 1 3 (Bx0-3142 ∷ CCZ123 ∷ []) (lem-T312-beta-at13213442 c4) ▸
       at 0 2 (Bx0-3241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3142⟩ (lit c4)) ▸
       at 1 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;0412): 3 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩ : Ws → ⟪ (CCZ012 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx3-0142 ∷ []) (lem-sym23-at0310243142 c4) ▸
       at 0 2 (Bx3-0142 ∷ CCZ012 ∷ []) (lem-c124-beta-at0310213442 c4) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-sym23-at0310213442 c4) ▸ done


-- auto CCZ012 | BOX(3;0412) @2332: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 : Ws → ⟪ (CCZ013 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 2 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (Bx3-0412 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩ c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto S0 | BOX(1;2034) @0110: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at0110 : Ws → ⟪ (S1 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ S1 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at0110 c4 = run b0
  where
  b0 : Chain (S1 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ S1 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (S0 ∷ Sw01 ∷ []) (sym (wl0372 (lit c4))) ▸
       at 2 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 (Bx1-2034 ∷ S0 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩ c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ (lit c4)) ▸
       at 1 2 (S1 ∷ Sw01 ∷ []) (sym (wl0373 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto S0 | BOX(1;2034) @021021: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at021021 : Ws → ⟪ (S2 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ S2 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at021021 c4 = run b0
  where
  b0 : Chain (S2 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ S2 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (S1 ∷ Sw12 ∷ []) (sym (wl0642 (lit c4))) ▸
       at 2 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (Bx0-2134 ∷ S1 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at0110 c4) ▸
       at 0 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 (S2 ∷ Sw12 ∷ []) (sym (wl0643 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto S0 | BOX(1;2034) @03102132: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at03102132 : Ws → ⟪ (S3 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ S3 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at03102132 c4 = run b0
  where
  b0 : Chain (S3 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ S3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (S2 ∷ Sw23 ∷ []) (sym (wl0644 (lit c4))) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ S2 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at021021 c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (S3 ∷ Sw23 ∷ []) (sym (wl0645 (lit c4))) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto S0 | BOX(1;2034) @0410213243: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at0410213243 : Ws → ⟪ (S4 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (S4 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (S3 ∷ Sw34 ∷ []) (sym (wl0646 (lit c4))) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ S3 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at03102132 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (S4 ∷ Sw34 ∷ []) (sym (wl0647 (lit c4))) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto S0 | BOX(1;2034) @04203243: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at04203243 : Ws → ⟪ (S4 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at04203243 c4 = run b0
  where
  b0 : Chain (S4 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at0410213243 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto S0 | BOX(1;2034) @0412203143: 7 steps
lem-auto-S0-∣-BOX⟨1·2034⟩-at0412203143 : Ws → ⟪ (S4 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩-at0412203143 c4 = run b0
  where
  b0 : Chain (S4 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at04203243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F4 iI^0|CS01^1: 24 steps
lem-F4-iIᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-iIᵖ0∣CS01ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ S4 ∷ CCZ013 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 2 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 3 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 2 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 1 2 (Bx2-0413 ∷ S4 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩-at0412203143 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ S4 ∷ CCZ013 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b1 = at 1 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 0 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 0 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 4 2 (X4 ∷ CCZ013 ∷ []) (wp0296 c4) ▸
       at 1 4 (X4 ∷ S4 ∷ X4 ∷ CCZ013 ∷ []) (wp0297 c4) ▸
       at 4 2 [] (wl0659 (lit c4)) ▸
       at 1 4 (Toff314 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0660 (lit c4))) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b2 = at 5 1 (CS03 ∷ []) (refl) ▸
       at 2 4 (CS03 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0298 c4)) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 4 (Toff314 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0660 (lit c4))) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0299 c4)) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


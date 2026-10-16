{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D151 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-T312-beta-at1221 ; lem-sym12-at1221 ; lem-sym23-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-sym23-at122331)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym12-at021021 ; lem-sym23-at021021 ; lem-sym34-at122331)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-CKbox ; lem-KB-form ; lem-SB2)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-F0-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-auto-K0-∣-BOX⟨0·1234⟩ ; lem-sym12-at0210233441 ; lem-sym23-at02102331 ; lem-sym34-at02102331)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-auto-Sd0-∣-BOX⟨1·2034⟩ ; lem-beta-T-at011220 ; lem-sym12-at02132031 ; lem-sym12-at02132130 ; lem-sym12-at022330 ; lem-sym23-at0220 ; lem-sym23-at022330)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-CS20-beta-c-at011220 ; lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0412203143 ; lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413203142 ; lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413213042 ; lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 ; lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04203243)
open import Examples.Groups.Clifford+CS.Five.D.D080 using (lem-sym23-at0213203441 ; lem-sym23-at0213243041 ; lem-sym34-at0213203441)
open import Examples.Groups.Clifford+CS.Five.D.D081 using (lem-sym23-at0310243241)
open import Examples.Groups.Clifford+CS.Five.D.D082 using (lem-sym23-at03103441)
open import Examples.Groups.Clifford+CS.Five.D.D136 using (lem-sym12-at1331)
open import Examples.Groups.Clifford+CS.Five.D.D137 using (lem-sym12-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D138 using (lem-SB2-at011220)
open import Examples.Groups.Clifford+CS.Five.D.D144 using (lem-SB2-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D147 using (lem-boxify-10)
open import Examples.Groups.Clifford+CS.Five.D.D148 using (lem-boxify-11 ; lem-boxify-12 ; lem-boxify-13)
open import Examples.Groups.Clifford+CS.Five.D.D149 using (lem-F1-toff-ccz-nf-of-rhs ; lem-boxify-14 ; lem-sym12-at031031 ; lem-sym23-at03122031 ; lem-sym23-at03122130)
open import Examples.Groups.Clifford+CS.Five.D.D150 using (lem-T312-beta-at0213243041 ; lem-TW-at02132130 ; lem-TW-at0310243241 ; lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0214⟩-at021021 ; lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03122130 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at03122130 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at13243241 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at021021 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at13243241 ; lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at13243241 ; lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at03122130 ; lem-auto-CCZ012-∣-TOFF342-at0112243043 ; lem-auto-CCZ012-∣-TOFF342-at02243043 ; lem-beta-inv-at03102132 ; lem-beta-inv-at03122130 ; lem-beta-inv-at13243241 ; lem-sym12-at0220 ; lem-sym12-at0312203441 ; lem-sym23-at13243241 ; lem-sym23-at133441 ; lem-sym34-at03103441 ; lem-sym34-at03122031 ; lem-sym34-at133441)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·2134⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-1-BOX⟨0·1234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-0-BOX⟨0·2134⟩ ; lem-nat-0-BOX⟨1·2034⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-CS04 ; lem-nat-0-CS14 ; lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-CS04 ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-2-CS02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-3-CS04)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-2-CS04 ; lem-nat-3-CS03)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-CS03)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-2-SBOX⟨0·1·42·3⟩ ; lem-nat-2-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-1-SBOX⟨0·1·43·2⟩ ; lem-nat-1-SBOX⟨0·2·43·1⟩ ; lem-nat-2-SBOX⟨1·2·34·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R024 using (lem-nat-0-SBOX⟨0·2·13·4⟩ ; lem-nat-0-SBOX⟨1·2·03·4⟩ ; lem-nat-1-SBOX⟨0·1·23·4⟩ ; lem-nat-1-SBOX⟨0·2·13·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-0-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R034 using (lem-nat-0-CK40 ; lem-nat-0-CK41 ; lem-nat-0-SBOX⟨1·0·43·2⟩ ; lem-nat-0-SBOX⟨1·3·24·0⟩ ; lem-nat-1-CK10 ; lem-nat-1-CK20 ; lem-nat-1-CK40 ; lem-nat-2-CK20 ; lem-nat-2-CK30 ; lem-nat-2-CK40 ; lem-nat-2-SBOX⟨0·3·24·1⟩ ; lem-nat-3-CK30 ; lem-nat-3-CK40)
-- F1 toff-ccz: 190 steps
lem-F1-toff-ccz : Complete 4 → ⟪ (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
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
       at 2 4 (Toff104 ∷ []) (pw2 c4 (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Toff104 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (Toff104 ∷ []) (pw2 c4 (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Toff104 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (Toff214 ∷ []) (lw0 c4 (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (Toff124 ∷ []) (lw0 c4 (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (Toff214 ∷ []) (lw0 c4 (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (Toff214 ∷ []) (lw0 c4 (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (Toff124 ∷ []) (lw0 c4 (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (CK40 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CK40 ∷ S4 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ [])
  b5 = at 12 4 (Toff214 ∷ []) (lw0 c4 (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (Toff324 ∷ []) (lw0 c4 (CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (Toff234 ∷ []) (lw0 c4 (CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) (Toff234 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (Toff324 ∷ []) (lw0 c4 (CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (Toff104 ∷ []) (pw2 c4 (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Toff104 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (Toff104 ∷ []) (pw2 c4 (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Toff104 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (Toff214 ∷ []) (lw0 c4 (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 24 4 (Toff124 ∷ []) (lw0 c4 (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (CK40 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CK40 ∷ S4 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CK40 ∷ S4 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CK40 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ [])
  b6 = at 25 4 (Toff214 ∷ []) (lw0 c4 (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 27 4 (Toff214 ∷ []) (lw0 c4 (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 28 4 (Toff124 ∷ []) (lw0 c4 (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ []) tt tt Eq.refl) ▸
       at 29 4 (Toff214 ∷ []) (lw0 c4 (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 30 4 (Toff324 ∷ []) (lw0 c4 (CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 31 4 (Toff234 ∷ []) (lw0 c4 (CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) (Toff234 ∷ []) tt tt Eq.refl) ▸
       at 32 4 (Toff324 ∷ []) (lw0 c4 (CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 35 4 (Toff104 ∷ []) (pw2 c4 (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Toff104 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (CK40 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CK40 ∷ S4 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CK40 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ Bx3-0124 ∷ CK40 ∷ S4 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CK40 ∷ Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CK40 ∷ S4 ∷ [])
  b7 = at 38 4 (Toff104 ∷ []) (pw2 c4 (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Toff104 ∷ []) tt tt Eq.refl) ▸
       at 39 4 (Toff214 ∷ []) (lw0 c4 (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 40 4 (Toff124 ∷ []) (lw0 c4 (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ []) tt tt Eq.refl) ▸
       at 41 4 (Toff214 ∷ []) (lw0 c4 (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 43 4 (Toff214 ∷ []) (lw0 c4 (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 44 4 (Toff124 ∷ []) (lw0 c4 (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ []) tt tt Eq.refl) ▸
       at 45 4 (Toff214 ∷ []) (lw0 c4 (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
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
  b9 = at 4 0 (Toff312 ∷ Toff312 ∷ []) (lw4 c4 [] (Toff312 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Toff312 ∷ []) (lw4 c4 (Toff312 ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Toff312 ∷ []) (lw4 c4 (Toff312 ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx2-1034 ∷ []) (lem-sym12-at021021 c4) ▸
       at 6 1 (Bx2-1304 ∷ []) (lem-sym23-at0220 c4) ▸
       at 6 1 (Bx2-3104 ∷ []) (lem-sym12-at022330 c4) ▸
       at 5 3 (Bx2-3104 ∷ Bx3-2104 ∷ []) (lem-TW-at02132130 c4) ▸
       at 5 1 (Bx2-1304 ∷ []) (lem-sym12-at02132130 c4) ▸ done

  b10 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx2-1304 ∷ Bx3-2104 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-2104 ∷ Toff034 ∷ Toff034 ∷ Bx2-3401 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ [])
  b10 = at 5 1 (Bx2-1034 ∷ []) (lem-sym23-at022330 c4) ▸
       at 5 1 (Bx2-0134 ∷ []) (lem-sym12-at0220 c4) ▸
       at 5 2 (Bx3-2104 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0214⟩-at021021 c4) ▸
       at 6 0 (Toff034 ∷ Toff034 ∷ []) (pw1 c4 [] (Toff034 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
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
       at 8 0 (Toff312 ∷ Toff312 ∷ []) (lw4 c4 [] (Toff312 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Toff312 ∷ []) (lw4 c4 (Toff312 ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-2104 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff312 ∷ Bx2-0134 ∷ Toff312 ∷ Toff034 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-2104 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx2-0134 ∷ Bx3-2104 ∷ Toff034 ∷ [])
  b12 = at 11 1 (Toff312 ∷ []) (lw4 c4 (Toff312 ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (Bx2-1034 ∷ []) (lem-sym12-at021021 c4) ▸
       at 10 1 (Bx2-1304 ∷ []) (lem-sym23-at0220 c4) ▸
       at 10 1 (Bx2-3104 ∷ []) (lem-sym12-at022330 c4) ▸
       at 9 3 (Bx2-3104 ∷ Bx3-2104 ∷ []) (lem-TW-at02132130 c4) ▸
       at 9 1 (Bx2-1304 ∷ []) (lem-sym12-at02132130 c4) ▸
       at 9 1 (Bx2-1034 ∷ []) (lem-sym23-at022330 c4) ▸
       at 9 1 (Bx2-0134 ∷ []) (lem-sym12-at0220 c4) ▸ done

  b13 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-2104 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx2-0134 ∷ Bx3-2104 ∷ Toff034 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-2104 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx3-2104 ∷ Toff034 ∷ Bx2-3041 ∷ CCZ134 ∷ [])
  b13 = at 9 2 (Bx3-2104 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0214⟩-at021021 c4) ▸
       at 10 0 (Toff034 ∷ Toff034 ∷ []) (pw1 c4 [] (Toff034 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
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
       at 9 0 (Toff034 ∷ Toff034 ∷ []) (pw1 c4 [] (Toff034 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
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
       at 5 0 (Toff034 ∷ Toff034 ∷ []) (pw1 c4 [] (Toff034 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
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
       at 9 0 (Toff034 ∷ Toff034 ∷ []) (pw1 c4 [] (Toff034 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
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
       at 7 0 (Toff312 ∷ Toff312 ∷ []) (lw4 c4 [] (Toff312 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Toff312 ∷ []) (lw4 c4 (Toff312 ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (Toff312 ∷ []) (lw4 c4 (Toff312 ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸
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
       at 6 2 (Toff312 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff034 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff034 ∷ CCZ124 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at0112243043 c4) ▸
       at 0 4 (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ []) (sym (lem-KB-form c4)) ▸ done

  b23 : Chain (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ Bx0-1234 ∷ Bx2-0134 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  b23 = at 3 4 (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ []) (sym (lem-KB-form c4)) ▸
       at 2 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 [] (lem-beta-inv-at03102132 c4) ▸
       at 0 2 [] (lw4 c4 (K0 ∷ K0⁻ ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 [] (lw0 c4 (CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (sym (lem-F1-toff-ccz-nf-of-rhs c4)) ▸ done


-- auto S0 | BOX(1;2034): 6 steps
lem-auto-S0-∣-BOX⟨1·2034⟩ : Complete 4 → ⟪ (S0 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2034⟩ c4 = run b0
  where
  b0 : Chain (S0 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ S0 ∷ [])
  b0 = at 1 1 (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) (lem-beta-T-at011220 c4) ▸
       at 0 2 (Toff102 ∷ S0 ∷ []) (lw4 c4 (S0 ∷ Toff102 ∷ []) (Toff102 ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ134 ∷ S0 ∷ []) (c₁ (S) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 2 2 (Toff102 ∷ S0 ∷ []) (lw4 c4 (S0 ∷ Toff102 ∷ []) (Toff102 ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ134 ∷ S0 ∷ []) (c₁ (S) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 0 4 (Bx1-2034 ∷ []) (sym (lem-beta-T-at011220 c4)) ▸ done


-- auto S0 | SBOX(1;2;03;4): 11 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩ : Complete 4 → ⟪ (S0 ∷ Sb1-2-03-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-03-4 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (S0 ∷ Sb1-2-03-4 ∷ []) (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ S0 ∷ CS24⁻ ∷ [])
  b0 = at 1 1 (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ Sb⁻1-2-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-2034 ∷ S0 ∷ []) (lem-auto-S0-∣-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (Toff403 ∷ S0 ∷ []) (pw1 c4 (S0 ∷ Toff403 ∷ []) (Toff403 ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS24 ∷ []) (refl) ▸
       at 2 2 (CS24 ∷ S0 ∷ []) (lw1 c4 (S0 ∷ CS24 ∷ []) (CS24 ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-2-4-3 ∷ []) (refl) ▸
       at 3 2 (Toff403 ∷ S0 ∷ []) (pw1 c4 (S0 ∷ Toff403 ∷ []) (Toff403 ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS24⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ S0 ∷ CS24⁻ ∷ []) (Sb1-2-03-4 ∷ S0 ∷ [])
  b1 = at 4 2 (CS24⁻ ∷ S0 ∷ []) (lw1 c4 (S0 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻1-2-4-3 ∷ []) (refl) ▸
       at 0 5 (Sb1-2-03-4 ∷ []) (refl) ▸ done


-- auto S0 | SBOX(1;2;03;4) @0110: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0110 : Complete 4 → ⟪ (S1 ∷ Sb0-2-13-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-13-4 ∷ S1 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0110 c4 = run b0
  where
  b0 : Chain (S1 ∷ Sb0-2-13-4 ∷ []) (Sb0-2-13-4 ∷ S1 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ S1 ∷ []) (S0 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-2-03-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·13·4⟩ c4) ▸
       at 1 2 (Sb1-2-03-4 ∷ S0 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩ c4) ▸
       at 0 2 (Sb0-2-13-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·03·4⟩ c4) ▸
       at 1 2 (S1 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ S0 ∷ []) (S1 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto S0 | SBOX(1;2;03;4) @021021: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at021021 : Complete 4 → ⟪ (S2 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ S2 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at021021 c4 = run b0
  where
  b0 : Chain (S2 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-23-4 ∷ S2 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ S2 ∷ []) (S1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-2-13-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·23·4⟩ c4) ▸
       at 1 2 (Sb0-2-13-4 ∷ S1 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0110 c4) ▸
       at 0 2 (Sb0-1-23-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·13·4⟩ c4) ▸
       at 1 2 (S2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ S1 ∷ []) (S2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto S0 | SBOX(1;2;03;4) @03102132: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at03102132 : Complete 4 → ⟪ (S3 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ S3 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at03102132 c4 = run b0
  where
  b0 : Chain (S3 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-32-4 ∷ S3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S2 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ S3 ∷ []) (S2 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 1 2 (Sb0-1-23-4 ∷ S2 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at021021 c4) ▸
       at 0 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 1 2 (S3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto S0 | SBOX(1;2;03;4) @0410213243: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0410213243 : Complete 4 → ⟪ (S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ S4 ∷ []) (S3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ S3 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at03102132 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 1 2 (S4 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ S3 ∷ []) (S4 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto S0 | SBOX(1;2;03;4) @04203243: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at04203243 : Complete 4 → ⟪ (S4 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at04203243 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto S0 | SBOX(1;2;03;4) @0412203143: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0412203143 : Complete 4 → ⟪ (S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0412203143 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at04203243 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F2 iI|CS01: 1 steps
lem-F2-iI∣CS01 : Complete 4 → ⟪ (S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S4 ∷ []) ⟫ʷ
lem-F2-iI∣CS01 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S4 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0412203143 c4) ▸ done


-- F2 iI|CS02: 1 steps
lem-F2-iI∣CS02 : Complete 4 → ⟪ (S4 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ S4 ∷ []) ⟫ʷ
lem-F2-iI∣CS02 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ S4 ∷ [])
  b0 = at 0 2 (Sb1-0-42-3 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at04203243 c4) ▸ done


-- auto S0 | SBOX(1;2;03;4) @04102142: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at04102142 : Complete 4 → ⟪ (S4 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at04102142 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4) ▸
       at 0 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto S0 | SBOX(1;2;03;4) @042042: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at042042 : Complete 4 → ⟪ (S4 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at042042 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at04102142 c4) ▸
       at 0 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F2 iI|CS03: 1 steps
lem-F2-iI∣CS03 : Complete 4 → ⟪ (S4 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ S4 ∷ []) ⟫ʷ
lem-F2-iI∣CS03 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ S4 ∷ [])
  b0 = at 0 2 (Sb1-0-43-2 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at042042 c4) ▸ done


-- F2 iI|CS12: 1 steps
lem-F2-iI∣CS12 : Complete 4 → ⟪ (S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ S4 ∷ []) ⟫ʷ
lem-F2-iI∣CS12 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ S4 ∷ [])
  b0 = at 0 2 (Sb0-1-42-3 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4) ▸ done


-- F2 iI|CS13: 1 steps
lem-F2-iI∣CS13 : Complete 4 → ⟪ (S4 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ S4 ∷ []) ⟫ʷ
lem-F2-iI∣CS13 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ S4 ∷ [])
  b0 = at 0 2 (Sb0-1-43-2 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at04102142 c4) ▸ done


-- auto S0 | SBOX(1;2;03;4) @041041: 7 steps
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at041041 : Complete 4 → ⟪ (S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ S4 ∷ []) ⟫ʷ
lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at041041 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at04102142 c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F2 iI|CS23: 1 steps
lem-F2-iI∣CS23 : Complete 4 → ⟪ (S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ S4 ∷ []) ⟫ʷ
lem-F2-iI∣CS23 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ S4 ∷ [])
  b0 = at 0 2 (Sb0-2-43-1 ∷ S4 ∷ []) (lem-auto-S0-∣-SBOX⟨1·2·03·4⟩-at041041 c4) ▸ done


-- auto CS01 | BOX(1;2034): 3 steps
lem-auto-CS01-∣-BOX⟨1·2034⟩ : Complete 4 → ⟪ (CS01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2034⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CS01 ∷ [])
  b0 = at 0 1 (CS01 ∷ []) (lw4 c4 (CS01 ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Bx1-2034 ∷ CS01 ∷ []) (lem-CS20-beta-c-at011220 c4) ▸
       at 1 1 (CS01 ∷ []) (lw4 c4 (CS01 ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸ done


-- auto CS01 | SBOX(1;2;03;4): 11 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩ : Complete 4 → ⟪ (CS01 ∷ Sb1-2-03-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-03-4 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS01 ∷ Sb1-2-03-4 ∷ []) (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ CS01 ∷ CS24⁻ ∷ [])
  b0 = at 1 1 (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ Sb⁻1-2-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-2034 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (Toff403 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ Toff403 ∷ []) (Toff403 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS24 ∷ []) (refl) ▸
       at 2 2 (CS24 ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ CS24 ∷ []) (CS24 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-2-4-3 ∷ []) (refl) ▸
       at 3 2 (Toff403 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ Toff403 ∷ []) (Toff403 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS24⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ CS01 ∷ CS24⁻ ∷ []) (Sb1-2-03-4 ∷ CS01 ∷ [])
  b1 = at 4 2 (CS24⁻ ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻1-2-4-3 ∷ []) (refl) ▸
       at 0 5 (Sb1-2-03-4 ∷ []) (refl) ▸ done


-- auto CS01 | SBOX(1;2;03;4) @0110: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0110 : Complete 4 → ⟪ (CS01 ∷ Sb0-2-13-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-13-4 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0110 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Sb0-2-13-4 ∷ []) (Sb0-2-13-4 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-2-03-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·13·4⟩ c4) ▸
       at 1 2 (Sb1-2-03-4 ∷ CS01 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩ c4) ▸
       at 0 2 (Sb0-2-13-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·03·4⟩ c4) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | SBOX(1;2;03;4) @021021: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at021021 : Complete 4 → ⟪ (CS02 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at021021 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-23-4 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 2 2 (Sb0-2-13-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·23·4⟩ c4) ▸
       at 1 2 (Sb0-2-13-4 ∷ CS01 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0110 c4) ▸
       at 0 2 (Sb0-1-23-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·13·4⟩ c4) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | SBOX(1;2;03;4) @03102132: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at03102132 : Complete 4 → ⟪ (CS03 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ CS03 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at03102132 c4 = run b0
  where
  b0 : Chain (CS03 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-32-4 ∷ CS03 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 2 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 1 2 (Sb0-1-23-4 ∷ CS02 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at021021 c4) ▸
       at 0 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 1 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | SBOX(1;2;03;4) @0410213243: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0410213243 : Complete 4 → ⟪ (CS04 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS04 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 c4) ▸
       at 2 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ CS03 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at03102132 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 1 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- F2 S0|CS12: 1 steps
lem-F2-S0∣CS12 : Complete 4 → ⟪ (CS04 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0∣CS12 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS04 ∷ [])
  b0 = at 0 2 (Sb0-1-42-3 ∷ CS04 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4) ▸ done


-- auto CS01 | SBOX(1;2;03;4) @04102142: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at04102142 : Complete 4 → ⟪ (CS04 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at04102142 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CS04 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 c4) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ CS04 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4) ▸
       at 0 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F2 S0|CS13: 1 steps
lem-F2-S0∣CS13 : Complete 4 → ⟪ (CS04 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0∣CS13 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CS04 ∷ [])
  b0 = at 0 2 (Sb0-1-43-2 ∷ CS04 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at04102142 c4) ▸ done


-- auto CS01 | SBOX(1;2;03;4) @041041: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at041041 : Complete 4 → ⟪ (CS04 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at041041 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS04 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 c4) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ CS04 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at04102142 c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F2 S0|CS23: 1 steps
lem-F2-S0∣CS23 : Complete 4 → ⟪ (CS04 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0∣CS23 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS04 ∷ [])
  b0 = at 0 2 (Sb0-2-43-1 ∷ CS04 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at041041 c4) ▸ done


-- auto CS01 | SBOX(1;2;03;4) @04203243: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at04203243 : Complete 4 → ⟪ (CS14 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CS14 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at04203243 c4 = run b0
  where
  b0 : Chain (CS14 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CS14 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 c4) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ CS04 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F2 S1|CS02: 1 steps
lem-F2-S1∣CS02 : Complete 4 → ⟪ (CS14 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1∣CS02 c4 = run b0
  where
  b0 : Chain (CS14 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CS14 ∷ [])
  b0 = at 0 2 (Sb1-0-42-3 ∷ CS14 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at04203243 c4) ▸ done


-- auto CS01 | SBOX(1;2;03;4) @042042: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at042042 : Complete 4 → ⟪ (CS14 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ CS14 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at042042 c4 = run b0
  where
  b0 : Chain (CS14 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ CS14 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 c4) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ CS04 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at04102142 c4) ▸
       at 0 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F2 S1|CS03: 1 steps
lem-F2-S1∣CS03 : Complete 4 → ⟪ (CS14 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1∣CS03 c4 = run b0
  where
  b0 : Chain (CS14 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ CS14 ∷ [])
  b0 = at 0 2 (Sb1-0-43-2 ∷ CS14 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at042042 c4) ▸ done


-- F2 S1|CS23: 1 steps
lem-F2-S1∣CS23 : Complete 4 → ⟪ (CS14 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1∣CS23 c4 = run b0
  where
  b0 : Chain (CS14 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS14 ∷ [])
  b0 = at 0 2 (Sb0-2-43-1 ∷ CS14 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04203243 c4) ▸ done


-- auto CS01 | SBOX(1;2;03;4) @0412203143: 7 steps
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0412203143 : Complete 4 → ⟪ (CS24 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS24 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0412203143 c4 = run b0
  where
  b0 : Chain (CS24 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS24 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ CS14 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at04203243 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F2 S2|CS01: 1 steps
lem-F2-S2∣CS01 : Complete 4 → ⟪ (CS24 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2∣CS01 c4 = run b0
  where
  b0 : Chain (CS24 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS24 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ CS24 ∷ []) (lem-auto-CS01-∣-SBOX⟨1·2·03·4⟩-at0412203143 c4) ▸ done


-- auto CS01 | SBOX(2;3;04;1) @0412213043: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0412213043 : Complete 4 → ⟪ (CS24 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ CS24 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0412213043 c4 = run b0
  where
  b0 : Chain (CS24 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ CS24 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ CS24 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0412203143 c4) ▸
       at 0 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F2 S2|CS03: 1 steps
lem-F2-S2∣CS03 : Complete 4 → ⟪ (CS24 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2∣CS03 c4 = run b0
  where
  b0 : Chain (CS24 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ CS24 ∷ [])
  b0 = at 0 2 (Sb1-0-43-2 ∷ CS24 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0412213043 c4) ▸ done


-- F2 S2|CS13: 1 steps
lem-F2-S2∣CS13 : Complete 4 → ⟪ (CS24 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2∣CS13 c4 = run b0
  where
  b0 : Chain (CS24 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CS24 ∷ [])
  b0 = at 0 2 (Sb0-1-43-2 ∷ CS24 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0412203143 c4) ▸ done


-- F2 S3|CS01: 1 steps
lem-F2-S3∣CS01 : Complete 4 → ⟪ (CS34 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3∣CS01 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS34 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ CS34 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 c4) ▸ done


-- F2 S3|CS02: 1 steps
lem-F2-S3∣CS02 : Complete 4 → ⟪ (CS34 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3∣CS02 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CS34 ∷ [])
  b0 = at 0 2 (Sb1-0-42-3 ∷ CS34 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413213042 c4) ▸ done


-- F2 S3|CS12: 1 steps
lem-F2-S3∣CS12 : Complete 4 → ⟪ (CS34 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3∣CS12 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS34 ∷ [])
  b0 = at 0 2 (Sb0-1-42-3 ∷ CS34 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413203142 c4) ▸ done


-- auto iI | BOX(0;1234): 1 steps
lem-auto-iI-∣-BOX⟨0·1234⟩ : Complete 4 → ⟪ (ι ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ ι ∷ []) ⟫ʷ
lem-auto-iI-∣-BOX⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (ι ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ ι ∷ [])
  b0 = at 0 2 (Bx0-1234 ∷ ι ∷ []) (sym zc) ▸ done


-- auto K0 | BOX(0;1234) @1221: 7 steps
lem-auto-K0-∣-BOX⟨0·1234⟩-at1221 : Complete 4 → ⟪ (K0 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ K0 ∷ []) ⟫ʷ
lem-auto-K0-∣-BOX⟨0·1234⟩-at1221 c4 = run b0
  where
  b0 : Chain (K0 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ K0 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ K0 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩ c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto K0 | BOX(0;1234) @011220: 7 steps
lem-auto-K0-∣-BOX⟨0·1234⟩-at011220 : Complete 4 → ⟪ (K1 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ K1 ∷ []) ⟫ʷ
lem-auto-K0-∣-BOX⟨0·1234⟩-at011220 c4 = run b0
  where
  b0 : Chain (K1 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ K1 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (Bx0-2134 ∷ K0 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩-at1221 c4) ▸
       at 0 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (K1 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto iI | BOX(0;1234) @1221: 7 steps
lem-auto-iI-∣-BOX⟨0·1234⟩-at1221 : Complete 4 → ⟪ (ι ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ ι ∷ []) ⟫ʷ
lem-auto-iI-∣-BOX⟨0·1234⟩-at1221 c4 = run b0
  where
  b0 : Chain (ι ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ ι ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 2 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ ι ∷ []) (lem-auto-iI-∣-BOX⟨0·1234⟩ c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto iI | BOX(0;1234) @011220: 7 steps
lem-auto-iI-∣-BOX⟨0·1234⟩-at011220 : Complete 4 → ⟪ (ι ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ ι ∷ []) ⟫ʷ
lem-auto-iI-∣-BOX⟨0·1234⟩-at011220 c4 = run b0
  where
  b0 : Chain (ι ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ ι ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (ι ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (Bx0-2134 ∷ ι ∷ []) (lem-auto-iI-∣-BOX⟨0·1234⟩-at1221 c4) ▸
       at 0 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (ι ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CK01 | BOX(1;2034): 9 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩ : Complete 4 → ⟪ (CK01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CK01 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ [])
  b0 = at 0 1 (ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) (lw4 c4 (CK01 ∷ []) (ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Bx1-2034 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩ c4) ▸
       at 5 2 (Bx1-2034 ∷ K1 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩-at011220 c4) ▸
       at 4 2 (Bx1-2034 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩ c4) ▸
       at 3 2 (Bx1-2034 ∷ K1 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩-at011220 c4) ▸
       at 2 2 (Bx1-2034 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (Bx1-2034 ∷ S0⁻ ∷ []) (lem-auto-Sd0-∣-BOX⟨1·2034⟩ c4) ▸
       at 0 2 (Bx1-2034 ∷ ι ∷ []) (lem-auto-iI-∣-BOX⟨0·1234⟩-at011220 c4) ▸ done

  b1 : Chain (Bx1-2034 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) (Bx1-2034 ∷ CK01 ∷ [])
  b1 = at 1 7 (CK01 ∷ []) (lw4 c4 (ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) (CK01 ∷ []) tt tt Eq.refl) ▸ done


-- auto CK01 | SBOX(1;2;03;4): 11 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩ : Complete 4 → ⟪ (CK01 ∷ Sb1-2-03-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-03-4 ∷ CK01 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK01 ∷ Sb1-2-03-4 ∷ []) (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ CK01 ∷ CS24⁻ ∷ [])
  b0 = at 1 1 (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ Sb⁻1-2-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-2034 ∷ CK01 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (Toff403 ∷ CK01 ∷ []) (pw2 c4 (CK01 ∷ Toff403 ∷ []) (Toff403 ∷ CK01 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS24 ∷ []) (refl) ▸
       at 2 2 (CS24 ∷ CK01 ∷ []) (pw3 c4 (CK01 ∷ CS24 ∷ []) (CS24 ∷ CK01 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-2-4-3 ∷ []) (refl) ▸
       at 3 2 (Toff403 ∷ CK01 ∷ []) (pw2 c4 (CK01 ∷ Toff403 ∷ []) (Toff403 ∷ CK01 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS24⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ CK01 ∷ CS24⁻ ∷ []) (Sb1-2-03-4 ∷ CK01 ∷ [])
  b1 = at 4 2 (CS24⁻ ∷ CK01 ∷ []) (pw3 c4 (CK01 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CK01 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻1-2-4-3 ∷ []) (refl) ▸
       at 0 5 (Sb1-2-03-4 ∷ []) (refl) ▸ done


-- auto CK01 | SBOX(1;2;03;4) @0110: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0110 : Complete 4 → ⟪ (CK10 ∷ Sb0-2-13-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-13-4 ∷ CK10 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0110 c4 = run b0
  where
  b0 : Chain (CK10 ∷ Sb0-2-13-4 ∷ []) (Sb0-2-13-4 ∷ CK10 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CK10 ∷ []) (CK01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-2-03-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·13·4⟩ c4) ▸
       at 1 2 (Sb1-2-03-4 ∷ CK01 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩ c4) ▸
       at 0 2 (Sb0-2-13-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·03·4⟩ c4) ▸
       at 1 2 (CK10 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CK01 ∷ []) (CK10 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CK01 | SBOX(1;2;03;4) @021021: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at021021 : Complete 4 → ⟪ (CK20 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ CK20 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at021021 c4 = run b0
  where
  b0 : Chain (CK20 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-23-4 ∷ CK20 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK10 ∷ Sw12 ∷ []) (lem-nat-1-CK20 c4) ▸
       at 2 2 (Sb0-2-13-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·23·4⟩ c4) ▸
       at 1 2 (Sb0-2-13-4 ∷ CK10 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0110 c4) ▸
       at 0 2 (Sb0-1-23-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·13·4⟩ c4) ▸
       at 1 2 (CK20 ∷ Sw12 ∷ []) (lem-nat-1-CK10 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CK01 | SBOX(1;2;03;4) @03102132: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at03102132 : Complete 4 → ⟪ (CK30 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ CK30 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at03102132 c4 = run b0
  where
  b0 : Chain (CK30 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-32-4 ∷ CK30 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK20 ∷ Sw23 ∷ []) (lem-nat-2-CK30 c4) ▸
       at 2 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 1 2 (Sb0-1-23-4 ∷ CK20 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at021021 c4) ▸
       at 0 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 1 2 (CK30 ∷ Sw23 ∷ []) (lem-nat-2-CK20 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CK01 | SBOX(1;2;03;4) @0410213243: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0410213243 : Complete 4 → ⟪ (CK40 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK40 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK40 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK30 ∷ Sw34 ∷ []) (lem-nat-3-CK40 c4) ▸
       at 2 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ CK30 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at03102132 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 1 2 (CK40 ∷ Sw34 ∷ []) (lem-nat-3-CK30 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- F2 K0|CS12: 1 steps
lem-F2-K0∣CS12 : Complete 4 → ⟪ (CK40 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0∣CS12 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK40 ∷ [])
  b0 = at 0 2 (Sb0-1-42-3 ∷ CK40 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4) ▸ done


-- auto CK01 | SBOX(1;2;03;4) @04102142: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at04102142 : Complete 4 → ⟪ (CK40 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CK40 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at04102142 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CK40 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 c4) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ CK40 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4) ▸
       at 0 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F2 K0|CS13: 1 steps
lem-F2-K0∣CS13 : Complete 4 → ⟪ (CK40 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0∣CS13 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CK40 ∷ [])
  b0 = at 0 2 (Sb0-1-43-2 ∷ CK40 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at04102142 c4) ▸ done


-- auto CK01 | SBOX(1;2;03;4) @041041: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at041041 : Complete 4 → ⟪ (CK40 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CK40 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at041041 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CK40 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 c4) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ CK40 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at04102142 c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F2 K0|CS23: 1 steps
lem-F2-K0∣CS23 : Complete 4 → ⟪ (CK40 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0∣CS23 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CK40 ∷ [])
  b0 = at 0 2 (Sb0-2-43-1 ∷ CK40 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at041041 c4) ▸ done


-- auto CK01 | SBOX(1;2;03;4) @04203243: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at04203243 : Complete 4 → ⟪ (CK41 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CK41 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at04203243 c4 = run b0
  where
  b0 : Chain (CK41 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CK41 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 c4) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ CK40 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (CK41 ∷ Sw01 ∷ []) (lem-nat-0-CK40 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F2 K1|CS02: 1 steps
lem-F2-K1∣CS02 : Complete 4 → ⟪ (CK41 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CK41 ∷ []) ⟫ʷ
lem-F2-K1∣CS02 c4 = run b0
  where
  b0 : Chain (CK41 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CK41 ∷ [])
  b0 = at 0 2 (Sb1-0-42-3 ∷ CK41 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at04203243 c4) ▸ done


-- auto CK01 | SBOX(1;2;03;4) @042042: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at042042 : Complete 4 → ⟪ (CK41 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ CK41 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at042042 c4 = run b0
  where
  b0 : Chain (CK41 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ CK41 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 c4) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ CK40 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at04102142 c4) ▸
       at 0 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (CK41 ∷ Sw01 ∷ []) (lem-nat-0-CK40 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F2 K1|CS03: 1 steps
lem-F2-K1∣CS03 : Complete 4 → ⟪ (CK41 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ CK41 ∷ []) ⟫ʷ
lem-F2-K1∣CS03 c4 = run b0
  where
  b0 : Chain (CK41 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ CK41 ∷ [])
  b0 = at 0 2 (Sb1-0-43-2 ∷ CK41 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at042042 c4) ▸ done


-- F0 @0314203142: 5 steps
lem-F0-at0314203142 : Complete 4 → ⟪ (Sb0-3-24-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-24-0 ∷ []) ⟫ʷ
lem-F0-at0314203142 c4 = run b0
  where
  b0 : Chain (Sb0-3-24-1 ∷ []) (Sb1-3-24-0 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-2-34-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·3·24·1⟩ c4) ▸
       at 1 1 (Sb1-2-34-0 ∷ []) (lem-F0-at0214203143 c4) ▸
       at 0 2 (Sb1-3-24-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·2·34·0⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0 @0314213042: 5 steps
lem-F0-at0314213042 : Complete 4 → ⟪ (Sb1-3-24-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-24-1 ∷ []) ⟫ʷ
lem-F0-at0314213042 c4 = run b0
  where
  b0 : Chain (Sb1-3-24-0 ∷ []) (Sb0-3-24-1 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-3-24-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·3·24·0⟩ c4) ▸
       at 1 1 (Sb1-3-24-0 ∷ []) (lem-F0-at0314203142 c4) ▸
       at 0 2 (Sb0-3-24-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·3·24·0⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


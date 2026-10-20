{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D178 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0035 ; wl0036 ; wl0138 ; wl0139 ; wl0212 ; wl0283 ; wl0333 ; wl0353 ; wl0729 ; wl0731 ; wl0732 ; wl0759 ; wl0760 ; wl0761 ; wl0762 ; wl0763 ; wl0764 ; wl0765 ; wl0766 ; wl0767 ; wl0768 ; wl0769 ; wl0770 ; wl0771 ; wl0772 ; wl0773 ; wl0774 ; wl0775 ; wl0776 ; wl0777 ; wl0778 ; wl0779 ; wl0780 ; wl0781 ; wl0782 ; wl0783 ; wl0784 ; wl0785 ; wl0786 ; wp0043 ; wp0044 ; wp0126 ; wp0178 ; wp0348 ; wp0349 ; wp0351 ; wp0352 ; wp0365 ; wp0397 ; wp0398 ; wp0399 ; wp0400 ; wp0401 ; wp0402 ; wp0403 ; wp0404 ; wp0405 ; wp0406 ; wp0407 ; wp0408 ; wp0409 ; wp0410 ; wp0411)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-Cz-beta ; lem-beta-T-at243243 ; lem-sym23 ; lem-sym34 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym23-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-SBsym-at0113203442 ; lem-T312-beta-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at243243 ; lem-beta-T-at233442 ; lem-sym23-at233442 ; lem-sym23-at2442 ; lem-sym34-at243243 ; lem-sym34-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D160 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS02-at2332 ; lem-sym12-at04103143 ; lem-sym12-at0412203143 ; lem-sym23-at0412203143)
open import Examples.Groups.Clifford+CS.Five.D.D161 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ123 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ403 ; lem-auto-CS01-∣-BOX⟨1·2304⟩ ; lem-auto-CSd01-∣-BOX⟨1·2304⟩ ; lem-beta-T-at0412203143)
open import Examples.Groups.Clifford+CS.Five.D.D173 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D174 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-auto-CCZ012-∣-CCZ342-at0410233142 ; lem-auto-CCZ012-∣-TOFF342-at3443 ; lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0412233041)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0412⟩)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨2·0413⟩ ; lem-nat-0-BOX⟨2·1403⟩ ; lem-nat-1-CSd02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-1-CSd01 ; lem-nat-3-BOX⟨3·0412⟩ ; lem-nat-3-SBOX⟨3·0·2·1⟩ ; lem-nat-3-SBOXd⟨3·0·2·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-BOX⟨1·2403⟩ ; lem-nat-1-BOX⟨2·1403⟩ ; lem-nat-3-BOX⟨1·2304⟩ ; lem-nat-3-BOX⟨1·2403⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-2-BOX⟨4·0213⟩ ; lem-nat-2-BOX⟨4·0312⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-2-SBOX⟨4·0·2·1⟩ ; lem-nat-2-SBOXd⟨4·0·2·1⟩ ; lem-nat-2-SBOXd⟨4·0·3·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-0-BOX⟨4·2103⟩ ; lem-nat-2-SBOX⟨4·0·3·1⟩ ; lem-nat-3-BOX⟨4·0312⟩ ; lem-nat-3-SBOX⟨4·0·2·1⟩ ; lem-nat-3-SBOXd⟨4·0·2·1⟩)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CK40 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (wp0126 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (X4 ∷ ι ∷ []) (ι ∷ X4 ∷ []) (zc)
  q3 : Ws → Eqn
  q3 c4 = eqn (Sb0-1-42-3 ∷ ι ∷ []) (ι ∷ Sb0-1-42-3 ∷ []) (zc)
  q4 : Ws → Eqn
  q4 c4 = eqn (X4 ∷ X4 ∷ []) [] (wl0283 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (S4⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ X4 ∷ S4⁻ ∷ []) (wl0769 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (S4⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ S4⁻ ∷ []) (wl0770 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (S4⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ S4⁻ ∷ []) (wl0771 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Bx0-1423 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ X4 ∷ S4⁻ ∷ []) (wp0407 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ S4⁻ ∷ []) (wp0408 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CS04 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ X4 ∷ CS04 ∷ []) (wp0397 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CS04 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ CS04 ∷ []) (wp0398 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (CS04 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ CS04 ∷ []) (wp0399 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ X4 ∷ CS04 ∷ []) (wp0400 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ CS04 ∷ []) (wp0401 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (K0 ∷ X4 ∷ []) (X4 ∷ K0 ∷ []) (wl0772 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (Sb0-1-42-3 ∷ K0 ∷ []) (K0 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at243243 c4)

-- F4 CS12^0|K0^1: 131 steps
lem-F4-CS12ᵖ0∣K0ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣K0ᵖ1 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw 3 (q1 c4) ∷
   rw 2 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 0 (q2 c4) ∷
   re 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 12 (q4 c4) ∷
   re 14 1 (CS13⁻ ∷ []) ∷
   rw⁻ 13 (q5 c4) ∷
   re 15 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 10 (q6 c4) ∷
   re 8 1 (CS13 ∷ []) ∷
   rw⁻ 7 (q7 c4) ∷
   re 9 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 4 (q6 c4) ∷
   rw 2 (q8 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 10 (q9 c4) ∷
   rw⁻ 7 (q10 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   rw 4 (q4 c4) ∷
   rw 5 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw⁻ 3 (q8 c4) ∷
   rw 4 (q4 c4) ∷
   rw 5 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw 7 (q4 c4) ∷
   re 3 5 (Sb0-1-42-3 ∷ []) ∷
   re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw⁻ 13 (q4 c4) ∷
   re 15 1 (CS13⁻ ∷ []) ∷
   rw⁻ 14 (q11 c4) ∷
   re 16 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 11 (q12 c4) ∷
   re 9 1 (CS13 ∷ []) ∷
   rw⁻ 8 (q13 c4) ∷
   re 10 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 5 (q12 c4) ∷
   rw 3 (q8 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw⁻ 11 (q14 c4) ∷
   rw⁻ 8 (q15 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   rw⁻ 2 (q15 c4) ∷
   rw 5 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw 7 (q4 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 5 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw 7 (q4 c4) ∷
   rw 8 (q4 c4) ∷
   re 4 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 5 (q16 c4) ∷
   rw 4 (q17 c4) ∷
   rw⁻ 3 (q16 c4) ∷
   re 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 12 (q4 c4) ∷
   rw⁻ 15 (q4 c4) ∷
   re 17 1 (CS13⁻ ∷ []) ∷
   rw⁻ 16 (q11 c4) ∷
   re 18 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 13 (q12 c4) ∷
   re 11 1 (CS13 ∷ []) ∷
   rw⁻ 10 (q13 c4) ∷
   re 12 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 7 (q12 c4) ∷
   rw 5 (q8 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 12 (q4 c4) ∷
   rw⁻ 13 (q14 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   rw 7 (q4 c4) ∷
   rw 8 (q4 c4) ∷
   rw 9 (q4 c4) ∷
   rw⁻ 6 (q8 c4) ∷
   rw 7 (q4 c4) ∷
   rw 8 (q4 c4) ∷
   rw 9 (q4 c4) ∷
   rw 10 (q4 c4) ∷
   re 6 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 7 (q16 c4) ∷
   rw 6 (q17 c4) ∷
   rw⁻ 5 (q16 c4) ∷
   re 7 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 8 (q4 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 14 (q4 c4) ∷
   rw⁻ 17 (q4 c4) ∷
   re 19 1 (CS13⁻ ∷ []) ∷
   rw⁻ 18 (q11 c4) ∷
   re 20 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 15 (q12 c4) ∷
   re 13 1 (CS13 ∷ []) ∷
   rw⁻ 12 (q13 c4) ∷
   re 14 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 9 (q12 c4) ∷
   rw 7 (q8 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 14 (q4 c4) ∷
   rw⁻ 15 (q14 c4) ∷
   rw⁻ 12 (q15 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 6 (q15 c4) ∷
   rw 9 (q4 c4) ∷
   rw 10 (q4 c4) ∷
   rw 11 (q4 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 9 (q4 c4) ∷
   rw 10 (q4 c4) ∷
   rw 11 (q4 c4) ∷
   rw 12 (q4 c4) ∷
   re 8 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷ []) Eq.refl

private
  q18 : Ws → Eqn
  q18 c4 = eqn (CK41 ∷ []) (ι1 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (wp0178 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (ι1 ∷ []) (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl)
  q20 : Ws → Eqn
  q20 c4 = eqn (CS14 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ X4 ∷ CS14 ∷ []) (wl0759 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (CS14 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ CS14 ∷ []) (wl0760 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CS14 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ CS14 ∷ []) (wl0761 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ023 ∷ []) (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0353 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (wp0365 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ []) (wl0762 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ []) (wp0348 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ []) (wp0349 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ []) (wp0402 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) (wl0773 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) (wl0774 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (K1 ∷ X4 ∷ []) (X4 ∷ K1 ∷ []) (c₂ (K ↑) (X ↑ ↑))
  q32 : Ws → Eqn
  q32 c4 = eqn (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) (wp0409 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (ι ∷ []) (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl)

-- F4 CS12^0|K1^1: 221 steps
lem-F4-CS12ᵖ0∣K1ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣K1ᵖ1 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw 3 (q18 c4) ∷
   rw 3 (q19 c4) ∷
   rw 2 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 0 (q2 c4) ∷
   re 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 12 (q4 c4) ∷
   re 14 1 (CS13⁻ ∷ []) ∷
   rw⁻ 13 (q5 c4) ∷
   re 15 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 10 (q6 c4) ∷
   re 8 1 (CS13 ∷ []) ∷
   rw⁻ 7 (q7 c4) ∷
   re 9 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 4 (q6 c4) ∷
   rw 2 (q8 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 10 (q9 c4) ∷
   rw⁻ 7 (q10 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   rw 4 (q4 c4) ∷
   rw 5 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw⁻ 3 (q8 c4) ∷
   rw 4 (q4 c4) ∷
   rw 5 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw 7 (q4 c4) ∷
   re 3 5 (Sb0-1-42-3 ∷ []) ∷
   re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw⁻ 13 (q4 c4) ∷
   re 15 1 (CS13⁻ ∷ []) ∷
   rw⁻ 14 (q20 c4) ∷
   re 16 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 11 (q21 c4) ∷
   re 9 1 (CS13 ∷ []) ∷
   rw⁻ 8 (q22 c4) ∷
   re 10 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 5 (q21 c4) ∷
   rw 3 (q8 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw 12 (q23 c4) ∷
   rw⁻ 13 (q4 c4) ∷
   rw⁻ 16 (q4 c4) ∷
   rw⁻ 19 (q4 c4) ∷
   rw⁻ 22 (q4 c4) ∷
   rw⁻ 23 (q24 c4) ∷
   rw⁻ 20 (q25 c4) ∷
   rw⁻ 17 (q26 c4) ∷
   rw⁻ 14 (q25 c4) ∷
   rw⁻ 11 (q27 c4) ∷
   rw 14 (q4 c4) ∷
   rw 15 (q4 c4) ∷
   rw 16 (q4 c4) ∷
   rw 17 (q4 c4) ∷
   rw⁻ 13 (q23 c4) ∷
   rw⁻ 8 (q28 c4) ∷
   rw 6 (q23 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw⁻ 13 (q4 c4) ∷
   rw⁻ 16 (q4 c4) ∷
   rw⁻ 17 (q24 c4) ∷
   rw⁻ 14 (q25 c4) ∷
   rw⁻ 11 (q26 c4) ∷
   rw⁻ 8 (q25 c4) ∷
   rw⁻ 5 (q27 c4) ∷
   rw 8 (q4 c4) ∷
   rw 9 (q4 c4) ∷
   rw 10 (q4 c4) ∷
   rw 11 (q4 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   rw⁻ 2 (q28 c4) ∷
   rw 5 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw 7 (q4 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 5 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw 7 (q4 c4) ∷
   rw 8 (q4 c4) ∷
   re 4 5 (Sb0-1-42-3 ∷ []) ∷
   re 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 14 (q4 c4) ∷
   re 10 1 (CS13 ∷ []) ∷
   re 16 1 (CS13⁻ ∷ []) ∷
   rw⁻ 9 (q29 c4) ∷
   re 13 1 (Sb0-1-3-2 ∷ []) ∷
   re 19 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 6 (q30 c4) ∷
   rw 4 (q8 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 14 (q31 c4) ∷
   rw 13 (q32 c4) ∷
   rw⁻ 12 (q31 c4) ∷
   rw 14 (q23 c4) ∷
   rw⁻ 15 (q4 c4) ∷
   rw⁻ 18 (q4 c4) ∷
   rw⁻ 21 (q4 c4) ∷
   rw⁻ 24 (q4 c4) ∷
   rw⁻ 25 (q24 c4) ∷
   rw⁻ 22 (q25 c4) ∷
   rw⁻ 19 (q26 c4) ∷
   rw⁻ 16 (q25 c4) ∷
   rw⁻ 13 (q27 c4) ∷
   rw 16 (q4 c4) ∷
   rw 17 (q4 c4) ∷
   rw 18 (q4 c4) ∷
   rw 19 (q4 c4) ∷
   rw⁻ 15 (q23 c4) ∷
   rw⁻ 16 (q31 c4) ∷
   rw 15 (q32 c4) ∷
   rw⁻ 14 (q31 c4) ∷
   rw⁻ 9 (q33 c4) ∷
   rw⁻ 8 (q31 c4) ∷
   rw 7 (q32 c4) ∷
   rw⁻ 6 (q31 c4) ∷
   rw 8 (q23 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 12 (q4 c4) ∷
   rw⁻ 15 (q4 c4) ∷
   rw⁻ 18 (q4 c4) ∷
   rw⁻ 19 (q24 c4) ∷
   rw⁻ 16 (q25 c4) ∷
   rw⁻ 13 (q26 c4) ∷
   rw⁻ 10 (q25 c4) ∷
   rw⁻ 7 (q27 c4) ∷
   rw 10 (q4 c4) ∷
   rw 11 (q4 c4) ∷
   rw 12 (q4 c4) ∷
   rw 13 (q4 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   rw⁻ 10 (q31 c4) ∷
   rw 9 (q32 c4) ∷
   rw⁻ 8 (q31 c4) ∷
   rw⁻ 3 (q33 c4) ∷
   rw 8 (q4 c4) ∷
   rw 9 (q4 c4) ∷
   rw 10 (q4 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw 8 (q4 c4) ∷
   rw 9 (q4 c4) ∷
   rw 10 (q4 c4) ∷
   rw 11 (q4 c4) ∷
   re 7 5 (Sb0-1-42-3 ∷ []) ∷
   re 7 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 8 (q4 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 14 (q4 c4) ∷
   rw⁻ 17 (q4 c4) ∷
   re 19 1 (CS13⁻ ∷ []) ∷
   rw⁻ 18 (q20 c4) ∷
   re 20 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 15 (q21 c4) ∷
   re 13 1 (CS13 ∷ []) ∷
   rw⁻ 12 (q22 c4) ∷
   re 14 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 9 (q21 c4) ∷
   rw 7 (q8 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 14 (q4 c4) ∷
   rw 16 (q23 c4) ∷
   rw⁻ 17 (q4 c4) ∷
   rw⁻ 20 (q4 c4) ∷
   rw⁻ 23 (q4 c4) ∷
   rw⁻ 26 (q4 c4) ∷
   rw⁻ 27 (q24 c4) ∷
   rw⁻ 24 (q25 c4) ∷
   rw⁻ 21 (q26 c4) ∷
   rw⁻ 18 (q25 c4) ∷
   rw⁻ 15 (q27 c4) ∷
   rw 18 (q4 c4) ∷
   rw 19 (q4 c4) ∷
   rw 20 (q4 c4) ∷
   rw 21 (q4 c4) ∷
   rw⁻ 17 (q23 c4) ∷
   rw⁻ 12 (q28 c4) ∷
   rw 10 (q23 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 14 (q4 c4) ∷
   rw⁻ 17 (q4 c4) ∷
   rw⁻ 20 (q4 c4) ∷
   rw⁻ 21 (q24 c4) ∷
   rw⁻ 18 (q25 c4) ∷
   rw⁻ 15 (q26 c4) ∷
   rw⁻ 12 (q25 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw 12 (q4 c4) ∷
   rw 13 (q4 c4) ∷
   rw 14 (q4 c4) ∷
   rw 15 (q4 c4) ∷
   rw⁻ 11 (q23 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw 9 (q4 c4) ∷
   rw 10 (q4 c4) ∷
   rw 11 (q4 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 9 (q4 c4) ∷
   rw 10 (q4 c4) ∷
   rw 11 (q4 c4) ∷
   rw 12 (q4 c4) ∷
   re 8 5 (Sb0-1-42-3 ∷ []) ∷
   rw 0 (q34 c4) ∷
   rw⁻ 0 (q18 c4) ∷ []) Eq.refl

private
  q35 : Ws → Eqn
  q35 c4 = eqn (CK42 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (wl0729 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CS24 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ X4 ∷ CS24 ∷ []) (wl0763 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (CS24 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ CS24 ∷ []) (wl0764 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CS24 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ CS24 ∷ []) (wl0765 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CS24 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ X4 ∷ CS24 ∷ []) (wp0403 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CS24 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ CS24 ∷ []) (wp0404 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ []) (wl0776 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ []) (wl0777 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ []) (wl0778 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (Bx0-1423 ∷ []) (Bx0-1432 ∷ []) (lem-sym34-at243243 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (Bx0-1432 ∷ []) (Bx0-1342 ∷ []) (lem-sym23-at2442 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (Bx0-1342 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ []) (wp0410 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (K2 ∷ X4 ∷ []) (X4 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (X ↑))
  q49 : Ws → Eqn
  q49 c4 = eqn (K2 ∷ Toff013 ∷ []) (Toff013 ∷ K2 ∷ []) (wl0779 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) (wl0780 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (X4 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ []) (wl0781 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0333 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ []) (wp0411 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ []) (wl0782 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ []) (wp0351 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ []) (wp0352 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) (X4 ∷ K0 ∷ X4 ∷ CS24 ∷ []) (wl0783 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (Bx0-1342 ∷ []) (Bx0-1432 ∷ []) (lem-sym23-at233442 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (Bx0-1432 ∷ []) (Bx0-1423 ∷ []) (lem-sym34-at2442 c4)

-- F4 CS12^0|K2^1: 185 steps
lem-F4-CS12ᵖ0∣K2ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣K2ᵖ1 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw 3 (q35 c4) ∷
   rw 2 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 0 (q2 c4) ∷
   re 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 12 (q4 c4) ∷
   re 14 1 (CS13⁻ ∷ []) ∷
   rw⁻ 13 (q5 c4) ∷
   re 15 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 10 (q6 c4) ∷
   re 8 1 (CS13 ∷ []) ∷
   rw⁻ 7 (q7 c4) ∷
   re 9 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 4 (q6 c4) ∷
   rw 2 (q8 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 10 (q9 c4) ∷
   rw⁻ 7 (q10 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   rw 4 (q4 c4) ∷
   rw 5 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw⁻ 3 (q8 c4) ∷
   rw 4 (q4 c4) ∷
   rw 5 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw 7 (q4 c4) ∷
   re 3 5 (Sb0-1-42-3 ∷ []) ∷
   re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw⁻ 13 (q4 c4) ∷
   re 15 1 (CS13⁻ ∷ []) ∷
   rw⁻ 14 (q36 c4) ∷
   re 16 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 11 (q37 c4) ∷
   re 9 1 (CS13 ∷ []) ∷
   rw⁻ 8 (q38 c4) ∷
   re 10 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 5 (q37 c4) ∷
   rw 3 (q8 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw⁻ 11 (q39 c4) ∷
   rw⁻ 8 (q40 c4) ∷
   rw⁻ 5 (q39 c4) ∷
   rw⁻ 2 (q40 c4) ∷
   rw 5 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw 7 (q4 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 5 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw 7 (q4 c4) ∷
   rw 8 (q4 c4) ∷
   re 4 5 (Sb0-1-42-3 ∷ []) ∷
   re 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 14 (q4 c4) ∷
   re 16 1 (CS13⁻ ∷ []) ∷
   rw⁻ 15 (q41 c4) ∷
   re 19 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 12 (q42 c4) ∷
   re 10 1 (CS13 ∷ []) ∷
   rw⁻ 9 (q43 c4) ∷
   re 13 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 6 (q42 c4) ∷
   rw 4 (q44 c4) ∷
   rw 4 (q45 c4) ∷
   rw 4 (q46 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 12 (q47 c4) ∷
   rw⁻ 11 (q48 c4) ∷
   rw⁻ 10 (q49 c4) ∷
   rw⁻ 9 (q48 c4) ∷
   rw⁻ 11 (q50 c4) ∷
   rw⁻ 12 (q4 c4) ∷
   rw⁻ 15 (q4 c4) ∷
   rw⁻ 16 (q51 c4) ∷
   rw 14 (q52 c4) ∷
   rw⁻ 15 (q4 c4) ∷
   rw⁻ 18 (q4 c4) ∷
   rw⁻ 21 (q4 c4) ∷
   rw⁻ 24 (q4 c4) ∷
   rw⁻ 25 (q53 c4) ∷
   rw⁻ 22 (q54 c4) ∷
   rw⁻ 19 (q55 c4) ∷
   rw⁻ 16 (q54 c4) ∷
   rw⁻ 13 (q56 c4) ∷
   rw 16 (q4 c4) ∷
   rw 17 (q4 c4) ∷
   rw 18 (q4 c4) ∷
   rw 19 (q4 c4) ∷
   rw⁻ 15 (q52 c4) ∷
   rw⁻ 10 (q57 c4) ∷
   rw 13 (q4 c4) ∷
   rw 14 (q4 c4) ∷
   rw 12 (q50 c4) ∷
   rw⁻ 13 (q48 c4) ∷
   rw⁻ 12 (q49 c4) ∷
   rw⁻ 11 (q48 c4) ∷
   rw⁻ 6 (q47 c4) ∷
   rw⁻ 5 (q48 c4) ∷
   rw⁻ 4 (q49 c4) ∷
   rw⁻ 3 (q48 c4) ∷
   rw⁻ 5 (q50 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 10 (q51 c4) ∷
   rw 8 (q52 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 12 (q4 c4) ∷
   rw⁻ 15 (q4 c4) ∷
   rw⁻ 18 (q4 c4) ∷
   rw⁻ 19 (q53 c4) ∷
   rw⁻ 16 (q54 c4) ∷
   rw⁻ 13 (q55 c4) ∷
   rw⁻ 10 (q54 c4) ∷
   rw⁻ 7 (q56 c4) ∷
   rw 10 (q4 c4) ∷
   rw 11 (q4 c4) ∷
   rw 12 (q4 c4) ∷
   rw 13 (q4 c4) ∷
   rw⁻ 9 (q52 c4) ∷
   rw⁻ 4 (q57 c4) ∷
   rw 7 (q4 c4) ∷
   rw 8 (q4 c4) ∷
   rw 6 (q50 c4) ∷
   rw⁻ 7 (q48 c4) ∷
   rw⁻ 6 (q49 c4) ∷
   rw⁻ 5 (q48 c4) ∷
   rw 8 (q4 c4) ∷
   rw 9 (q4 c4) ∷
   rw 10 (q4 c4) ∷
   rw⁻ 7 (q46 c4) ∷
   rw 7 (q58 c4) ∷
   rw 7 (q59 c4) ∷
   rw 8 (q4 c4) ∷
   rw 9 (q4 c4) ∷
   rw 10 (q4 c4) ∷
   rw 11 (q4 c4) ∷
   re 7 5 (Sb0-1-42-3 ∷ []) ∷
   re 7 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 8 (q4 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 14 (q4 c4) ∷
   rw⁻ 17 (q4 c4) ∷
   re 19 1 (CS13⁻ ∷ []) ∷
   rw⁻ 18 (q36 c4) ∷
   re 20 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 15 (q37 c4) ∷
   re 13 1 (CS13 ∷ []) ∷
   rw⁻ 12 (q38 c4) ∷
   re 14 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 9 (q37 c4) ∷
   rw 7 (q8 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 14 (q4 c4) ∷
   rw⁻ 15 (q39 c4) ∷
   rw⁻ 12 (q40 c4) ∷
   rw⁻ 9 (q39 c4) ∷
   rw⁻ 6 (q40 c4) ∷
   rw 9 (q4 c4) ∷
   rw 10 (q4 c4) ∷
   rw 11 (q4 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 9 (q4 c4) ∷
   rw 10 (q4 c4) ∷
   rw 11 (q4 c4) ∷
   rw 12 (q4 c4) ∷
   re 8 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 0 (q35 c4) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = eqn (CK43 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (wl0731 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (CS34 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ X4 ∷ CS34 ∷ []) (wl0766 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ CS34 ∷ []) (wl0767 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (CS34 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ CS34 ∷ []) (wl0768 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ X4 ∷ CS34 ∷ []) (wp0405 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ CS34 ∷ []) (wp0406 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (K3 ∷ X4 ∷ []) (X4 ∷ K3 ∷ []) (wl0732 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (Sb0-1-42-3 ∷ K3 ∷ []) (K3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at243243 c4)

-- F4 CS12^0|K3^1: 131 steps
lem-F4-CS12ᵖ0∣K3ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣K3ᵖ1 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw 3 (q60 c4) ∷
   rw 2 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 0 (q2 c4) ∷
   re 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 12 (q4 c4) ∷
   re 14 1 (CS13⁻ ∷ []) ∷
   rw⁻ 13 (q5 c4) ∷
   re 15 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 10 (q6 c4) ∷
   re 8 1 (CS13 ∷ []) ∷
   rw⁻ 7 (q7 c4) ∷
   re 9 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 4 (q6 c4) ∷
   rw 2 (q8 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 10 (q9 c4) ∷
   rw⁻ 7 (q10 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   rw 4 (q4 c4) ∷
   rw 5 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw⁻ 3 (q8 c4) ∷
   rw 4 (q4 c4) ∷
   rw 5 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw 7 (q4 c4) ∷
   re 3 5 (Sb0-1-42-3 ∷ []) ∷
   re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw⁻ 13 (q4 c4) ∷
   re 15 1 (CS13⁻ ∷ []) ∷
   rw⁻ 14 (q61 c4) ∷
   re 16 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 11 (q62 c4) ∷
   re 9 1 (CS13 ∷ []) ∷
   rw⁻ 8 (q63 c4) ∷
   re 10 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 5 (q62 c4) ∷
   rw 3 (q8 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw⁻ 11 (q64 c4) ∷
   rw⁻ 8 (q65 c4) ∷
   rw⁻ 5 (q64 c4) ∷
   rw⁻ 2 (q65 c4) ∷
   rw 5 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw 7 (q4 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 5 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw 7 (q4 c4) ∷
   rw 8 (q4 c4) ∷
   re 4 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 5 (q66 c4) ∷
   rw 4 (q67 c4) ∷
   rw⁻ 3 (q66 c4) ∷
   re 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 12 (q4 c4) ∷
   rw⁻ 15 (q4 c4) ∷
   re 17 1 (CS13⁻ ∷ []) ∷
   rw⁻ 16 (q61 c4) ∷
   re 18 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 13 (q62 c4) ∷
   re 11 1 (CS13 ∷ []) ∷
   rw⁻ 10 (q63 c4) ∷
   re 12 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 7 (q62 c4) ∷
   rw 5 (q8 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 12 (q4 c4) ∷
   rw⁻ 13 (q64 c4) ∷
   rw⁻ 10 (q65 c4) ∷
   rw⁻ 7 (q64 c4) ∷
   rw⁻ 4 (q65 c4) ∷
   rw 7 (q4 c4) ∷
   rw 8 (q4 c4) ∷
   rw 9 (q4 c4) ∷
   rw⁻ 6 (q8 c4) ∷
   rw 7 (q4 c4) ∷
   rw 8 (q4 c4) ∷
   rw 9 (q4 c4) ∷
   rw 10 (q4 c4) ∷
   re 6 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 7 (q66 c4) ∷
   rw 6 (q67 c4) ∷
   rw⁻ 5 (q66 c4) ∷
   re 7 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 8 (q4 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 14 (q4 c4) ∷
   rw⁻ 17 (q4 c4) ∷
   re 19 1 (CS13⁻ ∷ []) ∷
   rw⁻ 18 (q61 c4) ∷
   re 20 1 (Sb⁻0-1-3-2 ∷ []) ∷
   rw⁻ 15 (q62 c4) ∷
   re 13 1 (CS13 ∷ []) ∷
   rw⁻ 12 (q63 c4) ∷
   re 14 1 (Sb0-1-3-2 ∷ []) ∷
   rw⁻ 9 (q62 c4) ∷
   rw 7 (q8 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 14 (q4 c4) ∷
   rw⁻ 15 (q64 c4) ∷
   rw⁻ 12 (q65 c4) ∷
   rw⁻ 9 (q64 c4) ∷
   rw⁻ 6 (q65 c4) ∷
   rw 9 (q4 c4) ∷
   rw 10 (q4 c4) ∷
   rw 11 (q4 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 9 (q4 c4) ∷
   rw 10 (q4 c4) ∷
   rw 11 (q4 c4) ∷
   rw 12 (q4 c4) ∷
   re 8 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 0 (q60 c4) ∷ []) Eq.refl

private
  q68 : Ws → Eqn
  q68 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (CS01⁻ ∷ Sw34 ∷ []) (Sw34 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑))
  q70 : Ws → Eqn
  q70 c4 = eqn (Sw34 ∷ Bx1-2403 ∷ []) (Bx1-2304 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2403⟩ (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (CS01⁻ ∷ Bx1-2304 ∷ []) (Bx1-2304 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2304⟩ c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (Sw34 ∷ Bx1-2304 ∷ []) (Bx1-2403 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2304⟩ (lit c4))

-- auto CSd01 | BOX(1;2304) @3443: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at3443 : Ws → ⟪ (CS01⁻ ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at3443 c4 = derive (CS01⁻ ∷ Bx1-2403 ∷ []) (Bx1-2403 ∷ CS01⁻ ∷ [])
  (rw⁻ 0 (q68 c4) ∷
   rw⁻ 1 (q69 c4) ∷
   rw 2 (q70 c4) ∷
   rw 1 (q71 c4) ∷
   rw 0 (q72 c4) ∷
   rw⁻ 1 (q69 c4) ∷
   rw 2 (q68 c4) ∷ []) Eq.refl

private
  q73 : Ws → Eqn
  q73 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (Sw12 ∷ CS02⁻ ∷ []) (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (Sw12 ∷ Bx2-1403 ∷ []) (Bx1-2403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1403⟩ (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (CS01⁻ ∷ Bx1-2403 ∷ []) (Bx1-2403 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2304⟩-at3443 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (Sw12 ∷ Bx1-2403 ∷ []) (Bx2-1403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2403⟩ (lit c4))
  q78 : Ws → Eqn
  q78 c4 = eqn (Sw12 ∷ CS01⁻ ∷ []) (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 (lit c4))

-- auto CSd01 | BOX(1;2304) @12213443: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at12213443 : Ws → ⟪ (CS02⁻ ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at12213443 c4 = derive (CS02⁻ ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ CS02⁻ ∷ [])
  (rw⁻ 0 (q73 c4) ∷
   rw 1 (q74 c4) ∷
   rw 2 (q75 c4) ∷
   rw 1 (q76 c4) ∷
   rw 0 (q77 c4) ∷
   rw 1 (q78 c4) ∷
   rw 2 (q73 c4) ∷ []) Eq.refl

private
  q79 : Ws → Eqn
  q79 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q80 : Ws → Eqn
  q80 c4 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wl0036 (lit c4))
  q81 : Ws → Eqn
  q81 c4 = eqn (Sw01 ∷ Bx2-0413 ∷ []) (Bx2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0413⟩ (lit c4))
  q82 : Ws → Eqn
  q82 c4 = eqn (CS02⁻ ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ CS02⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2304⟩-at12213443 c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (Sw01 ∷ Bx2-1403 ∷ []) (Bx2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1403⟩ (lit c4))
  q84 : Ws → Eqn
  q84 c4 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wl0139 (lit c4))

-- auto CSd01 | BOX(1;2304) @0112203443: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at0112203443 : Ws → ⟪ (CS12⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at0112203443 c4 = derive (CS12⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS12⁻ ∷ [])
  (rw⁻ 0 (q79 c4) ∷
   rw⁻ 1 (q80 c4) ∷
   rw 2 (q81 c4) ∷
   rw 1 (q82 c4) ∷
   rw 0 (q83 c4) ∷
   rw⁻ 1 (q84 c4) ∷
   rw 2 (q79 c4) ∷ []) Eq.refl

private
  q85 : Ws → Eqn
  q85 c4 = eqn (CS12⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS12⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2304⟩-at0112203443 c4)

-- auto SBOXd(0;1;2;3) | BOX(2;0413): 3 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩ : Ws → ⟪ (Sb⁻0-1-2-3 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩ c4 = derive (Sb⁻0-1-2-3 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ Sb⁻0-1-2-3 ∷ [])
  (re 0 1 (CS12⁻ ∷ []) ∷
   rw 0 (q85 c4) ∷
   re 1 1 (Sb⁻0-1-2-3 ∷ []) ∷ []) Eq.refl

private
  q86 : Ws → Eqn
  q86 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))
  q87 : Ws → Eqn
  q87 c4 = eqn (CS01 ∷ Bx1-2304 ∷ []) (Bx1-2304 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2304⟩ c4)

-- auto CS01 | BOX(1;2304) @3443: 7 steps
lem-auto-CS01-∣-BOX⟨1·2304⟩-at3443 : Ws → ⟪ (CS01 ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2304⟩-at3443 c4 = derive (CS01 ∷ Bx1-2403 ∷ []) (Bx1-2403 ∷ CS01 ∷ [])
  (rw⁻ 0 (q68 c4) ∷
   rw⁻ 1 (q86 c4) ∷
   rw 2 (q70 c4) ∷
   rw 1 (q87 c4) ∷
   rw 0 (q72 c4) ∷
   rw⁻ 1 (q86 c4) ∷
   rw 2 (q68 c4) ∷ []) Eq.refl

private
  q88 : Ws → Eqn
  q88 c4 = eqn (Sw12 ∷ CS02 ∷ []) (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4))
  q89 : Ws → Eqn
  q89 c4 = eqn (CS01 ∷ Bx1-2403 ∷ []) (Bx1-2403 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2304⟩-at3443 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (Sw12 ∷ CS01 ∷ []) (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4))

-- auto CS01 | BOX(1;2304) @12213443: 7 steps
lem-auto-CS01-∣-BOX⟨1·2304⟩-at12213443 : Ws → ⟪ (CS02 ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2304⟩-at12213443 c4 = derive (CS02 ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ CS02 ∷ [])
  (rw⁻ 0 (q73 c4) ∷
   rw 1 (q88 c4) ∷
   rw 2 (q75 c4) ∷
   rw 1 (q89 c4) ∷
   rw 0 (q77 c4) ∷
   rw 1 (q90 c4) ∷
   rw 2 (q73 c4) ∷ []) Eq.refl

private
  q91 : Ws → Eqn
  q91 c4 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wl0035 (lit c4))
  q92 : Ws → Eqn
  q92 c4 = eqn (CS02 ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2304⟩-at12213443 c4)
  q93 : Ws → Eqn
  q93 c4 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wl0138 (lit c4))

-- auto CS01 | BOX(1;2304) @0112203443: 7 steps
lem-auto-CS01-∣-BOX⟨1·2304⟩-at0112203443 : Ws → ⟪ (CS12 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS12 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2304⟩-at0112203443 c4 = derive (CS12 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS12 ∷ [])
  (rw⁻ 0 (q79 c4) ∷
   rw⁻ 1 (q91 c4) ∷
   rw 2 (q81 c4) ∷
   rw 1 (q92 c4) ∷
   rw 0 (q83 c4) ∷
   rw⁻ 1 (q93 c4) ∷
   rw 2 (q79 c4) ∷ []) Eq.refl

private
  q94 : Ws → Eqn
  q94 c4 = eqn (CS12 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS12 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2304⟩-at0112203443 c4)

-- auto SBOX(0;1;2;3) | BOX(2;0413): 3 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩ : Ws → ⟪ (Sb0-1-2-3 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩ c4 = derive (Sb0-1-2-3 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ Sb0-1-2-3 ∷ [])
  (re 0 1 (CS12 ∷ []) ∷
   rw 0 (q94 c4) ∷
   re 1 1 (Sb0-1-2-3 ∷ []) ∷ []) Eq.refl

private
  q95 : Ws → Eqn
  q95 c4 = eqn (Sw01 ∷ Bx4-2103 ∷ []) (Bx4-2013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·2103⟩ (lit c4))
  q96 : Ws → Eqn
  q96 c4 = eqn (Bx4-2013 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-beta-T-at0412203143 c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (Sw01 ∷ Toff402 ∷ []) (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 (lit c4))
  q98 : Ws → Eqn
  q98 c4 = eqn (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4))

-- beta-T @0412213043: 8 steps
lem-beta-T-at0412213043 : Ws → ⟪ (Bx4-2103 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-T-at0412213043 c4 = derive (Bx4-2103 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q79 c4) ∷
   rw 1 (q95 c4) ∷
   rw 1 (q96 c4) ∷
   rw 0 (q97 c4) ∷
   rw 1 (q98 c4) ∷
   rw 2 (q97 c4) ∷
   rw 3 (q98 c4) ∷
   rw 4 (q79 c4) ∷ []) Eq.refl

private
  q99 : Ws → Eqn
  q99 c4 = eqn (Bx4-2013 ∷ []) (Bx4-2103 ∷ []) (lem-sym23-at0412203143 c4)

-- sym23 @0412213043: 5 steps
lem-sym23-at0412213043 : Ws → ⟪ (Bx4-2103 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2013 ∷ []) ⟫ʷ
lem-sym23-at0412213043 c4 = derive (Bx4-2103 ∷ []) (Bx4-2013 ∷ [])
  (rw⁻ 0 (q79 c4) ∷
   rw 1 (q95 c4) ∷
   rw 1 (q99 c4) ∷
   rw 0 (q95 c4) ∷
   rw 1 (q79 c4) ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = eqn (Bx4-0213 ∷ []) (Bx4-2013 ∷ []) (lem-sym12-at04103143 c4)
  q101 : Ws → Eqn
  q101 c4 = eqn (Bx4-2103 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-beta-T-at0412213043 c4)
  q102 : Ws → Eqn
  q102 c4 = eqn (Toff412 ∷ Toff412 ∷ []) [] (wl0784 (lit c4))
  q103 : Ws → Eqn
  q103 c4 = eqn (Toff412 ∷ []) (Toff412 ∷ []) (wl0785 (lit c4))
  q104 : Ws → Eqn
  q104 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1243 ∷ []) (lem-sym34 c4)
  q105 : Ws → Eqn
  q105 c4 = eqn (Toff412 ∷ Bx0-1243 ∷ Toff412 ∷ []) (Bx0-1243 ∷ CCZ123 ∷ []) (lem-T312-beta-at3443 c4)
  q106 : Ws → Eqn
  q106 c4 = eqn (Bx0-1243 ∷ []) (Bx0-1234 ∷ []) (lem-sym34-at3443 c4)
  q107 : Ws → Eqn
  q107 c4 = eqn (Bx0-1234 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123 c4)
  q108 : Ws → Eqn
  q108 c4 = eqn (Bx0-1234 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ403 c4)
  q109 : Ws → Eqn
  q109 c4 = eqn (CCZ123 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ123 ∷ []) (wl0786 (lit c4))
  q110 : Ws → Eqn
  q110 c4 = eqn (CCZ034 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0410233142 c4)
  q111 : Ws → Eqn
  q111 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl0212 (lit c4))
  q112 : Ws → Eqn
  q112 c4 = eqn (Bx4-2103 ∷ []) (Bx4-2013 ∷ []) (lem-sym23-at0412213043 c4)
  q113 : Ws → Eqn
  q113 c4 = eqn (Bx4-2013 ∷ []) (Bx4-0213 ∷ []) (lem-sym12-at0412203143 c4)

-- auto BOX(0;1234) | BOX(4;0213): 27 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·0213⟩ : Ws → ⟪ (Bx0-1234 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·0213⟩ c4 = derive (Bx0-1234 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Bx0-1234 ∷ [])
  (rw 1 (q100 c4) ∷
   rw 1 (q99 c4) ∷
   rw 1 (q101 c4) ∷
   rw⁻ 0 (q102 c4) ∷
   rw 1 (q103 c4) ∷
   rw 3 (q103 c4) ∷
   rw 2 (q104 c4) ∷
   rw 1 (q105 c4) ∷
   rw 1 (q106 c4) ∷
   rw 1 (q107 c4) ∷
   rw 2 (q108 c4) ∷
   rw⁻ 3 (q102 c4) ∷
   rw 4 (q103 c4) ∷
   rw 6 (q103 c4) ∷
   rw 5 (q104 c4) ∷
   rw 4 (q105 c4) ∷
   rw 4 (q106 c4) ∷
   rw 4 (q107 c4) ∷
   rw 5 (q108 c4) ∷
   rw⁻ 0 (q109 c4) ∷
   rw⁻ 3 (q109 c4) ∷
   rw 2 (q110 c4) ∷
   rw⁻ 1 (q109 c4) ∷
   rw 0 (q111 c4) ∷
   rw⁻ 0 (q101 c4) ∷
   rw 0 (q112 c4) ∷
   rw 0 (q113 c4) ∷ []) Eq.refl

private
  q114 : Ws → Eqn
  q114 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q115 : Ws → Eqn
  q115 c4 = eqn (Sw23 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ (lit c4))
  q116 : Ws → Eqn
  q116 c4 = eqn (Sw23 ∷ Bx3-0412 ∷ []) (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4))
  q117 : Ws → Eqn
  q117 c4 = eqn (Sb⁻0-1-2-3 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩ c4)
  q118 : Ws → Eqn
  q118 c4 = eqn (Sw23 ∷ Bx2-0413 ∷ []) (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4))
  q119 : Ws → Eqn
  q119 c4 = eqn (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ (lit c4))

-- auto SBOXd(0;1;2;3) | BOX(2;0413) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2332 : Ws → ⟪ (Sb⁻0-1-3-2 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2332 c4 = derive (Sb⁻0-1-3-2 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ Sb⁻0-1-3-2 ∷ [])
  (rw⁻ 0 (q114 c4) ∷
   rw 1 (q115 c4) ∷
   rw 2 (q116 c4) ∷
   rw 1 (q117 c4) ∷
   rw 0 (q118 c4) ∷
   rw 1 (q119 c4) ∷
   rw 2 (q114 c4) ∷ []) Eq.refl

private
  q120 : Ws → Eqn
  q120 c4 = eqn (Sw34 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ (lit c4))
  q121 : Ws → Eqn
  q121 c4 = eqn (Sw34 ∷ Bx4-0312 ∷ []) (Bx3-0412 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0312⟩ (lit c4))
  q122 : Ws → Eqn
  q122 c4 = eqn (Sb⁻0-1-3-2 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2332 c4)
  q123 : Ws → Eqn
  q123 c4 = eqn (Sw34 ∷ Bx3-0412 ∷ []) (Bx4-0312 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0412⟩ (lit c4))
  q124 : Ws → Eqn
  q124 c4 = eqn (Sw34 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ (lit c4))

-- auto SBOXd(0;1;2;3) | BOX(2;0413) @243243: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at243243 : Ws → ⟪ (Sb⁻0-1-4-2 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at243243 c4 = derive (Sb⁻0-1-4-2 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Sb⁻0-1-4-2 ∷ [])
  (rw⁻ 0 (q68 c4) ∷
   rw 1 (q120 c4) ∷
   rw 2 (q121 c4) ∷
   rw 1 (q122 c4) ∷
   rw 0 (q123 c4) ∷
   rw 1 (q124 c4) ∷
   rw 2 (q68 c4) ∷ []) Eq.refl

private
  q125 : Ws → Eqn
  q125 c4 = eqn (Sw23 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ (lit c4))
  q126 : Ws → Eqn
  q126 c4 = eqn (Sw23 ∷ Bx4-0213 ∷ []) (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ (lit c4))
  q127 : Ws → Eqn
  q127 c4 = eqn (Sb⁻0-1-4-2 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Sb⁻0-1-4-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at243243 c4)
  q128 : Ws → Eqn
  q128 c4 = eqn (Sw23 ∷ Bx4-0312 ∷ []) (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ (lit c4))
  q129 : Ws → Eqn
  q129 c4 = eqn (Sw23 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ (lit c4))

-- auto SBOXd(0;1;2;3) | BOX(2;0413) @2442: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2442 : Ws → ⟪ (Sb⁻0-1-4-3 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2442 c4 = derive (Sb⁻0-1-4-3 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Sb⁻0-1-4-3 ∷ [])
  (rw⁻ 0 (q114 c4) ∷
   rw 1 (q125 c4) ∷
   rw 2 (q126 c4) ∷
   rw 1 (q127 c4) ∷
   rw 0 (q128 c4) ∷
   rw 1 (q129 c4) ∷
   rw 2 (q114 c4) ∷ []) Eq.refl

private
  q130 : Ws → Eqn
  q130 c4 = eqn (Sw23 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ (lit c4))
  q131 : Ws → Eqn
  q131 c4 = eqn (Sb0-1-2-3 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩ c4)
  q132 : Ws → Eqn
  q132 c4 = eqn (Sw23 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ (lit c4))

-- auto SBOX(0;1;2;3) | BOX(2;0413) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2332 : Ws → ⟪ (Sb0-1-3-2 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2332 c4 = derive (Sb0-1-3-2 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ Sb0-1-3-2 ∷ [])
  (rw⁻ 0 (q114 c4) ∷
   rw 1 (q130 c4) ∷
   rw 2 (q116 c4) ∷
   rw 1 (q131 c4) ∷
   rw 0 (q118 c4) ∷
   rw 1 (q132 c4) ∷
   rw 2 (q114 c4) ∷ []) Eq.refl

private
  q133 : Ws → Eqn
  q133 c4 = eqn (Sw34 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ (lit c4))
  q134 : Ws → Eqn
  q134 c4 = eqn (Sb0-1-3-2 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2332 c4)
  q135 : Ws → Eqn
  q135 c4 = eqn (Sw34 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ (lit c4))

-- auto SBOX(0;1;2;3) | BOX(2;0413) @243243: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at243243 : Ws → ⟪ (Sb0-1-4-2 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at243243 c4 = derive (Sb0-1-4-2 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Sb0-1-4-2 ∷ [])
  (rw⁻ 0 (q68 c4) ∷
   rw 1 (q133 c4) ∷
   rw 2 (q121 c4) ∷
   rw 1 (q134 c4) ∷
   rw 0 (q123 c4) ∷
   rw 1 (q135 c4) ∷
   rw 2 (q68 c4) ∷ []) Eq.refl

private
  q136 : Ws → Eqn
  q136 c4 = eqn (Sw23 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ (lit c4))
  q137 : Ws → Eqn
  q137 c4 = eqn (Sb0-1-4-2 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Sb0-1-4-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at243243 c4)
  q138 : Ws → Eqn
  q138 c4 = eqn (Sw23 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ (lit c4))

-- auto SBOX(0;1;2;3) | BOX(2;0413) @2442: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2442 : Ws → ⟪ (Sb0-1-4-3 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2442 c4 = derive (Sb0-1-4-3 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Sb0-1-4-3 ∷ [])
  (rw⁻ 0 (q114 c4) ∷
   rw 1 (q136 c4) ∷
   rw 2 (q126 c4) ∷
   rw 1 (q137 c4) ∷
   rw 0 (q128 c4) ∷
   rw 1 (q138 c4) ∷
   rw 2 (q114 c4) ∷ []) Eq.refl

private
  q139 : Ws → Eqn
  q139 c4 = eqn (Sb⁻0-1-4-3 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2442 c4)
  q140 : Ws → Eqn
  q140 c4 = eqn (Toff423 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0412233041 c4)
  q141 : Ws → Eqn
  q141 c4 = eqn (Sb0-1-4-3 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2442 c4)
  q142 : Ws → Eqn
  q142 c4 = eqn (Bx0-1234 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·0213⟩ c4)

-- auto SBOX(0;1;23;4) | BOX(4;0213): 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩ c4 = derive (Sb0-1-23-4 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Sb0-1-23-4 ∷ [])
  (re 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   rw 4 (q139 c4) ∷
   rw 3 (q140 c4) ∷
   rw 2 (q141 c4) ∷
   rw 1 (q140 c4) ∷
   rw 0 (q142 c4) ∷
   re 1 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q143 : Ws → Eqn
  q143 c4 = eqn (Bx0-1324 ∷ []) (Bx0-1234 ∷ []) (lem-sym23-at2332 c4)
  q144 : Ws → Eqn
  q144 c4 = eqn (CCZ012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ012 ∷ []) (lem-Cz-beta c4)
  q145 : Ws → Eqn
  q145 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1324 ∷ []) (lem-sym23 c4)

-- auto CCZ012 | BOX(0;1324): 3 steps
lem-auto-CCZ012-∣-BOX⟨0·1324⟩ : Ws → ⟪ (CCZ012 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨0·1324⟩ c4 = derive (CCZ012 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CCZ012 ∷ [])
  (rw 1 (q143 c4) ∷
   rw 0 (q144 c4) ∷
   rw 0 (q145 c4) ∷ []) Eq.refl

private
  q146 : Ws → Eqn
  q146 c4 = eqn (CCZ012 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨0·1324⟩ c4)
  q147 : Ws → Eqn
  q147 c4 = eqn (CCZ012 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at3443 c4)
  q148 : Ws → Eqn
  q148 c4 = eqn (CCZ012 ∷ CS14 ∷ []) (CS14 ∷ CCZ012 ∷ []) (wp0044 c4)
  q149 : Ws → Eqn
  q149 c4 = eqn (CCZ012 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ012 ∷ []) (wp0043 c4)

-- auto CCZ012 | SBOX(0;1;32;4): 11 steps
lem-auto-CCZ012-∣-SBOX⟨0·1·32·4⟩ : Ws → ⟪ (CCZ012 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨0·1·32·4⟩ c4 = derive (CCZ012 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-32-4 ∷ CCZ012 ∷ [])
  (re 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) ∷
   rw 0 (q146 c4) ∷
   rw 1 (q147 c4) ∷
   re 3 1 (CS14 ∷ []) ∷
   rw 2 (q148 c4) ∷
   re 2 1 (Sb0-1-4-2 ∷ []) ∷
   rw 3 (q147 c4) ∷
   re 5 1 (CS14⁻ ∷ []) ∷
   rw 4 (q149 c4) ∷
   re 4 1 (Sb⁻0-1-4-2 ∷ []) ∷
   re 0 5 (Sb0-1-32-4 ∷ []) ∷ []) Eq.refl

private
  q150 : Ws → Eqn
  q150 c4 = eqn (Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4)
  q151 : Ws → Eqn
  q151 c4 = eqn (Sb0-1-32-4 ∷ CS03 ∷ []) (CS03 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS02-at2332 c4)

-- auto SBOX(0;1;23;4) | SBOX(4;0;3;1): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-3-1 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩ c4 = derive (Sb0-1-23-4 ∷ Sb4-0-3-1 ∷ []) (Sb4-0-3-1 ∷ Sb0-1-23-4 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw 0 (q150 c4) ∷
   rw 0 (q151 c4) ∷
   rw⁻ 1 (q150 c4) ∷
   re 0 1 (Sb4-0-3-1 ∷ []) ∷ []) Eq.refl

private
  q152 : Ws → Eqn
  q152 c4 = eqn (Sb0-1-32-4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02-at2332 c4)

-- auto SBOX(0;1;23;4) | SBOXd(4;0;3;1): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb⁻4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-3-1 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩ c4 = derive (Sb0-1-23-4 ∷ Sb⁻4-0-3-1 ∷ []) (Sb⁻4-0-3-1 ∷ Sb0-1-23-4 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw 0 (q150 c4) ∷
   rw 0 (q152 c4) ∷
   rw⁻ 1 (q150 c4) ∷
   re 0 1 (Sb⁻4-0-3-1 ∷ []) ∷ []) Eq.refl

private
  q153 : Ws → Eqn
  q153 c4 = eqn (Sw23 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4))
  q154 : Ws → Eqn
  q154 c4 = eqn (Sb0-1-23-4 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩ c4)
  q155 : Ws → Eqn
  q155 c4 = eqn (Sw23 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | BOX(4;0213) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩-at2332 c4 = derive (Sb0-1-32-4 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q114 c4) ∷
   rw 1 (q153 c4) ∷
   rw 2 (q128 c4) ∷
   rw 1 (q154 c4) ∷
   rw 0 (q126 c4) ∷
   rw 1 (q155 c4) ∷
   rw 2 (q114 c4) ∷ []) Eq.refl

private
  q156 : Ws → Eqn
  q156 c4 = eqn (Sw34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4))
  q157 : Ws → Eqn
  q157 c4 = eqn (Sb0-1-32-4 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩-at2332 c4)
  q158 : Ws → Eqn
  q158 c4 = eqn (Sw34 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | BOX(4;0213) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩-at243243 c4 = derive (Sb0-1-42-3 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q68 c4) ∷
   rw 1 (q156 c4) ∷
   rw 2 (q123 c4) ∷
   rw 1 (q157 c4) ∷
   rw 0 (q121 c4) ∷
   rw 1 (q158 c4) ∷
   rw 2 (q68 c4) ∷ []) Eq.refl

private
  q159 : Ws → Eqn
  q159 c4 = eqn (CCZ012 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (Swap))
  q160 : Ws → Eqn
  q160 c4 = eqn (CCZ012 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-32-4 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨0·1·32·4⟩ c4)

-- auto CCZ012 | SBOX(0;1;32;4) @3443: 7 steps
lem-auto-CCZ012-∣-SBOX⟨0·1·32·4⟩-at3443 : Ws → ⟪ (CCZ012 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨0·1·32·4⟩-at3443 c4 = derive (CCZ012 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q68 c4) ∷
   rw⁻ 1 (q159 c4) ∷
   rw 2 (q156 c4) ∷
   rw 1 (q160 c4) ∷
   rw 0 (q158 c4) ∷
   rw⁻ 1 (q159 c4) ∷
   rw 2 (q68 c4) ∷ []) Eq.refl

private
  q161 : Ws → Eqn
  q161 c4 = eqn (Sw23 ∷ Sb4-0-2-1 ∷ []) (Sb4-0-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·0·2·1⟩ (lit c4))
  q162 : Ws → Eqn
  q162 c4 = eqn (Sb0-1-23-4 ∷ Sb4-0-3-1 ∷ []) (Sb4-0-3-1 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩ c4)
  q163 : Ws → Eqn
  q163 c4 = eqn (Sw23 ∷ Sb4-0-3-1 ∷ []) (Sb4-0-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·0·3·1⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(4;0;3;1) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-2-1 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩-at2332 c4 = derive (Sb0-1-32-4 ∷ Sb4-0-2-1 ∷ []) (Sb4-0-2-1 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q114 c4) ∷
   rw 1 (q153 c4) ∷
   rw 2 (q161 c4) ∷
   rw 1 (q162 c4) ∷
   rw 0 (q163 c4) ∷
   rw 1 (q155 c4) ∷
   rw 2 (q114 c4) ∷ []) Eq.refl

private
  q164 : Ws → Eqn
  q164 c4 = eqn (Sw34 ∷ Sb3-0-2-1 ∷ []) (Sb4-0-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨3·0·2·1⟩ (lit c4))
  q165 : Ws → Eqn
  q165 c4 = eqn (Sb0-1-32-4 ∷ Sb4-0-2-1 ∷ []) (Sb4-0-2-1 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩-at2332 c4)
  q166 : Ws → Eqn
  q166 c4 = eqn (Sw34 ∷ Sb4-0-2-1 ∷ []) (Sb3-0-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨4·0·2·1⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOX(4;0;3;1) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-2-1 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩-at243243 c4 = derive (Sb0-1-42-3 ∷ Sb3-0-2-1 ∷ []) (Sb3-0-2-1 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q68 c4) ∷
   rw 1 (q156 c4) ∷
   rw 2 (q164 c4) ∷
   rw 1 (q165 c4) ∷
   rw 0 (q166 c4) ∷
   rw 1 (q158 c4) ∷
   rw 2 (q68 c4) ∷ []) Eq.refl

private
  q167 : Ws → Eqn
  q167 c4 = eqn (Sw23 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻4-0-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·0·2·1⟩ (lit c4))
  q168 : Ws → Eqn
  q168 c4 = eqn (Sb0-1-23-4 ∷ Sb⁻4-0-3-1 ∷ []) (Sb⁻4-0-3-1 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩ c4)
  q169 : Ws → Eqn
  q169 c4 = eqn (Sw23 ∷ Sb⁻4-0-3-1 ∷ []) (Sb⁻4-0-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·0·3·1⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(4;0;3;1) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb⁻4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-2-1 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩-at2332 c4 = derive (Sb0-1-32-4 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻4-0-2-1 ∷ Sb0-1-32-4 ∷ [])
  (rw⁻ 0 (q114 c4) ∷
   rw 1 (q153 c4) ∷
   rw 2 (q167 c4) ∷
   rw 1 (q168 c4) ∷
   rw 0 (q169 c4) ∷
   rw 1 (q155 c4) ∷
   rw 2 (q114 c4) ∷ []) Eq.refl

private
  q170 : Ws → Eqn
  q170 c4 = eqn (Sw34 ∷ Sb⁻3-0-2-1 ∷ []) (Sb⁻4-0-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨3·0·2·1⟩ (lit c4))
  q171 : Ws → Eqn
  q171 c4 = eqn (Sb0-1-32-4 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻4-0-2-1 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩-at2332 c4)
  q172 : Ws → Eqn
  q172 c4 = eqn (Sw34 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻3-0-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨4·0·2·1⟩ (lit c4))

-- auto SBOX(0;1;23;4) | SBOXd(4;0;3;1) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb⁻3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-2-1 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩-at243243 c4 = derive (Sb0-1-42-3 ∷ Sb⁻3-0-2-1 ∷ []) (Sb⁻3-0-2-1 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q68 c4) ∷
   rw 1 (q156 c4) ∷
   rw 2 (q170 c4) ∷
   rw 1 (q171 c4) ∷
   rw 0 (q172 c4) ∷
   rw 1 (q158 c4) ∷
   rw 2 (q68 c4) ∷ []) Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D167 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0244 ; wl0265 ; wl0351 ; wl0503 ; wl0616 ; wl0618 ; wl0619 ; wl0620 ; wl0622 ; wl0627 ; wl0628 ; wl0629 ; wl0630 ; wl0631 ; wl0632 ; wl0633 ; wl0634 ; wl0635 ; wl0636)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-T312-beta-at14213243 ; lem-sym12 ; lem-sym12-at1221 ; lem-sym12-at14213243 ; lem-sym23-at1221 ; lem-sym23-at14213243 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-T312-beta-at122331 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ234 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at243243 ; lem-sym12-at243243 ; lem-sym23-at011220 ; lem-sym23-at01122330 ; lem-sym23-at122331 ; lem-sym23-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-beta-T-at01122330)
open import Examples.Groups.Clifford+CS.Five.D.D161 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D164 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ104 ; lem-auto-CCZ012-∣-CCZ342-at0110243243)
open import Examples.Groups.Clifford+CS.Five.D.D166 using (lem-T312-beta-at122441 ; lem-T312-beta-at14233142 ; lem-T312-beta-at14233241 ; lem-T312-beta-at1441 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CS43-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CSd43-at122441 ; lem-beta-inv-at122441 ; lem-boxify-9-nf-of-rhs ; lem-sym12-at122441 ; lem-sym12-at1441 ; lem-sym23-at14233241 ; lem-sym23-at143143 ; lem-sym23-at1441 ; lem-sym34-at14233142 ; lem-sym34-at14233241 ; lem-sym34-at143143 ; lem-sym34-at1441)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Toff324 ∷ Toff324 ∷ []) [] (wl0616 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Bx0-1423 ∷ []) (Bx0-4123 ∷ []) (lem-sym12-at243243 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx0-4123 ∷ []) (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Bx0-4213 ∷ []) (Bx0-4231 ∷ []) (lem-sym34-at143143 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Toff324 ∷ Bx0-4231 ∷ Toff324 ∷ []) (Bx0-4231 ∷ CCZ124 ∷ []) (lem-T312-beta-at1441 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Bx0-4231 ∷ []) (Bx0-4213 ∷ []) (lem-sym34-at1441 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (Bx0-4213 ∷ []) (Bx0-4123 ∷ []) (lem-sym23-at143143 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (Bx0-4123 ∷ []) (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (Bx0-1423 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (Bx0-1423 ∷ CS13 ∷ []) (CS13 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at243243 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Bx0-1423 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at243243 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Toff234 ∷ Toff234 ∷ []) [] (wl0620 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (Bx0-4231 ∷ []) (Bx0-4321 ∷ []) (lem-sym23-at1441 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Toff234 ∷ Bx0-4321 ∷ Toff234 ∷ []) (Bx0-4321 ∷ CCZ134 ∷ []) (lem-T312-beta-at14233241 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (Bx0-4321 ∷ []) (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Bx0-1423 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at243243 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (Toff134 ∷ Toff134 ∷ []) [] (wl0627 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Bx0-2431 ∷ []) (Bx0-4231 ∷ []) (lem-sym12-at122441 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (Bx0-4321 ∷ []) (Bx0-4312 ∷ []) (lem-sym34-at14233241 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Toff134 ∷ Bx0-4312 ∷ Toff134 ∷ []) (Bx0-4312 ∷ CCZ234 ∷ []) (lem-T312-beta-at14233142 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (Bx0-4312 ∷ []) (Bx0-4321 ∷ []) (lem-sym34-at14233142 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (Bx0-4231 ∷ []) (Bx0-2431 ∷ []) (lem-sym12-at1441 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (Bx0-2431 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (Bx0-2431 ∷ CS12 ∷ []) (CS12 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at122441 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Bx0-2431 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at122441 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (Toff214 ∷ Toff214 ∷ []) [] (wl0244 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (Toff214 ∷ Bx0-4123 ∷ Toff214 ∷ []) (Bx0-4123 ∷ CCZ134 ∷ []) (lem-T312-beta-at14213243 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (Bx0-2431 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at122441 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (Toff324 ∷ []) (Toff324 ∷ []) (wl0622 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (Toff324 ∷ Bx0-2431 ∷ Toff324 ∷ []) (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Bx0-2431 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Bx0-2431 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at122441 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx0-2431 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at122441 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (Bx0-2431 ∷ CS13 ∷ []) (CS13 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS43-at122441 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (Bx0-2431 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd43-at122441 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Bx0-2431 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at122441 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (Bx0-2431 ∷ Bx0-2431 ∷ []) [] (lem-beta-inv-at122441 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Bx0-1423 ∷ []) (Bx0-1243 ∷ []) (lem-sym23-at243243 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (Bx0-1243 ∷ []) (Bx0-1234 ∷ []) (lem-sym34-at3443 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ124 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0629 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) (wl0630 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ134 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ134 ∷ []) (wl0631 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ234 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ234 ∷ []) (wl0632 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ134 ∷ Toff134 ∷ []) (Toff134 ∷ CZ34 ∷ CCZ134 ∷ []) (wl0633 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ124 ∷ CCZ124 ∷ []) [] (wl0351 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ []) (wl0634 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (CCZ134 ∷ CCZ134 ∷ []) [] (wl0503 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ124 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ124 ∷ []) (wl0635 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CZ34 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ []) [] (wl0636 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1234 ∷ []) (lem-boxify-9-nf-of-rhs c4)

-- boxify-9: 331 steps
lem-boxify-9 : Ws → ⟪ (Sb0-2-43-1 ∷ Toff214 ∷ CCZ234 ∷ Sb0-2-43-1 ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-boxify-9 c4 = derive (Sb0-2-43-1 ∷ Toff214 ∷ CCZ234 ∷ Sb0-2-43-1 ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) (Bx0-1234 ∷ [])
  (re 0 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 2 1 (CS12 ∷ []) ∷
   re 4 1 (CS12⁻ ∷ []) ∷
   re 7 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 9 1 (CS12 ∷ []) ∷
   re 11 1 (CS12⁻ ∷ []) ∷
   re 16 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 18 1 (CS13 ∷ []) ∷
   re 20 1 (CS13⁻ ∷ []) ∷
   rw⁻ 16 (q1 c4) ∷
   rw 18 (q2 c4) ∷
   rw 18 (q3 c4) ∷
   rw 18 (q4 c4) ∷
   rw 17 (q5 c4) ∷
   rw 17 (q6 c4) ∷
   rw 17 (q7 c4) ∷
   rw 17 (q8 c4) ∷
   rw 17 (q9 c4) ∷
   rw 18 (q10 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw 21 (q2 c4) ∷
   rw 21 (q3 c4) ∷
   rw 21 (q4 c4) ∷
   rw 20 (q5 c4) ∷
   rw 20 (q6 c4) ∷
   rw 20 (q7 c4) ∷
   rw 20 (q8 c4) ∷
   rw 20 (q9 c4) ∷
   rw 21 (q11 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw 24 (q2 c4) ∷
   rw 24 (q3 c4) ∷
   rw 24 (q4 c4) ∷
   rw 23 (q5 c4) ∷
   rw 23 (q6 c4) ∷
   rw 23 (q7 c4) ∷
   rw 23 (q8 c4) ∷
   rw 23 (q9 c4) ∷
   rw⁻ 24 (q12 c4) ∷
   rw 26 (q2 c4) ∷
   rw 26 (q3 c4) ∷
   rw 26 (q4 c4) ∷
   rw 26 (q13 c4) ∷
   rw 25 (q14 c4) ∷
   rw 25 (q15 c4) ∷
   rw 25 (q6 c4) ∷
   rw 25 (q7 c4) ∷
   rw 25 (q8 c4) ∷
   rw 25 (q16 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw 28 (q2 c4) ∷
   rw 28 (q3 c4) ∷
   rw 28 (q4 c4) ∷
   rw 27 (q5 c4) ∷
   rw 27 (q6 c4) ∷
   rw 27 (q7 c4) ∷
   rw 27 (q8 c4) ∷
   rw 27 (q9 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw 9 (q18 c4) ∷
   rw 9 (q13 c4) ∷
   rw 9 (q19 c4) ∷
   rw 8 (q20 c4) ∷
   rw 8 (q21 c4) ∷
   rw 8 (q15 c4) ∷
   rw 8 (q22 c4) ∷
   rw 8 (q23 c4) ∷
   rw 9 (q24 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   rw 12 (q18 c4) ∷
   rw 12 (q13 c4) ∷
   rw 12 (q19 c4) ∷
   rw 11 (q20 c4) ∷
   rw 11 (q21 c4) ∷
   rw 11 (q15 c4) ∷
   rw 11 (q22 c4) ∷
   rw 11 (q23 c4) ∷
   rw 12 (q25 c4) ∷
   rw⁻ 13 (q26 c4) ∷
   rw 15 (q18 c4) ∷
   rw 15 (q6 c4) ∷
   rw 15 (q7 c4) ∷
   rw 14 (q27 c4) ∷
   rw 14 (q3 c4) ∷
   rw 14 (q4 c4) ∷
   rw 14 (q22 c4) ∷
   rw 14 (q28 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw 16 (q29 c4) ∷
   rw 18 (q29 c4) ∷
   rw 16 (q30 c4) ∷
   rw 16 (q31 c4) ∷
   rw⁻ 17 (q12 c4) ∷
   rw 19 (q18 c4) ∷
   rw 19 (q13 c4) ∷
   rw 18 (q14 c4) ∷
   rw 18 (q15 c4) ∷
   rw 18 (q22 c4) ∷
   rw 18 (q32 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw 20 (q29 c4) ∷
   rw 22 (q29 c4) ∷
   rw 20 (q30 c4) ∷
   rw 20 (q31 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw 22 (q29 c4) ∷
   rw 24 (q29 c4) ∷
   rw 22 (q30 c4) ∷
   rw 22 (q31 c4) ∷
   rw 23 (q33 c4) ∷
   rw 24 (q34 c4) ∷
   rw⁻ 25 (q1 c4) ∷
   rw 26 (q29 c4) ∷
   rw 28 (q29 c4) ∷
   rw 26 (q30 c4) ∷
   rw 26 (q31 c4) ∷
   rw 27 (q33 c4) ∷
   rw 28 (q35 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw 30 (q29 c4) ∷
   rw 32 (q29 c4) ∷
   rw 30 (q30 c4) ∷
   rw 30 (q31 c4) ∷
   rw 31 (q33 c4) ∷
   rw⁻ 32 (q12 c4) ∷
   rw 34 (q18 c4) ∷
   rw 34 (q13 c4) ∷
   rw 33 (q14 c4) ∷
   rw 33 (q15 c4) ∷
   rw 33 (q22 c4) ∷
   rw 33 (q32 c4) ∷
   rw 34 (q32 c4) ∷
   rw⁻ 35 (q1 c4) ∷
   rw 36 (q29 c4) ∷
   rw 38 (q29 c4) ∷
   rw 36 (q30 c4) ∷
   rw 36 (q31 c4) ∷
   rw 37 (q33 c4) ∷
   rw⁻ 0 (q17 c4) ∷
   rw 2 (q18 c4) ∷
   rw 2 (q13 c4) ∷
   rw 2 (q19 c4) ∷
   rw 1 (q20 c4) ∷
   rw 1 (q21 c4) ∷
   rw 1 (q15 c4) ∷
   rw 1 (q22 c4) ∷
   rw 1 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   rw⁻ 3 (q17 c4) ∷
   rw 5 (q18 c4) ∷
   rw 5 (q13 c4) ∷
   rw 5 (q19 c4) ∷
   rw 4 (q20 c4) ∷
   rw 4 (q21 c4) ∷
   rw 4 (q15 c4) ∷
   rw 4 (q22 c4) ∷
   rw 4 (q23 c4) ∷
   rw 5 (q25 c4) ∷
   rw⁻ 6 (q26 c4) ∷
   rw 8 (q18 c4) ∷
   rw 8 (q6 c4) ∷
   rw 8 (q7 c4) ∷
   rw 7 (q27 c4) ∷
   rw 7 (q3 c4) ∷
   rw 7 (q4 c4) ∷
   rw 7 (q22 c4) ∷
   rw 7 (q28 c4) ∷
   rw 8 (q36 c4) ∷
   rw⁻ 9 (q17 c4) ∷
   rw 11 (q18 c4) ∷
   rw 11 (q13 c4) ∷
   rw 11 (q19 c4) ∷
   rw 10 (q20 c4) ∷
   rw 10 (q21 c4) ∷
   rw 10 (q15 c4) ∷
   rw 10 (q22 c4) ∷
   rw 10 (q23 c4) ∷
   rw 11 (q23 c4) ∷
   rw 12 (q24 c4) ∷
   rw⁻ 13 (q17 c4) ∷
   rw 15 (q18 c4) ∷
   rw 15 (q13 c4) ∷
   rw 15 (q19 c4) ∷
   rw 14 (q20 c4) ∷
   rw 14 (q21 c4) ∷
   rw 14 (q15 c4) ∷
   rw 14 (q22 c4) ∷
   rw 14 (q23 c4) ∷
   rw 15 (q23 c4) ∷
   rw 16 (q25 c4) ∷
   rw⁻ 17 (q26 c4) ∷
   rw 19 (q18 c4) ∷
   rw 19 (q6 c4) ∷
   rw 19 (q7 c4) ∷
   rw 18 (q27 c4) ∷
   rw 18 (q3 c4) ∷
   rw 18 (q4 c4) ∷
   rw 18 (q22 c4) ∷
   rw 18 (q28 c4) ∷
   rw 19 (q28 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw 21 (q29 c4) ∷
   rw 23 (q29 c4) ∷
   rw 21 (q30 c4) ∷
   rw 21 (q31 c4) ∷
   rw 22 (q31 c4) ∷
   rw⁻ 23 (q12 c4) ∷
   rw 25 (q18 c4) ∷
   rw 25 (q13 c4) ∷
   rw 24 (q14 c4) ∷
   rw 24 (q15 c4) ∷
   rw 24 (q22 c4) ∷
   rw 24 (q32 c4) ∷
   rw 25 (q32 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw 27 (q29 c4) ∷
   rw 29 (q29 c4) ∷
   rw 27 (q30 c4) ∷
   rw 27 (q31 c4) ∷
   rw 28 (q31 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw 30 (q29 c4) ∷
   rw 32 (q29 c4) ∷
   rw 30 (q30 c4) ∷
   rw 30 (q31 c4) ∷
   rw 31 (q31 c4) ∷
   rw 32 (q33 c4) ∷
   rw 33 (q34 c4) ∷
   rw⁻ 34 (q1 c4) ∷
   rw 35 (q29 c4) ∷
   rw 37 (q29 c4) ∷
   rw 35 (q30 c4) ∷
   rw 35 (q31 c4) ∷
   rw 36 (q31 c4) ∷
   rw 37 (q33 c4) ∷
   rw 38 (q35 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw 40 (q29 c4) ∷
   rw 42 (q29 c4) ∷
   rw 40 (q30 c4) ∷
   rw 40 (q31 c4) ∷
   rw 41 (q31 c4) ∷
   rw 42 (q33 c4) ∷
   rw⁻ 43 (q12 c4) ∷
   rw 45 (q18 c4) ∷
   rw 45 (q13 c4) ∷
   rw 44 (q14 c4) ∷
   rw 44 (q15 c4) ∷
   rw 44 (q22 c4) ∷
   rw 44 (q32 c4) ∷
   rw 45 (q32 c4) ∷
   rw 46 (q32 c4) ∷
   rw⁻ 47 (q1 c4) ∷
   rw 48 (q29 c4) ∷
   rw 50 (q29 c4) ∷
   rw 48 (q30 c4) ∷
   rw 48 (q31 c4) ∷
   rw 49 (q31 c4) ∷
   rw 50 (q33 c4) ∷
   rw 51 (q37 c4) ∷
   rw 51 (q38 c4) ∷
   rw 51 (q39 c4) ∷
   rw 46 (q40 c4) ∷
   rw 45 (q40 c4) ∷
   rw 44 (q40 c4) ∷
   rw 42 (q41 c4) ∷
   rw 44 (q40 c4) ∷
   rw 43 (q42 c4) ∷
   rw 41 (q41 c4) ∷
   rw 43 (q40 c4) ∷
   rw 42 (q42 c4) ∷
   rw 40 (q41 c4) ∷
   rw 42 (q40 c4) ∷
   rw 41 (q42 c4) ∷
   rw 28 (q42 c4) ∷
   rw 27 (q42 c4) ∷
   rw 25 (q40 c4) ∷
   rw 27 (q40 c4) ∷
   rw 26 (q42 c4) ∷
   rw 24 (q40 c4) ∷
   rw 26 (q40 c4) ∷
   rw 25 (q42 c4) ∷
   rw 22 (q41 c4) ∷
   rw 24 (q40 c4) ∷
   rw 26 (q40 c4) ∷
   rw 25 (q42 c4) ∷
   rw 23 (q42 c4) ∷
   rw 24 (q42 c4) ∷
   rw 21 (q41 c4) ∷
   rw 23 (q40 c4) ∷
   rw 25 (q40 c4) ∷
   rw 24 (q42 c4) ∷
   rw 22 (q42 c4) ∷
   rw 23 (q42 c4) ∷
   rw 19 (q40 c4) ∷
   rw 21 (q43 c4) ∷
   rw 22 (q40 c4) ∷
   rw 24 (q40 c4) ∷
   rw 23 (q42 c4) ∷
   rw 20 (q41 c4) ∷
   rw 22 (q40 c4) ∷
   rw 24 (q40 c4) ∷
   rw 23 (q42 c4) ∷
   rw 21 (q42 c4) ∷
   rw 22 (q42 c4) ∷
   rw 18 (q40 c4) ∷
   rw 20 (q43 c4) ∷
   rw 21 (q40 c4) ∷
   rw 23 (q40 c4) ∷
   rw 22 (q42 c4) ∷
   rw 19 (q41 c4) ∷
   rw 21 (q40 c4) ∷
   rw 23 (q40 c4) ∷
   rw 22 (q42 c4) ∷
   rw 20 (q42 c4) ∷
   rw 21 (q42 c4) ∷
   rw 8 (q44 c4) ∷
   rw 7 (q45 c4) ∷
   rw 65 (q46 c4) ∷
   rw 66 (q47 c4) ∷
   rw 65 (q48 c4) ∷
   rw 65 (q46 c4) ∷
   rw 65 (q46 c4) ∷
   rw 66 (q49 c4) ∷
   rw 65 (q48 c4) ∷
   rw 65 (q46 c4) ∷
   rw 66 (q49 c4) ∷
   rw 65 (q48 c4) ∷
   rw 66 (q46 c4) ∷
   rw 0 (q50 c4) ∷
   rw⁻ 0 (q51 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = eqn (Bx1-2034 ∷ []) (Bx1-2304 ∷ []) (lem-sym23-at011220 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (Bx1-2304 ∷ []) (Toff123 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ []) (lem-beta-T-at01122330 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (Toff123 ∷ Toff123 ∷ []) [] (wl0618 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (Bx0-1234 ∷ []) (Bx0-2134 ∷ []) (lem-sym12 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (Bx0-2134 ∷ []) (Bx0-2314 ∷ []) (lem-sym23-at1221 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (Toff123 ∷ Bx0-2314 ∷ Toff123 ∷ []) (Bx0-2314 ∷ CCZ234 ∷ []) (lem-T312-beta-at122331 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (Bx0-2314 ∷ []) (Bx0-2134 ∷ []) (lem-sym23-at122331 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (Bx0-2134 ∷ []) (Bx0-1234 ∷ []) (lem-sym12-at1221 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (Bx0-1234 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (Bx0-1234 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ104 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (CCZ234 ∷ Toff123 ∷ []) (Toff123 ∷ CCZ234 ∷ []) (wl0619 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (CCZ014 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0110243243 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (CCZ234 ∷ CCZ234 ∷ []) [] (wl0265 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (Bx1-2304 ∷ []) (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4)

-- auto BOX(0;1234) | BOX(1;2034): 25 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·2034⟩ : Ws → ⟪ (Bx0-1234 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·2034⟩ c4 = derive (Bx0-1234 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ Bx0-1234 ∷ [])
  (rw 1 (q52 c4) ∷
   rw 1 (q53 c4) ∷
   rw⁻ 0 (q54 c4) ∷
   rw 2 (q55 c4) ∷
   rw 2 (q56 c4) ∷
   rw 1 (q57 c4) ∷
   rw 1 (q58 c4) ∷
   rw 1 (q59 c4) ∷
   rw 1 (q60 c4) ∷
   rw 2 (q61 c4) ∷
   rw⁻ 3 (q54 c4) ∷
   rw 5 (q55 c4) ∷
   rw 5 (q56 c4) ∷
   rw 4 (q57 c4) ∷
   rw 4 (q58 c4) ∷
   rw 4 (q59 c4) ∷
   rw 4 (q60 c4) ∷
   rw 5 (q61 c4) ∷
   rw⁻ 0 (q62 c4) ∷
   rw⁻ 3 (q62 c4) ∷
   rw 2 (q63 c4) ∷
   rw⁻ 1 (q62 c4) ∷
   rw 0 (q64 c4) ∷
   rw⁻ 0 (q53 c4) ∷
   rw 0 (q65 c4) ∷ []) Eq.refl

-- boxify-10 [nf of rhs]: 0 steps
lem-boxify-10-nf-of-rhs : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-boxify-10-nf-of-rhs c4 = refl

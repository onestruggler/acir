{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D169 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0244 ; wl0614 ; wl0615 ; wl0616 ; wl0620 ; wl0621 ; wl0622 ; wl0623 ; wp0034 ; wp0055 ; wp0064 ; wp0263 ; wp0265 ; wp0268 ; wp0276 ; wp0277 ; wp0278 ; wp0279 ; wp0281 ; wp0282 ; wp0283)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0 ; lem-T312-beta-at0314203142 ; lem-T312-beta-at0314213240 ; lem-sym12-at0314203142 ; lem-sym23-at0314203142 ; lem-sym23-at0314213042 ; lem-sym34-at0310213442 ; lem-sym34-at0314213042 ; lem-sym34-at0314213240)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym23-at03102132 ; lem-sym23-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-sym23-at02102331)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym12-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D089 using (lem-sym12-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-sym23-at0213243041 ; lem-sym34-at0213203441)
open import Examples.Groups.Clifford+CS.Five.D.D161 using (lem-F0-at011220 ; lem-T312-beta-at03143041 ; lem-T312-beta-at03143140 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at03243240 ; lem-sym12-at0314213240 ; lem-sym12-at03243240 ; lem-sym23-at0314213240 ; lem-sym23-at03143140 ; lem-sym34-at03143041 ; lem-sym34-at03143140)
open import Examples.Groups.Clifford+CS.Five.D.D162 using (lem-T312-beta-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CS43-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CSd43-at03243240 ; lem-beta-inv-at03243240)
open import Examples.Groups.Clifford+CS.Five.D.D164 using (lem-TW-at0213243041 ; lem-TW-at0312243041 ; lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0213243041 ; lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0312243041 ; lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03102132 ; lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at03102132 ; lem-beta-inv-at0312243041 ; lem-sym12-at03103441 ; lem-sym12-at03122031 ; lem-sym23-at031031 ; lem-sym23-at0312203441 ; lem-sym23-at0312243041 ; lem-sym34-at031031 ; lem-sym34-at0312203441)
open import Examples.Groups.Clifford+CS.Five.D.D168 using (lem-boxify-11-nf-of-rhs)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sb0-1-42-3 ∷ []) (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ []) (lem-F0 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Toff214 ∷ Toff214 ∷ []) [] (wl0244 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (Bx3-0412 ∷ []) (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Bx3-4012 ∷ []) (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Bx3-4102 ∷ []) (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (Toff214 ∷ Bx3-4120 ∷ Toff214 ∷ []) (Bx3-4120 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314213240 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (Bx3-4120 ∷ []) (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (Bx3-4102 ∷ []) (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (Bx3-4012 ∷ []) (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Bx3-0412 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Bx3-0412 ∷ CS02 ∷ []) (CS02 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Bx3-0412 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Toff124 ∷ Toff124 ∷ []) [] (wl0614 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (Bx3-4120 ∷ []) (Bx3-4210 ∷ []) (lem-sym23-at0314213240 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Toff124 ∷ Bx3-4210 ∷ Toff124 ∷ []) (Bx3-4210 ∷ CCZ024 ∷ []) (lem-T312-beta-at03143140 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (Bx3-4210 ∷ []) (Bx3-4120 ∷ []) (lem-sym23-at03143140 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (Bx3-0412 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (Toff024 ∷ Toff024 ∷ []) [] (wp0268 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Bx3-1420 ∷ []) (Bx3-4120 ∷ []) (lem-sym12-at03243240 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (Bx3-4210 ∷ []) (Bx3-4201 ∷ []) (lem-sym34-at03143140 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (Toff024 ∷ Bx3-4201 ∷ Toff024 ∷ []) (Bx3-4201 ∷ CCZ124 ∷ []) (lem-T312-beta-at03143041 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (Bx3-4201 ∷ []) (Bx3-4210 ∷ []) (lem-sym34-at03143041 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (Bx3-4120 ∷ []) (Bx3-1420 ∷ []) (lem-sym12-at0314213240 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Bx3-1420 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (Bx3-1420 ∷ CS01 ∷ []) (CS01 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at03243240 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (Bx3-1420 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at03243240 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (Toff104 ∷ Toff104 ∷ []) [] (wp0064 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (Toff104 ∷ Bx3-4012 ∷ Toff104 ∷ []) (Bx3-4012 ∷ CCZ024 ∷ []) (lem-T312-beta-at0314203142 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (Bx3-1420 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at03243240 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Toff214 ∷ []) (Toff214 ∷ []) (wl0615 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (Toff214 ∷ Bx3-1420 ∷ Toff214 ∷ []) (Bx3-1420 ∷ CCZ014 ∷ []) (lem-T312-beta-at03243240 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx3-1420 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (Bx3-1420 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at03243240 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (Bx3-1420 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at03243240 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Bx3-1420 ∷ CS02 ∷ []) (CS02 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS43-at03243240 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (Bx3-1420 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd43-at03243240 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Bx3-1420 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at03243240 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (Bx3-1420 ∷ Bx3-1420 ∷ []) [] (lem-beta-inv-at03243240 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (Bx3-0412 ∷ []) (Bx3-0142 ∷ []) (lem-sym23-at0310243142 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (Bx3-0142 ∷ []) (Bx3-0124 ∷ []) (lem-sym34-at0310213442 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ024 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ014 ∷ Toff124 ∷ []) (Toff124 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0265 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ014 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ024 ∷ Toff124 ∷ []) (Toff124 ∷ CCZ024 ∷ []) (wp0281 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ124 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ124 ∷ []) (wp0278 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ024 ∷ Toff024 ∷ []) (Toff024 ∷ CZ24 ∷ CCZ024 ∷ []) (wp0279 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp0055 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ []) (wp0282 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CCZ024 ∷ CCZ024 ∷ []) [] (wp0034 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (CCZ014 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ014 ∷ []) (wp0277 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Toff024 ∷ CZ24 ∷ CCZ024 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ []) [] (wp0283 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (Bx3-0124 ∷ []) (Bx3-0124 ∷ []) (lem-boxify-11-nf-of-rhs c4)

-- boxify-11: 334 steps
lem-boxify-11 : Ws → ⟪ (Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-boxify-11 c4 = derive (Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-0124 ∷ [])
  (rw 0 (q1 c4) ∷
   re 0 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) ∷
   re 2 1 (CS01 ∷ []) ∷
   re 4 1 (CS01⁻ ∷ []) ∷
   rw 7 (q1 c4) ∷
   re 7 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) ∷
   re 9 1 (CS01 ∷ []) ∷
   re 11 1 (CS01⁻ ∷ []) ∷
   rw 16 (q2 c4) ∷
   re 16 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   re 18 1 (CS02 ∷ []) ∷
   re 20 1 (CS02⁻ ∷ []) ∷
   rw⁻ 16 (q3 c4) ∷
   rw 18 (q4 c4) ∷
   rw 18 (q5 c4) ∷
   rw 18 (q6 c4) ∷
   rw 17 (q7 c4) ∷
   rw 17 (q8 c4) ∷
   rw 17 (q9 c4) ∷
   rw 17 (q10 c4) ∷
   rw 17 (q11 c4) ∷
   rw 18 (q12 c4) ∷
   rw⁻ 19 (q3 c4) ∷
   rw 21 (q4 c4) ∷
   rw 21 (q5 c4) ∷
   rw 21 (q6 c4) ∷
   rw 20 (q7 c4) ∷
   rw 20 (q8 c4) ∷
   rw 20 (q9 c4) ∷
   rw 20 (q10 c4) ∷
   rw 20 (q11 c4) ∷
   rw 21 (q13 c4) ∷
   rw⁻ 22 (q3 c4) ∷
   rw 24 (q4 c4) ∷
   rw 24 (q5 c4) ∷
   rw 24 (q6 c4) ∷
   rw 23 (q7 c4) ∷
   rw 23 (q8 c4) ∷
   rw 23 (q9 c4) ∷
   rw 23 (q10 c4) ∷
   rw 23 (q11 c4) ∷
   rw⁻ 24 (q14 c4) ∷
   rw 26 (q4 c4) ∷
   rw 26 (q5 c4) ∷
   rw 26 (q6 c4) ∷
   rw 26 (q15 c4) ∷
   rw 25 (q16 c4) ∷
   rw 25 (q17 c4) ∷
   rw 25 (q8 c4) ∷
   rw 25 (q9 c4) ∷
   rw 25 (q10 c4) ∷
   rw 25 (q18 c4) ∷
   rw⁻ 26 (q3 c4) ∷
   rw 28 (q4 c4) ∷
   rw 28 (q5 c4) ∷
   rw 28 (q6 c4) ∷
   rw 27 (q7 c4) ∷
   rw 27 (q8 c4) ∷
   rw 27 (q9 c4) ∷
   rw 27 (q10 c4) ∷
   rw 27 (q11 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw 9 (q20 c4) ∷
   rw 9 (q15 c4) ∷
   rw 9 (q21 c4) ∷
   rw 8 (q22 c4) ∷
   rw 8 (q23 c4) ∷
   rw 8 (q17 c4) ∷
   rw 8 (q24 c4) ∷
   rw 8 (q25 c4) ∷
   rw 9 (q26 c4) ∷
   rw⁻ 10 (q19 c4) ∷
   rw 12 (q20 c4) ∷
   rw 12 (q15 c4) ∷
   rw 12 (q21 c4) ∷
   rw 11 (q22 c4) ∷
   rw 11 (q23 c4) ∷
   rw 11 (q17 c4) ∷
   rw 11 (q24 c4) ∷
   rw 11 (q25 c4) ∷
   rw 12 (q27 c4) ∷
   rw⁻ 13 (q28 c4) ∷
   rw 15 (q20 c4) ∷
   rw 15 (q8 c4) ∷
   rw 15 (q9 c4) ∷
   rw 14 (q29 c4) ∷
   rw 14 (q5 c4) ∷
   rw 14 (q6 c4) ∷
   rw 14 (q24 c4) ∷
   rw 14 (q30 c4) ∷
   rw⁻ 15 (q3 c4) ∷
   rw 16 (q31 c4) ∷
   rw 18 (q31 c4) ∷
   rw 16 (q32 c4) ∷
   rw 16 (q33 c4) ∷
   rw⁻ 17 (q14 c4) ∷
   rw 19 (q20 c4) ∷
   rw 19 (q15 c4) ∷
   rw 18 (q16 c4) ∷
   rw 18 (q17 c4) ∷
   rw 18 (q24 c4) ∷
   rw 18 (q34 c4) ∷
   rw⁻ 19 (q3 c4) ∷
   rw 20 (q31 c4) ∷
   rw 22 (q31 c4) ∷
   rw 20 (q32 c4) ∷
   rw 20 (q33 c4) ∷
   rw⁻ 21 (q3 c4) ∷
   rw 22 (q31 c4) ∷
   rw 24 (q31 c4) ∷
   rw 22 (q32 c4) ∷
   rw 22 (q33 c4) ∷
   rw 23 (q35 c4) ∷
   rw 24 (q36 c4) ∷
   rw⁻ 25 (q3 c4) ∷
   rw 26 (q31 c4) ∷
   rw 28 (q31 c4) ∷
   rw 26 (q32 c4) ∷
   rw 26 (q33 c4) ∷
   rw 27 (q35 c4) ∷
   rw 28 (q37 c4) ∷
   rw⁻ 29 (q3 c4) ∷
   rw 30 (q31 c4) ∷
   rw 32 (q31 c4) ∷
   rw 30 (q32 c4) ∷
   rw 30 (q33 c4) ∷
   rw 31 (q35 c4) ∷
   rw⁻ 32 (q14 c4) ∷
   rw 34 (q20 c4) ∷
   rw 34 (q15 c4) ∷
   rw 33 (q16 c4) ∷
   rw 33 (q17 c4) ∷
   rw 33 (q24 c4) ∷
   rw 33 (q34 c4) ∷
   rw 34 (q34 c4) ∷
   rw⁻ 35 (q3 c4) ∷
   rw 36 (q31 c4) ∷
   rw 38 (q31 c4) ∷
   rw 36 (q32 c4) ∷
   rw 36 (q33 c4) ∷
   rw 37 (q35 c4) ∷
   rw⁻ 0 (q19 c4) ∷
   rw 2 (q20 c4) ∷
   rw 2 (q15 c4) ∷
   rw 2 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   rw 1 (q23 c4) ∷
   rw 1 (q17 c4) ∷
   rw 1 (q24 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q26 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw 5 (q20 c4) ∷
   rw 5 (q15 c4) ∷
   rw 5 (q21 c4) ∷
   rw 4 (q22 c4) ∷
   rw 4 (q23 c4) ∷
   rw 4 (q17 c4) ∷
   rw 4 (q24 c4) ∷
   rw 4 (q25 c4) ∷
   rw 5 (q27 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw 8 (q20 c4) ∷
   rw 8 (q8 c4) ∷
   rw 8 (q9 c4) ∷
   rw 7 (q29 c4) ∷
   rw 7 (q5 c4) ∷
   rw 7 (q6 c4) ∷
   rw 7 (q24 c4) ∷
   rw 7 (q30 c4) ∷
   rw 8 (q38 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw 11 (q20 c4) ∷
   rw 11 (q15 c4) ∷
   rw 11 (q21 c4) ∷
   rw 10 (q22 c4) ∷
   rw 10 (q23 c4) ∷
   rw 10 (q17 c4) ∷
   rw 10 (q24 c4) ∷
   rw 10 (q25 c4) ∷
   rw 11 (q25 c4) ∷
   rw 12 (q26 c4) ∷
   rw⁻ 13 (q19 c4) ∷
   rw 15 (q20 c4) ∷
   rw 15 (q15 c4) ∷
   rw 15 (q21 c4) ∷
   rw 14 (q22 c4) ∷
   rw 14 (q23 c4) ∷
   rw 14 (q17 c4) ∷
   rw 14 (q24 c4) ∷
   rw 14 (q25 c4) ∷
   rw 15 (q25 c4) ∷
   rw 16 (q27 c4) ∷
   rw⁻ 17 (q28 c4) ∷
   rw 19 (q20 c4) ∷
   rw 19 (q8 c4) ∷
   rw 19 (q9 c4) ∷
   rw 18 (q29 c4) ∷
   rw 18 (q5 c4) ∷
   rw 18 (q6 c4) ∷
   rw 18 (q24 c4) ∷
   rw 18 (q30 c4) ∷
   rw 19 (q30 c4) ∷
   rw⁻ 20 (q3 c4) ∷
   rw 21 (q31 c4) ∷
   rw 23 (q31 c4) ∷
   rw 21 (q32 c4) ∷
   rw 21 (q33 c4) ∷
   rw 22 (q33 c4) ∷
   rw⁻ 23 (q14 c4) ∷
   rw 25 (q20 c4) ∷
   rw 25 (q15 c4) ∷
   rw 24 (q16 c4) ∷
   rw 24 (q17 c4) ∷
   rw 24 (q24 c4) ∷
   rw 24 (q34 c4) ∷
   rw 25 (q34 c4) ∷
   rw⁻ 26 (q3 c4) ∷
   rw 27 (q31 c4) ∷
   rw 29 (q31 c4) ∷
   rw 27 (q32 c4) ∷
   rw 27 (q33 c4) ∷
   rw 28 (q33 c4) ∷
   rw⁻ 29 (q3 c4) ∷
   rw 30 (q31 c4) ∷
   rw 32 (q31 c4) ∷
   rw 30 (q32 c4) ∷
   rw 30 (q33 c4) ∷
   rw 31 (q33 c4) ∷
   rw 32 (q35 c4) ∷
   rw 33 (q36 c4) ∷
   rw⁻ 34 (q3 c4) ∷
   rw 35 (q31 c4) ∷
   rw 37 (q31 c4) ∷
   rw 35 (q32 c4) ∷
   rw 35 (q33 c4) ∷
   rw 36 (q33 c4) ∷
   rw 37 (q35 c4) ∷
   rw 38 (q37 c4) ∷
   rw⁻ 39 (q3 c4) ∷
   rw 40 (q31 c4) ∷
   rw 42 (q31 c4) ∷
   rw 40 (q32 c4) ∷
   rw 40 (q33 c4) ∷
   rw 41 (q33 c4) ∷
   rw 42 (q35 c4) ∷
   rw⁻ 43 (q14 c4) ∷
   rw 45 (q20 c4) ∷
   rw 45 (q15 c4) ∷
   rw 44 (q16 c4) ∷
   rw 44 (q17 c4) ∷
   rw 44 (q24 c4) ∷
   rw 44 (q34 c4) ∷
   rw 45 (q34 c4) ∷
   rw 46 (q34 c4) ∷
   rw⁻ 47 (q3 c4) ∷
   rw 48 (q31 c4) ∷
   rw 50 (q31 c4) ∷
   rw 48 (q32 c4) ∷
   rw 48 (q33 c4) ∷
   rw 49 (q33 c4) ∷
   rw 50 (q35 c4) ∷
   rw 51 (q39 c4) ∷
   rw 51 (q40 c4) ∷
   rw 51 (q41 c4) ∷
   rw 46 (q42 c4) ∷
   rw 45 (q42 c4) ∷
   rw 44 (q42 c4) ∷
   rw 42 (q43 c4) ∷
   rw 44 (q42 c4) ∷
   rw 43 (q44 c4) ∷
   rw 41 (q43 c4) ∷
   rw 43 (q42 c4) ∷
   rw 42 (q44 c4) ∷
   rw 40 (q43 c4) ∷
   rw 42 (q42 c4) ∷
   rw 41 (q44 c4) ∷
   rw 28 (q44 c4) ∷
   rw 27 (q44 c4) ∷
   rw 25 (q42 c4) ∷
   rw 27 (q42 c4) ∷
   rw 26 (q44 c4) ∷
   rw 24 (q42 c4) ∷
   rw 26 (q42 c4) ∷
   rw 25 (q44 c4) ∷
   rw 22 (q43 c4) ∷
   rw 24 (q42 c4) ∷
   rw 26 (q42 c4) ∷
   rw 25 (q44 c4) ∷
   rw 23 (q44 c4) ∷
   rw 24 (q44 c4) ∷
   rw 21 (q43 c4) ∷
   rw 23 (q42 c4) ∷
   rw 25 (q42 c4) ∷
   rw 24 (q44 c4) ∷
   rw 22 (q44 c4) ∷
   rw 23 (q44 c4) ∷
   rw 19 (q42 c4) ∷
   rw 21 (q45 c4) ∷
   rw 22 (q42 c4) ∷
   rw 24 (q42 c4) ∷
   rw 23 (q44 c4) ∷
   rw 20 (q43 c4) ∷
   rw 22 (q42 c4) ∷
   rw 24 (q42 c4) ∷
   rw 23 (q44 c4) ∷
   rw 21 (q44 c4) ∷
   rw 22 (q44 c4) ∷
   rw 18 (q42 c4) ∷
   rw 20 (q45 c4) ∷
   rw 21 (q42 c4) ∷
   rw 23 (q42 c4) ∷
   rw 22 (q44 c4) ∷
   rw 19 (q43 c4) ∷
   rw 21 (q42 c4) ∷
   rw 23 (q42 c4) ∷
   rw 22 (q44 c4) ∷
   rw 20 (q44 c4) ∷
   rw 21 (q44 c4) ∷
   rw 8 (q46 c4) ∷
   rw 7 (q47 c4) ∷
   rw 65 (q48 c4) ∷
   rw 66 (q49 c4) ∷
   rw 65 (q50 c4) ∷
   rw 65 (q48 c4) ∷
   rw 65 (q48 c4) ∷
   rw 66 (q51 c4) ∷
   rw 65 (q50 c4) ∷
   rw 65 (q48 c4) ∷
   rw 66 (q51 c4) ∷
   rw 65 (q50 c4) ∷
   rw 66 (q48 c4) ∷
   rw 0 (q52 c4) ∷
   rw⁻ 0 (q53 c4) ∷ []) Eq.refl

-- boxify-12 [nf of rhs]: 0 steps
lem-boxify-12-nf-of-rhs : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-boxify-12-nf-of-rhs c4 = refl

private
  q54 : Ws → Eqn
  q54 c4 = eqn (Bx3-0124 ∷ Toff324 ∷ []) (Toff324 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at03102132 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (Toff324 ∷ Toff324 ∷ []) [] (wl0616 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (Bx3-0124 ∷ []) (Bx3-0124 ∷ []) (lem-boxify-12-nf-of-rhs c4)

-- boxify-12: 3 steps
lem-boxify-12 : Ws → ⟪ (Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-boxify-12 c4 = derive (Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ []) (Bx3-0124 ∷ [])
  (rw 1 (q54 c4) ∷
   rw 0 (q55 c4) ∷
   rw⁻ 0 (q56 c4) ∷ []) Eq.refl

-- boxify-13 [nf of rhs]: 0 steps
lem-boxify-13-nf-of-rhs : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-boxify-13-nf-of-rhs c4 = refl

private
  q57 : Ws → Eqn
  q57 c4 = eqn (Toff234 ∷ Toff234 ∷ []) [] (wl0620 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (Toff234 ∷ []) (Toff234 ∷ []) (wl0621 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (Bx3-0124 ∷ []) (Bx3-0214 ∷ []) (lem-sym23-at03102132 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (Bx3-0214 ∷ []) (Bx3-0241 ∷ []) (lem-sym34-at031031 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (Bx3-0241 ∷ []) (Bx3-2041 ∷ []) (lem-sym12-at03103441 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (Bx3-2041 ∷ []) (Bx3-2401 ∷ []) (lem-sym23-at0312203441 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (Toff234 ∷ Bx3-2401 ∷ Toff234 ∷ []) (Bx3-2401 ∷ Bx2-3401 ∷ []) (lem-TW-at0312243041 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (Bx3-2401 ∷ []) (Bx3-2041 ∷ []) (lem-sym23-at0312243041 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (Bx3-2041 ∷ []) (Bx3-2014 ∷ []) (lem-sym34-at0312203441 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (Bx3-2014 ∷ []) (Bx3-0214 ∷ []) (lem-sym12-at03122031 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (Bx3-0214 ∷ []) (Bx3-0124 ∷ []) (lem-sym23-at031031 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (Bx3-0124 ∷ Bx2-3401 ∷ []) (Bx2-3401 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03102132 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (Toff324 ∷ []) (Toff324 ∷ []) (wl0622 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (Toff324 ∷ Bx2-3401 ∷ Toff324 ∷ []) (Bx2-3401 ∷ Bx3-2401 ∷ []) (lem-TW-at0213243041 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (Bx2-3401 ∷ Bx3-2401 ∷ []) (Bx3-2401 ∷ Bx2-3401 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0213243041 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (Bx3-2401 ∷ Bx2-3401 ∷ []) (Bx2-3401 ∷ Bx3-2401 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0312243041 c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (Bx3-2401 ∷ Bx3-2401 ∷ []) [] (lem-beta-inv-at0312243041 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (Bx2-3401 ∷ []) (Bx2-3041 ∷ []) (lem-sym23-at0213243041 c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (Bx2-3041 ∷ []) (Bx2-3014 ∷ []) (lem-sym34-at0213203441 c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (Bx2-3014 ∷ []) (Bx2-0314 ∷ []) (lem-sym12-at02132031 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (Bx2-0314 ∷ []) (Bx2-0134 ∷ []) (lem-sym23-at02102331 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (Toff324 ∷ Toff234 ∷ Toff234 ∷ Toff324 ∷ []) [] (wl0623 (lit c4))
  q79 : Ws → Eqn
  q79 c4 = eqn (Bx2-0134 ∷ []) (Bx2-0134 ∷ []) (lem-boxify-13-nf-of-rhs c4)

-- boxify-13: 31 steps
lem-boxify-13 : Ws → ⟪ (Toff324 ∷ Toff234 ∷ Bx3-0124 ∷ Toff234 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-boxify-13 c4 = derive (Toff324 ∷ Toff234 ∷ Bx3-0124 ∷ Toff234 ∷ Toff324 ∷ []) (Bx2-0134 ∷ [])
  (rw⁻ 2 (q57 c4) ∷
   rw 3 (q58 c4) ∷
   rw 5 (q58 c4) ∷
   rw 4 (q59 c4) ∷
   rw 4 (q60 c4) ∷
   rw 4 (q61 c4) ∷
   rw 4 (q62 c4) ∷
   rw 3 (q63 c4) ∷
   rw 3 (q64 c4) ∷
   rw 3 (q65 c4) ∷
   rw 3 (q66 c4) ∷
   rw 3 (q67 c4) ∷
   rw 3 (q68 c4) ∷
   rw 4 (q54 c4) ∷
   rw⁻ 3 (q55 c4) ∷
   rw 4 (q69 c4) ∷
   rw 6 (q69 c4) ∷
   rw 4 (q70 c4) ∷
   rw 4 (q71 c4) ∷
   rw 4 (q72 c4) ∷
   rw 6 (q59 c4) ∷
   rw 6 (q60 c4) ∷
   rw 6 (q61 c4) ∷
   rw 6 (q62 c4) ∷
   rw 5 (q73 c4) ∷
   rw 4 (q74 c4) ∷
   rw 4 (q75 c4) ∷
   rw 4 (q76 c4) ∷
   rw 4 (q77 c4) ∷
   rw 0 (q78 c4) ∷
   rw⁻ 0 (q79 c4) ∷ []) Eq.refl

-- boxify-14 [nf of rhs]: 0 steps
lem-boxify-14-nf-of-rhs : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-boxify-14-nf-of-rhs c4 = refl

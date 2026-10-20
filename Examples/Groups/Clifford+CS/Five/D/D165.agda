{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D165 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0084 ; wl0244 ; wl0612 ; wl0613 ; wl0614 ; wl0615 ; wl0620 ; wl0621 ; wl0625 ; wl0626 ; wp0034 ; wp0055 ; wp0064 ; wp0263 ; wp0265 ; wp0267 ; wp0268 ; wp0276 ; wp0277 ; wp0278 ; wp0279 ; wp0281 ; wp0282 ; wp0283)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0 ; lem-T312-beta-at0314203142 ; lem-T312-beta-at0314213240 ; lem-sym12-at0314203142 ; lem-sym23-at0314203142 ; lem-sym23-at0314213042 ; lem-sym34-at0310213442 ; lem-sym34-at0314213042 ; lem-sym34-at0314213240)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-SB2 ; lem-sym23-at03102132 ; lem-sym23-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-sym23-at02102331)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym12-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D089 using (lem-sym12-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-sym23-at0213243041 ; lem-sym34-at0213203441)
open import Examples.Groups.Clifford+CS.Five.D.D161 using (lem-F0-at011220 ; lem-SB2-at011220 ; lem-SB2-at1221 ; lem-T312-beta-at03143041 ; lem-T312-beta-at03143140 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at03243240 ; lem-sym12-at0314213240 ; lem-sym12-at03243240 ; lem-sym23-at0314213240 ; lem-sym23-at03143140 ; lem-sym34-at03143041 ; lem-sym34-at03143140)
open import Examples.Groups.Clifford+CS.Five.D.D162 using (lem-T312-beta-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CS43-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CSd43-at03243240 ; lem-beta-inv-at03243240)
open import Examples.Groups.Clifford+CS.Five.D.D163 using (lem-boxify-1)
open import Examples.Groups.Clifford+CS.Five.D.D164 using (lem-TW-at0312243041 ; lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03102132 ; lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·1204⟩ ; lem-boxify-2 ; lem-boxify-3 ; lem-boxify-4 ; lem-boxify-5-nf-of-rhs ; lem-sym12-at03103441 ; lem-sym12-at03122031 ; lem-sym23-at031031 ; lem-sym23-at0312203441 ; lem-sym23-at0312243041 ; lem-sym34-at031031 ; lem-sym34-at0312203441)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-2-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-BOX⟨3·0124⟩ ; lem-nat-1-BOX⟨3·0214⟩ ; lem-nat-2-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨3·0124⟩)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨3·0214⟩ ; lem-nat-0-BOX⟨3·1204⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-2-SBOX⟨1·0·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-SBOX⟨0·2·43·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-SBOX⟨0·1·43·2⟩)

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
  q53 c4 = eqn (Bx3-0124 ∷ []) (Bx3-0124 ∷ []) (lem-boxify-5-nf-of-rhs c4)

-- boxify-5: 334 steps
lem-boxify-5 : Ws → ⟪ (Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-boxify-5 c4 = derive (Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-0124 ∷ [])
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

private
  q54 : Ws → Eqn
  q54 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (Sw23 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ []) (CCZ024 ∷ []) (lem-SB2-at1221 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 (lit c4))

-- SB2 @132132: 6 steps
lem-SB2-at132132 : Ws → ⟪ (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ []) ⟫ʷ
lem-SB2-at132132 c4 = derive (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ []) (CCZ034 ∷ [])
  (rw⁻ 0 (q54 c4) ∷
   rw 1 (q55 c4) ∷
   rw 2 (q55 c4) ∷
   rw 1 (q56 c4) ∷
   rw 0 (q57 c4) ∷
   rw 1 (q54 c4) ∷ []) Eq.refl

private
  q58 : Ws → Eqn
  q58 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (Sw01 ∷ Sb0-1-43-2 ∷ []) (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (Sb1-0-43-2 ∷ Sb1-0-43-2 ∷ []) (CCZ034 ∷ []) (lem-SB2-at132132 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 (lit c4))

-- SB2 @01132032: 6 steps
lem-SB2-at01132032 : Ws → ⟪ (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ []) ⟫ʷ
lem-SB2-at01132032 c4 = derive (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ []) (CCZ134 ∷ [])
  (rw⁻ 0 (q58 c4) ∷
   rw 1 (q59 c4) ∷
   rw 2 (q59 c4) ∷
   rw 1 (q60 c4) ∷
   rw 0 (q61 c4) ∷
   rw 1 (q58 c4) ∷ []) Eq.refl

private
  q62 : Ws → Eqn
  q62 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (Sw12 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ []) (CCZ134 ∷ []) (lem-SB2-at01132032 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl0084 (lit c4))

-- SB2 @02132031: 6 steps
lem-SB2-at02132031 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ []) ⟫ʷ
lem-SB2-at02132031 c4 = derive (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CCZ234 ∷ [])
  (rw⁻ 0 (q62 c4) ∷
   rw 1 (q63 c4) ∷
   rw 2 (q63 c4) ∷
   rw 1 (q64 c4) ∷
   rw⁻ 0 (q65 c4) ∷
   rw 1 (q62 c4) ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = eqn (Sw01 ∷ Bx1-0234 ∷ []) (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (Sw01 ∷ Bx3-0214 ∷ []) (Bx3-1204 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0214⟩ (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (Bx0-1234 ∷ Bx3-1204 ∷ []) (Bx3-1204 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·1204⟩ c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (Sw01 ∷ Bx3-1204 ∷ []) (Bx3-0214 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1204⟩ (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (Sw01 ∷ Bx0-1234 ∷ []) (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4))

-- auto BOX(0;1234) | BOX(3;1204) @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·1204⟩-at0110 : Ws → ⟪ (Bx1-0234 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·1204⟩-at0110 c4 = derive (Bx1-0234 ∷ Bx3-0214 ∷ []) (Bx3-0214 ∷ Bx1-0234 ∷ [])
  (rw⁻ 0 (q58 c4) ∷
   rw 1 (q66 c4) ∷
   rw 2 (q67 c4) ∷
   rw 1 (q68 c4) ∷
   rw 0 (q69 c4) ∷
   rw 1 (q70 c4) ∷
   rw 2 (q58 c4) ∷ []) Eq.refl

private
  q71 : Ws → Eqn
  q71 c4 = eqn (Sw12 ∷ Bx2-0134 ∷ []) (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (Sw12 ∷ Bx3-0124 ∷ []) (Bx3-0214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0124⟩ (lit c4))
  q73 : Ws → Eqn
  q73 c4 = eqn (Bx1-0234 ∷ Bx3-0214 ∷ []) (Bx3-0214 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·1204⟩-at0110 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (Sw12 ∷ Bx3-0214 ∷ []) (Bx3-0124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0214⟩ (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (Sw12 ∷ Bx1-0234 ∷ []) (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4))

-- auto BOX(0;1234) | BOX(3;1204) @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·1204⟩-at021021 : Ws → ⟪ (Bx2-0134 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·1204⟩-at021021 c4 = derive (Bx2-0134 ∷ Bx3-0124 ∷ []) (Bx3-0124 ∷ Bx2-0134 ∷ [])
  (rw⁻ 0 (q62 c4) ∷
   rw 1 (q71 c4) ∷
   rw 2 (q72 c4) ∷
   rw 1 (q73 c4) ∷
   rw 0 (q74 c4) ∷
   rw 1 (q75 c4) ∷
   rw 2 (q62 c4) ∷ []) Eq.refl

private
  q76 : Ws → Eqn
  q76 c4 = eqn (Sw23 ∷ Bx3-0124 ∷ []) (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ (lit c4))
  q77 : Ws → Eqn
  q77 c4 = eqn (Sw23 ∷ Bx2-0134 ∷ []) (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ (lit c4))
  q78 : Ws → Eqn
  q78 c4 = eqn (Bx2-0134 ∷ Bx3-0124 ∷ []) (Bx3-0124 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·1204⟩-at021021 c4)

-- auto BOX(0;1234) | BOX(3;1204) @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·1204⟩-at03102132 : Ws → ⟪ (Bx3-0124 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·1204⟩-at03102132 c4 = derive (Bx3-0124 ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ Bx3-0124 ∷ [])
  (rw⁻ 0 (q54 c4) ∷
   rw 1 (q76 c4) ∷
   rw 2 (q77 c4) ∷
   rw 1 (q78 c4) ∷
   rw 0 (q76 c4) ∷
   rw 1 (q77 c4) ∷
   rw 2 (q54 c4) ∷ []) Eq.refl

private
  q79 : Ws → Eqn
  q79 c4 = eqn (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (CCZ014 ∷ []) (lem-SB2 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (CCZ124 ∷ []) (lem-SB2-at011220 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CCZ234 ∷ []) (lem-SB2-at02132031 c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Toff104 ∷ []) (wp0267 c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ []) (wl0612 (lit c4))
  q84 : Ws → Eqn
  q84 c4 = eqn (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ []) (wl0613 (lit c4))
  q85 : Ws → Eqn
  q85 c4 = eqn (CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ []) (wl0625 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) (Toff234 ∷ []) (wl0626 (lit c4))
  q87 : Ws → Eqn
  q87 c4 = eqn (Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-0124 ∷ []) (lem-boxify-1 c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-0124 ∷ []) (lem-boxify-2 c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ []) (Bx3-0124 ∷ []) (lem-boxify-3 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (Toff324 ∷ Toff234 ∷ Bx3-0124 ∷ Toff234 ∷ Toff324 ∷ []) (Bx2-0134 ∷ []) (lem-boxify-4 c4)
  q91 : Ws → Eqn
  q91 c4 = eqn (Bx3-0124 ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·1204⟩-at03102132 c4)

-- F1 cx-ccz [nf of rhs]: 51 steps
lem-F1-cx-ccz-nf-of-rhs : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-F1-cx-ccz-nf-of-rhs c4 = derive (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (Bx2-0134 ∷ Bx3-0124 ∷ [])
  (rw 2 (q79 c4) ∷
   rw 5 (q80 c4) ∷
   rw 8 (q79 c4) ∷
   rw 12 (q80 c4) ∷
   rw 16 (q80 c4) ∷
   rw 20 (q80 c4) ∷
   rw 25 (q80 c4) ∷
   rw 29 (q80 c4) ∷
   rw 33 (q80 c4) ∷
   rw 37 (q81 c4) ∷
   rw 41 (q81 c4) ∷
   rw 45 (q81 c4) ∷
   rw 50 (q79 c4) ∷
   rw 53 (q80 c4) ∷
   rw 56 (q79 c4) ∷
   rw 60 (q80 c4) ∷
   rw 64 (q80 c4) ∷
   rw 68 (q80 c4) ∷
   rw 73 (q80 c4) ∷
   rw 77 (q80 c4) ∷
   rw 81 (q80 c4) ∷
   rw 85 (q81 c4) ∷
   rw 89 (q81 c4) ∷
   rw 93 (q81 c4) ∷
   rw 1 (q82 c4) ∷
   rw 4 (q82 c4) ∷
   rw 5 (q83 c4) ∷
   rw 6 (q84 c4) ∷
   rw 7 (q83 c4) ∷
   rw 9 (q83 c4) ∷
   rw 10 (q84 c4) ∷
   rw 11 (q83 c4) ∷
   rw 12 (q85 c4) ∷
   rw 13 (q86 c4) ∷
   rw 14 (q85 c4) ∷
   rw 16 (q82 c4) ∷
   rw 19 (q82 c4) ∷
   rw 20 (q83 c4) ∷
   rw 21 (q84 c4) ∷
   rw 22 (q83 c4) ∷
   rw 24 (q83 c4) ∷
   rw 25 (q84 c4) ∷
   rw 26 (q83 c4) ∷
   rw 27 (q85 c4) ∷
   rw 28 (q86 c4) ∷
   rw 29 (q85 c4) ∷
   rw 0 (q87 c4) ∷
   rw 4 (q88 c4) ∷
   rw 3 (q89 c4) ∷
   rw 1 (q90 c4) ∷
   rw 0 (q91 c4) ∷ []) Eq.refl

private
  q92 : Ws → Eqn
  q92 c4 = eqn (Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-0124 ∷ []) (lem-boxify-5 c4)
  q93 : Ws → Eqn
  q93 c4 = eqn (Toff234 ∷ Toff234 ∷ []) [] (wl0620 (lit c4))
  q94 : Ws → Eqn
  q94 c4 = eqn (Toff234 ∷ []) (Toff234 ∷ []) (wl0621 (lit c4))
  q95 : Ws → Eqn
  q95 c4 = eqn (Bx3-0124 ∷ []) (Bx3-0214 ∷ []) (lem-sym23-at03102132 c4)
  q96 : Ws → Eqn
  q96 c4 = eqn (Bx3-0214 ∷ []) (Bx3-0241 ∷ []) (lem-sym34-at031031 c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (Bx3-0241 ∷ []) (Bx3-2041 ∷ []) (lem-sym12-at03103441 c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (Bx3-2041 ∷ []) (Bx3-2401 ∷ []) (lem-sym23-at0312203441 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (Toff234 ∷ Bx3-2401 ∷ Toff234 ∷ []) (Bx3-2401 ∷ Bx2-3401 ∷ []) (lem-TW-at0312243041 c4)
  q100 : Ws → Eqn
  q100 c4 = eqn (Bx3-2401 ∷ []) (Bx3-2041 ∷ []) (lem-sym23-at0312243041 c4)
  q101 : Ws → Eqn
  q101 c4 = eqn (Bx3-2041 ∷ []) (Bx3-2014 ∷ []) (lem-sym34-at0312203441 c4)
  q102 : Ws → Eqn
  q102 c4 = eqn (Bx3-2014 ∷ []) (Bx3-0214 ∷ []) (lem-sym12-at03122031 c4)
  q103 : Ws → Eqn
  q103 c4 = eqn (Bx3-0214 ∷ []) (Bx3-0124 ∷ []) (lem-sym23-at031031 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (Bx3-0124 ∷ Bx2-3401 ∷ []) (Bx2-3401 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03102132 c4)
  q105 : Ws → Eqn
  q105 c4 = eqn (Bx2-3401 ∷ []) (Bx2-3041 ∷ []) (lem-sym23-at0213243041 c4)
  q106 : Ws → Eqn
  q106 c4 = eqn (Bx2-3041 ∷ []) (Bx2-3014 ∷ []) (lem-sym34-at0213203441 c4)
  q107 : Ws → Eqn
  q107 c4 = eqn (Bx2-3014 ∷ []) (Bx2-0314 ∷ []) (lem-sym12-at02132031 c4)
  q108 : Ws → Eqn
  q108 c4 = eqn (Bx2-0314 ∷ []) (Bx2-0134 ∷ []) (lem-sym23-at02102331 c4)
  q109 : Ws → Eqn
  q109 c4 = eqn (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (Bx2-0134 ∷ Bx3-0124 ∷ []) (lem-F1-cx-ccz-nf-of-rhs c4)

-- F1 cx-ccz: 41 steps
lem-F1-cx-ccz : Ws → ⟪ (CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-F1-cx-ccz c4 = derive (CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  (rw 1 (q81 c4) ∷
   rw 6 (q79 c4) ∷
   rw 9 (q80 c4) ∷
   rw 12 (q79 c4) ∷
   rw 16 (q80 c4) ∷
   rw 20 (q80 c4) ∷
   rw 24 (q80 c4) ∷
   rw 29 (q80 c4) ∷
   rw 33 (q80 c4) ∷
   rw 37 (q80 c4) ∷
   rw 41 (q81 c4) ∷
   rw 0 (q86 c4) ∷
   rw 2 (q82 c4) ∷
   rw 5 (q82 c4) ∷
   rw 6 (q83 c4) ∷
   rw 7 (q84 c4) ∷
   rw 8 (q83 c4) ∷
   rw 10 (q83 c4) ∷
   rw 11 (q84 c4) ∷
   rw 12 (q83 c4) ∷
   rw 13 (q86 c4) ∷
   rw 1 (q92 c4) ∷
   rw⁻ 1 (q93 c4) ∷
   rw 2 (q94 c4) ∷
   rw 4 (q94 c4) ∷
   rw 3 (q95 c4) ∷
   rw 3 (q96 c4) ∷
   rw 3 (q97 c4) ∷
   rw 3 (q98 c4) ∷
   rw 2 (q99 c4) ∷
   rw 2 (q100 c4) ∷
   rw 2 (q101 c4) ∷
   rw 2 (q102 c4) ∷
   rw 2 (q103 c4) ∷
   rw 2 (q104 c4) ∷
   rw 2 (q105 c4) ∷
   rw 2 (q106 c4) ∷
   rw 2 (q107 c4) ∷
   rw 2 (q108 c4) ∷
   rw 0 (q93 c4) ∷
   rw⁻ 0 (q109 c4) ∷ []) Eq.refl

-- boxify-6 [nf of rhs]: 0 steps
lem-boxify-6-nf-of-rhs : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-boxify-6-nf-of-rhs c4 = refl

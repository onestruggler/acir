{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D162 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0011 ; wl0012 ; wl0015 ; wl0016 ; wl0024 ; wl0025 ; wl0034 ; wl0035 ; wl0036 ; wl0043 ; wl0046 ; wl0078 ; wl0084 ; wl0134 ; wl0135 ; wl0138 ; wl0139 ; wl0154 ; wl0155 ; wl0244 ; wl0351 ; wl0613 ; wl0614 ; wp0034 ; wp0055 ; wp0064 ; wp0263 ; wp0264 ; wp0265 ; wp0266 ; wp0267 ; wp0268 ; wp0269 ; wp0270 ; wp0271 ; wp0272 ; wp0273 ; wp0274 ; wp0275 ; wp0276 ; wp0277 ; wp0278 ; wp0279 ; wp0280)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0 ; lem-T312-beta-at0314203142 ; lem-T312-beta-at0314213240 ; lem-beta-inv-at0310243142 ; lem-sym12-at0314203142 ; lem-sym23-at0314203142 ; lem-sym23-at0314213042 ; lem-sym34-at0314213042 ; lem-sym34-at0314213240)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-SB2)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at2332 ; lem-auto-BOX⟨0·1234⟩-∣-CS43)
open import Examples.Groups.Clifford+CS.Five.D.D089 using (lem-auto-BOX⟨0·1234⟩-∣-CSd43 ; lem-sym12-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D160 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D161 using (lem-F0-at011220 ; lem-F1-rel-266-nf-of-rhs ; lem-SB2-at011220 ; lem-T312-beta-at0310243142 ; lem-T312-beta-at03143041 ; lem-T312-beta-at03143140 ; lem-T312-beta-at03243042 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at03243240 ; lem-sym12-at0314213240 ; lem-sym12-at03243240 ; lem-sym23-at0314213240 ; lem-sym23-at03143140 ; lem-sym34-at03143041 ; lem-sym34-at03143140 ; lem-sym34-at03243042 ; lem-sym34-at03243240)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-3-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ014 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-3-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ014 ; lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-TOFF214)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0412⟩)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-2-CS12 ; lem-nat-2-CS13 ; lem-nat-2-CSd12 ; lem-nat-2-CSd13)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-1-BOX⟨3·0412⟩ ; lem-nat-3-CS23 ; lem-nat-3-CS24)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-3-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-3-CSd23)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-BOX⟨3·0421⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨3·0421⟩ ; lem-nat-0-BOX⟨3·1420⟩)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (CCZ014 ∷ []) (lem-SB2 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ []) (wp0266 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Toff104 ∷ []) (wp0267 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Sb0-1-42-3 ∷ []) (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Toff024 ∷ Toff024 ∷ []) [] (wp0268 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Bx3-1420 ∷ []) (Bx3-4120 ∷ []) (lem-sym12-at03243240 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (Bx3-4120 ∷ []) (Bx3-4210 ∷ []) (lem-sym23-at0314213240 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (Bx3-4210 ∷ []) (Bx3-4201 ∷ []) (lem-sym34-at03143140 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (Toff024 ∷ Bx3-4201 ∷ Toff024 ∷ []) (Bx3-4201 ∷ CCZ124 ∷ []) (lem-T312-beta-at03143041 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (Bx3-4201 ∷ []) (Bx3-4210 ∷ []) (lem-sym34-at03143041 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Bx3-4210 ∷ []) (Bx3-4120 ∷ []) (lem-sym23-at03143140 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Bx3-4120 ∷ []) (Bx3-1420 ∷ []) (lem-sym12-at0314213240 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Bx3-1420 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx3-1420 ∷ CS01 ∷ []) (CS01 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at03243240 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (Bx3-1420 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at03243240 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Toff104 ∷ Toff104 ∷ []) [] (wp0064 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (Bx3-4120 ∷ []) (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (Bx3-4102 ∷ []) (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (Toff104 ∷ Bx3-4012 ∷ Toff104 ∷ []) (Bx3-4012 ∷ CCZ024 ∷ []) (lem-T312-beta-at0314203142 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Bx3-4012 ∷ []) (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (Bx3-4102 ∷ []) (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (Bx3-1420 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at03243240 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (Toff014 ∷ Toff014 ∷ []) [] (wp0269 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (Toff014 ∷ []) (Toff014 ∷ []) (wp0270 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Bx3-1420 ∷ []) (Bx3-1402 ∷ []) (lem-sym34-at03243240 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (Toff014 ∷ Bx3-1402 ∷ Toff014 ∷ []) (Bx3-1402 ∷ CCZ124 ∷ []) (lem-T312-beta-at03243042 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (Bx3-1402 ∷ []) (Bx3-1420 ∷ []) (lem-sym34-at03243042 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (Bx3-1420 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at03243240 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (Bx3-4012 ∷ []) (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CCZ024 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0271 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Toff014 ∷ CCZ024 ∷ CCZ124 ∷ CCZ124 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0272 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (lem-F1-rel-266-nf-of-rhs c4)

-- F1 rel-266: 55 steps
lem-F1-rel-266 : Ws → ⟪ (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-266 c4 = derive (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ [])
  (rw 1 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw 14 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 3 (q3 c4) ∷
   rw 4 (q2 c4) ∷
   rw 2 (q4 c4) ∷
   re 2 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) ∷
   re 4 1 (CS01 ∷ []) ∷
   re 6 1 (CS01⁻ ∷ []) ∷
   rw⁻ 2 (q5 c4) ∷
   rw 4 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 4 (q8 c4) ∷
   rw 3 (q9 c4) ∷
   rw 3 (q10 c4) ∷
   rw 3 (q11 c4) ∷
   rw 3 (q12 c4) ∷
   rw 3 (q13 c4) ∷
   rw 4 (q14 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw 7 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 6 (q9 c4) ∷
   rw 6 (q10 c4) ∷
   rw 6 (q11 c4) ∷
   rw 6 (q12 c4) ∷
   rw 6 (q13 c4) ∷
   rw 7 (q15 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   rw 10 (q6 c4) ∷
   rw 10 (q17 c4) ∷
   rw 10 (q18 c4) ∷
   rw 9 (q19 c4) ∷
   rw 9 (q20 c4) ∷
   rw 9 (q21 c4) ∷
   rw 9 (q12 c4) ∷
   rw 9 (q22 c4) ∷
   rw⁻ 10 (q23 c4) ∷
   rw 11 (q24 c4) ∷
   rw 13 (q24 c4) ∷
   rw 12 (q25 c4) ∷
   rw 11 (q26 c4) ∷
   rw 11 (q27 c4) ∷
   rw 11 (q28 c4) ∷
   rw 12 (q6 c4) ∷
   rw 12 (q17 c4) ∷
   rw 12 (q18 c4) ∷
   rw 12 (q29 c4) ∷
   rw 9 (q30 c4) ∷
   rw 0 (q31 c4) ∷
   rw⁻ 0 (q32 c4) ∷ []) Eq.refl

private
  q33 : Ws → Eqn
  q33 c4 = eqn (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (CCZ124 ∷ []) (lem-SB2-at011220 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (CCZ124 ∷ Toff104 ∷ []) (Toff104 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0273 c4)

-- F1 rel-267 [nf of rhs]: 7 steps
lem-F1-rel-267-nf-of-rhs : Ws → ⟪ (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ CCZ124 ∷ []) ⟫ʷ
lem-F1-rel-267-nf-of-rhs c4 = derive (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (Toff104 ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ CCZ124 ∷ [])
  (rw 1 (q1 c4) ∷
   rw 4 (q33 c4) ∷
   rw 6 (q1 c4) ∷
   rw 9 (q33 c4) ∷
   rw 0 (q3 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q34 c4) ∷ []) Eq.refl

private
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ124 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ124 ∷ []) (wp0274 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (CCZ124 ∷ CCZ124 ∷ []) [] (wl0351 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (Toff014 ∷ Toff104 ∷ Toff104 ∷ Toff014 ∷ CCZ024 ∷ []) (Toff104 ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ CCZ124 ∷ []) (wp0275 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (Toff104 ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ CCZ124 ∷ []) (lem-F1-rel-267-nf-of-rhs c4)

-- F1 rel-267: 15 steps
lem-F1-rel-267 : Ws → ⟪ (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-rel-267 c4 = derive (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ [])
  (rw 1 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 8 (q33 c4) ∷
   rw 10 (q1 c4) ∷
   rw 14 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 3 (q3 c4) ∷
   rw 4 (q2 c4) ∷
   rw 2 (q34 c4) ∷
   rw 4 (q35 c4) ∷
   rw 3 (q30 c4) ∷
   rw 5 (q36 c4) ∷
   rw 0 (q37 c4) ∷
   rw⁻ 0 (q38 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = eqn (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ []) (wl0613 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ []) (lem-F0 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (Toff214 ∷ Toff214 ∷ []) [] (wl0244 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (Bx3-0412 ∷ []) (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (Toff214 ∷ Bx3-4120 ∷ Toff214 ∷ []) (Bx3-4120 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314213240 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (Bx3-0412 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (Bx3-0412 ∷ CS02 ∷ []) (CS02 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (Bx3-0412 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (Toff124 ∷ Toff124 ∷ []) [] (wl0614 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (Toff124 ∷ Bx3-4210 ∷ Toff124 ∷ []) (Bx3-4210 ∷ CCZ024 ∷ []) (lem-T312-beta-at03143140 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (Bx3-0412 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (Bx3-0412 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0310243142 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (Bx3-0412 ∷ Bx3-0412 ∷ []) [] (lem-beta-inv-at0310243142 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (CS02⁻ ∷ Toff124 ∷ []) (Toff124 ∷ CS02⁻ ∷ []) (wp0264 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (CCZ014 ∷ Toff124 ∷ []) (Toff124 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0265 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (CCZ014 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ []) (wp0276 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ024 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CCZ014 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ014 ∷ []) (wp0277 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp0055 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (CCZ024 ∷ CCZ024 ∷ []) [] (wp0034 c4)

-- F1 rel-268 [nf of rhs]: 122 steps
lem-F1-rel-268-nf-of-rhs : Ws → ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-F1-rel-268-nf-of-rhs c4 = derive (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CS02⁻ ∷ [])
  (rw 2 (q33 c4) ∷
   rw 5 (q1 c4) ∷
   rw 8 (q33 c4) ∷
   rw 1 (q39 c4) ∷
   rw 4 (q39 c4) ∷
   rw 0 (q40 c4) ∷
   re 0 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   re 2 1 (CS02 ∷ []) ∷
   re 4 1 (CS02⁻ ∷ []) ∷
   rw 7 (q40 c4) ∷
   re 7 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   re 9 1 (CS02 ∷ []) ∷
   re 11 1 (CS02⁻ ∷ []) ∷
   rw⁻ 7 (q41 c4) ∷
   rw 9 (q42 c4) ∷
   rw 9 (q20 c4) ∷
   rw 9 (q21 c4) ∷
   rw 8 (q43 c4) ∷
   rw 8 (q17 c4) ∷
   rw 8 (q18 c4) ∷
   rw 8 (q29 c4) ∷
   rw 8 (q44 c4) ∷
   rw 9 (q45 c4) ∷
   rw⁻ 10 (q41 c4) ∷
   rw 12 (q42 c4) ∷
   rw 12 (q20 c4) ∷
   rw 12 (q21 c4) ∷
   rw 11 (q43 c4) ∷
   rw 11 (q17 c4) ∷
   rw 11 (q18 c4) ∷
   rw 11 (q29 c4) ∷
   rw 11 (q44 c4) ∷
   rw 12 (q46 c4) ∷
   rw⁻ 13 (q47 c4) ∷
   rw 15 (q42 c4) ∷
   rw 15 (q20 c4) ∷
   rw 15 (q21 c4) ∷
   rw 15 (q7 c4) ∷
   rw 14 (q48 c4) ∷
   rw 14 (q11 c4) ∷
   rw 14 (q17 c4) ∷
   rw 14 (q18 c4) ∷
   rw 14 (q29 c4) ∷
   rw 14 (q49 c4) ∷
   rw⁻ 0 (q41 c4) ∷
   rw 2 (q42 c4) ∷
   rw 2 (q20 c4) ∷
   rw 2 (q21 c4) ∷
   rw 1 (q43 c4) ∷
   rw 1 (q17 c4) ∷
   rw 1 (q18 c4) ∷
   rw 1 (q29 c4) ∷
   rw 1 (q44 c4) ∷
   rw 2 (q45 c4) ∷
   rw⁻ 3 (q41 c4) ∷
   rw 5 (q42 c4) ∷
   rw 5 (q20 c4) ∷
   rw 5 (q21 c4) ∷
   rw 4 (q43 c4) ∷
   rw 4 (q17 c4) ∷
   rw 4 (q18 c4) ∷
   rw 4 (q29 c4) ∷
   rw 4 (q44 c4) ∷
   rw 5 (q46 c4) ∷
   rw⁻ 6 (q47 c4) ∷
   rw 8 (q42 c4) ∷
   rw 8 (q20 c4) ∷
   rw 8 (q21 c4) ∷
   rw 8 (q7 c4) ∷
   rw 7 (q48 c4) ∷
   rw 7 (q11 c4) ∷
   rw 7 (q17 c4) ∷
   rw 7 (q18 c4) ∷
   rw 7 (q29 c4) ∷
   rw 7 (q49 c4) ∷
   rw 8 (q50 c4) ∷
   rw⁻ 9 (q41 c4) ∷
   rw 11 (q42 c4) ∷
   rw 11 (q20 c4) ∷
   rw 11 (q21 c4) ∷
   rw 10 (q43 c4) ∷
   rw 10 (q17 c4) ∷
   rw 10 (q18 c4) ∷
   rw 10 (q29 c4) ∷
   rw 10 (q44 c4) ∷
   rw 11 (q44 c4) ∷
   rw 12 (q45 c4) ∷
   rw⁻ 13 (q41 c4) ∷
   rw 15 (q42 c4) ∷
   rw 15 (q20 c4) ∷
   rw 15 (q21 c4) ∷
   rw 14 (q43 c4) ∷
   rw 14 (q17 c4) ∷
   rw 14 (q18 c4) ∷
   rw 14 (q29 c4) ∷
   rw 14 (q44 c4) ∷
   rw 15 (q44 c4) ∷
   rw 16 (q46 c4) ∷
   rw⁻ 17 (q47 c4) ∷
   rw 19 (q42 c4) ∷
   rw 19 (q20 c4) ∷
   rw 19 (q21 c4) ∷
   rw 19 (q7 c4) ∷
   rw 18 (q48 c4) ∷
   rw 18 (q11 c4) ∷
   rw 18 (q17 c4) ∷
   rw 18 (q18 c4) ∷
   rw 18 (q29 c4) ∷
   rw 18 (q49 c4) ∷
   rw 19 (q49 c4) ∷
   rw 20 (q51 c4) ∷
   rw 16 (q52 c4) ∷
   rw 15 (q53 c4) ∷
   rw 14 (q53 c4) ∷
   rw 8 (q54 c4) ∷
   rw 7 (q55 c4) ∷
   rw 5 (q52 c4) ∷
   rw 4 (q53 c4) ∷
   rw⁻ 18 (q56 c4) ∷
   rw 17 (q57 c4) ∷
   rw 17 (q58 c4) ∷
   rw 18 (q58 c4) ∷ []) Eq.refl

private
  q59 : Ws → Eqn
  q59 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (Sw12 ∷ Bx3-0421 ∷ []) (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ (lit c4))

-- beta-inv @0310243241: 5 steps
lem-beta-inv-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at0310243241 c4 = derive (Bx3-0421 ∷ Bx3-0421 ∷ []) []
  (rw⁻ 0 (q59 c4) ∷
   rw 1 (q60 c4) ∷
   rw 2 (q60 c4) ∷
   rw 1 (q51 c4) ∷
   rw 0 (q59 c4) ∷ []) Eq.refl

private
  q61 : Ws → Eqn
  q61 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (Sw01 ∷ Bx3-1420 ∷ []) (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (Bx3-0421 ∷ Bx3-0421 ∷ []) [] (lem-beta-inv-at0310243241 c4)

-- beta-inv @03243240: 5 steps
lem-beta-inv-at03243240 : Ws → ⟪ (Bx3-1420 ∷ Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at03243240 c4 = derive (Bx3-1420 ∷ Bx3-1420 ∷ []) []
  (rw⁻ 0 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   rw 2 (q62 c4) ∷
   rw 1 (q63 c4) ∷
   rw 0 (q61 c4) ∷ []) Eq.refl

private
  q64 : Ws → Eqn
  q64 c4 = eqn (Bx3-1420 ∷ Bx3-1420 ∷ []) [] (lem-beta-inv-at03243240 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (CCZ124 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ124 ∷ []) (wp0278 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ024 ∷ Toff024 ∷ []) (Toff024 ∷ CZ24 ∷ CCZ024 ∷ []) (wp0279 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Toff024 ∷ CZ24 ∷ CCZ024 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CS02⁻ ∷ []) (wp0280 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CS02⁻ ∷ []) (lem-F1-rel-268-nf-of-rhs c4)

-- F1 rel-268: 110 steps
lem-F1-rel-268 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-268 c4 = derive (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ []) (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ [])
  (rw 2 (q1 c4) ∷
   rw 5 (q33 c4) ∷
   rw 8 (q1 c4) ∷
   rw 1 (q3 c4) ∷
   rw 4 (q3 c4) ∷
   rw 0 (q4 c4) ∷
   re 0 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) ∷
   re 2 1 (CS01 ∷ []) ∷
   re 4 1 (CS01⁻ ∷ []) ∷
   rw 7 (q4 c4) ∷
   re 7 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) ∷
   re 9 1 (CS01 ∷ []) ∷
   re 11 1 (CS01⁻ ∷ []) ∷
   rw⁻ 7 (q5 c4) ∷
   rw 9 (q6 c4) ∷
   rw 9 (q7 c4) ∷
   rw 9 (q8 c4) ∷
   rw 8 (q9 c4) ∷
   rw 8 (q10 c4) ∷
   rw 8 (q11 c4) ∷
   rw 8 (q12 c4) ∷
   rw 8 (q13 c4) ∷
   rw 9 (q14 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw 12 (q6 c4) ∷
   rw 12 (q7 c4) ∷
   rw 12 (q8 c4) ∷
   rw 11 (q9 c4) ∷
   rw 11 (q10 c4) ∷
   rw 11 (q11 c4) ∷
   rw 11 (q12 c4) ∷
   rw 11 (q13 c4) ∷
   rw 12 (q15 c4) ∷
   rw⁻ 13 (q16 c4) ∷
   rw 15 (q6 c4) ∷
   rw 15 (q17 c4) ∷
   rw 15 (q18 c4) ∷
   rw 14 (q19 c4) ∷
   rw 14 (q20 c4) ∷
   rw 14 (q21 c4) ∷
   rw 14 (q12 c4) ∷
   rw 14 (q22 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw 2 (q8 c4) ∷
   rw 1 (q9 c4) ∷
   rw 1 (q10 c4) ∷
   rw 1 (q11 c4) ∷
   rw 1 (q12 c4) ∷
   rw 1 (q13 c4) ∷
   rw 2 (q14 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 5 (q7 c4) ∷
   rw 5 (q8 c4) ∷
   rw 4 (q9 c4) ∷
   rw 4 (q10 c4) ∷
   rw 4 (q11 c4) ∷
   rw 4 (q12 c4) ∷
   rw 4 (q13 c4) ∷
   rw 5 (q15 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   rw 8 (q6 c4) ∷
   rw 8 (q17 c4) ∷
   rw 8 (q18 c4) ∷
   rw 7 (q19 c4) ∷
   rw 7 (q20 c4) ∷
   rw 7 (q21 c4) ∷
   rw 7 (q12 c4) ∷
   rw 7 (q22 c4) ∷
   rw 8 (q28 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw 11 (q6 c4) ∷
   rw 11 (q7 c4) ∷
   rw 11 (q8 c4) ∷
   rw 10 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw 10 (q11 c4) ∷
   rw 10 (q12 c4) ∷
   rw 10 (q13 c4) ∷
   rw 11 (q13 c4) ∷
   rw 12 (q14 c4) ∷
   rw⁻ 13 (q5 c4) ∷
   rw 15 (q6 c4) ∷
   rw 15 (q7 c4) ∷
   rw 15 (q8 c4) ∷
   rw 14 (q9 c4) ∷
   rw 14 (q10 c4) ∷
   rw 14 (q11 c4) ∷
   rw 14 (q12 c4) ∷
   rw 14 (q13 c4) ∷
   rw 15 (q13 c4) ∷
   rw 16 (q15 c4) ∷
   rw⁻ 17 (q16 c4) ∷
   rw 19 (q6 c4) ∷
   rw 19 (q17 c4) ∷
   rw 19 (q18 c4) ∷
   rw 18 (q19 c4) ∷
   rw 18 (q20 c4) ∷
   rw 18 (q21 c4) ∷
   rw 18 (q12 c4) ∷
   rw 18 (q22 c4) ∷
   rw 19 (q22 c4) ∷
   rw 20 (q64 c4) ∷
   rw 8 (q65 c4) ∷
   rw 7 (q66 c4) ∷
   rw 19 (q58 c4) ∷
   rw 0 (q67 c4) ∷
   rw⁻ 0 (q68 c4) ∷ []) Eq.refl

-- boxify-1 [nf of rhs]: 0 steps
lem-boxify-1-nf-of-rhs : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-boxify-1-nf-of-rhs c4 = refl

private
  q69 : Ws → Eqn
  q69 c4 = eqn (Sw12 ∷ Toff204 ∷ []) (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (Toff104 ∷ Bx3-0412 ∷ Toff104 ∷ []) (Bx3-0412 ∷ CCZ024 ∷ []) (lem-T312-beta-at0310243142 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (Sw12 ∷ Bx3-0412 ∷ []) (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4))

-- T312-beta @0310243241: 8 steps
lem-T312-beta-at0310243241 : Ws → ⟪ (Toff204 ∷ Bx3-0421 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ CCZ014 ∷ []) ⟫ʷ
lem-T312-beta-at0310243241 c4 = derive (Toff204 ∷ Bx3-0421 ∷ Toff204 ∷ []) (Bx3-0421 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q59 c4) ∷
   rw 1 (q69 c4) ∷
   rw 2 (q60 c4) ∷
   rw 3 (q69 c4) ∷
   rw 1 (q70 c4) ∷
   rw 0 (q71 c4) ∷
   rw 1 (q72 c4) ∷
   rw 2 (q59 c4) ∷ []) Eq.refl

private
  q73 : Ws → Eqn
  q73 c4 = eqn (Sw01 ∷ Toff214 ∷ []) (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (Toff204 ∷ Bx3-0421 ∷ Toff204 ∷ []) (Bx3-0421 ∷ CCZ014 ∷ []) (lem-T312-beta-at0310243241 c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (Sw01 ∷ Bx3-0421 ∷ []) (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (Sw01 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 (lit c4))

-- T312-beta @03243240: 8 steps
lem-T312-beta-at03243240 : Ws → ⟪ (Toff214 ∷ Bx3-1420 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ CCZ014 ∷ []) ⟫ʷ
lem-T312-beta-at03243240 c4 = derive (Toff214 ∷ Bx3-1420 ∷ Toff214 ∷ []) (Bx3-1420 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q61 c4) ∷
   rw 1 (q73 c4) ∷
   rw 2 (q62 c4) ∷
   rw 3 (q73 c4) ∷
   rw 1 (q74 c4) ∷
   rw 0 (q75 c4) ∷
   rw 1 (q76 c4) ∷
   rw 2 (q61 c4) ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q78 : Ws → Eqn
  q78 c4 = eqn (Sw23 ∷ Bx3-0412 ∷ []) (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4))
  q79 : Ws → Eqn
  q79 c4 = eqn (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 (lit c4))
  q80 : Ws → Eqn
  q80 c4 = eqn (Bx2-0413 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0210243143 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4))
  q82 : Ws → Eqn
  q82 c4 = eqn (Sw23 ∷ Bx2-0413 ∷ []) (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4))

-- auto BOX(0;1234) | CCZ124 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0310243142 c4 = derive (Bx3-0412 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0412 ∷ [])
  (rw⁻ 0 (q77 c4) ∷
   rw 1 (q78 c4) ∷
   rw 2 (q79 c4) ∷
   rw 1 (q80 c4) ∷
   rw 0 (q81 c4) ∷
   rw 1 (q82 c4) ∷
   rw 2 (q77 c4) ∷ []) Eq.refl

private
  q83 : Ws → Eqn
  q83 c4 = eqn (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4))
  q84 : Ws → Eqn
  q84 c4 = eqn (Bx3-0412 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0310243142 c4)

-- auto BOX(0;1234) | CCZ124 @0310243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx3-0421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0310243241 c4 = derive (Bx3-0421 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx3-0421 ∷ [])
  (rw⁻ 0 (q59 c4) ∷
   rw 1 (q60 c4) ∷
   rw 2 (q83 c4) ∷
   rw 1 (q84 c4) ∷
   rw 0 (q72 c4) ∷
   rw 1 (q71 c4) ∷
   rw 2 (q59 c4) ∷ []) Eq.refl

private
  q85 : Ws → Eqn
  q85 c4 = eqn (Bx3-0421 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx3-0421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0310243241 c4)

-- auto BOX(0;1234) | CCZ124 @03243240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 : Ws → ⟪ (Bx3-1420 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 c4 = derive (Bx3-1420 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx3-1420 ∷ [])
  (rw⁻ 0 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   rw 2 (q76 c4) ∷
   rw 1 (q85 c4) ∷
   rw 0 (q76 c4) ∷
   rw 1 (q75 c4) ∷
   rw 2 (q61 c4) ∷ []) Eq.refl

private
  q86 : Ws → Eqn
  q86 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 (lit c4))
  q87 : Ws → Eqn
  q87 c4 = eqn (Sw34 ∷ Bx0-1423 ∷ []) (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4))
  q88 : Ws → Eqn
  q88 c4 = eqn (CCZ234 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ234 ∷ []) (wl0155 (lit c4))
  q89 : Ws → Eqn
  q89 c4 = eqn (Bx0-1324 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at2332 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (Sw34 ∷ Bx0-1324 ∷ []) (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4))

-- auto BOX(0;1234) | CCZ234 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at243243 : Ws → ⟪ (Bx0-1423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at243243 c4 = derive (Bx0-1423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q86 c4) ∷
   rw 1 (q87 c4) ∷
   rw⁻ 2 (q88 c4) ∷
   rw 1 (q89 c4) ∷
   rw⁻ 0 (q88 c4) ∷
   rw 1 (q90 c4) ∷
   rw 2 (q86 c4) ∷ []) Eq.refl

private
  q91 : Ws → Eqn
  q91 c4 = eqn (Sw01 ∷ Bx1-0423 ∷ []) (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4))
  q92 : Ws → Eqn
  q92 c4 = eqn (Sw01 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ))
  q93 : Ws → Eqn
  q93 c4 = eqn (Bx0-1423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at243243 c4)
  q94 : Ws → Eqn
  q94 c4 = eqn (Sw01 ∷ Bx0-1423 ∷ []) (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4))

-- auto BOX(0;1234) | CCZ234 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at0110243243 c4 = derive (Bx1-0423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q61 c4) ∷
   rw 1 (q91 c4) ∷
   rw 2 (q92 c4) ∷
   rw 1 (q93 c4) ∷
   rw 0 (q92 c4) ∷
   rw 1 (q94 c4) ∷
   rw 2 (q61 c4) ∷ []) Eq.refl

private
  q95 : Ws → Eqn
  q95 c4 = eqn (Sw12 ∷ Bx2-0413 ∷ []) (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4))
  q96 : Ws → Eqn
  q96 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl0084 (lit c4))
  q97 : Ws → Eqn
  q97 c4 = eqn (Bx1-0423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at0110243243 c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 (lit c4))
  q99 : Ws → Eqn
  q99 c4 = eqn (Sw12 ∷ Bx1-0423 ∷ []) (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4))

-- auto BOX(0;1234) | CCZ234 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at0210243143 c4 = derive (Bx2-0413 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q59 c4) ∷
   rw 1 (q95 c4) ∷
   rw⁻ 2 (q96 c4) ∷
   rw 1 (q97 c4) ∷
   rw⁻ 0 (q98 c4) ∷
   rw 1 (q99 c4) ∷
   rw 2 (q59 c4) ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = eqn (Sw23 ∷ CCZ124 ∷ []) (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4))
  q101 : Ws → Eqn
  q101 c4 = eqn (Bx2-0413 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at0210243143 c4)
  q102 : Ws → Eqn
  q102 c4 = eqn (Sw23 ∷ CCZ134 ∷ []) (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4))

-- auto BOX(0;1234) | CCZ234 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at0310243142 c4 = derive (Bx3-0412 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-0412 ∷ [])
  (rw⁻ 0 (q77 c4) ∷
   rw 1 (q78 c4) ∷
   rw 2 (q100 c4) ∷
   rw 1 (q101 c4) ∷
   rw 0 (q102 c4) ∷
   rw 1 (q82 c4) ∷
   rw 2 (q77 c4) ∷ []) Eq.refl

private
  q103 : Ws → Eqn
  q103 c4 = eqn (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) (wl0078 (lit c4))
  q104 : Ws → Eqn
  q104 c4 = eqn (Bx3-0412 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at0310243142 c4)

-- auto BOX(0;1234) | CCZ234 @0310243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx3-0421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at0310243241 c4 = derive (Bx3-0421 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-0421 ∷ [])
  (rw⁻ 0 (q59 c4) ∷
   rw 1 (q60 c4) ∷
   rw⁻ 2 (q103 c4) ∷
   rw 1 (q104 c4) ∷
   rw⁻ 0 (q103 c4) ∷
   rw 1 (q71 c4) ∷
   rw 2 (q59 c4) ∷ []) Eq.refl

private
  q105 : Ws → Eqn
  q105 c4 = eqn (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4))
  q106 : Ws → Eqn
  q106 c4 = eqn (Bx3-0421 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-0421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at0310243241 c4)
  q107 : Ws → Eqn
  q107 c4 = eqn (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4))

-- auto BOX(0;1234) | CCZ234 @03243240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at03243240 : Ws → ⟪ (Bx3-1420 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at03243240 c4 = derive (Bx3-1420 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-1420 ∷ [])
  (rw⁻ 0 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   rw 2 (q105 c4) ∷
   rw 1 (q106 c4) ∷
   rw 0 (q107 c4) ∷
   rw 1 (q75 c4) ∷
   rw 2 (q61 c4) ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = eqn (CCZ134 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ134 ∷ []) (wl0154 (lit c4))
  q109 : Ws → Eqn
  q109 c4 = eqn (Bx0-1324 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at2332 c4)

-- auto BOX(0;1234) | CCZ214 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at243243 : Ws → ⟪ (Bx0-1423 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at243243 c4 = derive (Bx0-1423 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q86 c4) ∷
   rw 1 (q87 c4) ∷
   rw⁻ 2 (q108 c4) ∷
   rw 1 (q109 c4) ∷
   rw⁻ 0 (q108 c4) ∷
   rw 1 (q90 c4) ∷
   rw 2 (q86 c4) ∷ []) Eq.refl

private
  q110 : Ws → Eqn
  q110 c4 = eqn (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 (lit c4))
  q111 : Ws → Eqn
  q111 c4 = eqn (Bx0-1423 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at243243 c4)
  q112 : Ws → Eqn
  q112 c4 = eqn (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4))

-- auto BOX(0;1234) | CCZ214 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at0110243243 c4 = derive (Bx1-0423 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q61 c4) ∷
   rw 1 (q91 c4) ∷
   rw 2 (q110 c4) ∷
   rw 1 (q111 c4) ∷
   rw 0 (q112 c4) ∷
   rw 1 (q94 c4) ∷
   rw 2 (q61 c4) ∷ []) Eq.refl

private
  q113 : Ws → Eqn
  q113 c4 = eqn (Sw12 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4))
  q114 : Ws → Eqn
  q114 c4 = eqn (Bx1-0423 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at0110243243 c4)

-- auto BOX(0;1234) | CCZ214 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at0210243143 c4 = derive (Bx2-0413 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q59 c4) ∷
   rw 1 (q95 c4) ∷
   rw 2 (q113 c4) ∷
   rw 1 (q114 c4) ∷
   rw 0 (q113 c4) ∷
   rw 1 (q99 c4) ∷
   rw 2 (q59 c4) ∷ []) Eq.refl

private
  q115 : Ws → Eqn
  q115 c4 = eqn (Bx2-0413 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at0210243143 c4)

-- auto BOX(0;1234) | CCZ214 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at0310243142 c4 = derive (Bx3-0412 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0412 ∷ [])
  (rw⁻ 0 (q77 c4) ∷
   rw 1 (q78 c4) ∷
   rw 2 (q79 c4) ∷
   rw 1 (q115 c4) ∷
   rw 0 (q81 c4) ∷
   rw 1 (q82 c4) ∷
   rw 2 (q77 c4) ∷ []) Eq.refl

private
  q116 : Ws → Eqn
  q116 c4 = eqn (Bx3-0412 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at0310243142 c4)

-- auto BOX(0;1234) | CCZ214 @0310243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx3-0421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at0310243241 c4 = derive (Bx3-0421 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx3-0421 ∷ [])
  (rw⁻ 0 (q59 c4) ∷
   rw 1 (q60 c4) ∷
   rw 2 (q83 c4) ∷
   rw 1 (q116 c4) ∷
   rw 0 (q72 c4) ∷
   rw 1 (q71 c4) ∷
   rw 2 (q59 c4) ∷ []) Eq.refl

private
  q117 : Ws → Eqn
  q117 c4 = eqn (Bx3-0421 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx3-0421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at0310243241 c4)

-- auto BOX(0;1234) | CCZ214 @03243240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at03243240 : Ws → ⟪ (Bx3-1420 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at03243240 c4 = derive (Bx3-1420 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx3-1420 ∷ [])
  (rw⁻ 0 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   rw 2 (q76 c4) ∷
   rw 1 (q117 c4) ∷
   rw 0 (q76 c4) ∷
   rw 1 (q75 c4) ∷
   rw 2 (q61 c4) ∷ []) Eq.refl

private
  q118 : Ws → Eqn
  q118 c4 = eqn (Sw23 ∷ Bx0-1324 ∷ []) (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4))
  q119 : Ws → Eqn
  q119 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0011 (lit c4))
  q120 : Ws → Eqn
  q120 c4 = eqn (Bx0-1234 ∷ CS34 ∷ []) (CS34 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS43 c4)
  q121 : Ws → Eqn
  q121 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0015 (lit c4))
  q122 : Ws → Eqn
  q122 c4 = eqn (Sw23 ∷ Bx0-1234 ∷ []) (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4))

-- auto BOX(0;1234) | CS43 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS43-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS43-at2332 c4 = derive (Bx0-1324 ∷ CS24 ∷ []) (CS24 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q77 c4) ∷
   rw 1 (q118 c4) ∷
   rw⁻ 2 (q119 c4) ∷
   rw 1 (q120 c4) ∷
   rw⁻ 0 (q121 c4) ∷
   rw 1 (q122 c4) ∷
   rw 2 (q77 c4) ∷ []) Eq.refl

private
  q123 : Ws → Eqn
  q123 c4 = eqn (Sw34 ∷ CS23 ∷ []) (CS24 ∷ Sw34 ∷ []) (lem-nat-3-CS23 (lit c4))
  q124 : Ws → Eqn
  q124 c4 = eqn (Bx0-1324 ∷ CS24 ∷ []) (CS24 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS43-at2332 c4)
  q125 : Ws → Eqn
  q125 c4 = eqn (Sw34 ∷ CS24 ∷ []) (CS23 ∷ Sw34 ∷ []) (lem-nat-3-CS24 (lit c4))

-- auto BOX(0;1234) | CS43 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS43-at243243 : Ws → ⟪ (Bx0-1423 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS43-at243243 c4 = derive (Bx0-1423 ∷ CS23 ∷ []) (CS23 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q86 c4) ∷
   rw 1 (q87 c4) ∷
   rw 2 (q123 c4) ∷
   rw 1 (q124 c4) ∷
   rw 0 (q125 c4) ∷
   rw 1 (q90 c4) ∷
   rw 2 (q86 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (c₂ (Swap) (CS))
  q127 : Ws → Eqn
  q127 c4 = eqn (Bx0-1423 ∷ CS23 ∷ []) (CS23 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS43-at243243 c4)

-- auto BOX(0;1234) | CS43 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS43-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS43-at0110243243 c4 = derive (Bx1-0423 ∷ CS23 ∷ []) (CS23 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q61 c4) ∷
   rw 1 (q91 c4) ∷
   rw 2 (q126 c4) ∷
   rw 1 (q127 c4) ∷
   rw 0 (q126 c4) ∷
   rw 1 (q94 c4) ∷
   rw 2 (q61 c4) ∷ []) Eq.refl

private
  q128 : Ws → Eqn
  q128 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl0025 (lit c4))
  q129 : Ws → Eqn
  q129 c4 = eqn (Bx1-0423 ∷ CS23 ∷ []) (CS23 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS43-at0110243243 c4)
  q130 : Ws → Eqn
  q130 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl0024 (lit c4))

-- auto BOX(0;1234) | CS43 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS43-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS43-at0210243143 c4 = derive (Bx2-0413 ∷ CS13 ∷ []) (CS13 ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q59 c4) ∷
   rw 1 (q95 c4) ∷
   rw⁻ 2 (q128 c4) ∷
   rw 1 (q129 c4) ∷
   rw⁻ 0 (q130 c4) ∷
   rw 1 (q99 c4) ∷
   rw 2 (q59 c4) ∷ []) Eq.refl

private
  q131 : Ws → Eqn
  q131 c4 = eqn (Sw23 ∷ CS12 ∷ []) (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 (lit c4))
  q132 : Ws → Eqn
  q132 c4 = eqn (Bx2-0413 ∷ CS13 ∷ []) (CS13 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS43-at0210243143 c4)
  q133 : Ws → Eqn
  q133 c4 = eqn (Sw23 ∷ CS13 ∷ []) (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 (lit c4))

-- auto BOX(0;1234) | CS43 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS43-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS43-at0310243142 c4 = derive (Bx3-0412 ∷ CS12 ∷ []) (CS12 ∷ Bx3-0412 ∷ [])
  (rw⁻ 0 (q77 c4) ∷
   rw 1 (q78 c4) ∷
   rw 2 (q131 c4) ∷
   rw 1 (q132 c4) ∷
   rw 0 (q133 c4) ∷
   rw 1 (q82 c4) ∷
   rw 2 (q77 c4) ∷ []) Eq.refl

private
  q134 : Ws → Eqn
  q134 c4 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wl0134 (lit c4))
  q135 : Ws → Eqn
  q135 c4 = eqn (Bx3-0412 ∷ CS12 ∷ []) (CS12 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS43-at0310243142 c4)

-- auto BOX(0;1234) | CS43 @0310243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS43-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Bx3-0421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS43-at0310243241 c4 = derive (Bx3-0421 ∷ CS12 ∷ []) (CS12 ∷ Bx3-0421 ∷ [])
  (rw⁻ 0 (q59 c4) ∷
   rw 1 (q60 c4) ∷
   rw⁻ 2 (q134 c4) ∷
   rw 1 (q135 c4) ∷
   rw⁻ 0 (q134 c4) ∷
   rw 1 (q71 c4) ∷
   rw 2 (q59 c4) ∷ []) Eq.refl

private
  q136 : Ws → Eqn
  q136 c4 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wl0138 (lit c4))
  q137 : Ws → Eqn
  q137 c4 = eqn (Bx3-0421 ∷ CS12 ∷ []) (CS12 ∷ Bx3-0421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS43-at0310243241 c4)
  q138 : Ws → Eqn
  q138 c4 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wl0035 (lit c4))

-- auto BOX(0;1234) | CS43 @03243240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS43-at03243240 : Ws → ⟪ (Bx3-1420 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS43-at03243240 c4 = derive (Bx3-1420 ∷ CS02 ∷ []) (CS02 ∷ Bx3-1420 ∷ [])
  (rw⁻ 0 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   rw⁻ 2 (q136 c4) ∷
   rw 1 (q137 c4) ∷
   rw⁻ 0 (q138 c4) ∷
   rw 1 (q75 c4) ∷
   rw 2 (q61 c4) ∷ []) Eq.refl

private
  q139 : Ws → Eqn
  q139 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl0012 (lit c4))
  q140 : Ws → Eqn
  q140 c4 = eqn (Bx0-1234 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd43 c4)
  q141 : Ws → Eqn
  q141 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl0016 (lit c4))

-- auto BOX(0;1234) | CSd43 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd43-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd43-at2332 c4 = derive (Bx0-1324 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q77 c4) ∷
   rw 1 (q118 c4) ∷
   rw⁻ 2 (q139 c4) ∷
   rw 1 (q140 c4) ∷
   rw⁻ 0 (q141 c4) ∷
   rw 1 (q122 c4) ∷
   rw 2 (q77 c4) ∷ []) Eq.refl

private
  q142 : Ws → Eqn
  q142 c4 = eqn (Sw34 ∷ CS23⁻ ∷ []) (CS24⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd23 (lit c4))
  q143 : Ws → Eqn
  q143 c4 = eqn (Bx0-1324 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd43-at2332 c4)
  q144 : Ws → Eqn
  q144 c4 = eqn (Sw34 ∷ CS24⁻ ∷ []) (CS23⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd24 (lit c4))

-- auto BOX(0;1234) | CSd43 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd43-at243243 : Ws → ⟪ (Bx0-1423 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd43-at243243 c4 = derive (Bx0-1423 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q86 c4) ∷
   rw 1 (q87 c4) ∷
   rw 2 (q142 c4) ∷
   rw 1 (q143 c4) ∷
   rw 0 (q144 c4) ∷
   rw 1 (q90 c4) ∷
   rw 2 (q86 c4) ∷ []) Eq.refl

private
  q145 : Ws → Eqn
  q145 c4 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (CS • CS • CS))
  q146 : Ws → Eqn
  q146 c4 = eqn (Bx0-1423 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd43-at243243 c4)

-- auto BOX(0;1234) | CSd43 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd43-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd43-at0110243243 c4 = derive (Bx1-0423 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q61 c4) ∷
   rw 1 (q91 c4) ∷
   rw 2 (q145 c4) ∷
   rw 1 (q146 c4) ∷
   rw 0 (q145 c4) ∷
   rw 1 (q94 c4) ∷
   rw 2 (q61 c4) ∷ []) Eq.refl

private
  q147 : Ws → Eqn
  q147 c4 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wl0046 (lit c4))
  q148 : Ws → Eqn
  q148 c4 = eqn (Bx1-0423 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd43-at0110243243 c4)
  q149 : Ws → Eqn
  q149 c4 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wl0043 (lit c4))

-- auto BOX(0;1234) | CSd43 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd43-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd43-at0210243143 c4 = derive (Bx2-0413 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q59 c4) ∷
   rw 1 (q95 c4) ∷
   rw⁻ 2 (q147 c4) ∷
   rw 1 (q148 c4) ∷
   rw⁻ 0 (q149 c4) ∷
   rw 1 (q99 c4) ∷
   rw 2 (q59 c4) ∷ []) Eq.refl

private
  q150 : Ws → Eqn
  q150 c4 = eqn (Sw23 ∷ CS12⁻ ∷ []) (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 (lit c4))
  q151 : Ws → Eqn
  q151 c4 = eqn (Bx2-0413 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd43-at0210243143 c4)
  q152 : Ws → Eqn
  q152 c4 = eqn (Sw23 ∷ CS13⁻ ∷ []) (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 (lit c4))

-- auto BOX(0;1234) | CSd43 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd43-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd43-at0310243142 c4 = derive (Bx3-0412 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Bx3-0412 ∷ [])
  (rw⁻ 0 (q77 c4) ∷
   rw 1 (q78 c4) ∷
   rw 2 (q150 c4) ∷
   rw 1 (q151 c4) ∷
   rw 0 (q152 c4) ∷
   rw 1 (q82 c4) ∷
   rw 2 (q77 c4) ∷ []) Eq.refl

private
  q153 : Ws → Eqn
  q153 c4 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wl0135 (lit c4))
  q154 : Ws → Eqn
  q154 c4 = eqn (Bx3-0412 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd43-at0310243142 c4)

-- auto BOX(0;1234) | CSd43 @0310243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd43-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Bx3-0421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd43-at0310243241 c4 = derive (Bx3-0421 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Bx3-0421 ∷ [])
  (rw⁻ 0 (q59 c4) ∷
   rw 1 (q60 c4) ∷
   rw⁻ 2 (q153 c4) ∷
   rw 1 (q154 c4) ∷
   rw⁻ 0 (q153 c4) ∷
   rw 1 (q71 c4) ∷
   rw 2 (q59 c4) ∷ []) Eq.refl

private
  q155 : Ws → Eqn
  q155 c4 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wl0139 (lit c4))
  q156 : Ws → Eqn
  q156 c4 = eqn (Bx3-0421 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Bx3-0421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd43-at0310243241 c4)
  q157 : Ws → Eqn
  q157 c4 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wl0036 (lit c4))

-- auto BOX(0;1234) | CSd43 @03243240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd43-at03243240 : Ws → ⟪ (Bx3-1420 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd43-at03243240 c4 = derive (Bx3-1420 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx3-1420 ∷ [])
  (rw⁻ 0 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   rw⁻ 2 (q155 c4) ∷
   rw 1 (q156 c4) ∷
   rw⁻ 0 (q157 c4) ∷
   rw 1 (q75 c4) ∷
   rw 2 (q61 c4) ∷ []) Eq.refl

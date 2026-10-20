{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D164 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0034 ; wl0063 ; wl0078 ; wl0084 ; wl0086 ; wl0127 ; wl0136 ; wl0140 ; wl0144 ; wl0155 ; wl0230 ; wl0242 ; wl0244 ; wl0248 ; wl0265 ; wl0267 ; wl0351 ; wl0614 ; wl0615 ; wl0616 ; wl0617 ; wl0618 ; wl0619 ; wl0620 ; wl0621 ; wl0622 ; wl0623 ; wl0624 ; wp0025 ; wp0034 ; wp0055 ; wp0064 ; wp0263 ; wp0265 ; wp0268 ; wp0276 ; wp0277 ; wp0278 ; wp0279 ; wp0281 ; wp0282 ; wp0283 ; wp0284 ; wp0285)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0 ; lem-T-beta ; lem-T312-beta ; lem-T312-beta-at0314203142 ; lem-T312-beta-at0314213240 ; lem-beta-T-at0314213042 ; lem-beta-inv-at0310243142 ; lem-sym12 ; lem-sym12-at0110 ; lem-sym12-at011220 ; lem-sym12-at0314203142 ; lem-sym12-at1221 ; lem-sym12-at132132 ; lem-sym23 ; lem-sym23-at0314203142 ; lem-sym23-at0314213042 ; lem-sym23-at1221 ; lem-sym34 ; lem-sym34-at03102132 ; lem-sym34-at0310213442 ; lem-sym34-at0314213042 ; lem-sym34-at0314213240 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-Cz-beta-at13243142 ; lem-Cz-beta-at2332 ; lem-Cz-beta-at243243 ; lem-T312-beta-at122331 ; lem-TW ; lem-auto-BOX⟨0·1234⟩-∣-CCZ234 ; lem-beta-T-at0330 ; lem-sym12-at03102132 ; lem-sym12-at233442 ; lem-sym23-at011220 ; lem-sym23-at01122330 ; lem-sym23-at03102132 ; lem-sym23-at0310213442 ; lem-sym23-at0310243142 ; lem-sym23-at122331 ; lem-sym23-at13213442 ; lem-sym23-at13243142 ; lem-sym23-at2332 ; lem-sym23-at243243 ; lem-sym23-at3443 ; lem-sym34-at13213442 ; lem-sym34-at2332 ; lem-sym34-at233442)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ124 ; lem-sym23-at02102331)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-beta-T-at01122330 ; lem-sym12-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-sym12-at0210213443 ; lem-sym23-at233442 ; lem-sym23-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D089 using (lem-sym12-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-sym23-at0213243041 ; lem-sym34-at0213203441)
open import Examples.Groups.Clifford+CS.Five.D.D160 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ142)
open import Examples.Groups.Clifford+CS.Five.D.D161 using (lem-F0-at011220 ; lem-T312-beta-at03143041 ; lem-T312-beta-at03143140 ; lem-T312-beta-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at03243240 ; lem-auto-CCZ012-∣-CCZ342 ; lem-auto-CCZ012-∣-CCZ342-at03102132 ; lem-sym12-at0314213240 ; lem-sym12-at03243240 ; lem-sym23-at0314213240 ; lem-sym23-at03143140 ; lem-sym34-at03143041 ; lem-sym34-at03143140)
open import Examples.Groups.Clifford+CS.Five.D.D162 using (lem-T312-beta-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CS43-at03243240 ; lem-auto-BOX⟨0·1234⟩-∣-CSd43-at03243240 ; lem-beta-inv-at03243240)
open import Examples.Groups.Clifford+CS.Five.D.D163 using (lem-boxify-2-nf-of-rhs)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-BOX⟨0·3412⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF034 ; lem-nat-2-TOFF103 ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-CCZ014 ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF014 ; lem-nat-3-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·1423⟩ ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-2-BOX⟨0·2413⟩ ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF304 ; lem-nat-3-BOX⟨0·1324⟩ ; lem-nat-3-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ014 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF314 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-1-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-1-BOX⟨3·0124⟩ ; lem-nat-1-BOX⟨3·0214⟩ ; lem-nat-2-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0124⟩ ; lem-nat-2-BOX⟨3·0142⟩ ; lem-nat-2-BOX⟨3·0412⟩)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨3·1024⟩ ; lem-nat-1-BOX⟨0·2314⟩ ; lem-nat-2-TOFF314)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-TOFF134 ; lem-nat-2-BOX⟨0·1432⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-TOFF034 ; lem-nat-2-BOX⟨1·0234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-2-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-BOX⟨3·0142⟩ ; lem-nat-1-BOX⟨3·0241⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-BOX⟨0·3412⟩ ; lem-nat-0-BOX⟨1·3402⟩ ; lem-nat-0-BOX⟨3·0412⟩ ; lem-nat-1-BOX⟨1·3402⟩ ; lem-nat-1-BOX⟨2·3401⟩ ; lem-nat-1-BOX⟨3·1402⟩ ; lem-nat-2-BOX⟨3·2401⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-2-BOX⟨1·0324⟩ ; lem-nat-3-BOX⟨1·0324⟩ ; lem-nat-3-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨3·0124⟩ ; lem-nat-0-BOX⟨3·0142⟩ ; lem-nat-0-BOX⟨3·1042⟩ ; lem-nat-0-BOX⟨3·1402⟩ ; lem-nat-1-BOX⟨3·1024⟩ ; lem-nat-1-BOX⟨3·1042⟩ ; lem-nat-1-BOX⟨3·2014⟩ ; lem-nat-1-BOX⟨3·2041⟩ ; lem-nat-1-BOX⟨3·2401⟩ ; lem-nat-2-BOX⟨2·1043⟩ ; lem-nat-2-BOX⟨2·3401⟩)

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
  q53 c4 = eqn (Bx3-0124 ∷ []) (Bx3-0124 ∷ []) (lem-boxify-2-nf-of-rhs c4)

-- boxify-2: 334 steps
lem-boxify-2 : Ws → ⟪ (Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-boxify-2 c4 = derive (Sb0-1-42-3 ∷ Toff104 ∷ CCZ124 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-0124 ∷ [])
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
  q55 c4 = eqn (Sw23 ∷ Toff013 ∷ []) (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (Sw23 ∷ Bx0-1324 ∷ []) (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (Toff012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Toff012 ∷ []) (lem-T-beta c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (Sw23 ∷ Bx0-1234 ∷ []) (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (Sw23 ∷ Toff012 ∷ []) (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4))

-- T-beta @2332: 7 steps
lem-T-beta-at2332 : Ws → ⟪ (Toff013 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ Toff013 ∷ []) ⟫ʷ
lem-T-beta-at2332 c4 = derive (Toff013 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ Toff013 ∷ [])
  (rw⁻ 0 (q54 c4) ∷
   rw 1 (q55 c4) ∷
   rw 2 (q56 c4) ∷
   rw 1 (q57 c4) ∷
   rw 0 (q58 c4) ∷
   rw 1 (q59 c4) ∷
   rw 2 (q54 c4) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (Sw34 ∷ Toff014 ∷ []) (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (Sw34 ∷ Bx0-1423 ∷ []) (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (Toff013 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ Toff013 ∷ []) (lem-T-beta-at2332 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (Sw34 ∷ Bx0-1324 ∷ []) (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (Sw34 ∷ Toff013 ∷ []) (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 (lit c4))

-- T-beta @243243: 7 steps
lem-T-beta-at243243 : Ws → ⟪ (Toff014 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Toff014 ∷ []) ⟫ʷ
lem-T-beta-at243243 c4 = derive (Toff014 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Toff014 ∷ [])
  (rw⁻ 0 (q60 c4) ∷
   rw 1 (q61 c4) ∷
   rw 2 (q62 c4) ∷
   rw 1 (q63 c4) ∷
   rw 0 (q64 c4) ∷
   rw 1 (q65 c4) ∷
   rw 2 (q60 c4) ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (Sw12 ∷ Toff024 ∷ []) (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (Sw12 ∷ Bx0-2413 ∷ []) (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (Toff014 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Toff014 ∷ []) (lem-T-beta-at243243 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (Sw12 ∷ Bx0-1423 ∷ []) (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (Sw12 ∷ Toff014 ∷ []) (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 (lit c4))

-- T-beta @12243143: 7 steps
lem-T-beta-at12243143 : Ws → ⟪ (Toff024 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Toff024 ∷ []) ⟫ʷ
lem-T-beta-at12243143 c4 = derive (Toff024 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ Toff024 ∷ [])
  (rw⁻ 0 (q66 c4) ∷
   rw 1 (q67 c4) ∷
   rw 2 (q68 c4) ∷
   rw 1 (q69 c4) ∷
   rw 0 (q70 c4) ∷
   rw 1 (q71 c4) ∷
   rw 2 (q66 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = eqn (Sw23 ∷ Toff034 ∷ []) (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 (lit c4))
  q73 : Ws → Eqn
  q73 c4 = eqn (Sw23 ∷ Bx0-3412 ∷ []) (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (Toff024 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ Toff024 ∷ []) (lem-T-beta-at12243143 c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (Sw23 ∷ Bx0-2413 ∷ []) (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (Sw23 ∷ Toff024 ∷ []) (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 (lit c4))

-- T-beta @13243142: 7 steps
lem-T-beta-at13243142 : Ws → ⟪ (Toff034 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Toff034 ∷ []) ⟫ʷ
lem-T-beta-at13243142 c4 = derive (Toff034 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ Toff034 ∷ [])
  (rw⁻ 0 (q54 c4) ∷
   rw 1 (q72 c4) ∷
   rw 2 (q73 c4) ∷
   rw 1 (q74 c4) ∷
   rw 0 (q75 c4) ∷
   rw 1 (q76 c4) ∷
   rw 2 (q54 c4) ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = eqn (Toff034 ∷ []) (Toff034 ∷ []) (wp0284 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1324 ∷ []) (lem-sym23 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (Bx0-1324 ∷ []) (Bx0-1342 ∷ []) (lem-sym34-at2332 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (Bx0-1342 ∷ []) (Bx0-3142 ∷ []) (lem-sym12-at233442 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (Bx0-3142 ∷ []) (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (Toff034 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ Toff034 ∷ []) (lem-T-beta-at13243142 c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (Bx0-3412 ∷ []) (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (Bx0-3142 ∷ []) (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (Bx0-3124 ∷ []) (Bx0-1324 ∷ []) (lem-sym12-at132132 c4)
  q86 : Ws → Eqn
  q86 c4 = eqn (Bx0-1324 ∷ []) (Bx0-1234 ∷ []) (lem-sym23-at2332 c4)

-- auto BOX(0;1234) | TOFF043: 11 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF043 : Ws → ⟪ (Bx0-1234 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF043 c4 = derive (Bx0-1234 ∷ Toff034 ∷ []) (Toff034 ∷ Bx0-1234 ∷ [])
  (rw 1 (q77 c4) ∷
   rw 0 (q78 c4) ∷
   rw 0 (q79 c4) ∷
   rw 0 (q80 c4) ∷
   rw 0 (q81 c4) ∷
   rw⁻ 0 (q82 c4) ∷
   rw 1 (q83 c4) ∷
   rw 1 (q84 c4) ∷
   rw 1 (q85 c4) ∷
   rw 1 (q86 c4) ∷
   rw 0 (q77 c4) ∷ []) Eq.refl

-- boxify-3 [nf of rhs]: 0 steps
lem-boxify-3-nf-of-rhs : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-boxify-3-nf-of-rhs c4 = refl

private
  q87 : Ws → Eqn
  q87 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q88 : Ws → Eqn
  q88 c4 = eqn (Sw01 ∷ Bx1-0234 ∷ []) (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4))
  q89 : Ws → Eqn
  q89 c4 = eqn (Sw01 ∷ Toff134 ∷ []) (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 (lit c4))
  q90 : Ws → Eqn
  q90 c4 = eqn (Bx0-1234 ∷ Toff034 ∷ []) (Toff034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF043 c4)
  q91 : Ws → Eqn
  q91 c4 = eqn (Sw01 ∷ Toff034 ∷ []) (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 (lit c4))
  q92 : Ws → Eqn
  q92 c4 = eqn (Sw01 ∷ Bx0-1234 ∷ []) (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4))

-- auto BOX(0;1234) | TOFF043 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at0110 : Ws → ⟪ (Bx1-0234 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at0110 c4 = derive (Bx1-0234 ∷ Toff134 ∷ []) (Toff134 ∷ Bx1-0234 ∷ [])
  (rw⁻ 0 (q87 c4) ∷
   rw 1 (q88 c4) ∷
   rw 2 (q89 c4) ∷
   rw 1 (q90 c4) ∷
   rw 0 (q91 c4) ∷
   rw 1 (q92 c4) ∷
   rw 2 (q87 c4) ∷ []) Eq.refl

private
  q93 : Ws → Eqn
  q93 c4 = eqn (Sw12 ∷ Bx2-0134 ∷ []) (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4))
  q94 : Ws → Eqn
  q94 c4 = eqn (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) (wl0140 (lit c4))
  q95 : Ws → Eqn
  q95 c4 = eqn (Bx1-0234 ∷ Toff134 ∷ []) (Toff134 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at0110 c4)
  q96 : Ws → Eqn
  q96 c4 = eqn (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) (wl0136 (lit c4))
  q97 : Ws → Eqn
  q97 c4 = eqn (Sw12 ∷ Bx1-0234 ∷ []) (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4))

-- auto BOX(0;1234) | TOFF043 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at021021 : Ws → ⟪ (Bx2-0134 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at021021 c4 = derive (Bx2-0134 ∷ Toff234 ∷ []) (Toff234 ∷ Bx2-0134 ∷ [])
  (rw⁻ 0 (q66 c4) ∷
   rw 1 (q93 c4) ∷
   rw 2 (q94 c4) ∷
   rw 1 (q95 c4) ∷
   rw 0 (q96 c4) ∷
   rw 1 (q97 c4) ∷
   rw 2 (q66 c4) ∷ []) Eq.refl

private
  q98 : Ws → Eqn
  q98 c4 = eqn (Sw23 ∷ Bx3-0124 ∷ []) (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ (lit c4))
  q99 : Ws → Eqn
  q99 c4 = eqn (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) (wl0144 (lit c4))
  q100 : Ws → Eqn
  q100 c4 = eqn (Bx2-0134 ∷ Toff234 ∷ []) (Toff234 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at021021 c4)
  q101 : Ws → Eqn
  q101 c4 = eqn (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) (wl0127 (lit c4))
  q102 : Ws → Eqn
  q102 c4 = eqn (Sw23 ∷ Bx2-0134 ∷ []) (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ (lit c4))

-- auto BOX(0;1234) | TOFF043 @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at03102132 : Ws → ⟪ (Bx3-0124 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at03102132 c4 = derive (Bx3-0124 ∷ Toff324 ∷ []) (Toff324 ∷ Bx3-0124 ∷ [])
  (rw⁻ 0 (q54 c4) ∷
   rw 1 (q98 c4) ∷
   rw 2 (q99 c4) ∷
   rw 1 (q100 c4) ∷
   rw 0 (q101 c4) ∷
   rw 1 (q102 c4) ∷
   rw 2 (q54 c4) ∷ []) Eq.refl

private
  q103 : Ws → Eqn
  q103 c4 = eqn (Bx3-0124 ∷ Toff324 ∷ []) (Toff324 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at03102132 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (Toff324 ∷ Toff324 ∷ []) [] (wl0616 (lit c4))
  q105 : Ws → Eqn
  q105 c4 = eqn (Bx3-0124 ∷ []) (Bx3-0124 ∷ []) (lem-boxify-3-nf-of-rhs c4)

-- boxify-3: 3 steps
lem-boxify-3 : Ws → ⟪ (Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-boxify-3 c4 = derive (Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ []) (Bx3-0124 ∷ [])
  (rw 1 (q103 c4) ∷
   rw 0 (q104 c4) ∷
   rw⁻ 0 (q105 c4) ∷ []) Eq.refl

private
  q106 : Ws → Eqn
  q106 c4 = eqn (CCZ034 ∷ []) (CCZ034 ∷ []) (wp0025 c4)
  q107 : Ws → Eqn
  q107 c4 = eqn (CCZ034 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ CCZ034 ∷ []) (lem-Cz-beta-at13243142 c4)

-- auto BOX(0;1234) | CCZ304: 11 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ304 : Ws → ⟪ (Bx0-1234 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ304 c4 = derive (Bx0-1234 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx0-1234 ∷ [])
  (rw 1 (q106 c4) ∷
   rw 0 (q78 c4) ∷
   rw 0 (q79 c4) ∷
   rw 0 (q80 c4) ∷
   rw 0 (q81 c4) ∷
   rw⁻ 0 (q107 c4) ∷
   rw 1 (q83 c4) ∷
   rw 1 (q84 c4) ∷
   rw 1 (q85 c4) ∷
   rw 1 (q86 c4) ∷
   rw 0 (q106 c4) ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = eqn (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4))
  q109 : Ws → Eqn
  q109 c4 = eqn (Sw12 ∷ Bx0-2314 ∷ []) (Bx0-1324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2314⟩ (lit c4))
  q110 : Ws → Eqn
  q110 c4 = eqn (CCZ013 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CCZ013 ∷ []) (lem-Cz-beta-at2332 c4)
  q111 : Ws → Eqn
  q111 c4 = eqn (Sw12 ∷ Bx0-1324 ∷ []) (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ (lit c4))
  q112 : Ws → Eqn
  q112 c4 = eqn (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4))

-- Cz-beta @122331: 7 steps
lem-Cz-beta-at122331 : Ws → ⟪ (CCZ023 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CCZ023 ∷ []) ⟫ʷ
lem-Cz-beta-at122331 c4 = derive (CCZ023 ∷ Bx0-2314 ∷ []) (Bx0-2314 ∷ CCZ023 ∷ [])
  (rw⁻ 0 (q66 c4) ∷
   rw 1 (q108 c4) ∷
   rw 2 (q109 c4) ∷
   rw 1 (q110 c4) ∷
   rw 0 (q111 c4) ∷
   rw 1 (q112 c4) ∷
   rw 2 (q66 c4) ∷ []) Eq.refl

private
  q113 : Ws → Eqn
  q113 c4 = eqn (CCZ023 ∷ []) (CCZ023 ∷ []) (wl0242 (lit c4))
  q114 : Ws → Eqn
  q114 c4 = eqn (Bx0-1234 ∷ []) (Bx0-2134 ∷ []) (lem-sym12 c4)
  q115 : Ws → Eqn
  q115 c4 = eqn (Bx0-2134 ∷ []) (Bx0-2314 ∷ []) (lem-sym23-at1221 c4)
  q116 : Ws → Eqn
  q116 c4 = eqn (CCZ023 ∷ Bx0-2314 ∷ []) (Bx0-2314 ∷ CCZ023 ∷ []) (lem-Cz-beta-at122331 c4)
  q117 : Ws → Eqn
  q117 c4 = eqn (Bx0-2314 ∷ []) (Bx0-2134 ∷ []) (lem-sym23-at122331 c4)
  q118 : Ws → Eqn
  q118 c4 = eqn (Bx0-2134 ∷ []) (Bx0-1234 ∷ []) (lem-sym12-at1221 c4)

-- auto BOX(0;1234) | CCZ302: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ302 : Ws → ⟪ (Bx0-1234 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ302 c4 = derive (Bx0-1234 ∷ CCZ023 ∷ []) (CCZ023 ∷ Bx0-1234 ∷ [])
  (rw 1 (q113 c4) ∷
   rw 0 (q114 c4) ∷
   rw 0 (q115 c4) ∷
   rw⁻ 0 (q116 c4) ∷
   rw 1 (q117 c4) ∷
   rw 1 (q118 c4) ∷
   rw 0 (q113 c4) ∷ []) Eq.refl

private
  q119 : Ws → Eqn
  q119 c4 = eqn (Sw23 ∷ Toff314 ∷ []) (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 (lit c4))
  q120 : Ws → Eqn
  q120 c4 = eqn (Sw23 ∷ Bx0-1432 ∷ []) (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4))
  q121 : Ws → Eqn
  q121 c4 = eqn (Toff214 ∷ Bx0-1423 ∷ Toff214 ∷ []) (Bx0-1423 ∷ CCZ134 ∷ []) (lem-T312-beta-at243243 c4)
  q122 : Ws → Eqn
  q122 c4 = eqn (Sw23 ∷ Bx0-1423 ∷ []) (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ (lit c4))
  q123 : Ws → Eqn
  q123 c4 = eqn (Sw23 ∷ CCZ134 ∷ []) (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4))

-- T312-beta @2442: 8 steps
lem-T312-beta-at2442 : Ws → ⟪ (Toff314 ∷ Bx0-1432 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CCZ124 ∷ []) ⟫ʷ
lem-T312-beta-at2442 c4 = derive (Toff314 ∷ Bx0-1432 ∷ Toff314 ∷ []) (Bx0-1432 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q54 c4) ∷
   rw 1 (q119 c4) ∷
   rw 2 (q120 c4) ∷
   rw 3 (q119 c4) ∷
   rw 1 (q121 c4) ∷
   rw 0 (q122 c4) ∷
   rw 1 (q123 c4) ∷
   rw 2 (q54 c4) ∷ []) Eq.refl

private
  q124 : Ws → Eqn
  q124 c4 = eqn (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) (wl0078 (lit c4))
  q125 : Ws → Eqn
  q125 c4 = eqn (CCZ013 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at03102132 c4)

-- auto CCZ012 | CCZ342 @031031: 7 steps
lem-auto-CCZ012-∣-CCZ342-at031031 : Ws → ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at031031 c4 = derive (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ [])
  (rw⁻ 0 (q66 c4) ∷
   rw 1 (q108 c4) ∷
   rw⁻ 2 (q124 c4) ∷
   rw 1 (q125 c4) ∷
   rw⁻ 0 (q124 c4) ∷
   rw 1 (q112 c4) ∷
   rw 2 (q66 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = eqn (Bx3-4102 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-beta-T-at0314213042 c4)
  q127 : Ws → Eqn
  q127 c4 = eqn (Toff314 ∷ Toff314 ∷ []) [] (wl0248 (lit c4))
  q128 : Ws → Eqn
  q128 c4 = eqn (Toff314 ∷ []) (Toff314 ∷ []) (wl0267 (lit c4))
  q129 : Ws → Eqn
  q129 c4 = eqn (Bx0-1342 ∷ []) (Bx0-1432 ∷ []) (lem-sym23-at233442 c4)
  q130 : Ws → Eqn
  q130 c4 = eqn (Toff314 ∷ Bx0-1432 ∷ Toff314 ∷ []) (Bx0-1432 ∷ CCZ124 ∷ []) (lem-T312-beta-at2442 c4)
  q131 : Ws → Eqn
  q131 c4 = eqn (Bx0-1432 ∷ []) (Bx0-1342 ∷ []) (lem-sym23-at2442 c4)
  q132 : Ws → Eqn
  q132 c4 = eqn (Bx0-1342 ∷ []) (Bx0-1324 ∷ []) (lem-sym34-at233442 c4)
  q133 : Ws → Eqn
  q133 c4 = eqn (Bx0-1234 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ142 c4)
  q134 : Ws → Eqn
  q134 c4 = eqn (Bx0-1234 ∷ CCZ023 ∷ []) (CCZ023 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ302 c4)
  q135 : Ws → Eqn
  q135 c4 = eqn (CCZ124 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ124 ∷ []) (wl0617 (lit c4))
  q136 : Ws → Eqn
  q136 c4 = eqn (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at031031 c4)
  q137 : Ws → Eqn
  q137 c4 = eqn (CCZ124 ∷ CCZ124 ∷ []) [] (wl0351 (lit c4))

-- auto BOX(0;1234) | BOX(3;0412): 35 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩ : Ws → ⟪ (Bx0-1234 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩ c4 = derive (Bx0-1234 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ Bx0-1234 ∷ [])
  (rw 1 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 1 (q126 c4) ∷
   rw⁻ 0 (q127 c4) ∷
   rw 1 (q128 c4) ∷
   rw 3 (q128 c4) ∷
   rw 2 (q78 c4) ∷
   rw 2 (q79 c4) ∷
   rw 2 (q129 c4) ∷
   rw 1 (q130 c4) ∷
   rw 1 (q131 c4) ∷
   rw 1 (q132 c4) ∷
   rw 1 (q86 c4) ∷
   rw 1 (q133 c4) ∷
   rw 2 (q134 c4) ∷
   rw⁻ 3 (q127 c4) ∷
   rw 4 (q128 c4) ∷
   rw 6 (q128 c4) ∷
   rw 5 (q78 c4) ∷
   rw 5 (q79 c4) ∷
   rw 5 (q129 c4) ∷
   rw 4 (q130 c4) ∷
   rw 4 (q131 c4) ∷
   rw 4 (q132 c4) ∷
   rw 4 (q86 c4) ∷
   rw 4 (q133 c4) ∷
   rw 5 (q134 c4) ∷
   rw⁻ 0 (q135 c4) ∷
   rw⁻ 3 (q135 c4) ∷
   rw 2 (q136 c4) ∷
   rw⁻ 1 (q135 c4) ∷
   rw 0 (q137 c4) ∷
   rw⁻ 0 (q126 c4) ∷
   rw 0 (q9 c4) ∷
   rw 0 (q10 c4) ∷ []) Eq.refl

private
  q138 : Ws → Eqn
  q138 c4 = eqn (CCZ014 ∷ []) (CCZ014 ∷ []) (wp0285 c4)
  q139 : Ws → Eqn
  q139 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1243 ∷ []) (lem-sym34 c4)
  q140 : Ws → Eqn
  q140 c4 = eqn (Bx0-1243 ∷ []) (Bx0-1423 ∷ []) (lem-sym23-at3443 c4)
  q141 : Ws → Eqn
  q141 c4 = eqn (CCZ014 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ []) (lem-Cz-beta-at243243 c4)
  q142 : Ws → Eqn
  q142 c4 = eqn (Bx0-1423 ∷ []) (Bx0-1243 ∷ []) (lem-sym23-at243243 c4)
  q143 : Ws → Eqn
  q143 c4 = eqn (Bx0-1243 ∷ []) (Bx0-1234 ∷ []) (lem-sym34-at3443 c4)

-- auto BOX(0;1234) | CCZ104: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ104 : Ws → ⟪ (Bx0-1234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ104 c4 = derive (Bx0-1234 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx0-1234 ∷ [])
  (rw 1 (q138 c4) ∷
   rw 0 (q139 c4) ∷
   rw 0 (q140 c4) ∷
   rw⁻ 0 (q141 c4) ∷
   rw 1 (q142 c4) ∷
   rw 1 (q143 c4) ∷
   rw 0 (q138 c4) ∷ []) Eq.refl

private
  q144 : Ws → Eqn
  q144 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4))
  q145 : Ws → Eqn
  q145 c4 = eqn (CCZ234 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ234 ∷ []) (wl0086 (lit c4))
  q146 : Ws → Eqn
  q146 c4 = eqn (CCZ012 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ342 c4)
  q147 : Ws → Eqn
  q147 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4))

-- auto CCZ012 | CCZ342 @2332: 7 steps
lem-auto-CCZ012-∣-CCZ342-at2332 : Ws → ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at2332 c4 = derive (CCZ013 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q54 c4) ∷
   rw 1 (q144 c4) ∷
   rw⁻ 2 (q145 c4) ∷
   rw 1 (q146 c4) ∷
   rw⁻ 0 (q145 c4) ∷
   rw 1 (q147 c4) ∷
   rw 2 (q54 c4) ∷ []) Eq.refl

private
  q148 : Ws → Eqn
  q148 c4 = eqn (Sw34 ∷ CCZ014 ∷ []) (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 (lit c4))
  q149 : Ws → Eqn
  q149 c4 = eqn (CCZ234 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ234 ∷ []) (wl0155 (lit c4))
  q150 : Ws → Eqn
  q150 c4 = eqn (CCZ013 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at2332 c4)
  q151 : Ws → Eqn
  q151 c4 = eqn (Sw34 ∷ CCZ013 ∷ []) (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 (lit c4))

-- auto CCZ012 | CCZ342 @243243: 7 steps
lem-auto-CCZ012-∣-CCZ342-at243243 : Ws → ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at243243 c4 = derive (CCZ014 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q60 c4) ∷
   rw 1 (q148 c4) ∷
   rw⁻ 2 (q149 c4) ∷
   rw 1 (q150 c4) ∷
   rw⁻ 0 (q149 c4) ∷
   rw 1 (q151 c4) ∷
   rw 2 (q60 c4) ∷ []) Eq.refl

private
  q152 : Ws → Eqn
  q152 c4 = eqn (Sw01 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 (lit c4))
  q153 : Ws → Eqn
  q153 c4 = eqn (Sw01 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ))
  q154 : Ws → Eqn
  q154 c4 = eqn (CCZ014 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at243243 c4)

-- auto CCZ012 | CCZ342 @0110243243: 7 steps
lem-auto-CCZ012-∣-CCZ342-at0110243243 : Ws → ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at0110243243 c4 = derive (CCZ014 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q87 c4) ∷
   rw 1 (q152 c4) ∷
   rw 2 (q153 c4) ∷
   rw 1 (q154 c4) ∷
   rw 0 (q153 c4) ∷
   rw 1 (q152 c4) ∷
   rw 2 (q87 c4) ∷ []) Eq.refl

private
  q155 : Ws → Eqn
  q155 c4 = eqn (Bx1-0234 ∷ []) (Bx1-2034 ∷ []) (lem-sym12-at0110 c4)
  q156 : Ws → Eqn
  q156 c4 = eqn (Bx1-2034 ∷ []) (Bx1-2304 ∷ []) (lem-sym23-at011220 c4)
  q157 : Ws → Eqn
  q157 c4 = eqn (Bx1-2304 ∷ []) (Toff123 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ []) (lem-beta-T-at01122330 c4)
  q158 : Ws → Eqn
  q158 c4 = eqn (Toff123 ∷ Toff123 ∷ []) [] (wl0618 (lit c4))
  q159 : Ws → Eqn
  q159 c4 = eqn (Toff123 ∷ Bx0-2314 ∷ Toff123 ∷ []) (Bx0-2314 ∷ CCZ234 ∷ []) (lem-T312-beta-at122331 c4)
  q160 : Ws → Eqn
  q160 c4 = eqn (Bx0-1234 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234 c4)
  q161 : Ws → Eqn
  q161 c4 = eqn (Bx0-1234 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ104 c4)
  q162 : Ws → Eqn
  q162 c4 = eqn (CCZ234 ∷ Toff123 ∷ []) (Toff123 ∷ CCZ234 ∷ []) (wl0619 (lit c4))
  q163 : Ws → Eqn
  q163 c4 = eqn (CCZ014 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0110243243 c4)
  q164 : Ws → Eqn
  q164 c4 = eqn (CCZ234 ∷ CCZ234 ∷ []) [] (wl0265 (lit c4))
  q165 : Ws → Eqn
  q165 c4 = eqn (Bx1-2304 ∷ []) (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4)
  q166 : Ws → Eqn
  q166 c4 = eqn (Bx1-2034 ∷ []) (Bx1-0234 ∷ []) (lem-sym12-at011220 c4)

-- auto BOX(0;1234) | BOX(1;0234): 27 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩ : Ws → ⟪ (Bx0-1234 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩ c4 = derive (Bx0-1234 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ Bx0-1234 ∷ [])
  (rw 1 (q155 c4) ∷
   rw 1 (q156 c4) ∷
   rw 1 (q157 c4) ∷
   rw⁻ 0 (q158 c4) ∷
   rw 2 (q114 c4) ∷
   rw 2 (q115 c4) ∷
   rw 1 (q159 c4) ∷
   rw 1 (q117 c4) ∷
   rw 1 (q118 c4) ∷
   rw 1 (q160 c4) ∷
   rw 2 (q161 c4) ∷
   rw⁻ 3 (q158 c4) ∷
   rw 5 (q114 c4) ∷
   rw 5 (q115 c4) ∷
   rw 4 (q159 c4) ∷
   rw 4 (q117 c4) ∷
   rw 4 (q118 c4) ∷
   rw 4 (q160 c4) ∷
   rw 5 (q161 c4) ∷
   rw⁻ 0 (q162 c4) ∷
   rw⁻ 3 (q162 c4) ∷
   rw 2 (q163 c4) ∷
   rw⁻ 1 (q162 c4) ∷
   rw 0 (q164 c4) ∷
   rw⁻ 0 (q157 c4) ∷
   rw 0 (q165 c4) ∷
   rw 0 (q166 c4) ∷ []) Eq.refl

-- boxify-4 [nf of rhs]: 0 steps
lem-boxify-4-nf-of-rhs : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-boxify-4-nf-of-rhs c4 = refl

private
  q167 : Ws → Eqn
  q167 c4 = eqn (Sw12 ∷ Bx3-0214 ∷ []) (Bx3-0124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0214⟩ (lit c4))
  q168 : Ws → Eqn
  q168 c4 = eqn (Bx3-0124 ∷ []) (Bx3-0142 ∷ []) (lem-sym34-at03102132 c4)
  q169 : Ws → Eqn
  q169 c4 = eqn (Sw12 ∷ Bx3-0142 ∷ []) (Bx3-0241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0142⟩ (lit c4))

-- sym34 @031031: 5 steps
lem-sym34-at031031 : Ws → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-sym34-at031031 c4 = derive (Bx3-0214 ∷ []) (Bx3-0241 ∷ [])
  (rw⁻ 0 (q66 c4) ∷
   rw 1 (q167 c4) ∷
   rw 1 (q168 c4) ∷
   rw 0 (q169 c4) ∷
   rw 1 (q66 c4) ∷ []) Eq.refl

private
  q170 : Ws → Eqn
  q170 c4 = eqn (Sw23 ∷ Bx3-0142 ∷ []) (Bx2-0143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0142⟩ (lit c4))
  q171 : Ws → Eqn
  q171 c4 = eqn (Bx2-0143 ∷ []) (Bx2-1043 ∷ []) (lem-sym12-at0210213443 c4)
  q172 : Ws → Eqn
  q172 c4 = eqn (Sw23 ∷ Bx2-1043 ∷ []) (Bx3-1042 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·1043⟩ (lit c4))

-- sym12 @0310213442: 5 steps
lem-sym12-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ []) ⟫ʷ
lem-sym12-at0310213442 c4 = derive (Bx3-0142 ∷ []) (Bx3-1042 ∷ [])
  (rw⁻ 0 (q54 c4) ∷
   rw 1 (q170 c4) ∷
   rw 1 (q171 c4) ∷
   rw 0 (q172 c4) ∷
   rw 1 (q54 c4) ∷ []) Eq.refl

private
  q173 : Ws → Eqn
  q173 c4 = eqn (Sw12 ∷ Bx3-0241 ∷ []) (Bx3-0142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0241⟩ (lit c4))
  q174 : Ws → Eqn
  q174 c4 = eqn (Bx3-0142 ∷ []) (Bx3-1042 ∷ []) (lem-sym12-at0310213442 c4)
  q175 : Ws → Eqn
  q175 c4 = eqn (Sw12 ∷ Bx3-1042 ∷ []) (Bx3-2041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1042⟩ (lit c4))

-- sym12 @03103441: 5 steps
lem-sym12-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-sym12-at03103441 c4 = derive (Bx3-0241 ∷ []) (Bx3-2041 ∷ [])
  (rw⁻ 0 (q66 c4) ∷
   rw 1 (q173 c4) ∷
   rw 1 (q174 c4) ∷
   rw 0 (q175 c4) ∷
   rw 1 (q66 c4) ∷ []) Eq.refl

private
  q176 : Ws → Eqn
  q176 c4 = eqn (Sw01 ∷ Bx3-1042 ∷ []) (Bx3-0142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1042⟩ (lit c4))
  q177 : Ws → Eqn
  q177 c4 = eqn (Bx3-0142 ∷ []) (Bx3-0412 ∷ []) (lem-sym23-at0310213442 c4)
  q178 : Ws → Eqn
  q178 c4 = eqn (Sw01 ∷ Bx3-0412 ∷ []) (Bx3-1402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0412⟩ (lit c4))

-- sym23 @03203442: 5 steps
lem-sym23-at03203442 : Ws → ⟪ (Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ []) ⟫ʷ
lem-sym23-at03203442 c4 = derive (Bx3-1042 ∷ []) (Bx3-1402 ∷ [])
  (rw⁻ 0 (q87 c4) ∷
   rw 1 (q176 c4) ∷
   rw 1 (q177 c4) ∷
   rw 0 (q178 c4) ∷
   rw 1 (q87 c4) ∷ []) Eq.refl

private
  q179 : Ws → Eqn
  q179 c4 = eqn (Sw12 ∷ Bx3-2041 ∷ []) (Bx3-1042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2041⟩ (lit c4))
  q180 : Ws → Eqn
  q180 c4 = eqn (Bx3-1042 ∷ []) (Bx3-1402 ∷ []) (lem-sym23-at03203442 c4)
  q181 : Ws → Eqn
  q181 c4 = eqn (Sw12 ∷ Bx3-1402 ∷ []) (Bx3-2401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1402⟩ (lit c4))

-- sym23 @0312203441: 5 steps
lem-sym23-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-sym23-at0312203441 c4 = derive (Bx3-2041 ∷ []) (Bx3-2401 ∷ [])
  (rw⁻ 0 (q66 c4) ∷
   rw 1 (q179 c4) ∷
   rw 1 (q180 c4) ∷
   rw 0 (q181 c4) ∷
   rw 1 (q66 c4) ∷ []) Eq.refl

private
  q182 : Ws → Eqn
  q182 c4 = eqn (Sw23 ∷ Toff103 ∷ []) (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 (lit c4))
  q183 : Ws → Eqn
  q183 c4 = eqn (Toff102 ∷ Bx0-1234 ∷ Toff102 ∷ []) (Bx0-1234 ∷ Bx1-0234 ∷ []) (lem-TW c4)
  q184 : Ws → Eqn
  q184 c4 = eqn (Sw23 ∷ Bx1-0234 ∷ []) (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ (lit c4))

-- TW @2332: 8 steps
lem-TW-at2332 : Ws → ⟪ (Toff103 ∷ Bx0-1324 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ Bx1-0324 ∷ []) ⟫ʷ
lem-TW-at2332 c4 = derive (Toff103 ∷ Bx0-1324 ∷ Toff103 ∷ []) (Bx0-1324 ∷ Bx1-0324 ∷ [])
  (rw⁻ 0 (q54 c4) ∷
   rw 1 (q182 c4) ∷
   rw 2 (q56 c4) ∷
   rw 3 (q182 c4) ∷
   rw 1 (q183 c4) ∷
   rw 0 (q58 c4) ∷
   rw 1 (q184 c4) ∷
   rw 2 (q54 c4) ∷ []) Eq.refl

private
  q185 : Ws → Eqn
  q185 c4 = eqn (Sw34 ∷ Toff104 ∷ []) (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 (lit c4))
  q186 : Ws → Eqn
  q186 c4 = eqn (Toff103 ∷ Bx0-1324 ∷ Toff103 ∷ []) (Bx0-1324 ∷ Bx1-0324 ∷ []) (lem-TW-at2332 c4)
  q187 : Ws → Eqn
  q187 c4 = eqn (Sw34 ∷ Bx1-0324 ∷ []) (Bx1-0423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0324⟩ (lit c4))

-- TW @243243: 8 steps
lem-TW-at243243 : Ws → ⟪ (Toff104 ∷ Bx0-1423 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-TW-at243243 c4 = derive (Toff104 ∷ Bx0-1423 ∷ Toff104 ∷ []) (Bx0-1423 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q60 c4) ∷
   rw 1 (q185 c4) ∷
   rw 2 (q62 c4) ∷
   rw 3 (q185 c4) ∷
   rw 1 (q186 c4) ∷
   rw 0 (q64 c4) ∷
   rw 1 (q187 c4) ∷
   rw 2 (q60 c4) ∷ []) Eq.refl

private
  q188 : Ws → Eqn
  q188 c4 = eqn (Sw01 ∷ Toff014 ∷ []) (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 (lit c4))
  q189 : Ws → Eqn
  q189 c4 = eqn (Sw01 ∷ Bx1-0423 ∷ []) (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4))
  q190 : Ws → Eqn
  q190 c4 = eqn (Toff104 ∷ Bx0-1423 ∷ Toff104 ∷ []) (Bx0-1423 ∷ Bx1-0423 ∷ []) (lem-TW-at243243 c4)
  q191 : Ws → Eqn
  q191 c4 = eqn (Sw01 ∷ Bx0-1423 ∷ []) (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4))

-- TW @0110243243: 8 steps
lem-TW-at0110243243 : Ws → ⟪ (Toff014 ∷ Bx1-0423 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-TW-at0110243243 c4 = derive (Toff014 ∷ Bx1-0423 ∷ Toff014 ∷ []) (Bx1-0423 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q87 c4) ∷
   rw 1 (q188 c4) ∷
   rw 2 (q189 c4) ∷
   rw 3 (q188 c4) ∷
   rw 1 (q190 c4) ∷
   rw 0 (q191 c4) ∷
   rw 1 (q189 c4) ∷
   rw 2 (q87 c4) ∷ []) Eq.refl

private
  q192 : Ws → Eqn
  q192 c4 = eqn (Sw12 ∷ Bx2-0413 ∷ []) (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4))
  q193 : Ws → Eqn
  q193 c4 = eqn (Toff014 ∷ Bx1-0423 ∷ Toff014 ∷ []) (Bx1-0423 ∷ Bx0-1423 ∷ []) (lem-TW-at0110243243 c4)
  q194 : Ws → Eqn
  q194 c4 = eqn (Sw12 ∷ Bx1-0423 ∷ []) (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4))

-- TW @0210243143: 8 steps
lem-TW-at0210243143 : Ws → ⟪ (Toff024 ∷ Bx2-0413 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Bx0-2413 ∷ []) ⟫ʷ
lem-TW-at0210243143 c4 = derive (Toff024 ∷ Bx2-0413 ∷ Toff024 ∷ []) (Bx2-0413 ∷ Bx0-2413 ∷ [])
  (rw⁻ 0 (q66 c4) ∷
   rw 1 (q67 c4) ∷
   rw 2 (q192 c4) ∷
   rw 3 (q67 c4) ∷
   rw 1 (q193 c4) ∷
   rw 0 (q194 c4) ∷
   rw 1 (q70 c4) ∷
   rw 2 (q66 c4) ∷ []) Eq.refl

private
  q195 : Ws → Eqn
  q195 c4 = eqn (Sw23 ∷ Bx3-0412 ∷ []) (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4))
  q196 : Ws → Eqn
  q196 c4 = eqn (Toff024 ∷ Bx2-0413 ∷ Toff024 ∷ []) (Bx2-0413 ∷ Bx0-2413 ∷ []) (lem-TW-at0210243143 c4)
  q197 : Ws → Eqn
  q197 c4 = eqn (Sw23 ∷ Bx2-0413 ∷ []) (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4))

-- TW @0310243142: 8 steps
lem-TW-at0310243142 : Ws → ⟪ (Toff034 ∷ Bx3-0412 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Bx0-3412 ∷ []) ⟫ʷ
lem-TW-at0310243142 c4 = derive (Toff034 ∷ Bx3-0412 ∷ Toff034 ∷ []) (Bx3-0412 ∷ Bx0-3412 ∷ [])
  (rw⁻ 0 (q54 c4) ∷
   rw 1 (q72 c4) ∷
   rw 2 (q195 c4) ∷
   rw 3 (q72 c4) ∷
   rw 1 (q196 c4) ∷
   rw 0 (q197 c4) ∷
   rw 1 (q75 c4) ∷
   rw 2 (q54 c4) ∷ []) Eq.refl

private
  q198 : Ws → Eqn
  q198 c4 = eqn (Sw01 ∷ Bx3-1402 ∷ []) (Bx3-0412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1402⟩ (lit c4))
  q199 : Ws → Eqn
  q199 c4 = eqn (Toff034 ∷ Bx3-0412 ∷ Toff034 ∷ []) (Bx3-0412 ∷ Bx0-3412 ∷ []) (lem-TW-at0310243142 c4)
  q200 : Ws → Eqn
  q200 c4 = eqn (Sw01 ∷ Bx0-3412 ∷ []) (Bx1-3402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3412⟩ (lit c4))

-- TW @03243042: 8 steps
lem-TW-at03243042 : Ws → ⟪ (Toff134 ∷ Bx3-1402 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Bx1-3402 ∷ []) ⟫ʷ
lem-TW-at03243042 c4 = derive (Toff134 ∷ Bx3-1402 ∷ Toff134 ∷ []) (Bx3-1402 ∷ Bx1-3402 ∷ [])
  (rw⁻ 0 (q87 c4) ∷
   rw 1 (q89 c4) ∷
   rw 2 (q198 c4) ∷
   rw 3 (q89 c4) ∷
   rw 1 (q199 c4) ∷
   rw 0 (q178 c4) ∷
   rw 1 (q200 c4) ∷
   rw 2 (q87 c4) ∷ []) Eq.refl

private
  q201 : Ws → Eqn
  q201 c4 = eqn (Sw12 ∷ Bx3-2401 ∷ []) (Bx3-1402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2401⟩ (lit c4))
  q202 : Ws → Eqn
  q202 c4 = eqn (Toff134 ∷ Bx3-1402 ∷ Toff134 ∷ []) (Bx3-1402 ∷ Bx1-3402 ∷ []) (lem-TW-at03243042 c4)
  q203 : Ws → Eqn
  q203 c4 = eqn (Sw12 ∷ Bx1-3402 ∷ []) (Bx2-3401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3402⟩ (lit c4))

-- TW @0312243041: 8 steps
lem-TW-at0312243041 : Ws → ⟪ (Toff234 ∷ Bx3-2401 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ Bx2-3401 ∷ []) ⟫ʷ
lem-TW-at0312243041 c4 = derive (Toff234 ∷ Bx3-2401 ∷ Toff234 ∷ []) (Bx3-2401 ∷ Bx2-3401 ∷ [])
  (rw⁻ 0 (q66 c4) ∷
   rw 1 (q94 c4) ∷
   rw 2 (q201 c4) ∷
   rw 3 (q94 c4) ∷
   rw 1 (q202 c4) ∷
   rw 0 (q181 c4) ∷
   rw 1 (q203 c4) ∷
   rw 2 (q66 c4) ∷ []) Eq.refl

private
  q204 : Ws → Eqn
  q204 c4 = eqn (Sw01 ∷ Bx3-0142 ∷ []) (Bx3-1042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0142⟩ (lit c4))

-- sym23 @03243042: 5 steps
lem-sym23-at03243042 : Ws → ⟪ (Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ []) ⟫ʷ
lem-sym23-at03243042 c4 = derive (Bx3-1402 ∷ []) (Bx3-1042 ∷ [])
  (rw⁻ 0 (q87 c4) ∷
   rw 1 (q198 c4) ∷
   rw 1 (q40 c4) ∷
   rw 0 (q204 c4) ∷
   rw 1 (q87 c4) ∷ []) Eq.refl

private
  q205 : Ws → Eqn
  q205 c4 = eqn (Bx3-1402 ∷ []) (Bx3-1042 ∷ []) (lem-sym23-at03243042 c4)

-- sym23 @0312243041: 5 steps
lem-sym23-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-sym23-at0312243041 c4 = derive (Bx3-2401 ∷ []) (Bx3-2041 ∷ [])
  (rw⁻ 0 (q66 c4) ∷
   rw 1 (q201 c4) ∷
   rw 1 (q205 c4) ∷
   rw 0 (q175 c4) ∷
   rw 1 (q66 c4) ∷ []) Eq.refl

private
  q206 : Ws → Eqn
  q206 c4 = eqn (Sw01 ∷ Bx3-0124 ∷ []) (Bx3-1024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0124⟩ (lit c4))

-- sym34 @03203442: 5 steps
lem-sym34-at03203442 : Ws → ⟪ (Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-sym34-at03203442 c4 = derive (Bx3-1042 ∷ []) (Bx3-1024 ∷ [])
  (rw⁻ 0 (q87 c4) ∷
   rw 1 (q176 c4) ∷
   rw 1 (q41 c4) ∷
   rw 0 (q206 c4) ∷
   rw 1 (q87 c4) ∷ []) Eq.refl

private
  q207 : Ws → Eqn
  q207 c4 = eqn (Bx3-1042 ∷ []) (Bx3-1024 ∷ []) (lem-sym34-at03203442 c4)
  q208 : Ws → Eqn
  q208 c4 = eqn (Sw12 ∷ Bx3-1024 ∷ []) (Bx3-2014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1024⟩ (lit c4))

-- sym34 @0312203441: 5 steps
lem-sym34-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-sym34-at0312203441 c4 = derive (Bx3-2041 ∷ []) (Bx3-2014 ∷ [])
  (rw⁻ 0 (q66 c4) ∷
   rw 1 (q179 c4) ∷
   rw 1 (q207 c4) ∷
   rw 0 (q208 c4) ∷
   rw 1 (q66 c4) ∷ []) Eq.refl

private
  q209 : Ws → Eqn
  q209 c4 = eqn (Sw01 ∷ Bx3-1024 ∷ []) (Bx3-0124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1024⟩ (lit c4))
  q210 : Ws → Eqn
  q210 c4 = eqn (Bx3-0124 ∷ []) (Bx3-1024 ∷ []) (lem-sym12-at03102132 c4)

-- sym12 @032032: 5 steps
lem-sym12-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-sym12-at032032 c4 = derive (Bx3-1024 ∷ []) (Bx3-0124 ∷ [])
  (rw⁻ 0 (q87 c4) ∷
   rw 1 (q209 c4) ∷
   rw 1 (q210 c4) ∷
   rw 0 (q209 c4) ∷
   rw 1 (q87 c4) ∷ []) Eq.refl

private
  q211 : Ws → Eqn
  q211 c4 = eqn (Sw12 ∷ Bx3-2014 ∷ []) (Bx3-1024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2014⟩ (lit c4))
  q212 : Ws → Eqn
  q212 c4 = eqn (Bx3-1024 ∷ []) (Bx3-0124 ∷ []) (lem-sym12-at032032 c4)
  q213 : Ws → Eqn
  q213 c4 = eqn (Sw12 ∷ Bx3-0124 ∷ []) (Bx3-0214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0124⟩ (lit c4))

-- sym12 @03122031: 5 steps
lem-sym12-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-sym12-at03122031 c4 = derive (Bx3-2014 ∷ []) (Bx3-0214 ∷ [])
  (rw⁻ 0 (q66 c4) ∷
   rw 1 (q211 c4) ∷
   rw 1 (q212 c4) ∷
   rw 0 (q213 c4) ∷
   rw 1 (q66 c4) ∷ []) Eq.refl

private
  q214 : Ws → Eqn
  q214 c4 = eqn (Bx3-0124 ∷ []) (Bx3-0214 ∷ []) (lem-sym23-at03102132 c4)

-- sym23 @031031: 5 steps
lem-sym23-at031031 : Ws → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-sym23-at031031 c4 = derive (Bx3-0214 ∷ []) (Bx3-0124 ∷ [])
  (rw⁻ 0 (q66 c4) ∷
   rw 1 (q167 c4) ∷
   rw 1 (q214 c4) ∷
   rw 0 (q167 c4) ∷
   rw 1 (q66 c4) ∷ []) Eq.refl

private
  q215 : Ws → Eqn
  q215 c4 = eqn (Bx0-1234 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩ c4)

-- auto BOX(0;1234) | BOX(3;0412) @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at0110 : Ws → ⟪ (Bx1-0234 ∷ Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at0110 c4 = derive (Bx1-0234 ∷ Bx3-1402 ∷ []) (Bx3-1402 ∷ Bx1-0234 ∷ [])
  (rw⁻ 0 (q87 c4) ∷
   rw 1 (q88 c4) ∷
   rw 2 (q198 c4) ∷
   rw 1 (q215 c4) ∷
   rw 0 (q178 c4) ∷
   rw 1 (q92 c4) ∷
   rw 2 (q87 c4) ∷ []) Eq.refl

private
  q216 : Ws → Eqn
  q216 c4 = eqn (Bx1-0234 ∷ Bx3-1402 ∷ []) (Bx3-1402 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at0110 c4)

-- auto BOX(0;1234) | BOX(3;0412) @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at021021 : Ws → ⟪ (Bx2-0134 ∷ Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at021021 c4 = derive (Bx2-0134 ∷ Bx3-2401 ∷ []) (Bx3-2401 ∷ Bx2-0134 ∷ [])
  (rw⁻ 0 (q66 c4) ∷
   rw 1 (q93 c4) ∷
   rw 2 (q201 c4) ∷
   rw 1 (q216 c4) ∷
   rw 0 (q181 c4) ∷
   rw 1 (q97 c4) ∷
   rw 2 (q66 c4) ∷ []) Eq.refl

private
  q217 : Ws → Eqn
  q217 c4 = eqn (Sw23 ∷ Bx2-3401 ∷ []) (Bx3-2401 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·3401⟩ (lit c4))
  q218 : Ws → Eqn
  q218 c4 = eqn (Bx2-0134 ∷ Bx3-2401 ∷ []) (Bx3-2401 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at021021 c4)
  q219 : Ws → Eqn
  q219 c4 = eqn (Sw23 ∷ Bx3-2401 ∷ []) (Bx2-3401 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·2401⟩ (lit c4))

-- auto BOX(0;1234) | BOX(3;0412) @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03102132 : Ws → ⟪ (Bx3-0124 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03102132 c4 = derive (Bx3-0124 ∷ Bx2-3401 ∷ []) (Bx2-3401 ∷ Bx3-0124 ∷ [])
  (rw⁻ 0 (q54 c4) ∷
   rw 1 (q98 c4) ∷
   rw 2 (q217 c4) ∷
   rw 1 (q218 c4) ∷
   rw 0 (q219 c4) ∷
   rw 1 (q102 c4) ∷
   rw 2 (q54 c4) ∷ []) Eq.refl

private
  q220 : Ws → Eqn
  q220 c4 = eqn (Sw12 ∷ Toff204 ∷ []) (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 (lit c4))

-- TW @12243143: 8 steps
lem-TW-at12243143 : Ws → ⟪ (Toff204 ∷ Bx0-2413 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-TW-at12243143 c4 = derive (Toff204 ∷ Bx0-2413 ∷ Toff204 ∷ []) (Bx0-2413 ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q66 c4) ∷
   rw 1 (q220 c4) ∷
   rw 2 (q68 c4) ∷
   rw 3 (q220 c4) ∷
   rw 1 (q190 c4) ∷
   rw 0 (q70 c4) ∷
   rw 1 (q194 c4) ∷
   rw 2 (q66 c4) ∷ []) Eq.refl

private
  q221 : Ws → Eqn
  q221 c4 = eqn (Sw23 ∷ Toff304 ∷ []) (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 (lit c4))
  q222 : Ws → Eqn
  q222 c4 = eqn (Toff204 ∷ Bx0-2413 ∷ Toff204 ∷ []) (Bx0-2413 ∷ Bx2-0413 ∷ []) (lem-TW-at12243143 c4)

-- TW @13243142: 8 steps
lem-TW-at13243142 : Ws → ⟪ (Toff304 ∷ Bx0-3412 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-TW-at13243142 c4 = derive (Toff304 ∷ Bx0-3412 ∷ Toff304 ∷ []) (Bx0-3412 ∷ Bx3-0412 ∷ [])
  (rw⁻ 0 (q54 c4) ∷
   rw 1 (q221 c4) ∷
   rw 2 (q73 c4) ∷
   rw 3 (q221 c4) ∷
   rw 1 (q222 c4) ∷
   rw 0 (q75 c4) ∷
   rw 1 (q197 c4) ∷
   rw 2 (q54 c4) ∷ []) Eq.refl

private
  q223 : Ws → Eqn
  q223 c4 = eqn (Sw01 ∷ Toff314 ∷ []) (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 (lit c4))
  q224 : Ws → Eqn
  q224 c4 = eqn (Sw01 ∷ Bx1-3402 ∷ []) (Bx0-3412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3402⟩ (lit c4))
  q225 : Ws → Eqn
  q225 c4 = eqn (Toff304 ∷ Bx0-3412 ∷ Toff304 ∷ []) (Bx0-3412 ∷ Bx3-0412 ∷ []) (lem-TW-at13243142 c4)

-- TW @0113243042: 8 steps
lem-TW-at0113243042 : Ws → ⟪ (Toff314 ∷ Bx1-3402 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ Bx3-1402 ∷ []) ⟫ʷ
lem-TW-at0113243042 c4 = derive (Toff314 ∷ Bx1-3402 ∷ Toff314 ∷ []) (Bx1-3402 ∷ Bx3-1402 ∷ [])
  (rw⁻ 0 (q87 c4) ∷
   rw 1 (q223 c4) ∷
   rw 2 (q224 c4) ∷
   rw 3 (q223 c4) ∷
   rw 1 (q225 c4) ∷
   rw 0 (q200 c4) ∷
   rw 1 (q178 c4) ∷
   rw 2 (q87 c4) ∷ []) Eq.refl

private
  q226 : Ws → Eqn
  q226 c4 = eqn (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) (wl0063 (lit c4))
  q227 : Ws → Eqn
  q227 c4 = eqn (Sw12 ∷ Bx2-3401 ∷ []) (Bx1-3402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3401⟩ (lit c4))
  q228 : Ws → Eqn
  q228 c4 = eqn (Toff314 ∷ Bx1-3402 ∷ Toff314 ∷ []) (Bx1-3402 ∷ Bx3-1402 ∷ []) (lem-TW-at0113243042 c4)

-- TW @0213243041: 8 steps
lem-TW-at0213243041 : Ws → ⟪ (Toff324 ∷ Bx2-3401 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Bx3-2401 ∷ []) ⟫ʷ
lem-TW-at0213243041 c4 = derive (Toff324 ∷ Bx2-3401 ∷ Toff324 ∷ []) (Bx2-3401 ∷ Bx3-2401 ∷ [])
  (rw⁻ 0 (q66 c4) ∷
   rw 1 (q226 c4) ∷
   rw 2 (q227 c4) ∷
   rw 3 (q226 c4) ∷
   rw 1 (q228 c4) ∷
   rw 0 (q203 c4) ∷
   rw 1 (q181 c4) ∷
   rw 2 (q66 c4) ∷ []) Eq.refl

private
  q229 : Ws → Eqn
  q229 c4 = eqn (Sw23 ∷ Bx1-0324 ∷ []) (Bx1-0234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0324⟩ (lit c4))
  q230 : Ws → Eqn
  q230 c4 = eqn (Bx0-1234 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩ c4)

-- auto BOX(0;1234) | BOX(1;0234) @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at2332 : Ws → ⟪ (Bx0-1324 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at2332 c4 = derive (Bx0-1324 ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ Bx0-1324 ∷ [])
  (rw⁻ 0 (q54 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q229 c4) ∷
   rw 1 (q230 c4) ∷
   rw 0 (q184 c4) ∷
   rw 1 (q58 c4) ∷
   rw 2 (q54 c4) ∷ []) Eq.refl

private
  q231 : Ws → Eqn
  q231 c4 = eqn (Sw34 ∷ Bx1-0423 ∷ []) (Bx1-0324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0423⟩ (lit c4))
  q232 : Ws → Eqn
  q232 c4 = eqn (Bx0-1324 ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at2332 c4)

-- auto BOX(0;1234) | BOX(1;0234) @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at243243 : Ws → ⟪ (Bx0-1423 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at243243 c4 = derive (Bx0-1423 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ Bx0-1423 ∷ [])
  (rw⁻ 0 (q60 c4) ∷
   rw 1 (q62 c4) ∷
   rw 2 (q231 c4) ∷
   rw 1 (q232 c4) ∷
   rw 0 (q187 c4) ∷
   rw 1 (q64 c4) ∷
   rw 2 (q60 c4) ∷ []) Eq.refl

private
  q233 : Ws → Eqn
  q233 c4 = eqn (Bx0-1423 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at243243 c4)

-- auto BOX(0;1234) | BOX(1;0234) @12243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at12243143 : Ws → ⟪ (Bx0-2413 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Bx0-2413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at12243143 c4 = derive (Bx0-2413 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ Bx0-2413 ∷ [])
  (rw⁻ 0 (q66 c4) ∷
   rw 1 (q68 c4) ∷
   rw 2 (q192 c4) ∷
   rw 1 (q233 c4) ∷
   rw 0 (q194 c4) ∷
   rw 1 (q70 c4) ∷
   rw 2 (q66 c4) ∷ []) Eq.refl

private
  q234 : Ws → Eqn
  q234 c4 = eqn (Bx0-2413 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ Bx0-2413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at12243143 c4)

-- auto BOX(0;1234) | BOX(1;0234) @13243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at13243142 : Ws → ⟪ (Bx0-3412 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Bx0-3412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at13243142 c4 = derive (Bx0-3412 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ Bx0-3412 ∷ [])
  (rw⁻ 0 (q54 c4) ∷
   rw 1 (q73 c4) ∷
   rw 2 (q195 c4) ∷
   rw 1 (q234 c4) ∷
   rw 0 (q197 c4) ∷
   rw 1 (q75 c4) ∷
   rw 2 (q54 c4) ∷ []) Eq.refl

private
  q235 : Ws → Eqn
  q235 c4 = eqn (Bx0-3412 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ Bx0-3412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at13243142 c4)

-- auto BOX(0;1234) | BOX(1;0234) @0113243042: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0113243042 : Ws → ⟪ (Bx1-3402 ∷ Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Bx1-3402 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0113243042 c4 = derive (Bx1-3402 ∷ Bx3-1402 ∷ []) (Bx3-1402 ∷ Bx1-3402 ∷ [])
  (rw⁻ 0 (q87 c4) ∷
   rw 1 (q224 c4) ∷
   rw 2 (q198 c4) ∷
   rw 1 (q235 c4) ∷
   rw 0 (q178 c4) ∷
   rw 1 (q200 c4) ∷
   rw 2 (q87 c4) ∷ []) Eq.refl

private
  q236 : Ws → Eqn
  q236 c4 = eqn (Bx1-3402 ∷ Bx3-1402 ∷ []) (Bx3-1402 ∷ Bx1-3402 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0113243042 c4)

-- auto BOX(0;1234) | BOX(1;0234) @0213243041: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ Bx2-3401 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0213243041 c4 = derive (Bx2-3401 ∷ Bx3-2401 ∷ []) (Bx3-2401 ∷ Bx2-3401 ∷ [])
  (rw⁻ 0 (q66 c4) ∷
   rw 1 (q227 c4) ∷
   rw 2 (q201 c4) ∷
   rw 1 (q236 c4) ∷
   rw 0 (q181 c4) ∷
   rw 1 (q203 c4) ∷
   rw 2 (q66 c4) ∷ []) Eq.refl

-- auto BOX(0;1234) | BOX(1;0234) @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0110243243 c4 = derive (Bx1-0423 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Bx1-0423 ∷ [])
  (rw⁻ 0 (q87 c4) ∷
   rw 1 (q189 c4) ∷
   rw 2 (q191 c4) ∷
   rw 1 (q233 c4) ∷
   rw 0 (q189 c4) ∷
   rw 1 (q191 c4) ∷
   rw 2 (q87 c4) ∷ []) Eq.refl

private
  q237 : Ws → Eqn
  q237 c4 = eqn (Bx1-0423 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0110243243 c4)

-- auto BOX(0;1234) | BOX(1;0234) @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0210243143 c4 = derive (Bx2-0413 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ Bx2-0413 ∷ [])
  (rw⁻ 0 (q66 c4) ∷
   rw 1 (q192 c4) ∷
   rw 2 (q68 c4) ∷
   rw 1 (q237 c4) ∷
   rw 0 (q70 c4) ∷
   rw 1 (q194 c4) ∷
   rw 2 (q66 c4) ∷ []) Eq.refl

private
  q238 : Ws → Eqn
  q238 c4 = eqn (Bx2-0413 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0210243143 c4)

-- auto BOX(0;1234) | BOX(1;0234) @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0310243142 c4 = derive (Bx3-0412 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ Bx3-0412 ∷ [])
  (rw⁻ 0 (q54 c4) ∷
   rw 1 (q195 c4) ∷
   rw 2 (q73 c4) ∷
   rw 1 (q238 c4) ∷
   rw 0 (q75 c4) ∷
   rw 1 (q197 c4) ∷
   rw 2 (q54 c4) ∷ []) Eq.refl

private
  q239 : Ws → Eqn
  q239 c4 = eqn (Bx3-0412 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0310243142 c4)

-- auto BOX(0;1234) | BOX(1;0234) @03243042: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at03243042 : Ws → ⟪ (Bx3-1402 ∷ Bx1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ Bx3-1402 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at03243042 c4 = derive (Bx3-1402 ∷ Bx1-3402 ∷ []) (Bx1-3402 ∷ Bx3-1402 ∷ [])
  (rw⁻ 0 (q87 c4) ∷
   rw 1 (q198 c4) ∷
   rw 2 (q224 c4) ∷
   rw 1 (q239 c4) ∷
   rw 0 (q200 c4) ∷
   rw 1 (q178 c4) ∷
   rw 2 (q87 c4) ∷ []) Eq.refl

private
  q240 : Ws → Eqn
  q240 c4 = eqn (Bx3-1402 ∷ Bx1-3402 ∷ []) (Bx1-3402 ∷ Bx3-1402 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at03243042 c4)

-- auto BOX(0;1234) | BOX(1;0234) @0312243041: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Bx3-2401 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0312243041 c4 = derive (Bx3-2401 ∷ Bx2-3401 ∷ []) (Bx2-3401 ∷ Bx3-2401 ∷ [])
  (rw⁻ 0 (q66 c4) ∷
   rw 1 (q201 c4) ∷
   rw 2 (q227 c4) ∷
   rw 1 (q240 c4) ∷
   rw 0 (q203 c4) ∷
   rw 1 (q181 c4) ∷
   rw 2 (q66 c4) ∷ []) Eq.refl

private
  q241 : Ws → Eqn
  q241 c4 = eqn (Bx3-0412 ∷ Bx3-0412 ∷ []) [] (lem-beta-inv-at0310243142 c4)

-- beta-inv @03243042: 5 steps
lem-beta-inv-at03243042 : Ws → ⟪ (Bx3-1402 ∷ Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at03243042 c4 = derive (Bx3-1402 ∷ Bx3-1402 ∷ []) []
  (rw⁻ 0 (q87 c4) ∷
   rw 1 (q198 c4) ∷
   rw 2 (q198 c4) ∷
   rw 1 (q241 c4) ∷
   rw 0 (q87 c4) ∷ []) Eq.refl

private
  q242 : Ws → Eqn
  q242 c4 = eqn (Bx3-1402 ∷ Bx3-1402 ∷ []) [] (lem-beta-inv-at03243042 c4)

-- beta-inv @0312243041: 5 steps
lem-beta-inv-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at0312243041 c4 = derive (Bx3-2401 ∷ Bx3-2401 ∷ []) []
  (rw⁻ 0 (q66 c4) ∷
   rw 1 (q201 c4) ∷
   rw 2 (q201 c4) ∷
   rw 1 (q242 c4) ∷
   rw 0 (q66 c4) ∷ []) Eq.refl

private
  q243 : Ws → Eqn
  q243 c4 = eqn (Toff234 ∷ Toff234 ∷ []) [] (wl0620 (lit c4))
  q244 : Ws → Eqn
  q244 c4 = eqn (Toff234 ∷ []) (Toff234 ∷ []) (wl0621 (lit c4))
  q245 : Ws → Eqn
  q245 c4 = eqn (Bx3-0214 ∷ []) (Bx3-0241 ∷ []) (lem-sym34-at031031 c4)
  q246 : Ws → Eqn
  q246 c4 = eqn (Bx3-0241 ∷ []) (Bx3-2041 ∷ []) (lem-sym12-at03103441 c4)
  q247 : Ws → Eqn
  q247 c4 = eqn (Bx3-2041 ∷ []) (Bx3-2401 ∷ []) (lem-sym23-at0312203441 c4)
  q248 : Ws → Eqn
  q248 c4 = eqn (Toff234 ∷ Bx3-2401 ∷ Toff234 ∷ []) (Bx3-2401 ∷ Bx2-3401 ∷ []) (lem-TW-at0312243041 c4)
  q249 : Ws → Eqn
  q249 c4 = eqn (Bx3-2401 ∷ []) (Bx3-2041 ∷ []) (lem-sym23-at0312243041 c4)
  q250 : Ws → Eqn
  q250 c4 = eqn (Bx3-2041 ∷ []) (Bx3-2014 ∷ []) (lem-sym34-at0312203441 c4)
  q251 : Ws → Eqn
  q251 c4 = eqn (Bx3-2014 ∷ []) (Bx3-0214 ∷ []) (lem-sym12-at03122031 c4)
  q252 : Ws → Eqn
  q252 c4 = eqn (Bx3-0214 ∷ []) (Bx3-0124 ∷ []) (lem-sym23-at031031 c4)
  q253 : Ws → Eqn
  q253 c4 = eqn (Bx3-0124 ∷ Bx2-3401 ∷ []) (Bx2-3401 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03102132 c4)
  q254 : Ws → Eqn
  q254 c4 = eqn (Toff324 ∷ []) (Toff324 ∷ []) (wl0622 (lit c4))
  q255 : Ws → Eqn
  q255 c4 = eqn (Toff324 ∷ Bx2-3401 ∷ Toff324 ∷ []) (Bx2-3401 ∷ Bx3-2401 ∷ []) (lem-TW-at0213243041 c4)
  q256 : Ws → Eqn
  q256 c4 = eqn (Bx2-3401 ∷ Bx3-2401 ∷ []) (Bx3-2401 ∷ Bx2-3401 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0213243041 c4)
  q257 : Ws → Eqn
  q257 c4 = eqn (Bx3-2401 ∷ Bx2-3401 ∷ []) (Bx2-3401 ∷ Bx3-2401 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0312243041 c4)
  q258 : Ws → Eqn
  q258 c4 = eqn (Bx3-2401 ∷ Bx3-2401 ∷ []) [] (lem-beta-inv-at0312243041 c4)
  q259 : Ws → Eqn
  q259 c4 = eqn (Bx2-3401 ∷ []) (Bx2-3041 ∷ []) (lem-sym23-at0213243041 c4)
  q260 : Ws → Eqn
  q260 c4 = eqn (Bx2-3041 ∷ []) (Bx2-3014 ∷ []) (lem-sym34-at0213203441 c4)
  q261 : Ws → Eqn
  q261 c4 = eqn (Bx2-3014 ∷ []) (Bx2-0314 ∷ []) (lem-sym12-at02132031 c4)
  q262 : Ws → Eqn
  q262 c4 = eqn (Bx2-0314 ∷ []) (Bx2-0134 ∷ []) (lem-sym23-at02102331 c4)
  q263 : Ws → Eqn
  q263 c4 = eqn (Toff324 ∷ Toff234 ∷ Toff234 ∷ Toff324 ∷ []) [] (wl0623 (lit c4))
  q264 : Ws → Eqn
  q264 c4 = eqn (Bx2-0134 ∷ []) (Bx2-0134 ∷ []) (lem-boxify-4-nf-of-rhs c4)

-- boxify-4: 31 steps
lem-boxify-4 : Ws → ⟪ (Toff324 ∷ Toff234 ∷ Bx3-0124 ∷ Toff234 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-boxify-4 c4 = derive (Toff324 ∷ Toff234 ∷ Bx3-0124 ∷ Toff234 ∷ Toff324 ∷ []) (Bx2-0134 ∷ [])
  (rw⁻ 2 (q243 c4) ∷
   rw 3 (q244 c4) ∷
   rw 5 (q244 c4) ∷
   rw 4 (q214 c4) ∷
   rw 4 (q245 c4) ∷
   rw 4 (q246 c4) ∷
   rw 4 (q247 c4) ∷
   rw 3 (q248 c4) ∷
   rw 3 (q249 c4) ∷
   rw 3 (q250 c4) ∷
   rw 3 (q251 c4) ∷
   rw 3 (q252 c4) ∷
   rw 3 (q253 c4) ∷
   rw 4 (q103 c4) ∷
   rw⁻ 3 (q104 c4) ∷
   rw 4 (q254 c4) ∷
   rw 6 (q254 c4) ∷
   rw 4 (q255 c4) ∷
   rw 4 (q256 c4) ∷
   rw 4 (q257 c4) ∷
   rw 6 (q214 c4) ∷
   rw 6 (q245 c4) ∷
   rw 6 (q246 c4) ∷
   rw 6 (q247 c4) ∷
   rw 5 (q258 c4) ∷
   rw 4 (q259 c4) ∷
   rw 4 (q260 c4) ∷
   rw 4 (q261 c4) ∷
   rw 4 (q262 c4) ∷
   rw 0 (q263 c4) ∷
   rw⁻ 0 (q264 c4) ∷ []) Eq.refl

private
  q265 : Ws → Eqn
  q265 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4))
  q266 : Ws → Eqn
  q266 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl0084 (lit c4))
  q267 : Ws → Eqn
  q267 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 (lit c4))
  q268 : Ws → Eqn
  q268 c4 = eqn (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4))

-- auto CCZ012 | CCZ342 @0210243143: 7 steps
lem-auto-CCZ012-∣-CCZ342-at0210243143 : Ws → ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at0210243143 c4 = derive (CCZ024 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q66 c4) ∷
   rw 1 (q265 c4) ∷
   rw⁻ 2 (q266 c4) ∷
   rw 1 (q163 c4) ∷
   rw⁻ 0 (q267 c4) ∷
   rw 1 (q268 c4) ∷
   rw 2 (q66 c4) ∷ []) Eq.refl

private
  q269 : Ws → Eqn
  q269 c4 = eqn (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4))
  q270 : Ws → Eqn
  q270 c4 = eqn (Sw23 ∷ CCZ124 ∷ []) (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4))
  q271 : Ws → Eqn
  q271 c4 = eqn (CCZ024 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0210243143 c4)
  q272 : Ws → Eqn
  q272 c4 = eqn (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 (lit c4))

-- auto CCZ012 | CCZ342 @0310243142: 7 steps
lem-auto-CCZ012-∣-CCZ342-at0310243142 : Ws → ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at0310243142 c4 = derive (CCZ034 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q54 c4) ∷
   rw 1 (q269 c4) ∷
   rw 2 (q270 c4) ∷
   rw 1 (q271 c4) ∷
   rw 0 (q123 c4) ∷
   rw 1 (q272 c4) ∷
   rw 2 (q54 c4) ∷ []) Eq.refl

private
  q273 : Ws → Eqn
  q273 c4 = eqn (Bx3-1204 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-beta-T-at0330 c4)
  q274 : Ws → Eqn
  q274 c4 = eqn (Toff312 ∷ Toff312 ∷ []) [] (wl0230 (lit c4))
  q275 : Ws → Eqn
  q275 c4 = eqn (Toff312 ∷ Bx0-1234 ∷ Toff312 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ []) (lem-T312-beta c4)
  q276 : Ws → Eqn
  q276 c4 = eqn (Bx0-1234 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124 c4)
  q277 : Ws → Eqn
  q277 c4 = eqn (Bx0-1234 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ304 c4)
  q278 : Ws → Eqn
  q278 c4 = eqn (CCZ124 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ124 ∷ []) (wl0624 (lit c4))
  q279 : Ws → Eqn
  q279 c4 = eqn (CCZ034 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0310243142 c4)

-- auto BOX(0;1234) | BOX(3;1204): 15 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·1204⟩ : Ws → ⟪ (Bx0-1234 ∷ Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·1204⟩ c4 = derive (Bx0-1234 ∷ Bx3-1204 ∷ []) (Bx3-1204 ∷ Bx0-1234 ∷ [])
  (rw 1 (q273 c4) ∷
   rw⁻ 0 (q274 c4) ∷
   rw 1 (q275 c4) ∷
   rw 1 (q276 c4) ∷
   rw 2 (q277 c4) ∷
   rw⁻ 3 (q274 c4) ∷
   rw 4 (q275 c4) ∷
   rw 4 (q276 c4) ∷
   rw 5 (q277 c4) ∷
   rw⁻ 0 (q278 c4) ∷
   rw⁻ 3 (q278 c4) ∷
   rw 2 (q279 c4) ∷
   rw⁻ 1 (q278 c4) ∷
   rw 0 (q137 c4) ∷
   rw⁻ 0 (q273 c4) ∷ []) Eq.refl

-- boxify-5 [nf of rhs]: 0 steps
lem-boxify-5-nf-of-rhs : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-boxify-5-nf-of-rhs c4 = refl

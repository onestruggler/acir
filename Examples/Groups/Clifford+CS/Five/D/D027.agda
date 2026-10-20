{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D027 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym-ab-at0210243143 ; lem-sym-ab-at0214203143 ; lem-sym-ab-at0310243142 ; lem-sym-ab-at0314203142 ; lem-sym-ab-at122441 ; lem-sym-ab-at13213442 ; lem-sym-ab-at233442 ; lem-sym-ab-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym-ab-at0314213240 ; lem-sym-ab-at03243240 ; lem-sym-ab-at14213243 ; lem-sym-ab-at1441)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-tQ-at0310213442)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at0210233441 ; lem-box-tQ-at033440 ; lem-box-tQ-at12213443 ; lem-box-tQ-at12233441 ; lem-box-tQ-at13213442 ; lem-box-tQ-at233442)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-box-tQ-at02233440 ; lem-box-tQ-at03103441 ; lem-box-tQ-at0312203441 ; lem-box-tQ-at03143140)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-sym-bc-at14233241)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-Xb-box-at13243142 ; lem-box-cP-at0310243142 ; lem-box-cP-at03243240 ; lem-box-cP-at122441 ; lem-box-perm-1324-at0310213442 ; lem-box-perm-1324-at13243142 ; lem-sym-bc-at0214213043 ; lem-sym-bc-at0314203142 ; lem-sym-bc-at0314213042 ; lem-sym-bc-at03243240 ; lem-sym-bc-at033440 ; lem-sym-bc-at143143)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-Xb-box-at122441 ; lem-box-perm-1324-at122441 ; lem-pairs-at13213442 ; lem-pairs-at143143)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-pairs-at0210233441)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-pairs-at12233441 ; lem-pairs-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-CSdu-box-3-at03143140 ; lem-CXu-box-4-at243243 ; lem-Xb-box-at02102441 ; lem-Xb-box-at022440 ; lem-Xb-box-at0310243142 ; lem-Xb-box-at0310243241 ; lem-Xb-box-at0312243041 ; lem-Xb-box-at03243240 ; lem-Xb-box-at12243143 ; lem-Xb-box-at2442 ; lem-box-perm-1324-at0210233441 ; lem-box-perm-1324-at02102441 ; lem-box-perm-1324-at02233440 ; lem-box-perm-1324-at022440 ; lem-box-perm-1324-at0310243142 ; lem-box-perm-1324-at0310243241 ; lem-box-perm-1324-at03103441 ; lem-box-perm-1324-at0312203441 ; lem-box-perm-1324-at0312243041 ; lem-box-perm-1324-at03243240 ; lem-box-perm-1324-at033440 ; lem-box-perm-1324-at12213443 ; lem-box-perm-1324-at12233441 ; lem-box-perm-1324-at12243143 ; lem-box-perm-1324-at13213442 ; lem-box-perm-1324-at233442 ; lem-box-perm-1324-at2442 ; lem-box2-at0310243142 ; lem-box2-at03243240 ; lem-nf-comm-CS-S1at2 ; lem-pairs-at0214203143 ; lem-pairs-at02233440 ; lem-pairs-at03103441 ; lem-pairs-at0312203441 ; lem-pairs-at0314203142 ; lem-pairs-at0314213042 ; lem-pairs-at0314213240 ; lem-pairs-at033440 ; lem-pairs-at12213443 ; lem-pairs-at1441 ; lem-pairs-at233442)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX02-CCZ134 ; lem-comm-CX12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ014-CX23 ; lem-comm-CCZ024-CX13 ; lem-comm-CCZ024-CX31 ; lem-comm-CCZ034-CX12 ; lem-comm-CCZ034-CX21 ; lem-comm-CCZ124-CX03 ; lem-comm-CCZ134-CX02 ; lem-comm-CX04-TOFF312 ; lem-comm-CX14-TOFF302 ; lem-comm-TOFF013-CK42 ; lem-comm-TOFF013-CX24 ; lem-comm-TOFF024-CS13 ; lem-comm-TOFF213-CK40)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CCZ134-CX20 ; lem-comm-TOFF301-CK42 ; lem-comm-TOFF312-CK40)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF023-CK41 ; lem-comm-TOFF203-CK41 ; lem-comm-TOFF302-CK41)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx0-2431 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Toff013 ∷ Toff134 ∷ []) (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp 843 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CCZ024 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp 845 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) (wl 241 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ024 ∷ K1 ∷ []) (K1 ∷ CCZ024 ∷ []) (wp 89 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) (wp 36 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ024 ∷ CX13 ∷ []) (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) (wp 35 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) (wp 34 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ024 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ024 ∷ []) (wp 88 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Toff013 ∷ Toff034 ∷ []) (Toff034 ∷ Toff013 ∷ []) (wp 97 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl 245 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (CS34 ∷ Toff013 ∷ []) (Toff013 ∷ CS34 ∷ []) (wp 95 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Toff013 ∷ CX24 ∷ []) (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (CS34⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS34⁻ ∷ []) (wp 94 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CS23 ∷ Toff013 ∷ []) (Toff013 ∷ CS23 ∷ []) (wl 246 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ234 ∷ []) (Toff034 ∷ CCZ234 ∷ Toff034 ∷ []) (wp 842 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ024 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ024 ∷ []) (wp 90 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CS12 ∷ Toff013 ∷ []) (Toff013 ∷ CS12 ∷ []) (wl 247 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ024 ∷ CS12 ∷ []) (CS12 ∷ CCZ024 ∷ []) (wp 81 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CS12⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS12⁻ ∷ []) (wl 244 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ024 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ024 ∷ []) (wp 87 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ234 ∷ Toff134 ∷ CS12 ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl 1037 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ234 ∷ CCZ234 ∷ []) [] (wl 305 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CS34 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ []) (wl 1118 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS34 ∷ Sb0-2-43-1 ∷ []) (CS34 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (lem-nf-comm-CS-S1at2 c4)

-- F1-comm-CS-S1@2: 91 steps
lem-F1-comm-CS-S1at2 : Ws → ⟪ (Sb0-2-43-1 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-comm-CS-S1at2 c4 = derive (Sb0-2-43-1 ∷ CS34 ∷ []) (CS34 ∷ Sb0-2-43-1 ∷ [])
  (re 0 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 2 1 (CS12 ∷ []) ∷
   re 4 1 (CS12⁻ ∷ []) ∷
   rw 0 (q1 c4) ∷
   rw 3 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw 4 (q4 c4) ∷
   rw 1 (q11 c4) ∷
   rw 3 (q12 c4) ∷
   rw⁻ 2 (q13 c4) ∷
   rw 3 (q14 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   rw 5 (q14 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   rw⁻ 2 (q12 c4) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 1 (q17 c4) ∷
   rw 0 (q18 c4) ∷
   rw⁻ 2 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   rw 3 (q7 c4) ∷
   rw 4 (q8 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q9 c4) ∷
   rw 7 (q10 c4) ∷
   rw 1 (q4 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw 4 (q20 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw 2 (q20 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw 6 (q2 c4) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q6 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q8 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q9 c4) ∷
   rw 13 (q10 c4) ∷
   rw 7 (q4 c4) ∷
   rw 4 (q11 c4) ∷
   rw 6 (q12 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw 8 (q14 c4) ∷
   rw⁻ 9 (q16 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   rw 6 (q2 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 3 (q18 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw 4 (q4 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 8 (q21 c4) ∷
   rw 7 (q22 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw 5 (q22 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw 8 (q6 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw 0 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   rw⁻ 0 (q25 c4) ∷
   rw⁻ 0 (q26 c4) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = eqn (Bx2-0413 ∷ []) (Bx2-4013 ∷ []) (lem-sym-ab-at0210243143 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (Bx2-4013 ∷ []) (Bx2-1340 ∷ []) (lem-pairs-at0214203143 c4)

-- box-perm-3421 @0210243143: 2 steps
lem-box-perm-3421-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-box-perm-3421-at0210243143 c4 = derive (Bx2-0413 ∷ []) (Bx2-1340 ∷ [])
  (rw 0 (q27 c4) ∷
   rw 0 (q28 c4) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ013 ∷ CCZ013 ∷ []) [] (wl 230 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (Bx2-1340 ∷ []) (Bx2-1430 ∷ []) (lem-box-perm-1324-at02233440 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (X4 ∷ Bx2-1430 ∷ X4 ∷ []) (Bx2-1430 ∷ CCZ013 ∷ []) (lem-Xb-box-at022440 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CCZ013 ∷ CK40 ∷ CCZ013 ∷ CCZ013 ∷ []) (CCZ013 ∷ CK40 ∷ []) (wp 925 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))
  q34 : Ws → Eqn
  q34 c4 = eqn (K0 ∷ CK40 ∷ S4 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ []) (wp 610 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (Bx2-1430 ∷ []) (Bx2-1340 ∷ []) (lem-box-perm-1324-at022440 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Bx2-1340 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02233440 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl 289 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CCZ024 ∷ CS03 ∷ []) (CS03 ∷ CCZ024 ∷ []) (wp 21 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ []) (wp 32 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ024 ∷ CS01 ∷ []) (CS01 ∷ CCZ024 ∷ []) (wp 39 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ024 ∷ K0 ∷ []) (K0 ∷ Toff024 ∷ CCZ024 ∷ CCZ024 ∷ []) (wp 926 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ024 ∷ CK40 ∷ []) (CZ02 ∷ CK40 ∷ CZ02 ∷ CCZ024 ∷ []) (wp 927 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ024 ∷ S4 ∷ []) (S4 ∷ CCZ024 ∷ []) (wp 617 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ Toff024 ∷ CCZ024 ∷ CZ02 ∷ CK40 ∷ CZ02 ∷ S4 ∷ []) (wp 928 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ013 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ013 ∷ []) (wl 186 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (K0 ∷ Toff213 ∷ []) (Toff213 ∷ K0 ∷ []) (c₁ (K) (K ↑ • CCZ • K ↑ • iI))
  q47 : Ws → Eqn
  q47 c4 = eqn (Toff213 ∷ CK40 ∷ []) (CK40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CK40 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (Toff213 ∷ S4 ∷ []) (S4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (S))
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ013 ∷ CK40 ∷ CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ []) (wp 929 c4)

-- CKc-box @02233440: 61 steps
lem-CKc-box-at02233440 : Ws → ⟪ (Bx2-1340 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CK40 ∷ CCZ013 ∷ Bx2-1340 ∷ []) ⟫ʷ
lem-CKc-box-at02233440 c4 = derive (Bx2-1340 ∷ CK40 ∷ []) (CCZ013 ∷ CK40 ∷ CCZ013 ∷ Bx2-1340 ∷ [])
  (rw⁻ 1 (q29 c4) ∷
   rw 0 (q30 c4) ∷
   rw⁻ 0 (q31 c4) ∷
   rw⁻ 3 (q32 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   rw⁻ 3 (q34 c4) ∷
   rw⁻ 6 (q33 c4) ∷
   rw 1 (q35 c4) ∷
   rw 1 (q36 c4) ∷
   rw 5 (q37 c4) ∷
   rw 4 (q38 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q39 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q40 c4) ∷
   rw⁻ 4 (q37 c4) ∷
   rw 5 (q41 c4) ∷
   rw 8 (q42 c4) ∷
   rw 11 (q43 c4) ∷
   rw 13 (q37 c4) ∷
   rw 12 (q38 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q39 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q40 c4) ∷
   rw⁻ 12 (q37 c4) ∷
   rw⁻ 5 (q44 c4) ∷
   rw⁻ 3 (q45 c4) ∷
   rw⁻ 4 (q46 c4) ∷
   rw 5 (q47 c4) ∷
   rw 6 (q48 c4) ∷
   rw⁻ 7 (q45 c4) ∷
   rw 3 (q37 c4) ∷
   rw 2 (q38 c4) ∷
   rw 3 (q7 c4) ∷
   rw 4 (q39 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q40 c4) ∷
   rw⁻ 2 (q37 c4) ∷
   rw 3 (q41 c4) ∷
   rw 6 (q42 c4) ∷
   rw 9 (q43 c4) ∷
   rw 11 (q37 c4) ∷
   rw 10 (q38 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q39 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q40 c4) ∷
   rw⁻ 10 (q37 c4) ∷
   rw⁻ 3 (q44 c4) ∷
   rw⁻ 1 (q45 c4) ∷
   rw⁻ 2 (q46 c4) ∷
   rw 3 (q47 c4) ∷
   rw 4 (q48 c4) ∷
   rw⁻ 5 (q45 c4) ∷
   rw⁻ 6 (q36 c4) ∷
   rw⁻ 6 (q35 c4) ∷
   rw⁻ 0 (q49 c4) ∷
   rw 3 (q31 c4) ∷
   rw 4 (q29 c4) ∷
   rw 3 (q35 c4) ∷ []) Eq.refl

private
  q50 : Ws → Eqn
  q50 c4 = eqn (Bx2-1340 ∷ []) (Bx2-4013 ∷ []) (lem-pairs-at02233440 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (Bx2-4013 ∷ []) (Bx2-0413 ∷ []) (lem-sym-ab-at0214203143 c4)

-- box-perm-4312 @02233440: 2 steps
lem-box-perm-4312-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-box-perm-4312-at02233440 c4 = derive (Bx2-1340 ∷ []) (Bx2-0413 ∷ [])
  (rw 0 (q50 c4) ∷
   rw 0 (q51 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = eqn (Bx0-1423 ∷ []) (Bx0-4123 ∷ []) (lem-sym-ab-at243243 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (Bx0-4123 ∷ []) (Bx0-2341 ∷ []) (lem-pairs-at14213243 c4)

-- box-perm-3421 @243243: 2 steps
lem-box-perm-3421-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-box-perm-3421-at243243 c4 = derive (Bx0-1423 ∷ []) (Bx0-2341 ∷ [])
  (rw 0 (q52 c4) ∷
   rw 0 (q53 c4) ∷ []) Eq.refl

private
  q54 : Ws → Eqn
  q54 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl 181 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (Bx0-2341 ∷ []) (Bx0-2431 ∷ []) (lem-box-perm-1324-at12233441 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (X4 ∷ Bx0-2431 ∷ X4 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ []) (lem-Xb-box-at122441 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (CCZ123 ∷ CK41 ∷ CCZ123 ∷ CCZ123 ∷ []) (CCZ123 ∷ CK41 ∷ []) (wl 1139 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) (c₄ (CCZ ↑) (X))
  q59 : Ws → Eqn
  q59 c4 = eqn (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ []) (wl 720 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (Bx0-2431 ∷ []) (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (Bx0-2341 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at12233441 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (CCZ123 ∷ []) (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (wl 233 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (CCZ014 ∷ CS13 ∷ []) (CS13 ∷ CCZ014 ∷ []) (wp 53 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (CCZ014 ∷ CX23 ∷ []) (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (CCZ014 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ014 ∷ []) (wp 60 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ014 ∷ CS12 ∷ []) (CS12 ∷ CCZ014 ∷ []) (wp 67 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (CCZ014 ∷ K1 ∷ []) (K1 ∷ Toff104 ∷ CCZ014 ∷ CCZ014 ∷ []) (wp 933 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (CCZ014 ∷ CK41 ∷ []) (CZ01 ∷ CK41 ∷ CZ01 ∷ CCZ014 ∷ []) (wp 934 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (CCZ014 ∷ S4 ∷ []) (S4 ∷ CCZ014 ∷ []) (wp 633 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (K1 ∷ CK41 ∷ S4 ∷ []) (K1 ∷ Toff104 ∷ CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ S4 ∷ []) (wp 935 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ123 ∷ []) (wl 209 (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (K1 ∷ Toff023 ∷ []) (Toff023 ∷ K1 ∷ []) (wl 735 (lit c4))
  q73 : Ws → Eqn
  q73 c4 = eqn (Toff023 ∷ CK41 ∷ []) (CK41 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CK41 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (Toff023 ∷ S4 ∷ []) (S4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (S))
  q75 : Ws → Eqn
  q75 c4 = eqn (CCZ123 ∷ CK41 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ []) (wl 1140 (lit c4))

-- CKc-box @12233441: 61 steps
lem-CKc-box-at12233441 : Ws → ⟪ (Bx0-2341 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK41 ∷ CCZ123 ∷ Bx0-2341 ∷ []) ⟫ʷ
lem-CKc-box-at12233441 c4 = derive (Bx0-2341 ∷ CK41 ∷ []) (CCZ123 ∷ CK41 ∷ CCZ123 ∷ Bx0-2341 ∷ [])
  (rw⁻ 1 (q54 c4) ∷
   rw 0 (q55 c4) ∷
   rw⁻ 0 (q56 c4) ∷
   rw⁻ 3 (q57 c4) ∷
   rw⁻ 2 (q58 c4) ∷
   rw⁻ 3 (q59 c4) ∷
   rw⁻ 6 (q58 c4) ∷
   rw 1 (q60 c4) ∷
   rw 1 (q61 c4) ∷
   rw 5 (q62 c4) ∷
   rw 4 (q63 c4) ∷
   rw 5 (q64 c4) ∷
   rw 6 (q65 c4) ∷
   rw 7 (q64 c4) ∷
   rw 8 (q66 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw 5 (q67 c4) ∷
   rw 8 (q68 c4) ∷
   rw 11 (q69 c4) ∷
   rw 13 (q62 c4) ∷
   rw 12 (q63 c4) ∷
   rw 13 (q64 c4) ∷
   rw 14 (q65 c4) ∷
   rw 15 (q64 c4) ∷
   rw 16 (q66 c4) ∷
   rw⁻ 12 (q62 c4) ∷
   rw⁻ 5 (q70 c4) ∷
   rw⁻ 3 (q71 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   rw 5 (q73 c4) ∷
   rw 6 (q74 c4) ∷
   rw⁻ 7 (q71 c4) ∷
   rw 3 (q62 c4) ∷
   rw 2 (q63 c4) ∷
   rw 3 (q64 c4) ∷
   rw 4 (q65 c4) ∷
   rw 5 (q64 c4) ∷
   rw 6 (q66 c4) ∷
   rw⁻ 2 (q62 c4) ∷
   rw 3 (q67 c4) ∷
   rw 6 (q68 c4) ∷
   rw 9 (q69 c4) ∷
   rw 11 (q62 c4) ∷
   rw 10 (q63 c4) ∷
   rw 11 (q64 c4) ∷
   rw 12 (q65 c4) ∷
   rw 13 (q64 c4) ∷
   rw 14 (q66 c4) ∷
   rw⁻ 10 (q62 c4) ∷
   rw⁻ 3 (q70 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw⁻ 2 (q72 c4) ∷
   rw 3 (q73 c4) ∷
   rw 4 (q74 c4) ∷
   rw⁻ 5 (q71 c4) ∷
   rw⁻ 6 (q61 c4) ∷
   rw⁻ 6 (q60 c4) ∷
   rw⁻ 0 (q75 c4) ∷
   rw 3 (q56 c4) ∷
   rw 4 (q54 c4) ∷
   rw 3 (q60 c4) ∷ []) Eq.refl

private
  q76 : Ws → Eqn
  q76 c4 = eqn (Bx0-2341 ∷ []) (Bx0-4123 ∷ []) (lem-pairs-at12233441 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (Bx0-4123 ∷ []) (Bx0-1423 ∷ []) (lem-sym-ab-at14213243 c4)

-- box-perm-4312 @12233441: 2 steps
lem-box-perm-4312-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-4312-at12233441 c4 = derive (Bx0-2341 ∷ []) (Bx0-1423 ∷ [])
  (rw 0 (q76 c4) ∷
   rw 0 (q77 c4) ∷ []) Eq.refl

private
  q78 : Ws → Eqn
  q78 c4 = eqn (Bx0-2431 ∷ []) (Bx0-4231 ∷ []) (lem-sym-ab-at122441 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (Bx0-4231 ∷ []) (Bx0-3142 ∷ []) (lem-pairs-at1441 c4)

-- box-perm-3421 @122441: 2 steps
lem-box-perm-3421-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-box-perm-3421-at122441 c4 = derive (Bx0-2431 ∷ []) (Bx0-3142 ∷ [])
  (rw 0 (q78 c4) ∷
   rw 0 (q79 c4) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = eqn (Bx0-3142 ∷ []) (Bx0-3412 ∷ []) (lem-box-perm-1324-at13213442 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (X4 ∷ Bx0-3412 ∷ X4 ∷ []) (Bx0-3412 ∷ CCZ123 ∷ []) (lem-Xb-box-at13243142 c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ []) (CCZ123 ∷ CK42 ∷ []) (wl 1144 (lit c4))
  q83 : Ws → Eqn
  q83 c4 = eqn (K2 ∷ CK42 ∷ S4 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ []) (wl 725 (lit c4))
  q84 : Ws → Eqn
  q84 c4 = eqn (Bx0-3412 ∷ []) (Bx0-3142 ∷ []) (lem-box-perm-1324-at13243142 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (Bx0-3142 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at13213442 c4)
  q86 : Ws → Eqn
  q86 c4 = eqn (CCZ123 ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl 297 (lit c4))
  q87 : Ws → Eqn
  q87 c4 = eqn (CCZ024 ∷ CX31 ∷ []) (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4))
  q88 : Ws → Eqn
  q88 c4 = eqn (CCZ024 ∷ CS23 ∷ []) (CS23 ∷ CCZ024 ∷ []) (wp 92 c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (CCZ024 ∷ K2 ∷ []) (K2 ∷ Toff204 ∷ CCZ024 ∷ CCZ024 ∷ []) (wp 936 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (CCZ024 ∷ CK42 ∷ []) (CZ02 ∷ CK42 ∷ CZ02 ∷ CCZ024 ∷ []) (wp 937 c4)
  q91 : Ws → Eqn
  q91 c4 = eqn (K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ Toff204 ∷ CCZ024 ∷ CZ02 ∷ CK42 ∷ CZ02 ∷ S4 ∷ []) (wp 938 c4)
  q92 : Ws → Eqn
  q92 c4 = eqn (CCZ123 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ123 ∷ []) (wl 234 (lit c4))
  q93 : Ws → Eqn
  q93 c4 = eqn (K2 ∷ Toff013 ∷ []) (Toff013 ∷ K2 ∷ []) (wl 743 (lit c4))
  q94 : Ws → Eqn
  q94 c4 = eqn (Toff013 ∷ CK42 ∷ []) (CK42 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CK42 (lit c4))
  q95 : Ws → Eqn
  q95 c4 = eqn (Toff013 ∷ S4 ∷ []) (S4 ∷ Toff013 ∷ []) (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (S))
  q96 : Ws → Eqn
  q96 c4 = eqn (CCZ123 ∷ CK42 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ []) (wl 1145 (lit c4))

-- CKc-box @13213442: 61 steps
lem-CKc-box-at13213442 : Ws → ⟪ (Bx0-3142 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-3142 ∷ []) ⟫ʷ
lem-CKc-box-at13213442 c4 = derive (Bx0-3142 ∷ CK42 ∷ []) (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-3142 ∷ [])
  (rw⁻ 1 (q54 c4) ∷
   rw 0 (q80 c4) ∷
   rw⁻ 0 (q81 c4) ∷
   rw⁻ 3 (q82 c4) ∷
   rw⁻ 2 (q58 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   rw⁻ 6 (q58 c4) ∷
   rw 1 (q84 c4) ∷
   rw 1 (q85 c4) ∷
   rw 5 (q86 c4) ∷
   rw 4 (q20 c4) ∷
   rw 5 (q87 c4) ∷
   rw 6 (q22 c4) ∷
   rw 7 (q87 c4) ∷
   rw 8 (q88 c4) ∷
   rw⁻ 4 (q86 c4) ∷
   rw 5 (q89 c4) ∷
   rw 8 (q90 c4) ∷
   rw 11 (q43 c4) ∷
   rw 13 (q86 c4) ∷
   rw 12 (q20 c4) ∷
   rw 13 (q87 c4) ∷
   rw 14 (q22 c4) ∷
   rw 15 (q87 c4) ∷
   rw 16 (q88 c4) ∷
   rw⁻ 12 (q86 c4) ∷
   rw⁻ 5 (q91 c4) ∷
   rw⁻ 3 (q92 c4) ∷
   rw⁻ 4 (q93 c4) ∷
   rw 5 (q94 c4) ∷
   rw 6 (q95 c4) ∷
   rw⁻ 7 (q92 c4) ∷
   rw 3 (q86 c4) ∷
   rw 2 (q20 c4) ∷
   rw 3 (q87 c4) ∷
   rw 4 (q22 c4) ∷
   rw 5 (q87 c4) ∷
   rw 6 (q88 c4) ∷
   rw⁻ 2 (q86 c4) ∷
   rw 3 (q89 c4) ∷
   rw 6 (q90 c4) ∷
   rw 9 (q43 c4) ∷
   rw 11 (q86 c4) ∷
   rw 10 (q20 c4) ∷
   rw 11 (q87 c4) ∷
   rw 12 (q22 c4) ∷
   rw 13 (q87 c4) ∷
   rw 14 (q88 c4) ∷
   rw⁻ 10 (q86 c4) ∷
   rw⁻ 3 (q91 c4) ∷
   rw⁻ 1 (q92 c4) ∷
   rw⁻ 2 (q93 c4) ∷
   rw 3 (q94 c4) ∷
   rw 4 (q95 c4) ∷
   rw⁻ 5 (q92 c4) ∷
   rw⁻ 6 (q85 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   rw⁻ 0 (q96 c4) ∷
   rw 3 (q81 c4) ∷
   rw 4 (q54 c4) ∷
   rw 3 (q84 c4) ∷ []) Eq.refl

private
  q97 : Ws → Eqn
  q97 c4 = eqn (Bx0-3142 ∷ []) (Bx0-4231 ∷ []) (lem-pairs-at13213442 c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (Bx0-4231 ∷ []) (Bx0-2431 ∷ []) (lem-sym-ab-at1441 c4)

-- box-perm-4312 @13213442: 2 steps
lem-box-perm-4312-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-4312-at13213442 c4 = derive (Bx0-3142 ∷ []) (Bx0-2431 ∷ [])
  (rw 0 (q97 c4) ∷
   rw 0 (q98 c4) ∷ []) Eq.refl

private
  q99 : Ws → Eqn
  q99 c4 = eqn (Bx2-0341 ∷ []) (Bx2-0431 ∷ []) (lem-box-perm-1324-at0210233441 c4)
  q100 : Ws → Eqn
  q100 c4 = eqn (X4 ∷ Bx2-0431 ∷ X4 ∷ []) (Bx2-0431 ∷ CCZ013 ∷ []) (lem-Xb-box-at02102441 c4)
  q101 : Ws → Eqn
  q101 c4 = eqn (CCZ013 ∷ CK41 ∷ CCZ013 ∷ CCZ013 ∷ []) (CCZ013 ∷ CK41 ∷ []) (wp 951 c4)
  q102 : Ws → Eqn
  q102 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-box-perm-1324-at02102441 c4)
  q103 : Ws → Eqn
  q103 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-box-tQ-at0210233441 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (CCZ013 ∷ []) (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl 905 (lit c4))
  q105 : Ws → Eqn
  q105 c4 = eqn (CCZ124 ∷ CS13 ∷ []) (CS13 ∷ CCZ124 ∷ []) (wl 1152 (lit c4))
  q106 : Ws → Eqn
  q106 c4 = eqn (CCZ124 ∷ CX03 ∷ []) (CX03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CX03 (lit c4))
  q107 : Ws → Eqn
  q107 c4 = eqn (CCZ124 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ124 ∷ []) (wl 1151 (lit c4))
  q108 : Ws → Eqn
  q108 c4 = eqn (CCZ124 ∷ CS01 ∷ []) (CS01 ∷ CCZ124 ∷ []) (wp 919 c4)
  q109 : Ws → Eqn
  q109 c4 = eqn (CCZ124 ∷ K1 ∷ []) (K1 ∷ Toff124 ∷ CCZ124 ∷ CCZ124 ∷ []) (wl 1159 (lit c4))
  q110 : Ws → Eqn
  q110 c4 = eqn (CCZ124 ∷ CK41 ∷ []) (CZ12 ∷ CK41 ∷ CZ12 ∷ CCZ124 ∷ []) (wl 1160 (lit c4))
  q111 : Ws → Eqn
  q111 c4 = eqn (CCZ124 ∷ S4 ∷ []) (S4 ∷ CCZ124 ∷ []) (wl 1161 (lit c4))
  q112 : Ws → Eqn
  q112 c4 = eqn (K1 ∷ CK41 ∷ S4 ∷ []) (K1 ∷ Toff124 ∷ CCZ124 ∷ CZ12 ∷ CK41 ∷ CZ12 ∷ S4 ∷ []) (wl 1162 (lit c4))
  q113 : Ws → Eqn
  q113 c4 = eqn (CCZ013 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ013 ∷ []) (wl 1131 (lit c4))
  q114 : Ws → Eqn
  q114 c4 = eqn (K1 ∷ Toff203 ∷ []) (Toff203 ∷ K1 ∷ []) (wl 1163 (lit c4))
  q115 : Ws → Eqn
  q115 c4 = eqn (Toff203 ∷ CK41 ∷ []) (CK41 ∷ Toff203 ∷ []) (lem-comm-TOFF203-CK41 (lit c4))
  q116 : Ws → Eqn
  q116 c4 = eqn (Toff203 ∷ S4 ∷ []) (S4 ∷ Toff203 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (S))
  q117 : Ws → Eqn
  q117 c4 = eqn (CCZ013 ∷ CK41 ∷ CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ []) (wp 952 c4)

-- CKc-box @0210233441: 61 steps
lem-CKc-box-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CK41 ∷ CCZ013 ∷ Bx2-0341 ∷ []) ⟫ʷ
lem-CKc-box-at0210233441 c4 = derive (Bx2-0341 ∷ CK41 ∷ []) (CCZ013 ∷ CK41 ∷ CCZ013 ∷ Bx2-0341 ∷ [])
  (rw⁻ 1 (q29 c4) ∷
   rw 0 (q99 c4) ∷
   rw⁻ 0 (q100 c4) ∷
   rw⁻ 3 (q101 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   rw⁻ 3 (q59 c4) ∷
   rw⁻ 6 (q33 c4) ∷
   rw 1 (q102 c4) ∷
   rw 1 (q103 c4) ∷
   rw 5 (q104 c4) ∷
   rw 4 (q105 c4) ∷
   rw 5 (q106 c4) ∷
   rw 6 (q107 c4) ∷
   rw 7 (q106 c4) ∷
   rw 8 (q108 c4) ∷
   rw⁻ 4 (q104 c4) ∷
   rw 5 (q109 c4) ∷
   rw 8 (q110 c4) ∷
   rw 11 (q111 c4) ∷
   rw 13 (q104 c4) ∷
   rw 12 (q105 c4) ∷
   rw 13 (q106 c4) ∷
   rw 14 (q107 c4) ∷
   rw 15 (q106 c4) ∷
   rw 16 (q108 c4) ∷
   rw⁻ 12 (q104 c4) ∷
   rw⁻ 5 (q112 c4) ∷
   rw⁻ 3 (q113 c4) ∷
   rw⁻ 4 (q114 c4) ∷
   rw 5 (q115 c4) ∷
   rw 6 (q116 c4) ∷
   rw⁻ 7 (q113 c4) ∷
   rw 3 (q104 c4) ∷
   rw 2 (q105 c4) ∷
   rw 3 (q106 c4) ∷
   rw 4 (q107 c4) ∷
   rw 5 (q106 c4) ∷
   rw 6 (q108 c4) ∷
   rw⁻ 2 (q104 c4) ∷
   rw 3 (q109 c4) ∷
   rw 6 (q110 c4) ∷
   rw 9 (q111 c4) ∷
   rw 11 (q104 c4) ∷
   rw 10 (q105 c4) ∷
   rw 11 (q106 c4) ∷
   rw 12 (q107 c4) ∷
   rw 13 (q106 c4) ∷
   rw 14 (q108 c4) ∷
   rw⁻ 10 (q104 c4) ∷
   rw⁻ 3 (q112 c4) ∷
   rw⁻ 1 (q113 c4) ∷
   rw⁻ 2 (q114 c4) ∷
   rw 3 (q115 c4) ∷
   rw 4 (q116 c4) ∷
   rw⁻ 5 (q113 c4) ∷
   rw⁻ 6 (q103 c4) ∷
   rw⁻ 6 (q102 c4) ∷
   rw⁻ 0 (q117 c4) ∷
   rw 3 (q100 c4) ∷
   rw 4 (q29 c4) ∷
   rw 3 (q102 c4) ∷ []) Eq.refl

private
  q118 : Ws → Eqn
  q118 c4 = eqn (Bx2-0341 ∷ []) (Bx2-4103 ∷ []) (lem-pairs-at0210233441 c4)
  q119 : Ws → Eqn
  q119 c4 = eqn (Bx2-4103 ∷ []) (Bx2-4013 ∷ []) (lem-sym-bc-at0214213043 c4)

-- box-perm-1342 @0210233441: 3 steps
lem-box-perm-1342-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-box-perm-1342-at0210233441 c4 = derive (Bx2-0341 ∷ []) (Bx2-0413 ∷ [])
  (rw 0 (q118 c4) ∷
   rw 0 (q119 c4) ∷
   rw 0 (q51 c4) ∷ []) Eq.refl

private
  q120 : Ws → Eqn
  q120 c4 = eqn (Bx0-1342 ∷ []) (Bx0-1432 ∷ []) (lem-box-perm-1324-at233442 c4)
  q121 : Ws → Eqn
  q121 c4 = eqn (X4 ∷ Bx0-1432 ∷ X4 ∷ []) (Bx0-1432 ∷ CCZ123 ∷ []) (lem-Xb-box-at2442 c4)
  q122 : Ws → Eqn
  q122 c4 = eqn (Bx0-1432 ∷ []) (Bx0-1342 ∷ []) (lem-box-perm-1324-at2442 c4)
  q123 : Ws → Eqn
  q123 c4 = eqn (Bx0-1342 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at233442 c4)
  q124 : Ws → Eqn
  q124 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl 242 (lit c4))
  q125 : Ws → Eqn
  q125 c4 = eqn (CCZ024 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ024 ∷ []) (wp 91 c4)

-- CKc-box @233442: 61 steps
lem-CKc-box-at233442 : Ws → ⟪ (Bx0-1342 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-1342 ∷ []) ⟫ʷ
lem-CKc-box-at233442 c4 = derive (Bx0-1342 ∷ CK42 ∷ []) (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-1342 ∷ [])
  (rw⁻ 1 (q54 c4) ∷
   rw 0 (q120 c4) ∷
   rw⁻ 0 (q121 c4) ∷
   rw⁻ 3 (q82 c4) ∷
   rw⁻ 2 (q58 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   rw⁻ 6 (q58 c4) ∷
   rw 1 (q122 c4) ∷
   rw 1 (q123 c4) ∷
   rw 5 (q124 c4) ∷
   rw 4 (q88 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q125 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q20 c4) ∷
   rw⁻ 4 (q124 c4) ∷
   rw 5 (q89 c4) ∷
   rw 8 (q90 c4) ∷
   rw 11 (q43 c4) ∷
   rw 13 (q124 c4) ∷
   rw 12 (q88 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q125 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q20 c4) ∷
   rw⁻ 12 (q124 c4) ∷
   rw⁻ 5 (q91 c4) ∷
   rw⁻ 3 (q92 c4) ∷
   rw⁻ 4 (q93 c4) ∷
   rw 5 (q94 c4) ∷
   rw 6 (q95 c4) ∷
   rw⁻ 7 (q92 c4) ∷
   rw 3 (q124 c4) ∷
   rw 2 (q88 c4) ∷
   rw 3 (q7 c4) ∷
   rw 4 (q125 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q20 c4) ∷
   rw⁻ 2 (q124 c4) ∷
   rw 3 (q89 c4) ∷
   rw 6 (q90 c4) ∷
   rw 9 (q43 c4) ∷
   rw 11 (q124 c4) ∷
   rw 10 (q88 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q125 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q20 c4) ∷
   rw⁻ 10 (q124 c4) ∷
   rw⁻ 3 (q91 c4) ∷
   rw⁻ 1 (q92 c4) ∷
   rw⁻ 2 (q93 c4) ∷
   rw 3 (q94 c4) ∷
   rw 4 (q95 c4) ∷
   rw⁻ 5 (q92 c4) ∷
   rw⁻ 6 (q123 c4) ∷
   rw⁻ 6 (q122 c4) ∷
   rw⁻ 0 (q96 c4) ∷
   rw 3 (q121 c4) ∷
   rw 4 (q54 c4) ∷
   rw 3 (q122 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = eqn (Bx0-1342 ∷ []) (Bx0-4213 ∷ []) (lem-pairs-at233442 c4)
  q127 : Ws → Eqn
  q127 c4 = eqn (Bx0-4213 ∷ []) (Bx0-4123 ∷ []) (lem-sym-bc-at143143 c4)

-- box-perm-1342 @233442: 3 steps
lem-box-perm-1342-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-1342-at233442 c4 = derive (Bx0-1342 ∷ []) (Bx0-1423 ∷ [])
  (rw 0 (q126 c4) ∷
   rw 0 (q127 c4) ∷
   rw 0 (q77 c4) ∷ []) Eq.refl

private
  q128 : Ws → Eqn
  q128 c4 = eqn (Bx0-2143 ∷ []) (Bx0-2413 ∷ []) (lem-box-perm-1324-at12213443 c4)
  q129 : Ws → Eqn
  q129 c4 = eqn (X4 ∷ Bx0-2413 ∷ X4 ∷ []) (Bx0-2413 ∷ CCZ123 ∷ []) (lem-Xb-box-at12243143 c4)
  q130 : Ws → Eqn
  q130 c4 = eqn (CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ123 ∷ []) (CCZ123 ∷ CK43 ∷ []) (wl 1172 (lit c4))
  q131 : Ws → Eqn
  q131 c4 = eqn (K3 ∷ CK43 ∷ S4 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ []) (wl 729 (lit c4))
  q132 : Ws → Eqn
  q132 c4 = eqn (Bx0-2413 ∷ []) (Bx0-2143 ∷ []) (lem-box-perm-1324-at12243143 c4)
  q133 : Ws → Eqn
  q133 c4 = eqn (Bx0-2143 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at12213443 c4)
  q134 : Ws → Eqn
  q134 c4 = eqn (CCZ123 ∷ []) (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl 326 (lit c4))
  q135 : Ws → Eqn
  q135 c4 = eqn (CCZ034 ∷ CS13 ∷ []) (CS13 ∷ CCZ034 ∷ []) (wp 312 c4)
  q136 : Ws → Eqn
  q136 c4 = eqn (CCZ034 ∷ CX21 ∷ []) (CX21 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX21 (lit c4))
  q137 : Ws → Eqn
  q137 c4 = eqn (CCZ034 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ034 ∷ []) (wp 734 c4)
  q138 : Ws → Eqn
  q138 c4 = eqn (CCZ034 ∷ CS23 ∷ []) (CS23 ∷ CCZ034 ∷ []) (wp 314 c4)
  q139 : Ws → Eqn
  q139 c4 = eqn (CCZ034 ∷ K3 ∷ []) (K3 ∷ Toff304 ∷ CCZ034 ∷ CCZ034 ∷ []) (wp 979 c4)
  q140 : Ws → Eqn
  q140 c4 = eqn (CCZ034 ∷ CK43 ∷ []) (CZ03 ∷ CK43 ∷ CZ03 ∷ CCZ034 ∷ []) (wp 980 c4)
  q141 : Ws → Eqn
  q141 c4 = eqn (CCZ034 ∷ S4 ∷ []) (S4 ∷ CCZ034 ∷ []) (wp 981 c4)
  q142 : Ws → Eqn
  q142 c4 = eqn (K3 ∷ CK43 ∷ S4 ∷ []) (K3 ∷ Toff304 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ S4 ∷ []) (wp 982 c4)
  q143 : Ws → Eqn
  q143 c4 = eqn (CCZ123 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ123 ∷ []) (wl 464 (lit c4))
  q144 : Ws → Eqn
  q144 c4 = eqn (Toff012 ∷ K3 ∷ []) (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K))
  q145 : Ws → Eqn
  q145 c4 = eqn (Toff012 ∷ CK43 ∷ []) (CK43 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₁₀))
  q146 : Ws → Eqn
  q146 c4 = eqn (Toff012 ∷ S4 ∷ []) (S4 ∷ Toff012 ∷ []) (c₃ (Toff) (S ↑))
  q147 : Ws → Eqn
  q147 c4 = eqn (CCZ123 ∷ CK43 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ []) (wl 1173 (lit c4))

-- CKc-box @12213443: 61 steps
lem-CKc-box-at12213443 : Ws → ⟪ (Bx0-2143 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-2143 ∷ []) ⟫ʷ
lem-CKc-box-at12213443 c4 = derive (Bx0-2143 ∷ CK43 ∷ []) (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-2143 ∷ [])
  (rw⁻ 1 (q54 c4) ∷
   rw 0 (q128 c4) ∷
   rw⁻ 0 (q129 c4) ∷
   rw⁻ 3 (q130 c4) ∷
   rw⁻ 2 (q58 c4) ∷
   rw⁻ 3 (q131 c4) ∷
   rw⁻ 6 (q58 c4) ∷
   rw 1 (q132 c4) ∷
   rw 1 (q133 c4) ∷
   rw 5 (q134 c4) ∷
   rw 4 (q135 c4) ∷
   rw 5 (q136 c4) ∷
   rw 6 (q137 c4) ∷
   rw 7 (q136 c4) ∷
   rw 8 (q138 c4) ∷
   rw⁻ 4 (q134 c4) ∷
   rw 5 (q139 c4) ∷
   rw 8 (q140 c4) ∷
   rw 11 (q141 c4) ∷
   rw 13 (q134 c4) ∷
   rw 12 (q135 c4) ∷
   rw 13 (q136 c4) ∷
   rw 14 (q137 c4) ∷
   rw 15 (q136 c4) ∷
   rw 16 (q138 c4) ∷
   rw⁻ 12 (q134 c4) ∷
   rw⁻ 5 (q142 c4) ∷
   rw⁻ 3 (q143 c4) ∷
   rw 4 (q144 c4) ∷
   rw 5 (q145 c4) ∷
   rw 6 (q146 c4) ∷
   rw⁻ 7 (q143 c4) ∷
   rw 3 (q134 c4) ∷
   rw 2 (q135 c4) ∷
   rw 3 (q136 c4) ∷
   rw 4 (q137 c4) ∷
   rw 5 (q136 c4) ∷
   rw 6 (q138 c4) ∷
   rw⁻ 2 (q134 c4) ∷
   rw 3 (q139 c4) ∷
   rw 6 (q140 c4) ∷
   rw 9 (q141 c4) ∷
   rw 11 (q134 c4) ∷
   rw 10 (q135 c4) ∷
   rw 11 (q136 c4) ∷
   rw 12 (q137 c4) ∷
   rw 13 (q136 c4) ∷
   rw 14 (q138 c4) ∷
   rw⁻ 10 (q134 c4) ∷
   rw⁻ 3 (q142 c4) ∷
   rw⁻ 1 (q143 c4) ∷
   rw 2 (q144 c4) ∷
   rw 3 (q145 c4) ∷
   rw 4 (q146 c4) ∷
   rw⁻ 5 (q143 c4) ∷
   rw⁻ 6 (q133 c4) ∷
   rw⁻ 6 (q132 c4) ∷
   rw⁻ 0 (q147 c4) ∷
   rw 3 (q129 c4) ∷
   rw 4 (q54 c4) ∷
   rw 3 (q132 c4) ∷ []) Eq.refl

private
  q148 : Ws → Eqn
  q148 c4 = eqn (Bx0-2143 ∷ []) (Bx0-4321 ∷ []) (lem-pairs-at12213443 c4)
  q149 : Ws → Eqn
  q149 c4 = eqn (Bx0-4321 ∷ []) (Bx0-4231 ∷ []) (lem-sym-bc-at14233241 c4)

-- box-perm-1342 @12213443: 3 steps
lem-box-perm-1342-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-1342-at12213443 c4 = derive (Bx0-2143 ∷ []) (Bx0-2431 ∷ [])
  (rw 0 (q148 c4) ∷
   rw 0 (q149 c4) ∷
   rw 0 (q98 c4) ∷ []) Eq.refl

private
  q150 : Ws → Eqn
  q150 c4 = eqn (Bx0-4213 ∷ []) (Bx0-1342 ∷ []) (lem-pairs-at143143 c4)
  q151 : Ws → Eqn
  q151 c4 = eqn (Bx0-1342 ∷ []) (Bx0-3142 ∷ []) (lem-sym-ab-at233442 c4)

-- box-perm-4312 @143143: 2 steps
lem-box-perm-4312-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-box-perm-4312-at143143 c4 = derive (Bx0-4213 ∷ []) (Bx0-3142 ∷ [])
  (rw 0 (q150 c4) ∷
   rw 0 (q151 c4) ∷ []) Eq.refl

private
  q152 : Ws → Eqn
  q152 c4 = eqn (Bx0-3142 ∷ []) (Bx0-1342 ∷ []) (lem-sym-ab-at13213442 c4)

-- box-perm-3421 @13213442: 2 steps
lem-box-perm-3421-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-box-perm-3421-at13213442 c4 = derive (Bx0-3142 ∷ []) (Bx0-4213 ∷ [])
  (rw 0 (q152 c4) ∷
   rw 0 (q126 c4) ∷ []) Eq.refl

private
  q153 : Ws → Eqn
  q153 c4 = eqn (CX03 ∷ Toff324 ∷ []) (Toff324 ∷ CX03 ∷ []) (wp 1009 c4)
  q154 : Ws → Eqn
  q154 c4 = eqn (CS13 ∷ CS01 ∷ CCZ013 ∷ CX03 ∷ []) (CX03 ∷ CS13 ∷ []) (wl 1195 (lit c4))
  q155 : Ws → Eqn
  q155 c4 = eqn (CS13⁻ ∷ CS01⁻ ∷ CCZ013 ∷ CX03 ∷ []) (CX03 ∷ CS13⁻ ∷ []) (wl 1196 (lit c4))
  q156 : Ws → Eqn
  q156 c4 = eqn (CCZ013 ∷ CS01 ∷ []) (CS01 ∷ CCZ013 ∷ []) (wl 1197 (lit c4))
  q157 : Ws → Eqn
  q157 c4 = eqn (CS01 ∷ Toff324 ∷ []) (Toff324 ∷ CS01 ∷ []) (c₂ (CS) (K ↑ • CCZ • K ↑ • iI))
  q158 : Ws → Eqn
  q158 c4 = eqn (CS01 ∷ CS13⁻ ∷ CS01⁻ ∷ []) (CS13⁻ ∷ []) (wl 1198 (lit c4))
  q159 : Ws → Eqn
  q159 c4 = eqn (Toff324 ∷ Toff324 ∷ []) [] (wl 442 (lit c4))
  q160 : Ws → Eqn
  q160 c4 = eqn (CCZ013 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ013 ∷ []) (wl 1199 (lit c4))
  q161 : Ws → Eqn
  q161 c4 = eqn (Bx3-4210 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at03143140 c4)
  q162 : Ws → Eqn
  q162 c4 = eqn (CS13⁻ ∷ Bx3-4210 ∷ []) (Bx3-4210 ∷ CS13⁻ ∷ []) (lem-CSdu-box-3-at03143140 c4)

-- F0-R @01143043: 11 steps
lem-F0-R-at01143043 : Ws → ⟪ (CX03 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Bx3-4210 ∷ CX03 ∷ []) ⟫ʷ
lem-F0-R-at01143043 c4 = derive (CX03 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Bx3-4210 ∷ CX03 ∷ [])
  (rw 0 (q153 c4) ∷
   rw⁻ 1 (q154 c4) ∷
   rw 4 (q153 c4) ∷
   rw⁻ 5 (q155 c4) ∷
   rw⁻ 2 (q156 c4) ∷
   rw 3 (q157 c4) ∷
   rw 4 (q158 c4) ∷
   rw⁻ 2 (q159 c4) ∷
   rw⁻ 6 (q160 c4) ∷
   rw⁻ 3 (q161 c4) ∷
   rw⁻ 3 (q162 c4) ∷ []) Eq.refl

private
  q163 : Ws → Eqn
  q163 c4 = eqn (CX30 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CX30 ∷ []) (lem-CXu-box-4-at243243 c4)
  q164 : Ws → Eqn
  q164 c4 = eqn (CX30 ∷ Toff324 ∷ []) (Toff324 ∷ CX30 ∷ Toff024 ∷ []) (wp 1012 c4)
  q165 : Ws → Eqn
  q165 c4 = eqn (Toff024 ∷ CS13 ∷ []) (CS13 ∷ Toff024 ∷ []) (lem-comm-TOFF024-CS13 (lit c4))
  q166 : Ws → Eqn
  q166 c4 = eqn (CS13 ∷ CX30 ∷ []) (CX30 ∷ CS13 ∷ []) (wl 1208 (lit c4))
  q167 : Ws → Eqn
  q167 c4 = eqn (CX30 ∷ Toff024 ∷ Toff324 ∷ []) (Toff324 ∷ CX30 ∷ []) (wp 1013 c4)
  q168 : Ws → Eqn
  q168 c4 = eqn (CS13⁻ ∷ CX30 ∷ []) (CX30 ∷ CS13⁻ ∷ []) (wl 1209 (lit c4))

-- CXAu-S @01143043: 12 steps
lem-CXAu-S-at01143043 : Ws → ⟪ (CX30 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CX30 ∷ []) ⟫ʷ
lem-CXAu-S-at01143043 c4 = derive (CX30 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CX30 ∷ [])
  (re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 0 (q163 c4) ∷
   rw 1 (q164 c4) ∷
   rw 3 (q165 c4) ∷
   rw⁻ 2 (q166 c4) ∷
   rw 3 (q167 c4) ∷
   rw⁻ 4 (q168 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q169 : Ws → Eqn
  q169 c4 = eqn (Bx3-0412 ∷ []) (Bx3-4012 ∷ []) (lem-sym-ab-at0310243142 c4)
  q170 : Ws → Eqn
  q170 c4 = eqn (Bx3-4012 ∷ []) (Bx3-1240 ∷ []) (lem-pairs-at0314203142 c4)
  q171 : Ws → Eqn
  q171 c4 = eqn (Bx3-1240 ∷ []) (Bx3-1420 ∷ []) (lem-sym-bc-at033440 c4)

-- box-perm-3241 @0310243142: 3 steps
lem-box-perm-3241-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-box-perm-3241-at0310243142 c4 = derive (Bx3-0412 ∷ []) (Bx3-1420 ∷ [])
  (rw 0 (q169 c4) ∷
   rw 0 (q170 c4) ∷
   rw 0 (q171 c4) ∷ []) Eq.refl

private
  q172 : Ws → Eqn
  q172 c4 = eqn (Bx3-1420 ∷ []) (Bx3-1240 ∷ []) (lem-sym-bc-at03243240 c4)
  q173 : Ws → Eqn
  q173 c4 = eqn (Bx3-1240 ∷ []) (Bx3-4012 ∷ []) (lem-pairs-at033440 c4)
  q174 : Ws → Eqn
  q174 c4 = eqn (Bx3-4012 ∷ []) (Bx3-0412 ∷ []) (lem-sym-ab-at0314203142 c4)

-- box-perm-4213 @03243240: 3 steps
lem-box-perm-4213-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-box-perm-4213-at03243240 c4 = derive (Bx3-1420 ∷ []) (Bx3-0412 ∷ [])
  (rw 0 (q172 c4) ∷
   rw 0 (q173 c4) ∷
   rw 0 (q174 c4) ∷ []) Eq.refl

private
  q175 : Ws → Eqn
  q175 c4 = eqn (Bx3-1420 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4)
  q176 : Ws → Eqn
  q176 c4 = eqn (CCZ134 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ134 ∷ []) (wp 1027 c4)
  q177 : Ws → Eqn
  q177 c4 = eqn (CS01⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS01⁻ ∷ []) (wl 1224 (lit c4))
  q178 : Ws → Eqn
  q178 c4 = eqn (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (Toff024 ∷ []) (wp 1026 c4)
  q179 : Ws → Eqn
  q179 c4 = eqn (K0⁻ ∷ CCZ134 ∷ []) (CCZ134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q180 : Ws → Eqn
  q180 c4 = eqn (CCZ134 ∷ CS04 ∷ []) (CS04 ∷ CCZ134 ∷ []) (wp 1003 c4)
  q181 : Ws → Eqn
  q181 c4 = eqn (CX02 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4))
  q182 : Ws → Eqn
  q182 c4 = eqn (CCZ134 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ134 ∷ []) (wl 1221 (lit c4))
  q183 : Ws → Eqn
  q183 c4 = eqn (CCZ134 ∷ CS24 ∷ []) (CS24 ∷ CCZ134 ∷ []) (wl 1220 (lit c4))
  q184 : Ws → Eqn
  q184 c4 = eqn (K0 ∷ CCZ134 ∷ []) (CCZ134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q185 : Ws → Eqn
  q185 c4 = eqn (Toff024 ∷ Toff302 ∷ []) (Toff302 ∷ Toff024 ∷ Toff324 ∷ []) (wp 1004 c4)
  q186 : Ws → Eqn
  q186 c4 = eqn (CCZ134 ∷ Toff324 ∷ CCZ124 ∷ []) (Toff324 ∷ CCZ134 ∷ []) (wl 1189 (lit c4))
  q187 : Ws → Eqn
  q187 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl 220 (lit c4))
  q188 : Ws → Eqn
  q188 c4 = eqn (CS12 ∷ Toff302 ∷ []) (Toff302 ∷ CS12 ∷ []) (wl 1190 (lit c4))
  q189 : Ws → Eqn
  q189 c4 = eqn (CX14 ∷ Toff302 ∷ []) (Toff302 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF302 (lit c4))
  q190 : Ws → Eqn
  q190 c4 = eqn (CS24⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS24⁻ ∷ []) (wp 1005 c4)
  q191 : Ws → Eqn
  q191 c4 = eqn (CS24 ∷ Toff302 ∷ []) (Toff302 ∷ CS24 ∷ []) (wp 1006 c4)
  q192 : Ws → Eqn
  q192 c4 = eqn (Toff302 ∷ Toff324 ∷ []) (Toff324 ∷ Toff302 ∷ []) (wp 1007 c4)
  q193 : Ws → Eqn
  q193 c4 = eqn (Toff024 ∷ Toff324 ∷ Toff324 ∷ []) (Toff024 ∷ []) (wp 1008 c4)
  q194 : Ws → Eqn
  q194 c4 = eqn (CCZ134 ∷ CS01 ∷ []) (CS01 ∷ CCZ134 ∷ []) (wp 261 c4)
  q195 : Ws → Eqn
  q195 c4 = eqn (CS01 ∷ Toff302 ∷ []) (Toff302 ∷ CS01 ∷ []) (wl 1223 (lit c4))
  q196 : Ws → Eqn
  q196 c4 = eqn (Bx3-1420 ∷ Bx3-1420 ∷ []) [] (lem-box2-at03243240 c4)
  q197 : Ws → Eqn
  q197 c4 = eqn (CCZ124 ∷ CS01 ∷ Toff024 ∷ []) (CS01 ∷ Toff024 ∷ CCZ124 ∷ []) (wp 1042 c4)
  q198 : Ws → Eqn
  q198 c4 = eqn (CCZ124 ∷ CCZ124 ∷ []) [] (wl 263 (lit c4))
  q199 : Ws → Eqn
  q199 c4 = eqn (CCZ124 ∷ []) (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (wp 1047 c4)

-- S2-SBOX(3;1;42;0): 86 steps
lem-S2-SBOX⟨3·1·42·0⟩ : Ws → ⟪ (Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
lem-S2-SBOX⟨3·1·42·0⟩ c4 = derive (Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ []) (CCZ124 ∷ [])
  (re 1 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) ∷
   re 3 1 (CS01 ∷ []) ∷
   re 5 1 (CS01⁻ ∷ []) ∷
   re 0 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) ∷
   re 2 1 (CS01 ∷ []) ∷
   re 4 1 (CS01⁻ ∷ []) ∷
   rw 5 (q175 c4) ∷
   rw⁻ 4 (q176 c4) ∷
   rw 5 (q177 c4) ∷
   rw⁻ 6 (q176 c4) ∷
   rw 7 (q177 c4) ∷
   rw⁻ 4 (q175 c4) ∷
   rw 4 (q175 c4) ∷
   rw⁻ 3 (q178 c4) ∷
   rw 9 (q179 c4) ∷
   rw⁻ 8 (q180 c4) ∷
   rw 7 (q181 c4) ∷
   rw⁻ 6 (q182 c4) ∷
   rw 5 (q181 c4) ∷
   rw⁻ 4 (q183 c4) ∷
   rw 3 (q184 c4) ∷
   rw 4 (q178 c4) ∷
   rw 4 (q185 c4) ∷
   rw⁻ 6 (q186 c4) ∷
   rw⁻ 5 (q178 c4) ∷
   rw 11 (q179 c4) ∷
   rw⁻ 10 (q180 c4) ∷
   rw 9 (q181 c4) ∷
   rw⁻ 8 (q182 c4) ∷
   rw 7 (q181 c4) ∷
   rw⁻ 6 (q183 c4) ∷
   rw 5 (q184 c4) ∷
   rw 6 (q178 c4) ∷
   rw 8 (q187 c4) ∷
   rw 12 (q188 c4) ∷
   rw 11 (q189 c4) ∷
   rw 10 (q190 c4) ∷
   rw 9 (q189 c4) ∷
   rw 8 (q191 c4) ∷
   rw⁻ 9 (q187 c4) ∷
   rw⁻ 7 (q192 c4) ∷
   rw 6 (q185 c4) ∷
   rw 7 (q193 c4) ∷
   rw⁻ 3 (q175 c4) ∷
   rw 3 (q175 c4) ∷
   rw⁻ 2 (q194 c4) ∷
   rw 3 (q195 c4) ∷
   rw⁻ 4 (q194 c4) ∷
   rw 5 (q195 c4) ∷
   rw⁻ 2 (q175 c4) ∷
   rw 2 (q175 c4) ∷
   rw⁻ 1 (q178 c4) ∷
   rw 7 (q179 c4) ∷
   rw⁻ 6 (q180 c4) ∷
   rw 5 (q181 c4) ∷
   rw⁻ 4 (q182 c4) ∷
   rw 3 (q181 c4) ∷
   rw⁻ 2 (q183 c4) ∷
   rw 1 (q184 c4) ∷
   rw 2 (q178 c4) ∷
   rw 2 (q185 c4) ∷
   rw⁻ 4 (q186 c4) ∷
   rw⁻ 3 (q178 c4) ∷
   rw 9 (q179 c4) ∷
   rw⁻ 8 (q180 c4) ∷
   rw 7 (q181 c4) ∷
   rw⁻ 6 (q182 c4) ∷
   rw 5 (q181 c4) ∷
   rw⁻ 4 (q183 c4) ∷
   rw 3 (q184 c4) ∷
   rw 4 (q178 c4) ∷
   rw 6 (q187 c4) ∷
   rw 10 (q188 c4) ∷
   rw 9 (q189 c4) ∷
   rw 8 (q190 c4) ∷
   rw 7 (q189 c4) ∷
   rw 6 (q191 c4) ∷
   rw⁻ 7 (q187 c4) ∷
   rw⁻ 5 (q192 c4) ∷
   rw 4 (q185 c4) ∷
   rw 5 (q193 c4) ∷
   rw⁻ 1 (q175 c4) ∷
   rw 0 (q196 c4) ∷
   rw 1 (q197 c4) ∷
   rw 3 (q198 c4) ∷
   rw⁻ 0 (q199 c4) ∷ []) Eq.refl

private
  q200 : Ws → Eqn
  q200 c4 = eqn (Bx3-4012 ∷ []) (Bx3-4102 ∷ []) (lem-sym-bc-at0314203142 c4)
  q201 : Ws → Eqn
  q201 c4 = eqn (Bx3-4102 ∷ []) (Bx3-0241 ∷ []) (lem-pairs-at0314213042 c4)

-- box-perm-1423 @0310243142: 3 steps
lem-box-perm-1423-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-box-perm-1423-at0310243142 c4 = derive (Bx3-0412 ∷ []) (Bx3-0241 ∷ [])
  (rw 0 (q169 c4) ∷
   rw 0 (q200 c4) ∷
   rw 0 (q201 c4) ∷ []) Eq.refl

private
  q202 : Ws → Eqn
  q202 c4 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wl 341 (lit c4))
  q203 : Ws → Eqn
  q203 c4 = eqn (Bx3-0241 ∷ []) (Bx3-0421 ∷ []) (lem-box-perm-1324-at03103441 c4)
  q204 : Ws → Eqn
  q204 c4 = eqn (X4 ∷ Bx3-0421 ∷ X4 ∷ []) (Bx3-0421 ∷ CCZ012 ∷ []) (lem-Xb-box-at0310243241 c4)
  q205 : Ws → Eqn
  q205 c4 = eqn (CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ []) (CCZ012 ∷ CK41 ∷ []) (wp 1061 c4)
  q206 : Ws → Eqn
  q206 c4 = eqn (CCZ012 ∷ X4 ∷ []) (X4 ∷ CCZ012 ∷ []) (c₃ (CCZ) (X ↑))
  q207 : Ws → Eqn
  q207 c4 = eqn (Bx3-0421 ∷ []) (Bx3-0241 ∷ []) (lem-box-perm-1324-at0310243241 c4)
  q208 : Ws → Eqn
  q208 c4 = eqn (Bx3-0241 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at03103441 c4)
  q209 : Ws → Eqn
  q209 c4 = eqn (CCZ012 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl 391 (lit c4))
  q210 : Ws → Eqn
  q210 c4 = eqn (CCZ134 ∷ CS12 ∷ []) (CS12 ∷ CCZ134 ∷ []) (wl 393 (lit c4))
  q211 : Ws → Eqn
  q211 c4 = eqn (CCZ134 ∷ CX02 ∷ []) (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4))
  q212 : Ws → Eqn
  q212 c4 = eqn (CCZ134 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ134 ∷ []) (wl 392 (lit c4))
  q213 : Ws → Eqn
  q213 c4 = eqn (CCZ134 ∷ K1 ∷ []) (K1 ∷ Toff134 ∷ CCZ134 ∷ CCZ134 ∷ []) (wl 1247 (lit c4))
  q214 : Ws → Eqn
  q214 c4 = eqn (CCZ134 ∷ CK41 ∷ []) (CZ13 ∷ CK41 ∷ CZ13 ∷ CCZ134 ∷ []) (wl 1248 (lit c4))
  q215 : Ws → Eqn
  q215 c4 = eqn (CCZ134 ∷ S4 ∷ []) (S4 ∷ CCZ134 ∷ []) (wl 1249 (lit c4))
  q216 : Ws → Eqn
  q216 c4 = eqn (K1 ∷ CK41 ∷ S4 ∷ []) (K1 ∷ Toff134 ∷ CCZ134 ∷ CZ13 ∷ CK41 ∷ CZ13 ∷ S4 ∷ []) (wl 1250 (lit c4))
  q217 : Ws → Eqn
  q217 c4 = eqn (CCZ012 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ012 ∷ []) (wl 1251 (lit c4))
  q218 : Ws → Eqn
  q218 c4 = eqn (K1 ∷ Toff302 ∷ []) (Toff302 ∷ K1 ∷ []) (wl 1252 (lit c4))
  q219 : Ws → Eqn
  q219 c4 = eqn (Toff302 ∷ CK41 ∷ []) (CK41 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CK41 (lit c4))
  q220 : Ws → Eqn
  q220 c4 = eqn (Toff302 ∷ S4 ∷ []) (S4 ∷ Toff302 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (S))
  q221 : Ws → Eqn
  q221 c4 = eqn (CCZ012 ∷ CK41 ∷ CCZ012 ∷ X4 ∷ []) (X4 ∷ CCZ012 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ []) (wp 1062 c4)

-- CKc-box @03103441: 61 steps
lem-CKc-box-at03103441 : Ws → ⟪ (Bx3-0241 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-0241 ∷ []) ⟫ʷ
lem-CKc-box-at03103441 c4 = derive (Bx3-0241 ∷ CK41 ∷ []) (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-0241 ∷ [])
  (rw⁻ 1 (q202 c4) ∷
   rw 0 (q203 c4) ∷
   rw⁻ 0 (q204 c4) ∷
   rw⁻ 3 (q205 c4) ∷
   rw⁻ 2 (q206 c4) ∷
   rw⁻ 3 (q59 c4) ∷
   rw⁻ 6 (q206 c4) ∷
   rw 1 (q207 c4) ∷
   rw 1 (q208 c4) ∷
   rw 5 (q209 c4) ∷
   rw 4 (q210 c4) ∷
   rw 5 (q211 c4) ∷
   rw 6 (q212 c4) ∷
   rw 7 (q211 c4) ∷
   rw 8 (q194 c4) ∷
   rw⁻ 4 (q209 c4) ∷
   rw 5 (q213 c4) ∷
   rw 8 (q214 c4) ∷
   rw 11 (q215 c4) ∷
   rw 13 (q209 c4) ∷
   rw 12 (q210 c4) ∷
   rw 13 (q211 c4) ∷
   rw 14 (q212 c4) ∷
   rw 15 (q211 c4) ∷
   rw 16 (q194 c4) ∷
   rw⁻ 12 (q209 c4) ∷
   rw⁻ 5 (q216 c4) ∷
   rw⁻ 3 (q217 c4) ∷
   rw⁻ 4 (q218 c4) ∷
   rw 5 (q219 c4) ∷
   rw 6 (q220 c4) ∷
   rw⁻ 7 (q217 c4) ∷
   rw 3 (q209 c4) ∷
   rw 2 (q210 c4) ∷
   rw 3 (q211 c4) ∷
   rw 4 (q212 c4) ∷
   rw 5 (q211 c4) ∷
   rw 6 (q194 c4) ∷
   rw⁻ 2 (q209 c4) ∷
   rw 3 (q213 c4) ∷
   rw 6 (q214 c4) ∷
   rw 9 (q215 c4) ∷
   rw 11 (q209 c4) ∷
   rw 10 (q210 c4) ∷
   rw 11 (q211 c4) ∷
   rw 12 (q212 c4) ∷
   rw 13 (q211 c4) ∷
   rw 14 (q194 c4) ∷
   rw⁻ 10 (q209 c4) ∷
   rw⁻ 3 (q216 c4) ∷
   rw⁻ 1 (q217 c4) ∷
   rw⁻ 2 (q218 c4) ∷
   rw 3 (q219 c4) ∷
   rw 4 (q220 c4) ∷
   rw⁻ 5 (q217 c4) ∷
   rw⁻ 6 (q208 c4) ∷
   rw⁻ 6 (q207 c4) ∷
   rw⁻ 0 (q221 c4) ∷
   rw 3 (q204 c4) ∷
   rw 4 (q202 c4) ∷
   rw 3 (q207 c4) ∷ []) Eq.refl

private
  q222 : Ws → Eqn
  q222 c4 = eqn (Bx3-0241 ∷ []) (Bx3-4102 ∷ []) (lem-pairs-at03103441 c4)
  q223 : Ws → Eqn
  q223 c4 = eqn (Bx3-4102 ∷ []) (Bx3-4012 ∷ []) (lem-sym-bc-at0314213042 c4)

-- box-perm-1342 @03103441: 3 steps
lem-box-perm-1342-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-box-perm-1342-at03103441 c4 = derive (Bx3-0241 ∷ []) (Bx3-0412 ∷ [])
  (rw 0 (q222 c4) ∷
   rw 0 (q223 c4) ∷
   rw 0 (q174 c4) ∷ []) Eq.refl

private
  q224 : Ws → Eqn
  q224 c4 = eqn (Bx3-0142 ∷ []) (Bx3-0412 ∷ []) (lem-box-perm-1324-at0310213442 c4)
  q225 : Ws → Eqn
  q225 c4 = eqn (X4 ∷ Bx3-0412 ∷ X4 ∷ []) (Bx3-0412 ∷ CCZ012 ∷ []) (lem-Xb-box-at0310243142 c4)
  q226 : Ws → Eqn
  q226 c4 = eqn (CCZ012 ∷ CK42 ∷ CCZ012 ∷ CCZ012 ∷ []) (CCZ012 ∷ CK42 ∷ []) (wp 1074 c4)
  q227 : Ws → Eqn
  q227 c4 = eqn (Bx3-0412 ∷ []) (Bx3-0142 ∷ []) (lem-box-perm-1324-at0310243142 c4)
  q228 : Ws → Eqn
  q228 c4 = eqn (Bx3-0142 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at0310213442 c4)
  q229 : Ws → Eqn
  q229 c4 = eqn (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl 348 (lit c4))
  q230 : Ws → Eqn
  q230 c4 = eqn (CCZ234 ∷ CS12 ∷ []) (CS12 ∷ CCZ234 ∷ []) (wl 415 (lit c4))
  q231 : Ws → Eqn
  q231 c4 = eqn (CX01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ))
  q232 : Ws → Eqn
  q232 c4 = eqn (CCZ234 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ234 ∷ []) (wl 414 (lit c4))
  q233 : Ws → Eqn
  q233 c4 = eqn (CCZ234 ∷ CS02 ∷ []) (CS02 ∷ CCZ234 ∷ []) (wp 279 c4)
  q234 : Ws → Eqn
  q234 c4 = eqn (CCZ234 ∷ K2 ∷ []) (K2 ∷ Toff234 ∷ CCZ234 ∷ CCZ234 ∷ []) (wl 1261 (lit c4))
  q235 : Ws → Eqn
  q235 c4 = eqn (CCZ234 ∷ CK42 ∷ []) (CZ23 ∷ CK42 ∷ CZ23 ∷ CCZ234 ∷ []) (wl 1262 (lit c4))
  q236 : Ws → Eqn
  q236 c4 = eqn (CCZ234 ∷ S4 ∷ []) (S4 ∷ CCZ234 ∷ []) (wl 1263 (lit c4))
  q237 : Ws → Eqn
  q237 c4 = eqn (K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ Toff234 ∷ CCZ234 ∷ CZ23 ∷ CK42 ∷ CZ23 ∷ S4 ∷ []) (wl 1264 (lit c4))
  q238 : Ws → Eqn
  q238 c4 = eqn (CCZ012 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ012 ∷ []) (wl 1265 (lit c4))
  q239 : Ws → Eqn
  q239 c4 = eqn (K2 ∷ Toff301 ∷ []) (Toff301 ∷ K2 ∷ []) (wl 1266 (lit c4))
  q240 : Ws → Eqn
  q240 c4 = eqn (Toff301 ∷ CK42 ∷ []) (CK42 ∷ Toff301 ∷ []) (lem-comm-TOFF301-CK42 (lit c4))
  q241 : Ws → Eqn
  q241 c4 = eqn (Toff301 ∷ S4 ∷ []) (S4 ∷ Toff301 ∷ []) (c₄ (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) (S))
  q242 : Ws → Eqn
  q242 c4 = eqn (CCZ012 ∷ CK42 ∷ CCZ012 ∷ X4 ∷ []) (X4 ∷ CCZ012 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ012 ∷ []) (wp 1075 c4)

-- CKc-box @0310213442: 61 steps
lem-CKc-box-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CK42 ∷ CCZ012 ∷ Bx3-0142 ∷ []) ⟫ʷ
lem-CKc-box-at0310213442 c4 = derive (Bx3-0142 ∷ CK42 ∷ []) (CCZ012 ∷ CK42 ∷ CCZ012 ∷ Bx3-0142 ∷ [])
  (rw⁻ 1 (q202 c4) ∷
   rw 0 (q224 c4) ∷
   rw⁻ 0 (q225 c4) ∷
   rw⁻ 3 (q226 c4) ∷
   rw⁻ 2 (q206 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   rw⁻ 6 (q206 c4) ∷
   rw 1 (q227 c4) ∷
   rw 1 (q228 c4) ∷
   rw 5 (q229 c4) ∷
   rw 4 (q230 c4) ∷
   rw⁻ 5 (q231 c4) ∷
   rw 6 (q232 c4) ∷
   rw⁻ 7 (q231 c4) ∷
   rw 8 (q233 c4) ∷
   rw⁻ 4 (q229 c4) ∷
   rw 5 (q234 c4) ∷
   rw 8 (q235 c4) ∷
   rw 11 (q236 c4) ∷
   rw 13 (q229 c4) ∷
   rw 12 (q230 c4) ∷
   rw⁻ 13 (q231 c4) ∷
   rw 14 (q232 c4) ∷
   rw⁻ 15 (q231 c4) ∷
   rw 16 (q233 c4) ∷
   rw⁻ 12 (q229 c4) ∷
   rw⁻ 5 (q237 c4) ∷
   rw⁻ 3 (q238 c4) ∷
   rw⁻ 4 (q239 c4) ∷
   rw 5 (q240 c4) ∷
   rw 6 (q241 c4) ∷
   rw⁻ 7 (q238 c4) ∷
   rw 3 (q229 c4) ∷
   rw 2 (q230 c4) ∷
   rw⁻ 3 (q231 c4) ∷
   rw 4 (q232 c4) ∷
   rw⁻ 5 (q231 c4) ∷
   rw 6 (q233 c4) ∷
   rw⁻ 2 (q229 c4) ∷
   rw 3 (q234 c4) ∷
   rw 6 (q235 c4) ∷
   rw 9 (q236 c4) ∷
   rw 11 (q229 c4) ∷
   rw 10 (q230 c4) ∷
   rw⁻ 11 (q231 c4) ∷
   rw 12 (q232 c4) ∷
   rw⁻ 13 (q231 c4) ∷
   rw 14 (q233 c4) ∷
   rw⁻ 10 (q229 c4) ∷
   rw⁻ 3 (q237 c4) ∷
   rw⁻ 1 (q238 c4) ∷
   rw⁻ 2 (q239 c4) ∷
   rw 3 (q240 c4) ∷
   rw 4 (q241 c4) ∷
   rw⁻ 5 (q238 c4) ∷
   rw⁻ 6 (q228 c4) ∷
   rw⁻ 6 (q227 c4) ∷
   rw⁻ 0 (q242 c4) ∷
   rw 3 (q225 c4) ∷
   rw 4 (q202 c4) ∷
   rw 3 (q227 c4) ∷ []) Eq.refl

private
  q243 : Ws → Eqn
  q243 c4 = eqn (Bx3-0412 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4)
  q244 : Ws → Eqn
  q244 c4 = eqn (CCZ034 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ034 ∷ []) (wp 2 c4)
  q245 : Ws → Eqn
  q245 c4 = eqn (CS02⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS02⁻ ∷ []) (wl 1226 (lit c4))
  q246 : Ws → Eqn
  q246 c4 = eqn (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (Toff214 ∷ []) (wl 888 (lit c4))
  q247 : Ws → Eqn
  q247 c4 = eqn (CCZ034 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ034 ∷ []) (wp 700 c4)
  q248 : Ws → Eqn
  q248 c4 = eqn (CCZ034 ∷ CS14 ∷ []) (CS14 ∷ CCZ034 ∷ []) (wp 106 c4)
  q249 : Ws → Eqn
  q249 c4 = eqn (CX12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4))
  q250 : Ws → Eqn
  q250 c4 = eqn (CCZ034 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ034 ∷ []) (wp 107 c4)
  q251 : Ws → Eqn
  q251 c4 = eqn (CCZ034 ∷ CS24 ∷ []) (CS24 ∷ CCZ034 ∷ []) (wp 108 c4)
  q252 : Ws → Eqn
  q252 c4 = eqn (CCZ034 ∷ K2 ∷ []) (K2 ∷ CCZ034 ∷ []) (wp 701 c4)
  q253 : Ws → Eqn
  q253 c4 = eqn (Toff214 ∷ Toff312 ∷ []) (Toff312 ∷ Toff214 ∷ Toff314 ∷ []) (wl 777 (lit c4))
  q254 : Ws → Eqn
  q254 c4 = eqn (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) (Toff314 ∷ CCZ034 ∷ []) (wp 702 c4)
  q255 : Ws → Eqn
  q255 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp 41 c4)
  q256 : Ws → Eqn
  q256 c4 = eqn (CS01 ∷ Toff312 ∷ []) (Toff312 ∷ CS01 ∷ []) (wl 501 (lit c4))
  q257 : Ws → Eqn
  q257 c4 = eqn (CX04 ∷ Toff312 ∷ []) (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4))
  q258 : Ws → Eqn
  q258 c4 = eqn (CS14⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS14⁻ ∷ []) (wl 778 (lit c4))
  q259 : Ws → Eqn
  q259 c4 = eqn (CS14 ∷ Toff312 ∷ []) (Toff312 ∷ CS14 ∷ []) (wl 499 (lit c4))
  q260 : Ws → Eqn
  q260 c4 = eqn (Toff312 ∷ Toff314 ∷ []) (Toff314 ∷ Toff312 ∷ []) (wl 779 (lit c4))
  q261 : Ws → Eqn
  q261 c4 = eqn (Toff214 ∷ Toff314 ∷ Toff314 ∷ []) (Toff214 ∷ []) (wl 780 (lit c4))
  q262 : Ws → Eqn
  q262 c4 = eqn (CCZ034 ∷ CS02 ∷ []) (CS02 ∷ CCZ034 ∷ []) (wp 3 c4)
  q263 : Ws → Eqn
  q263 c4 = eqn (CS02 ∷ Toff312 ∷ []) (Toff312 ∷ CS02 ∷ []) (wl 861 (lit c4))
  q264 : Ws → Eqn
  q264 c4 = eqn (Bx3-0412 ∷ Bx3-0412 ∷ []) [] (lem-box2-at0310243142 c4)
  q265 : Ws → Eqn
  q265 c4 = eqn (CCZ014 ∷ CS02 ∷ Toff214 ∷ []) (CS02 ∷ Toff214 ∷ CCZ014 ∷ []) (wp 1030 c4)
  q266 : Ws → Eqn
  q266 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp 161 c4)
  q267 : Ws → Eqn
  q267 c4 = eqn (CCZ014 ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (wp 1076 c4)

-- S2-SBOX(3;0;41;2): 86 steps
lem-S2-SBOX⟨3·0·41·2⟩ : Ws → ⟪ (Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
lem-S2-SBOX⟨3·0·41·2⟩ c4 = derive (Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ []) (CCZ014 ∷ [])
  (re 1 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   re 3 1 (CS02 ∷ []) ∷
   re 5 1 (CS02⁻ ∷ []) ∷
   re 0 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   re 2 1 (CS02 ∷ []) ∷
   re 4 1 (CS02⁻ ∷ []) ∷
   rw 5 (q243 c4) ∷
   rw⁻ 4 (q244 c4) ∷
   rw 5 (q245 c4) ∷
   rw⁻ 6 (q244 c4) ∷
   rw 7 (q245 c4) ∷
   rw⁻ 4 (q243 c4) ∷
   rw 4 (q243 c4) ∷
   rw⁻ 3 (q246 c4) ∷
   rw⁻ 9 (q247 c4) ∷
   rw⁻ 8 (q248 c4) ∷
   rw 7 (q249 c4) ∷
   rw⁻ 6 (q250 c4) ∷
   rw 5 (q249 c4) ∷
   rw⁻ 4 (q251 c4) ∷
   rw⁻ 3 (q252 c4) ∷
   rw 4 (q246 c4) ∷
   rw 4 (q253 c4) ∷
   rw⁻ 6 (q254 c4) ∷
   rw⁻ 5 (q246 c4) ∷
   rw⁻ 11 (q247 c4) ∷
   rw⁻ 10 (q248 c4) ∷
   rw 9 (q249 c4) ∷
   rw⁻ 8 (q250 c4) ∷
   rw 7 (q249 c4) ∷
   rw⁻ 6 (q251 c4) ∷
   rw⁻ 5 (q252 c4) ∷
   rw 6 (q246 c4) ∷
   rw 8 (q255 c4) ∷
   rw 12 (q256 c4) ∷
   rw 11 (q257 c4) ∷
   rw 10 (q258 c4) ∷
   rw 9 (q257 c4) ∷
   rw 8 (q259 c4) ∷
   rw⁻ 9 (q255 c4) ∷
   rw⁻ 7 (q260 c4) ∷
   rw 6 (q253 c4) ∷
   rw 7 (q261 c4) ∷
   rw⁻ 3 (q243 c4) ∷
   rw 3 (q243 c4) ∷
   rw⁻ 2 (q262 c4) ∷
   rw 3 (q263 c4) ∷
   rw⁻ 4 (q262 c4) ∷
   rw 5 (q263 c4) ∷
   rw⁻ 2 (q243 c4) ∷
   rw 2 (q243 c4) ∷
   rw⁻ 1 (q246 c4) ∷
   rw⁻ 7 (q247 c4) ∷
   rw⁻ 6 (q248 c4) ∷
   rw 5 (q249 c4) ∷
   rw⁻ 4 (q250 c4) ∷
   rw 3 (q249 c4) ∷
   rw⁻ 2 (q251 c4) ∷
   rw⁻ 1 (q252 c4) ∷
   rw 2 (q246 c4) ∷
   rw 2 (q253 c4) ∷
   rw⁻ 4 (q254 c4) ∷
   rw⁻ 3 (q246 c4) ∷
   rw⁻ 9 (q247 c4) ∷
   rw⁻ 8 (q248 c4) ∷
   rw 7 (q249 c4) ∷
   rw⁻ 6 (q250 c4) ∷
   rw 5 (q249 c4) ∷
   rw⁻ 4 (q251 c4) ∷
   rw⁻ 3 (q252 c4) ∷
   rw 4 (q246 c4) ∷
   rw 6 (q255 c4) ∷
   rw 10 (q256 c4) ∷
   rw 9 (q257 c4) ∷
   rw 8 (q258 c4) ∷
   rw 7 (q257 c4) ∷
   rw 6 (q259 c4) ∷
   rw⁻ 7 (q255 c4) ∷
   rw⁻ 5 (q260 c4) ∷
   rw 4 (q253 c4) ∷
   rw 5 (q261 c4) ∷
   rw⁻ 1 (q243 c4) ∷
   rw 0 (q264 c4) ∷
   rw 1 (q265 c4) ∷
   rw 3 (q266 c4) ∷
   rw⁻ 0 (q267 c4) ∷ []) Eq.refl

private
  q268 : Ws → Eqn
  q268 c4 = eqn (Bx3-1420 ∷ []) (Bx3-4120 ∷ []) (lem-sym-ab-at03243240 c4)
  q269 : Ws → Eqn
  q269 c4 = eqn (Bx3-4120 ∷ []) (Bx3-2041 ∷ []) (lem-pairs-at0314213240 c4)

-- box-perm-3421 @03243240: 2 steps
lem-box-perm-3421-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-box-perm-3421-at03243240 c4 = derive (Bx3-1420 ∷ []) (Bx3-2041 ∷ [])
  (rw 0 (q268 c4) ∷
   rw 0 (q269 c4) ∷ []) Eq.refl

private
  q270 : Ws → Eqn
  q270 c4 = eqn (Bx3-2041 ∷ []) (Bx3-2401 ∷ []) (lem-box-perm-1324-at0312203441 c4)
  q271 : Ws → Eqn
  q271 c4 = eqn (X4 ∷ Bx3-2401 ∷ X4 ∷ []) (Bx3-2401 ∷ CCZ012 ∷ []) (lem-Xb-box-at0312243041 c4)
  q272 : Ws → Eqn
  q272 c4 = eqn (Bx3-2401 ∷ []) (Bx3-2041 ∷ []) (lem-box-perm-1324-at0312243041 c4)
  q273 : Ws → Eqn
  q273 c4 = eqn (Bx3-2041 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at0312203441 c4)
  q274 : Ws → Eqn
  q274 c4 = eqn (CCZ012 ∷ []) (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wl 1273 (lit c4))
  q275 : Ws → Eqn
  q275 c4 = eqn (CCZ134 ∷ CX20 ∷ []) (CX20 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX20 (lit c4))

-- CKc-box @0312203441: 61 steps
lem-CKc-box-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-2041 ∷ []) ⟫ʷ
lem-CKc-box-at0312203441 c4 = derive (Bx3-2041 ∷ CK41 ∷ []) (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-2041 ∷ [])
  (rw⁻ 1 (q202 c4) ∷
   rw 0 (q270 c4) ∷
   rw⁻ 0 (q271 c4) ∷
   rw⁻ 3 (q205 c4) ∷
   rw⁻ 2 (q206 c4) ∷
   rw⁻ 3 (q59 c4) ∷
   rw⁻ 6 (q206 c4) ∷
   rw 1 (q272 c4) ∷
   rw 1 (q273 c4) ∷
   rw 5 (q274 c4) ∷
   rw 4 (q194 c4) ∷
   rw 5 (q275 c4) ∷
   rw 6 (q176 c4) ∷
   rw 7 (q275 c4) ∷
   rw 8 (q210 c4) ∷
   rw⁻ 4 (q274 c4) ∷
   rw 5 (q213 c4) ∷
   rw 8 (q214 c4) ∷
   rw 11 (q215 c4) ∷
   rw 13 (q274 c4) ∷
   rw 12 (q194 c4) ∷
   rw 13 (q275 c4) ∷
   rw 14 (q176 c4) ∷
   rw 15 (q275 c4) ∷
   rw 16 (q210 c4) ∷
   rw⁻ 12 (q274 c4) ∷
   rw⁻ 5 (q216 c4) ∷
   rw⁻ 3 (q217 c4) ∷
   rw⁻ 4 (q218 c4) ∷
   rw 5 (q219 c4) ∷
   rw 6 (q220 c4) ∷
   rw⁻ 7 (q217 c4) ∷
   rw 3 (q274 c4) ∷
   rw 2 (q194 c4) ∷
   rw 3 (q275 c4) ∷
   rw 4 (q176 c4) ∷
   rw 5 (q275 c4) ∷
   rw 6 (q210 c4) ∷
   rw⁻ 2 (q274 c4) ∷
   rw 3 (q213 c4) ∷
   rw 6 (q214 c4) ∷
   rw 9 (q215 c4) ∷
   rw 11 (q274 c4) ∷
   rw 10 (q194 c4) ∷
   rw 11 (q275 c4) ∷
   rw 12 (q176 c4) ∷
   rw 13 (q275 c4) ∷
   rw 14 (q210 c4) ∷
   rw⁻ 10 (q274 c4) ∷
   rw⁻ 3 (q216 c4) ∷
   rw⁻ 1 (q217 c4) ∷
   rw⁻ 2 (q218 c4) ∷
   rw 3 (q219 c4) ∷
   rw 4 (q220 c4) ∷
   rw⁻ 5 (q217 c4) ∷
   rw⁻ 6 (q273 c4) ∷
   rw⁻ 6 (q272 c4) ∷
   rw⁻ 0 (q221 c4) ∷
   rw 3 (q271 c4) ∷
   rw 4 (q202 c4) ∷
   rw 3 (q272 c4) ∷ []) Eq.refl

private
  q276 : Ws → Eqn
  q276 c4 = eqn (Bx3-2041 ∷ []) (Bx3-4120 ∷ []) (lem-pairs-at0312203441 c4)
  q277 : Ws → Eqn
  q277 c4 = eqn (Bx3-4120 ∷ []) (Bx3-1420 ∷ []) (lem-sym-ab-at0314213240 c4)

-- box-perm-4312 @0312203441: 2 steps
lem-box-perm-4312-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-box-perm-4312-at0312203441 c4 = derive (Bx3-2041 ∷ []) (Bx3-1420 ∷ [])
  (rw 0 (q276 c4) ∷
   rw 0 (q277 c4) ∷ []) Eq.refl

private
  q278 : Ws → Eqn
  q278 c4 = eqn (Bx3-1240 ∷ []) (Bx3-1420 ∷ []) (lem-box-perm-1324-at033440 c4)
  q279 : Ws → Eqn
  q279 c4 = eqn (X4 ∷ Bx3-1420 ∷ X4 ∷ []) (Bx3-1420 ∷ CCZ012 ∷ []) (lem-Xb-box-at03243240 c4)
  q280 : Ws → Eqn
  q280 c4 = eqn (CCZ012 ∷ CK40 ∷ CCZ012 ∷ CCZ012 ∷ []) (CCZ012 ∷ CK40 ∷ []) (wp 1105 c4)
  q281 : Ws → Eqn
  q281 c4 = eqn (Bx3-1420 ∷ []) (Bx3-1240 ∷ []) (lem-box-perm-1324-at03243240 c4)
  q282 : Ws → Eqn
  q282 c4 = eqn (Bx3-1240 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at033440 c4)
  q283 : Ws → Eqn
  q283 c4 = eqn (CCZ012 ∷ []) (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl 155 (lit c4))
  q284 : Ws → Eqn
  q284 c4 = eqn (CCZ034 ∷ CX12 ∷ []) (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4))
  q285 : Ws → Eqn
  q285 c4 = eqn (CCZ034 ∷ CS01 ∷ []) (CS01 ∷ CCZ034 ∷ []) (wp 1 c4)
  q286 : Ws → Eqn
  q286 c4 = eqn (CCZ034 ∷ K0 ∷ []) (K0 ∷ Toff034 ∷ CCZ034 ∷ CCZ034 ∷ []) (wp 1106 c4)
  q287 : Ws → Eqn
  q287 c4 = eqn (CCZ034 ∷ CK40 ∷ []) (CZ03 ∷ CK40 ∷ CZ03 ∷ CCZ034 ∷ []) (wp 1107 c4)
  q288 : Ws → Eqn
  q288 c4 = eqn (K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ Toff034 ∷ CCZ034 ∷ CZ03 ∷ CK40 ∷ CZ03 ∷ S4 ∷ []) (wp 1108 c4)
  q289 : Ws → Eqn
  q289 c4 = eqn (CCZ012 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ012 ∷ []) (wl 503 (lit c4))
  q290 : Ws → Eqn
  q290 c4 = eqn (K0 ∷ Toff312 ∷ []) (Toff312 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ))
  q291 : Ws → Eqn
  q291 c4 = eqn (Toff312 ∷ CK40 ∷ []) (CK40 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CK40 (lit c4))
  q292 : Ws → Eqn
  q292 c4 = eqn (Toff312 ∷ S4 ∷ []) (S4 ∷ Toff312 ∷ []) (c₄ (Toffᵗ ↑) (S))
  q293 : Ws → Eqn
  q293 c4 = eqn (CCZ012 ∷ CK40 ∷ CCZ012 ∷ X4 ∷ []) (X4 ∷ CCZ012 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ012 ∷ []) (wp 1109 c4)

-- CKc-box @033440: 61 steps
lem-CKc-box-at033440 : Ws → ⟪ (Bx3-1240 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CK40 ∷ CCZ012 ∷ Bx3-1240 ∷ []) ⟫ʷ
lem-CKc-box-at033440 c4 = derive (Bx3-1240 ∷ CK40 ∷ []) (CCZ012 ∷ CK40 ∷ CCZ012 ∷ Bx3-1240 ∷ [])
  (rw⁻ 1 (q202 c4) ∷
   rw 0 (q278 c4) ∷
   rw⁻ 0 (q279 c4) ∷
   rw⁻ 3 (q280 c4) ∷
   rw⁻ 2 (q206 c4) ∷
   rw⁻ 3 (q34 c4) ∷
   rw⁻ 6 (q206 c4) ∷
   rw 1 (q281 c4) ∷
   rw 1 (q282 c4) ∷
   rw 5 (q283 c4) ∷
   rw 4 (q262 c4) ∷
   rw 5 (q284 c4) ∷
   rw 6 (q244 c4) ∷
   rw 7 (q284 c4) ∷
   rw 8 (q285 c4) ∷
   rw⁻ 4 (q283 c4) ∷
   rw 5 (q286 c4) ∷
   rw 8 (q287 c4) ∷
   rw 11 (q141 c4) ∷
   rw 13 (q283 c4) ∷
   rw 12 (q262 c4) ∷
   rw 13 (q284 c4) ∷
   rw 14 (q244 c4) ∷
   rw 15 (q284 c4) ∷
   rw 16 (q285 c4) ∷
   rw⁻ 12 (q283 c4) ∷
   rw⁻ 5 (q288 c4) ∷
   rw⁻ 3 (q289 c4) ∷
   rw⁻ 4 (q290 c4) ∷
   rw 5 (q291 c4) ∷
   rw 6 (q292 c4) ∷
   rw⁻ 7 (q289 c4) ∷
   rw 3 (q283 c4) ∷
   rw 2 (q262 c4) ∷
   rw 3 (q284 c4) ∷
   rw 4 (q244 c4) ∷
   rw 5 (q284 c4) ∷
   rw 6 (q285 c4) ∷
   rw⁻ 2 (q283 c4) ∷
   rw 3 (q286 c4) ∷
   rw 6 (q287 c4) ∷
   rw 9 (q141 c4) ∷
   rw 11 (q283 c4) ∷
   rw 10 (q262 c4) ∷
   rw 11 (q284 c4) ∷
   rw 12 (q244 c4) ∷
   rw 13 (q284 c4) ∷
   rw 14 (q285 c4) ∷
   rw⁻ 10 (q283 c4) ∷
   rw⁻ 3 (q288 c4) ∷
   rw⁻ 1 (q289 c4) ∷
   rw⁻ 2 (q290 c4) ∷
   rw 3 (q291 c4) ∷
   rw 4 (q292 c4) ∷
   rw⁻ 5 (q289 c4) ∷
   rw⁻ 6 (q282 c4) ∷
   rw⁻ 6 (q281 c4) ∷
   rw⁻ 0 (q293 c4) ∷
   rw 3 (q279 c4) ∷
   rw 4 (q202 c4) ∷
   rw 3 (q281 c4) ∷ []) Eq.refl

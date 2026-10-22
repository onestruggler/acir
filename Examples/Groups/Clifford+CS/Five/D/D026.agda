{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD026 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D026 (Sᴰ : SD026) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX04-TOFF213 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024 ; lem-comm-CX14-TOFF023 ; lem-comm-CX23-CCZ014 ; lem-comm-CX24-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ014-CX23 ; lem-comm-CCZ024-CX13 ; lem-comm-CCZ034-CX12 ; lem-comm-TOFF013-CS24 ; lem-comm-TOFF013-CX24 ; lem-comm-TOFF213-CS04 ; lem-comm-TOFF213-CX04)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF023-CS14 ; lem-comm-TOFF023-CX14)

-- The lemmas of other derivation modules (DSig).
private
  lem-box-tQ-at0210213443 : Ws → St 77
  lem-box-tQ-at0210213443 = pickᴰ 0 Sᴰ
  lem-box-tQ : Ws → St 146
  lem-box-tQ = pickᴰ 1 Sᴰ
  lem-box-tQ-at3443 : Ws → St 163
  lem-box-tQ-at3443 = pickᴰ 2 Sᴰ
  lem-box-cP-at0210243143 : Ws → St 842
  lem-box-cP-at0210243143 = pickᴰ 3 Sᴰ
  lem-box-cP-at122441 : Ws → St 850
  lem-box-cP-at122441 = pickᴰ 4 Sᴰ
  lem-box-cP-at243243 : Ws → St 856
  lem-box-cP-at243243 = pickᴰ 5 Sᴰ
  lem-box-perm-1324 : Ws → St 1108
  lem-box-perm-1324 = pickᴰ 6 Sᴰ
  lem-box-perm-1324-at0210243143 : Ws → St 1077
  lem-box-perm-1324-at0210243143 = pickᴰ 7 Sᴰ
  lem-box-perm-1324-at243243 : Ws → St 1079
  lem-box-perm-1324-at243243 = pickᴰ 8 Sᴰ
  lem-box2-at0210243143 : Ws → St 1081
  lem-box2-at0210243143 = pickᴰ 9 Sᴰ
  lem-box2-at122441 : Ws → St 1082
  lem-box2-at122441 = pickᴰ 10 Sᴰ
  lem-box2-at243243 : Ws → St 1083
  lem-box2-at243243 = pickᴰ 11 Sᴰ
  lem-CSu-box-4-at122441 : Ws → St 1109
  lem-CSu-box-4-at122441 = pickᴰ 12 Sᴰ
  lem-Xb-box-at2332 : Ws → St 1110
  lem-Xb-box-at2332 = pickᴰ 13 Sᴰ
  lem-box-perm-1324-at2332 : Ws → St 1111
  lem-box-perm-1324-at2332 = pickᴰ 14 Sᴰ
  lem-nf-comm-CS-S0at0 : Ws → St 1112
  lem-nf-comm-CS-S0at0 = pickᴰ 15 Sᴰ
  lem-nf-comm-CS-S0at1 : Ws → St 1113
  lem-nf-comm-CS-S0at1 = pickᴰ 16 Sᴰ
  lem-nf-comm-CS-S0at2 : Ws → St 1114
  lem-nf-comm-CS-S0at2 = pickᴰ 17 Sᴰ
  lem-nf-comm-CS-S1at0 : Ws → St 1115
  lem-nf-comm-CS-S1at0 = pickᴰ 18 Sᴰ
  lem-nf-comm-CS-S1at1 : Ws → St 1116
  lem-nf-comm-CS-S1at1 = pickᴰ 19 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1077 (lem-box-perm-1324-at0210243143 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 77 (lem-box-tQ-at0210213443 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Toff201 ∷ CK43 ∷ []) (CK43 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CK₁₀))
  q4 : Ws → Eqn
  q4 c4 = wlE 1069 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = wlE 1070 (lit c4)
  q6 : Ws → Eqn
  q6 c4 = wlE 184 (lit c4)
  q7 : Ws → Eqn
  q7 c4 = wpE 294 c4
  q8 : Ws → Eqn
  q8 c4 = eqn (CX01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ))
  q9 : Ws → Eqn
  q9 c4 = wlE 432 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = wlE 433 (lit c4)
  q11 : Ws → Eqn
  q11 c4 = wlE 1071 (lit c4)
  q12 : Ws → Eqn
  q12 c4 = wlE 1072 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = wlE 1073 (lit c4)
  q14 : Ws → Eqn
  q14 c4 = wpE 880 c4

-- F2-K3-CS0: 35 steps
lem-F2-K3-CS0 : Ws → ⟪ (CK43 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK43 ∷ []) ⟫ʷ
lem-F2-K3-CS0 c4 = derive (CK43 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK43 ∷ [])
  (re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw 1 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   rw⁻ 1 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 2 (q5 c4) ∷
   rw 7 (q6 c4) ∷
   rw⁻ 11 (q7 c4) ∷
   rw 10 (q8 c4) ∷
   rw⁻ 9 (q9 c4) ∷
   rw 8 (q8 c4) ∷
   rw⁻ 7 (q10 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   rw⁻ 6 (q11 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw 5 (q8 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   rw 6 (q12 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 1 (q14 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q15 : Ws → Eqn
  q15 c4 = sE 1079 (lem-box-perm-1324-at243243 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 163 (lem-box-tQ-at3443 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (Toff012 ∷ CK43 ∷ []) (CK43 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₁₀))
  q18 : Ws → Eqn
  q18 c4 = wpE 881 c4
  q19 : Ws → Eqn
  q19 c4 = wlE 1074 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = wlE 207 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = wpE 312 c4
  q22 : Ws → Eqn
  q22 c4 = eqn (CX12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = wpE 313 c4
  q24 : Ws → Eqn
  q24 c4 = wpE 314 c4
  q25 : Ws → Eqn
  q25 c4 = wpE 797 c4
  q26 : Ws → Eqn
  q26 c4 = wpE 882 c4
  q27 : Ws → Eqn
  q27 c4 = wlE 1075 (lit c4)
  q28 : Ws → Eqn
  q28 c4 = wlE 1076 (lit c4)

-- F2-K3-CS1: 35 steps
lem-F2-K3-CS1 : Ws → ⟪ (CK43 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK43 ∷ []) ⟫ʷ
lem-F2-K3-CS1 c4 = derive (CK43 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK43 ∷ [])
  (re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 1 (q15 c4) ∷
   rw 1 (q16 c4) ∷
   rw⁻ 0 (q17 c4) ∷
   rw⁻ 1 (q18 c4) ∷
   rw 4 (q19 c4) ∷
   rw⁻ 3 (q17 c4) ∷
   rw 2 (q19 c4) ∷
   rw 7 (q20 c4) ∷
   rw⁻ 11 (q21 c4) ∷
   rw 10 (q22 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   rw 8 (q22 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw⁻ 8 (q20 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   rw⁻ 5 (q18 c4) ∷
   rw 4 (q20 c4) ∷
   rw⁻ 8 (q21 c4) ∷
   rw 7 (q22 c4) ∷
   rw⁻ 6 (q23 c4) ∷
   rw 5 (q22 c4) ∷
   rw⁻ 4 (q24 c4) ∷
   rw⁻ 5 (q20 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   rw 6 (q26 c4) ∷
   rw⁻ 4 (q27 c4) ∷
   rw⁻ 0 (q16 c4) ∷
   rw⁻ 0 (q15 c4) ∷
   rw 1 (q28 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = sE 1109 (lem-CSu-box-4-at122441 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CS01 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS01 ∷ []) (axAX)

-- AX-S23: 8 steps
lem-AX-S23 : Ws → ⟪ (CS01 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS01 ∷ []) ⟫ʷ
lem-AX-S23 c4 = derive (CS01 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS01 ∷ [])
  (re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw 0 (q29 c4) ∷
   rw 1 (q30 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q31 : Ws → Eqn
  q31 c4 = wlE 263 (lit c4)
  q32 : Ws → Eqn
  q32 c4 = sE 1108 (lem-box-perm-1324 c4)
  q33 : Ws → Eqn
  q33 c4 = sE 1110 (lem-Xb-box-at2332 c4)
  q34 : Ws → Eqn
  q34 c4 = wlE 1090 (lit c4)
  q35 : Ws → Eqn
  q35 c4 = wlE 1091 (lit c4)
  q36 : Ws → Eqn
  q36 c4 = wlE 1092 (lit c4)
  q37 : Ws → Eqn
  q37 c4 = sE 1111 (lem-box-perm-1324-at2332 c4)
  q38 : Ws → Eqn
  q38 c4 = sE 146 (lem-box-tQ c4)
  q39 : Ws → Eqn
  q39 c4 = wlE 256 (lit c4)
  q40 : Ws → Eqn
  q40 c4 = wpE 108 c4
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ034 ∷ CX12 ∷ []) (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = wpE 107 c4
  q43 : Ws → Eqn
  q43 c4 = wpE 106 c4
  q44 : Ws → Eqn
  q44 c4 = wpE 888 c4
  q45 : Ws → Eqn
  q45 c4 = wpE 889 c4
  q46 : Ws → Eqn
  q46 c4 = wpE 890 c4
  q47 : Ws → Eqn
  q47 c4 = wpE 891 c4
  q48 : Ws → Eqn
  q48 c4 = wpE 300 c4
  q49 : Ws → Eqn
  q49 c4 = eqn (Toff012 ∷ K4 ∷ []) (K4 ∷ Toff012 ∷ []) (c₃ (Toff) (K ↑))
  q50 : Ws → Eqn
  q50 c4 = eqn (Toff012 ∷ CK34 ∷ []) (CK34 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₀₁))
  q51 : Ws → Eqn
  q51 c4 = eqn (Toff012 ∷ S3 ∷ []) (S3 ∷ Toff012 ∷ []) (c₃ (Toff) (S))
  q52 : Ws → Eqn
  q52 c4 = wlE 1093 (lit c4)

-- CKc-box: 61 steps
lem-CKc-box : Ws → ⟪ (Bx0-1234 ∷ CK34 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CK34 ∷ CCZ124 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-CKc-box c4 = derive (Bx0-1234 ∷ CK34 ∷ []) (CCZ124 ∷ CK34 ∷ CCZ124 ∷ Bx0-1234 ∷ [])
  (rw⁻ 1 (q31 c4) ∷
   rw 0 (q32 c4) ∷
   rw⁻ 0 (q33 c4) ∷
   rw⁻ 3 (q34 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   rw⁻ 3 (q36 c4) ∷
   rw⁻ 6 (q35 c4) ∷
   rw 1 (q37 c4) ∷
   rw 1 (q38 c4) ∷
   rw 5 (q39 c4) ∷
   rw 4 (q40 c4) ∷
   rw 5 (q41 c4) ∷
   rw 6 (q42 c4) ∷
   rw 7 (q41 c4) ∷
   rw 8 (q43 c4) ∷
   rw⁻ 4 (q39 c4) ∷
   rw 5 (q44 c4) ∷
   rw 8 (q45 c4) ∷
   rw 11 (q46 c4) ∷
   rw 13 (q39 c4) ∷
   rw 12 (q40 c4) ∷
   rw 13 (q41 c4) ∷
   rw 14 (q42 c4) ∷
   rw 15 (q41 c4) ∷
   rw 16 (q43 c4) ∷
   rw⁻ 12 (q39 c4) ∷
   rw⁻ 5 (q47 c4) ∷
   rw⁻ 3 (q48 c4) ∷
   rw 4 (q49 c4) ∷
   rw 5 (q50 c4) ∷
   rw 6 (q51 c4) ∷
   rw⁻ 7 (q48 c4) ∷
   rw 3 (q39 c4) ∷
   rw 2 (q40 c4) ∷
   rw 3 (q41 c4) ∷
   rw 4 (q42 c4) ∷
   rw 5 (q41 c4) ∷
   rw 6 (q43 c4) ∷
   rw⁻ 2 (q39 c4) ∷
   rw 3 (q44 c4) ∷
   rw 6 (q45 c4) ∷
   rw 9 (q46 c4) ∷
   rw 11 (q39 c4) ∷
   rw 10 (q40 c4) ∷
   rw 11 (q41 c4) ∷
   rw 12 (q42 c4) ∷
   rw 13 (q41 c4) ∷
   rw 14 (q43 c4) ∷
   rw⁻ 10 (q39 c4) ∷
   rw⁻ 3 (q47 c4) ∷
   rw⁻ 1 (q48 c4) ∷
   rw 2 (q49 c4) ∷
   rw 3 (q50 c4) ∷
   rw 4 (q51 c4) ∷
   rw⁻ 5 (q48 c4) ∷
   rw⁻ 6 (q38 c4) ∷
   rw⁻ 6 (q37 c4) ∷
   rw⁻ 0 (q52 c4) ∷
   rw 3 (q33 c4) ∷
   rw 4 (q31 c4) ∷
   rw 3 (q37 c4) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = wlE 1094 (lit c4)
  q54 : Ws → Eqn
  q54 c4 = wlE 1095 (lit c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ034 ∷ ι ∷ []) (ι ∷ CCZ034 ∷ []) (zc)
  q56 : Ws → Eqn
  q56 c4 = wpE 892 c4
  q57 : Ws → Eqn
  q57 c4 = eqn (Toff012 ∷ ι ∷ []) (ι ∷ Toff012 ∷ []) (zc)
  q58 : Ws → Eqn
  q58 c4 = eqn (ι ∷ []) (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl)
  q59 : Ws → Eqn
  q59 c4 = wpE 893 c4
  q60 : Ws → Eqn
  q60 c4 = wlE 1096 (lit c4)

-- CKdc-box: 63 steps
lem-CKdc-box : Ws → ⟪ (Bx0-1234 ∷ CK34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CK34⁻ ∷ CCZ124 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-CKdc-box c4 = derive (Bx0-1234 ∷ CK34⁻ ∷ []) (CCZ124 ∷ CK34⁻ ∷ CCZ124 ∷ Bx0-1234 ∷ [])
  (rw⁻ 1 (q31 c4) ∷
   rw 0 (q32 c4) ∷
   rw⁻ 0 (q33 c4) ∷
   rw⁻ 3 (q53 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   rw⁻ 3 (q54 c4) ∷
   rw⁻ 6 (q35 c4) ∷
   rw 1 (q37 c4) ∷
   rw 1 (q38 c4) ∷
   rw 5 (q39 c4) ∷
   rw 4 (q40 c4) ∷
   rw 5 (q41 c4) ∷
   rw 6 (q42 c4) ∷
   rw 7 (q41 c4) ∷
   rw 8 (q43 c4) ∷
   rw⁻ 4 (q39 c4) ∷
   rw 5 (q44 c4) ∷
   rw 8 (q45 c4) ∷
   rw 11 (q55 c4) ∷
   rw 13 (q39 c4) ∷
   rw 12 (q40 c4) ∷
   rw 13 (q41 c4) ∷
   rw 14 (q42 c4) ∷
   rw 15 (q41 c4) ∷
   rw 16 (q43 c4) ∷
   rw⁻ 12 (q39 c4) ∷
   rw⁻ 5 (q56 c4) ∷
   rw⁻ 3 (q48 c4) ∷
   rw 4 (q49 c4) ∷
   rw 5 (q50 c4) ∷
   rw 6 (q57 c4) ∷
   rw⁻ 7 (q48 c4) ∷
   rw 3 (q39 c4) ∷
   rw 2 (q40 c4) ∷
   rw 3 (q41 c4) ∷
   rw 4 (q42 c4) ∷
   rw 5 (q41 c4) ∷
   rw 6 (q43 c4) ∷
   rw⁻ 2 (q39 c4) ∷
   rw 3 (q44 c4) ∷
   rw 6 (q45 c4) ∷
   rw 9 (q55 c4) ∷
   rw 11 (q39 c4) ∷
   rw 10 (q40 c4) ∷
   rw 11 (q41 c4) ∷
   rw 12 (q42 c4) ∷
   rw 13 (q41 c4) ∷
   rw 14 (q43 c4) ∷
   rw⁻ 10 (q39 c4) ∷
   rw⁻ 3 (q56 c4) ∷
   rw⁻ 1 (q48 c4) ∷
   rw 2 (q49 c4) ∷
   rw 3 (q50 c4) ∷
   rw 4 (q57 c4) ∷
   rw⁻ 5 (q48 c4) ∷
   rw⁻ 6 (q38 c4) ∷
   rw⁻ 6 (q37 c4) ∷
   rw 4 (q58 c4) ∷
   rw⁻ 0 (q59 c4) ∷
   rw 0 (q60 c4) ∷
   rw 3 (q33 c4) ∷
   rw 4 (q31 c4) ∷
   rw 3 (q37 c4) ∷ []) Eq.refl

private
  q61 : Ws → Eqn
  q61 c4 = sE 842 (lem-box-cP-at0210243143 c4)
  q62 : Ws → Eqn
  q62 c4 = wpE 32 c4
  q63 : Ws → Eqn
  q63 c4 = wlE 191 (lit c4)
  q64 : Ws → Eqn
  q64 c4 = wlE 190 (lit c4)
  q65 : Ws → Eqn
  q65 c4 = wpE 33 c4
  q66 : Ws → Eqn
  q66 c4 = wpE 34 c4
  q67 : Ws → Eqn
  q67 c4 = eqn (CX13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = wpE 35 c4
  q69 : Ws → Eqn
  q69 c4 = wpE 36 c4
  q70 : Ws → Eqn
  q70 c4 = wpE 37 c4
  q71 : Ws → Eqn
  q71 c4 = wlE 192 (lit c4)
  q72 : Ws → Eqn
  q72 c4 = wpE 42 c4
  q73 : Ws → Eqn
  q73 c4 = wpE 41 c4
  q74 : Ws → Eqn
  q74 c4 = wlE 193 (lit c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (CX04 ∷ Toff213 ∷ []) (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = wlE 194 (lit c4)
  q77 : Ws → Eqn
  q77 c4 = wlE 195 (lit c4)
  q78 : Ws → Eqn
  q78 c4 = wlE 197 (lit c4)
  q79 : Ws → Eqn
  q79 c4 = wpE 44 c4
  q80 : Ws → Eqn
  q80 c4 = wpE 21 c4
  q81 : Ws → Eqn
  q81 c4 = wlE 196 (lit c4)
  q82 : Ws → Eqn
  q82 c4 = sE 1081 (lem-box2-at0210243143 c4)
  q83 : Ws → Eqn
  q83 c4 = wpE 651 c4
  q84 : Ws → Eqn
  q84 c4 = wpE 161 c4
  q85 : Ws → Eqn
  q85 c4 = wpE 905 c4

-- S2-SBOX(2;0;41;3): 86 steps
lem-S2-SBOX⟨2·0·41·3⟩ : Ws → ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
lem-S2-SBOX⟨2·0·41·3⟩ c4 = derive (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (CCZ014 ∷ [])
  (re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   re 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 2 1 (CS03 ∷ []) ∷
   re 4 1 (CS03⁻ ∷ []) ∷
   rw 5 (q61 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw 5 (q63 c4) ∷
   rw⁻ 6 (q62 c4) ∷
   rw 7 (q63 c4) ∷
   rw⁻ 4 (q61 c4) ∷
   rw 4 (q61 c4) ∷
   rw⁻ 3 (q64 c4) ∷
   rw⁻ 9 (q65 c4) ∷
   rw⁻ 8 (q66 c4) ∷
   rw 7 (q67 c4) ∷
   rw⁻ 6 (q68 c4) ∷
   rw 5 (q67 c4) ∷
   rw⁻ 4 (q69 c4) ∷
   rw⁻ 3 (q70 c4) ∷
   rw 4 (q64 c4) ∷
   rw⁻ 4 (q71 c4) ∷
   rw⁻ 6 (q64 c4) ∷
   rw⁻ 12 (q65 c4) ∷
   rw⁻ 11 (q66 c4) ∷
   rw 10 (q67 c4) ∷
   rw⁻ 9 (q68 c4) ∷
   rw 8 (q67 c4) ∷
   rw⁻ 7 (q69 c4) ∷
   rw⁻ 6 (q70 c4) ∷
   rw 7 (q64 c4) ∷
   rw⁻ 5 (q72 c4) ∷
   rw⁻ 8 (q71 c4) ∷
   rw 7 (q73 c4) ∷
   rw 11 (q74 c4) ∷
   rw 10 (q75 c4) ∷
   rw 9 (q76 c4) ∷
   rw 8 (q75 c4) ∷
   rw 7 (q77 c4) ∷
   rw⁻ 8 (q73 c4) ∷
   rw⁻ 6 (q78 c4) ∷
   rw⁻ 7 (q79 c4) ∷
   rw⁻ 3 (q61 c4) ∷
   rw 3 (q61 c4) ∷
   rw⁻ 2 (q80 c4) ∷
   rw 3 (q81 c4) ∷
   rw⁻ 4 (q80 c4) ∷
   rw 5 (q81 c4) ∷
   rw⁻ 2 (q61 c4) ∷
   rw 2 (q61 c4) ∷
   rw⁻ 1 (q64 c4) ∷
   rw⁻ 7 (q65 c4) ∷
   rw⁻ 6 (q66 c4) ∷
   rw 5 (q67 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 3 (q67 c4) ∷
   rw⁻ 2 (q69 c4) ∷
   rw⁻ 1 (q70 c4) ∷
   rw 2 (q64 c4) ∷
   rw⁻ 2 (q71 c4) ∷
   rw⁻ 4 (q64 c4) ∷
   rw⁻ 10 (q65 c4) ∷
   rw⁻ 9 (q66 c4) ∷
   rw 8 (q67 c4) ∷
   rw⁻ 7 (q68 c4) ∷
   rw 6 (q67 c4) ∷
   rw⁻ 5 (q69 c4) ∷
   rw⁻ 4 (q70 c4) ∷
   rw 5 (q64 c4) ∷
   rw⁻ 3 (q72 c4) ∷
   rw⁻ 6 (q71 c4) ∷
   rw 5 (q73 c4) ∷
   rw 9 (q74 c4) ∷
   rw 8 (q75 c4) ∷
   rw 7 (q76 c4) ∷
   rw 6 (q75 c4) ∷
   rw 5 (q77 c4) ∷
   rw⁻ 6 (q73 c4) ∷
   rw⁻ 4 (q78 c4) ∷
   rw⁻ 5 (q79 c4) ∷
   rw⁻ 1 (q61 c4) ∷
   rw 0 (q82 c4) ∷
   rw 0 (q83 c4) ∷
   rw 2 (q84 c4) ∷
   rw⁻ 0 (q85 c4) ∷ []) Eq.refl

private
  q86 : Ws → Eqn
  q86 c4 = sE 856 (lem-box-cP-at243243 c4)
  q87 : Ws → Eqn
  q87 c4 = wpE 60 c4
  q88 : Ws → Eqn
  q88 c4 = wlE 219 (lit c4)
  q89 : Ws → Eqn
  q89 c4 = wlE 217 (lit c4)
  q90 : Ws → Eqn
  q90 c4 = wpE 61 c4
  q91 : Ws → Eqn
  q91 c4 = wpE 62 c4
  q92 : Ws → Eqn
  q92 c4 = eqn (CX23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4))
  q93 : Ws → Eqn
  q93 c4 = wpE 63 c4
  q94 : Ws → Eqn
  q94 c4 = wpE 64 c4
  q95 : Ws → Eqn
  q95 c4 = wpE 65 c4
  q96 : Ws → Eqn
  q96 c4 = wpE 68 c4
  q97 : Ws → Eqn
  q97 c4 = wpE 71 c4
  q98 : Ws → Eqn
  q98 c4 = wlE 220 (lit c4)
  q99 : Ws → Eqn
  q99 c4 = wlE 221 (lit c4)
  q100 : Ws → Eqn
  q100 c4 = eqn (CX14 ∷ Toff023 ∷ []) (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4))
  q101 : Ws → Eqn
  q101 c4 = wpE 69 c4
  q102 : Ws → Eqn
  q102 c4 = wpE 70 c4
  q103 : Ws → Eqn
  q103 c4 = wpE 72 c4
  q104 : Ws → Eqn
  q104 c4 = wpE 74 c4
  q105 : Ws → Eqn
  q105 c4 = wpE 53 c4
  q106 : Ws → Eqn
  q106 c4 = wlE 222 (lit c4)
  q107 : Ws → Eqn
  q107 c4 = sE 1083 (lem-box2-at243243 c4)
  q108 : Ws → Eqn
  q108 c4 = wlE 1000 (lit c4)
  q109 : Ws → Eqn
  q109 c4 = wlE 1113 (lit c4)

-- S2-SBOX(0;1;42;3): 86 steps
lem-S2-SBOX⟨0·1·42·3⟩ : Ws → ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
lem-S2-SBOX⟨0·1·42·3⟩ c4 = derive (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (CCZ124 ∷ [])
  (re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   re 0 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 2 1 (CS13 ∷ []) ∷
   re 4 1 (CS13⁻ ∷ []) ∷
   rw 5 (q86 c4) ∷
   rw⁻ 4 (q87 c4) ∷
   rw 5 (q88 c4) ∷
   rw⁻ 6 (q87 c4) ∷
   rw 7 (q88 c4) ∷
   rw⁻ 4 (q86 c4) ∷
   rw 4 (q86 c4) ∷
   rw⁻ 3 (q89 c4) ∷
   rw⁻ 9 (q90 c4) ∷
   rw⁻ 8 (q91 c4) ∷
   rw 7 (q92 c4) ∷
   rw⁻ 6 (q93 c4) ∷
   rw 5 (q92 c4) ∷
   rw⁻ 4 (q94 c4) ∷
   rw⁻ 3 (q95 c4) ∷
   rw 4 (q89 c4) ∷
   rw⁻ 4 (q96 c4) ∷
   rw⁻ 6 (q89 c4) ∷
   rw⁻ 12 (q90 c4) ∷
   rw⁻ 11 (q91 c4) ∷
   rw 10 (q92 c4) ∷
   rw⁻ 9 (q93 c4) ∷
   rw 8 (q92 c4) ∷
   rw⁻ 7 (q94 c4) ∷
   rw⁻ 6 (q95 c4) ∷
   rw 7 (q89 c4) ∷
   rw⁻ 5 (q97 c4) ∷
   rw⁻ 8 (q96 c4) ∷
   rw 7 (q98 c4) ∷
   rw 11 (q99 c4) ∷
   rw 10 (q100 c4) ∷
   rw 9 (q101 c4) ∷
   rw 8 (q100 c4) ∷
   rw 7 (q102 c4) ∷
   rw⁻ 8 (q98 c4) ∷
   rw⁻ 6 (q103 c4) ∷
   rw⁻ 7 (q104 c4) ∷
   rw⁻ 3 (q86 c4) ∷
   rw 3 (q86 c4) ∷
   rw⁻ 2 (q105 c4) ∷
   rw 3 (q106 c4) ∷
   rw⁻ 4 (q105 c4) ∷
   rw 5 (q106 c4) ∷
   rw⁻ 2 (q86 c4) ∷
   rw 2 (q86 c4) ∷
   rw⁻ 1 (q89 c4) ∷
   rw⁻ 7 (q90 c4) ∷
   rw⁻ 6 (q91 c4) ∷
   rw 5 (q92 c4) ∷
   rw⁻ 4 (q93 c4) ∷
   rw 3 (q92 c4) ∷
   rw⁻ 2 (q94 c4) ∷
   rw⁻ 1 (q95 c4) ∷
   rw 2 (q89 c4) ∷
   rw⁻ 2 (q96 c4) ∷
   rw⁻ 4 (q89 c4) ∷
   rw⁻ 10 (q90 c4) ∷
   rw⁻ 9 (q91 c4) ∷
   rw 8 (q92 c4) ∷
   rw⁻ 7 (q93 c4) ∷
   rw 6 (q92 c4) ∷
   rw⁻ 5 (q94 c4) ∷
   rw⁻ 4 (q95 c4) ∷
   rw 5 (q89 c4) ∷
   rw⁻ 3 (q97 c4) ∷
   rw⁻ 6 (q96 c4) ∷
   rw 5 (q98 c4) ∷
   rw 9 (q99 c4) ∷
   rw 8 (q100 c4) ∷
   rw 7 (q101 c4) ∷
   rw 6 (q100 c4) ∷
   rw 5 (q102 c4) ∷
   rw⁻ 6 (q98 c4) ∷
   rw⁻ 4 (q103 c4) ∷
   rw⁻ 5 (q104 c4) ∷
   rw⁻ 1 (q86 c4) ∷
   rw 0 (q107 c4) ∷
   rw 0 (q108 c4) ∷
   rw 2 (q31 c4) ∷
   rw⁻ 0 (q109 c4) ∷ []) Eq.refl

private
  q110 : Ws → Eqn
  q110 c4 = sE 850 (lem-box-cP-at122441 c4)
  q111 : Ws → Eqn
  q111 c4 = wpE 87 c4
  q112 : Ws → Eqn
  q112 c4 = wlE 244 (lit c4)
  q113 : Ws → Eqn
  q113 c4 = wlE 241 (lit c4)
  q114 : Ws → Eqn
  q114 c4 = wpE 88 c4
  q115 : Ws → Eqn
  q115 c4 = wpE 89 c4
  q116 : Ws → Eqn
  q116 c4 = wpE 93 c4
  q117 : Ws → Eqn
  q117 c4 = wpE 96 c4
  q118 : Ws → Eqn
  q118 c4 = wlE 245 (lit c4)
  q119 : Ws → Eqn
  q119 c4 = wlE 246 (lit c4)
  q120 : Ws → Eqn
  q120 c4 = eqn (CX24 ∷ Toff013 ∷ []) (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 (lit c4))
  q121 : Ws → Eqn
  q121 c4 = wpE 94 c4
  q122 : Ws → Eqn
  q122 c4 = wpE 95 c4
  q123 : Ws → Eqn
  q123 c4 = wpE 97 c4
  q124 : Ws → Eqn
  q124 c4 = wpE 842 c4
  q125 : Ws → Eqn
  q125 c4 = wpE 81 c4
  q126 : Ws → Eqn
  q126 c4 = wlE 247 (lit c4)
  q127 : Ws → Eqn
  q127 c4 = sE 1082 (lem-box2-at122441 c4)
  q128 : Ws → Eqn
  q128 c4 = wlE 1037 (lit c4)
  q129 : Ws → Eqn
  q129 c4 = wlE 305 (lit c4)
  q130 : Ws → Eqn
  q130 c4 = wlE 1114 (lit c4)

-- S2-SBOX(0;2;43;1): 86 steps
lem-S2-SBOX⟨0·2·43·1⟩ : Ws → ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ []) ⟫ʷ
lem-S2-SBOX⟨0·2·43·1⟩ c4 = derive (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CCZ234 ∷ [])
  (re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   re 0 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 2 1 (CS12 ∷ []) ∷
   re 4 1 (CS12⁻ ∷ []) ∷
   rw 5 (q110 c4) ∷
   rw⁻ 4 (q111 c4) ∷
   rw 5 (q112 c4) ∷
   rw⁻ 6 (q111 c4) ∷
   rw 7 (q112 c4) ∷
   rw⁻ 4 (q110 c4) ∷
   rw 4 (q110 c4) ∷
   rw⁻ 3 (q113 c4) ∷
   rw⁻ 9 (q114 c4) ∷
   rw⁻ 8 (q66 c4) ∷
   rw 7 (q67 c4) ∷
   rw⁻ 6 (q68 c4) ∷
   rw 5 (q67 c4) ∷
   rw⁻ 4 (q69 c4) ∷
   rw⁻ 3 (q115 c4) ∷
   rw 4 (q113 c4) ∷
   rw⁻ 4 (q116 c4) ∷
   rw⁻ 6 (q113 c4) ∷
   rw⁻ 12 (q114 c4) ∷
   rw⁻ 11 (q66 c4) ∷
   rw 10 (q67 c4) ∷
   rw⁻ 9 (q68 c4) ∷
   rw 8 (q67 c4) ∷
   rw⁻ 7 (q69 c4) ∷
   rw⁻ 6 (q115 c4) ∷
   rw 7 (q113 c4) ∷
   rw⁻ 5 (q117 c4) ∷
   rw⁻ 8 (q116 c4) ∷
   rw 7 (q118 c4) ∷
   rw 11 (q119 c4) ∷
   rw 10 (q120 c4) ∷
   rw 9 (q121 c4) ∷
   rw 8 (q120 c4) ∷
   rw 7 (q122 c4) ∷
   rw⁻ 8 (q118 c4) ∷
   rw⁻ 6 (q123 c4) ∷
   rw⁻ 7 (q124 c4) ∷
   rw⁻ 3 (q110 c4) ∷
   rw 3 (q110 c4) ∷
   rw⁻ 2 (q125 c4) ∷
   rw 3 (q126 c4) ∷
   rw⁻ 4 (q125 c4) ∷
   rw 5 (q126 c4) ∷
   rw⁻ 2 (q110 c4) ∷
   rw 2 (q110 c4) ∷
   rw⁻ 1 (q113 c4) ∷
   rw⁻ 7 (q114 c4) ∷
   rw⁻ 6 (q66 c4) ∷
   rw 5 (q67 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 3 (q67 c4) ∷
   rw⁻ 2 (q69 c4) ∷
   rw⁻ 1 (q115 c4) ∷
   rw 2 (q113 c4) ∷
   rw⁻ 2 (q116 c4) ∷
   rw⁻ 4 (q113 c4) ∷
   rw⁻ 10 (q114 c4) ∷
   rw⁻ 9 (q66 c4) ∷
   rw 8 (q67 c4) ∷
   rw⁻ 7 (q68 c4) ∷
   rw 6 (q67 c4) ∷
   rw⁻ 5 (q69 c4) ∷
   rw⁻ 4 (q115 c4) ∷
   rw 5 (q113 c4) ∷
   rw⁻ 3 (q117 c4) ∷
   rw⁻ 6 (q116 c4) ∷
   rw 5 (q118 c4) ∷
   rw 9 (q119 c4) ∷
   rw 8 (q120 c4) ∷
   rw 7 (q121 c4) ∷
   rw 6 (q120 c4) ∷
   rw 5 (q122 c4) ∷
   rw⁻ 6 (q118 c4) ∷
   rw⁻ 4 (q123 c4) ∷
   rw⁻ 5 (q124 c4) ∷
   rw⁻ 1 (q110 c4) ∷
   rw 0 (q127 c4) ∷
   rw 0 (q128 c4) ∷
   rw 2 (q129 c4) ∷
   rw⁻ 0 (q130 c4) ∷ []) Eq.refl

private
  q131 : Ws → Eqn
  q131 c4 = wlE 747 (lit c4)
  q132 : Ws → Eqn
  q132 c4 = wpE 654 c4
  q133 : Ws → Eqn
  q133 c4 = eqn (CCZ024 ∷ CX13 ∷ []) (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4))
  q134 : Ws → Eqn
  q134 c4 = eqn (Toff213 ∷ CX04 ∷ []) (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4))
  q135 : Ws → Eqn
  q135 c4 = wpE 38 c4
  q136 : Ws → Eqn
  q136 c4 = eqn (Toff213 ∷ CS04 ∷ []) (CS04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CS04 (lit c4))
  q137 : Ws → Eqn
  q137 c4 = wpE 906 c4
  q138 : Ws → Eqn
  q138 c4 = wpE 907 c4
  q139 : Ws → Eqn
  q139 c4 = sE 1112 (lem-nf-comm-CS-S0at0 c4)

-- F1-comm-CS-S0@0: 91 steps
lem-F1-comm-CS-S0at0 : Ws → ⟪ (Sb2-0-41-3 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-S0at0 c4 = derive (Sb2-0-41-3 ∷ CS04 ∷ []) (CS04 ∷ Sb2-0-41-3 ∷ [])
  (re 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 2 1 (CS03 ∷ []) ∷
   re 4 1 (CS03⁻ ∷ []) ∷
   rw 0 (q61 c4) ∷
   rw 3 (q131 c4) ∷
   rw 2 (q132 c4) ∷
   rw⁻ 5 (q64 c4) ∷
   rw 4 (q70 c4) ∷
   rw 5 (q69 c4) ∷
   rw 6 (q133 c4) ∷
   rw 7 (q68 c4) ∷
   rw 8 (q133 c4) ∷
   rw 9 (q66 c4) ∷
   rw 10 (q65 c4) ∷
   rw 4 (q64 c4) ∷
   rw 1 (q78 c4) ∷
   rw 3 (q73 c4) ∷
   rw⁻ 2 (q77 c4) ∷
   rw 3 (q134 c4) ∷
   rw⁻ 4 (q76 c4) ∷
   rw 5 (q134 c4) ∷
   rw⁻ 6 (q74 c4) ∷
   rw⁻ 2 (q73 c4) ∷
   rw 3 (q131 c4) ∷
   rw⁻ 1 (q79 c4) ∷
   rw⁻ 0 (q135 c4) ∷
   rw⁻ 2 (q64 c4) ∷
   rw 1 (q70 c4) ∷
   rw 2 (q69 c4) ∷
   rw 3 (q133 c4) ∷
   rw 4 (q68 c4) ∷
   rw 5 (q133 c4) ∷
   rw 6 (q66 c4) ∷
   rw 7 (q65 c4) ∷
   rw 1 (q64 c4) ∷
   rw⁻ 2 (q61 c4) ∷
   rw 2 (q61 c4) ∷
   rw⁻ 5 (q81 c4) ∷
   rw 4 (q80 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   rw 2 (q80 c4) ∷
   rw⁻ 3 (q61 c4) ∷
   rw 3 (q61 c4) ∷
   rw 6 (q131 c4) ∷
   rw 5 (q132 c4) ∷
   rw⁻ 8 (q64 c4) ∷
   rw 7 (q70 c4) ∷
   rw 8 (q69 c4) ∷
   rw 9 (q133 c4) ∷
   rw 10 (q68 c4) ∷
   rw 11 (q133 c4) ∷
   rw 12 (q66 c4) ∷
   rw 13 (q65 c4) ∷
   rw 7 (q64 c4) ∷
   rw 4 (q78 c4) ∷
   rw 6 (q73 c4) ∷
   rw⁻ 5 (q77 c4) ∷
   rw 6 (q134 c4) ∷
   rw⁻ 7 (q76 c4) ∷
   rw 8 (q134 c4) ∷
   rw⁻ 9 (q74 c4) ∷
   rw⁻ 5 (q73 c4) ∷
   rw 6 (q131 c4) ∷
   rw⁻ 4 (q79 c4) ∷
   rw⁻ 3 (q135 c4) ∷
   rw⁻ 5 (q64 c4) ∷
   rw 4 (q70 c4) ∷
   rw 5 (q69 c4) ∷
   rw 6 (q133 c4) ∷
   rw 7 (q68 c4) ∷
   rw 8 (q133 c4) ∷
   rw 9 (q66 c4) ∷
   rw 10 (q65 c4) ∷
   rw 4 (q64 c4) ∷
   rw⁻ 5 (q61 c4) ∷
   rw 5 (q61 c4) ∷
   rw⁻ 8 (q63 c4) ∷
   rw 7 (q62 c4) ∷
   rw⁻ 6 (q63 c4) ∷
   rw 5 (q62 c4) ∷
   rw⁻ 6 (q61 c4) ∷
   rw 6 (q61 c4) ∷
   rw 9 (q136 c4) ∷
   rw 8 (q137 c4) ∷
   rw 7 (q136 c4) ∷
   rw 6 (q137 c4) ∷
   rw⁻ 7 (q61 c4) ∷
   rw 0 (q83 c4) ∷
   rw 2 (q84 c4) ∷
   rw⁻ 0 (q138 c4) ∷
   rw⁻ 0 (q139 c4) ∷ []) Eq.refl

private
  q140 : Ws → Eqn
  q140 c4 = wpE 805 c4
  q141 : Ws → Eqn
  q141 c4 = wpE 806 c4
  q142 : Ws → Eqn
  q142 c4 = eqn (CCZ014 ∷ CX23 ∷ []) (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4))
  q143 : Ws → Eqn
  q143 c4 = eqn (Toff023 ∷ CX14 ∷ []) (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4))
  q144 : Ws → Eqn
  q144 c4 = wpE 66 c4
  q145 : Ws → Eqn
  q145 c4 = eqn (Toff023 ∷ CS14 ∷ []) (CS14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CS14 (lit c4))
  q146 : Ws → Eqn
  q146 c4 = wpE 908 c4
  q147 : Ws → Eqn
  q147 c4 = wlE 1115 (lit c4)
  q148 : Ws → Eqn
  q148 c4 = sE 1113 (lem-nf-comm-CS-S0at1 c4)

-- F1-comm-CS-S0@1: 91 steps
lem-F1-comm-CS-S0at1 : Ws → ⟪ (Sb0-1-42-3 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-S0at1 c4 = derive (Sb0-1-42-3 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-42-3 ∷ [])
  (re 0 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 2 1 (CS13 ∷ []) ∷
   re 4 1 (CS13⁻ ∷ []) ∷
   rw 0 (q86 c4) ∷
   rw 3 (q140 c4) ∷
   rw 2 (q141 c4) ∷
   rw⁻ 5 (q89 c4) ∷
   rw 4 (q95 c4) ∷
   rw 5 (q94 c4) ∷
   rw 6 (q142 c4) ∷
   rw 7 (q93 c4) ∷
   rw 8 (q142 c4) ∷
   rw 9 (q91 c4) ∷
   rw 10 (q90 c4) ∷
   rw 4 (q89 c4) ∷
   rw 1 (q103 c4) ∷
   rw 3 (q98 c4) ∷
   rw⁻ 2 (q102 c4) ∷
   rw 3 (q143 c4) ∷
   rw⁻ 4 (q101 c4) ∷
   rw 5 (q143 c4) ∷
   rw⁻ 6 (q99 c4) ∷
   rw⁻ 2 (q98 c4) ∷
   rw 3 (q140 c4) ∷
   rw⁻ 1 (q104 c4) ∷
   rw 0 (q144 c4) ∷
   rw⁻ 2 (q89 c4) ∷
   rw 1 (q95 c4) ∷
   rw 2 (q94 c4) ∷
   rw 3 (q142 c4) ∷
   rw 4 (q93 c4) ∷
   rw 5 (q142 c4) ∷
   rw 6 (q91 c4) ∷
   rw 7 (q90 c4) ∷
   rw 1 (q89 c4) ∷
   rw⁻ 2 (q86 c4) ∷
   rw 2 (q86 c4) ∷
   rw⁻ 5 (q106 c4) ∷
   rw 4 (q105 c4) ∷
   rw⁻ 3 (q106 c4) ∷
   rw 2 (q105 c4) ∷
   rw⁻ 3 (q86 c4) ∷
   rw 3 (q86 c4) ∷
   rw 6 (q140 c4) ∷
   rw 5 (q141 c4) ∷
   rw⁻ 8 (q89 c4) ∷
   rw 7 (q95 c4) ∷
   rw 8 (q94 c4) ∷
   rw 9 (q142 c4) ∷
   rw 10 (q93 c4) ∷
   rw 11 (q142 c4) ∷
   rw 12 (q91 c4) ∷
   rw 13 (q90 c4) ∷
   rw 7 (q89 c4) ∷
   rw 4 (q103 c4) ∷
   rw 6 (q98 c4) ∷
   rw⁻ 5 (q102 c4) ∷
   rw 6 (q143 c4) ∷
   rw⁻ 7 (q101 c4) ∷
   rw 8 (q143 c4) ∷
   rw⁻ 9 (q99 c4) ∷
   rw⁻ 5 (q98 c4) ∷
   rw 6 (q140 c4) ∷
   rw⁻ 4 (q104 c4) ∷
   rw 3 (q144 c4) ∷
   rw⁻ 5 (q89 c4) ∷
   rw 4 (q95 c4) ∷
   rw 5 (q94 c4) ∷
   rw 6 (q142 c4) ∷
   rw 7 (q93 c4) ∷
   rw 8 (q142 c4) ∷
   rw 9 (q91 c4) ∷
   rw 10 (q90 c4) ∷
   rw 4 (q89 c4) ∷
   rw⁻ 5 (q86 c4) ∷
   rw 5 (q86 c4) ∷
   rw⁻ 8 (q88 c4) ∷
   rw 7 (q87 c4) ∷
   rw⁻ 6 (q88 c4) ∷
   rw 5 (q87 c4) ∷
   rw⁻ 6 (q86 c4) ∷
   rw 6 (q86 c4) ∷
   rw 9 (q145 c4) ∷
   rw 8 (q146 c4) ∷
   rw 7 (q145 c4) ∷
   rw 6 (q146 c4) ∷
   rw⁻ 7 (q86 c4) ∷
   rw 0 (q108 c4) ∷
   rw 2 (q31 c4) ∷
   rw⁻ 0 (q147 c4) ∷
   rw⁻ 0 (q148 c4) ∷ []) Eq.refl

private
  q149 : Ws → Eqn
  q149 c4 = wpE 843 c4
  q150 : Ws → Eqn
  q150 c4 = wpE 845 c4
  q151 : Ws → Eqn
  q151 c4 = eqn (Toff013 ∷ CX24 ∷ []) (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4))
  q152 : Ws → Eqn
  q152 c4 = wpE 90 c4
  q153 : Ws → Eqn
  q153 c4 = eqn (Toff013 ∷ CS24 ∷ []) (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4))
  q154 : Ws → Eqn
  q154 c4 = wpE 909 c4
  q155 : Ws → Eqn
  q155 c4 = wlE 1116 (lit c4)
  q156 : Ws → Eqn
  q156 c4 = sE 1114 (lem-nf-comm-CS-S0at2 c4)

-- F1-comm-CS-S0@2: 91 steps
lem-F1-comm-CS-S0at2 : Ws → ⟪ (Sb0-2-43-1 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-comm-CS-S0at2 c4 = derive (Sb0-2-43-1 ∷ CS24 ∷ []) (CS24 ∷ Sb0-2-43-1 ∷ [])
  (re 0 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 2 1 (CS12 ∷ []) ∷
   re 4 1 (CS12⁻ ∷ []) ∷
   rw 0 (q110 c4) ∷
   rw 3 (q149 c4) ∷
   rw 2 (q150 c4) ∷
   rw⁻ 5 (q113 c4) ∷
   rw 4 (q115 c4) ∷
   rw 5 (q69 c4) ∷
   rw 6 (q133 c4) ∷
   rw 7 (q68 c4) ∷
   rw 8 (q133 c4) ∷
   rw 9 (q66 c4) ∷
   rw 10 (q114 c4) ∷
   rw 4 (q113 c4) ∷
   rw 1 (q123 c4) ∷
   rw 3 (q118 c4) ∷
   rw⁻ 2 (q122 c4) ∷
   rw 3 (q151 c4) ∷
   rw⁻ 4 (q121 c4) ∷
   rw 5 (q151 c4) ∷
   rw⁻ 6 (q119 c4) ∷
   rw⁻ 2 (q118 c4) ∷
   rw 3 (q149 c4) ∷
   rw⁻ 1 (q124 c4) ∷
   rw 0 (q152 c4) ∷
   rw⁻ 2 (q113 c4) ∷
   rw 1 (q115 c4) ∷
   rw 2 (q69 c4) ∷
   rw 3 (q133 c4) ∷
   rw 4 (q68 c4) ∷
   rw 5 (q133 c4) ∷
   rw 6 (q66 c4) ∷
   rw 7 (q114 c4) ∷
   rw 1 (q113 c4) ∷
   rw⁻ 2 (q110 c4) ∷
   rw 2 (q110 c4) ∷
   rw⁻ 5 (q126 c4) ∷
   rw 4 (q125 c4) ∷
   rw⁻ 3 (q126 c4) ∷
   rw 2 (q125 c4) ∷
   rw⁻ 3 (q110 c4) ∷
   rw 3 (q110 c4) ∷
   rw 6 (q149 c4) ∷
   rw 5 (q150 c4) ∷
   rw⁻ 8 (q113 c4) ∷
   rw 7 (q115 c4) ∷
   rw 8 (q69 c4) ∷
   rw 9 (q133 c4) ∷
   rw 10 (q68 c4) ∷
   rw 11 (q133 c4) ∷
   rw 12 (q66 c4) ∷
   rw 13 (q114 c4) ∷
   rw 7 (q113 c4) ∷
   rw 4 (q123 c4) ∷
   rw 6 (q118 c4) ∷
   rw⁻ 5 (q122 c4) ∷
   rw 6 (q151 c4) ∷
   rw⁻ 7 (q121 c4) ∷
   rw 8 (q151 c4) ∷
   rw⁻ 9 (q119 c4) ∷
   rw⁻ 5 (q118 c4) ∷
   rw 6 (q149 c4) ∷
   rw⁻ 4 (q124 c4) ∷
   rw 3 (q152 c4) ∷
   rw⁻ 5 (q113 c4) ∷
   rw 4 (q115 c4) ∷
   rw 5 (q69 c4) ∷
   rw 6 (q133 c4) ∷
   rw 7 (q68 c4) ∷
   rw 8 (q133 c4) ∷
   rw 9 (q66 c4) ∷
   rw 10 (q114 c4) ∷
   rw 4 (q113 c4) ∷
   rw⁻ 5 (q110 c4) ∷
   rw 5 (q110 c4) ∷
   rw⁻ 8 (q112 c4) ∷
   rw 7 (q111 c4) ∷
   rw⁻ 6 (q112 c4) ∷
   rw 5 (q111 c4) ∷
   rw⁻ 6 (q110 c4) ∷
   rw 6 (q110 c4) ∷
   rw 9 (q153 c4) ∷
   rw 8 (q154 c4) ∷
   rw 7 (q153 c4) ∷
   rw 6 (q154 c4) ∷
   rw⁻ 7 (q110 c4) ∷
   rw 0 (q128 c4) ∷
   rw 2 (q129 c4) ∷
   rw⁻ 0 (q155 c4) ∷
   rw⁻ 0 (q156 c4) ∷ []) Eq.refl

private
  q157 : Ws → Eqn
  q157 c4 = wpE 910 c4
  q158 : Ws → Eqn
  q158 c4 = sE 1115 (lem-nf-comm-CS-S1at0 c4)

-- F1-comm-CS-S1@0: 91 steps
lem-F1-comm-CS-S1at0 : Ws → ⟪ (Sb2-0-41-3 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-S1at0 c4 = derive (Sb2-0-41-3 ∷ CS14 ∷ []) (CS14 ∷ Sb2-0-41-3 ∷ [])
  (re 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 2 1 (CS03 ∷ []) ∷
   re 4 1 (CS03⁻ ∷ []) ∷
   rw 0 (q61 c4) ∷
   rw 3 (q131 c4) ∷
   rw 2 (q132 c4) ∷
   rw⁻ 5 (q64 c4) ∷
   rw 4 (q70 c4) ∷
   rw 5 (q69 c4) ∷
   rw 6 (q133 c4) ∷
   rw 7 (q68 c4) ∷
   rw 8 (q133 c4) ∷
   rw 9 (q66 c4) ∷
   rw 10 (q65 c4) ∷
   rw 4 (q64 c4) ∷
   rw 1 (q78 c4) ∷
   rw 3 (q73 c4) ∷
   rw⁻ 2 (q77 c4) ∷
   rw 3 (q134 c4) ∷
   rw⁻ 4 (q76 c4) ∷
   rw 5 (q134 c4) ∷
   rw⁻ 6 (q74 c4) ∷
   rw⁻ 2 (q73 c4) ∷
   rw 3 (q131 c4) ∷
   rw⁻ 1 (q79 c4) ∷
   rw⁻ 0 (q135 c4) ∷
   rw⁻ 2 (q64 c4) ∷
   rw 1 (q70 c4) ∷
   rw 2 (q69 c4) ∷
   rw 3 (q133 c4) ∷
   rw 4 (q68 c4) ∷
   rw 5 (q133 c4) ∷
   rw 6 (q66 c4) ∷
   rw 7 (q65 c4) ∷
   rw 1 (q64 c4) ∷
   rw⁻ 2 (q61 c4) ∷
   rw 2 (q61 c4) ∷
   rw⁻ 5 (q81 c4) ∷
   rw 4 (q80 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   rw 2 (q80 c4) ∷
   rw⁻ 3 (q61 c4) ∷
   rw 3 (q61 c4) ∷
   rw 6 (q131 c4) ∷
   rw 5 (q132 c4) ∷
   rw⁻ 8 (q64 c4) ∷
   rw 7 (q70 c4) ∷
   rw 8 (q69 c4) ∷
   rw 9 (q133 c4) ∷
   rw 10 (q68 c4) ∷
   rw 11 (q133 c4) ∷
   rw 12 (q66 c4) ∷
   rw 13 (q65 c4) ∷
   rw 7 (q64 c4) ∷
   rw 4 (q78 c4) ∷
   rw 6 (q73 c4) ∷
   rw⁻ 5 (q77 c4) ∷
   rw 6 (q134 c4) ∷
   rw⁻ 7 (q76 c4) ∷
   rw 8 (q134 c4) ∷
   rw⁻ 9 (q74 c4) ∷
   rw⁻ 5 (q73 c4) ∷
   rw 6 (q131 c4) ∷
   rw⁻ 4 (q79 c4) ∷
   rw⁻ 3 (q135 c4) ∷
   rw⁻ 5 (q64 c4) ∷
   rw 4 (q70 c4) ∷
   rw 5 (q69 c4) ∷
   rw 6 (q133 c4) ∷
   rw 7 (q68 c4) ∷
   rw 8 (q133 c4) ∷
   rw 9 (q66 c4) ∷
   rw 10 (q65 c4) ∷
   rw 4 (q64 c4) ∷
   rw⁻ 5 (q61 c4) ∷
   rw 5 (q61 c4) ∷
   rw⁻ 8 (q63 c4) ∷
   rw 7 (q62 c4) ∷
   rw⁻ 6 (q63 c4) ∷
   rw 5 (q62 c4) ∷
   rw⁻ 6 (q61 c4) ∷
   rw 6 (q61 c4) ∷
   rw⁻ 9 (q77 c4) ∷
   rw 8 (q66 c4) ∷
   rw⁻ 7 (q77 c4) ∷
   rw 6 (q66 c4) ∷
   rw⁻ 7 (q61 c4) ∷
   rw 0 (q83 c4) ∷
   rw 2 (q84 c4) ∷
   rw⁻ 0 (q157 c4) ∷
   rw⁻ 0 (q158 c4) ∷ []) Eq.refl

private
  q159 : Ws → Eqn
  q159 c4 = wlE 1117 (lit c4)
  q160 : Ws → Eqn
  q160 c4 = sE 1116 (lem-nf-comm-CS-S1at1 c4)

-- F1-comm-CS-S1@1: 91 steps
lem-F1-comm-CS-S1at1 : Ws → ⟪ (Sb0-1-42-3 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-S1at1 c4 = derive (Sb0-1-42-3 ∷ CS24 ∷ []) (CS24 ∷ Sb0-1-42-3 ∷ [])
  (re 0 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 2 1 (CS13 ∷ []) ∷
   re 4 1 (CS13⁻ ∷ []) ∷
   rw 0 (q86 c4) ∷
   rw 3 (q140 c4) ∷
   rw 2 (q141 c4) ∷
   rw⁻ 5 (q89 c4) ∷
   rw 4 (q95 c4) ∷
   rw 5 (q94 c4) ∷
   rw 6 (q142 c4) ∷
   rw 7 (q93 c4) ∷
   rw 8 (q142 c4) ∷
   rw 9 (q91 c4) ∷
   rw 10 (q90 c4) ∷
   rw 4 (q89 c4) ∷
   rw 1 (q103 c4) ∷
   rw 3 (q98 c4) ∷
   rw⁻ 2 (q102 c4) ∷
   rw 3 (q143 c4) ∷
   rw⁻ 4 (q101 c4) ∷
   rw 5 (q143 c4) ∷
   rw⁻ 6 (q99 c4) ∷
   rw⁻ 2 (q98 c4) ∷
   rw 3 (q140 c4) ∷
   rw⁻ 1 (q104 c4) ∷
   rw 0 (q144 c4) ∷
   rw⁻ 2 (q89 c4) ∷
   rw 1 (q95 c4) ∷
   rw 2 (q94 c4) ∷
   rw 3 (q142 c4) ∷
   rw 4 (q93 c4) ∷
   rw 5 (q142 c4) ∷
   rw 6 (q91 c4) ∷
   rw 7 (q90 c4) ∷
   rw 1 (q89 c4) ∷
   rw⁻ 2 (q86 c4) ∷
   rw 2 (q86 c4) ∷
   rw⁻ 5 (q106 c4) ∷
   rw 4 (q105 c4) ∷
   rw⁻ 3 (q106 c4) ∷
   rw 2 (q105 c4) ∷
   rw⁻ 3 (q86 c4) ∷
   rw 3 (q86 c4) ∷
   rw 6 (q140 c4) ∷
   rw 5 (q141 c4) ∷
   rw⁻ 8 (q89 c4) ∷
   rw 7 (q95 c4) ∷
   rw 8 (q94 c4) ∷
   rw 9 (q142 c4) ∷
   rw 10 (q93 c4) ∷
   rw 11 (q142 c4) ∷
   rw 12 (q91 c4) ∷
   rw 13 (q90 c4) ∷
   rw 7 (q89 c4) ∷
   rw 4 (q103 c4) ∷
   rw 6 (q98 c4) ∷
   rw⁻ 5 (q102 c4) ∷
   rw 6 (q143 c4) ∷
   rw⁻ 7 (q101 c4) ∷
   rw 8 (q143 c4) ∷
   rw⁻ 9 (q99 c4) ∷
   rw⁻ 5 (q98 c4) ∷
   rw 6 (q140 c4) ∷
   rw⁻ 4 (q104 c4) ∷
   rw 3 (q144 c4) ∷
   rw⁻ 5 (q89 c4) ∷
   rw 4 (q95 c4) ∷
   rw 5 (q94 c4) ∷
   rw 6 (q142 c4) ∷
   rw 7 (q93 c4) ∷
   rw 8 (q142 c4) ∷
   rw 9 (q91 c4) ∷
   rw 10 (q90 c4) ∷
   rw 4 (q89 c4) ∷
   rw⁻ 5 (q86 c4) ∷
   rw 5 (q86 c4) ∷
   rw⁻ 8 (q88 c4) ∷
   rw 7 (q87 c4) ∷
   rw⁻ 6 (q88 c4) ∷
   rw 5 (q87 c4) ∷
   rw⁻ 6 (q86 c4) ∷
   rw 6 (q86 c4) ∷
   rw⁻ 9 (q102 c4) ∷
   rw 8 (q91 c4) ∷
   rw⁻ 7 (q102 c4) ∷
   rw 6 (q91 c4) ∷
   rw⁻ 7 (q86 c4) ∷
   rw 0 (q108 c4) ∷
   rw 2 (q31 c4) ∷
   rw⁻ 0 (q159 c4) ∷
   rw⁻ 0 (q160 c4) ∷ []) Eq.refl

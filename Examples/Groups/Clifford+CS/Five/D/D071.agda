{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD071 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D071 (Sᴰ : SD071) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS12-CCZ034 ; lem-comm-CSd12-CCZ034 ; lem-comm-TOFF013-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ014-CX23 ; lem-comm-CCZ024-CS13 ; lem-comm-CCZ024-CX13 ; lem-comm-CS04-CCZ123 ; lem-comm-CSd04-CCZ123 ; lem-comm-CX41-CCZ023 ; lem-comm-TOFF013-CS24 ; lem-comm-TOFF013-CX24 ; lem-comm-TOFF014-CX23)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX21-TOFF304 ; lem-comm-CX24-TOFF301 ; lem-comm-CX32-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-CCZ023-CX14 ; lem-comm-TOFF023-CX14)

-- The lemmas of other derivation modules (DSig).
private
  lem-box-tQ-at0220 : Ws → St 24
  lem-box-tQ-at0220 = pickᴰ 0 Sᴰ
  lem-box-tQ-at032032 : Ws → St 25
  lem-box-tQ-at032032 = pickᴰ 1 Sᴰ
  lem-box-tQ-at0314213042 : Ws → St 192
  lem-box-tQ-at0314213042 = pickᴰ 2 Sᴰ
  lem-box-tQ-at142142 : Ws → St 270
  lem-box-tQ-at142142 = pickᴰ 3 Sᴰ
  lem-box-cP-at14233142 : Ws → St 733
  lem-box-cP-at14233142 = pickᴰ 4 Sᴰ
  lem-box-cP-at0330 : Ws → St 846
  lem-box-cP-at0330 = pickᴰ 5 Sᴰ
  lem-box-cP-at12233441 : Ws → St 902
  lem-box-cP-at12233441 = pickᴰ 6 Sᴰ
  lem-box-cP-at122441 : Ws → St 850
  lem-box-cP-at122441 = pickᴰ 7 Sᴰ
  lem-box-cP-at243243 : Ws → St 856
  lem-box-cP-at243243 = pickᴰ 8 Sᴰ
  lem-box-perm-1324-at032032 : Ws → St 1518
  lem-box-perm-1324-at032032 = pickᴰ 9 Sᴰ
  lem-box-perm-2314-at13243142 : Ws → St 1519
  lem-box-perm-2314-at13243142 = pickᴰ 10 Sᴰ
  lem-box-perm-3124-at0220 : Ws → St 1520
  lem-box-perm-3124-at0220 = pickᴰ 11 Sᴰ
  lem-box-perm-3124-at032032 : Ws → St 1521
  lem-box-perm-3124-at032032 = pickᴰ 12 Sᴰ
  lem-box-perm-1324-at122441 : Ws → St 1078
  lem-box-perm-1324-at122441 = pickᴰ 13 Sᴰ
  lem-box-perm-2314-at0310243142 : Ws → St 1268
  lem-box-perm-2314-at0310243142 = pickᴰ 14 Sᴰ
  lem-box-perm-3124-at0314213042 : Ws → St 1270
  lem-box-perm-3124-at0314213042 = pickᴰ 15 Sᴰ
  lem-box-perm-1324-at142142 : Ws → St 1522
  lem-box-perm-1324-at142142 = pickᴰ 16 Sᴰ
  lem-box-perm-2314-at02132130 : Ws → St 1523
  lem-box-perm-2314-at02132130 = pickᴰ 17 Sᴰ
  lem-box-perm-2314-at03122130 : Ws → St 1524
  lem-box-perm-2314-at03122130 = pickᴰ 18 Sᴰ
  lem-box-perm-3124-at142142 : Ws → St 1525
  lem-box-perm-3124-at142142 = pickᴰ 19 Sᴰ
  lem-S2-SBOX⟨0·2·43·1⟩ : Ws → St 1314
  lem-S2-SBOX⟨0·2·43·1⟩ = pickᴰ 20 Sᴰ
  lem-L-CX01-1 : Ws → St 1526
  lem-L-CX01-1 = pickᴰ 21 Sᴰ
  lem-L-CX01-2 : Ws → St 1527
  lem-L-CX01-2 = pickᴰ 22 Sᴰ
  lem-L-CX10-2 : Ws → St 1528
  lem-L-CX10-2 = pickᴰ 23 Sᴰ
  lem-box-box-1-at03122130 : Ws → St 1529
  lem-box-box-1-at03122130 = pickᴰ 24 Sᴰ
  lem-box-box-1-at13243142 : Ws → St 1530
  lem-box-box-1-at13243142 = pickᴰ 25 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1526 (lem-L-CX01-1 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1527 (lem-L-CX01-2 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1528 (lem-L-CX10-2 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1314 (lem-S2-SBOX⟨0·2·43·1⟩ c4)
  q5 : Ws → Eqn
  q5 c4 = sE 856 (lem-box-cP-at243243 c4)
  q6 : Ws → Eqn
  q6 c4 = wpE 805 c4
  q7 : Ws → Eqn
  q7 c4 = wpE 806 c4
  q8 : Ws → Eqn
  q8 c4 = wlE 217 (lit c4)
  q9 : Ws → Eqn
  q9 c4 = wpE 65 c4
  q10 : Ws → Eqn
  q10 c4 = wpE 64 c4
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ014 ∷ CX23 ∷ []) (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = wpE 63 c4
  q13 : Ws → Eqn
  q13 c4 = wpE 62 c4
  q14 : Ws → Eqn
  q14 c4 = wpE 61 c4
  q15 : Ws → Eqn
  q15 c4 = wpE 72 c4
  q16 : Ws → Eqn
  q16 c4 = wlE 220 (lit c4)
  q17 : Ws → Eqn
  q17 c4 = wpE 70 c4
  q18 : Ws → Eqn
  q18 c4 = eqn (Toff023 ∷ CX14 ∷ []) (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = wpE 69 c4
  q20 : Ws → Eqn
  q20 c4 = wlE 221 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = wpE 74 c4
  q22 : Ws → Eqn
  q22 c4 = wpE 66 c4
  q23 : Ws → Eqn
  q23 c4 = wlE 222 (lit c4)
  q24 : Ws → Eqn
  q24 c4 = wpE 53 c4
  q25 : Ws → Eqn
  q25 c4 = wlE 219 (lit c4)
  q26 : Ws → Eqn
  q26 c4 = wpE 60 c4
  q27 : Ws → Eqn
  q27 c4 = wpE 1208 c4
  q28 : Ws → Eqn
  q28 c4 = wpE 1209 c4
  q29 : Ws → Eqn
  q29 c4 = wlE 1374 (lit c4)
  q30 : Ws → Eqn
  q30 c4 = wpE 1210 c4
  q31 : Ws → Eqn
  q31 c4 = wpE 1211 c4
  q32 : Ws → Eqn
  q32 c4 = wpE 173 c4
  q33 : Ws → Eqn
  q33 c4 = wlE 698 (lit c4)
  q34 : Ws → Eqn
  q34 c4 = wpE 725 c4
  q35 : Ws → Eqn
  q35 c4 = wpE 823 c4
  q36 : Ws → Eqn
  q36 c4 = wpE 1212 c4
  q37 : Ws → Eqn
  q37 c4 = wpE 272 c4
  q38 : Ws → Eqn
  q38 c4 = sE 850 (lem-box-cP-at122441 c4)
  q39 : Ws → Eqn
  q39 c4 = wpE 843 c4
  q40 : Ws → Eqn
  q40 c4 = wpE 845 c4
  q41 : Ws → Eqn
  q41 c4 = wlE 241 (lit c4)
  q42 : Ws → Eqn
  q42 c4 = wpE 89 c4
  q43 : Ws → Eqn
  q43 c4 = wpE 36 c4
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ024 ∷ CX13 ∷ []) (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = wpE 35 c4
  q46 : Ws → Eqn
  q46 c4 = wpE 34 c4
  q47 : Ws → Eqn
  q47 c4 = wpE 88 c4
  q48 : Ws → Eqn
  q48 c4 = wpE 97 c4
  q49 : Ws → Eqn
  q49 c4 = wlE 245 (lit c4)
  q50 : Ws → Eqn
  q50 c4 = wpE 95 c4
  q51 : Ws → Eqn
  q51 c4 = eqn (Toff013 ∷ CX24 ∷ []) (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = wpE 94 c4
  q53 : Ws → Eqn
  q53 c4 = wlE 246 (lit c4)
  q54 : Ws → Eqn
  q54 c4 = wpE 842 c4
  q55 : Ws → Eqn
  q55 c4 = wpE 90 c4
  q56 : Ws → Eqn
  q56 c4 = wlE 247 (lit c4)
  q57 : Ws → Eqn
  q57 c4 = wpE 81 c4
  q58 : Ws → Eqn
  q58 c4 = wlE 244 (lit c4)
  q59 : Ws → Eqn
  q59 c4 = wpE 87 c4
  q60 : Ws → Eqn
  q60 c4 = wlE 888 (lit c4)
  q61 : Ws → Eqn
  q61 c4 = wlE 743 (lit c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (Toff013 ∷ CS24 ∷ []) (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = wlE 872 (lit c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (Toff013 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = wpE 785 c4
  q66 : Ws → Eqn
  q66 c4 = wlE 1375 (lit c4)
  q67 : Ws → Eqn
  q67 c4 = wpE 654 c4
  q68 : Ws → Eqn
  q68 c4 = wpE 1213 c4
  q69 : Ws → Eqn
  q69 c4 = wpE 38 c4
  q70 : Ws → Eqn
  q70 c4 = wlE 166 (lit c4)
  q71 : Ws → Eqn
  q71 c4 = wpE 753 c4
  q72 : Ws → Eqn
  q72 c4 = sE 1078 (lem-box-perm-1324-at122441 c4)
  q73 : Ws → Eqn
  q73 c4 = sE 902 (lem-box-cP-at12233441 c4)
  q74 : Ws → Eqn
  q74 c4 = wpE 819 c4
  q75 : Ws → Eqn
  q75 c4 = wpE 546 c4
  q76 : Ws → Eqn
  q76 c4 = eqn (Toff014 ∷ CX23 ∷ []) (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4))
  q77 : Ws → Eqn
  q77 c4 = wpE 818 c4
  q78 : Ws → Eqn
  q78 c4 = wpE 817 c4
  q79 : Ws → Eqn
  q79 c4 = wpE 816 c4
  q80 : Ws → Eqn
  q80 c4 = wpE 1046 c4
  q81 : Ws → Eqn
  q81 c4 = wpE 839 c4
  q82 : Ws → Eqn
  q82 c4 = wpE 669 c4
  q83 : Ws → Eqn
  q83 c4 = wpE 513 c4
  q84 : Ws → Eqn
  q84 c4 = eqn (CCZ023 ∷ CX14 ∷ []) (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4))
  q85 : Ws → Eqn
  q85 c4 = wpE 820 c4
  q86 : Ws → Eqn
  q86 c4 = wlE 621 (lit c4)
  q87 : Ws → Eqn
  q87 c4 = wpE 821 c4
  q88 : Ws → Eqn
  q88 c4 = wlE 1376 (lit c4)
  q89 : Ws → Eqn
  q89 c4 = wpE 790 c4
  q90 : Ws → Eqn
  q90 c4 = wpE 1214 c4
  q91 : Ws → Eqn
  q91 c4 = wpE 109 c4
  q92 : Ws → Eqn
  q92 c4 = wpE 1215 c4
  q93 : Ws → Eqn
  q93 c4 = wlE 256 (lit c4)
  q94 : Ws → Eqn
  q94 c4 = wpE 827 c4
  q95 : Ws → Eqn
  q95 c4 = wlE 910 (lit c4)
  q96 : Ws → Eqn
  q96 c4 = eqn (CCZ024 ∷ CS13 ∷ []) (CS13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CS13 (lit c4))

-- L-CCZ-1 part0: 500 steps
lem-L-CCZ-1-part0 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ134 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-L-CCZ-1-part0 c4 = derive (Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ134 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ Bx0-1423 ∷ [])
  (rw 1 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q2 c4) ∷
   rw 7 (q3 c4) ∷
   rw 8 (q2 c4) ∷
   rw 10 (q2 c4) ∷
   rw 11 (q3 c4) ∷
   rw 12 (q2 c4) ∷
   rw 2 (q4 c4) ∷
   re 0 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 2 1 (CS12 ∷ []) ∷
   re 4 1 (CS12⁻ ∷ []) ∷
   re 7 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 9 1 (CS12 ∷ []) ∷
   re 11 1 (CS12⁻ ∷ []) ∷
   re 16 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 18 1 (CS13 ∷ []) ∷
   re 20 1 (CS13⁻ ∷ []) ∷
   rw 16 (q5 c4) ∷
   rw 19 (q6 c4) ∷
   rw 18 (q7 c4) ∷
   rw⁻ 21 (q8 c4) ∷
   rw 20 (q9 c4) ∷
   rw 21 (q10 c4) ∷
   rw 22 (q11 c4) ∷
   rw 23 (q12 c4) ∷
   rw 24 (q11 c4) ∷
   rw 25 (q13 c4) ∷
   rw 26 (q14 c4) ∷
   rw 20 (q8 c4) ∷
   rw 17 (q15 c4) ∷
   rw 19 (q16 c4) ∷
   rw⁻ 18 (q17 c4) ∷
   rw 19 (q18 c4) ∷
   rw⁻ 20 (q19 c4) ∷
   rw 21 (q18 c4) ∷
   rw⁻ 22 (q20 c4) ∷
   rw⁻ 18 (q16 c4) ∷
   rw 19 (q6 c4) ∷
   rw⁻ 17 (q21 c4) ∷
   rw 16 (q22 c4) ∷
   rw⁻ 18 (q8 c4) ∷
   rw 17 (q9 c4) ∷
   rw 18 (q10 c4) ∷
   rw 19 (q11 c4) ∷
   rw 20 (q12 c4) ∷
   rw 21 (q11 c4) ∷
   rw 22 (q13 c4) ∷
   rw 23 (q14 c4) ∷
   rw 17 (q8 c4) ∷
   rw⁻ 18 (q5 c4) ∷
   rw 18 (q5 c4) ∷
   rw⁻ 21 (q23 c4) ∷
   rw 20 (q24 c4) ∷
   rw⁻ 19 (q23 c4) ∷
   rw 18 (q24 c4) ∷
   rw⁻ 19 (q5 c4) ∷
   rw 19 (q5 c4) ∷
   rw 22 (q6 c4) ∷
   rw 21 (q7 c4) ∷
   rw⁻ 24 (q8 c4) ∷
   rw 23 (q9 c4) ∷
   rw 24 (q10 c4) ∷
   rw 25 (q11 c4) ∷
   rw 26 (q12 c4) ∷
   rw 27 (q11 c4) ∷
   rw 28 (q13 c4) ∷
   rw 29 (q14 c4) ∷
   rw 23 (q8 c4) ∷
   rw 20 (q15 c4) ∷
   rw 22 (q16 c4) ∷
   rw⁻ 21 (q17 c4) ∷
   rw 22 (q18 c4) ∷
   rw⁻ 23 (q19 c4) ∷
   rw 24 (q18 c4) ∷
   rw⁻ 25 (q20 c4) ∷
   rw⁻ 21 (q16 c4) ∷
   rw 22 (q6 c4) ∷
   rw⁻ 20 (q21 c4) ∷
   rw 19 (q22 c4) ∷
   rw⁻ 21 (q8 c4) ∷
   rw 20 (q9 c4) ∷
   rw 21 (q10 c4) ∷
   rw 22 (q11 c4) ∷
   rw 23 (q12 c4) ∷
   rw 24 (q11 c4) ∷
   rw 25 (q13 c4) ∷
   rw 26 (q14 c4) ∷
   rw 20 (q8 c4) ∷
   rw⁻ 21 (q5 c4) ∷
   rw 21 (q5 c4) ∷
   rw⁻ 24 (q25 c4) ∷
   rw 23 (q26 c4) ∷
   rw⁻ 22 (q25 c4) ∷
   rw 21 (q26 c4) ∷
   rw⁻ 22 (q5 c4) ∷
   rw 22 (q5 c4) ∷
   rw 25 (q6 c4) ∷
   rw 24 (q7 c4) ∷
   rw⁻ 27 (q8 c4) ∷
   rw 26 (q9 c4) ∷
   rw 27 (q10 c4) ∷
   rw 28 (q11 c4) ∷
   rw 29 (q12 c4) ∷
   rw 30 (q11 c4) ∷
   rw 31 (q13 c4) ∷
   rw 32 (q14 c4) ∷
   rw 26 (q8 c4) ∷
   rw 23 (q15 c4) ∷
   rw 25 (q16 c4) ∷
   rw⁻ 24 (q17 c4) ∷
   rw 25 (q18 c4) ∷
   rw⁻ 26 (q19 c4) ∷
   rw 27 (q18 c4) ∷
   rw⁻ 28 (q20 c4) ∷
   rw⁻ 24 (q16 c4) ∷
   rw 25 (q6 c4) ∷
   rw⁻ 23 (q21 c4) ∷
   rw 22 (q22 c4) ∷
   rw⁻ 24 (q8 c4) ∷
   rw 23 (q9 c4) ∷
   rw 24 (q10 c4) ∷
   rw 25 (q11 c4) ∷
   rw 26 (q12 c4) ∷
   rw 27 (q11 c4) ∷
   rw 28 (q13 c4) ∷
   rw 29 (q14 c4) ∷
   rw 23 (q8 c4) ∷
   rw⁻ 24 (q5 c4) ∷
   rw 24 (q5 c4) ∷
   rw 27 (q27 c4) ∷
   rw 26 (q28 c4) ∷
   rw⁻ 29 (q29 c4) ∷
   rw 28 (q30 c4) ∷
   rw 29 (q10 c4) ∷
   rw 30 (q11 c4) ∷
   rw 31 (q12 c4) ∷
   rw 32 (q11 c4) ∷
   rw 33 (q13 c4) ∷
   rw 34 (q31 c4) ∷
   rw 28 (q29 c4) ∷
   rw 25 (q32 c4) ∷
   rw 27 (q33 c4) ∷
   rw⁻ 26 (q34 c4) ∷
   rw 27 (q18 c4) ∷
   rw⁻ 28 (q35 c4) ∷
   rw 29 (q18 c4) ∷
   rw⁻ 30 (q23 c4) ∷
   rw⁻ 26 (q33 c4) ∷
   rw 27 (q27 c4) ∷
   rw⁻ 25 (q36 c4) ∷
   rw 24 (q37 c4) ∷
   rw⁻ 26 (q29 c4) ∷
   rw 25 (q30 c4) ∷
   rw 26 (q10 c4) ∷
   rw 27 (q11 c4) ∷
   rw 28 (q12 c4) ∷
   rw 29 (q11 c4) ∷
   rw 30 (q13 c4) ∷
   rw 31 (q31 c4) ∷
   rw 25 (q29 c4) ∷
   rw⁻ 26 (q5 c4) ∷
   rw 26 (q5 c4) ∷
   rw 29 (q6 c4) ∷
   rw 28 (q7 c4) ∷
   rw⁻ 31 (q8 c4) ∷
   rw 30 (q9 c4) ∷
   rw 31 (q10 c4) ∷
   rw 32 (q11 c4) ∷
   rw 33 (q12 c4) ∷
   rw 34 (q11 c4) ∷
   rw 35 (q13 c4) ∷
   rw 36 (q14 c4) ∷
   rw 30 (q8 c4) ∷
   rw 27 (q15 c4) ∷
   rw 29 (q16 c4) ∷
   rw⁻ 28 (q17 c4) ∷
   rw 29 (q18 c4) ∷
   rw⁻ 30 (q19 c4) ∷
   rw 31 (q18 c4) ∷
   rw⁻ 32 (q20 c4) ∷
   rw⁻ 28 (q16 c4) ∷
   rw 29 (q6 c4) ∷
   rw⁻ 27 (q21 c4) ∷
   rw 26 (q22 c4) ∷
   rw⁻ 28 (q8 c4) ∷
   rw 27 (q9 c4) ∷
   rw 28 (q10 c4) ∷
   rw 29 (q11 c4) ∷
   rw 30 (q12 c4) ∷
   rw 31 (q11 c4) ∷
   rw 32 (q13 c4) ∷
   rw 33 (q14 c4) ∷
   rw 27 (q8 c4) ∷
   rw⁻ 28 (q5 c4) ∷
   rw 7 (q38 c4) ∷
   rw 10 (q39 c4) ∷
   rw 9 (q40 c4) ∷
   rw⁻ 12 (q41 c4) ∷
   rw 11 (q42 c4) ∷
   rw 12 (q43 c4) ∷
   rw 13 (q44 c4) ∷
   rw 14 (q45 c4) ∷
   rw 15 (q44 c4) ∷
   rw 16 (q46 c4) ∷
   rw 17 (q47 c4) ∷
   rw 11 (q41 c4) ∷
   rw 8 (q48 c4) ∷
   rw 10 (q49 c4) ∷
   rw⁻ 9 (q50 c4) ∷
   rw 10 (q51 c4) ∷
   rw⁻ 11 (q52 c4) ∷
   rw 12 (q51 c4) ∷
   rw⁻ 13 (q53 c4) ∷
   rw⁻ 9 (q49 c4) ∷
   rw 10 (q39 c4) ∷
   rw⁻ 8 (q54 c4) ∷
   rw 7 (q55 c4) ∷
   rw⁻ 9 (q41 c4) ∷
   rw 8 (q42 c4) ∷
   rw 9 (q43 c4) ∷
   rw 10 (q44 c4) ∷
   rw 11 (q45 c4) ∷
   rw 12 (q44 c4) ∷
   rw 13 (q46 c4) ∷
   rw 14 (q47 c4) ∷
   rw 8 (q41 c4) ∷
   rw⁻ 9 (q38 c4) ∷
   rw 9 (q38 c4) ∷
   rw⁻ 12 (q56 c4) ∷
   rw 11 (q57 c4) ∷
   rw⁻ 10 (q56 c4) ∷
   rw 9 (q57 c4) ∷
   rw⁻ 10 (q38 c4) ∷
   rw 10 (q38 c4) ∷
   rw 13 (q39 c4) ∷
   rw 12 (q40 c4) ∷
   rw⁻ 15 (q41 c4) ∷
   rw 14 (q42 c4) ∷
   rw 15 (q43 c4) ∷
   rw 16 (q44 c4) ∷
   rw 17 (q45 c4) ∷
   rw 18 (q44 c4) ∷
   rw 19 (q46 c4) ∷
   rw 20 (q47 c4) ∷
   rw 14 (q41 c4) ∷
   rw 11 (q48 c4) ∷
   rw 13 (q49 c4) ∷
   rw⁻ 12 (q50 c4) ∷
   rw 13 (q51 c4) ∷
   rw⁻ 14 (q52 c4) ∷
   rw 15 (q51 c4) ∷
   rw⁻ 16 (q53 c4) ∷
   rw⁻ 12 (q49 c4) ∷
   rw 13 (q39 c4) ∷
   rw⁻ 11 (q54 c4) ∷
   rw 10 (q55 c4) ∷
   rw⁻ 12 (q41 c4) ∷
   rw 11 (q42 c4) ∷
   rw 12 (q43 c4) ∷
   rw 13 (q44 c4) ∷
   rw 14 (q45 c4) ∷
   rw 15 (q44 c4) ∷
   rw 16 (q46 c4) ∷
   rw 17 (q47 c4) ∷
   rw 11 (q41 c4) ∷
   rw⁻ 12 (q38 c4) ∷
   rw 12 (q38 c4) ∷
   rw⁻ 15 (q58 c4) ∷
   rw 14 (q59 c4) ∷
   rw⁻ 13 (q58 c4) ∷
   rw 12 (q59 c4) ∷
   rw⁻ 13 (q38 c4) ∷
   rw 13 (q38 c4) ∷
   rw⁻ 17 (q60 c4) ∷
   rw⁻ 16 (q61 c4) ∷
   rw 17 (q62 c4) ∷
   rw⁻ 18 (q63 c4) ∷
   rw 19 (q64 c4) ∷
   rw⁻ 20 (q63 c4) ∷
   rw⁻ 21 (q65 c4) ∷
   rw⁻ 22 (q66 c4) ∷
   rw 16 (q60 c4) ∷
   rw 15 (q67 c4) ∷
   rw⁻ 15 (q60 c4) ∷
   rw⁻ 14 (q61 c4) ∷
   rw 15 (q62 c4) ∷
   rw⁻ 16 (q63 c4) ∷
   rw 17 (q64 c4) ∷
   rw⁻ 18 (q63 c4) ∷
   rw⁻ 19 (q65 c4) ∷
   rw⁻ 20 (q66 c4) ∷
   rw 14 (q60 c4) ∷
   rw⁻ 15 (q68 c4) ∷
   rw 13 (q67 c4) ∷
   rw⁻ 15 (q69 c4) ∷
   rw 17 (q70 c4) ∷
   rw 16 (q43 c4) ∷
   rw 17 (q44 c4) ∷
   rw 18 (q45 c4) ∷
   rw 19 (q44 c4) ∷
   rw 20 (q46 c4) ∷
   rw⁻ 16 (q70 c4) ∷
   rw 13 (q71 c4) ∷
   rw⁻ 15 (q38 c4) ∷
   rw 15 (q72 c4) ∷
   rw 15 (q73 c4) ∷
   rw⁻ 19 (q8 c4) ∷
   rw⁻ 18 (q74 c4) ∷
   rw⁻ 19 (q75 c4) ∷
   rw 20 (q76 c4) ∷
   rw⁻ 21 (q77 c4) ∷
   rw 22 (q76 c4) ∷
   rw⁻ 23 (q78 c4) ∷
   rw⁻ 24 (q79 c4) ∷
   rw 18 (q8 c4) ∷
   rw 17 (q80 c4) ∷
   rw⁻ 17 (q8 c4) ∷
   rw⁻ 16 (q74 c4) ∷
   rw⁻ 17 (q75 c4) ∷
   rw 18 (q76 c4) ∷
   rw⁻ 19 (q77 c4) ∷
   rw 20 (q76 c4) ∷
   rw⁻ 21 (q78 c4) ∷
   rw⁻ 22 (q79 c4) ∷
   rw 16 (q8 c4) ∷
   rw⁻ 17 (q81 c4) ∷
   rw 15 (q80 c4) ∷
   rw 17 (q82 c4) ∷
   rw 19 (q16 c4) ∷
   rw 18 (q83 c4) ∷
   rw 19 (q84 c4) ∷
   rw 20 (q85 c4) ∷
   rw 21 (q84 c4) ∷
   rw 22 (q86 c4) ∷
   rw⁻ 18 (q16 c4) ∷
   rw 15 (q87 c4) ∷
   rw⁻ 17 (q73 c4) ∷
   rw⁻ 17 (q72 c4) ∷
   rw 17 (q38 c4) ∷
   rw⁻ 21 (q88 c4) ∷
   rw⁻ 20 (q61 c4) ∷
   rw⁻ 21 (q50 c4) ∷
   rw 22 (q51 c4) ∷
   rw⁻ 23 (q52 c4) ∷
   rw 24 (q51 c4) ∷
   rw⁻ 25 (q53 c4) ∷
   rw⁻ 26 (q66 c4) ∷
   rw 20 (q88 c4) ∷
   rw 19 (q89 c4) ∷
   rw⁻ 19 (q88 c4) ∷
   rw⁻ 18 (q61 c4) ∷
   rw⁻ 19 (q50 c4) ∷
   rw 20 (q51 c4) ∷
   rw⁻ 21 (q52 c4) ∷
   rw 22 (q51 c4) ∷
   rw⁻ 23 (q53 c4) ∷
   rw⁻ 24 (q66 c4) ∷
   rw 18 (q88 c4) ∷
   rw⁻ 19 (q90 c4) ∷
   rw 17 (q89 c4) ∷
   rw 19 (q91 c4) ∷
   rw 21 (q70 c4) ∷
   rw 20 (q43 c4) ∷
   rw 21 (q44 c4) ∷
   rw 22 (q45 c4) ∷
   rw 23 (q44 c4) ∷
   rw 24 (q46 c4) ∷
   rw⁻ 20 (q70 c4) ∷
   rw 17 (q92 c4) ∷
   rw⁻ 19 (q38 c4) ∷
   rw 19 (q72 c4) ∷
   rw 19 (q73 c4) ∷
   rw⁻ 23 (q8 c4) ∷
   rw⁻ 22 (q74 c4) ∷
   rw⁻ 23 (q75 c4) ∷
   rw 24 (q76 c4) ∷
   rw⁻ 25 (q77 c4) ∷
   rw 26 (q76 c4) ∷
   rw⁻ 27 (q78 c4) ∷
   rw⁻ 28 (q79 c4) ∷
   rw 22 (q8 c4) ∷
   rw 21 (q80 c4) ∷
   rw⁻ 21 (q8 c4) ∷
   rw⁻ 20 (q74 c4) ∷
   rw⁻ 21 (q75 c4) ∷
   rw 22 (q76 c4) ∷
   rw⁻ 23 (q77 c4) ∷
   rw 24 (q76 c4) ∷
   rw⁻ 25 (q78 c4) ∷
   rw⁻ 26 (q79 c4) ∷
   rw 20 (q8 c4) ∷
   rw⁻ 21 (q81 c4) ∷
   rw 19 (q80 c4) ∷
   rw 21 (q82 c4) ∷
   rw 23 (q16 c4) ∷
   rw 22 (q83 c4) ∷
   rw 23 (q84 c4) ∷
   rw 24 (q85 c4) ∷
   rw 25 (q84 c4) ∷
   rw 26 (q86 c4) ∷
   rw⁻ 22 (q16 c4) ∷
   rw 19 (q87 c4) ∷
   rw⁻ 21 (q73 c4) ∷
   rw⁻ 21 (q72 c4) ∷
   rw 21 (q38 c4) ∷
   rw 25 (q93 c4) ∷
   rw 24 (q62 c4) ∷
   rw⁻ 25 (q63 c4) ∷
   rw 26 (q64 c4) ∷
   rw⁻ 27 (q63 c4) ∷
   rw⁻ 28 (q65 c4) ∷
   rw⁻ 24 (q93 c4) ∷
   rw 23 (q94 c4) ∷
   rw 23 (q93 c4) ∷
   rw 22 (q62 c4) ∷
   rw⁻ 23 (q63 c4) ∷
   rw 24 (q64 c4) ∷
   rw⁻ 25 (q63 c4) ∷
   rw⁻ 26 (q65 c4) ∷
   rw⁻ 22 (q93 c4) ∷
   rw 21 (q94 c4) ∷
   rw⁻ 22 (q38 c4) ∷
   rw 22 (q72 c4) ∷
   rw 22 (q73 c4) ∷
   rw⁻ 26 (q8 c4) ∷
   rw⁻ 25 (q74 c4) ∷
   rw⁻ 26 (q75 c4) ∷
   rw 27 (q76 c4) ∷
   rw⁻ 28 (q77 c4) ∷
   rw 29 (q76 c4) ∷
   rw⁻ 30 (q78 c4) ∷
   rw⁻ 31 (q79 c4) ∷
   rw 25 (q8 c4) ∷
   rw 24 (q80 c4) ∷
   rw⁻ 24 (q8 c4) ∷
   rw⁻ 23 (q74 c4) ∷
   rw⁻ 24 (q75 c4) ∷
   rw 25 (q76 c4) ∷
   rw⁻ 26 (q77 c4) ∷
   rw 27 (q76 c4) ∷
   rw⁻ 28 (q78 c4) ∷
   rw⁻ 29 (q79 c4) ∷
   rw 23 (q8 c4) ∷
   rw⁻ 24 (q81 c4) ∷
   rw 22 (q80 c4) ∷
   rw 24 (q82 c4) ∷
   rw 26 (q16 c4) ∷
   rw 25 (q83 c4) ∷
   rw 26 (q84 c4) ∷
   rw 27 (q85 c4) ∷
   rw 28 (q84 c4) ∷
   rw 29 (q86 c4) ∷
   rw⁻ 25 (q16 c4) ∷
   rw 22 (q87 c4) ∷
   rw⁻ 24 (q73 c4) ∷
   rw⁻ 24 (q72 c4) ∷
   rw 24 (q38 c4) ∷
   rw⁻ 27 (q95 c4) ∷
   rw 26 (q96 c4) ∷
   rw⁻ 25 (q95 c4) ∷
   rw 24 (q96 c4) ∷
   rw⁻ 25 (q38 c4) ∷
   rw 25 (q38 c4) ∷
   rw 29 (q93 c4) ∷
   rw 28 (q62 c4) ∷
   rw⁻ 29 (q63 c4) ∷
   rw 30 (q64 c4) ∷
   rw⁻ 31 (q63 c4) ∷
   rw⁻ 32 (q65 c4) ∷
   rw⁻ 28 (q93 c4) ∷
   rw 27 (q94 c4) ∷
   rw 27 (q93 c4) ∷
   rw 26 (q62 c4) ∷
   rw⁻ 27 (q63 c4) ∷
   rw 28 (q64 c4) ∷
   rw⁻ 29 (q63 c4) ∷
   rw⁻ 30 (q65 c4) ∷
   rw⁻ 26 (q93 c4) ∷
   rw 25 (q94 c4) ∷
   rw⁻ 26 (q38 c4) ∷
   rw 26 (q72 c4) ∷
   rw 26 (q73 c4) ∷
   rw⁻ 30 (q8 c4) ∷
   rw⁻ 29 (q74 c4) ∷
   rw⁻ 30 (q75 c4) ∷
   rw 31 (q76 c4) ∷
   rw⁻ 32 (q77 c4) ∷
   rw 33 (q76 c4) ∷
   rw⁻ 34 (q78 c4) ∷
   rw⁻ 35 (q79 c4) ∷
   rw 29 (q8 c4) ∷
   rw 28 (q80 c4) ∷
   rw⁻ 28 (q8 c4) ∷
   rw⁻ 27 (q74 c4) ∷
   rw⁻ 28 (q75 c4) ∷
   rw 29 (q76 c4) ∷
   rw⁻ 30 (q77 c4) ∷
   rw 31 (q76 c4) ∷
   rw⁻ 32 (q78 c4) ∷ []) Eq.refl

private
  q97 : Ws → Eqn
  q97 c4 = sE 24 (lem-box-tQ-at0220 c4)
  q98 : Ws → Eqn
  q98 c4 = wlE 1381 (lit c4)
  q99 : Ws → Eqn
  q99 c4 = wlE 1382 (lit c4)
  q100 : Ws → Eqn
  q100 c4 = wlE 1383 (lit c4)
  q101 : Ws → Eqn
  q101 c4 = wpE 1223 c4
  q102 : Ws → Eqn
  q102 c4 = wpE 1173 c4
  q103 : Ws → Eqn
  q103 c4 = wlE 644 (lit c4)
  q104 : Ws → Eqn
  q104 c4 = wlE 1384 (lit c4)
  q105 : Ws → Eqn
  q105 c4 = eqn (CX24 ∷ Toff301 ∷ []) (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4))
  q106 : Ws → Eqn
  q106 c4 = wpE 1224 c4
  q107 : Ws → Eqn
  q107 c4 = wpE 379 c4
  q108 : Ws → Eqn
  q108 c4 = wlE 1385 (lit c4)
  q109 : Ws → Eqn
  q109 c4 = wpE 341 c4
  q110 : Ws → Eqn
  q110 c4 = wlE 452 (lit c4)
  q111 : Ws → Eqn
  q111 c4 = eqn (CX10 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ))
  q112 : Ws → Eqn
  q112 c4 = wpE 342 c4
  q113 : Ws → Eqn
  q113 c4 = wpE 302 c4
  q114 : Ws → Eqn
  q114 c4 = wlE 1386 (lit c4)
  q115 : Ws → Eqn
  q115 c4 = wlE 305 (lit c4)
  q116 : Ws → Eqn
  q116 c4 = sE 25 (lem-box-tQ-at032032 c4)
  q117 : Ws → Eqn
  q117 c4 = sE 1518 (lem-box-perm-1324-at032032 c4)
  q118 : Ws → Eqn
  q118 c4 = sE 846 (lem-box-cP-at0330 c4)
  q119 : Ws → Eqn
  q119 c4 = wlE 696 (lit c4)
  q120 : Ws → Eqn
  q120 c4 = wpE 1159 c4
  q121 : Ws → Eqn
  q121 c4 = wlE 1387 (lit c4)
  q122 : Ws → Eqn
  q122 c4 = wpE 1038 c4
  q123 : Ws → Eqn
  q123 c4 = wpE 1065 c4
  q124 : Ws → Eqn
  q124 c4 = eqn (CX21 ∷ Toff304 ∷ []) (Toff304 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF304 (lit c4))
  q125 : Ws → Eqn
  q125 c4 = wpE 1225 c4
  q126 : Ws → Eqn
  q126 c4 = wpE 1058 c4
  q127 : Ws → Eqn
  q127 c4 = wpE 1035 c4
  q128 : Ws → Eqn
  q128 c4 = wlE 765 (lit c4)
  q129 : Ws → Eqn
  q129 c4 = wlE 616 (lit c4)
  q130 : Ws → Eqn
  q130 c4 = eqn (CS04⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 (lit c4))
  q131 : Ws → Eqn
  q131 c4 = eqn (CS04 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4))
  q132 : Ws → Eqn
  q132 c4 = wlE 327 (lit c4)
  q133 : Ws → Eqn
  q133 c4 = wlE 1366 (lit c4)
  q134 : Ws → Eqn
  q134 c4 = wpE 687 c4
  q135 : Ws → Eqn
  q135 c4 = wpE 1189 c4
  q136 : Ws → Eqn
  q136 c4 = wpE 161 c4
  q137 : Ws → Eqn
  q137 c4 = sE 1521 (lem-box-perm-3124-at032032 c4)
  q138 : Ws → Eqn
  q138 c4 = sE 1520 (lem-box-perm-3124-at0220 c4)
  q139 : Ws → Eqn
  q139 c4 = sE 1529 (lem-box-box-1-at03122130 c4)
  q140 : Ws → Eqn
  q140 c4 = sE 1523 (lem-box-perm-2314-at02132130 c4)
  q141 : Ws → Eqn
  q141 c4 = sE 1524 (lem-box-perm-2314-at03122130 c4)

-- Tu-box @0220: 83 steps
lem-Tu-box-at0220 : Ws → ⟪ (Toff312 ∷ Bx2-1034 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ Bx3-1024 ∷ []) ⟫ʷ
lem-Tu-box-at0220 c4 = derive (Toff312 ∷ Bx2-1034 ∷ Toff312 ∷ []) (Bx2-1034 ∷ Bx3-1024 ∷ [])
  (rw 1 (q97 c4) ∷
   rw⁻ 0 (q98 c4) ∷
   rw⁻ 2 (q99 c4) ∷
   rw⁻ 4 (q98 c4) ∷
   rw⁻ 6 (q100 c4) ∷
   rw 3 (q101 c4) ∷
   rw 5 (q102 c4) ∷
   rw 4 (q103 c4) ∷
   rw 8 (q104 c4) ∷
   rw 7 (q105 c4) ∷
   rw 6 (q106 c4) ∷
   rw 5 (q105 c4) ∷
   rw 4 (q107 c4) ∷
   rw⁻ 5 (q103 c4) ∷
   rw⁻ 5 (q22 c4) ∷
   rw 6 (q108 c4) ∷
   rw 5 (q109 c4) ∷
   rw⁻ 9 (q110 c4) ∷
   rw 8 (q111 c4) ∷
   rw⁻ 7 (q112 c4) ∷
   rw 6 (q111 c4) ∷
   rw⁻ 5 (q113 c4) ∷
   rw⁻ 6 (q109 c4) ∷
   rw 3 (q114 c4) ∷
   rw⁻ 4 (q115 c4) ∷
   rw⁻ 1 (q116 c4) ∷
   rw 1 (q117 c4) ∷
   rw 1 (q118 c4) ∷
   rw⁻ 0 (q119 c4) ∷
   rw 2 (q120 c4) ∷
   rw⁻ 1 (q121 c4) ∷
   rw 7 (q122 c4) ∷
   rw 6 (q123 c4) ∷
   rw 5 (q124 c4) ∷
   rw 4 (q125 c4) ∷
   rw 3 (q124 c4) ∷
   rw 2 (q126 c4) ∷
   rw 1 (q127 c4) ∷
   rw 2 (q121 c4) ∷
   rw 4 (q109 c4) ∷
   rw⁻ 8 (q128 c4) ∷
   rw⁻ 7 (q129 c4) ∷
   rw 6 (q130 c4) ∷
   rw⁻ 5 (q129 c4) ∷
   rw 4 (q131 c4) ∷
   rw⁻ 5 (q109 c4) ∷
   rw 3 (q132 c4) ∷
   rw⁻ 2 (q119 c4) ∷
   rw 3 (q133 c4) ∷
   rw 4 (q134 c4) ∷
   rw⁻ 3 (q121 c4) ∷
   rw 9 (q122 c4) ∷
   rw 8 (q123 c4) ∷
   rw 7 (q124 c4) ∷
   rw 6 (q125 c4) ∷
   rw 5 (q124 c4) ∷
   rw 4 (q126 c4) ∷
   rw 3 (q127 c4) ∷
   rw 4 (q121 c4) ∷
   rw⁻ 0 (q118 c4) ∷
   rw⁻ 0 (q117 c4) ∷
   rw 2 (q109 c4) ∷
   rw⁻ 6 (q110 c4) ∷
   rw 5 (q111 c4) ∷
   rw⁻ 4 (q112 c4) ∷
   rw 3 (q111 c4) ∷
   rw⁻ 2 (q113 c4) ∷
   rw⁻ 3 (q109 c4) ∷
   rw 3 (q135 c4) ∷
   rw 4 (q109 c4) ∷
   rw⁻ 8 (q110 c4) ∷
   rw 7 (q111 c4) ∷
   rw⁻ 6 (q112 c4) ∷
   rw 5 (q111 c4) ∷
   rw⁻ 4 (q113 c4) ∷
   rw⁻ 5 (q109 c4) ∷
   rw 5 (q136 c4) ∷
   rw⁻ 1 (q97 c4) ∷
   rw 0 (q137 c4) ∷
   rw 1 (q138 c4) ∷
   rw 0 (q139 c4) ∷
   rw 0 (q140 c4) ∷
   rw 1 (q141 c4) ∷ []) Eq.refl

private
  q142 : Ws → Eqn
  q142 c4 = sE 192 (lem-box-tQ-at0314213042 c4)
  q143 : Ws → Eqn
  q143 c4 = wpE 1241 c4
  q144 : Ws → Eqn
  q144 c4 = wpE 1242 c4
  q145 : Ws → Eqn
  q145 c4 = wpE 1243 c4
  q146 : Ws → Eqn
  q146 c4 = wlE 1396 (lit c4)
  q147 : Ws → Eqn
  q147 c4 = wpE 822 c4
  q148 : Ws → Eqn
  q148 c4 = wlE 829 (lit c4)
  q149 : Ws → Eqn
  q149 c4 = eqn (CX32 ∷ Toff014 ∷ []) (Toff014 ∷ CX32 ∷ []) (lem-comm-CX32-TOFF014 (lit c4))
  q150 : Ws → Eqn
  q150 c4 = wpE 1244 c4
  q151 : Ws → Eqn
  q151 c4 = wlE 527 (lit c4)
  q152 : Ws → Eqn
  q152 c4 = wpE 1245 c4
  q153 : Ws → Eqn
  q153 c4 = wlE 334 (lit c4)
  q154 : Ws → Eqn
  q154 c4 = eqn (CX41 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4))
  q155 : Ws → Eqn
  q155 c4 = wlE 620 (lit c4)
  q156 : Ws → Eqn
  q156 c4 = wpE 1246 c4
  q157 : Ws → Eqn
  q157 c4 = wlE 204 (lit c4)
  q158 : Ws → Eqn
  q158 c4 = sE 270 (lem-box-tQ-at142142 c4)
  q159 : Ws → Eqn
  q159 c4 = sE 1522 (lem-box-perm-1324-at142142 c4)
  q160 : Ws → Eqn
  q160 c4 = sE 733 (lem-box-cP-at14233142 c4)
  q161 : Ws → Eqn
  q161 c4 = wpE 702 c4
  q162 : Ws → Eqn
  q162 c4 = wpE 122 c4
  q163 : Ws → Eqn
  q163 c4 = wlE 1397 (lit c4)
  q164 : Ws → Eqn
  q164 c4 = eqn (Toff012 ∷ K3⁻ ∷ []) (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI))
  q165 : Ws → Eqn
  q165 c4 = wlE 1284 (lit c4)
  q166 : Ws → Eqn
  q166 c4 = eqn (Toff012 ∷ CX34 ∷ []) (CX34 ∷ Toff012 ∷ []) (c₃ (Toff) (CX₀₁))
  q167 : Ws → Eqn
  q167 c4 = wpE 1247 c4
  q168 : Ws → Eqn
  q168 c4 = wpE 102 c4
  q169 : Ws → Eqn
  q169 c4 = eqn (Toff012 ∷ K3 ∷ []) (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K))
  q170 : Ws → Eqn
  q170 c4 = wpE 108 c4
  q171 : Ws → Eqn
  q171 c4 = wpE 357 c4
  q172 : Ws → Eqn
  q172 c4 = eqn (CS12⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4))
  q173 : Ws → Eqn
  q173 c4 = eqn (CS12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4))
  q174 : Ws → Eqn
  q174 c4 = wpE 124 c4
  q175 : Ws → Eqn
  q175 c4 = wpE 1248 c4
  q176 : Ws → Eqn
  q176 c4 = wpE 300 c4
  q177 : Ws → Eqn
  q177 c4 = wlE 974 (lit c4)
  q178 : Ws → Eqn
  q178 c4 = wlE 263 (lit c4)
  q179 : Ws → Eqn
  q179 c4 = sE 1525 (lem-box-perm-3124-at142142 c4)
  q180 : Ws → Eqn
  q180 c4 = sE 1270 (lem-box-perm-3124-at0314213042 c4)
  q181 : Ws → Eqn
  q181 c4 = sE 1530 (lem-box-box-1-at13243142 c4)
  q182 : Ws → Eqn
  q182 c4 = sE 1268 (lem-box-perm-2314-at0310243142 c4)
  q183 : Ws → Eqn
  q183 c4 = sE 1519 (lem-box-perm-2314-at13243142 c4)

-- Tu-box @0314213042: 83 steps
lem-Tu-box-at0314213042 : Ws → ⟪ (Toff034 ∷ Bx3-4102 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ Bx0-4132 ∷ []) ⟫ʷ
lem-Tu-box-at0314213042 c4 = derive (Toff034 ∷ Bx3-4102 ∷ Toff034 ∷ []) (Bx3-4102 ∷ Bx0-4132 ∷ [])
  (rw 1 (q142 c4) ∷
   rw 0 (q143 c4) ∷
   rw⁻ 2 (q144 c4) ∷
   rw 4 (q143 c4) ∷
   rw⁻ 6 (q145 c4) ∷
   rw 3 (q146 c4) ∷
   rw 5 (q147 c4) ∷
   rw 4 (q148 c4) ∷
   rw 8 (q75 c4) ∷
   rw 7 (q149 c4) ∷
   rw 6 (q150 c4) ∷
   rw 5 (q149 c4) ∷
   rw 4 (q78 c4) ∷
   rw⁻ 5 (q148 c4) ∷
   rw⁻ 5 (q151 c4) ∷
   rw⁻ 6 (q152 c4) ∷
   rw 5 (q153 c4) ∷
   rw⁻ 9 (q83 c4) ∷
   rw 8 (q154 c4) ∷
   rw⁻ 7 (q155 c4) ∷
   rw 6 (q154 c4) ∷
   rw⁻ 5 (q86 c4) ∷
   rw⁻ 6 (q153 c4) ∷
   rw⁻ 3 (q156 c4) ∷
   rw⁻ 4 (q157 c4) ∷
   rw⁻ 1 (q158 c4) ∷
   rw 1 (q159 c4) ∷
   rw 1 (q160 c4) ∷
   rw⁻ 0 (q161 c4) ∷
   rw 2 (q162 c4) ∷
   rw⁻ 1 (q163 c4) ∷
   rw⁻ 7 (q164 c4) ∷
   rw 6 (q165 c4) ∷
   rw⁻ 5 (q166 c4) ∷
   rw 4 (q167 c4) ∷
   rw⁻ 3 (q166 c4) ∷
   rw 2 (q168 c4) ∷
   rw⁻ 1 (q169 c4) ∷
   rw 2 (q163 c4) ∷
   rw 4 (q153 c4) ∷
   rw⁻ 8 (q170 c4) ∷
   rw⁻ 7 (q171 c4) ∷
   rw 6 (q172 c4) ∷
   rw⁻ 5 (q171 c4) ∷
   rw 4 (q173 c4) ∷
   rw⁻ 5 (q153 c4) ∷
   rw 3 (q174 c4) ∷
   rw⁻ 2 (q161 c4) ∷
   rw 3 (q175 c4) ∷
   rw 4 (q176 c4) ∷
   rw⁻ 3 (q163 c4) ∷
   rw⁻ 9 (q164 c4) ∷
   rw 8 (q165 c4) ∷
   rw⁻ 7 (q166 c4) ∷
   rw 6 (q167 c4) ∷
   rw⁻ 5 (q166 c4) ∷
   rw 4 (q168 c4) ∷
   rw⁻ 3 (q169 c4) ∷
   rw 4 (q163 c4) ∷
   rw⁻ 0 (q160 c4) ∷
   rw⁻ 0 (q159 c4) ∷
   rw 2 (q153 c4) ∷
   rw⁻ 6 (q83 c4) ∷
   rw 5 (q154 c4) ∷
   rw⁻ 4 (q155 c4) ∷
   rw 3 (q154 c4) ∷
   rw⁻ 2 (q86 c4) ∷
   rw⁻ 3 (q153 c4) ∷
   rw 3 (q177 c4) ∷
   rw 4 (q153 c4) ∷
   rw⁻ 8 (q83 c4) ∷
   rw 7 (q154 c4) ∷
   rw⁻ 6 (q155 c4) ∷
   rw 5 (q154 c4) ∷
   rw⁻ 4 (q86 c4) ∷
   rw⁻ 5 (q153 c4) ∷
   rw 5 (q178 c4) ∷
   rw⁻ 1 (q142 c4) ∷
   rw 0 (q179 c4) ∷
   rw 1 (q180 c4) ∷
   rw 0 (q181 c4) ∷
   rw 0 (q182 c4) ∷
   rw 1 (q183 c4) ∷ []) Eq.refl

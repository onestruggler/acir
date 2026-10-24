{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD038 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D038 (Sᴰ : SD038) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-CS13-CCZ024 : Ws → St 958
  lem-comm-CS13-CCZ024 = pickᴰ 0 Sᴰ
  lem-comm-CS23-CCZ014 : Ws → St 703
  lem-comm-CS23-CCZ014 = pickᴰ 1 Sᴰ
  lem-comm-CS24-TOFF013 : Ws → St 195
  lem-comm-CS24-TOFF013 = pickᴰ 2 Sᴰ
  lem-comm-CSd13-CCZ024 : Ws → St 960
  lem-comm-CSd13-CCZ024 = pickᴰ 3 Sᴰ
  lem-comm-CSd23-CCZ014 : Ws → St 704
  lem-comm-CSd23-CCZ014 = pickᴰ 4 Sᴰ
  lem-comm-CSd24-TOFF013 : Ws → St 205
  lem-comm-CSd24-TOFF013 = pickᴰ 5 Sᴰ
  lem-comm-CX13-CCZ024 : Ws → St 3
  lem-comm-CX13-CCZ024 = pickᴰ 6 Sᴰ
  lem-comm-CX14-CCZ023 : Ws → St 4
  lem-comm-CX14-CCZ023 = pickᴰ 7 Sᴰ
  lem-comm-CX14-TOFF023 : Ws → St 1056
  lem-comm-CX14-TOFF023 = pickᴰ 8 Sᴰ
  lem-comm-CX23-CCZ014 : Ws → St 6
  lem-comm-CX23-CCZ014 = pickᴰ 9 Sᴰ
  lem-comm-CZ13-CCZ024 : Ws → St 67
  lem-comm-CZ13-CCZ024 = pickᴰ 10 Sᴰ
  lem-comm-CCZ024-CS13 : Ws → St 1382
  lem-comm-CCZ024-CS13 = pickᴰ 11 Sᴰ
  lem-comm-CCZ024-CSd13 : Ws → St 1383
  lem-comm-CCZ024-CSd13 = pickᴰ 12 Sᴰ
  lem-comm-CCZ024-CX13 : Ws → St 1024
  lem-comm-CCZ024-CX13 = pickᴰ 13 Sᴰ
  lem-comm-CCZ024-CX31 : Ws → St 1058
  lem-comm-CCZ024-CX31 = pickᴰ 14 Sᴰ
  lem-comm-CCZ124-CS03 : Ws → St 1504
  lem-comm-CCZ124-CS03 = pickᴰ 15 Sᴰ
  lem-comm-CX23-TOFF014 : Ws → St 1505
  lem-comm-CX23-TOFF014 = pickᴰ 16 Sᴰ
  lem-comm-TOFF014-CX23 : Ws → St 1384
  lem-comm-TOFF014-CX23 = pickᴰ 17 Sᴰ
  lem-comm-TOFF213-CX04 : Ws → St 1028
  lem-comm-TOFF213-CX04 = pickᴰ 18 Sᴰ
  lem-comm-TOFF023-CX14 : Ws → St 1060
  lem-comm-TOFF023-CX14 = pickᴰ 19 Sᴰ
  lem-nf-order-CSat0 : Ws → St 1506
  lem-nf-order-CSat0 = pickᴰ 20 Sᴰ
  lem-nf-order-CSat1 : Ws → St 1507
  lem-nf-order-CSat1 = pickᴰ 21 Sᴰ
  lem-nf-order-CSat2 : Ws → St 1508
  lem-nf-order-CSat2 = pickᴰ 22 Sᴰ
  lem-box-cP-at0210243143 : Ws → St 994
  lem-box-cP-at0210243143 = pickᴰ 23 Sᴰ
  lem-box-cP-at12233441 : Ws → St 1065
  lem-box-cP-at12233441 = pickᴰ 24 Sᴰ
  lem-box-cP-at122441 : Ws → St 1002
  lem-box-cP-at122441 = pickᴰ 25 Sᴰ
  lem-box-cP-at243243 : Ws → St 1008
  lem-box-cP-at243243 = pickᴰ 26 Sᴰ
  lem-box-perm-1324-at122441 : Ws → St 1255
  lem-box-perm-1324-at122441 = pickᴰ 27 Sᴰ
  lem-box2 : Ws → St 1509
  lem-box2 = pickᴰ 28 Sᴰ
  lem-CSdu-box-3-at0210243143 : Ws → St 1510
  lem-CSdu-box-3-at0210243143 = pickᴰ 29 Sᴰ
  lem-CSdu-box-3-at122441 : Ws → St 1511
  lem-CSdu-box-3-at122441 = pickᴰ 30 Sᴰ
  lem-CSu-box-3-at0210243143 : Ws → St 1512
  lem-CSu-box-3-at0210243143 = pickᴰ 31 Sᴰ
  lem-CSu-box-3-at122441 : Ws → St 1513
  lem-CSu-box-3-at122441 = pickᴰ 32 Sᴰ
  lem-box-perm-1432-at122441 : Ws → St 1514
  lem-box-perm-1432-at122441 = pickᴰ 33 Sᴰ
  lem-CKu-box-2-at0210243143 : Ws → St 1488
  lem-CKu-box-2-at0210243143 = pickᴰ 34 Sᴰ
  lem-CKu-box-2-at122441 : Ws → St 1489
  lem-CKu-box-2-at122441 = pickᴰ 35 Sᴰ
  lem-CKu-box-2-at243243 : Ws → St 1490
  lem-CKu-box-2-at243243 = pickᴰ 36 Sᴰ
  lem-box-box-1-at021021 : Ws → St 1515
  lem-box-box-1-at021021 = pickᴰ 37 Sᴰ
  lem-box-perm-1342-at0210243143 : Ws → St 1516
  lem-box-perm-1342-at0210243143 = pickᴰ 38 Sᴰ
  lem-box-perm-1423-at021021 : Ws → St 1517
  lem-box-perm-1423-at021021 = pickᴰ 39 Sᴰ
  lem-box-perm-1432-at1221 : Ws → St 1518
  lem-box-perm-1432-at1221 = pickᴰ 40 Sᴰ
  lem-box-perm-3241-at243243 : Ws → St 1519
  lem-box-perm-3241-at243243 = pickᴰ 41 Sᴰ
  lem-box-perm-4213-at122441 : Ws → St 1520
  lem-box-perm-4213-at122441 = pickᴰ 42 Sᴰ
  lem-CKc-box : Ws → St 1521
  lem-CKc-box = pickᴰ 43 Sᴰ
  lem-CKdc-box : Ws → St 1522
  lem-CKdc-box = pickᴰ 44 Sᴰ
  lem-S2-SBOX⟨0·1·42·3⟩ : Ws → St 1523
  lem-S2-SBOX⟨0·1·42·3⟩ = pickᴰ 45 Sᴰ
  lem-S2-SBOX⟨0·2·43·1⟩ : Ws → St 1524
  lem-S2-SBOX⟨0·2·43·1⟩ = pickᴰ 46 Sᴰ
  lem-S2-SBOX⟨2·0·41·3⟩ : Ws → St 1525
  lem-S2-SBOX⟨2·0·41·3⟩ = pickᴰ 47 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1002 (lem-box-cP-at122441 c4)
  q2 : Ws → Eqn
  q2 c4 = wpE 20 c4
  q3 : Ws → Eqn
  q3 c4 = wlE 232 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (ℓ "云並") (ℓ "並云") (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))
  q5 : Ws → Eqn
  q5 c4 = wlE 242 (lit c4)
  q6 : Ws → Eqn
  q6 c4 = wpE 81 c4
  q7 : Ws → Eqn
  q7 c4 = sE 3 (lem-comm-CX13-CCZ024 c4)
  q8 : Ws → Eqn
  q8 c4 = wpE 91 c4
  q9 : Ws → Eqn
  q9 c4 = wpE 92 c4
  q10 : Ws → Eqn
  q10 c4 = wpE 23 c4
  q11 : Ws → Eqn
  q11 c4 = wlE 185 (lit c4)
  q12 : Ws → Eqn
  q12 c4 = wlE 234 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1511 (lem-CSdu-box-3-at122441 c4)
  q14 : Ws → Eqn
  q14 c4 = wlE 190 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = wpE 33 c4
  q16 : Ws → Eqn
  q16 c4 = wpE 34 c4
  q17 : Ws → Eqn
  q17 c4 = wpE 35 c4
  q18 : Ws → Eqn
  q18 c4 = wpE 36 c4
  q19 : Ws → Eqn
  q19 c4 = wpE 37 c4
  q20 : Ws → Eqn
  q20 c4 = wpE 783 c4
  q21 : Ws → Eqn
  q21 c4 = wpE 784 c4
  q22 : Ws → Eqn
  q22 c4 = wlE 256 (lit c4)
  q23 : Ws → Eqn
  q23 c4 = wpE 785 c4
  q24 : Ws → Eqn
  q24 c4 = wlE 872 (lit c4)
  q25 : Ws → Eqn
  q25 c4 = sE 205 (lem-comm-CSd24-TOFF013 c4)
  q26 : Ws → Eqn
  q26 c4 = sE 195 (lem-comm-CS24-TOFF013 c4)
  q27 : Ws → Eqn
  q27 c4 = wpE 786 c4
  q28 : Ws → Eqn
  q28 c4 = wpE 787 c4
  q29 : Ws → Eqn
  q29 c4 = sE 1513 (lem-CSu-box-3-at122441 c4)
  q30 : Ws → Eqn
  q30 c4 = sE 1516 (lem-box-perm-1342-at0210243143 c4)
  q31 : Ws → Eqn
  q31 c4 = sE 1514 (lem-box-perm-1432-at122441 c4)
  q32 : Ws → Eqn
  q32 c4 = sE 1515 (lem-box-box-1-at021021 c4)
  q33 : Ws → Eqn
  q33 c4 = sE 1518 (lem-box-perm-1432-at1221 c4)
  q34 : Ws → Eqn
  q34 c4 = sE 1517 (lem-box-perm-1423-at021021 c4)
  q35 : Ws → Eqn
  q35 c4 = sE 994 (lem-box-cP-at0210243143 c4)
  q36 : Ws → Eqn
  q36 c4 = wlE 965 (lit c4)
  q37 : Ws → Eqn
  q37 c4 = sE 67 (lem-comm-CZ13-CCZ024 c4)
  q38 : Ws → Eqn
  q38 c4 = wlE 971 (lit c4)
  q39 : Ws → Eqn
  q39 c4 = wlE 972 (lit c4)
  q40 : Ws → Eqn
  q40 c4 = sE 1504 (lem-comm-CCZ124-CS03 c4)
  q41 : Ws → Eqn
  q41 c4 = wlE 490 (lit c4)
  q42 : Ws → Eqn
  q42 c4 = wlE 973 (lit c4)
  q43 : Ws → Eqn
  q43 c4 = wlE 495 (lit c4)
  q44 : Ws → Eqn
  q44 c4 = wlE 892 (lit c4)
  q45 : Ws → Eqn
  q45 c4 = wlE 181 (lit c4)
  q46 : Ws → Eqn
  q46 c4 = wlE 974 (lit c4)
  q47 : Ws → Eqn
  q47 c4 = wlE 263 (lit c4)
  q48 : Ws → Eqn
  q48 c4 = wlE 975 (lit c4)
  q49 : Ws → Eqn
  q49 c4 = wpE 788 c4
  q50 : Ws → Eqn
  q50 c4 = wlE 976 (lit c4)
  q51 : Ws → Eqn
  q51 c4 = wlE 977 (lit c4)
  q52 : Ws → Eqn
  q52 c4 = sE 1058 (lem-comm-CCZ024-CX31 c4)
  q53 : Ws → Eqn
  q53 c4 = wpE 789 c4
  q54 : Ws → Eqn
  q54 c4 = wlE 241 (lit c4)
  q55 : Ws → Eqn
  q55 c4 = wpE 89 c4
  q56 : Ws → Eqn
  q56 c4 = sE 1024 (lem-comm-CCZ024-CX13 c4)
  q57 : Ws → Eqn
  q57 c4 = wpE 88 c4
  q58 : Ws → Eqn
  q58 c4 = wpE 790 c4
  q59 : Ws → Eqn
  q59 c4 = wlE 809 (lit c4)
  q60 : Ws → Eqn
  q60 c4 = wpE 352 c4
  q61 : Ws → Eqn
  q61 c4 = wlE 808 (lit c4)
  q62 : Ws → Eqn
  q62 c4 = sE 1028 (lem-comm-TOFF213-CX04 c4)
  q63 : Ws → Eqn
  q63 c4 = wlE 807 (lit c4)
  q64 : Ws → Eqn
  q64 c4 = wlE 196 (lit c4)
  q65 : Ws → Eqn
  q65 c4 = wlE 942 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = wlE 978 (lit c4)
  q67 : Ws → Eqn
  q67 c4 = wlE 979 (lit c4)
  q68 : Ws → Eqn
  q68 c4 = wpE 791 c4
  q69 : Ws → Eqn
  q69 c4 = wlE 235 (lit c4)
  q70 : Ws → Eqn
  q70 c4 = wlE 980 (lit c4)
  q71 : Ws → Eqn
  q71 c4 = wlE 981 (lit c4)
  q72 : Ws → Eqn
  q72 c4 = wlE 982 (lit c4)
  q73 : Ws → Eqn
  q73 c4 = wlE 983 (lit c4)
  q74 : Ws → Eqn
  q74 c4 = sE 1512 (lem-CSu-box-3-at0210243143 c4)
  q75 : Ws → Eqn
  q75 c4 = wlE 984 (lit c4)
  q76 : Ws → Eqn
  q76 c4 = wlE 469 (lit c4)
  q77 : Ws → Eqn
  q77 c4 = wlE 985 (lit c4)
  q78 : Ws → Eqn
  q78 c4 = wlE 986 (lit c4)
  q79 : Ws → Eqn
  q79 c4 = sE 1510 (lem-CSdu-box-3-at0210243143 c4)

-- F4-CS0-CS2: 284 steps
lem-F4-CS0-CS2 : Ws → ⟪ (ℓ "並俄並侬") ⟫ʷ ≈ ⟪ (ℓ "侬並俄並") ⟫ʷ
lem-F4-CS0-CS2 c4 = derive (ℓ "並俄並侬") (ℓ "侬並俄並")
  (re 3 1 (ℓ "仞亭侪亭侫") ∷
   re 5 1 (ℓ "乇") ∷
   re 7 1 (ℓ "么") ∷
   rw 3 (q1 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw 6 (q5 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 5 (q10 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 5 (q11 c4) ∷
   rw 6 (q12 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   re 1 1 (ℓ "伱亮係亮促") ∷
   re 5 1 (ℓ "丷") ∷
   rw 5 (q13 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   rw⁻ 9 (q16 c4) ∷
   rw 8 (q7 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 5 (q18 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw 5 (q14 c4) ∷
   rw⁻ 5 (q20 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw⁻ 13 (q15 c4) ∷
   rw⁻ 12 (q16 c4) ∷
   rw 11 (q7 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 8 (q18 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw 8 (q14 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw⁻ 9 (q20 c4) ∷
   rw 8 (q22 c4) ∷
   rw 12 (q23 c4) ∷
   rw 11 (q24 c4) ∷
   rw 10 (q25 c4) ∷
   rw 9 (q24 c4) ∷
   rw 8 (q26 c4) ∷
   rw⁻ 9 (q22 c4) ∷
   rw⁻ 7 (q27 c4) ∷
   rw⁻ 8 (q28 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 3 1 (ℓ "丶") ∷
   rw 3 (q29 c4) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 8 (q15 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 5 (q17 c4) ∷
   rw 4 (q7 c4) ∷
   rw⁻ 3 (q18 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   rw 3 (q14 c4) ∷
   rw⁻ 3 (q20 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   rw⁻ 11 (q15 c4) ∷
   rw⁻ 10 (q16 c4) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 8 (q17 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q18 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 4 (q21 c4) ∷
   rw⁻ 7 (q20 c4) ∷
   rw 6 (q22 c4) ∷
   rw 10 (q23 c4) ∷
   rw 9 (q24 c4) ∷
   rw 8 (q25 c4) ∷
   rw 7 (q24 c4) ∷
   rw 6 (q26 c4) ∷
   rw⁻ 7 (q22 c4) ∷
   rw⁻ 5 (q27 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q30 c4) ∷
   rw 2 (q31 c4) ∷
   rw 1 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw 2 (q34 c4) ∷
   rw 1 (q1 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 1 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q8 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q12 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 3 (q35 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 3 (q36 c4) ∷
   rw 5 (q5 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   rw 8 (q7 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 4 (q37 c4) ∷
   rw 5 (q38 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   rw 3 (q39 c4) ∷
   rw 6 (q40 c4) ∷
   rw 5 (q41 c4) ∷
   rw 6 (q42 c4) ∷
   rw 8 (q43 c4) ∷
   rw 9 (q44 c4) ∷
   rw 10 (q45 c4) ∷
   rw 3 (q46 c4) ∷
   rw 4 (q40 c4) ∷
   rw 5 (q47 c4) ∷
   re 4 1 (ℓ "係") ∷
   re 6 1 (ℓ "促") ∷
   re 2 5 (ℓ "俄") ∷
   rw⁻ 3 (q48 c4) ∷
   re 2 1 (ℓ "伱亮係亮促") ∷
   re 4 1 (ℓ "丶") ∷
   re 6 1 (ℓ "丷") ∷
   rw⁻ 3 (q49 c4) ∷
   rw 2 (q35 c4) ∷
   rw⁻ 5 (q50 c4) ∷
   rw⁻ 7 (q51 c4) ∷
   rw 4 (q52 c4) ∷
   rw 5 (q53 c4) ∷
   rw⁻ 8 (q54 c4) ∷
   rw 7 (q55 c4) ∷
   rw 8 (q18 c4) ∷
   rw 9 (q56 c4) ∷
   rw 10 (q17 c4) ∷
   rw 11 (q56 c4) ∷
   rw 12 (q16 c4) ∷
   rw 13 (q57 c4) ∷
   rw 7 (q54 c4) ∷
   rw 8 (q58 c4) ∷
   rw⁻ 3 (q50 c4) ∷
   rw⁻ 5 (q59 c4) ∷
   rw 7 (q60 c4) ∷
   rw⁻ 6 (q61 c4) ∷
   rw 7 (q62 c4) ∷
   rw⁻ 8 (q63 c4) ∷
   rw 9 (q62 c4) ∷
   rw⁻ 10 (q64 c4) ∷
   rw⁻ 6 (q60 c4) ∷
   rw⁻ 7 (q51 c4) ∷
   rw 9 (q65 c4) ∷
   rw 11 (q60 c4) ∷
   rw⁻ 10 (q61 c4) ∷
   rw 11 (q62 c4) ∷
   rw⁻ 12 (q63 c4) ∷
   rw 13 (q62 c4) ∷
   rw⁻ 14 (q64 c4) ∷
   rw⁻ 10 (q60 c4) ∷
   rw 3 (q66 c4) ∷
   rw 5 (q67 c4) ∷
   rw 3 (q68 c4) ∷
   rw 2 (q52 c4) ∷
   rw⁻ 4 (q54 c4) ∷
   rw 3 (q55 c4) ∷
   rw 4 (q18 c4) ∷
   rw 5 (q56 c4) ∷
   rw 6 (q17 c4) ∷
   rw 7 (q56 c4) ∷
   rw 8 (q16 c4) ∷
   rw 9 (q57 c4) ∷
   rw 3 (q54 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   re 6 1 (ℓ "係") ∷
   re 8 1 (ℓ "促") ∷
   re 4 5 (ℓ "俄") ∷
   rw⁻ 1 (q69 c4) ∷
   rw⁻ 4 (q70 c4) ∷
   re 3 1 (ℓ "伱亮係亮促") ∷
   re 5 1 (ℓ "丶") ∷
   re 7 1 (ℓ "丷") ∷
   rw 7 (q71 c4) ∷
   rw⁻ 6 (q72 c4) ∷
   rw 5 (q73 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   rw⁻ 3 (q74 c4) ∷
   re 6 1 (ℓ "係") ∷
   re 8 1 (ℓ "促") ∷
   re 4 5 (ℓ "俄") ∷
   rw⁻ 2 (q70 c4) ∷
   rw⁻ 5 (q48 c4) ∷
   re 4 1 (ℓ "伱亮係亮促") ∷
   re 6 1 (ℓ "丶") ∷
   re 8 1 (ℓ "丷") ∷
   rw⁻ 5 (q49 c4) ∷
   rw 4 (q35 c4) ∷
   rw⁻ 7 (q50 c4) ∷
   rw⁻ 9 (q51 c4) ∷
   rw 6 (q52 c4) ∷
   rw 7 (q53 c4) ∷
   rw⁻ 10 (q54 c4) ∷
   rw 9 (q55 c4) ∷
   rw 10 (q18 c4) ∷
   rw 11 (q56 c4) ∷
   rw 12 (q17 c4) ∷
   rw 13 (q56 c4) ∷
   rw 14 (q16 c4) ∷
   rw 15 (q57 c4) ∷
   rw 9 (q54 c4) ∷
   rw 10 (q58 c4) ∷
   rw⁻ 5 (q50 c4) ∷
   rw⁻ 7 (q59 c4) ∷
   rw 9 (q60 c4) ∷
   rw⁻ 8 (q61 c4) ∷
   rw 9 (q62 c4) ∷
   rw⁻ 10 (q63 c4) ∷
   rw 11 (q62 c4) ∷
   rw⁻ 12 (q64 c4) ∷
   rw⁻ 8 (q60 c4) ∷
   rw⁻ 9 (q51 c4) ∷
   rw 11 (q65 c4) ∷
   rw 13 (q60 c4) ∷
   rw⁻ 12 (q61 c4) ∷
   rw 13 (q62 c4) ∷
   rw⁻ 14 (q63 c4) ∷
   rw 15 (q62 c4) ∷
   rw⁻ 16 (q64 c4) ∷
   rw⁻ 12 (q60 c4) ∷
   rw 5 (q66 c4) ∷
   rw 7 (q67 c4) ∷
   rw 5 (q68 c4) ∷
   rw 4 (q52 c4) ∷
   rw⁻ 6 (q54 c4) ∷
   rw 5 (q55 c4) ∷
   rw 6 (q18 c4) ∷
   rw 7 (q56 c4) ∷
   rw 8 (q17 c4) ∷
   rw 9 (q56 c4) ∷
   rw 10 (q16 c4) ∷
   rw 11 (q57 c4) ∷
   rw 5 (q54 c4) ∷
   rw⁻ 6 (q35 c4) ∷
   re 8 1 (ℓ "係") ∷
   re 10 1 (ℓ "促") ∷
   re 6 5 (ℓ "俄") ∷
   rw⁻ 3 (q69 c4) ∷
   rw⁻ 6 (q75 c4) ∷
   re 5 1 (ℓ "伱亮係亮促") ∷
   re 7 1 (ℓ "丶") ∷
   re 9 1 (ℓ "丷") ∷
   rw 9 (q76 c4) ∷
   rw⁻ 8 (q77 c4) ∷
   rw 7 (q78 c4) ∷
   rw⁻ 6 (q77 c4) ∷
   rw⁻ 5 (q79 c4) ∷
   re 8 1 (ℓ "係") ∷
   re 10 1 (ℓ "促") ∷
   re 6 5 (ℓ "俄") ∷
   rw⁻ 4 (q75 c4) ∷
   re 2 1 (ℓ "侪") ∷
   re 4 1 (ℓ "侫") ∷
   re 0 5 (ℓ "侬") ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = sE 960 (lem-comm-CSd13-CCZ024 c4)
  q81 : Ws → Eqn
  q81 c4 = wlE 907 (lit c4)
  q82 : Ws → Eqn
  q82 c4 = sE 1255 (lem-box-perm-1324-at122441 c4)
  q83 : Ws → Eqn
  q83 c4 = sE 1065 (lem-box-cP-at12233441 c4)
  q84 : Ws → Eqn
  q84 c4 = wpE 814 c4
  q85 : Ws → Eqn
  q85 c4 = wpE 815 c4
  q86 : Ws → Eqn
  q86 c4 = wlE 217 (lit c4)
  q87 : Ws → Eqn
  q87 c4 = wpE 816 c4
  q88 : Ws → Eqn
  q88 c4 = wpE 817 c4
  q89 : Ws → Eqn
  q89 c4 = sE 1505 (lem-comm-CX23-TOFF014 c4)
  q90 : Ws → Eqn
  q90 c4 = wpE 818 c4
  q91 : Ws → Eqn
  q91 c4 = wpE 546 c4
  q92 : Ws → Eqn
  q92 c4 = wpE 819 c4
  q93 : Ws → Eqn
  q93 c4 = wlE 220 (lit c4)
  q94 : Ws → Eqn
  q94 c4 = wlE 621 (lit c4)
  q95 : Ws → Eqn
  q95 c4 = sE 4 (lem-comm-CX14-CCZ023 c4)
  q96 : Ws → Eqn
  q96 c4 = wpE 820 c4
  q97 : Ws → Eqn
  q97 c4 = wpE 513 c4
  q98 : Ws → Eqn
  q98 c4 = wpE 669 c4
  q99 : Ws → Eqn
  q99 c4 = wpE 821 c4
  q100 : Ws → Eqn
  q100 c4 = wpE 822 c4
  q101 : Ws → Eqn
  q101 c4 = sE 958 (lem-comm-CS13-CCZ024 c4)
  q102 : Ws → Eqn
  q102 c4 = wlE 910 (lit c4)
  q103 : Ws → Eqn
  q103 c4 = sE 1519 (lem-box-perm-3241-at243243 c4)
  q104 : Ws → Eqn
  q104 c4 = sE 1520 (lem-box-perm-4213-at122441 c4)
  q105 : Ws → Eqn
  q105 c4 = sE 1008 (lem-box-cP-at243243 c4)
  q106 : Ws → Eqn
  q106 c4 = wlE 207 (lit c4)
  q107 : Ws → Eqn
  q107 c4 = wpE 53 c4
  q108 : Ws → Eqn
  q108 c4 = wpE 54 c4
  q109 : Ws → Eqn
  q109 c4 = sE 704 (lem-comm-CSd23-CCZ014 c4)
  q110 : Ws → Eqn
  q110 c4 = sE 703 (lem-comm-CS23-CCZ014 c4)
  q111 : Ws → Eqn
  q111 c4 = wlE 209 (lit c4)
  q112 : Ws → Eqn
  q112 c4 = wlE 1010 (lit c4)
  q113 : Ws → Eqn
  q113 c4 = wlE 1011 (lit c4)
  q114 : Ws → Eqn
  q114 c4 = wlE 1012 (lit c4)
  q115 : Ws → Eqn
  q115 c4 = wlE 832 (lit c4)
  q116 : Ws → Eqn
  q116 c4 = wlE 1013 (lit c4)
  q117 : Ws → Eqn
  q117 c4 = wlE 735 (lit c4)
  q118 : Ws → Eqn
  q118 c4 = wpE 725 c4
  q119 : Ws → Eqn
  q119 c4 = sE 1060 (lem-comm-TOFF023-CX14 c4)
  q120 : Ws → Eqn
  q120 c4 = wpE 823 c4
  q121 : Ws → Eqn
  q121 c4 = wlE 222 (lit c4)
  q122 : Ws → Eqn
  q122 c4 = wlE 1014 (lit c4)
  q123 : Ws → Eqn
  q123 c4 = wpE 824 c4
  q124 : Ws → Eqn
  q124 c4 = wlE 1015 (lit c4)
  q125 : Ws → Eqn
  q125 c4 = wlE 221 (lit c4)
  q126 : Ws → Eqn
  q126 c4 = wpE 67 c4
  q127 : Ws → Eqn
  q127 c4 = wlE 1016 (lit c4)
  q128 : Ws → Eqn
  q128 c4 = wlE 1017 (lit c4)
  q129 : Ws → Eqn
  q129 c4 = wpE 265 c4

-- F4-CS1-CS2: 248 steps
lem-F4-CS1-CS2 : Ws → ⟪ (ℓ "並侧並侬") ⟫ʷ ≈ ⟪ (ℓ "侬並侧並") ⟫ʷ
lem-F4-CS1-CS2 c4 = derive (ℓ "並侧並侬") (ℓ "侬並侧並")
  (re 3 1 (ℓ "仞亭侪亭侫") ∷
   re 5 1 (ℓ "乇") ∷
   re 7 1 (ℓ "么") ∷
   rw 3 (q1 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw 6 (q5 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 5 (q10 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 5 (q11 c4) ∷
   rw 6 (q12 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   re 1 1 (ℓ "仄亲侥亲侦") ∷
   re 5 1 (ℓ "乏") ∷
   rw 6 (q1 c4) ∷
   rw 5 (q80 c4) ∷
   rw 6 (q81 c4) ∷
   rw 7 (q80 c4) ∷
   rw 8 (q81 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw 5 (q82 c4) ∷
   rw 5 (q83 c4) ∷
   rw⁻ 4 (q84 c4) ∷
   rw 6 (q85 c4) ∷
   rw⁻ 5 (q86 c4) ∷
   rw 11 (q87 c4) ∷
   rw 10 (q88 c4) ∷
   rw 9 (q89 c4) ∷
   rw 8 (q90 c4) ∷
   rw 7 (q89 c4) ∷
   rw 6 (q91 c4) ∷
   rw 5 (q92 c4) ∷
   rw 6 (q86 c4) ∷
   rw 8 (q93 c4) ∷
   rw⁻ 12 (q94 c4) ∷
   rw 11 (q95 c4) ∷
   rw⁻ 10 (q96 c4) ∷
   rw 9 (q95 c4) ∷
   rw⁻ 8 (q97 c4) ∷
   rw⁻ 9 (q93 c4) ∷
   rw⁻ 7 (q98 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   rw 7 (q99 c4) ∷
   rw 8 (q100 c4) ∷
   rw⁻ 7 (q86 c4) ∷
   rw 13 (q87 c4) ∷
   rw 12 (q88 c4) ∷
   rw 11 (q89 c4) ∷
   rw 10 (q90 c4) ∷
   rw 9 (q89 c4) ∷
   rw 8 (q91 c4) ∷
   rw 7 (q92 c4) ∷
   rw 8 (q86 c4) ∷
   rw⁻ 4 (q83 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   re 3 1 (ℓ "乎") ∷
   rw 4 (q1 c4) ∷
   rw 3 (q101 c4) ∷
   rw 4 (q102 c4) ∷
   rw 5 (q101 c4) ∷
   rw 6 (q102 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw 3 (q82 c4) ∷
   rw 3 (q83 c4) ∷
   rw⁻ 2 (q84 c4) ∷
   rw 4 (q85 c4) ∷
   rw⁻ 3 (q86 c4) ∷
   rw 9 (q87 c4) ∷
   rw 8 (q88 c4) ∷
   rw 7 (q89 c4) ∷
   rw 6 (q90 c4) ∷
   rw 5 (q89 c4) ∷
   rw 4 (q91 c4) ∷
   rw 3 (q92 c4) ∷
   rw 4 (q86 c4) ∷
   rw 6 (q93 c4) ∷
   rw⁻ 10 (q94 c4) ∷
   rw 9 (q95 c4) ∷
   rw⁻ 8 (q96 c4) ∷
   rw 7 (q95 c4) ∷
   rw⁻ 6 (q97 c4) ∷
   rw⁻ 7 (q93 c4) ∷
   rw⁻ 5 (q98 c4) ∷
   rw⁻ 4 (q84 c4) ∷
   rw 5 (q99 c4) ∷
   rw 6 (q100 c4) ∷
   rw⁻ 5 (q86 c4) ∷
   rw 11 (q87 c4) ∷
   rw 10 (q88 c4) ∷
   rw 9 (q89 c4) ∷
   rw 8 (q90 c4) ∷
   rw 7 (q89 c4) ∷
   rw 6 (q91 c4) ∷
   rw 5 (q92 c4) ∷
   rw 6 (q86 c4) ∷
   rw⁻ 2 (q83 c4) ∷
   rw⁻ 2 (q82 c4) ∷
   rw 1 (q103 c4) ∷
   rw 2 (q104 c4) ∷
   rw 1 (q1 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 1 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q8 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q12 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 3 (q105 c4) ∷
   rw 2 (q106 c4) ∷
   rw⁻ 6 (q107 c4) ∷
   rw⁻ 5 (q108 c4) ∷
   rw 4 (q109 c4) ∷
   rw⁻ 3 (q108 c4) ∷
   rw 2 (q110 c4) ∷
   rw⁻ 3 (q106 c4) ∷
   rw 3 (q111 c4) ∷
   rw 4 (q106 c4) ∷
   rw⁻ 8 (q107 c4) ∷
   rw⁻ 7 (q108 c4) ∷
   rw 6 (q109 c4) ∷
   rw⁻ 5 (q108 c4) ∷
   rw 4 (q110 c4) ∷
   rw⁻ 5 (q106 c4) ∷
   rw 5 (q111 c4) ∷
   rw⁻ 2 (q105 c4) ∷
   rw 3 (q112 c4) ∷
   rw 10 (q45 c4) ∷
   rw 4 (q113 c4) ∷
   rw 6 (q47 c4) ∷
   re 4 1 (ℓ "侥") ∷
   re 6 1 (ℓ "侦") ∷
   re 2 5 (ℓ "侧") ∷
   rw⁻ 3 (q48 c4) ∷
   re 2 1 (ℓ "仄亲侥亲侦") ∷
   re 4 1 (ℓ "乎") ∷
   re 6 1 (ℓ "乏") ∷
   rw⁻ 3 (q114 c4) ∷
   rw 2 (q105 c4) ∷
   rw⁻ 5 (q115 c4) ∷
   rw⁻ 7 (q116 c4) ∷
   rw⁻ 6 (q117 c4) ∷
   rw⁻ 7 (q118 c4) ∷
   rw 8 (q119 c4) ∷
   rw⁻ 9 (q120 c4) ∷
   rw 10 (q119 c4) ∷
   rw⁻ 11 (q121 c4) ∷
   rw⁻ 12 (q122 c4) ∷
   rw 6 (q116 c4) ∷
   rw 4 (q123 c4) ∷
   rw⁻ 3 (q115 c4) ∷
   rw⁻ 5 (q116 c4) ∷
   rw⁻ 4 (q117 c4) ∷
   rw⁻ 5 (q118 c4) ∷
   rw 6 (q119 c4) ∷
   rw⁻ 7 (q120 c4) ∷
   rw 8 (q119 c4) ∷
   rw⁻ 9 (q121 c4) ∷
   rw⁻ 10 (q122 c4) ∷
   rw 4 (q116 c4) ∷
   rw 2 (q123 c4) ∷
   rw⁻ 4 (q105 c4) ∷
   re 6 1 (ℓ "侥") ∷
   re 8 1 (ℓ "侦") ∷
   re 4 5 (ℓ "侧") ∷
   rw⁻ 1 (q69 c4) ∷
   rw⁻ 4 (q70 c4) ∷
   re 3 1 (ℓ "仄亲侥亲侦") ∷
   re 5 1 (ℓ "乎") ∷
   re 7 1 (ℓ "乏") ∷
   rw⁻ 4 (q124 c4) ∷
   rw 3 (q105 c4) ∷
   rw⁻ 6 (q125 c4) ∷
   rw 5 (q126 c4) ∷
   rw⁻ 4 (q125 c4) ∷
   rw 3 (q126 c4) ∷
   rw⁻ 4 (q105 c4) ∷
   re 6 1 (ℓ "侥") ∷
   re 8 1 (ℓ "侦") ∷
   re 4 5 (ℓ "侧") ∷
   rw⁻ 2 (q70 c4) ∷
   rw⁻ 5 (q48 c4) ∷
   re 4 1 (ℓ "仄亲侥亲侦") ∷
   re 6 1 (ℓ "乎") ∷
   re 8 1 (ℓ "乏") ∷
   rw⁻ 5 (q114 c4) ∷
   rw 4 (q105 c4) ∷
   rw⁻ 7 (q115 c4) ∷
   rw⁻ 9 (q116 c4) ∷
   rw⁻ 8 (q117 c4) ∷
   rw⁻ 9 (q118 c4) ∷
   rw 10 (q119 c4) ∷
   rw⁻ 11 (q120 c4) ∷
   rw 12 (q119 c4) ∷
   rw⁻ 13 (q121 c4) ∷
   rw⁻ 14 (q122 c4) ∷
   rw 8 (q116 c4) ∷
   rw 6 (q123 c4) ∷
   rw⁻ 5 (q115 c4) ∷
   rw⁻ 7 (q116 c4) ∷
   rw⁻ 6 (q117 c4) ∷
   rw⁻ 7 (q118 c4) ∷
   rw 8 (q119 c4) ∷
   rw⁻ 9 (q120 c4) ∷
   rw 10 (q119 c4) ∷
   rw⁻ 11 (q121 c4) ∷
   rw⁻ 12 (q122 c4) ∷
   rw 6 (q116 c4) ∷
   rw 4 (q123 c4) ∷
   rw⁻ 6 (q105 c4) ∷
   re 8 1 (ℓ "侥") ∷
   re 10 1 (ℓ "侦") ∷
   re 6 5 (ℓ "侧") ∷
   rw⁻ 3 (q69 c4) ∷
   rw⁻ 6 (q75 c4) ∷
   re 5 1 (ℓ "仄亲侥亲侦") ∷
   re 7 1 (ℓ "乎") ∷
   re 9 1 (ℓ "乏") ∷
   rw⁻ 6 (q127 c4) ∷
   rw 5 (q105 c4) ∷
   rw⁻ 8 (q128 c4) ∷
   rw 7 (q129 c4) ∷
   rw⁻ 6 (q128 c4) ∷
   rw 5 (q129 c4) ∷
   rw⁻ 6 (q105 c4) ∷
   re 8 1 (ℓ "侥") ∷
   re 10 1 (ℓ "侦") ∷
   re 6 5 (ℓ "侧") ∷
   rw⁻ 4 (q75 c4) ∷
   re 2 1 (ℓ "侪") ∷
   re 4 1 (ℓ "侫") ∷
   re 0 5 (ℓ "侬") ∷ []) Eq.refl

private
  q130 : Ws → Eqn
  q130 c4 = wpE 52 c4
  q131 : Ws → Eqn
  q131 c4 = wlE 206 (lit c4)
  q132 : Ws → Eqn
  q132 c4 = eqn (ℓ "亙並") (ℓ "並亙") (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))
  q133 : Ws → Eqn
  q133 c4 = wpE 55 c4
  q134 : Ws → Eqn
  q134 c4 = wlE 208 (lit c4)
  q135 : Ws → Eqn
  q135 c4 = wpE 835 c4
  q136 : Ws → Eqn
  q136 c4 = wpE 793 c4
  q137 : Ws → Eqn
  q137 c4 = sE 1056 (lem-comm-CX14-TOFF023 c4)
  q138 : Ws → Eqn
  q138 c4 = wlE 274 (lit c4)
  q139 : Ws → Eqn
  q139 c4 = wpE 62 c4
  q140 : Ws → Eqn
  q140 c4 = sE 6 (lem-comm-CX23-CCZ014 c4)
  q141 : Ws → Eqn
  q141 c4 = wpE 63 c4
  q142 : Ws → Eqn
  q142 c4 = wpE 64 c4
  q143 : Ws → Eqn
  q143 c4 = wpE 124 c4
  q144 : Ws → Eqn
  q144 c4 = wpE 836 c4
  q145 : Ws → Eqn
  q145 c4 = wpE 278 c4
  q146 : Ws → Eqn
  q146 c4 = wlE 1031 (lit c4)
  q147 : Ws → Eqn
  q147 c4 = wlE 1032 (lit c4)
  q148 : Ws → Eqn
  q148 c4 = wlE 305 (lit c4)
  q149 : Ws → Eqn
  q149 c4 = wlE 894 (lit c4)
  q150 : Ws → Eqn
  q150 c4 = wlE 1033 (lit c4)
  q151 : Ws → Eqn
  q151 c4 = sE 1384 (lem-comm-TOFF014-CX23 c4)
  q152 : Ws → Eqn
  q152 c4 = wpE 837 c4
  q153 : Ws → Eqn
  q153 c4 = wpE 838 c4
  q154 : Ws → Eqn
  q154 c4 = wpE 839 c4
  q155 : Ws → Eqn
  q155 c4 = wpE 840 c4
  q156 : Ws → Eqn
  q156 c4 = wpE 841 c4
  q157 : Ws → Eqn
  q157 c4 = wlE 211 (lit c4)
  q158 : Ws → Eqn
  q158 c4 = wlE 896 (lit c4)
  q159 : Ws → Eqn
  q159 c4 = wlE 1034 (lit c4)
  q160 : Ws → Eqn
  q160 c4 = sE 1382 (lem-comm-CCZ024-CS13 c4)
  q161 : Ws → Eqn
  q161 c4 = wlE 900 (lit c4)
  q162 : Ws → Eqn
  q162 c4 = wlE 1035 (lit c4)
  q163 : Ws → Eqn
  q163 c4 = sE 1383 (lem-comm-CCZ024-CSd13 c4)

-- F4-CS2-CS1: 254 steps
lem-F4-CS2-CS1 : Ws → ⟪ (ℓ "並侬並侧") ⟫ʷ ≈ ⟪ (ℓ "侧並侬並") ⟫ʷ
lem-F4-CS2-CS1 c4 = derive (ℓ "並侬並侧") (ℓ "侧並侬並")
  (re 3 1 (ℓ "仄亲侥亲侦") ∷
   re 5 1 (ℓ "乎") ∷
   re 7 1 (ℓ "乏") ∷
   rw 3 (q105 c4) ∷
   rw⁻ 2 (q130 c4) ∷
   rw 4 (q131 c4) ∷
   rw⁻ 3 (q132 c4) ∷
   rw 6 (q106 c4) ∷
   rw⁻ 10 (q107 c4) ∷
   rw⁻ 9 (q108 c4) ∷
   rw 8 (q109 c4) ∷
   rw⁻ 7 (q108 c4) ∷
   rw 6 (q110 c4) ∷
   rw⁻ 7 (q106 c4) ∷
   rw⁻ 5 (q133 c4) ∷
   rw⁻ 4 (q130 c4) ∷
   rw 5 (q134 c4) ∷
   rw 6 (q111 c4) ∷
   rw⁻ 5 (q132 c4) ∷
   rw⁻ 2 (q105 c4) ∷
   re 1 1 (ℓ "仞亭侪亭侫") ∷
   re 5 1 (ℓ "么") ∷
   rw 6 (q105 c4) ∷
   rw⁻ 5 (q129 c4) ∷
   rw 6 (q128 c4) ∷
   rw⁻ 7 (q129 c4) ∷
   rw 8 (q128 c4) ∷
   rw⁻ 5 (q105 c4) ∷
   rw 5 (q105 c4) ∷
   rw⁻ 4 (q135 c4) ∷
   rw 6 (q136 c4) ∷
   rw⁻ 5 (q116 c4) ∷
   rw 11 (q122 c4) ∷
   rw 10 (q121 c4) ∷
   rw 9 (q137 c4) ∷
   rw 8 (q120 c4) ∷
   rw 7 (q137 c4) ∷
   rw 6 (q118 c4) ∷
   rw 5 (q117 c4) ∷
   rw 6 (q116 c4) ∷
   rw 8 (q138 c4) ∷
   rw⁻ 12 (q139 c4) ∷
   rw 11 (q140 c4) ∷
   rw⁻ 10 (q141 c4) ∷
   rw 9 (q140 c4) ∷
   rw⁻ 8 (q142 c4) ∷
   rw⁻ 9 (q138 c4) ∷
   rw⁻ 7 (q143 c4) ∷
   rw⁻ 6 (q135 c4) ∷
   rw 7 (q144 c4) ∷
   rw 8 (q145 c4) ∷
   rw⁻ 7 (q116 c4) ∷
   rw 13 (q122 c4) ∷
   rw 12 (q121 c4) ∷
   rw 11 (q137 c4) ∷
   rw 10 (q120 c4) ∷
   rw 9 (q137 c4) ∷
   rw 8 (q118 c4) ∷
   rw 7 (q117 c4) ∷
   rw 8 (q116 c4) ∷
   rw⁻ 4 (q105 c4) ∷
   re 3 1 (ℓ "乇") ∷
   rw 4 (q105 c4) ∷
   rw⁻ 3 (q126 c4) ∷
   rw 4 (q125 c4) ∷
   rw⁻ 5 (q126 c4) ∷
   rw 6 (q125 c4) ∷
   rw⁻ 3 (q105 c4) ∷
   rw 3 (q105 c4) ∷
   rw⁻ 2 (q135 c4) ∷
   rw 4 (q136 c4) ∷
   rw⁻ 3 (q116 c4) ∷
   rw 9 (q122 c4) ∷
   rw 8 (q121 c4) ∷
   rw 7 (q137 c4) ∷
   rw 6 (q120 c4) ∷
   rw 5 (q137 c4) ∷
   rw 4 (q118 c4) ∷
   rw 3 (q117 c4) ∷
   rw 4 (q116 c4) ∷
   rw 6 (q138 c4) ∷
   rw⁻ 10 (q139 c4) ∷
   rw 9 (q140 c4) ∷
   rw⁻ 8 (q141 c4) ∷
   rw 7 (q140 c4) ∷
   rw⁻ 6 (q142 c4) ∷
   rw⁻ 7 (q138 c4) ∷
   rw⁻ 5 (q143 c4) ∷
   rw⁻ 4 (q135 c4) ∷
   rw 5 (q144 c4) ∷
   rw 6 (q145 c4) ∷
   rw⁻ 5 (q116 c4) ∷
   rw 11 (q122 c4) ∷
   rw 10 (q121 c4) ∷
   rw 9 (q137 c4) ∷
   rw 8 (q120 c4) ∷
   rw 7 (q137 c4) ∷
   rw 6 (q118 c4) ∷
   rw 5 (q117 c4) ∷
   rw 6 (q116 c4) ∷
   rw⁻ 2 (q105 c4) ∷
   rw 1 (q104 c4) ∷
   rw 2 (q103 c4) ∷
   rw 1 (q105 c4) ∷
   rw⁻ 0 (q130 c4) ∷
   rw 2 (q131 c4) ∷
   rw⁻ 1 (q132 c4) ∷
   rw 4 (q106 c4) ∷
   rw⁻ 8 (q107 c4) ∷
   rw⁻ 7 (q108 c4) ∷
   rw 6 (q109 c4) ∷
   rw⁻ 5 (q108 c4) ∷
   rw 4 (q110 c4) ∷
   rw⁻ 5 (q106 c4) ∷
   rw⁻ 3 (q133 c4) ∷
   rw⁻ 2 (q130 c4) ∷
   rw 3 (q134 c4) ∷
   rw 4 (q111 c4) ∷
   rw⁻ 3 (q132 c4) ∷
   rw⁻ 0 (q105 c4) ∷
   rw 3 (q1 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 3 (q12 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q8 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw 5 (q12 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 3 (q146 c4) ∷
   rw 10 (q45 c4) ∷
   rw 4 (q147 c4) ∷
   rw 6 (q148 c4) ∷
   re 4 1 (ℓ "侪") ∷
   re 6 1 (ℓ "侫") ∷
   re 2 5 (ℓ "侬") ∷
   rw⁻ 3 (q149 c4) ∷
   re 2 1 (ℓ "仞亭侪亭侫") ∷
   re 4 1 (ℓ "乇") ∷
   re 6 1 (ℓ "么") ∷
   rw⁻ 3 (q150 c4) ∷
   rw 2 (q82 c4) ∷
   rw 2 (q83 c4) ∷
   rw 5 (q151 c4) ∷
   rw⁻ 7 (q86 c4) ∷
   rw⁻ 6 (q92 c4) ∷
   rw⁻ 7 (q91 c4) ∷
   rw 8 (q151 c4) ∷
   rw⁻ 9 (q90 c4) ∷
   rw 10 (q151 c4) ∷
   rw⁻ 11 (q88 c4) ∷
   rw⁻ 12 (q87 c4) ∷
   rw 6 (q86 c4) ∷
   rw 4 (q152 c4) ∷
   rw 3 (q151 c4) ∷
   rw⁻ 5 (q86 c4) ∷
   rw⁻ 4 (q92 c4) ∷
   rw⁻ 5 (q91 c4) ∷
   rw 6 (q151 c4) ∷
   rw⁻ 7 (q90 c4) ∷
   rw 8 (q151 c4) ∷
   rw⁻ 9 (q88 c4) ∷
   rw⁻ 10 (q87 c4) ∷
   rw 4 (q86 c4) ∷
   rw⁻ 5 (q153 c4) ∷
   rw⁻ 7 (q154 c4) ∷
   rw⁻ 5 (q155 c4) ∷
   rw 2 (q156 c4) ∷
   rw⁻ 4 (q83 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   re 6 1 (ℓ "侪") ∷
   re 8 1 (ℓ "侫") ∷
   re 4 5 (ℓ "侬") ∷
   rw⁻ 1 (q157 c4) ∷
   rw⁻ 4 (q158 c4) ∷
   re 3 1 (ℓ "仞亭侪亭侫") ∷
   re 5 1 (ℓ "乇") ∷
   re 7 1 (ℓ "么") ∷
   rw⁻ 4 (q159 c4) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 6 (q102 c4) ∷
   rw 5 (q160 c4) ∷
   rw⁻ 4 (q102 c4) ∷
   rw 3 (q160 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 6 1 (ℓ "侪") ∷
   re 8 1 (ℓ "侫") ∷
   re 4 5 (ℓ "侬") ∷
   rw⁻ 2 (q158 c4) ∷
   rw⁻ 5 (q149 c4) ∷
   re 4 1 (ℓ "仞亭侪亭侫") ∷
   re 6 1 (ℓ "乇") ∷
   re 8 1 (ℓ "么") ∷
   rw⁻ 5 (q150 c4) ∷
   rw 4 (q82 c4) ∷
   rw 4 (q83 c4) ∷
   rw 7 (q151 c4) ∷
   rw⁻ 9 (q86 c4) ∷
   rw⁻ 8 (q92 c4) ∷
   rw⁻ 9 (q91 c4) ∷
   rw 10 (q151 c4) ∷
   rw⁻ 11 (q90 c4) ∷
   rw 12 (q151 c4) ∷
   rw⁻ 13 (q88 c4) ∷
   rw⁻ 14 (q87 c4) ∷
   rw 8 (q86 c4) ∷
   rw 6 (q152 c4) ∷
   rw 5 (q151 c4) ∷
   rw⁻ 7 (q86 c4) ∷
   rw⁻ 6 (q92 c4) ∷
   rw⁻ 7 (q91 c4) ∷
   rw 8 (q151 c4) ∷
   rw⁻ 9 (q90 c4) ∷
   rw 10 (q151 c4) ∷
   rw⁻ 11 (q88 c4) ∷
   rw⁻ 12 (q87 c4) ∷
   rw 6 (q86 c4) ∷
   rw⁻ 7 (q153 c4) ∷
   rw⁻ 9 (q154 c4) ∷
   rw⁻ 7 (q155 c4) ∷
   rw 4 (q156 c4) ∷
   rw⁻ 6 (q83 c4) ∷
   rw⁻ 6 (q82 c4) ∷
   re 8 1 (ℓ "侪") ∷
   re 10 1 (ℓ "侫") ∷
   re 6 5 (ℓ "侬") ∷
   rw⁻ 3 (q157 c4) ∷
   rw⁻ 6 (q161 c4) ∷
   re 5 1 (ℓ "仞亭侪亭侫") ∷
   re 7 1 (ℓ "乇") ∷
   re 9 1 (ℓ "么") ∷
   rw⁻ 6 (q162 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 8 (q81 c4) ∷
   rw 7 (q163 c4) ∷
   rw⁻ 6 (q81 c4) ∷
   rw 5 (q163 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 8 1 (ℓ "侪") ∷
   re 10 1 (ℓ "侫") ∷
   re 6 5 (ℓ "侬") ∷
   rw⁻ 4 (q161 c4) ∷
   re 2 1 (ℓ "侥") ∷
   re 4 1 (ℓ "侦") ∷
   re 0 5 (ℓ "侧") ∷ []) Eq.refl

private
  q164 : Ws → Eqn
  q164 c4 = sE 1490 (lem-CKu-box-2-at243243 c4)
  q165 : Ws → Eqn
  q165 c4 = wpE 870 c4
  q166 : Ws → Eqn
  q166 c4 = wpE 871 c4
  q167 : Ws → Eqn
  q167 c4 = wpE 872 c4

-- F2-K0-CS1: 11 steps
lem-F2-K0-CS1 : Ws → ⟪ (ℓ "亁侧") ⟫ʷ ≈ ⟪ (ℓ "侧亁") ⟫ʷ
lem-F2-K0-CS1 c4 = derive (ℓ "亁侧") (ℓ "侧亁")
  (re 1 1 (ℓ "仄亲侥亲侦") ∷
   re 3 1 (ℓ "乎") ∷
   re 5 1 (ℓ "乏") ∷
   rw 0 (q164 c4) ∷
   rw 1 (q165 c4) ∷
   rw 2 (q166 c4) ∷
   rw 3 (q165 c4) ∷
   rw 4 (q167 c4) ∷
   re 2 1 (ℓ "侥") ∷
   re 4 1 (ℓ "侦") ∷
   re 0 5 (ℓ "侧") ∷ []) Eq.refl

private
  q168 : Ws → Eqn
  q168 c4 = sE 1489 (lem-CKu-box-2-at122441 c4)
  q169 : Ws → Eqn
  q169 c4 = wpE 873 c4
  q170 : Ws → Eqn
  q170 c4 = wpE 874 c4
  q171 : Ws → Eqn
  q171 c4 = wpE 875 c4

-- F2-K0-CS2: 11 steps
lem-F2-K0-CS2 : Ws → ⟪ (ℓ "亁侬") ⟫ʷ ≈ ⟪ (ℓ "侬亁") ⟫ʷ
lem-F2-K0-CS2 c4 = derive (ℓ "亁侬") (ℓ "侬亁")
  (re 1 1 (ℓ "仞亭侪亭侫") ∷
   re 3 1 (ℓ "乇") ∷
   re 5 1 (ℓ "么") ∷
   rw 0 (q168 c4) ∷
   rw 1 (q169 c4) ∷
   rw 2 (q170 c4) ∷
   rw 3 (q169 c4) ∷
   rw 4 (q171 c4) ∷
   re 2 1 (ℓ "侪") ∷
   re 4 1 (ℓ "侫") ∷
   re 0 5 (ℓ "侬") ∷ []) Eq.refl

private
  q172 : Ws → Eqn
  q172 c4 = sE 1488 (lem-CKu-box-2-at0210243143 c4)
  q173 : Ws → Eqn
  q173 c4 = wlE 1068 (lit c4)
  q174 : Ws → Eqn
  q174 c4 = wpE 878 c4
  q175 : Ws → Eqn
  q175 c4 = wpE 879 c4

-- F2-K2-CS0: 11 steps
lem-F2-K2-CS0 : Ws → ⟪ (ℓ "亇俄") ⟫ʷ ≈ ⟪ (ℓ "俄亇") ⟫ʷ
lem-F2-K2-CS0 c4 = derive (ℓ "亇俄") (ℓ "俄亇")
  (re 1 1 (ℓ "伱亮係亮促") ∷
   re 3 1 (ℓ "丶") ∷
   re 5 1 (ℓ "丷") ∷
   rw 0 (q172 c4) ∷
   rw 1 (q173 c4) ∷
   rw 2 (q174 c4) ∷
   rw 3 (q173 c4) ∷
   rw 4 (q175 c4) ∷
   re 2 1 (ℓ "係") ∷
   re 4 1 (ℓ "促") ∷
   re 0 5 (ℓ "俄") ∷ []) Eq.refl

private
  q176 : Ws → Eqn
  q176 c4 = sE 1509 (lem-box2 c4)
  q177 : Ws → Eqn
  q177 c4 = sE 1521 (lem-CKc-box c4)

-- CKc-boxL: 3 steps
lem-CKc-boxL : Ws → ⟪ (ℓ "乾亹") ⟫ʷ ≈ ⟪ (ℓ "亹亨乾亨") ⟫ʷ
lem-CKc-boxL c4 = derive (ℓ "乾亹") (ℓ "亹亨乾亨")
  (rw⁻ 0 (q176 c4) ∷
   rw 1 (q177 c4) ∷
   rw 4 (q176 c4) ∷ []) Eq.refl

private
  q178 : Ws → Eqn
  q178 c4 = sE 1522 (lem-CKdc-box c4)

-- CKdc-boxL: 3 steps
lem-CKdc-boxL : Ws → ⟪ (ℓ "乿亹") ⟫ʷ ≈ ⟪ (ℓ "亹亨乿亨") ⟫ʷ
lem-CKdc-boxL c4 = derive (ℓ "乿亹") (ℓ "亹亨乿亨")
  (rw⁻ 0 (q176 c4) ∷
   rw 1 (q178 c4) ∷
   rw 4 (q176 c4) ∷ []) Eq.refl

private
  q179 : Ws → Eqn
  q179 c4 = sE 1525 (lem-S2-SBOX⟨2·0·41·3⟩ c4)
  q180 : Ws → Eqn
  q180 c4 = wpE 161 c4
  q181 : Ws → Eqn
  q181 c4 = wlE 1112 (lit c4)
  q182 : Ws → Eqn
  q182 c4 = sE 1506 (lem-nf-order-CSat0 c4)

-- F1-order-CS@0: 5 steps
lem-F1-order-CSat0 : Ws → ⟪ (ℓ "俄俄俄俄") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CSat0 c4 = derive (ℓ "俄俄俄俄") []
  (rw 0 (q179 c4) ∷
   rw 1 (q179 c4) ∷
   rw 0 (q180 c4) ∷
   rw 0 (q181 c4) ∷
   rw⁻ 0 (q182 c4) ∷ []) Eq.refl

private
  q183 : Ws → Eqn
  q183 c4 = sE 1523 (lem-S2-SBOX⟨0·1·42·3⟩ c4)
  q184 : Ws → Eqn
  q184 c4 = sE 1507 (lem-nf-order-CSat1 c4)

-- F1-order-CS@1: 5 steps
lem-F1-order-CSat1 : Ws → ⟪ (ℓ "侧侧侧侧") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CSat1 c4 = derive (ℓ "侧侧侧侧") []
  (rw 0 (q183 c4) ∷
   rw 1 (q183 c4) ∷
   rw 0 (q47 c4) ∷
   rw 0 (q181 c4) ∷
   rw⁻ 0 (q184 c4) ∷ []) Eq.refl

private
  q185 : Ws → Eqn
  q185 c4 = sE 1524 (lem-S2-SBOX⟨0·2·43·1⟩ c4)
  q186 : Ws → Eqn
  q186 c4 = sE 1508 (lem-nf-order-CSat2 c4)

-- F1-order-CS@2: 5 steps
lem-F1-order-CSat2 : Ws → ⟪ (ℓ "侬侬侬侬") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CSat2 c4 = derive (ℓ "侬侬侬侬") []
  (rw 0 (q185 c4) ∷
   rw 1 (q185 c4) ∷
   rw 0 (q148 c4) ∷
   rw 0 (q181 c4) ∷
   rw⁻ 0 (q186 c4) ∷ []) Eq.refl

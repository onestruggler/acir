{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD039 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D039 (Sᴰ : SD039) where

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
  lem-comm-CS24-CCZ013 : Ws → St 194
  lem-comm-CS24-CCZ013 = pickᴰ 0 Sᴰ
  lem-comm-CSd24-CCZ013 : Ws → St 204
  lem-comm-CSd24-CCZ013 = pickᴰ 1 Sᴰ
  lem-comm-CCZ014-CX23 : Ws → St 893
  lem-comm-CCZ014-CX23 = pickᴰ 2 Sᴰ
  lem-comm-CCZ024-CX13 : Ws → St 1024
  lem-comm-CCZ024-CX13 = pickᴰ 3 Sᴰ
  lem-comm-CS02-CCZ134 : Ws → St 431
  lem-comm-CS02-CCZ134 = pickᴰ 4 Sᴰ
  lem-comm-CSd02-CCZ134 : Ws → St 432
  lem-comm-CSd02-CCZ134 = pickᴰ 5 Sᴰ
  lem-comm-CX14-TOFF302 : Ws → St 1301
  lem-comm-CX14-TOFF302 = pickᴰ 6 Sᴰ
  lem-comm-TOFF013-CS24 : Ws → St 1286
  lem-comm-TOFF013-CS24 = pickᴰ 7 Sᴰ
  lem-comm-TOFF013-CX24 : Ws → St 1059
  lem-comm-TOFF013-CX24 = pickᴰ 8 Sᴰ
  lem-comm-TOFF213-CS04 : Ws → St 1287
  lem-comm-TOFF213-CS04 = pickᴰ 9 Sᴰ
  lem-comm-TOFF213-CX04 : Ws → St 1028
  lem-comm-TOFF213-CX04 = pickᴰ 10 Sᴰ
  lem-comm-TOFF023-CS14 : Ws → St 1288
  lem-comm-TOFF023-CS14 = pickᴰ 11 Sᴰ
  lem-comm-TOFF023-CX14 : Ws → St 1060
  lem-comm-TOFF023-CX14 = pickᴰ 12 Sᴰ
  lem-box-tQ-at143143 : Ws → St 314
  lem-box-tQ-at143143 = pickᴰ 13 Sᴰ
  lem-box-tQ-at03143140 : Ws → St 357
  lem-box-tQ-at03143140 = pickᴰ 14 Sᴰ
  lem-box-cP-at0210243143 : Ws → St 994
  lem-box-cP-at0210243143 = pickᴰ 15 Sᴰ
  lem-box-cP-at0314213240 : Ws → St 1121
  lem-box-cP-at0314213240 = pickᴰ 16 Sᴰ
  lem-box-cP-at122441 : Ws → St 1002
  lem-box-cP-at122441 = pickᴰ 17 Sᴰ
  lem-box-cP-at243243 : Ws → St 1008
  lem-box-cP-at243243 = pickᴰ 18 Sᴰ
  lem-box-perm-1423-at122441 : Ws → St 1257
  lem-box-perm-1423-at122441 = pickᴰ 19 Sᴰ
  lem-box-box-4-at03243240 : Ws → St 1526
  lem-box-box-4-at03243240 = pickᴰ 20 Sᴰ
  lem-box-perm-1324-at03143140 : Ws → St 1527
  lem-box-perm-1324-at03143140 = pickᴰ 21 Sᴰ
  lem-box-perm-2314-at03243240 : Ws → St 1528
  lem-box-perm-2314-at03243240 = pickᴰ 22 Sᴰ
  lem-box-perm-3124-at03143140 : Ws → St 1529
  lem-box-perm-3124-at03143140 = pickᴰ 23 Sᴰ
  lem-box-perm-1423-at0210243143 : Ws → St 1496
  lem-box-perm-1423-at0210243143 = pickᴰ 24 Sᴰ
  lem-box-perm-1423-at243243 : Ws → St 1497
  lem-box-perm-1423-at243243 = pickᴰ 25 Sᴰ
  lem-S2-SBOX⟨0·1·42·3⟩ : Ws → St 1523
  lem-S2-SBOX⟨0·1·42·3⟩ = pickᴰ 26 Sᴰ
  lem-S2-SBOX⟨0·2·43·1⟩ : Ws → St 1524
  lem-S2-SBOX⟨0·2·43·1⟩ = pickᴰ 27 Sᴰ
  lem-S2-SBOX⟨2·0·41·3⟩ : Ws → St 1525
  lem-S2-SBOX⟨2·0·41·3⟩ = pickᴰ 28 Sᴰ
  lem-CKc-box-at0210233441 : Ws → St 1530
  lem-CKc-box-at0210233441 = pickᴰ 29 Sᴰ
  lem-CKc-box-at02233440 : Ws → St 1531
  lem-CKc-box-at02233440 = pickᴰ 30 Sᴰ
  lem-CKc-box-at12213443 : Ws → St 1532
  lem-CKc-box-at12213443 = pickᴰ 31 Sᴰ
  lem-CKc-box-at12233441 : Ws → St 1533
  lem-CKc-box-at12233441 = pickᴰ 32 Sᴰ
  lem-CKc-box-at13213442 : Ws → St 1534
  lem-CKc-box-at13213442 = pickᴰ 33 Sᴰ
  lem-CKc-box-at233442 : Ws → St 1535
  lem-CKc-box-at233442 = pickᴰ 34 Sᴰ
  lem-box-perm-1342-at0210233441 : Ws → St 1536
  lem-box-perm-1342-at0210233441 = pickᴰ 35 Sᴰ
  lem-box-perm-1342-at12213443 : Ws → St 1537
  lem-box-perm-1342-at12213443 = pickᴰ 36 Sᴰ
  lem-box-perm-1342-at233442 : Ws → St 1538
  lem-box-perm-1342-at233442 = pickᴰ 37 Sᴰ
  lem-box-perm-3421-at0210243143 : Ws → St 1539
  lem-box-perm-3421-at0210243143 = pickᴰ 38 Sᴰ
  lem-box-perm-3421-at122441 : Ws → St 1540
  lem-box-perm-3421-at122441 = pickᴰ 39 Sᴰ
  lem-box-perm-3421-at13213442 : Ws → St 1541
  lem-box-perm-3421-at13213442 = pickᴰ 40 Sᴰ
  lem-box-perm-3421-at243243 : Ws → St 1542
  lem-box-perm-3421-at243243 = pickᴰ 41 Sᴰ
  lem-box-perm-4312-at02233440 : Ws → St 1543
  lem-box-perm-4312-at02233440 = pickᴰ 42 Sᴰ
  lem-box-perm-4312-at12233441 : Ws → St 1544
  lem-box-perm-4312-at12233441 = pickᴰ 43 Sᴰ
  lem-box-perm-4312-at13213442 : Ws → St 1545
  lem-box-perm-4312-at13213442 = pickᴰ 44 Sᴰ
  lem-box-perm-4312-at143143 : Ws → St 1546
  lem-box-perm-4312-at143143 = pickᴰ 45 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1525 (lem-S2-SBOX⟨2·0·41·3⟩ c4)
  q2 : Ws → Eqn
  q2 c4 = sE 994 (lem-box-cP-at0210243143 c4)
  q3 : Ws → Eqn
  q3 c4 = wlE 747 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = wpE 654 c4
  q5 : Ws → Eqn
  q5 c4 = wlE 190 (lit c4)
  q6 : Ws → Eqn
  q6 c4 = wpE 37 c4
  q7 : Ws → Eqn
  q7 c4 = wpE 36 c4
  q8 : Ws → Eqn
  q8 c4 = sE 1024 (lem-comm-CCZ024-CX13 c4)
  q9 : Ws → Eqn
  q9 c4 = wpE 35 c4
  q10 : Ws → Eqn
  q10 c4 = wpE 34 c4
  q11 : Ws → Eqn
  q11 c4 = wpE 33 c4
  q12 : Ws → Eqn
  q12 c4 = wlE 197 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = wpE 41 c4
  q14 : Ws → Eqn
  q14 c4 = wlE 195 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1028 (lem-comm-TOFF213-CX04 c4)
  q16 : Ws → Eqn
  q16 c4 = wlE 194 (lit c4)
  q17 : Ws → Eqn
  q17 c4 = wlE 193 (lit c4)
  q18 : Ws → Eqn
  q18 c4 = wpE 44 c4
  q19 : Ws → Eqn
  q19 c4 = wpE 38 c4
  q20 : Ws → Eqn
  q20 c4 = wlE 196 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = wpE 21 c4
  q22 : Ws → Eqn
  q22 c4 = wlE 191 (lit c4)
  q23 : Ws → Eqn
  q23 c4 = wpE 32 c4
  q24 : Ws → Eqn
  q24 c4 = sE 1539 (lem-box-perm-3421-at0210243143 c4)
  q25 : Ws → Eqn
  q25 c4 = sE 1531 (lem-CKc-box-at02233440 c4)
  q26 : Ws → Eqn
  q26 c4 = sE 1543 (lem-box-perm-4312-at02233440 c4)
  q27 : Ws → Eqn
  q27 c4 = sE 1287 (lem-comm-TOFF213-CS04 c4)
  q28 : Ws → Eqn
  q28 c4 = wpE 906 c4
  q29 : Ws → Eqn
  q29 c4 = wlE 727 (lit c4)
  q30 : Ws → Eqn
  q30 c4 = wpE 617 c4
  q31 : Ws → Eqn
  q31 c4 = wpE 161 c4
  q32 : Ws → Eqn
  q32 c4 = wpE 930 c4
  q33 : Ws → Eqn
  q33 c4 = wlE 230 (lit c4)

-- nf-X-CS0@0: 115 steps
lem-nf-X-CS0at0 : Ws → ⟪ (ℓ "俄俄俄亁丽丽亁丢乕") ⟫ʷ ≈ ⟪ (ℓ "亮丶五亮丷亐亁丽丽亁亐丢乕伱") ⟫ʷ
lem-nf-X-CS0at0 c4 = derive (ℓ "俄俄俄亁丽丽亁丢乕") (ℓ "亮丶五亮丷亐亁丽丽亁亐丢乕伱")
  (rw 0 (q1 c4) ∷
   re 1 1 (ℓ "伱亮係亮促") ∷
   re 3 1 (ℓ "丶") ∷
   re 5 1 (ℓ "丷") ∷
   rw 1 (q2 c4) ∷
   rw 4 (q3 c4) ∷
   rw 3 (q4 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q9 c4) ∷
   rw 9 (q8 c4) ∷
   rw 10 (q10 c4) ∷
   rw 11 (q11 c4) ∷
   rw 5 (q5 c4) ∷
   rw 2 (q12 c4) ∷
   rw 4 (q13 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw 4 (q15 c4) ∷
   rw⁻ 5 (q16 c4) ∷
   rw 6 (q15 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 2 (q18 c4) ∷
   rw⁻ 1 (q19 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   rw 3 (q7 c4) ∷
   rw 4 (q8 c4) ∷
   rw 5 (q9 c4) ∷
   rw 6 (q8 c4) ∷
   rw 7 (q10 c4) ∷
   rw 8 (q11 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 6 (q20 c4) ∷
   rw 5 (q21 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw 3 (q21 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 4 (q2 c4) ∷
   rw 7 (q3 c4) ∷
   rw 6 (q4 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw 8 (q6 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q8 c4) ∷
   rw 11 (q9 c4) ∷
   rw 12 (q8 c4) ∷
   rw 13 (q10 c4) ∷
   rw 14 (q11 c4) ∷
   rw 8 (q5 c4) ∷
   rw 5 (q12 c4) ∷
   rw 7 (q13 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw 7 (q15 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   rw 9 (q15 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 5 (q18 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q9 c4) ∷
   rw 9 (q8 c4) ∷
   rw 10 (q10 c4) ∷
   rw 11 (q11 c4) ∷
   rw 5 (q5 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   rw 6 (q2 c4) ∷
   rw⁻ 9 (q22 c4) ∷
   rw 8 (q23 c4) ∷
   rw⁻ 7 (q22 c4) ∷
   rw 6 (q23 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   rw 7 (q24 c4) ∷
   rw 7 (q25 c4) ∷
   rw 10 (q26 c4) ∷
   rw 10 (q2 c4) ∷
   rw 13 (q27 c4) ∷
   rw 12 (q28 c4) ∷
   rw 11 (q27 c4) ∷
   rw 10 (q28 c4) ∷
   rw⁻ 11 (q2 c4) ∷
   rw 11 (q2 c4) ∷
   rw 14 (q27 c4) ∷
   rw 13 (q28 c4) ∷
   rw 12 (q27 c4) ∷
   rw 11 (q28 c4) ∷
   rw⁻ 12 (q2 c4) ∷
   rw 12 (q24 c4) ∷
   rw 12 (q25 c4) ∷
   rw 15 (q26 c4) ∷
   rw 15 (q2 c4) ∷
   rw⁻ 18 (q29 c4) ∷
   rw 17 (q30 c4) ∷
   rw⁻ 16 (q29 c4) ∷
   rw 15 (q30 c4) ∷
   rw⁻ 16 (q2 c4) ∷
   rw 16 (q2 c4) ∷
   rw⁻ 19 (q14 c4) ∷
   rw 18 (q10 c4) ∷
   rw⁻ 17 (q14 c4) ∷
   rw 16 (q10 c4) ∷
   rw⁻ 17 (q2 c4) ∷
   rw 0 (q31 c4) ∷
   rw 7 (q32 c4) ∷
   rw 9 (q33 c4) ∷ []) Eq.refl

private
  q34 : Ws → Eqn
  q34 c4 = sE 1523 (lem-S2-SBOX⟨0·1·42·3⟩ c4)
  q35 : Ws → Eqn
  q35 c4 = sE 1008 (lem-box-cP-at243243 c4)
  q36 : Ws → Eqn
  q36 c4 = wpE 805 c4
  q37 : Ws → Eqn
  q37 c4 = wpE 806 c4
  q38 : Ws → Eqn
  q38 c4 = wlE 217 (lit c4)
  q39 : Ws → Eqn
  q39 c4 = wpE 65 c4
  q40 : Ws → Eqn
  q40 c4 = wpE 64 c4
  q41 : Ws → Eqn
  q41 c4 = sE 893 (lem-comm-CCZ014-CX23 c4)
  q42 : Ws → Eqn
  q42 c4 = wpE 63 c4
  q43 : Ws → Eqn
  q43 c4 = wpE 62 c4
  q44 : Ws → Eqn
  q44 c4 = wpE 61 c4
  q45 : Ws → Eqn
  q45 c4 = wpE 72 c4
  q46 : Ws → Eqn
  q46 c4 = wlE 220 (lit c4)
  q47 : Ws → Eqn
  q47 c4 = wpE 70 c4
  q48 : Ws → Eqn
  q48 c4 = sE 1060 (lem-comm-TOFF023-CX14 c4)
  q49 : Ws → Eqn
  q49 c4 = wpE 69 c4
  q50 : Ws → Eqn
  q50 c4 = wlE 221 (lit c4)
  q51 : Ws → Eqn
  q51 c4 = wpE 74 c4
  q52 : Ws → Eqn
  q52 c4 = wpE 66 c4
  q53 : Ws → Eqn
  q53 c4 = wlE 222 (lit c4)
  q54 : Ws → Eqn
  q54 c4 = wpE 53 c4
  q55 : Ws → Eqn
  q55 c4 = wlE 219 (lit c4)
  q56 : Ws → Eqn
  q56 c4 = wpE 60 c4
  q57 : Ws → Eqn
  q57 c4 = sE 1542 (lem-box-perm-3421-at243243 c4)
  q58 : Ws → Eqn
  q58 c4 = sE 1533 (lem-CKc-box-at12233441 c4)
  q59 : Ws → Eqn
  q59 c4 = sE 1544 (lem-box-perm-4312-at12233441 c4)
  q60 : Ws → Eqn
  q60 c4 = sE 1288 (lem-comm-TOFF023-CS14 c4)
  q61 : Ws → Eqn
  q61 c4 = wpE 908 c4
  q62 : Ws → Eqn
  q62 c4 = wpE 632 c4
  q63 : Ws → Eqn
  q63 c4 = wpE 633 c4
  q64 : Ws → Eqn
  q64 c4 = wlE 263 (lit c4)
  q65 : Ws → Eqn
  q65 c4 = wlE 1141 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = wlE 181 (lit c4)

-- nf-X-CS0@1: 115 steps
lem-nf-X-CS0at1 : Ws → ⟪ (ℓ "侧侧侧亄乕乕亄丢乩") ⟫ʷ ≈ ⟪ (ℓ "亲乎亨亲乏交亄乕乕亄交丢乩仄") ⟫ʷ
lem-nf-X-CS0at1 c4 = derive (ℓ "侧侧侧亄乕乕亄丢乩") (ℓ "亲乎亨亲乏交亄乕乕亄交丢乩仄")
  (rw 0 (q34 c4) ∷
   re 1 1 (ℓ "仄亲侥亲侦") ∷
   re 3 1 (ℓ "乎") ∷
   re 5 1 (ℓ "乏") ∷
   rw 1 (q35 c4) ∷
   rw 4 (q36 c4) ∷
   rw 3 (q37 c4) ∷
   rw⁻ 6 (q38 c4) ∷
   rw 5 (q39 c4) ∷
   rw 6 (q40 c4) ∷
   rw 7 (q41 c4) ∷
   rw 8 (q42 c4) ∷
   rw 9 (q41 c4) ∷
   rw 10 (q43 c4) ∷
   rw 11 (q44 c4) ∷
   rw 5 (q38 c4) ∷
   rw 2 (q45 c4) ∷
   rw 4 (q46 c4) ∷
   rw⁻ 3 (q47 c4) ∷
   rw 4 (q48 c4) ∷
   rw⁻ 5 (q49 c4) ∷
   rw 6 (q48 c4) ∷
   rw⁻ 7 (q50 c4) ∷
   rw⁻ 3 (q46 c4) ∷
   rw 4 (q36 c4) ∷
   rw⁻ 2 (q51 c4) ∷
   rw 1 (q52 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw 2 (q39 c4) ∷
   rw 3 (q40 c4) ∷
   rw 4 (q41 c4) ∷
   rw 5 (q42 c4) ∷
   rw 6 (q41 c4) ∷
   rw 7 (q43 c4) ∷
   rw 8 (q44 c4) ∷
   rw 2 (q38 c4) ∷
   rw⁻ 3 (q35 c4) ∷
   rw 3 (q35 c4) ∷
   rw⁻ 6 (q53 c4) ∷
   rw 5 (q54 c4) ∷
   rw⁻ 4 (q53 c4) ∷
   rw 3 (q54 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   rw 4 (q35 c4) ∷
   rw 7 (q36 c4) ∷
   rw 6 (q37 c4) ∷
   rw⁻ 9 (q38 c4) ∷
   rw 8 (q39 c4) ∷
   rw 9 (q40 c4) ∷
   rw 10 (q41 c4) ∷
   rw 11 (q42 c4) ∷
   rw 12 (q41 c4) ∷
   rw 13 (q43 c4) ∷
   rw 14 (q44 c4) ∷
   rw 8 (q38 c4) ∷
   rw 5 (q45 c4) ∷
   rw 7 (q46 c4) ∷
   rw⁻ 6 (q47 c4) ∷
   rw 7 (q48 c4) ∷
   rw⁻ 8 (q49 c4) ∷
   rw 9 (q48 c4) ∷
   rw⁻ 10 (q50 c4) ∷
   rw⁻ 6 (q46 c4) ∷
   rw 7 (q36 c4) ∷
   rw⁻ 5 (q51 c4) ∷
   rw 4 (q52 c4) ∷
   rw⁻ 6 (q38 c4) ∷
   rw 5 (q39 c4) ∷
   rw 6 (q40 c4) ∷
   rw 7 (q41 c4) ∷
   rw 8 (q42 c4) ∷
   rw 9 (q41 c4) ∷
   rw 10 (q43 c4) ∷
   rw 11 (q44 c4) ∷
   rw 5 (q38 c4) ∷
   rw⁻ 6 (q35 c4) ∷
   rw 6 (q35 c4) ∷
   rw⁻ 9 (q55 c4) ∷
   rw 8 (q56 c4) ∷
   rw⁻ 7 (q55 c4) ∷
   rw 6 (q56 c4) ∷
   rw⁻ 7 (q35 c4) ∷
   rw 7 (q57 c4) ∷
   rw 7 (q58 c4) ∷
   rw 10 (q59 c4) ∷
   rw 10 (q35 c4) ∷
   rw 13 (q60 c4) ∷
   rw 12 (q61 c4) ∷
   rw 11 (q60 c4) ∷
   rw 10 (q61 c4) ∷
   rw⁻ 11 (q35 c4) ∷
   rw 11 (q35 c4) ∷
   rw 14 (q60 c4) ∷
   rw 13 (q61 c4) ∷
   rw 12 (q60 c4) ∷
   rw 11 (q61 c4) ∷
   rw⁻ 12 (q35 c4) ∷
   rw 12 (q57 c4) ∷
   rw 12 (q58 c4) ∷
   rw 15 (q59 c4) ∷
   rw 15 (q35 c4) ∷
   rw⁻ 18 (q62 c4) ∷
   rw 17 (q63 c4) ∷
   rw⁻ 16 (q62 c4) ∷
   rw 15 (q63 c4) ∷
   rw⁻ 16 (q35 c4) ∷
   rw 16 (q35 c4) ∷
   rw⁻ 19 (q47 c4) ∷
   rw 18 (q43 c4) ∷
   rw⁻ 17 (q47 c4) ∷
   rw 16 (q43 c4) ∷
   rw⁻ 17 (q35 c4) ∷
   rw 0 (q64 c4) ∷
   rw 7 (q65 c4) ∷
   rw 9 (q66 c4) ∷ []) Eq.refl

private
  q67 : Ws → Eqn
  q67 c4 = sE 1524 (lem-S2-SBOX⟨0·2·43·1⟩ c4)
  q68 : Ws → Eqn
  q68 c4 = sE 1002 (lem-box-cP-at122441 c4)
  q69 : Ws → Eqn
  q69 c4 = wpE 843 c4
  q70 : Ws → Eqn
  q70 c4 = wpE 845 c4
  q71 : Ws → Eqn
  q71 c4 = wlE 241 (lit c4)
  q72 : Ws → Eqn
  q72 c4 = wpE 89 c4
  q73 : Ws → Eqn
  q73 c4 = wpE 88 c4
  q74 : Ws → Eqn
  q74 c4 = wpE 97 c4
  q75 : Ws → Eqn
  q75 c4 = wlE 245 (lit c4)
  q76 : Ws → Eqn
  q76 c4 = wpE 95 c4
  q77 : Ws → Eqn
  q77 c4 = sE 1059 (lem-comm-TOFF013-CX24 c4)
  q78 : Ws → Eqn
  q78 c4 = wpE 94 c4
  q79 : Ws → Eqn
  q79 c4 = wlE 246 (lit c4)
  q80 : Ws → Eqn
  q80 c4 = wpE 842 c4
  q81 : Ws → Eqn
  q81 c4 = wpE 90 c4
  q82 : Ws → Eqn
  q82 c4 = wlE 247 (lit c4)
  q83 : Ws → Eqn
  q83 c4 = wpE 81 c4
  q84 : Ws → Eqn
  q84 c4 = wlE 244 (lit c4)
  q85 : Ws → Eqn
  q85 c4 = wpE 87 c4
  q86 : Ws → Eqn
  q86 c4 = sE 1540 (lem-box-perm-3421-at122441 c4)
  q87 : Ws → Eqn
  q87 c4 = sE 1534 (lem-CKc-box-at13213442 c4)
  q88 : Ws → Eqn
  q88 c4 = sE 1545 (lem-box-perm-4312-at13213442 c4)
  q89 : Ws → Eqn
  q89 c4 = sE 1286 (lem-comm-TOFF013-CS24 c4)
  q90 : Ws → Eqn
  q90 c4 = wpE 909 c4
  q91 : Ws → Eqn
  q91 c4 = wpE 647 c4
  q92 : Ws → Eqn
  q92 c4 = wlE 305 (lit c4)
  q93 : Ws → Eqn
  q93 c4 = wlE 1146 (lit c4)

-- nf-X-CS0@2: 115 steps
lem-nf-X-CS0at2 : Ws → ⟪ (ℓ "侬侬侬亇乩乩亇丢乹") ⟫ʷ ≈ ⟪ (ℓ "亭乇亰亭么交亇乩乩亇交丢乹仞") ⟫ʷ
lem-nf-X-CS0at2 c4 = derive (ℓ "侬侬侬亇乩乩亇丢乹") (ℓ "亭乇亰亭么交亇乩乩亇交丢乹仞")
  (rw 0 (q67 c4) ∷
   re 1 1 (ℓ "仞亭侪亭侫") ∷
   re 3 1 (ℓ "乇") ∷
   re 5 1 (ℓ "么") ∷
   rw 1 (q68 c4) ∷
   rw 4 (q69 c4) ∷
   rw 3 (q70 c4) ∷
   rw⁻ 6 (q71 c4) ∷
   rw 5 (q72 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q9 c4) ∷
   rw 9 (q8 c4) ∷
   rw 10 (q10 c4) ∷
   rw 11 (q73 c4) ∷
   rw 5 (q71 c4) ∷
   rw 2 (q74 c4) ∷
   rw 4 (q75 c4) ∷
   rw⁻ 3 (q76 c4) ∷
   rw 4 (q77 c4) ∷
   rw⁻ 5 (q78 c4) ∷
   rw 6 (q77 c4) ∷
   rw⁻ 7 (q79 c4) ∷
   rw⁻ 3 (q75 c4) ∷
   rw 4 (q69 c4) ∷
   rw⁻ 2 (q80 c4) ∷
   rw 1 (q81 c4) ∷
   rw⁻ 3 (q71 c4) ∷
   rw 2 (q72 c4) ∷
   rw 3 (q7 c4) ∷
   rw 4 (q8 c4) ∷
   rw 5 (q9 c4) ∷
   rw 6 (q8 c4) ∷
   rw 7 (q10 c4) ∷
   rw 8 (q73 c4) ∷
   rw 2 (q71 c4) ∷
   rw⁻ 3 (q68 c4) ∷
   rw 3 (q68 c4) ∷
   rw⁻ 6 (q82 c4) ∷
   rw 5 (q83 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   rw 3 (q83 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 4 (q68 c4) ∷
   rw 7 (q69 c4) ∷
   rw 6 (q70 c4) ∷
   rw⁻ 9 (q71 c4) ∷
   rw 8 (q72 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q8 c4) ∷
   rw 11 (q9 c4) ∷
   rw 12 (q8 c4) ∷
   rw 13 (q10 c4) ∷
   rw 14 (q73 c4) ∷
   rw 8 (q71 c4) ∷
   rw 5 (q74 c4) ∷
   rw 7 (q75 c4) ∷
   rw⁻ 6 (q76 c4) ∷
   rw 7 (q77 c4) ∷
   rw⁻ 8 (q78 c4) ∷
   rw 9 (q77 c4) ∷
   rw⁻ 10 (q79 c4) ∷
   rw⁻ 6 (q75 c4) ∷
   rw 7 (q69 c4) ∷
   rw⁻ 5 (q80 c4) ∷
   rw 4 (q81 c4) ∷
   rw⁻ 6 (q71 c4) ∷
   rw 5 (q72 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q9 c4) ∷
   rw 9 (q8 c4) ∷
   rw 10 (q10 c4) ∷
   rw 11 (q73 c4) ∷
   rw 5 (q71 c4) ∷
   rw⁻ 6 (q68 c4) ∷
   rw 6 (q68 c4) ∷
   rw⁻ 9 (q84 c4) ∷
   rw 8 (q85 c4) ∷
   rw⁻ 7 (q84 c4) ∷
   rw 6 (q85 c4) ∷
   rw⁻ 7 (q68 c4) ∷
   rw 7 (q86 c4) ∷
   rw 7 (q87 c4) ∷
   rw 10 (q88 c4) ∷
   rw 10 (q68 c4) ∷
   rw 13 (q89 c4) ∷
   rw 12 (q90 c4) ∷
   rw 11 (q89 c4) ∷
   rw 10 (q90 c4) ∷
   rw⁻ 11 (q68 c4) ∷
   rw 11 (q68 c4) ∷
   rw 14 (q89 c4) ∷
   rw 13 (q90 c4) ∷
   rw 12 (q89 c4) ∷
   rw 11 (q90 c4) ∷
   rw⁻ 12 (q68 c4) ∷
   rw 12 (q86 c4) ∷
   rw 12 (q87 c4) ∷
   rw 15 (q88 c4) ∷
   rw 15 (q68 c4) ∷
   rw⁻ 18 (q91 c4) ∷
   rw 17 (q30 c4) ∷
   rw⁻ 16 (q91 c4) ∷
   rw 15 (q30 c4) ∷
   rw⁻ 16 (q68 c4) ∷
   rw 16 (q68 c4) ∷
   rw⁻ 19 (q76 c4) ∷
   rw 18 (q7 c4) ∷
   rw⁻ 17 (q76 c4) ∷
   rw 16 (q7 c4) ∷
   rw⁻ 17 (q68 c4) ∷
   rw 0 (q92 c4) ∷
   rw 7 (q93 c4) ∷
   rw 9 (q66 c4) ∷ []) Eq.refl

private
  q94 : Ws → Eqn
  q94 c4 = sE 1496 (lem-box-perm-1423-at0210243143 c4)
  q95 : Ws → Eqn
  q95 c4 = sE 1530 (lem-CKc-box-at0210233441 c4)
  q96 : Ws → Eqn
  q96 c4 = sE 1536 (lem-box-perm-1342-at0210233441 c4)
  q97 : Ws → Eqn
  q97 c4 = wpE 953 c4

-- nf-X-CS1@0: 115 steps
lem-nf-X-CS1at0 : Ws → ⟪ (ℓ "俄俄俄亄乕乕亄丢丽") ⟫ʷ ≈ ⟪ (ℓ "亮丶五亮丷亐亄乕乕亄亐丢丽伱") ⟫ʷ
lem-nf-X-CS1at0 c4 = derive (ℓ "俄俄俄亄乕乕亄丢丽") (ℓ "亮丶五亮丷亐亄乕乕亄亐丢丽伱")
  (rw 0 (q1 c4) ∷
   re 1 1 (ℓ "伱亮係亮促") ∷
   re 3 1 (ℓ "丶") ∷
   re 5 1 (ℓ "丷") ∷
   rw 1 (q2 c4) ∷
   rw 4 (q3 c4) ∷
   rw 3 (q4 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q9 c4) ∷
   rw 9 (q8 c4) ∷
   rw 10 (q10 c4) ∷
   rw 11 (q11 c4) ∷
   rw 5 (q5 c4) ∷
   rw 2 (q12 c4) ∷
   rw 4 (q13 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw 4 (q15 c4) ∷
   rw⁻ 5 (q16 c4) ∷
   rw 6 (q15 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 2 (q18 c4) ∷
   rw⁻ 1 (q19 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   rw 3 (q7 c4) ∷
   rw 4 (q8 c4) ∷
   rw 5 (q9 c4) ∷
   rw 6 (q8 c4) ∷
   rw 7 (q10 c4) ∷
   rw 8 (q11 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 6 (q20 c4) ∷
   rw 5 (q21 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw 3 (q21 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 4 (q2 c4) ∷
   rw 7 (q3 c4) ∷
   rw 6 (q4 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw 8 (q6 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q8 c4) ∷
   rw 11 (q9 c4) ∷
   rw 12 (q8 c4) ∷
   rw 13 (q10 c4) ∷
   rw 14 (q11 c4) ∷
   rw 8 (q5 c4) ∷
   rw 5 (q12 c4) ∷
   rw 7 (q13 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw 7 (q15 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   rw 9 (q15 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 5 (q18 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q9 c4) ∷
   rw 9 (q8 c4) ∷
   rw 10 (q10 c4) ∷
   rw 11 (q11 c4) ∷
   rw 5 (q5 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   rw 6 (q2 c4) ∷
   rw⁻ 9 (q22 c4) ∷
   rw 8 (q23 c4) ∷
   rw⁻ 7 (q22 c4) ∷
   rw 6 (q23 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   rw 7 (q94 c4) ∷
   rw 7 (q95 c4) ∷
   rw 10 (q96 c4) ∷
   rw 10 (q2 c4) ∷
   rw⁻ 13 (q14 c4) ∷
   rw 12 (q10 c4) ∷
   rw⁻ 11 (q14 c4) ∷
   rw 10 (q10 c4) ∷
   rw⁻ 11 (q2 c4) ∷
   rw 11 (q2 c4) ∷
   rw⁻ 14 (q14 c4) ∷
   rw 13 (q10 c4) ∷
   rw⁻ 12 (q14 c4) ∷
   rw 11 (q10 c4) ∷
   rw⁻ 12 (q2 c4) ∷
   rw 12 (q94 c4) ∷
   rw 12 (q95 c4) ∷
   rw 15 (q96 c4) ∷
   rw 15 (q2 c4) ∷
   rw⁻ 18 (q29 c4) ∷
   rw 17 (q30 c4) ∷
   rw⁻ 16 (q29 c4) ∷
   rw 15 (q30 c4) ∷
   rw⁻ 16 (q2 c4) ∷
   rw 16 (q2 c4) ∷
   rw 19 (q27 c4) ∷
   rw 18 (q28 c4) ∷
   rw 17 (q27 c4) ∷
   rw 16 (q28 c4) ∷
   rw⁻ 17 (q2 c4) ∷
   rw 0 (q31 c4) ∷
   rw 7 (q97 c4) ∷
   rw 9 (q33 c4) ∷ []) Eq.refl

private
  q98 : Ws → Eqn
  q98 c4 = sE 1497 (lem-box-perm-1423-at243243 c4)
  q99 : Ws → Eqn
  q99 c4 = sE 1535 (lem-CKc-box-at233442 c4)
  q100 : Ws → Eqn
  q100 c4 = sE 1538 (lem-box-perm-1342-at233442 c4)

-- nf-X-CS1@1: 115 steps
lem-nf-X-CS1at1 : Ws → ⟪ (ℓ "侧侧侧亇乩乩亇丢乕") ⟫ʷ ≈ ⟪ (ℓ "亲乎亨亲乏交亇乩乩亇交丢乕仄") ⟫ʷ
lem-nf-X-CS1at1 c4 = derive (ℓ "侧侧侧亇乩乩亇丢乕") (ℓ "亲乎亨亲乏交亇乩乩亇交丢乕仄")
  (rw 0 (q34 c4) ∷
   re 1 1 (ℓ "仄亲侥亲侦") ∷
   re 3 1 (ℓ "乎") ∷
   re 5 1 (ℓ "乏") ∷
   rw 1 (q35 c4) ∷
   rw 4 (q36 c4) ∷
   rw 3 (q37 c4) ∷
   rw⁻ 6 (q38 c4) ∷
   rw 5 (q39 c4) ∷
   rw 6 (q40 c4) ∷
   rw 7 (q41 c4) ∷
   rw 8 (q42 c4) ∷
   rw 9 (q41 c4) ∷
   rw 10 (q43 c4) ∷
   rw 11 (q44 c4) ∷
   rw 5 (q38 c4) ∷
   rw 2 (q45 c4) ∷
   rw 4 (q46 c4) ∷
   rw⁻ 3 (q47 c4) ∷
   rw 4 (q48 c4) ∷
   rw⁻ 5 (q49 c4) ∷
   rw 6 (q48 c4) ∷
   rw⁻ 7 (q50 c4) ∷
   rw⁻ 3 (q46 c4) ∷
   rw 4 (q36 c4) ∷
   rw⁻ 2 (q51 c4) ∷
   rw 1 (q52 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw 2 (q39 c4) ∷
   rw 3 (q40 c4) ∷
   rw 4 (q41 c4) ∷
   rw 5 (q42 c4) ∷
   rw 6 (q41 c4) ∷
   rw 7 (q43 c4) ∷
   rw 8 (q44 c4) ∷
   rw 2 (q38 c4) ∷
   rw⁻ 3 (q35 c4) ∷
   rw 3 (q35 c4) ∷
   rw⁻ 6 (q53 c4) ∷
   rw 5 (q54 c4) ∷
   rw⁻ 4 (q53 c4) ∷
   rw 3 (q54 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   rw 4 (q35 c4) ∷
   rw 7 (q36 c4) ∷
   rw 6 (q37 c4) ∷
   rw⁻ 9 (q38 c4) ∷
   rw 8 (q39 c4) ∷
   rw 9 (q40 c4) ∷
   rw 10 (q41 c4) ∷
   rw 11 (q42 c4) ∷
   rw 12 (q41 c4) ∷
   rw 13 (q43 c4) ∷
   rw 14 (q44 c4) ∷
   rw 8 (q38 c4) ∷
   rw 5 (q45 c4) ∷
   rw 7 (q46 c4) ∷
   rw⁻ 6 (q47 c4) ∷
   rw 7 (q48 c4) ∷
   rw⁻ 8 (q49 c4) ∷
   rw 9 (q48 c4) ∷
   rw⁻ 10 (q50 c4) ∷
   rw⁻ 6 (q46 c4) ∷
   rw 7 (q36 c4) ∷
   rw⁻ 5 (q51 c4) ∷
   rw 4 (q52 c4) ∷
   rw⁻ 6 (q38 c4) ∷
   rw 5 (q39 c4) ∷
   rw 6 (q40 c4) ∷
   rw 7 (q41 c4) ∷
   rw 8 (q42 c4) ∷
   rw 9 (q41 c4) ∷
   rw 10 (q43 c4) ∷
   rw 11 (q44 c4) ∷
   rw 5 (q38 c4) ∷
   rw⁻ 6 (q35 c4) ∷
   rw 6 (q35 c4) ∷
   rw⁻ 9 (q55 c4) ∷
   rw 8 (q56 c4) ∷
   rw⁻ 7 (q55 c4) ∷
   rw 6 (q56 c4) ∷
   rw⁻ 7 (q35 c4) ∷
   rw 7 (q98 c4) ∷
   rw 7 (q99 c4) ∷
   rw 10 (q100 c4) ∷
   rw 10 (q35 c4) ∷
   rw⁻ 13 (q47 c4) ∷
   rw 12 (q43 c4) ∷
   rw⁻ 11 (q47 c4) ∷
   rw 10 (q43 c4) ∷
   rw⁻ 11 (q35 c4) ∷
   rw 11 (q35 c4) ∷
   rw⁻ 14 (q47 c4) ∷
   rw 13 (q43 c4) ∷
   rw⁻ 12 (q47 c4) ∷
   rw 11 (q43 c4) ∷
   rw⁻ 12 (q35 c4) ∷
   rw 12 (q98 c4) ∷
   rw 12 (q99 c4) ∷
   rw 15 (q100 c4) ∷
   rw 15 (q35 c4) ∷
   rw⁻ 18 (q62 c4) ∷
   rw 17 (q63 c4) ∷
   rw⁻ 16 (q62 c4) ∷
   rw 15 (q63 c4) ∷
   rw⁻ 16 (q35 c4) ∷
   rw 16 (q35 c4) ∷
   rw 19 (q60 c4) ∷
   rw 18 (q61 c4) ∷
   rw 17 (q60 c4) ∷
   rw 16 (q61 c4) ∷
   rw⁻ 17 (q35 c4) ∷
   rw 0 (q64 c4) ∷
   rw 7 (q93 c4) ∷
   rw 9 (q66 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = sE 1257 (lem-box-perm-1423-at122441 c4)
  q102 : Ws → Eqn
  q102 c4 = sE 1532 (lem-CKc-box-at12213443 c4)
  q103 : Ws → Eqn
  q103 c4 = sE 1537 (lem-box-perm-1342-at12213443 c4)
  q104 : Ws → Eqn
  q104 c4 = wlE 1176 (lit c4)

-- nf-X-CS1@2: 115 steps
lem-nf-X-CS1at2 : Ws → ⟪ (ℓ "侬侬侬亊乹乹亊丢乩") ⟫ʷ ≈ ⟪ (ℓ "亭乇亰亭么交亊乹乹亊交丢乩仞") ⟫ʷ
lem-nf-X-CS1at2 c4 = derive (ℓ "侬侬侬亊乹乹亊丢乩") (ℓ "亭乇亰亭么交亊乹乹亊交丢乩仞")
  (rw 0 (q67 c4) ∷
   re 1 1 (ℓ "仞亭侪亭侫") ∷
   re 3 1 (ℓ "乇") ∷
   re 5 1 (ℓ "么") ∷
   rw 1 (q68 c4) ∷
   rw 4 (q69 c4) ∷
   rw 3 (q70 c4) ∷
   rw⁻ 6 (q71 c4) ∷
   rw 5 (q72 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q9 c4) ∷
   rw 9 (q8 c4) ∷
   rw 10 (q10 c4) ∷
   rw 11 (q73 c4) ∷
   rw 5 (q71 c4) ∷
   rw 2 (q74 c4) ∷
   rw 4 (q75 c4) ∷
   rw⁻ 3 (q76 c4) ∷
   rw 4 (q77 c4) ∷
   rw⁻ 5 (q78 c4) ∷
   rw 6 (q77 c4) ∷
   rw⁻ 7 (q79 c4) ∷
   rw⁻ 3 (q75 c4) ∷
   rw 4 (q69 c4) ∷
   rw⁻ 2 (q80 c4) ∷
   rw 1 (q81 c4) ∷
   rw⁻ 3 (q71 c4) ∷
   rw 2 (q72 c4) ∷
   rw 3 (q7 c4) ∷
   rw 4 (q8 c4) ∷
   rw 5 (q9 c4) ∷
   rw 6 (q8 c4) ∷
   rw 7 (q10 c4) ∷
   rw 8 (q73 c4) ∷
   rw 2 (q71 c4) ∷
   rw⁻ 3 (q68 c4) ∷
   rw 3 (q68 c4) ∷
   rw⁻ 6 (q82 c4) ∷
   rw 5 (q83 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   rw 3 (q83 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 4 (q68 c4) ∷
   rw 7 (q69 c4) ∷
   rw 6 (q70 c4) ∷
   rw⁻ 9 (q71 c4) ∷
   rw 8 (q72 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q8 c4) ∷
   rw 11 (q9 c4) ∷
   rw 12 (q8 c4) ∷
   rw 13 (q10 c4) ∷
   rw 14 (q73 c4) ∷
   rw 8 (q71 c4) ∷
   rw 5 (q74 c4) ∷
   rw 7 (q75 c4) ∷
   rw⁻ 6 (q76 c4) ∷
   rw 7 (q77 c4) ∷
   rw⁻ 8 (q78 c4) ∷
   rw 9 (q77 c4) ∷
   rw⁻ 10 (q79 c4) ∷
   rw⁻ 6 (q75 c4) ∷
   rw 7 (q69 c4) ∷
   rw⁻ 5 (q80 c4) ∷
   rw 4 (q81 c4) ∷
   rw⁻ 6 (q71 c4) ∷
   rw 5 (q72 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q9 c4) ∷
   rw 9 (q8 c4) ∷
   rw 10 (q10 c4) ∷
   rw 11 (q73 c4) ∷
   rw 5 (q71 c4) ∷
   rw⁻ 6 (q68 c4) ∷
   rw 6 (q68 c4) ∷
   rw⁻ 9 (q84 c4) ∷
   rw 8 (q85 c4) ∷
   rw⁻ 7 (q84 c4) ∷
   rw 6 (q85 c4) ∷
   rw⁻ 7 (q68 c4) ∷
   rw 7 (q101 c4) ∷
   rw 7 (q102 c4) ∷
   rw 10 (q103 c4) ∷
   rw 10 (q68 c4) ∷
   rw⁻ 13 (q76 c4) ∷
   rw 12 (q7 c4) ∷
   rw⁻ 11 (q76 c4) ∷
   rw 10 (q7 c4) ∷
   rw⁻ 11 (q68 c4) ∷
   rw 11 (q68 c4) ∷
   rw⁻ 14 (q76 c4) ∷
   rw 13 (q7 c4) ∷
   rw⁻ 12 (q76 c4) ∷
   rw 11 (q7 c4) ∷
   rw⁻ 12 (q68 c4) ∷
   rw 12 (q101 c4) ∷
   rw 12 (q102 c4) ∷
   rw 15 (q103 c4) ∷
   rw 15 (q68 c4) ∷
   rw⁻ 18 (q91 c4) ∷
   rw 17 (q30 c4) ∷
   rw⁻ 16 (q91 c4) ∷
   rw 15 (q30 c4) ∷
   rw⁻ 16 (q68 c4) ∷
   rw 16 (q68 c4) ∷
   rw 19 (q89 c4) ∷
   rw 18 (q90 c4) ∷
   rw 17 (q89 c4) ∷
   rw 16 (q90 c4) ∷
   rw⁻ 17 (q68 c4) ∷
   rw 0 (q92 c4) ∷
   rw 7 (q104 c4) ∷
   rw 9 (q66 c4) ∷ []) Eq.refl

private
  q105 : Ws → Eqn
  q105 c4 = sE 314 (lem-box-tQ-at143143 c4)
  q106 : Ws → Eqn
  q106 c4 = wpE 999 c4
  q107 : Ws → Eqn
  q107 c4 = wlE 1187 (lit c4)
  q108 : Ws → Eqn
  q108 c4 = wlE 1188 (lit c4)
  q109 : Ws → Eqn
  q109 c4 = wpE 886 c4
  q110 : Ws → Eqn
  q110 c4 = wlE 450 (lit c4)
  q111 : Ws → Eqn
  q111 c4 = eqn (ℓ "个亲") (ℓ "亲个") (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI))
  q112 : Ws → Eqn
  q112 c4 = wpE 1000 c4
  q113 : Ws → Eqn
  q113 c4 = wlE 868 (lit c4)
  q114 : Ws → Eqn
  q114 c4 = wpE 1001 c4
  q115 : Ws → Eqn
  q115 c4 = sE 357 (lem-box-tQ-at03143140 c4)
  q116 : Ws → Eqn
  q116 c4 = sE 1527 (lem-box-perm-1324-at03143140 c4)
  q117 : Ws → Eqn
  q117 c4 = sE 1121 (lem-box-cP-at0314213240 c4)
  q118 : Ws → Eqn
  q118 c4 = wpE 1002 c4
  q119 : Ws → Eqn
  q119 c4 = eqn (ℓ "不京") (ℓ "京不") (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q120 : Ws → Eqn
  q120 c4 = wpE 1003 c4
  q121 : Ws → Eqn
  q121 c4 = wlE 318 (lit c4)
  q122 : Ws → Eqn
  q122 c4 = sE 432 (lem-comm-CSd02-CCZ134 c4)
  q123 : Ws → Eqn
  q123 c4 = sE 431 (lem-comm-CS02-CCZ134 c4)
  q124 : Ws → Eqn
  q124 c4 = eqn (ℓ "丌京") (ℓ "京丌") (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q125 : Ws → Eqn
  q125 c4 = wpE 1004 c4
  q126 : Ws → Eqn
  q126 c4 = wlE 1189 (lit c4)
  q127 : Ws → Eqn
  q127 c4 = wlE 1190 (lit c4)
  q128 : Ws → Eqn
  q128 c4 = sE 1301 (lem-comm-CX14-TOFF302 c4)
  q129 : Ws → Eqn
  q129 c4 = wpE 1005 c4
  q130 : Ws → Eqn
  q130 c4 = wpE 1006 c4
  q131 : Ws → Eqn
  q131 c4 = wpE 1007 c4
  q132 : Ws → Eqn
  q132 c4 = wpE 1008 c4
  q133 : Ws → Eqn
  q133 c4 = wlE 645 (lit c4)
  q134 : Ws → Eqn
  q134 c4 = wpE 189 c4
  q135 : Ws → Eqn
  q135 c4 = sE 204 (lem-comm-CSd24-CCZ013 c4)
  q136 : Ws → Eqn
  q136 c4 = sE 194 (lem-comm-CS24-CCZ013 c4)
  q137 : Ws → Eqn
  q137 c4 = wpE 743 c4
  q138 : Ws → Eqn
  q138 c4 = sE 1529 (lem-box-perm-3124-at03143140 c4)
  q139 : Ws → Eqn
  q139 c4 = sE 1546 (lem-box-perm-4312-at143143 c4)
  q140 : Ws → Eqn
  q140 c4 = sE 1526 (lem-box-box-4-at03243240 c4)
  q141 : Ws → Eqn
  q141 c4 = sE 1541 (lem-box-perm-3421-at13213442 c4)
  q142 : Ws → Eqn
  q142 c4 = sE 1528 (lem-box-perm-2314-at03243240 c4)

-- F0-B @01143043: 62 steps
lem-F0-B-at01143043 : Ws → ⟪ (ℓ "为伅为") ⟫ʷ ≈ ⟪ (ℓ "伅侌") ⟫ʷ
lem-F0-B-at01143043 c4 = derive (ℓ "为伅为") (ℓ "伅侌")
  (rw 1 (q105 c4) ∷
   rw 0 (q106 c4) ∷
   rw⁻ 2 (q107 c4) ∷
   rw 4 (q106 c4) ∷
   rw⁻ 6 (q108 c4) ∷
   rw 3 (q109 c4) ∷
   rw 5 (q110 c4) ∷
   rw 4 (q111 c4) ∷
   rw⁻ 5 (q112 c4) ∷
   rw⁻ 6 (q113 c4) ∷
   rw 3 (q114 c4) ∷
   rw⁻ 4 (q33 c4) ∷
   rw⁻ 1 (q115 c4) ∷
   rw 1 (q116 c4) ∷
   rw 1 (q117 c4) ∷
   rw⁻ 0 (q118 c4) ∷
   rw 6 (q119 c4) ∷
   rw⁻ 5 (q120 c4) ∷
   rw⁻ 4 (q121 c4) ∷
   rw 3 (q122 c4) ∷
   rw⁻ 2 (q121 c4) ∷
   rw 1 (q123 c4) ∷
   rw 0 (q124 c4) ∷
   rw 1 (q118 c4) ∷
   rw 1 (q125 c4) ∷
   rw⁻ 3 (q126 c4) ∷
   rw⁻ 2 (q118 c4) ∷
   rw 8 (q119 c4) ∷
   rw⁻ 7 (q120 c4) ∷
   rw⁻ 6 (q121 c4) ∷
   rw 5 (q122 c4) ∷
   rw⁻ 4 (q121 c4) ∷
   rw 3 (q123 c4) ∷
   rw 2 (q124 c4) ∷
   rw 3 (q118 c4) ∷
   rw 5 (q46 c4) ∷
   rw 9 (q127 c4) ∷
   rw 8 (q128 c4) ∷
   rw 7 (q129 c4) ∷
   rw 6 (q128 c4) ∷
   rw 5 (q130 c4) ∷
   rw⁻ 6 (q46 c4) ∷
   rw⁻ 4 (q131 c4) ∷
   rw 3 (q125 c4) ∷
   rw 4 (q132 c4) ∷
   rw⁻ 0 (q117 c4) ∷
   rw⁻ 0 (q116 c4) ∷
   rw 2 (q46 c4) ∷
   rw⁻ 6 (q133 c4) ∷
   rw⁻ 5 (q134 c4) ∷
   rw 4 (q135 c4) ∷
   rw⁻ 3 (q134 c4) ∷
   rw 2 (q136 c4) ∷
   rw⁻ 3 (q46 c4) ∷
   rw 3 (q137 c4) ∷
   rw 4 (q64 c4) ∷
   rw⁻ 1 (q105 c4) ∷
   rw 0 (q138 c4) ∷
   rw 1 (q139 c4) ∷
   rw 0 (q140 c4) ∷
   rw 0 (q141 c4) ∷
   rw 1 (q142 c4) ∷ []) Eq.refl

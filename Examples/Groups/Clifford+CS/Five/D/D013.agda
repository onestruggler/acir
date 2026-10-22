{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD013 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D013 (Sᴰ : SD013) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-CS03-TOFF412 : Ws → St 190
  lem-comm-CS03-TOFF412 = pickᴰ 0 Sᴰ
  lem-comm-CSd03-TOFF412 : Ws → St 197
  lem-comm-CSd03-TOFF412 = pickᴰ 1 Sᴰ
  lem-comm-CSd12-TOFF403 : Ws → St 200
  lem-comm-CSd12-TOFF403 = pickᴰ 2 Sᴰ
  lem-comm-CX21-CCZ034 : Ws → St 5
  lem-comm-CX21-CCZ034 = pickᴰ 3 Sᴰ
  lem-comm-CX23-CCZ014 : Ws → St 6
  lem-comm-CX23-CCZ014 = pickᴰ 4 Sᴰ
  lem-comm-CX31-CCZ024 : Ws → St 8
  lem-comm-CX31-CCZ024 = pickᴰ 5 Sᴰ
  lem-comm-CX32-CCZ014 : Ws → St 9
  lem-comm-CX32-CCZ014 = pickᴰ 6 Sᴰ
  lem-comm-CZ03-TOFF412 : Ws → St 373
  lem-comm-CZ03-TOFF412 = pickᴰ 7 Sᴰ
  lem-comm-TOFF412-CSd03 : Ws → St 215
  lem-comm-TOFF412-CSd03 = pickᴰ 8 Sᴰ
  lem-comm-CS02-CCZ134 : Ws → St 431
  lem-comm-CS02-CCZ134 = pickᴰ 9 Sᴰ
  lem-comm-CS04-CCZ123 : Ws → St 216
  lem-comm-CS04-CCZ123 = pickᴰ 10 Sᴰ
  lem-comm-CSd02-CCZ134 : Ws → St 432
  lem-comm-CSd02-CCZ134 = pickᴰ 11 Sᴰ
  lem-comm-CSd04-CCZ123 : Ws → St 220
  lem-comm-CSd04-CCZ123 = pickᴰ 12 Sᴰ
  lem-comm-CSd23-TOFF401 : Ws → St 76
  lem-comm-CSd23-TOFF401 = pickᴰ 13 Sᴰ
  lem-comm-CZ03-TOFF214 : Ws → St 225
  lem-comm-CZ03-TOFF214 = pickᴰ 14 Sᴰ
  lem-comm-CZ12-TOFF403 : Ws → St 227
  lem-comm-CZ12-TOFF403 = pickᴰ 15 Sᴰ
  lem-comm-CZ14-TOFF203 : Ws → St 293
  lem-comm-CZ14-TOFF203 = pickᴰ 16 Sᴰ
  lem-comm-CZ14-TOFF302 : Ws → St 294
  lem-comm-CZ14-TOFF302 = pickᴰ 17 Sᴰ
  lem-comm-CSd02-TOFF413 : Ws → St 376
  lem-comm-CSd02-TOFF413 = pickᴰ 18 Sᴰ
  lem-comm-CSd13-TOFF402 : Ws → St 377
  lem-comm-CSd13-TOFF402 = pickᴰ 19 Sᴰ
  lem-comm-TOFF413-CSd02 : Ws → St 380
  lem-comm-TOFF413-CSd02 = pickᴰ 20 Sᴰ
  lem-comm-CS02-TOFF413 : Ws → St 381
  lem-comm-CS02-TOFF413 = pickᴰ 21 Sᴰ
  lem-comm-CZ02-TOFF413 : Ws → St 433
  lem-comm-CZ02-TOFF413 = pickᴰ 22 Sᴰ
  lem-comm-TOFF403-CSd12 : Ws → St 383
  lem-comm-TOFF403-CSd12 = pickᴰ 23 Sᴰ
  lem-box-tQ-at0214203143 : Ws → St 249
  lem-box-tQ-at0214203143 = pickᴰ 24 Sᴰ
  lem-box-tQ-at043043 : Ws → St 253
  lem-box-tQ-at043043 = pickᴰ 25 Sᴰ
  lem-tP-at043043 : Ws → St 272
  lem-tP-at043043 = pickᴰ 26 Sᴰ
  lem-box-tQ-at02132031 : Ws → St 396
  lem-box-tQ-at02132031 = pickᴰ 27 Sᴰ
  lem-box-tQ-at022440 : Ws → St 331
  lem-box-tQ-at022440 = pickᴰ 28 Sᴰ
  lem-box-tQ-at03122031 : Ws → St 398
  lem-box-tQ-at03122031 = pickᴰ 29 Sᴰ
  lem-box-tQ-at04122041 : Ws → St 403
  lem-box-tQ-at04122041 = pickᴰ 30 Sᴰ
  lem-tP-at02132031 : Ws → St 406
  lem-tP-at02132031 = pickᴰ 31 Sᴰ
  lem-tP-at022440 : Ws → St 334
  lem-tP-at022440 = pickᴰ 32 Sᴰ
  lem-tP-at03122031 : Ws → St 409
  lem-tP-at03122031 = pickᴰ 33 Sᴰ
  lem-tP-at04122041 : Ws → St 415
  lem-tP-at04122041 = pickᴰ 34 Sᴰ
  lem-CSdu-box-2-at04203243 : Ws → St 434
  lem-CSdu-box-2-at04203243 = pickᴰ 35 Sᴰ
  lem-Su-box-at04203243 : Ws → St 435
  lem-Su-box-at04203243 = pickᴰ 36 Sᴰ
  lem-box-tQ-at0410233142 : Ws → St 436
  lem-box-tQ-at0410233142 = pickᴰ 37 Sᴰ
  lem-box-tQ-at04122140 : Ws → St 437
  lem-box-tQ-at04122140 = pickᴰ 38 Sᴰ
  lem-box-tQ-at0412233140 : Ws → St 438
  lem-box-tQ-at0412233140 = pickᴰ 39 Sᴰ
  lem-box-tQ-at0413203241 : Ws → St 439
  lem-box-tQ-at0413203241 = pickᴰ 40 Sᴰ
  lem-box-tQ-at0413213240 : Ws → St 440
  lem-box-tQ-at0413213240 = pickᴰ 41 Sᴰ
  lem-box-tQ-at04133140 : Ws → St 441
  lem-box-tQ-at04133140 = pickᴰ 42 Sᴰ
  lem-tP-at0410233142 : Ws → St 442
  lem-tP-at0410233142 = pickᴰ 43 Sᴰ
  lem-tP-at04122140 : Ws → St 443
  lem-tP-at04122140 = pickᴰ 44 Sᴰ
  lem-tP-at0412233140 : Ws → St 444
  lem-tP-at0412233140 = pickᴰ 45 Sᴰ
  lem-tP-at0413203241 : Ws → St 445
  lem-tP-at0413203241 = pickᴰ 46 Sᴰ
  lem-tP-at0413213240 : Ws → St 446
  lem-tP-at0413213240 = pickᴰ 47 Sᴰ
  lem-tP-at0440 : Ws → St 430
  lem-tP-at0440 = pickᴰ 48 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 440 (lem-box-tQ-at0413213240 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 446 (lem-tP-at0413213240 c4)
  q3 : Ws → Eqn
  q3 c4 = wpE 1416 c4
  q4 : Ws → Eqn
  q4 c4 = wpE 1417 c4
  q5 : Ws → Eqn
  q5 c4 = sE 433 (lem-comm-CZ02-TOFF413 c4)
  q6 : Ws → Eqn
  q6 c4 = wpE 1418 c4

-- P-box @0413213240: 8 steps
lem-P-box-at0413213240 : Ws → ⟪ (Toff402 ∷ Bx4-3120 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ []) ⟫ʷ
lem-P-box-at0413213240 c4 = derive (Toff402 ∷ Bx4-3120 ∷ Toff402 ∷ []) (Bx4-3120 ∷ [])
  (rw 1 (q1 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw⁻ 0 (q1 c4) ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = wlE 1473 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = wpE 1322 c4
  q9 : Ws → Eqn
  q9 c4 = eqn (CS02⁻ ∷ S4⁻ ∷ []) (S4⁻ ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) ((S • S • S) ↑))
  q10 : Ws → Eqn
  q10 c4 = sE 380 (lem-comm-TOFF413-CSd02 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CS02⁻ ∷ S4 ∷ []) (S4 ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S ↑))
  q12 : Ws → Eqn
  q12 c4 = wlE 901 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = wlE 456 (lit c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (CS13⁻ ∷ S4 ∷ []) (S4 ∷ CS13⁻ ∷ []) (c₄ (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) (S))
  q15 : Ws → Eqn
  q15 c4 = sE 377 (lem-comm-CSd13-TOFF402 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CS13⁻ ∷ S4⁻ ∷ []) (S4⁻ ∷ CS13⁻ ∷ []) (c₄ (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) (S • S • S))

-- VPQ @0413213240: 14 steps
lem-VPQ-at0413213240 : Ws → ⟪ (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ []) ⟫ʷ
lem-VPQ-at0413213240 c4 = derive (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ []) (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   rw⁻ 3 (q9 c4) ∷
   rw 2 (q10 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw⁻ 0 (q12 c4) ∷
   rw 4 (q13 c4) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw 1 (q14 c4) ∷
   rw 2 (q15 c4) ∷
   rw 3 (q16 c4) ∷
   rw 0 (q8 c4) ∷
   rw 2 (q7 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = sE 249 (lem-box-tQ-at0214203143 c4)
  q18 : Ws → Eqn
  q18 c4 = wpE 1429 c4
  q19 : Ws → Eqn
  q19 c4 = wpE 75 c4
  q20 : Ws → Eqn
  q20 c4 = wlE 171 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = wlE 406 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = sE 220 (lem-comm-CSd04-CCZ123 c4)
  q23 : Ws → Eqn
  q23 c4 = sE 216 (lem-comm-CS04-CCZ123 c4)
  q24 : Ws → Eqn
  q24 c4 = wpE 28 c4
  q25 : Ws → Eqn
  q25 c4 = wpE 454 c4
  q26 : Ws → Eqn
  q26 c4 = wpE 1430 c4

-- CSu-box-2 @0214203143: 17 steps
lem-CSu-box-2-at0214203143 : Ws → ⟪ (CS02 ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CS02 ∷ []) ⟫ʷ
lem-CSu-box-2-at0214203143 c4 = derive (CS02 ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ CS02 ∷ [])
  (rw 1 (q17 c4) ∷
   rw 0 (q18 c4) ∷
   rw 3 (q19 c4) ∷
   rw⁻ 7 (q20 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw 5 (q22 c4) ∷
   rw⁻ 4 (q21 c4) ∷
   rw 3 (q23 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw 2 (q23 c4) ∷
   rw⁻ 1 (q20 c4) ∷
   rw 4 (q24 c4) ∷
   rw 3 (q25 c4) ∷
   rw 2 (q18 c4) ∷
   rw 3 (q26 c4) ∷
   rw⁻ 3 (q20 c4) ∷
   rw⁻ 0 (q17 c4) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = sE 438 (lem-box-tQ-at0412233140 c4)
  q28 : Ws → Eqn
  q28 c4 = wlE 1507 (lit c4)
  q29 : Ws → Eqn
  q29 c4 = wpE 792 c4
  q30 : Ws → Eqn
  q30 c4 = wpE 1365 c4
  q31 : Ws → Eqn
  q31 c4 = wlE 307 (lit c4)
  q32 : Ws → Eqn
  q32 c4 = wpE 155 c4
  q33 : Ws → Eqn
  q33 c4 = sE 6 (lem-comm-CX23-CCZ014 c4)
  q34 : Ws → Eqn
  q34 c4 = wpE 156 c4
  q35 : Ws → Eqn
  q35 c4 = wpE 157 c4
  q36 : Ws → Eqn
  q36 c4 = wpE 124 c4
  q37 : Ws → Eqn
  q37 c4 = wpE 794 c4
  q38 : Ws → Eqn
  q38 c4 = wlE 1661 (lit c4)

-- CXbc-box @0412233140: 17 steps
lem-CXbc-box-at0412233140 : Ws → ⟪ (CX31 ∷ Bx4-2310 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2310 ∷ CCZ023 ∷ []) ⟫ʷ
lem-CXbc-box-at0412233140 c4 = derive (CX31 ∷ Bx4-2310 ∷ CX31 ∷ []) (Bx4-2310 ∷ CCZ023 ∷ [])
  (rw 1 (q27 c4) ∷
   rw 0 (q28 c4) ∷
   rw⁻ 1 (q29 c4) ∷
   rw 3 (q30 c4) ∷
   rw 2 (q28 c4) ∷
   rw 5 (q31 c4) ∷
   rw⁻ 9 (q32 c4) ∷
   rw 8 (q33 c4) ∷
   rw⁻ 7 (q34 c4) ∷
   rw 6 (q33 c4) ∷
   rw⁻ 5 (q35 c4) ∷
   rw⁻ 6 (q31 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   rw⁻ 3 (q29 c4) ∷
   rw 4 (q37 c4) ∷
   rw⁻ 0 (q27 c4) ∷
   rw⁻ 1 (q38 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = wlE 1662 (lit c4)
  q40 : Ws → Eqn
  q40 c4 = wpE 376 c4
  q41 : Ws → Eqn
  q41 c4 = wpE 795 c4
  q42 : Ws → Eqn
  q42 c4 = wlE 270 (lit c4)
  q43 : Ws → Eqn
  q43 c4 = wpE 311 c4
  q44 : Ws → Eqn
  q44 c4 = wlE 1663 (lit c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (CS01⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toffᵗ))
  q46 : Ws → Eqn
  q46 c4 = eqn (CS01 ∷ Toff423 ∷ []) (Toff423 ∷ CS01 ∷ []) (c₂ (CS) (Toffᵗ))
  q47 : Ws → Eqn
  q47 c4 = wlE 516 (lit c4)
  q48 : Ws → Eqn
  q48 c4 = wlE 1664 (lit c4)
  q49 : Ws → Eqn
  q49 c4 = wpE 167 c4
  q50 : Ws → Eqn
  q50 c4 = wlE 1665 (lit c4)

-- CXcb-box @0412233140: 18 steps
lem-CXcb-box-at0412233140 : Ws → ⟪ (CX13 ∷ Bx4-2310 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2310 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXcb-box-at0412233140 c4 = derive (CX13 ∷ Bx4-2310 ∷ CX13 ∷ []) (Bx4-2310 ∷ CCZ012 ∷ [])
  (rw 1 (q27 c4) ∷
   rw 0 (q39 c4) ∷
   rw⁻ 2 (q40 c4) ∷
   rw⁻ 1 (q41 c4) ∷
   rw 4 (q42 c4) ∷
   rw 8 (q43 c4) ∷
   rw 7 (q44 c4) ∷
   rw 6 (q45 c4) ∷
   rw 5 (q44 c4) ∷
   rw 4 (q46 c4) ∷
   rw⁻ 5 (q42 c4) ∷
   rw 3 (q47 c4) ∷
   rw 2 (q39 c4) ∷
   rw 3 (q48 c4) ∷
   rw 4 (q49 c4) ∷
   rw⁻ 3 (q41 c4) ∷
   rw⁻ 0 (q27 c4) ∷
   rw⁻ 1 (q50 c4) ∷ []) Eq.refl

private
  q51 : Ws → Eqn
  q51 c4 = sE 436 (lem-box-tQ-at0410233142 c4)
  q52 : Ws → Eqn
  q52 c4 = sE 442 (lem-tP-at0410233142 c4)
  q53 : Ws → Eqn
  q53 c4 = wlE 1569 (lit c4)
  q54 : Ws → Eqn
  q54 c4 = wlE 1570 (lit c4)
  q55 : Ws → Eqn
  q55 c4 = sE 227 (lem-comm-CZ12-TOFF403 c4)
  q56 : Ws → Eqn
  q56 c4 = wlE 1571 (lit c4)

-- P-box @0410233142: 8 steps
lem-P-box-at0410233142 : Ws → ⟪ (Toff412 ∷ Bx4-0312 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ []) ⟫ʷ
lem-P-box-at0410233142 c4 = derive (Toff412 ∷ Bx4-0312 ∷ Toff412 ∷ []) (Bx4-0312 ∷ [])
  (rw 1 (q51 c4) ∷
   rw⁻ 0 (q52 c4) ∷
   rw⁻ 1 (q53 c4) ∷
   rw⁻ 3 (q52 c4) ∷
   rw⁻ 4 (q54 c4) ∷
   rw 2 (q55 c4) ∷
   rw⁻ 3 (q56 c4) ∷
   rw⁻ 0 (q51 c4) ∷ []) Eq.refl

private
  q57 : Ws → Eqn
  q57 c4 = wpE 316 c4
  q58 : Ws → Eqn
  q58 c4 = wlE 468 (lit c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (CS12⁻ ∷ S4⁻ ∷ []) (S4⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) ((S • S • S) ↑))
  q60 : Ws → Eqn
  q60 c4 = sE 383 (lem-comm-TOFF403-CSd12 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (CS12⁻ ∷ S4 ∷ []) (S4 ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S ↑))
  q62 : Ws → Eqn
  q62 c4 = wlE 469 (lit c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (CS03⁻ ∷ S4 ∷ []) (S4 ∷ CS03⁻ ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S))
  q64 : Ws → Eqn
  q64 c4 = sE 197 (lem-comm-CSd03-TOFF412 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (CS03⁻ ∷ S4⁻ ∷ []) (S4⁻ ∷ CS03⁻ ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S • S • S))

-- VPQ @0410233142: 14 steps
lem-VPQ-at0410233142 : Ws → ⟪ (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at0410233142 c4 = derive (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q57 c4) ∷
   rw⁻ 4 (q58 c4) ∷
   rw⁻ 3 (q59 c4) ∷
   rw 2 (q60 c4) ∷
   rw⁻ 1 (q61 c4) ∷
   rw 0 (q62 c4) ∷
   rw 4 (q13 c4) ∷
   rw 3 (q52 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw 1 (q63 c4) ∷
   rw 2 (q64 c4) ∷
   rw 3 (q65 c4) ∷
   rw 0 (q58 c4) ∷
   rw 2 (q57 c4) ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = sE 253 (lem-box-tQ-at043043 c4)
  q67 : Ws → Eqn
  q67 c4 = sE 272 (lem-tP-at043043 c4)
  q68 : Ws → Eqn
  q68 c4 = wpE 1399 c4
  q69 : Ws → Eqn
  q69 c4 = wpE 1400 c4
  q70 : Ws → Eqn
  q70 c4 = sE 373 (lem-comm-CZ03-TOFF412 c4)
  q71 : Ws → Eqn
  q71 c4 = wpE 375 c4

-- P-box @043043: 8 steps
lem-P-box-at043043 : Ws → ⟪ (Toff403 ∷ Bx4-1203 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-P-box-at043043 c4 = derive (Toff403 ∷ Bx4-1203 ∷ Toff403 ∷ []) (Bx4-1203 ∷ [])
  (rw 1 (q66 c4) ∷
   rw⁻ 0 (q67 c4) ∷
   rw⁻ 1 (q68 c4) ∷
   rw⁻ 3 (q67 c4) ∷
   rw⁻ 4 (q69 c4) ∷
   rw 2 (q70 c4) ∷
   rw⁻ 3 (q71 c4) ∷
   rw⁻ 0 (q66 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = sE 437 (lem-box-tQ-at04122140 c4)
  q73 : Ws → Eqn
  q73 c4 = wlE 1611 (lit c4)
  q74 : Ws → Eqn
  q74 c4 = wpE 121 c4
  q75 : Ws → Eqn
  q75 c4 = wpE 1439 c4
  q76 : Ws → Eqn
  q76 c4 = wpE 3 c4
  q77 : Ws → Eqn
  q77 c4 = sE 5 (lem-comm-CX21-CCZ034 c4)
  q78 : Ws → Eqn
  q78 c4 = wpE 120 c4
  q79 : Ws → Eqn
  q79 c4 = wpE 1 c4
  q80 : Ws → Eqn
  q80 c4 = wpE 125 c4

-- CXbc-box @04122140: 17 steps
lem-CXbc-box-at04122140 : Ws → ⟪ (CX13 ∷ Bx4-2130 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at04122140 c4 = derive (CX13 ∷ Bx4-2130 ∷ CX13 ∷ []) (Bx4-2130 ∷ CCZ012 ∷ [])
  (rw 1 (q72 c4) ∷
   rw 0 (q73 c4) ∷
   rw⁻ 1 (q74 c4) ∷
   rw 3 (q75 c4) ∷
   rw 2 (q73 c4) ∷
   rw 5 (q42 c4) ∷
   rw⁻ 9 (q76 c4) ∷
   rw 8 (q77 c4) ∷
   rw⁻ 7 (q78 c4) ∷
   rw 6 (q77 c4) ∷
   rw⁻ 5 (q79 c4) ∷
   rw⁻ 6 (q42 c4) ∷
   rw 4 (q36 c4) ∷
   rw⁻ 3 (q74 c4) ∷
   rw 4 (q80 c4) ∷
   rw⁻ 0 (q72 c4) ∷
   rw⁻ 1 (q50 c4) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = wlE 1677 (lit c4)
  q82 : Ws → Eqn
  q82 c4 = wpE 1440 c4
  q83 : Ws → Eqn
  q83 c4 = wpE 127 c4
  q84 : Ws → Eqn
  q84 c4 = wpE 1441 c4
  q85 : Ws → Eqn
  q85 c4 = wlE 1609 (lit c4)
  q86 : Ws → Eqn
  q86 c4 = sE 190 (lem-comm-CS03-TOFF412 c4)
  q87 : Ws → Eqn
  q87 c4 = wlE 1678 (lit c4)
  q88 : Ws → Eqn
  q88 c4 = wpE 575 c4

-- CXcb-box @04122140: 18 steps
lem-CXcb-box-at04122140 : Ws → ⟪ (CX31 ∷ Bx4-2130 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ CCZ023 ∷ []) ⟫ʷ
lem-CXcb-box-at04122140 c4 = derive (CX31 ∷ Bx4-2130 ∷ CX31 ∷ []) (Bx4-2130 ∷ CCZ023 ∷ [])
  (rw 1 (q72 c4) ∷
   rw 0 (q81 c4) ∷
   rw⁻ 2 (q82 c4) ∷
   rw⁻ 1 (q83 c4) ∷
   rw 4 (q31 c4) ∷
   rw 8 (q84 c4) ∷
   rw 7 (q85 c4) ∷
   rw 6 (q64 c4) ∷
   rw 5 (q85 c4) ∷
   rw 4 (q86 c4) ∷
   rw⁻ 5 (q31 c4) ∷
   rw⁻ 3 (q47 c4) ∷
   rw 2 (q81 c4) ∷
   rw 3 (q87 c4) ∷
   rw 4 (q88 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   rw⁻ 0 (q72 c4) ∷
   rw⁻ 1 (q38 c4) ∷ []) Eq.refl

private
  q89 : Ws → Eqn
  q89 c4 = sE 444 (lem-tP-at0412233140 c4)
  q90 : Ws → Eqn
  q90 c4 = wpE 1338 c4
  q91 : Ws → Eqn
  q91 c4 = wpE 1339 c4
  q92 : Ws → Eqn
  q92 c4 = eqn (CZ01 ∷ Toff423 ∷ []) (Toff423 ∷ CZ01 ∷ []) (c₂ (CZ) (Toffᵗ))
  q93 : Ws → Eqn
  q93 c4 = wpE 1340 c4

-- P-box @0412233140: 8 steps
lem-P-box-at0412233140 : Ws → ⟪ (Toff401 ∷ Bx4-2310 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2310 ∷ []) ⟫ʷ
lem-P-box-at0412233140 c4 = derive (Toff401 ∷ Bx4-2310 ∷ Toff401 ∷ []) (Bx4-2310 ∷ [])
  (rw 1 (q27 c4) ∷
   rw⁻ 0 (q89 c4) ∷
   rw⁻ 1 (q90 c4) ∷
   rw⁻ 3 (q89 c4) ∷
   rw⁻ 4 (q91 c4) ∷
   rw 2 (q92 c4) ∷
   rw⁻ 3 (q93 c4) ∷
   rw⁻ 0 (q27 c4) ∷ []) Eq.refl

private
  q94 : Ws → Eqn
  q94 c4 = wlE 455 (lit c4)
  q95 : Ws → Eqn
  q95 c4 = wpE 304 c4
  q96 : Ws → Eqn
  q96 c4 = eqn (CS01⁻ ∷ S4⁻ ∷ []) (S4⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((S • S • S) ↑ ↑))
  q97 : Ws → Eqn
  q97 c4 = eqn (CS01⁻ ∷ S4 ∷ []) (S4 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S ↑ ↑))
  q98 : Ws → Eqn
  q98 c4 = eqn (CS01⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CS • CS • CS))
  q99 : Ws → Eqn
  q99 c4 = eqn (CS23⁻ ∷ S4 ∷ []) (S4 ∷ CS23⁻ ∷ []) (c₄ ((CS • CS • CS) ↑ ↑) (S))
  q100 : Ws → Eqn
  q100 c4 = sE 76 (lem-comm-CSd23-TOFF401 c4)
  q101 : Ws → Eqn
  q101 c4 = eqn (CS23⁻ ∷ S4⁻ ∷ []) (S4⁻ ∷ CS23⁻ ∷ []) (c₄ ((CS • CS • CS) ↑ ↑) (S • S • S))

-- VPQ @0412233140: 14 steps
lem-VPQ-at0412233140 : Ws → ⟪ (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at0412233140 c4 = derive (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ []) (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ [])
  (rw⁻ 0 (q94 c4) ∷
   rw⁻ 4 (q95 c4) ∷
   rw⁻ 3 (q96 c4) ∷
   rw⁻ 2 (q45 c4) ∷
   rw⁻ 1 (q97 c4) ∷
   rw⁻ 0 (q98 c4) ∷
   rw 4 (q13 c4) ∷
   rw 3 (q89 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw 1 (q99 c4) ∷
   rw 2 (q100 c4) ∷
   rw 3 (q101 c4) ∷
   rw 0 (q95 c4) ∷
   rw 2 (q94 c4) ∷ []) Eq.refl

private
  q102 : Ws → Eqn
  q102 c4 = wpE 1458 c4
  q103 : Ws → Eqn
  q103 c4 = sE 415 (lem-tP-at04122041 c4)
  q104 : Ws → Eqn
  q104 c4 = wpE 1459 c4

-- t-cP @04122041: 5 steps
lem-t-cP-at04122041 : Ws → ⟪ (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff402 ∷ []) ⟫ʷ
lem-t-cP-at04122041 c4 = derive (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff402 ∷ [])
  (rw⁻ 0 (q102 c4) ∷
   rw 2 (q5 c4) ∷
   rw 1 (q103 c4) ∷
   rw⁻ 2 (q104 c4) ∷
   rw 3 (q103 c4) ∷ []) Eq.refl

private
  q105 : Ws → Eqn
  q105 c4 = wlE 532 (lit c4)
  q106 : Ws → Eqn
  q106 c4 = sE 430 (lem-tP-at0440 c4)
  q107 : Ws → Eqn
  q107 c4 = wlE 533 (lit c4)

-- t-cP @0440: 5 steps
lem-t-cP-at0440 : Ws → ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ Toff412 ∷ []) ⟫ʷ
lem-t-cP-at0440 c4 = derive (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ Toff412 ∷ [])
  (rw⁻ 0 (q105 c4) ∷
   rw 2 (q55 c4) ∷
   rw 1 (q106 c4) ∷
   rw⁻ 2 (q107 c4) ∷
   rw 3 (q106 c4) ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = sE 403 (lem-box-tQ-at04122041 c4)
  q109 : Ws → Eqn
  q109 c4 = wpE 1470 c4
  q110 : Ws → Eqn
  q110 c4 = wpE 213 c4
  q111 : Ws → Eqn
  q111 c4 = wpE 1003 c4
  q112 : Ws → Eqn
  q112 c4 = wlE 318 (lit c4)
  q113 : Ws → Eqn
  q113 c4 = sE 432 (lem-comm-CSd02-CCZ134 c4)
  q114 : Ws → Eqn
  q114 c4 = sE 431 (lem-comm-CS02-CCZ134 c4)
  q115 : Ws → Eqn
  q115 c4 = wpE 1206 c4
  q116 : Ws → Eqn
  q116 c4 = wpE 1471 c4
  q117 : Ws → Eqn
  q117 c4 = wpE 1472 c4

-- CSdu-box-2 @04122041: 17 steps
lem-CSdu-box-2-at04122041 : Ws → ⟪ (CS04⁻ ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-CSdu-box-2-at04122041 c4 = derive (CS04⁻ ∷ Bx4-2031 ∷ []) (Bx4-2031 ∷ CS04⁻ ∷ [])
  (rw 1 (q108 c4) ∷
   rw 0 (q109 c4) ∷
   rw 3 (q110 c4) ∷
   rw⁻ 7 (q111 c4) ∷
   rw⁻ 6 (q112 c4) ∷
   rw 5 (q113 c4) ∷
   rw⁻ 4 (q112 c4) ∷
   rw 3 (q114 c4) ∷
   rw⁻ 4 (q110 c4) ∷
   rw 2 (q113 c4) ∷
   rw⁻ 1 (q115 c4) ∷
   rw 4 (q104 c4) ∷
   rw 3 (q116 c4) ∷
   rw 2 (q109 c4) ∷
   rw 3 (q117 c4) ∷
   rw⁻ 3 (q115 c4) ∷
   rw⁻ 0 (q108 c4) ∷ []) Eq.refl

private
  q118 : Ws → Eqn
  q118 c4 = wpE 1473 c4
  q119 : Ws → Eqn
  q119 c4 = wlE 1249 (lit c4)
  q120 : Ws → Eqn
  q120 c4 = wpE 1474 c4
  q121 : Ws → Eqn
  q121 c4 = wpE 1475 c4

-- Su-box @04122041: 17 steps
lem-Su-box-at04122041 : Ws → ⟪ (S4 ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ S4 ∷ []) ⟫ʷ
lem-Su-box-at04122041 c4 = derive (S4 ∷ Bx4-2031 ∷ []) (Bx4-2031 ∷ S4 ∷ [])
  (rw 1 (q108 c4) ∷
   rw 0 (q118 c4) ∷
   rw 3 (q110 c4) ∷
   rw⁻ 7 (q111 c4) ∷
   rw⁻ 6 (q112 c4) ∷
   rw 5 (q113 c4) ∷
   rw⁻ 4 (q112 c4) ∷
   rw 3 (q114 c4) ∷
   rw⁻ 4 (q110 c4) ∷
   rw 2 (q114 c4) ∷
   rw⁻ 1 (q119 c4) ∷
   rw 4 (q104 c4) ∷
   rw 3 (q120 c4) ∷
   rw 2 (q118 c4) ∷
   rw 3 (q121 c4) ∷
   rw⁻ 3 (q119 c4) ∷
   rw⁻ 0 (q108 c4) ∷ []) Eq.refl

private
  q122 : Ws → Eqn
  q122 c4 = sE 439 (lem-box-tQ-at0413203241 c4)
  q123 : Ws → Eqn
  q123 c4 = sE 445 (lem-tP-at0413203241 c4)

-- P-box @0413203241: 8 steps
lem-P-box-at0413203241 : Ws → ⟪ (Toff412 ∷ Bx4-3021 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3021 ∷ []) ⟫ʷ
lem-P-box-at0413203241 c4 = derive (Toff412 ∷ Bx4-3021 ∷ Toff412 ∷ []) (Bx4-3021 ∷ [])
  (rw 1 (q122 c4) ∷
   rw⁻ 0 (q123 c4) ∷
   rw⁻ 1 (q53 c4) ∷
   rw⁻ 3 (q123 c4) ∷
   rw⁻ 4 (q54 c4) ∷
   rw 2 (q55 c4) ∷
   rw⁻ 3 (q56 c4) ∷
   rw⁻ 0 (q122 c4) ∷ []) Eq.refl

-- VPQ @0413203241: 14 steps
lem-VPQ-at0413203241 : Ws → ⟪ (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at0413203241 c4 = derive (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q57 c4) ∷
   rw⁻ 4 (q58 c4) ∷
   rw⁻ 3 (q59 c4) ∷
   rw 2 (q60 c4) ∷
   rw⁻ 1 (q61 c4) ∷
   rw 0 (q62 c4) ∷
   rw 4 (q13 c4) ∷
   rw 3 (q123 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw 1 (q63 c4) ∷
   rw 2 (q64 c4) ∷
   rw 3 (q65 c4) ∷
   rw 0 (q58 c4) ∷
   rw 2 (q57 c4) ∷ []) Eq.refl

private
  q124 : Ws → Eqn
  q124 c4 = sE 331 (lem-box-tQ-at022440 c4)
  q125 : Ws → Eqn
  q125 c4 = sE 334 (lem-tP-at022440 c4)
  q126 : Ws → Eqn
  q126 c4 = wlE 626 (lit c4)
  q127 : Ws → Eqn
  q127 c4 = wlE 627 (lit c4)
  q128 : Ws → Eqn
  q128 c4 = sE 225 (lem-comm-CZ03-TOFF214 c4)
  q129 : Ws → Eqn
  q129 c4 = wlE 628 (lit c4)

-- P-box @022440: 8 steps
lem-P-box-at022440 : Ws → ⟪ (Toff203 ∷ Bx2-1430 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ []) ⟫ʷ
lem-P-box-at022440 c4 = derive (Toff203 ∷ Bx2-1430 ∷ Toff203 ∷ []) (Bx2-1430 ∷ [])
  (rw 1 (q124 c4) ∷
   rw⁻ 0 (q125 c4) ∷
   rw⁻ 1 (q126 c4) ∷
   rw⁻ 3 (q125 c4) ∷
   rw⁻ 4 (q127 c4) ∷
   rw 2 (q128 c4) ∷
   rw⁻ 3 (q129 c4) ∷
   rw⁻ 0 (q124 c4) ∷ []) Eq.refl

private
  q130 : Ws → Eqn
  q130 c4 = sE 215 (lem-comm-TOFF412-CSd03 c4)
  q131 : Ws → Eqn
  q131 c4 = sE 443 (lem-tP-at04122140 c4)
  q132 : Ws → Eqn
  q132 c4 = sE 200 (lem-comm-CSd12-TOFF403 c4)

-- VPQ @04122140: 14 steps
lem-VPQ-at04122140 : Ws → ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) ⟫ʷ
lem-VPQ-at04122140 c4 = derive (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q58 c4) ∷
   rw⁻ 4 (q57 c4) ∷
   rw⁻ 3 (q65 c4) ∷
   rw 2 (q130 c4) ∷
   rw⁻ 1 (q63 c4) ∷
   rw⁻ 0 (q62 c4) ∷
   rw 4 (q13 c4) ∷
   rw 3 (q131 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw 1 (q61 c4) ∷
   rw 2 (q132 c4) ∷
   rw 3 (q59 c4) ∷
   rw 0 (q57 c4) ∷
   rw 2 (q58 c4) ∷ []) Eq.refl

private
  q133 : Ws → Eqn
  q133 c4 = sE 396 (lem-box-tQ-at02132031 c4)
  q134 : Ws → Eqn
  q134 c4 = sE 406 (lem-tP-at02132031 c4)
  q135 : Ws → Eqn
  q135 c4 = wlE 766 (lit c4)
  q136 : Ws → Eqn
  q136 c4 = wlE 767 (lit c4)
  q137 : Ws → Eqn
  q137 c4 = sE 293 (lem-comm-CZ14-TOFF203 c4)
  q138 : Ws → Eqn
  q138 c4 = wlE 768 (lit c4)

-- P-box @02132031: 8 steps
lem-P-box-at02132031 : Ws → ⟪ (Toff214 ∷ Bx2-3014 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-P-box-at02132031 c4 = derive (Toff214 ∷ Bx2-3014 ∷ Toff214 ∷ []) (Bx2-3014 ∷ [])
  (rw 1 (q133 c4) ∷
   rw⁻ 0 (q134 c4) ∷
   rw⁻ 1 (q135 c4) ∷
   rw⁻ 3 (q134 c4) ∷
   rw⁻ 4 (q136 c4) ∷
   rw 2 (q137 c4) ∷
   rw⁻ 3 (q138 c4) ∷
   rw⁻ 0 (q133 c4) ∷ []) Eq.refl

private
  q139 : Ws → Eqn
  q139 c4 = wpE 1489 c4
  q140 : Ws → Eqn
  q140 c4 = wlE 611 (lit c4)
  q141 : Ws → Eqn
  q141 c4 = wpE 451 c4
  q142 : Ws → Eqn
  q142 c4 = wpE 1490 c4

-- CSdu-box-2 @0214203143: 17 steps
lem-CSdu-box-2-at0214203143 : Ws → ⟪ (CS02⁻ ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-CSdu-box-2-at0214203143 c4 = derive (CS02⁻ ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ CS02⁻ ∷ [])
  (rw 1 (q17 c4) ∷
   rw 0 (q139 c4) ∷
   rw 3 (q19 c4) ∷
   rw⁻ 7 (q20 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw 5 (q22 c4) ∷
   rw⁻ 4 (q21 c4) ∷
   rw 3 (q23 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw 2 (q22 c4) ∷
   rw⁻ 1 (q140 c4) ∷
   rw 4 (q24 c4) ∷
   rw 3 (q141 c4) ∷
   rw 2 (q139 c4) ∷
   rw 3 (q142 c4) ∷
   rw⁻ 3 (q140 c4) ∷
   rw⁻ 0 (q17 c4) ∷ []) Eq.refl

private
  q143 : Ws → Eqn
  q143 c4 = wpE 1281 c4
  q144 : Ws → Eqn
  q144 c4 = sE 434 (lem-CSdu-box-2-at04203243 c4)
  q145 : Ws → Eqn
  q145 c4 = sE 435 (lem-Su-box-at04203243 c4)

-- XCSX-box-2 @04203243: 4 steps
lem-XCSX-box-2-at04203243 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-XCSX-box-2-at04203243 c4 = derive (X0 ∷ CS04 ∷ X0 ∷ Bx4-1023 ∷ []) (Bx4-1023 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  (rw⁻ 0 (q143 c4) ∷
   rw 1 (q144 c4) ∷
   rw 0 (q145 c4) ∷
   rw 1 (q143 c4) ∷ []) Eq.refl

private
  q146 : Ws → Eqn
  q146 c4 = sE 441 (lem-box-tQ-at04133140 c4)
  q147 : Ws → Eqn
  q147 c4 = wpE 720 c4
  q148 : Ws → Eqn
  q148 c4 = wpE 1504 c4
  q149 : Ws → Eqn
  q149 c4 = wlE 343 (lit c4)
  q150 : Ws → Eqn
  q150 c4 = sE 9 (lem-comm-CX32-CCZ014 c4)
  q151 : Ws → Eqn
  q151 c4 = wpE 215 c4
  q152 : Ws → Eqn
  q152 c4 = wpE 38 c4
  q153 : Ws → Eqn
  q153 c4 = wpE 723 c4
  q154 : Ws → Eqn
  q154 c4 = wlE 1478 (lit c4)

-- CXbc-box @04133140: 17 steps
lem-CXbc-box-at04133140 : Ws → ⟪ (CX21 ∷ Bx4-3210 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3210 ∷ CCZ023 ∷ []) ⟫ʷ
lem-CXbc-box-at04133140 c4 = derive (CX21 ∷ Bx4-3210 ∷ CX21 ∷ []) (Bx4-3210 ∷ CCZ023 ∷ [])
  (rw 1 (q146 c4) ∷
   rw 0 (q44 c4) ∷
   rw⁻ 1 (q147 c4) ∷
   rw 3 (q148 c4) ∷
   rw 2 (q44 c4) ∷
   rw 5 (q149 c4) ∷
   rw⁻ 9 (q35 c4) ∷
   rw 8 (q150 c4) ∷
   rw⁻ 7 (q151 c4) ∷
   rw 6 (q150 c4) ∷
   rw⁻ 5 (q32 c4) ∷
   rw⁻ 6 (q149 c4) ∷
   rw⁻ 4 (q152 c4) ∷
   rw⁻ 3 (q147 c4) ∷
   rw 4 (q153 c4) ∷
   rw⁻ 0 (q146 c4) ∷
   rw⁻ 1 (q154 c4) ∷ []) Eq.refl

private
  q155 : Ws → Eqn
  q155 c4 = wlE 1726 (lit c4)
  q156 : Ws → Eqn
  q156 c4 = wpE 1505 c4
  q157 : Ws → Eqn
  q157 c4 = wpE 54 c4
  q158 : Ws → Eqn
  q158 c4 = wlE 323 (lit c4)
  q159 : Ws → Eqn
  q159 c4 = wpE 1347 c4
  q160 : Ws → Eqn
  q160 c4 = wlE 1727 (lit c4)
  q161 : Ws → Eqn
  q161 c4 = wlE 1728 (lit c4)
  q162 : Ws → Eqn
  q162 c4 = wpE 394 c4
  q163 : Ws → Eqn
  q163 c4 = wlE 1477 (lit c4)

-- CXcb-box @04133140: 18 steps
lem-CXcb-box-at04133140 : Ws → ⟪ (CX12 ∷ Bx4-3210 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3210 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at04133140 c4 = derive (CX12 ∷ Bx4-3210 ∷ CX12 ∷ []) (Bx4-3210 ∷ CCZ013 ∷ [])
  (rw 1 (q146 c4) ∷
   rw 0 (q155 c4) ∷
   rw⁻ 2 (q156 c4) ∷
   rw⁻ 1 (q157 c4) ∷
   rw 4 (q158 c4) ∷
   rw 8 (q159 c4) ∷
   rw 7 (q28 c4) ∷
   rw 6 (q45 c4) ∷
   rw 5 (q28 c4) ∷
   rw 4 (q46 c4) ∷
   rw⁻ 5 (q158 c4) ∷
   rw 3 (q160 c4) ∷
   rw 2 (q155 c4) ∷
   rw 3 (q161 c4) ∷
   rw 4 (q162 c4) ∷
   rw⁻ 3 (q157 c4) ∷
   rw⁻ 0 (q146 c4) ∷
   rw⁻ 1 (q163 c4) ∷ []) Eq.refl

private
  q164 : Ws → Eqn
  q164 c4 = sE 398 (lem-box-tQ-at03122031 c4)
  q165 : Ws → Eqn
  q165 c4 = sE 409 (lem-tP-at03122031 c4)
  q166 : Ws → Eqn
  q166 c4 = wlE 1253 (lit c4)
  q167 : Ws → Eqn
  q167 c4 = wlE 1254 (lit c4)
  q168 : Ws → Eqn
  q168 c4 = sE 294 (lem-comm-CZ14-TOFF302 c4)
  q169 : Ws → Eqn
  q169 c4 = wlE 1255 (lit c4)

-- P-box @03122031: 8 steps
lem-P-box-at03122031 : Ws → ⟪ (Toff314 ∷ Bx3-2014 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-P-box-at03122031 c4 = derive (Toff314 ∷ Bx3-2014 ∷ Toff314 ∷ []) (Bx3-2014 ∷ [])
  (rw 1 (q164 c4) ∷
   rw⁻ 0 (q165 c4) ∷
   rw⁻ 1 (q166 c4) ∷
   rw⁻ 3 (q165 c4) ∷
   rw⁻ 4 (q167 c4) ∷
   rw 2 (q168 c4) ∷
   rw⁻ 3 (q169 c4) ∷
   rw⁻ 0 (q164 c4) ∷ []) Eq.refl

private
  q170 : Ws → Eqn
  q170 c4 = wlE 1588 (lit c4)
  q171 : Ws → Eqn
  q171 c4 = wpE 744 c4
  q172 : Ws → Eqn
  q172 c4 = wpE 1513 c4
  q173 : Ws → Eqn
  q173 c4 = wpE 21 c4
  q174 : Ws → Eqn
  q174 c4 = sE 8 (lem-comm-CX31-CCZ024 c4)
  q175 : Ws → Eqn
  q175 c4 = wpE 179 c4
  q176 : Ws → Eqn
  q176 c4 = wpE 39 c4
  q177 : Ws → Eqn
  q177 c4 = wpE 747 c4

-- CXbc-box @0413213240: 17 steps
lem-CXbc-box-at0413213240 : Ws → ⟪ (CX12 ∷ Bx4-3120 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at0413213240 c4 = derive (CX12 ∷ Bx4-3120 ∷ CX12 ∷ []) (Bx4-3120 ∷ CCZ013 ∷ [])
  (rw 1 (q1 c4) ∷
   rw 0 (q170 c4) ∷
   rw⁻ 1 (q171 c4) ∷
   rw 3 (q172 c4) ∷
   rw 2 (q170 c4) ∷
   rw 5 (q158 c4) ∷
   rw⁻ 9 (q173 c4) ∷
   rw 8 (q174 c4) ∷
   rw⁻ 7 (q175 c4) ∷
   rw 6 (q174 c4) ∷
   rw⁻ 5 (q176 c4) ∷
   rw⁻ 6 (q158 c4) ∷
   rw 4 (q152 c4) ∷
   rw⁻ 3 (q171 c4) ∷
   rw 4 (q177 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q163 c4) ∷ []) Eq.refl

private
  q178 : Ws → Eqn
  q178 c4 = wlE 1731 (lit c4)
  q179 : Ws → Eqn
  q179 c4 = wpE 1514 c4
  q180 : Ws → Eqn
  q180 c4 = wpE 749 c4
  q181 : Ws → Eqn
  q181 c4 = wpE 1376 c4
  q182 : Ws → Eqn
  q182 c4 = wlE 1586 (lit c4)
  q183 : Ws → Eqn
  q183 c4 = sE 376 (lem-comm-CSd02-TOFF413 c4)
  q184 : Ws → Eqn
  q184 c4 = sE 381 (lem-comm-CS02-TOFF413 c4)
  q185 : Ws → Eqn
  q185 c4 = wlE 1732 (lit c4)
  q186 : Ws → Eqn
  q186 c4 = wpE 669 c4

-- CXcb-box @0413213240: 18 steps
lem-CXcb-box-at0413213240 : Ws → ⟪ (CX21 ∷ Bx4-3120 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ CCZ023 ∷ []) ⟫ʷ
lem-CXcb-box-at0413213240 c4 = derive (CX21 ∷ Bx4-3120 ∷ CX21 ∷ []) (Bx4-3120 ∷ CCZ023 ∷ [])
  (rw 1 (q1 c4) ∷
   rw 0 (q178 c4) ∷
   rw⁻ 2 (q179 c4) ∷
   rw⁻ 1 (q180 c4) ∷
   rw 4 (q149 c4) ∷
   rw 8 (q181 c4) ∷
   rw 7 (q182 c4) ∷
   rw 6 (q183 c4) ∷
   rw 5 (q182 c4) ∷
   rw 4 (q184 c4) ∷
   rw⁻ 5 (q149 c4) ∷
   rw⁻ 3 (q160 c4) ∷
   rw 2 (q178 c4) ∷
   rw 3 (q185 c4) ∷
   rw 4 (q186 c4) ∷
   rw⁻ 3 (q180 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q154 c4) ∷ []) Eq.refl

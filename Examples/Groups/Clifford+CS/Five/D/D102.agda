{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD102 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D102 (Sᴰ : SD102) where

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
  lem-comm-CCZ014-CX23 : Ws → St 893
  lem-comm-CCZ014-CX23 = pickᴰ 0 Sᴰ
  lem-comm-CCZ024-CS13 : Ws → St 1382
  lem-comm-CCZ024-CS13 = pickᴰ 1 Sᴰ
  lem-comm-CCZ024-CX13 : Ws → St 1024
  lem-comm-CCZ024-CX13 = pickᴰ 2 Sᴰ
  lem-comm-TOFF401-CX23 : Ws → St 1454
  lem-comm-TOFF401-CX23 = pickᴰ 3 Sᴰ
  lem-comm-TOFF413-CSd02 : Ws → St 380
  lem-comm-TOFF413-CSd02 = pickᴰ 4 Sᴰ
  lem-comm-TOFF413-CS02 : Ws → St 1455
  lem-comm-TOFF413-CS02 = pickᴰ 5 Sᴰ
  lem-comm-TOFF413-CX20 : Ws → St 1179
  lem-comm-TOFF413-CX20 = pickᴰ 6 Sᴰ
  lem-box-cP-at04203243 : Ws → St 919
  lem-box-cP-at04203243 = pickᴰ 7 Sᴰ
  lem-box-cP-at04122041 : Ws → St 1192
  lem-box-cP-at04122041 = pickᴰ 8 Sᴰ
  lem-box-cP-at0412233041 : Ws → St 1193
  lem-box-cP-at0412233041 = pickᴰ 9 Sᴰ
  lem-box-perm-1324-at04122041 : Ws → St 1437
  lem-box-perm-1324-at04122041 = pickᴰ 10 Sᴰ
  lem-L-CX01-1-at0440 : Ws → St 1835
  lem-L-CX01-1-at0440 = pickᴰ 11 Sᴰ
  lem-S2-SBOX⟨0·2·43·1⟩-at0440 : Ws → St 1678
  lem-S2-SBOX⟨0·2·43·1⟩-at0440 = pickᴰ 12 Sᴰ
  lem-L-CX01-2-at0440 : Ws → St 1836
  lem-L-CX01-2-at0440 = pickᴰ 13 Sᴰ
  lem-L-CX10-2-at0440 : Ws → St 1837
  lem-L-CX10-2-at0440 = pickᴰ 14 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1835 (lem-L-CX01-1-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1836 (lem-L-CX01-2-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1837 (lem-L-CX10-2-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1678 (lem-S2-SBOX⟨0·2·43·1⟩-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 919 (lem-box-cP-at04203243 c4)
  q6 : Ws → Eqn
  q6 c4 = wpE 1357 c4
  q7 : Ws → Eqn
  q7 c4 = wpE 1358 c4
  q8 : Ws → Eqn
  q8 c4 = wlE 1501 (lit c4)
  q9 : Ws → Eqn
  q9 c4 = wpE 65 c4
  q10 : Ws → Eqn
  q10 c4 = wpE 157 c4
  q11 : Ws → Eqn
  q11 c4 = sE 893 (lem-comm-CCZ014-CX23 c4)
  q12 : Ws → Eqn
  q12 c4 = wpE 156 c4
  q13 : Ws → Eqn
  q13 c4 = wpE 155 c4
  q14 : Ws → Eqn
  q14 c4 = wpE 61 c4
  q15 : Ws → Eqn
  q15 c4 = wpE 1318 c4
  q16 : Ws → Eqn
  q16 c4 = wlE 929 (lit c4)
  q17 : Ws → Eqn
  q17 c4 = wpE 311 c4
  q18 : Ws → Eqn
  q18 c4 = eqn (ℓ "乄亳") (ℓ "亳乄") (c₂ (CX₁₀) (Toffᵗ))
  q19 : Ws → Eqn
  q19 c4 = wpE 1355 c4
  q20 : Ws → Eqn
  q20 c4 = wlE 461 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = wpE 1356 c4
  q22 : Ws → Eqn
  q22 c4 = wpE 167 c4
  q23 : Ws → Eqn
  q23 c4 = wlE 1509 (lit c4)
  q24 : Ws → Eqn
  q24 c4 = wpE 53 c4
  q25 : Ws → Eqn
  q25 c4 = wlE 1517 (lit c4)
  q26 : Ws → Eqn
  q26 c4 = wpE 60 c4
  q27 : Ws → Eqn
  q27 c4 = wpE 1460 c4
  q28 : Ws → Eqn
  q28 c4 = wpE 1461 c4
  q29 : Ws → Eqn
  q29 c4 = wlE 1708 (lit c4)
  q30 : Ws → Eqn
  q30 c4 = wpE 1210 c4
  q31 : Ws → Eqn
  q31 c4 = wpE 1211 c4
  q32 : Ws → Eqn
  q32 c4 = wpE 1462 c4
  q33 : Ws → Eqn
  q33 c4 = wlE 477 (lit c4)
  q34 : Ws → Eqn
  q34 c4 = wpE 1347 c4
  q35 : Ws → Eqn
  q35 c4 = wpE 1348 c4
  q36 : Ws → Eqn
  q36 c4 = wpE 1463 c4
  q37 : Ws → Eqn
  q37 c4 = wpE 394 c4
  q38 : Ws → Eqn
  q38 c4 = sE 1192 (lem-box-cP-at04122041 c4)
  q39 : Ws → Eqn
  q39 c4 = wpE 1379 c4
  q40 : Ws → Eqn
  q40 c4 = wpE 1381 c4
  q41 : Ws → Eqn
  q41 c4 = wlE 1545 (lit c4)
  q42 : Ws → Eqn
  q42 c4 = wpE 89 c4
  q43 : Ws → Eqn
  q43 c4 = wpE 21 c4
  q44 : Ws → Eqn
  q44 c4 = sE 1024 (lem-comm-CCZ024-CX13 c4)
  q45 : Ws → Eqn
  q45 c4 = wpE 32 c4
  q46 : Ws → Eqn
  q46 c4 = wpE 39 c4
  q47 : Ws → Eqn
  q47 c4 = wpE 88 c4
  q48 : Ws → Eqn
  q48 c4 = wpE 1377 c4
  q49 : Ws → Eqn
  q49 c4 = wlE 1270 (lit c4)
  q50 : Ws → Eqn
  q50 c4 = wpE 1376 c4
  q51 : Ws → Eqn
  q51 c4 = sE 1179 (lem-comm-TOFF413-CX20 c4)
  q52 : Ws → Eqn
  q52 c4 = wpE 1375 c4
  q53 : Ws → Eqn
  q53 c4 = wlE 1546 (lit c4)
  q54 : Ws → Eqn
  q54 c4 = wpE 1378 c4
  q55 : Ws → Eqn
  q55 c4 = wpE 669 c4
  q56 : Ws → Eqn
  q56 c4 = wlE 1547 (lit c4)
  q57 : Ws → Eqn
  q57 c4 = wpE 81 c4
  q58 : Ws → Eqn
  q58 c4 = wlE 1544 (lit c4)
  q59 : Ws → Eqn
  q59 c4 = wpE 87 c4
  q60 : Ws → Eqn
  q60 c4 = wlE 1695 (lit c4)
  q61 : Ws → Eqn
  q61 c4 = wlE 1538 (lit c4)
  q62 : Ws → Eqn
  q62 c4 = sE 1455 (lem-comm-TOFF413-CS02 c4)
  q63 : Ws → Eqn
  q63 c4 = wlE 1588 (lit c4)
  q64 : Ws → Eqn
  q64 c4 = sE 380 (lem-comm-TOFF413-CSd02 c4)
  q65 : Ws → Eqn
  q65 c4 = wpE 1398 c4
  q66 : Ws → Eqn
  q66 c4 = wlE 1709 (lit c4)
  q67 : Ws → Eqn
  q67 c4 = wpE 1288 c4
  q68 : Ws → Eqn
  q68 c4 = wpE 1464 c4
  q69 : Ws → Eqn
  q69 c4 = wpE 38 c4
  q70 : Ws → Eqn
  q70 c4 = wlE 289 (lit c4)
  q71 : Ws → Eqn
  q71 c4 = wpE 1465 c4
  q72 : Ws → Eqn
  q72 c4 = sE 1437 (lem-box-perm-1324-at04122041 c4)
  q73 : Ws → Eqn
  q73 c4 = sE 1193 (lem-box-cP-at0412233041 c4)
  q74 : Ws → Eqn
  q74 c4 = wpE 1345 c4
  q75 : Ws → Eqn
  q75 c4 = wpE 1328 c4
  q76 : Ws → Eqn
  q76 c4 = sE 1454 (lem-comm-TOFF401-CX23 c4)
  q77 : Ws → Eqn
  q77 c4 = wpE 1344 c4
  q78 : Ws → Eqn
  q78 c4 = wpE 1343 c4
  q79 : Ws → Eqn
  q79 c4 = wpE 1342 c4
  q80 : Ws → Eqn
  q80 c4 = wpE 1466 c4
  q81 : Ws → Eqn
  q81 c4 = wpE 1370 c4
  q82 : Ws → Eqn
  q82 c4 = wpE 90 c4
  q83 : Ws → Eqn
  q83 c4 = wpE 279 c4
  q84 : Ws → Eqn
  q84 c4 = eqn (ℓ "乄亰") (ℓ "亰乄") (c₂ (CX₁₀) (CCZ))
  q85 : Ws → Eqn
  q85 c4 = wpE 765 c4
  q86 : Ws → Eqn
  q86 c4 = wlE 415 (lit c4)
  q87 : Ws → Eqn
  q87 c4 = wpE 1346 c4
  q88 : Ws → Eqn
  q88 c4 = wlE 1710 (lit c4)
  q89 : Ws → Eqn
  q89 c4 = wpE 1467 c4
  q90 : Ws → Eqn
  q90 c4 = wpE 1468 c4
  q91 : Ws → Eqn
  q91 c4 = wpE 109 c4
  q92 : Ws → Eqn
  q92 c4 = wpE 1469 c4
  q93 : Ws → Eqn
  q93 c4 = wlE 155 (lit c4)
  q94 : Ws → Eqn
  q94 c4 = wpE 142 c4
  q95 : Ws → Eqn
  q95 c4 = wlE 1502 (lit c4)
  q96 : Ws → Eqn
  q96 c4 = sE 1382 (lem-comm-CCZ024-CS13 c4)

-- L-CCZ-1 @0440 part0: 500 steps
lem-L-CCZ-1-at0440-part0 : Ws → ⟪ (ℓ "俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上") ⟫ʷ ≈ ⟪ (ℓ "侗互乇互么亏亘亘互乇亘互么亏亐些二亚亐些二二些二乎二亰丞丶书丷书丯亗丟亜亰亗乏二些亐亚二些侒") ⟫ʷ
lem-L-CCZ-1-at0440-part0 c4 = derive (ℓ "俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上") (ℓ "侗互乇互么亏亘亘互乇亘互么亏亐些二亚亐些二二些二乎二亰丞丶书丷书丯亗丟亜亰亗乏二些亐亚二些侒")
  (rw 1 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q2 c4) ∷
   rw 7 (q3 c4) ∷
   rw 8 (q2 c4) ∷
   rw 10 (q2 c4) ∷
   rw 11 (q3 c4) ∷
   rw 12 (q2 c4) ∷
   rw 2 (q4 c4) ∷
   re 0 1 (ℓ "侗互俳互俴") ∷
   re 2 1 (ℓ "乇") ∷
   re 4 1 (ℓ "么") ∷
   re 7 1 (ℓ "侗互俳互俴") ∷
   re 9 1 (ℓ "乇") ∷
   re 11 1 (ℓ "么") ∷
   re 16 1 (ℓ "侒些俫些俬") ∷
   re 18 1 (ℓ "乎") ∷
   re 20 1 (ℓ "乏") ∷
   rw 16 (q5 c4) ∷
   rw⁻ 19 (q6 c4) ∷
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
   rw⁻ 17 (q15 c4) ∷
   rw 19 (q16 c4) ∷
   rw⁻ 18 (q17 c4) ∷
   rw⁻ 19 (q18 c4) ∷
   rw⁻ 20 (q19 c4) ∷
   rw⁻ 21 (q18 c4) ∷
   rw⁻ 22 (q20 c4) ∷
   rw⁻ 18 (q16 c4) ∷
   rw⁻ 19 (q6 c4) ∷
   rw⁻ 17 (q21 c4) ∷
   rw⁻ 16 (q22 c4) ∷
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
   rw⁻ 22 (q6 c4) ∷
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
   rw⁻ 20 (q15 c4) ∷
   rw 22 (q16 c4) ∷
   rw⁻ 21 (q17 c4) ∷
   rw⁻ 22 (q18 c4) ∷
   rw⁻ 23 (q19 c4) ∷
   rw⁻ 24 (q18 c4) ∷
   rw⁻ 25 (q20 c4) ∷
   rw⁻ 21 (q16 c4) ∷
   rw⁻ 22 (q6 c4) ∷
   rw⁻ 20 (q21 c4) ∷
   rw⁻ 19 (q22 c4) ∷
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
   rw⁻ 25 (q6 c4) ∷
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
   rw⁻ 23 (q15 c4) ∷
   rw 25 (q16 c4) ∷
   rw⁻ 24 (q17 c4) ∷
   rw⁻ 25 (q18 c4) ∷
   rw⁻ 26 (q19 c4) ∷
   rw⁻ 27 (q18 c4) ∷
   rw⁻ 28 (q20 c4) ∷
   rw⁻ 24 (q16 c4) ∷
   rw⁻ 25 (q6 c4) ∷
   rw⁻ 23 (q21 c4) ∷
   rw⁻ 22 (q22 c4) ∷
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
   rw⁻ 27 (q27 c4) ∷
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
   rw⁻ 25 (q32 c4) ∷
   rw 27 (q33 c4) ∷
   rw⁻ 26 (q34 c4) ∷
   rw⁻ 27 (q18 c4) ∷
   rw⁻ 28 (q35 c4) ∷
   rw⁻ 29 (q18 c4) ∷
   rw⁻ 30 (q23 c4) ∷
   rw⁻ 26 (q33 c4) ∷
   rw⁻ 27 (q27 c4) ∷
   rw⁻ 25 (q36 c4) ∷
   rw⁻ 24 (q37 c4) ∷
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
   rw⁻ 29 (q6 c4) ∷
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
   rw⁻ 27 (q15 c4) ∷
   rw 29 (q16 c4) ∷
   rw⁻ 28 (q17 c4) ∷
   rw⁻ 29 (q18 c4) ∷
   rw⁻ 30 (q19 c4) ∷
   rw⁻ 31 (q18 c4) ∷
   rw⁻ 32 (q20 c4) ∷
   rw⁻ 28 (q16 c4) ∷
   rw⁻ 29 (q6 c4) ∷
   rw⁻ 27 (q21 c4) ∷
   rw⁻ 26 (q22 c4) ∷
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
   rw⁻ 10 (q39 c4) ∷
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
   rw⁻ 8 (q48 c4) ∷
   rw 10 (q49 c4) ∷
   rw⁻ 9 (q50 c4) ∷
   rw 10 (q51 c4) ∷
   rw⁻ 11 (q52 c4) ∷
   rw 12 (q51 c4) ∷
   rw⁻ 13 (q53 c4) ∷
   rw⁻ 9 (q49 c4) ∷
   rw⁻ 10 (q39 c4) ∷
   rw⁻ 8 (q54 c4) ∷
   rw⁻ 7 (q55 c4) ∷
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
   rw⁻ 13 (q39 c4) ∷
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
   rw⁻ 11 (q48 c4) ∷
   rw 13 (q49 c4) ∷
   rw⁻ 12 (q50 c4) ∷
   rw 13 (q51 c4) ∷
   rw⁻ 14 (q52 c4) ∷
   rw 15 (q51 c4) ∷
   rw⁻ 16 (q53 c4) ∷
   rw⁻ 12 (q49 c4) ∷
   rw⁻ 13 (q39 c4) ∷
   rw⁻ 11 (q54 c4) ∷
   rw⁻ 10 (q55 c4) ∷
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
   rw⁻ 17 (q82 c4) ∷
   rw 19 (q16 c4) ∷
   rw 18 (q83 c4) ∷
   rw⁻ 19 (q84 c4) ∷
   rw 20 (q85 c4) ∷
   rw⁻ 21 (q84 c4) ∷
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
   rw⁻ 21 (q82 c4) ∷
   rw 23 (q16 c4) ∷
   rw 22 (q83 c4) ∷
   rw⁻ 23 (q84 c4) ∷
   rw 24 (q85 c4) ∷
   rw⁻ 25 (q84 c4) ∷
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
   rw⁻ 23 (q94 c4) ∷
   rw 23 (q93 c4) ∷
   rw 22 (q62 c4) ∷
   rw⁻ 23 (q63 c4) ∷
   rw 24 (q64 c4) ∷
   rw⁻ 25 (q63 c4) ∷
   rw⁻ 26 (q65 c4) ∷
   rw⁻ 22 (q93 c4) ∷
   rw⁻ 21 (q94 c4) ∷
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
   rw⁻ 24 (q82 c4) ∷
   rw 26 (q16 c4) ∷
   rw 25 (q83 c4) ∷
   rw⁻ 26 (q84 c4) ∷
   rw 27 (q85 c4) ∷
   rw⁻ 28 (q84 c4) ∷
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
   rw⁻ 27 (q94 c4) ∷
   rw 27 (q93 c4) ∷
   rw 26 (q62 c4) ∷
   rw⁻ 27 (q63 c4) ∷
   rw 28 (q64 c4) ∷
   rw⁻ 29 (q63 c4) ∷
   rw⁻ 30 (q65 c4) ∷
   rw⁻ 26 (q93 c4) ∷
   rw⁻ 25 (q94 c4) ∷
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

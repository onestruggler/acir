{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD213 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D213 (Sᴰ : SD213) where

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
  lem-F4-I-I-at0440 : Ws → St 1452
  lem-F4-I-I-at0440 = pickᴰ 0 Sᴰ
  lem-F4-I-K2-at0440 : Ws → St 1454
  lem-F4-I-K2-at0440 = pickᴰ 1 Sᴰ
  lem-F4-I-K3-at0440 : Ws → St 1455
  lem-F4-I-K3-at0440 = pickᴰ 2 Sᴰ
  lem-F4-K1-I-at0440 : Ws → St 1456
  lem-F4-K1-I-at0440 = pickᴰ 3 Sᴰ
  lem-F4-K1-K2-at0440 : Ws → St 1458
  lem-F4-K1-K2-at0440 = pickᴰ 4 Sᴰ
  lem-F4-K1-K3-at0440 : Ws → St 1459
  lem-F4-K1-K3-at0440 = pickᴰ 5 Sᴰ
  lem-F4-S0-I-at0440 : Ws → St 1843
  lem-F4-S0-I-at0440 = pickᴰ 6 Sᴰ
  lem-F4-S0-K2-at0440 : Ws → St 1845
  lem-F4-S0-K2-at0440 = pickᴰ 7 Sᴰ
  lem-F4-S0-K3-at0440 : Ws → St 1846
  lem-F4-S0-K3-at0440 = pickᴰ 8 Sᴰ
  lem-F4-S0-CS1-at0440 : Ws → St 1847
  lem-F4-S0-CS1-at0440 = pickᴰ 9 Sᴰ
  lem-F4-I-CS1-at0440 : Ws → St 1460
  lem-F4-I-CS1-at0440 = pickᴰ 10 Sᴰ
  lem-F4-K1-CS1-at0440 : Ws → St 1461
  lem-F4-K1-CS1-at0440 = pickᴰ 11 Sᴰ
  lem-F4-S0-CS2-at0440 : Ws → St 1848
  lem-F4-S0-CS2-at0440 = pickᴰ 12 Sᴰ
  lem-F4-I-CS2-at0440 : Ws → St 1462
  lem-F4-I-CS2-at0440 = pickᴰ 13 Sᴰ
  lem-F4-CS0-I-at0440 : Ws → St 1850
  lem-F4-CS0-I-at0440 = pickᴰ 14 Sᴰ
  lem-F4-K1-CS2-at0440 : Ws → St 1463
  lem-F4-K1-CS2-at0440 = pickᴰ 15 Sᴰ
  lem-F4-CS0-K3-at0440 : Ws → St 1853
  lem-F4-CS0-K3-at0440 = pickᴰ 16 Sᴰ
  lem-F4-CS0-K2-at0440 : Ws → St 1854
  lem-F4-CS0-K2-at0440 = pickᴰ 17 Sᴰ
  lem-F4-CS0-CS2-at0440 : Ws → St 1855
  lem-F4-CS0-CS2-at0440 = pickᴰ 18 Sᴰ
  lem-F4-CS0-CS1-at0440 : Ws → St 1856
  lem-F4-CS0-CS1-at0440 = pickᴰ 19 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1856 (lem-F4-CS0-CS1-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1461 (lem-F4-K1-CS1-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1454 (lem-F4-I-K2-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1845 (lem-F4-S0-K2-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1854 (lem-F4-CS0-K2-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1458 (lem-F4-K1-K2-at0440 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1452 (lem-F4-I-I-at0440 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1843 (lem-F4-S0-I-at0440 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1850 (lem-F4-CS0-I-at0440 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1456 (lem-F4-K1-I-at0440 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1462 (lem-F4-I-CS2-at0440 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1848 (lem-F4-S0-CS2-at0440 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1855 (lem-F4-CS0-CS2-at0440 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1463 (lem-F4-K1-CS2-at0440 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1460 (lem-F4-I-CS1-at0440 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1847 (lem-F4-S0-CS1-at0440 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1455 (lem-F4-I-K3-at0440 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1846 (lem-F4-S0-K3-at0440 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1853 (lem-F4-CS0-K3-at0440 c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1459 (lem-F4-K1-K3-at0440 c4)

-- F1-ck-tct@0 part2: 241 steps
lem-F1-ck-tctat0-part2 : Ws → ⟪ (CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CK03 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ []) ⟫ʷ
lem-F1-ck-tctat0-part2 c4 = derive (CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ []) (CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CK03 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ [])
  (rw 65 (q1 c4) ∷
   rw 62 (q2 c4) ∷
   rw 59 (q1 c4) ∷
   rw 56 (q2 c4) ∷
   rw 53 (q1 c4) ∷
   rw 78 (q3 c4) ∷
   rw 75 (q4 c4) ∷
   rw 72 (q4 c4) ∷
   rw 69 (q4 c4) ∷
   rw 66 (q5 c4) ∷
   rw 63 (q6 c4) ∷
   rw 60 (q5 c4) ∷
   rw 57 (q6 c4) ∷
   rw 54 (q5 c4) ∷
   rw 79 (q7 c4) ∷
   rw 76 (q8 c4) ∷
   rw 73 (q8 c4) ∷
   rw 70 (q8 c4) ∷
   rw 67 (q9 c4) ∷
   rw 64 (q10 c4) ∷
   rw 61 (q9 c4) ∷
   rw 58 (q10 c4) ∷
   rw 55 (q9 c4) ∷
   rw 80 (q11 c4) ∷
   rw 77 (q12 c4) ∷
   rw 74 (q12 c4) ∷
   rw 71 (q12 c4) ∷
   rw 68 (q13 c4) ∷
   rw 65 (q14 c4) ∷
   rw 62 (q13 c4) ∷
   rw 59 (q14 c4) ∷
   rw 56 (q13 c4) ∷
   rw 81 (q11 c4) ∷
   rw 78 (q12 c4) ∷
   rw 75 (q12 c4) ∷
   rw 72 (q12 c4) ∷
   rw 69 (q13 c4) ∷
   rw 66 (q14 c4) ∷
   rw 63 (q13 c4) ∷
   rw 60 (q14 c4) ∷
   rw 57 (q13 c4) ∷
   rw 82 (q11 c4) ∷
   rw 79 (q12 c4) ∷
   rw 76 (q12 c4) ∷
   rw 73 (q12 c4) ∷
   rw 70 (q13 c4) ∷
   rw 67 (q14 c4) ∷
   rw 64 (q13 c4) ∷
   rw 61 (q14 c4) ∷
   rw 58 (q13 c4) ∷
   rw 83 (q3 c4) ∷
   rw 80 (q4 c4) ∷
   rw 77 (q4 c4) ∷
   rw 74 (q4 c4) ∷
   rw 71 (q5 c4) ∷
   rw 68 (q6 c4) ∷
   rw 65 (q5 c4) ∷
   rw 62 (q6 c4) ∷
   rw 59 (q5 c4) ∷
   rw 84 (q15 c4) ∷
   rw 81 (q16 c4) ∷
   rw 78 (q16 c4) ∷
   rw 75 (q16 c4) ∷
   rw 72 (q1 c4) ∷
   rw 69 (q2 c4) ∷
   rw 66 (q1 c4) ∷
   rw 63 (q2 c4) ∷
   rw 60 (q1 c4) ∷
   rw 85 (q15 c4) ∷
   rw 82 (q16 c4) ∷
   rw 79 (q16 c4) ∷
   rw 76 (q16 c4) ∷
   rw 73 (q1 c4) ∷
   rw 70 (q2 c4) ∷
   rw 67 (q1 c4) ∷
   rw 64 (q2 c4) ∷
   rw 61 (q1 c4) ∷
   rw 86 (q3 c4) ∷
   rw 83 (q4 c4) ∷
   rw 80 (q4 c4) ∷
   rw 77 (q4 c4) ∷
   rw 74 (q5 c4) ∷
   rw 71 (q6 c4) ∷
   rw 68 (q5 c4) ∷
   rw 65 (q6 c4) ∷
   rw 62 (q5 c4) ∷
   rw 87 (q7 c4) ∷
   rw 84 (q8 c4) ∷
   rw 81 (q8 c4) ∷
   rw 78 (q8 c4) ∷
   rw 75 (q9 c4) ∷
   rw 72 (q10 c4) ∷
   rw 69 (q9 c4) ∷
   rw 66 (q10 c4) ∷
   rw 63 (q9 c4) ∷
   rw 88 (q17 c4) ∷
   rw 85 (q18 c4) ∷
   rw 82 (q18 c4) ∷
   rw 79 (q18 c4) ∷
   rw 76 (q19 c4) ∷
   rw 73 (q20 c4) ∷
   rw 70 (q19 c4) ∷
   rw 67 (q20 c4) ∷
   rw 64 (q19 c4) ∷
   rw 89 (q11 c4) ∷
   rw 86 (q12 c4) ∷
   rw 83 (q12 c4) ∷
   rw 80 (q12 c4) ∷
   rw 77 (q13 c4) ∷
   rw 74 (q14 c4) ∷
   rw 71 (q13 c4) ∷
   rw 68 (q14 c4) ∷
   rw 65 (q13 c4) ∷
   rw 90 (q11 c4) ∷
   rw 87 (q12 c4) ∷
   rw 84 (q12 c4) ∷
   rw 81 (q12 c4) ∷
   rw 78 (q13 c4) ∷
   rw 75 (q14 c4) ∷
   rw 72 (q13 c4) ∷
   rw 69 (q14 c4) ∷
   rw 66 (q13 c4) ∷
   rw 91 (q17 c4) ∷
   rw 88 (q18 c4) ∷
   rw 85 (q18 c4) ∷
   rw 82 (q18 c4) ∷
   rw 79 (q19 c4) ∷
   rw 76 (q20 c4) ∷
   rw 73 (q19 c4) ∷
   rw 70 (q20 c4) ∷
   rw 67 (q19 c4) ∷
   rw 92 (q7 c4) ∷
   rw 89 (q8 c4) ∷
   rw 86 (q8 c4) ∷
   rw 83 (q8 c4) ∷
   rw 80 (q9 c4) ∷
   rw 77 (q10 c4) ∷
   rw 74 (q9 c4) ∷
   rw 71 (q10 c4) ∷
   rw 68 (q9 c4) ∷
   rw 93 (q3 c4) ∷
   rw 90 (q4 c4) ∷
   rw 87 (q4 c4) ∷
   rw 84 (q4 c4) ∷
   rw 81 (q5 c4) ∷
   rw 78 (q6 c4) ∷
   rw 75 (q5 c4) ∷
   rw 72 (q6 c4) ∷
   rw 69 (q5 c4) ∷
   rw 94 (q11 c4) ∷
   rw 91 (q12 c4) ∷
   rw 88 (q12 c4) ∷
   rw 85 (q12 c4) ∷
   rw 82 (q13 c4) ∷
   rw 79 (q14 c4) ∷
   rw 76 (q13 c4) ∷
   rw 73 (q14 c4) ∷
   rw 70 (q13 c4) ∷
   rw 95 (q11 c4) ∷
   rw 92 (q12 c4) ∷
   rw 89 (q12 c4) ∷
   rw 86 (q12 c4) ∷
   rw 83 (q13 c4) ∷
   rw 80 (q14 c4) ∷
   rw 77 (q13 c4) ∷
   rw 74 (q14 c4) ∷
   rw 71 (q13 c4) ∷
   rw 96 (q3 c4) ∷
   rw 93 (q4 c4) ∷
   rw 90 (q4 c4) ∷
   rw 87 (q4 c4) ∷
   rw 84 (q5 c4) ∷
   rw 81 (q6 c4) ∷
   rw 78 (q5 c4) ∷
   rw 75 (q6 c4) ∷
   rw 72 (q5 c4) ∷
   rw 97 (q7 c4) ∷
   rw 94 (q8 c4) ∷
   rw 91 (q8 c4) ∷
   rw 88 (q8 c4) ∷
   rw 85 (q9 c4) ∷
   rw 82 (q10 c4) ∷
   rw 79 (q9 c4) ∷
   rw 76 (q10 c4) ∷
   rw 73 (q9 c4) ∷
   rw 98 (q17 c4) ∷
   rw 95 (q18 c4) ∷
   rw 92 (q18 c4) ∷
   rw 89 (q18 c4) ∷
   rw 86 (q19 c4) ∷
   rw 83 (q20 c4) ∷
   rw 80 (q19 c4) ∷
   rw 77 (q20 c4) ∷
   rw 74 (q19 c4) ∷
   rw 99 (q11 c4) ∷
   rw 96 (q12 c4) ∷
   rw 93 (q12 c4) ∷
   rw 90 (q12 c4) ∷
   rw 87 (q13 c4) ∷
   rw 84 (q14 c4) ∷
   rw 81 (q13 c4) ∷
   rw 78 (q14 c4) ∷
   rw 75 (q13 c4) ∷
   rw 100 (q11 c4) ∷
   rw 97 (q12 c4) ∷
   rw 94 (q12 c4) ∷
   rw 91 (q12 c4) ∷
   rw 88 (q13 c4) ∷
   rw 85 (q14 c4) ∷
   rw 82 (q13 c4) ∷
   rw 79 (q14 c4) ∷
   rw 76 (q13 c4) ∷
   rw 101 (q17 c4) ∷
   rw 98 (q18 c4) ∷
   rw 95 (q18 c4) ∷
   rw 92 (q18 c4) ∷
   rw 89 (q19 c4) ∷
   rw 86 (q20 c4) ∷
   rw 83 (q19 c4) ∷
   rw 80 (q20 c4) ∷
   rw 77 (q19 c4) ∷
   rw 102 (q7 c4) ∷
   rw 99 (q8 c4) ∷
   rw 96 (q8 c4) ∷
   rw 93 (q8 c4) ∷
   rw 90 (q9 c4) ∷
   rw 87 (q10 c4) ∷
   rw 84 (q9 c4) ∷
   rw 81 (q10 c4) ∷
   rw 78 (q9 c4) ∷
   rw 103 (q15 c4) ∷
   rw 100 (q16 c4) ∷
   rw 97 (q16 c4) ∷
   rw 94 (q16 c4) ∷
   rw 91 (q1 c4) ∷
   rw 88 (q2 c4) ∷
   rw 85 (q1 c4) ∷
   rw 82 (q2 c4) ∷
   rw 79 (q1 c4) ∷
   rw 104 (q17 c4) ∷
   rw 101 (q18 c4) ∷ []) Eq.refl

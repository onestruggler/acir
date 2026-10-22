{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD784 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D784 (W : Ws) (Sᴰ : SD784) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

-- The lemmas of other derivation modules (DSig).
private
  lem-Hc-passes-copies-X0-CS01-CS01-CK10-CS01-CX13-CS : St 3482
  lem-Hc-passes-copies-X0-CS01-CS01-CK10-CS01-CX13-CS = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 225 W
  q2 : Eqn
  q2 = wE 871 W
  q3 : Eqn
  q3 = wE 2580 W
  q4 : Eqn
  q4 = wE 1510 W
  q5 : Eqn
  q5 = wE 2578 W
  q6 : Eqn
  q6 = wE 1377 W
  q7 : Eqn
  q7 = wE 1376 W
  q8 : Eqn
  q8 = wE 1378 W
  q9 : Eqn
  q9 = wE 2579 W
  q10 : Eqn
  q10 = wE 1732 W
  q11 : Eqn
  q11 = wE 116 W
  q12 : Eqn
  q12 = wE 45 W
  q13 : Eqn
  q13 = wE 1 W
  q14 : Eqn
  q14 = wE 1357 W
  q15 : Eqn
  q15 = wE 3 W
  q16 : Eqn
  q16 = wE 231 W
  q17 : Eqn
  q17 = wE 54 W
  q18 : Eqn
  q18 = wE 1726 W
  q19 : Eqn
  q19 = sE 3482 lem-Hc-passes-copies-X0-CS01-CS01-CK10-CS01-CX13-CS
  q20 : Eqn
  q20 = wE 390 W
  q21 : Eqn
  q21 = wE 389 W
  q22 : Eqn
  q22 = wE 2583 W
  q23 : Eqn
  q23 = wE 2582 W
  q24 : Eqn
  q24 = wE 2581 W
  q25 : Eqn
  q25 = wE 1380 W
  q26 : Eqn
  q26 = wE 1379 W
  q27 : Eqn
  q27 = wE 1381 W
  q28 : Eqn
  q28 = wE 1509 W
  q29 : Eqn
  q29 = wE 2487 W
  q30 : Eqn
  q30 = wE 1339 W
  q31 : Eqn
  q31 = wE 227 W
  q32 : Eqn
  q32 = wE 1358 W
  q33 : Eqn
  q33 = wE 1342 W
  q34 : Eqn
  q34 = wE 1846 W
  q35 : Eqn
  q35 = wE 1728 W

-- Hc passes copies X0 CS01 CS01 CK10 CS01 CX13 CS ^inv: 225 steps
lem-Hc-passes-copies-X0-CS01-CS01-CK10-CS01-CX13-CS-ᵖinv : ⟪ (X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ X0 ∷ X3 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X2 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X3 ∷ X2 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ X2 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X2 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X3 ∷ X2 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ X2 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ X0 ∷ []) ⟫ʷ
lem-Hc-passes-copies-X0-CS01-CS01-CK10-CS01-CX13-CS-ᵖinv = derive (X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ X0 ∷ X3 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X2 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X3 ∷ X2 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ X2 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X2 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X3 ∷ X2 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ X2 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ X0 ∷ [])
  (rw 0 q1 ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q5 ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q7 ∷
   rw 8 q6 ∷
   rw 9 q8 ∷
   rw 10 q3 ∷
   rw 11 q3 ∷
   rw 12 q9 ∷
   rw 13 q5 ∷
   rw 14 q1 ∷
   rw 15 q2 ∷
   rw 16 q2 ∷
   rw 17 q3 ∷
   rw 18 q4 ∷
   rw 19 q5 ∷
   rw 20 q5 ∷
   rw 21 q6 ∷
   rw 22 q7 ∷
   rw 23 q6 ∷
   rw 24 q8 ∷
   rw 25 q3 ∷
   rw 26 q3 ∷
   rw 27 q9 ∷
   rw 28 q5 ∷
   rw 29 q2 ∷
   rw 30 q1 ∷
   rw 31 q3 ∷
   rw 32 q4 ∷
   rw 33 q5 ∷
   rw 34 q5 ∷
   rw 35 q6 ∷
   rw 36 q7 ∷
   rw 37 q6 ∷
   rw 38 q8 ∷
   rw 39 q3 ∷
   rw 40 q3 ∷
   rw 41 q9 ∷
   rw 42 q5 ∷
   rw 43 q1 ∷
   rw 44 q1 ∷
   rw 45 q2 ∷
   rw 46 q10 ∷
   rw 47 q11 ∷
   rw 48 q12 ∷
   rw 49 q13 ∷
   rw 50 q14 ∷
   rw 51 q13 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 52 q13 ∷
   re 50 3 (CS03⁻ ∷ []) ∷
   rw 51 q15 ∷
   rw 50 q12 ∷
   rw 51 q13 ∷
   rw 52 q16 ∷
   rw 53 q13 ∷
   re 51 3 (CS03⁻ ∷ []) ∷
   rw 54 q13 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw 53 q15 ∷
   rw 52 q17 ∷
   rw 53 q18 ∷
   rw 54 q1 ∷
   rw 55 q2 ∷
   rw 56 q2 ∷
   rw 57 q10 ∷
   rw 58 q11 ∷
   rw 59 q12 ∷
   rw 60 q13 ∷
   rw 61 q14 ∷
   rw 62 q13 ∷
   re 60 3 (CS03 ∷ []) ∷
   rw 63 q13 ∷
   re 61 3 (CS03⁻ ∷ []) ∷
   rw 62 q15 ∷
   rw 61 q12 ∷
   rw 62 q13 ∷
   rw 63 q16 ∷
   rw 64 q13 ∷
   re 62 3 (CS03⁻ ∷ []) ∷
   rw 65 q13 ∷
   re 63 3 (CS03 ∷ []) ∷
   rw 64 q15 ∷
   rw 63 q17 ∷
   rw 64 q18 ∷
   rw 65 q2 ∷
   rw 66 q1 ∷
   rw 67 q10 ∷
   rw 68 q11 ∷
   rw 69 q12 ∷
   rw 70 q13 ∷
   rw 71 q14 ∷
   rw 72 q13 ∷
   re 70 3 (CS03 ∷ []) ∷
   rw 73 q13 ∷
   re 71 3 (CS03⁻ ∷ []) ∷
   rw 72 q15 ∷
   rw 71 q12 ∷
   rw 72 q13 ∷
   rw 73 q16 ∷
   rw 74 q13 ∷
   re 72 3 (CS03⁻ ∷ []) ∷
   rw 75 q13 ∷
   re 73 3 (CS03 ∷ []) ∷
   rw 74 q15 ∷
   rw 73 q17 ∷
   rw 74 q18 ∷
   rw 75 q1 ∷
   rw⁻ 76 q19 ∷
   rw 233 q20 ∷
   rw 232 q21 ∷
   rw 231 q22 ∷
   rw 230 q23 ∷
   rw 229 q24 ∷
   rw 228 q24 ∷
   rw 227 q25 ∷
   rw 226 q26 ∷
   rw 225 q25 ∷
   rw 224 q27 ∷
   rw 223 q22 ∷
   rw 222 q22 ∷
   rw 221 q28 ∷
   rw 220 q24 ∷
   rw 219 q20 ∷
   rw 218 q21 ∷
   rw 217 q21 ∷
   rw 216 q22 ∷
   rw 215 q23 ∷
   rw 214 q24 ∷
   rw 213 q24 ∷
   rw 212 q25 ∷
   rw 211 q26 ∷
   rw 210 q25 ∷
   rw 209 q27 ∷
   rw 208 q22 ∷
   rw 207 q22 ∷
   rw 206 q28 ∷
   rw 205 q24 ∷
   rw 204 q21 ∷
   rw 203 q20 ∷
   rw 202 q22 ∷
   rw 201 q23 ∷
   rw 200 q24 ∷
   rw 199 q24 ∷
   rw 198 q25 ∷
   rw 197 q26 ∷
   rw 196 q25 ∷
   rw 195 q27 ∷
   rw 194 q22 ∷
   rw 193 q22 ∷
   rw 192 q28 ∷
   rw 191 q24 ∷
   rw 190 q20 ∷
   rw 189 q20 ∷
   rw 188 q21 ∷
   rw 187 q29 ∷
   rw 186 q30 ∷
   rw 185 q31 ∷
   rw 186 q13 ∷
   re 185 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 187 q15 ∷
   re 184 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 186 q15 ∷
   rw 185 q32 ∷
   rw 184 q15 ∷
   rw 183 q31 ∷
   rw 184 q13 ∷
   re 183 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 185 q15 ∷
   re 182 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 184 q15 ∷
   rw 183 q33 ∷
   rw 182 q15 ∷
   rw 181 q34 ∷
   rw 180 q35 ∷
   rw 179 q20 ∷
   rw 178 q21 ∷
   rw 177 q21 ∷
   rw 176 q29 ∷
   rw 175 q30 ∷
   rw 174 q31 ∷
   rw 175 q13 ∷
   re 174 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 176 q15 ∷
   re 173 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 175 q15 ∷
   rw 174 q32 ∷
   rw 173 q15 ∷
   rw 172 q31 ∷
   rw 173 q13 ∷
   re 172 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 174 q15 ∷
   re 171 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 173 q15 ∷
   rw 172 q33 ∷
   rw 171 q15 ∷
   rw 170 q34 ∷
   rw 169 q35 ∷
   rw 168 q21 ∷
   rw 167 q20 ∷
   rw 166 q29 ∷
   rw 165 q30 ∷
   rw 164 q31 ∷
   rw 165 q13 ∷
   re 164 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 166 q15 ∷
   re 163 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 165 q15 ∷
   rw 164 q32 ∷
   rw 163 q15 ∷
   rw 162 q31 ∷
   rw 163 q13 ∷
   re 162 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 164 q15 ∷
   re 161 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 163 q15 ∷
   rw 162 q33 ∷
   rw 161 q15 ∷
   rw 160 q34 ∷
   rw 159 q35 ∷
   rw 158 q20 ∷ []) Eq.refl

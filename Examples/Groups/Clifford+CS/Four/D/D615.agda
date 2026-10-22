{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD615 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D615 (W : Ws) (Sᴰ : SD615) where

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
  lem-pass-CCZ123-vs-CS13 : St 1333
  lem-pass-CCZ123-vs-CS13 = pickᴰ 0 Sᴰ
  lem-pass-CCZ123-vs-CSd13 : St 1334
  lem-pass-CCZ123-vs-CSd13 = pickᴰ 1 Sᴰ
  lem-pass-CZ13-vs-CS13 : St 1337
  lem-pass-CZ13-vs-CS13 = pickᴰ 2 Sᴰ
  lem-pass-CZ13-vs-CSd13 : St 1338
  lem-pass-CZ13-vs-CSd13 = pickᴰ 3 Sᴰ
  lem-pass-CCZ123-vs-CCZ023 : St 922
  lem-pass-CCZ123-vs-CCZ023 = pickᴰ 4 Sᴰ
  lem-pass-CCZ023-vs-CZ13 : St 1256
  lem-pass-CCZ023-vs-CZ13 = pickᴰ 5 Sᴰ
  lem-pass-S0-vs-TOFF012-CS03-TOFF012-CSd03 : St 1110
  lem-pass-S0-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 6 Sᴰ
  lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 1191
  lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 7 Sᴰ
  lem-T-CZ03-T-at1023 : St 1360
  lem-T-CZ03-T-at1023 = pickᴰ 8 Sᴰ
  lem-pass-X3-CKd31-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 1386
  lem-pass-X3-CKd31-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 9 Sᴰ
  lem-pass-X1-CS10-X1-vs-Sd0-K0-K0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-Kd0-Kd0-S0 : St 1387
  lem-pass-X1-CS10-X1-vs-Sd0-K0-K0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-Kd0-Kd0-S0 = pickᴰ 10 Sᴰ
  lem-pass-X2-CK21-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : St 1388
  lem-pass-X2-CK21-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = pickᴰ 11 Sᴰ
  lem-pass-X2-CKd21-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : St 1389
  lem-pass-X2-CKd21-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = pickᴰ 12 Sᴰ

private
  q1 : Eqn
  q1 = sE 1333 lem-pass-CCZ123-vs-CS13
  q2 : Eqn
  q2 = sE 1337 lem-pass-CZ13-vs-CS13
  q3 : Eqn
  q3 = wE 1377 W
  q4 : Eqn
  q4 = wE 5 W
  q5 : Eqn
  q5 = wE 127 W
  q6 : Eqn
  q6 = wE 271 W
  q7 : Eqn
  q7 = wE 7 W
  q8 : Eqn
  q8 = wE 8 W
  q9 : Eqn
  q9 = wE 9 W
  q10 : Eqn
  q10 = wE 10 W
  q11 : Eqn
  q11 = wE 272 W
  q12 : Eqn
  q12 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q13 : Eqn
  q13 = wE 253 W
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q15 : Eqn
  q15 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q16 : Eqn
  q16 = wE 24 W
  q17 : Eqn
  q17 = wE 25 W
  q18 : Eqn
  q18 = wE 26 W
  q19 : Eqn
  q19 = wE 12 W
  q20 : Eqn
  q20 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q21 : Eqn
  q21 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap))
  q22 : Eqn
  q22 = wE 14 W
  q23 : Eqn
  q23 = wE 15 W
  q24 : Eqn
  q24 = wE 16 W
  q25 : Eqn
  q25 = wE 46 W
  q26 : Eqn
  q26 = wE 30 W
  q27 : Eqn
  q27 = wE 27 W
  q28 : Eqn
  q28 = wE 31 W
  q29 : Eqn
  q29 = wE 22 W
  q30 : Eqn
  q30 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q31 : Eqn
  q31 = wE 23 W
  q32 : Eqn
  q32 = wE 47 W
  q33 : Eqn
  q33 = wE 48 W
  q34 : Eqn
  q34 = wE 1 W
  q35 : Eqn
  q35 = wE 3 W
  q36 : Eqn
  q36 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q37 : Eqn
  q37 = wE 43 W
  q38 : Eqn
  q38 = eqn (Toff012 ∷ CCZ013 ∷ Toff012 ∷ []) (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz)
  q39 : Eqn
  q39 = wE 20 W
  q40 : Eqn
  q40 = wE 21 W
  q41 : Eqn
  q41 = wE 49 W
  q42 : Eqn
  q42 = wE 50 W
  q43 : Eqn
  q43 = wE 51 W
  q44 : Eqn
  q44 = wE 52 W
  q45 : Eqn
  q45 = sE 1360 lem-T-CZ03-T-at1023
  q46 : Eqn
  q46 = sE 1256 lem-pass-CCZ023-vs-CZ13
  q47 : Eqn
  q47 = sE 922 lem-pass-CCZ123-vs-CCZ023
  q48 : Eqn
  q48 = wE 74 W
  q49 : Eqn
  q49 = wE 33 W
  q50 : Eqn
  q50 = sE 1334 lem-pass-CCZ123-vs-CSd13
  q51 : Eqn
  q51 = sE 1338 lem-pass-CZ13-vs-CSd13

-- pass [CZ13 CCZ123] [CS13 TOFF102 CSd13 TOFF102]: 516 steps
lem-pass-CZ13-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (CZ13 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CZ13 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CZ13-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 = derive (CZ13 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CZ13 ∷ CCZ123 ∷ [])
  (rw 1 q1 ∷
   rw 0 q2 ∷
   rw 2 q3 ∷
   rw 6 q4 ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 12 q5 ∷
   rw 11 q6 ∷
   rw 10 q7 ∷
   rw 9 q8 ∷
   rw 8 q9 ∷
   rw 7 q8 ∷
   rw 6 q10 ∷
   rw 5 q6 ∷
   rw 6 q11 ∷
   re 6 8 (Toff012 ∷ []) ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q12 ∷
   rw 9 q10 ∷
   rw⁻ 8 q12 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 7 q13 ∷
   rw⁻ 6 q14 ∷
   rw 5 q13 ∷
   rw⁻ 4 q15 ∷
   rw 5 q4 ∷
   rw 6 q15 ∷
   rw 7 q16 ∷
   rw 8 q14 ∷
   rw 9 q16 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q12 ∷
   rw 11 q17 ∷
   rw 12 q12 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 6 q18 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   re 5 3 (CCZ023 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 10 q5 ∷
   rw 9 q6 ∷
   rw 8 q7 ∷
   rw 7 q8 ∷
   rw 6 q9 ∷
   rw 5 q8 ∷
   rw 4 q10 ∷
   rw 3 q6 ∷
   rw 4 q11 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 7 q19 ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 13 q20 ∷
   rw 12 q21 ∷
   re 11 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 13 q22 ∷
   rw 10 q19 ∷
   re 11 3 (CX02 ∷ []) ∷
   rw 9 q23 ∷
   rw 8 q19 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q24 ∷
   rw 6 q21 ∷
   rw 7 q25 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q15 ∷
   rw 6 q26 ∷
   rw 7 q14 ∷
   rw 8 q26 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q27 ∷
   rw 11 q12 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q28 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 12 q29 ∷
   rw 11 q30 ∷
   rw 9 q31 ∷
   re 10 5 (CS03 ∷ []) ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 10 q22 ∷
   rw 7 q32 ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 8 q22 ∷
   rw 5 q33 ∷
   rw 6 q34 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q35 ∷
   rw⁻ 8 q36 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q35 ∷
   rw⁻ 10 q36 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q35 ∷
   rw 7 q37 ∷
   re 7 5 (CCZ012 ∷ []) ∷
   re 6 3 (CCZ013 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 11 q20 ∷
   rw 10 q21 ∷
   re 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 11 q22 ∷
   rw 8 q19 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q23 ∷
   rw 6 q19 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 5 q24 ∷
   rw 4 q21 ∷
   rw 5 q25 ∷
   re 5 8 (Toff012 ∷ []) ∷
   rw 5 q38 ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q34 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q36 ∷
   rw 9 q34 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q36 ∷
   rw 11 q34 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q35 ∷
   rw 4 q39 ∷
   rw 7 q19 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 q40 ∷
   rw 9 q19 ∷
   re 7 3 (CX02 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q29 ∷
   rw⁻ 10 q30 ∷
   rw 11 q31 ∷
   re 8 5 (CS03 ∷ []) ∷
   rw 4 q4 ∷
   rw 5 q15 ∷
   rw 6 q16 ∷
   rw 7 q14 ∷
   rw 8 q16 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q17 ∷
   rw 11 q12 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q18 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 4 3 (CCZ023 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q41 ∷
   rw 6 q42 ∷
   rw 7 q43 ∷
   rw 8 q42 ∷
   rw 9 q39 ∷
   rw 5 q44 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   rw 6 q22 ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q15 ∷
   rw 5 q26 ∷
   rw 6 q14 ∷
   rw 7 q26 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q12 ∷
   rw 9 q27 ∷
   rw 10 q12 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q28 ∷
   rw 3 q15 ∷
   rw 4 q16 ∷
   rw 5 q14 ∷
   rw 6 q16 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q12 ∷
   rw 8 q17 ∷
   rw 9 q12 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 3 q18 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q15 ∷
   rw 5 q26 ∷
   rw 6 q14 ∷
   rw 7 q26 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q12 ∷
   rw 9 q27 ∷
   rw 10 q12 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 4 q4 ∷
   rw 5 q15 ∷
   rw 6 q16 ∷
   rw 7 q14 ∷
   rw 8 q16 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q17 ∷
   rw 11 q12 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q18 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 4 3 (CCZ023 ∷ []) ∷
   rw 5 q28 ∷
   rw 1 q3 ∷
   rw 2 q45 ∷
   rw 2 q46 ∷
   rw 4 q47 ∷
   rw 5 q4 ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q15 ∷
   rw 5 q26 ∷
   rw 6 q14 ∷
   rw 7 q26 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q12 ∷
   rw 9 q27 ∷
   rw 10 q12 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q28 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q12 ∷
   rw 9 q7 ∷
   rw⁻ 8 q12 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q48 ∷
   rw⁻ 6 q14 ∷
   rw 5 q48 ∷
   rw⁻ 4 q15 ∷
   rw 5 q18 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 3 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q15 ∷
   rw 4 q26 ∷
   rw 5 q14 ∷
   rw 6 q26 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q12 ∷
   rw 8 q27 ∷
   rw 9 q12 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q28 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q12 ∷
   rw 8 q7 ∷
   rw⁻ 7 q12 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 6 q48 ∷
   rw⁻ 5 q14 ∷
   rw 4 q48 ∷
   rw⁻ 3 q15 ∷
   rw 4 q18 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   rw 4 q49 ∷
   rw 3 q28 ∷
   rw 3 q50 ∷
   rw 2 q51 ∷
   rw 4 q3 ∷
   rw 8 q4 ∷
   re 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 14 q5 ∷
   rw 13 q6 ∷
   rw 12 q7 ∷
   rw 11 q8 ∷
   rw 10 q9 ∷
   rw 9 q8 ∷
   rw 8 q10 ∷
   rw 7 q6 ∷
   rw 8 q11 ∷
   re 8 8 (Toff012 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q12 ∷
   rw 11 q10 ∷
   rw⁻ 10 q12 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 9 q13 ∷
   rw⁻ 8 q14 ∷
   rw 7 q13 ∷
   rw⁻ 6 q15 ∷
   rw 7 q4 ∷
   rw 8 q15 ∷
   rw 9 q16 ∷
   rw 10 q14 ∷
   rw 11 q16 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q12 ∷
   rw 13 q17 ∷
   rw 14 q12 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 8 q18 ∷
   re 8 5 (CCZ123 ∷ []) ∷
   re 7 3 (CCZ023 ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 12 q5 ∷
   rw 11 q6 ∷
   rw 10 q7 ∷
   rw 9 q8 ∷
   rw 8 q9 ∷
   rw 7 q8 ∷
   rw 6 q10 ∷
   rw 5 q6 ∷
   rw 6 q11 ∷
   re 6 8 (Toff012 ∷ []) ∷
   rw 9 q19 ∷
   re 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 15 q20 ∷
   rw 14 q21 ∷
   re 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 15 q22 ∷
   rw 12 q19 ∷
   re 13 3 (CX02 ∷ []) ∷
   rw 11 q23 ∷
   rw 10 q19 ∷
   re 11 3 (CX02 ∷ []) ∷
   rw 9 q24 ∷
   rw 8 q21 ∷
   rw 9 q25 ∷
   re 9 8 (Toff012 ∷ []) ∷
   re 7 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 7 q15 ∷
   rw 8 q26 ∷
   rw 9 q14 ∷
   rw 10 q26 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q12 ∷
   rw 12 q27 ∷
   rw 13 q12 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q28 ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q29 ∷
   rw 13 q30 ∷
   rw 11 q31 ∷
   re 12 5 (CS03 ∷ []) ∷
   re 10 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 12 q22 ∷
   rw 9 q32 ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 10 q22 ∷
   rw 7 q33 ∷
   rw 8 q34 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q35 ∷
   rw⁻ 10 q36 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q35 ∷
   rw⁻ 12 q36 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q35 ∷
   rw 9 q37 ∷
   re 9 5 (CCZ012 ∷ []) ∷
   re 8 3 (CCZ013 ∷ []) ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 13 q20 ∷
   rw 12 q21 ∷
   re 11 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 13 q22 ∷
   rw 10 q19 ∷
   re 11 3 (CX02 ∷ []) ∷
   rw 9 q23 ∷
   rw 8 q19 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q24 ∷
   rw 6 q21 ∷
   rw 7 q25 ∷
   re 7 8 (Toff012 ∷ []) ∷
   rw 7 q38 ∷
   re 7 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 8 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 9 q34 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q36 ∷
   rw 11 q34 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q36 ∷
   rw 13 q34 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q35 ∷
   rw 6 q39 ∷
   rw 9 q19 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 8 q40 ∷
   rw 11 q19 ∷
   re 9 3 (CX02 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q29 ∷
   rw⁻ 12 q30 ∷
   rw 13 q31 ∷
   re 10 5 (CS03 ∷ []) ∷
   rw 6 q4 ∷
   rw 7 q15 ∷
   rw 8 q16 ∷
   rw 9 q14 ∷
   rw 10 q16 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q12 ∷
   rw 12 q17 ∷
   rw 13 q12 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 7 q18 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   re 6 3 (CCZ023 ∷ []) ∷
   re 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 7 q41 ∷
   rw 8 q42 ∷
   rw 9 q43 ∷
   rw 10 q42 ∷
   rw 11 q39 ∷
   rw 7 q44 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   rw 8 q22 ∷
   re 6 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 6 q15 ∷
   rw 7 q26 ∷
   rw 8 q14 ∷
   rw 9 q26 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q12 ∷
   rw 11 q27 ∷
   rw 12 q12 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q28 ∷
   rw 5 q15 ∷
   rw 6 q16 ∷
   rw 7 q14 ∷
   rw 8 q16 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q17 ∷
   rw 11 q12 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q18 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 6 q15 ∷
   rw 7 q26 ∷
   rw 8 q14 ∷
   rw 9 q26 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q12 ∷
   rw 11 q27 ∷
   rw 12 q12 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 6 q4 ∷
   rw 7 q15 ∷
   rw 8 q16 ∷
   rw 9 q14 ∷
   rw 10 q16 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q12 ∷
   rw 12 q17 ∷
   rw 13 q12 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 7 q18 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   re 6 3 (CCZ023 ∷ []) ∷
   rw 7 q28 ∷
   rw 3 q3 ∷
   rw 4 q45 ∷
   rw 4 q46 ∷
   rw 6 q47 ∷
   rw 7 q4 ∷
   re 6 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 6 q15 ∷
   rw 7 q26 ∷
   rw 8 q14 ∷
   rw 9 q26 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q12 ∷
   rw 11 q27 ∷
   rw 12 q12 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q28 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q12 ∷
   rw 11 q7 ∷
   rw⁻ 10 q12 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 9 q48 ∷
   rw⁻ 8 q14 ∷
   rw 7 q48 ∷
   rw⁻ 6 q15 ∷
   rw 7 q18 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   re 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q15 ∷
   rw 6 q26 ∷
   rw 7 q14 ∷
   rw 8 q26 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q27 ∷
   rw 11 q12 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q28 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q12 ∷
   rw 10 q7 ∷
   rw⁻ 9 q12 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 8 q48 ∷
   rw⁻ 7 q14 ∷
   rw 6 q48 ∷
   rw⁻ 5 q15 ∷
   rw 6 q18 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   rw 6 q49 ∷
   rw 5 q28 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q53 : Eqn
  q53 = wE 173 W
  q54 : Eqn
  q54 = wE 1833 W
  q55 : Eqn
  q55 = wE 175 W
  q56 : Eqn
  q56 = wE 1677 W
  q57 : Eqn
  q57 = wE 1834 W
  q58 : Eqn
  q58 = sE 1386 lem-pass-X3-CKd31-X3-vs-CS13-TOFF102-CSd13-TOFF102

-- pass [X3 CKd31 X3] [X0 X2 CS13 TOFF102 CSd13 TOFF102 X0 X2]: 31 steps
lem-pass-X3-CKd31-X3-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd31-X3-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 = derive (X3 ∷ CK31⁻ ∷ X3 ∷ X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ [])
  (rw 4 q34 ∷
   rw 3 q52 ∷
   rw 2 q53 ∷
   re 1 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q35 ∷
   rw 0 q53 ∷
   rw 1 q54 ∷
   rw⁻ 0 q52 ∷
   rw 1 q55 ∷
   rw 4 q34 ∷
   re 2 3 (CK31⁻ ∷ []) ∷
   rw 3 q55 ∷
   rw 4 q35 ∷
   rw 1 q56 ∷
   rw 2 q57 ∷
   rw 2 q58 ∷
   rw 6 q57 ∷
   rw 10 q34 ∷
   rw 9 q52 ∷
   rw 8 q53 ∷
   re 7 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q35 ∷
   rw 6 q53 ∷
   rw 7 q54 ∷
   rw⁻ 6 q52 ∷
   rw 7 q55 ∷
   rw 10 q34 ∷
   re 8 3 (CK31⁻ ∷ []) ∷
   rw 9 q55 ∷
   rw 10 q35 ∷
   rw 7 q56 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = wE 1478 W
  q60 : Eqn
  q60 = sE 1389 lem-pass-X2-CKd21-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0
  q61 : Eqn
  q61 = wE 1479 W

-- pass [CKd21] [X2 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2]: 3 steps
lem-pass-CKd21-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 : ⟪ (CK21⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK21⁻ ∷ []) ⟫ʷ
lem-pass-CKd21-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 = derive (CK21⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ []) (X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK21⁻ ∷ [])
  (rw 0 q59 ∷
   rw 1 q60 ∷
   rw 13 q61 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = wE 1476 W
  q63 : Eqn
  q63 = sE 1388 lem-pass-X2-CK21-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0
  q64 : Eqn
  q64 = wE 1477 W

-- pass [CK21] [X2 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2]: 3 steps
lem-pass-CK21-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 : ⟪ (CK21 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK21 ∷ []) ⟫ʷ
lem-pass-CK21-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 = derive (CK21 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ []) (X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK21 ∷ [])
  (rw 0 q62 ∷
   rw 1 q63 ∷
   rw 13 q64 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = wE 1835 W
  q66 : Eqn
  q66 = sE 1191 lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012
  q67 : Eqn
  q67 = wE 1836 W

-- pass [X1 CSd10 X1] [Sd0 Kd0 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 K0 S0]: 3 steps
lem-pass-X1-CSd10-X1-vs-Sd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-S0 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-Sd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-S0 = derive (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  (rw 0 q65 ∷
   rw 3 q66 ∷
   rw 7 q67 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = wE 1837 W
  q69 : Eqn
  q69 = wE 1838 W

-- pass [X1 CSd10 X1] [Sd0 K0 K0 K0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Kd0 Kd0 Kd0 S0]: 3 steps
lem-pass-X1-CSd10-X1-vs-Sd0-K0-K0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-Kd0-Kd0-S0 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-Sd0-K0-K0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-Kd0-Kd0-S0 = derive (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  (rw 0 q68 ∷
   rw 5 q66 ∷
   rw 9 q69 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = wE 1817 W
  q71 : Eqn
  q71 = sE 1387 lem-pass-X1-CS10-X1-vs-Sd0-K0-K0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-Kd0-Kd0-S0
  q72 : Eqn
  q72 = wE 1839 W
  q73 : Eqn
  q73 = wE 1840 W
  q74 : Eqn
  q74 = wE 1818 W

-- CA CSd10 Gad(t=0, W=(), d=SdKKKK, e=1): 5 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKKKK-e≡1⟩ : ⟪ (CS01⁻ ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKKKK-e≡1⟩ = derive (CS01⁻ ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ CS01⁻ ∷ [])
  (rw 0 q70 ∷
   rw 1 q71 ∷
   rw 0 q72 ∷
   rw 10 q73 ∷
   rw 16 q74 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = wE 1841 W
  q76 : Eqn
  q76 = wE 1842 W
  q77 : Eqn
  q77 = wE 1843 W
  q78 : Eqn
  q78 = wE 1738 W
  q79 : Eqn
  q79 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q80 : Eqn
  q80 = wE 1739 W
  q81 : Eqn
  q81 = wE 1740 W
  q82 : Eqn
  q82 = sE 1110 lem-pass-S0-vs-TOFF012-CS03-TOFF012-CSd03
  q83 : Eqn
  q83 = wE 1844 W

-- spell Gad(t=0, W=(), d=SdKSdK, e=1) -> Gad(t=0, W=(), d=KdSd, e=1): 46 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdKSdK-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡KdSd-e≡1⟩ : ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdKSdK-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡KdSd-e≡1⟩ = derive (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ [])
  (rw 0 q75 ∷
   rw 12 q76 ∷
   rw 2 q77 ∷
   rw 5 q78 ∷
   rw 8 q34 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q35 ∷
   rw 6 q79 ∷
   rw 7 q80 ∷
   rw 8 q34 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q79 ∷
   rw 8 q35 ∷
   rw 7 q78 ∷
   rw 10 q34 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q35 ∷
   rw 8 q79 ∷
   rw 9 q81 ∷
   rw 10 q34 ∷
   re 8 3 (CS03⁻ ∷ []) ∷
   rw⁻ 9 q79 ∷
   rw 10 q35 ∷
   rw 4 q78 ∷
   rw 7 q34 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q35 ∷
   rw 5 q79 ∷
   rw 6 q80 ∷
   rw 7 q34 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q79 ∷
   rw 7 q35 ∷
   rw 6 q78 ∷
   rw 9 q34 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q35 ∷
   rw 7 q79 ∷
   rw 8 q81 ∷
   rw 9 q34 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw⁻ 8 q79 ∷
   rw 9 q35 ∷
   rw 3 q82 ∷
   rw 2 q82 ∷
   rw 6 q83 ∷ []) Eq.refl

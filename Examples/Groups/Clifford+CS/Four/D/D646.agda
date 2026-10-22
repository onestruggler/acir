{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD646 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D646 (W : Ws) (Sᴰ : SD646) where

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
  lem-pass-CS03-vs-CZ23 : St 1342
  lem-pass-CS03-vs-CZ23 = pickᴰ 0 Sᴰ
  lem-pass-CSd03-vs-CZ23 : St 1348
  lem-pass-CSd03-vs-CZ23 = pickᴰ 1 Sᴰ
  lem-pass-CCZ023-vs-CS02 : St 1591
  lem-pass-CCZ023-vs-CS02 = pickᴰ 2 Sᴰ
  lem-pass-CCZ023-vs-CSd02 : St 1592
  lem-pass-CCZ023-vs-CSd02 = pickᴰ 3 Sᴰ
  lem-pass-CCZ123-vs-CSd03 : St 861
  lem-pass-CCZ123-vs-CSd03 = pickᴰ 4 Sᴰ
  lem-pass-CCZ123-vs-CS03 : St 843
  lem-pass-CCZ123-vs-CS03 = pickᴰ 5 Sᴰ
  lem-pass-CCZ123-vs-CS02 : St 1593
  lem-pass-CCZ123-vs-CS02 = pickᴰ 6 Sᴰ
  lem-pass-TOFF012-vs-CZ23 : St 1364
  lem-pass-TOFF012-vs-CZ23 = pickᴰ 7 Sᴰ
  lem-pass-CCZ123-vs-TOFF012 : St 1444
  lem-pass-CCZ123-vs-TOFF012 = pickᴰ 8 Sᴰ
  lem-pass-CCZ123-vs-TOFF013 : St 1465
  lem-pass-CCZ123-vs-TOFF013 = pickᴰ 9 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 45 W
  q3 : Eqn
  q3 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q4 : Eqn
  q4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q5 : Eqn
  q5 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 56 W
  q8 : Eqn
  q8 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q9 : Eqn
  q9 = wE 30 W
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q11 : Eqn
  q11 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q12 : Eqn
  q12 = wE 27 W
  q13 : Eqn
  q13 = wE 31 W
  q14 : Eqn
  q14 = wE 1882 W
  q15 : Eqn
  q15 = wE 1883 W
  q16 : Eqn
  q16 = wE 5 W
  q17 : Eqn
  q17 = wE 24 W
  q18 : Eqn
  q18 = wE 25 W
  q19 : Eqn
  q19 = wE 73 W
  q20 : Eqn
  q20 = wE 12 W
  q21 : Eqn
  q21 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q22 : Eqn
  q22 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap))
  q23 : Eqn
  q23 = wE 14 W
  q24 : Eqn
  q24 = wE 15 W
  q25 : Eqn
  q25 = wE 16 W
  q26 : Eqn
  q26 = wE 46 W
  q27 : Eqn
  q27 = wE 22 W
  q28 : Eqn
  q28 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q29 : Eqn
  q29 = wE 23 W
  q30 : Eqn
  q30 = wE 47 W
  q31 : Eqn
  q31 = wE 48 W
  q32 : Eqn
  q32 = wE 43 W
  q33 : Eqn
  q33 = eqn (Toff012 ∷ CCZ013 ∷ Toff012 ∷ []) (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz)
  q34 : Eqn
  q34 = wE 20 W
  q35 : Eqn
  q35 = wE 21 W
  q36 : Eqn
  q36 = wE 26 W
  q37 : Eqn
  q37 = wE 49 W
  q38 : Eqn
  q38 = wE 50 W
  q39 : Eqn
  q39 = wE 51 W
  q40 : Eqn
  q40 = wE 52 W
  q41 : Eqn
  q41 = wE 71 W
  q42 : Eqn
  q42 = wE 72 W
  q43 : Eqn
  q43 = sE 1593 lem-pass-CCZ123-vs-CS02
  q44 : Eqn
  q44 = sE 1591 lem-pass-CCZ023-vs-CS02
  q45 : Eqn
  q45 = sE 1465 lem-pass-CCZ123-vs-TOFF013
  q46 : Eqn
  q46 = wE 33 W
  q47 : Eqn
  q47 = sE 1592 lem-pass-CCZ023-vs-CSd02

-- pass [CCZ023] [TOFF013 CS02 TOFF013 CSd02]: 619 steps
lem-pass-CCZ023-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (CCZ023 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ CCZ023 ∷ []) ⟫ʷ
lem-pass-CCZ023-vs-TOFF013-CS02-TOFF013-CSd02 = derive (CCZ023 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ CCZ023 ∷ [])
  (rw 0 q1 ∷
   rw 1 q2 ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q3 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw⁻ 7 q5 ∷
   rw 0 q1 ∷
   rw⁻ 1 q3 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw⁻ 3 q4 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 1 q7 ∷
   re 1 8 (Toff012 ∷ []) ∷
   re 0 3 (Toff013 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 1 q1 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q7 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 2 q6 ∷
   rw 4 q1 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q5 ∷
   rw 11 q6 ∷
   rw 10 q5 ∷
   rw 9 q3 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 7 q4 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 3 q3 ∷
   rw 4 q7 ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 2 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 2 q8 ∷
   rw 3 q9 ∷
   rw 4 q10 ∷
   rw 5 q9 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q11 ∷
   rw 7 q12 ∷
   rw 8 q11 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q13 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q1 ∷
   re 6 3 (CX03 ∷ []) ∷
   rw 4 q14 ∷
   rw 3 q1 ∷
   re 4 3 (CX03 ∷ []) ∷
   rw 2 q15 ∷
   rw 3 q16 ∷
   rw 4 q8 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 q11 ∷
   rw 6 q17 ∷
   rw 7 q11 ∷
   re 5 3 (CX13 ∷ []) ∷
   rw 6 q10 ∷
   re 8 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 7 q11 ∷
   rw 8 q17 ∷
   rw 9 q11 ∷
   re 7 3 (CX13 ∷ []) ∷
   rw 8 q18 ∷
   rw 4 q19 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   re 3 3 (CCZ023 ∷ []) ∷
   re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 9 q6 ∷
   rw 8 q5 ∷
   rw 7 q3 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 3 q4 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 1 q3 ∷
   rw 2 q7 ∷
   re 2 8 (Toff012 ∷ []) ∷
   rw 5 q20 ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 11 q21 ∷
   rw 10 q22 ∷
   re 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 11 q23 ∷
   rw 8 q20 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q24 ∷
   rw 6 q20 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 5 q25 ∷
   rw 4 q22 ∷
   rw 5 q26 ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 3 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q8 ∷
   rw 4 q9 ∷
   rw 5 q10 ∷
   rw 6 q9 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q11 ∷
   rw 8 q12 ∷
   rw 9 q11 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q13 ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q27 ∷
   rw 9 q28 ∷
   rw 7 q29 ∷
   re 8 5 (CS03 ∷ []) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 8 q23 ∷
   rw 5 q30 ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 q23 ∷
   rw 3 q31 ∷
   rw 4 q1 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw⁻ 8 q4 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 5 q32 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   re 4 3 (CCZ013 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 9 q21 ∷
   rw 8 q22 ∷
   re 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 9 q23 ∷
   rw 6 q20 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 5 q24 ∷
   rw 4 q20 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 3 q25 ∷
   rw 2 q22 ∷
   rw 3 q26 ∷
   re 3 8 (Toff012 ∷ []) ∷
   rw 3 q33 ∷
   re 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q6 ∷
   rw 2 q34 ∷
   rw 5 q20 ∷
   re 3 3 (CX02 ∷ []) ∷
   rw 4 q35 ∷
   rw 7 q20 ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 6 q27 ∷
   rw⁻ 8 q28 ∷
   rw 9 q29 ∷
   re 6 5 (CS03 ∷ []) ∷
   rw 2 q16 ∷
   rw 3 q8 ∷
   rw 4 q17 ∷
   rw 5 q10 ∷
   rw 6 q17 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q11 ∷
   rw 8 q18 ∷
   rw 9 q11 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 3 q36 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   re 2 3 (CCZ023 ∷ []) ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q37 ∷
   rw 4 q38 ∷
   rw 5 q39 ∷
   rw 6 q38 ∷
   rw 7 q34 ∷
   rw 3 q40 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   rw 4 q23 ∷
   re 2 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 2 q8 ∷
   rw 3 q9 ∷
   rw 4 q10 ∷
   rw 5 q9 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q11 ∷
   rw 7 q12 ∷
   rw 8 q11 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q13 ∷
   rw 1 q41 ∷
   rw 4 q1 ∷
   re 2 3 (CX03 ∷ []) ∷
   rw 3 q42 ∷
   rw 6 q1 ∷
   re 4 3 (CX03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 1 q16 ∷
   rw 2 q8 ∷
   re 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 3 q11 ∷
   rw 4 q17 ∷
   rw 5 q11 ∷
   re 3 3 (CX13 ∷ []) ∷
   rw 4 q10 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 q11 ∷
   rw 6 q17 ∷
   rw 7 q11 ∷
   re 5 3 (CX13 ∷ []) ∷
   rw 6 q18 ∷
   rw 2 q19 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 1 3 (CCZ023 ∷ []) ∷
   re 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 2 q41 ∷
   rw 5 q1 ∷
   re 3 3 (CX13 ∷ []) ∷
   rw 4 q42 ∷
   rw 7 q1 ∷
   re 5 3 (CX13 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 2 q19 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   rw 3 q6 ∷
   rw 2 q43 ∷
   rw 1 q44 ∷
   rw 3 q45 ∷
   rw 2 q1 ∷
   rw 3 q2 ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q1 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q5 ∷
   rw 3 q7 ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 2 3 (Toff013 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q5 ∷
   rw 3 q1 ∷
   rw⁻ 4 q3 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw⁻ 8 q4 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw⁻ 10 q3 ∷
   rw⁻ 11 q5 ∷
   rw 4 q7 ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 3 3 (Toff013 ∷ []) ∷
   rw 4 q6 ∷
   rw 6 q1 ∷
   re 5 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q3 ∷
   rw⁻ 12 q5 ∷
   rw 13 q6 ∷
   rw 12 q5 ∷
   rw 11 q3 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw 9 q4 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 7 q4 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q3 ∷
   rw 6 q7 ∷
   re 6 8 (Toff012 ∷ []) ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q8 ∷
   rw 5 q9 ∷
   rw 6 q10 ∷
   rw 7 q9 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q11 ∷
   rw 9 q12 ∷
   rw 10 q11 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q13 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 7 q1 ∷
   re 8 3 (CX03 ∷ []) ∷
   rw 6 q14 ∷
   rw 5 q1 ∷
   re 6 3 (CX03 ∷ []) ∷
   rw 4 q15 ∷
   rw 5 q16 ∷
   rw 6 q8 ∷
   re 8 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 7 q11 ∷
   rw 8 q17 ∷
   rw 9 q11 ∷
   re 7 3 (CX13 ∷ []) ∷
   rw 8 q10 ∷
   re 10 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 9 q11 ∷
   rw 10 q17 ∷
   rw 11 q11 ∷
   re 9 3 (CX13 ∷ []) ∷
   rw 10 q18 ∷
   rw 6 q19 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   re 5 3 (CCZ023 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q5 ∷
   rw 11 q6 ∷
   rw 10 q5 ∷
   rw 9 q3 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 7 q4 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 3 q3 ∷
   rw 4 q7 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 7 q20 ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 13 q21 ∷
   rw 12 q22 ∷
   re 11 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 13 q23 ∷
   rw 10 q20 ∷
   re 11 3 (CX02 ∷ []) ∷
   rw 9 q24 ∷
   rw 8 q20 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q25 ∷
   rw 6 q22 ∷
   rw 7 q26 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q8 ∷
   rw 6 q9 ∷
   rw 7 q10 ∷
   rw 8 q9 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q11 ∷
   rw 10 q12 ∷
   rw 11 q11 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q13 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 12 q27 ∷
   rw 11 q28 ∷
   rw 9 q29 ∷
   re 10 5 (CS03 ∷ []) ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 10 q23 ∷
   rw 7 q30 ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 8 q23 ∷
   rw 5 q31 ∷
   rw 6 q1 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw⁻ 8 q4 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw⁻ 10 q4 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   rw 7 q32 ∷
   re 7 5 (CCZ012 ∷ []) ∷
   re 6 3 (CCZ013 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 11 q21 ∷
   rw 10 q22 ∷
   re 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 11 q23 ∷
   rw 8 q20 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q24 ∷
   rw 6 q20 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 5 q25 ∷
   rw 4 q22 ∷
   rw 5 q26 ∷
   re 5 8 (Toff012 ∷ []) ∷
   rw 5 q33 ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q6 ∷
   rw 4 q34 ∷
   rw 7 q20 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 q35 ∷
   rw 9 q20 ∷
   re 7 3 (CX02 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q27 ∷
   rw⁻ 10 q28 ∷
   rw 11 q29 ∷
   re 8 5 (CS03 ∷ []) ∷
   rw 4 q16 ∷
   rw 5 q8 ∷
   rw 6 q17 ∷
   rw 7 q10 ∷
   rw 8 q17 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q11 ∷
   rw 10 q18 ∷
   rw 11 q11 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q36 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 4 3 (CCZ023 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q37 ∷
   rw 6 q38 ∷
   rw 7 q39 ∷
   rw 8 q38 ∷
   rw 9 q34 ∷
   rw 5 q40 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   rw 6 q23 ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q8 ∷
   rw 5 q9 ∷
   rw 6 q10 ∷
   rw 7 q9 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q11 ∷
   rw 9 q12 ∷
   rw 10 q11 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q13 ∷
   rw 3 q41 ∷
   rw 6 q1 ∷
   re 4 3 (CX03 ∷ []) ∷
   rw 5 q42 ∷
   rw 8 q1 ∷
   re 6 3 (CX03 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 3 q16 ∷
   rw 4 q8 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 q11 ∷
   rw 6 q17 ∷
   rw 7 q11 ∷
   re 5 3 (CX13 ∷ []) ∷
   rw 6 q10 ∷
   re 8 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 7 q11 ∷
   rw 8 q17 ∷
   rw 9 q11 ∷
   re 7 3 (CX13 ∷ []) ∷
   rw 8 q18 ∷
   rw 4 q19 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   re 3 3 (CCZ023 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q41 ∷
   rw 7 q1 ∷
   re 5 3 (CX13 ∷ []) ∷
   rw 6 q42 ∷
   rw 9 q1 ∷
   re 7 3 (CX13 ∷ []) ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 4 q19 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   rw 5 q6 ∷
   rw 4 q46 ∷
   rw 3 q47 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = sE 1444 lem-pass-CCZ123-vs-TOFF012
  q49 : Eqn
  q49 = sE 1364 lem-pass-TOFF012-vs-CZ23
  q50 : Eqn
  q50 = sE 843 lem-pass-CCZ123-vs-CS03
  q51 : Eqn
  q51 = sE 1342 lem-pass-CS03-vs-CZ23
  q52 : Eqn
  q52 = sE 861 lem-pass-CCZ123-vs-CSd03
  q53 : Eqn
  q53 = sE 1348 lem-pass-CSd03-vs-CZ23

-- pass [CZ23 CCZ123] [TOFF012 CS03 TOFF012 CSd03]: 8 steps
lem-pass-CZ23-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (CZ23 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CZ23 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CZ23-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03 = derive (CZ23 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CZ23 ∷ CCZ123 ∷ [])
  (rw 1 q48 ∷
   rw⁻ 0 q49 ∷
   rw 2 q50 ∷
   rw⁻ 1 q51 ∷
   rw 3 q48 ∷
   rw⁻ 2 q49 ∷
   rw 4 q52 ∷
   rw⁻ 3 q53 ∷ []) Eq.refl

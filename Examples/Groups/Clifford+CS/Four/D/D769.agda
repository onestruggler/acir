{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD769 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D769 (W : Ws) (Sᴰ : SD769) where

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
  lem-merge-R0 : St 3093
  lem-merge-R0 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = wE 2549 W
  q4 : Eqn
  q4 = wE 1731 W
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
  q13 = wE 1207 W
  q14 : Eqn
  q14 = sE 3093 lem-merge-R0
  q15 : Eqn
  q15 = wE 29 W
  q16 : Eqn
  q16 = wE 311 W
  q17 : Eqn
  q17 = wE 123 W
  q18 : Eqn
  q18 = wE 27 W
  q19 : Eqn
  q19 = wE 28 W
  q20 : Eqn
  q20 = wE 25 W
  q21 : Eqn
  q21 = wE 124 W
  q22 : Eqn
  q22 = wE 274 W
  q23 : Eqn
  q23 = wE 312 W
  q24 : Eqn
  q24 = wE 31 W

-- merge R0 @1023: 91 steps
lem-merge-R0-at1023 : ⟪ (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ []) ⟫ʷ
lem-merge-R0-at1023 = derive (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ [])
  (rw 18 q1 ∷
   rw⁻ 17 q2 ∷
   rw 16 q3 ∷
   rw 15 q4 ∷
   re 14 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 21 q5 ∷
   rw 20 q6 ∷
   rw 19 q7 ∷
   rw 18 q8 ∷
   rw 17 q9 ∷
   rw 16 q8 ∷
   rw 15 q10 ∷
   rw 14 q6 ∷
   rw 15 q11 ∷
   re 15 8 (Toff012 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q12 ∷
   rw 14 q9 ∷
   rw⁻ 13 q12 ∷
   re 14 3 (CS03⁻ ∷ []) ∷
   re 12 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 19 q5 ∷
   rw 18 q6 ∷
   rw 17 q7 ∷
   rw 16 q8 ∷
   rw 15 q9 ∷
   rw 14 q8 ∷
   rw 13 q10 ∷
   rw 12 q6 ∷
   rw 13 q11 ∷
   re 13 8 (Toff012 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q12 ∷
   rw 12 q10 ∷
   rw⁻ 11 q12 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 10 q6 ∷
   rw 9 q13 ∷
   rw⁻ 8 q2 ∷
   rw 7 q3 ∷
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
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q12 ∷
   rw 5 q9 ∷
   rw⁻ 4 q12 ∷
   re 5 3 (CS03⁻ ∷ []) ∷
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
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q12 ∷
   rw 3 q10 ∷
   rw⁻ 2 q12 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 1 q6 ∷
   rw 0 q13 ∷
   rw 1 q14 ∷
   rw 0 q15 ∷
   rw 1 q16 ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 2 q17 ∷
   rw 3 q18 ∷
   rw 4 q19 ∷
   rw 5 q15 ∷
   rw 6 q19 ∷
   rw 7 q20 ∷
   rw 8 q17 ∷
   rw 9 q21 ∷
   rw 2 q22 ∷
   re 2 8 (Toff102 ∷ []) ∷
   rw 3 q23 ∷
   rw 4 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = wE 12 W
  q26 : Eqn
  q26 = eqn (Sw12 ∷ X3 ∷ []) (X3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (X))
  q27 : Eqn
  q27 = wE 2573 W
  q28 : Eqn
  q28 = wE 2574 W
  q29 : Eqn
  q29 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q30 : Eqn
  q30 = wE 398 W
  q31 : Eqn
  q31 = wE 14 W
  q32 : Eqn
  q32 = wE 15 W
  q33 : Eqn
  q33 = wE 16 W
  q34 : Eqn
  q34 = wE 366 W
  q35 : Eqn
  q35 = wE 47 W
  q36 : Eqn
  q36 = wE 48 W
  q37 : Eqn
  q37 = wE 477 W
  q38 : Eqn
  q38 = wE 338 W
  q39 : Eqn
  q39 = wE 340 W
  q40 : Eqn
  q40 = wE 18 W
  q41 : Eqn
  q41 = wE 19 W
  q42 : Eqn
  q42 = wE 363 W
  q43 : Eqn
  q43 = wE 339 W

-- merge R0 @2013: 181 steps
lem-merge-R0-at2013 : ⟪ (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) ⟫ʷ
lem-merge-R0-at2013 = derive (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ []) (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ [])
  (rw 18 q25 ∷
   rw⁻ 17 q26 ∷
   rw 16 q27 ∷
   rw 15 q28 ∷
   re 14 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 21 q29 ∷
   rw 20 q30 ∷
   re 19 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 21 q31 ∷
   rw 18 q25 ∷
   re 19 3 (CX02 ∷ []) ∷
   rw 17 q32 ∷
   rw 16 q25 ∷
   re 17 3 (CX02 ∷ []) ∷
   rw 15 q33 ∷
   rw 14 q30 ∷
   rw 15 q34 ∷
   re 15 8 (Toff102 ∷ []) ∷
   rw 13 q35 ∷
   re 12 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 19 q29 ∷
   rw 18 q30 ∷
   re 17 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 19 q31 ∷
   rw 16 q25 ∷
   re 17 3 (CX02 ∷ []) ∷
   rw 15 q32 ∷
   rw 14 q25 ∷
   re 15 3 (CX02 ∷ []) ∷
   rw 13 q33 ∷
   rw 12 q30 ∷
   rw 13 q34 ∷
   re 13 8 (Toff102 ∷ []) ∷
   rw 11 q36 ∷
   rw 10 q30 ∷
   rw 9 q37 ∷
   rw⁻ 8 q26 ∷
   rw 7 q27 ∷
   rw 6 q28 ∷
   re 5 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 12 q29 ∷
   rw 11 q30 ∷
   re 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 12 q31 ∷
   rw 9 q25 ∷
   re 10 3 (CX02 ∷ []) ∷
   rw 8 q32 ∷
   rw 7 q25 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q33 ∷
   rw 5 q30 ∷
   rw 6 q34 ∷
   re 6 8 (Toff102 ∷ []) ∷
   rw 4 q35 ∷
   re 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 10 q29 ∷
   rw 9 q30 ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 10 q31 ∷
   rw 7 q25 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q32 ∷
   rw 5 q25 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q33 ∷
   rw 3 q30 ∷
   rw 4 q34 ∷
   re 4 8 (Toff102 ∷ []) ∷
   rw 2 q36 ∷
   rw 1 q30 ∷
   rw 0 q37 ∷
   rw 19 q1 ∷
   rw⁻ 18 q2 ∷
   rw 17 q3 ∷
   rw 16 q4 ∷
   re 15 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 22 q5 ∷
   rw 21 q6 ∷
   rw 20 q7 ∷
   rw 19 q8 ∷
   rw 18 q9 ∷
   rw 17 q8 ∷
   rw 16 q10 ∷
   rw 15 q6 ∷
   rw 16 q11 ∷
   re 16 8 (Toff012 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q12 ∷
   rw 15 q9 ∷
   rw⁻ 14 q12 ∷
   re 15 3 (CS03⁻ ∷ []) ∷
   re 13 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 20 q5 ∷
   rw 19 q6 ∷
   rw 18 q7 ∷
   rw 17 q8 ∷
   rw 16 q9 ∷
   rw 15 q8 ∷
   rw 14 q10 ∷
   rw 13 q6 ∷
   rw 14 q11 ∷
   re 14 8 (Toff012 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q12 ∷
   rw 13 q10 ∷
   rw⁻ 12 q12 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 11 q6 ∷
   rw 10 q13 ∷
   rw⁻ 9 q2 ∷
   rw 8 q3 ∷
   rw 7 q4 ∷
   re 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 13 q5 ∷
   rw 12 q6 ∷
   rw 11 q7 ∷
   rw 10 q8 ∷
   rw 9 q9 ∷
   rw 8 q8 ∷
   rw 7 q10 ∷
   rw 6 q6 ∷
   rw 7 q11 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q12 ∷
   rw 6 q9 ∷
   rw⁻ 5 q12 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   rw 9 q7 ∷
   rw 8 q8 ∷
   rw 7 q9 ∷
   rw 6 q8 ∷
   rw 5 q10 ∷
   rw 4 q6 ∷
   rw 5 q11 ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q12 ∷
   rw 4 q10 ∷
   rw⁻ 3 q12 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 2 q6 ∷
   rw 1 q13 ∷
   rw 2 q14 ∷
   rw 1 q15 ∷
   rw 2 q16 ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 3 q17 ∷
   rw 4 q18 ∷
   rw 5 q19 ∷
   rw 6 q15 ∷
   rw 7 q19 ∷
   rw 8 q20 ∷
   rw 9 q17 ∷
   rw 10 q21 ∷
   rw 3 q22 ∷
   re 3 8 (Toff102 ∷ []) ∷
   rw 4 q23 ∷
   rw 5 q24 ∷
   re 1 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 0 q31 ∷
   rw 1 q38 ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 2 q39 ∷
   rw 3 q40 ∷
   rw 6 q25 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 q41 ∷
   rw 8 q25 ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 q31 ∷
   rw 8 q39 ∷
   rw⁻ 9 q29 ∷
   rw 2 q42 ∷
   re 2 8 (Toff201 ∷ []) ∷
   rw 3 q43 ∷
   rw 4 q31 ∷ []) Eq.refl

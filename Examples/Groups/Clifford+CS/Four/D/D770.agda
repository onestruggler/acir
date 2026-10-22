{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD770 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D770 (W : Ws) (Sᴰ : SD770) where

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
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn (X2 ∷ Sw23 ∷ []) (Sw23 ∷ X3 ∷ []) (wn 1609 W)
  q3 : Eqn
  q3 = eqn (S3⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S2⁻ ∷ []) (wn 689 W)
  q4 : Eqn
  q4 = eqn (K3⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K2⁻ ∷ []) (wn 1810 W)
  q5 : Eqn
  q5 = eqn (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) (wn 335 W)
  q6 : Eqn
  q6 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q7 : Eqn
  q7 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q8 : Eqn
  q8 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q9 : Eqn
  q9 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wn 1294 W)
  q10 : Eqn
  q10 = eqn (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (wn 368 W)
  q11 : Eqn
  q11 = eqn (CS23⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS23⁻ ∷ []) (wn 1882 W)
  q12 : Eqn
  q12 = eqn (CS23 ∷ Sw23 ∷ []) (Sw23 ∷ CS23 ∷ []) (wn 1883 W)
  q13 : Eqn
  q13 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q14 : Eqn
  q14 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q15 : Eqn
  q15 = eqn (Sw12 ∷ X3 ∷ []) (X3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (X))
  q16 : Eqn
  q16 = eqn (S2⁻ ∷ Sw12 ∷ []) (Sw12 ∷ S1⁻ ∷ []) (wn 2573 W)
  q17 : Eqn
  q17 = eqn (K2⁻ ∷ Sw12 ∷ []) (Sw12 ∷ K1⁻ ∷ []) (wn 2574 W)
  q18 : Eqn
  q18 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q19 : Eqn
  q19 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wn 398 W)
  q20 : Eqn
  q20 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q21 : Eqn
  q21 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wn 15 W)
  q22 : Eqn
  q22 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wn 16 W)
  q23 : Eqn
  q23 = eqn (K1 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 366 W)
  q24 : Eqn
  q24 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wn 47 W)
  q25 : Eqn
  q25 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)
  q26 : Eqn
  q26 = eqn (S2 ∷ Sw12 ∷ []) (Sw12 ∷ S1 ∷ []) (wn 477 W)
  q27 : Eqn
  q27 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q28 : Eqn
  q28 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q29 : Eqn
  q29 = eqn (S1⁻ ∷ Sw01 ∷ []) (Sw01 ∷ S0⁻ ∷ []) (wn 2549 W)
  q30 : Eqn
  q30 = eqn (K1⁻ ∷ Sw01 ∷ []) (Sw01 ∷ K0⁻ ∷ []) (wn 1731 W)
  q31 : Eqn
  q31 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q32 : Eqn
  q32 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wn 271 W)
  q33 : Eqn
  q33 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q34 : Eqn
  q34 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wn 8 W)
  q35 : Eqn
  q35 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wn 9 W)
  q36 : Eqn
  q36 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q37 : Eqn
  q37 = eqn (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 272 W)
  q38 : Eqn
  q38 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q39 : Eqn
  q39 = eqn (S1 ∷ Sw01 ∷ []) (Sw01 ∷ S0 ∷ []) (wn 1207 W)
  q40 : Eqn
  q40 = eqn (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (lem-merge-R0)
  q41 : Eqn
  q41 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q42 : Eqn
  q42 = eqn (Sw01 ∷ S0 ∷ []) (S1 ∷ Sw01 ∷ []) (wn 311 W)
  q43 : Eqn
  q43 = eqn (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) (wn 123 W)
  q44 : Eqn
  q44 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q45 : Eqn
  q45 = eqn (Sw01 ∷ CX01 ∷ []) (CX10 ∷ Sw01 ∷ []) (wn 28 W)
  q46 : Eqn
  q46 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q47 : Eqn
  q47 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q48 : Eqn
  q48 = eqn (K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 274 W)
  q49 : Eqn
  q49 = eqn (Sw01 ∷ S0⁻ ∷ []) (S1⁻ ∷ Sw01 ∷ []) (wn 312 W)
  q50 : Eqn
  q50 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q51 : Eqn
  q51 = eqn (Sw12 ∷ S1 ∷ []) (S2 ∷ Sw12 ∷ []) (wn 338 W)
  q52 : Eqn
  q52 = eqn (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) (wn 340 W)
  q53 : Eqn
  q53 = eqn (Sw12 ∷ CS12 ∷ []) (CS12 ∷ Sw12 ∷ []) (wn 18 W)
  q54 : Eqn
  q54 = eqn (Sw12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sw12 ∷ []) (wn 19 W)
  q55 : Eqn
  q55 = eqn (K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (wn 363 W)
  q56 : Eqn
  q56 = eqn (Sw12 ∷ S1⁻ ∷ []) (S2⁻ ∷ Sw12 ∷ []) (wn 339 W)
  q57 : Eqn
  q57 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q58 : Eqn
  q58 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)
  q59 : Eqn
  q59 = eqn (Sw23 ∷ K3 ∷ []) (K2 ∷ Sw23 ∷ []) (wn 336 W)
  q60 : Eqn
  q60 = eqn (Sw23 ∷ S2⁻ ∷ []) (S3⁻ ∷ Sw23 ∷ []) (wn 153 W)

-- merge R0 @3012: 335 steps
lem-merge-R0-at3012 : ⟪ (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) ⟫ʷ
lem-merge-R0-at3012 = derive (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ []) (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ [])
  (rw 18 q1 ∷
   rw 17 q2 ∷
   rw 16 q3 ∷
   rw 15 q4 ∷
   re 14 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 15 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 14 q5 ∷
   rw 17 q1 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw⁻ 16 q6 ∷
   rw 19 q1 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw⁻ 18 q6 ∷
   rw 21 q1 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 20 q5 ∷
   rw⁻ 21 q7 ∷
   rw 22 q8 ∷
   rw 21 q7 ∷
   rw 20 q9 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q8 ∷
   rw 18 q6 ∷
   re 17 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q8 ∷
   rw 16 q6 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q8 ∷
   rw 14 q9 ∷
   rw 15 q10 ∷
   re 15 8 (Toff201 ∷ []) ∷
   rw 13 q11 ∷
   re 12 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 13 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 12 q5 ∷
   rw 15 q1 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw⁻ 14 q6 ∷
   rw 17 q1 ∷
   re 15 3 (CS13⁻ ∷ []) ∷
   rw⁻ 16 q6 ∷
   rw 19 q1 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 18 q5 ∷
   rw⁻ 19 q7 ∷
   rw 20 q8 ∷
   rw 19 q7 ∷
   rw 18 q9 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q8 ∷
   rw 16 q6 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q8 ∷
   rw 14 q6 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q8 ∷
   rw 12 q9 ∷
   rw 13 q10 ∷
   re 13 8 (Toff201 ∷ []) ∷
   rw 11 q12 ∷
   rw 10 q9 ∷
   rw 9 q13 ∷
   rw 8 q2 ∷
   rw 7 q3 ∷
   rw 6 q4 ∷
   re 5 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 6 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 5 q5 ∷
   rw 8 q1 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q6 ∷
   rw 10 q1 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q6 ∷
   rw 12 q1 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q5 ∷
   rw⁻ 12 q7 ∷
   rw 13 q8 ∷
   rw 12 q7 ∷
   rw 11 q9 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q8 ∷
   rw 9 q6 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q8 ∷
   rw 7 q6 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 5 q9 ∷
   rw 6 q10 ∷
   re 6 8 (Toff201 ∷ []) ∷
   rw 4 q11 ∷
   re 3 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 4 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 3 q5 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q6 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q6 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q5 ∷
   rw⁻ 10 q7 ∷
   rw 11 q8 ∷
   rw 10 q7 ∷
   rw 9 q9 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q8 ∷
   rw 7 q6 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 5 q6 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q8 ∷
   rw 3 q9 ∷
   rw 4 q10 ∷
   re 4 8 (Toff201 ∷ []) ∷
   rw 2 q12 ∷
   rw 1 q9 ∷
   rw 0 q13 ∷
   rw 19 q14 ∷
   rw⁻ 18 q15 ∷
   rw 17 q16 ∷
   rw 16 q17 ∷
   re 15 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 22 q18 ∷
   rw 21 q19 ∷
   re 20 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 22 q20 ∷
   rw 19 q14 ∷
   re 20 3 (CX02 ∷ []) ∷
   rw 18 q21 ∷
   rw 17 q14 ∷
   re 18 3 (CX02 ∷ []) ∷
   rw 16 q22 ∷
   rw 15 q19 ∷
   rw 16 q23 ∷
   re 16 8 (Toff102 ∷ []) ∷
   rw 14 q24 ∷
   re 13 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 20 q18 ∷
   rw 19 q19 ∷
   re 18 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 20 q20 ∷
   rw 17 q14 ∷
   re 18 3 (CX02 ∷ []) ∷
   rw 16 q21 ∷
   rw 15 q14 ∷
   re 16 3 (CX02 ∷ []) ∷
   rw 14 q22 ∷
   rw 13 q19 ∷
   rw 14 q23 ∷
   re 14 8 (Toff102 ∷ []) ∷
   rw 12 q25 ∷
   rw 11 q19 ∷
   rw 10 q26 ∷
   rw⁻ 9 q15 ∷
   rw 8 q16 ∷
   rw 7 q17 ∷
   re 6 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 13 q18 ∷
   rw 12 q19 ∷
   re 11 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 13 q20 ∷
   rw 10 q14 ∷
   re 11 3 (CX02 ∷ []) ∷
   rw 9 q21 ∷
   rw 8 q14 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q22 ∷
   rw 6 q19 ∷
   rw 7 q23 ∷
   re 7 8 (Toff102 ∷ []) ∷
   rw 5 q24 ∷
   re 4 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 11 q18 ∷
   rw 10 q19 ∷
   re 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 11 q20 ∷
   rw 8 q14 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q21 ∷
   rw 6 q14 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 5 q22 ∷
   rw 4 q19 ∷
   rw 5 q23 ∷
   re 5 8 (Toff102 ∷ []) ∷
   rw 3 q25 ∷
   rw 2 q19 ∷
   rw 1 q26 ∷
   rw 20 q27 ∷
   rw⁻ 19 q28 ∷
   rw 18 q29 ∷
   rw 17 q30 ∷
   re 16 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 23 q31 ∷
   rw 22 q32 ∷
   rw 21 q33 ∷
   rw 20 q34 ∷
   rw 19 q35 ∷
   rw 18 q34 ∷
   rw 17 q36 ∷
   rw 16 q32 ∷
   rw 17 q37 ∷
   re 17 8 (Toff012 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q38 ∷
   rw 16 q35 ∷
   rw⁻ 15 q38 ∷
   re 16 3 (CS03⁻ ∷ []) ∷
   re 14 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 21 q31 ∷
   rw 20 q32 ∷
   rw 19 q33 ∷
   rw 18 q34 ∷
   rw 17 q35 ∷
   rw 16 q34 ∷
   rw 15 q36 ∷
   rw 14 q32 ∷
   rw 15 q37 ∷
   re 15 8 (Toff012 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q38 ∷
   rw 14 q36 ∷
   rw⁻ 13 q38 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 12 q32 ∷
   rw 11 q39 ∷
   rw⁻ 10 q28 ∷
   rw 9 q29 ∷
   rw 8 q30 ∷
   re 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 14 q31 ∷
   rw 13 q32 ∷
   rw 12 q33 ∷
   rw 11 q34 ∷
   rw 10 q35 ∷
   rw 9 q34 ∷
   rw 8 q36 ∷
   rw 7 q32 ∷
   rw 8 q37 ∷
   re 8 8 (Toff012 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q38 ∷
   rw 7 q35 ∷
   rw⁻ 6 q38 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 12 q31 ∷
   rw 11 q32 ∷
   rw 10 q33 ∷
   rw 9 q34 ∷
   rw 8 q35 ∷
   rw 7 q34 ∷
   rw 6 q36 ∷
   rw 5 q32 ∷
   rw 6 q37 ∷
   re 6 8 (Toff012 ∷ []) ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q38 ∷
   rw 5 q36 ∷
   rw⁻ 4 q38 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 3 q32 ∷
   rw 2 q39 ∷
   rw 3 q40 ∷
   rw 2 q41 ∷
   rw 3 q42 ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 4 q43 ∷
   rw 5 q44 ∷
   rw 6 q45 ∷
   rw 7 q41 ∷
   rw 8 q45 ∷
   rw 9 q46 ∷
   rw 10 q43 ∷
   rw 11 q47 ∷
   rw 4 q48 ∷
   re 4 8 (Toff102 ∷ []) ∷
   rw 5 q49 ∷
   rw 6 q50 ∷
   re 2 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 1 q20 ∷
   rw 2 q51 ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 3 q52 ∷
   rw 4 q53 ∷
   rw 7 q14 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 q54 ∷
   rw 9 q14 ∷
   re 7 3 (CX02 ∷ []) ∷
   re 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 8 q20 ∷
   rw 9 q52 ∷
   rw⁻ 10 q18 ∷
   rw 3 q55 ∷
   re 3 8 (Toff201 ∷ []) ∷
   rw 4 q56 ∷
   rw 5 q20 ∷
   rw⁻ 0 q57 ∷
   rw 1 q58 ∷
   re 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 2 q5 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q6 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q6 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q5 ∷
   rw⁻ 9 q7 ∷
   rw 2 q1 ∷
   rw 3 q59 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q8 ∷
   rw⁻ 5 q6 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q8 ∷
   rw⁻ 7 q6 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 9 q59 ∷
   rw⁻ 10 q7 ∷
   rw 3 q10 ∷
   re 3 8 (Toff201 ∷ []) ∷
   re 2 3 (Toff301 ∷ []) ∷
   rw 3 q60 ∷
   rw 4 q8 ∷ []) Eq.refl

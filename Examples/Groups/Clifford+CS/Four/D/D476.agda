{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D476 (W : Ws) where

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

private
  q1 : Eqn
  q1 = wE 12 W
  q2 : Eqn
  q2 = wE 280 W
  q3 : Eqn
  q3 = eqn (Sw12 ∷ S3 ∷ []) (S3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (S))
  q4 : Eqn
  q4 = wE 14 W
  q5 : Eqn
  q5 = eqn (S0 ∷ Sw12 ∷ []) (Sw12 ∷ S0 ∷ []) (low₁-comm (S) (Swap))
  q6 : Eqn
  q6 = wE 16 W
  q7 : Eqn
  q7 = wE 757 W
  q8 : Eqn
  q8 = wE 479 W
  q9 : Eqn
  q9 = wE 5 W
  q10 : Eqn
  q10 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q11 : Eqn
  q11 = wE 273 W
  q12 : Eqn
  q12 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q13 : Eqn
  q13 = wE 216 W
  q14 : Eqn
  q14 = wE 480 W
  q15 : Eqn
  q15 = wE 481 W
  q16 : Eqn
  q16 = wE 74 W
  q17 : Eqn
  q17 = wE 10 W
  q18 : Eqn
  q18 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q19 : Eqn
  q19 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))
  q20 : Eqn
  q20 = wE 219 W
  q21 : Eqn
  q21 = wE 327 W
  q22 : Eqn
  q22 = wE 30 W
  q23 : Eqn
  q23 = wE 275 W
  q24 : Eqn
  q24 = wE 25 W
  q25 : Eqn
  q25 = eqn (Sw01 ∷ K3 ∷ []) (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑)))
  q26 : Eqn
  q26 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q27 : Eqn
  q27 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q28 : Eqn
  q28 = wE 27 W
  q29 : Eqn
  q29 = wE 122 W
  q30 : Eqn
  q30 = wE 24 W
  q31 : Eqn
  q31 = wE 124 W
  q32 : Eqn
  q32 = wE 337 W
  q33 : Eqn
  q33 = wE 31 W
  q34 : Eqn
  q34 = wE 355 W
  q35 : Eqn
  q35 = wE 343 W
  q36 : Eqn
  q36 = wE 18 W
  q37 : Eqn
  q37 = eqn (Sw12 ∷ K3 ∷ []) (K3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (K))
  q38 : Eqn
  q38 = wE 49 W
  q39 : Eqn
  q39 = wE 51 W
  q40 : Eqn
  q40 = wE 22 W
  q41 : Eqn
  q41 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q42 : Eqn
  q42 = wE 23 W
  q43 : Eqn
  q43 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q44 : Eqn
  q44 = wE 1 W
  q45 : Eqn
  q45 = wE 336 W
  q46 : Eqn
  q46 = wE 3 W
  q47 : Eqn
  q47 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q48 : Eqn
  q48 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q49 : Eqn
  q49 = wE 368 W
  q50 : Eqn
  q50 = wE 20 W
  q51 : Eqn
  q51 = wE 359 W

-- AXIOM LF @2013: 727 steps
lem-AXIOM-LF-at2013 : ⟪ (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S3 ∷ CK32 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Toff301 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ Toff301 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) ⟫ʷ
lem-AXIOM-LF-at2013 = derive (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S3 ∷ CK32 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Toff301 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ Toff301 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ [])
  (rw 80 q1 ∷
   rw 79 q2 ∷
   rw⁻ 78 q3 ∷
   re 77 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 79 q4 ∷
   re 76 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 78 q4 ∷
   re 75 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 77 q4 ∷
   re 74 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 76 q4 ∷
   re 73 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 75 q4 ∷
   re 72 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 74 q4 ∷
   re 71 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 73 q4 ∷
   rw 70 q5 ∷
   re 69 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 71 q4 ∷
   re 68 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 70 q4 ∷
   re 67 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 69 q4 ∷
   rw 66 q1 ∷
   re 67 3 (CX02 ∷ []) ∷
   rw 65 q6 ∷
   rw 64 q6 ∷
   rw 63 q6 ∷
   rw 62 q6 ∷
   rw 61 q6 ∷
   rw 60 q6 ∷
   rw 59 q6 ∷
   rw 58 q6 ∷
   rw 57 q6 ∷
   rw 56 q7 ∷
   rw 55 q8 ∷
   rw 54 q8 ∷
   rw 53 q8 ∷
   rw 52 q8 ∷
   rw 51 q6 ∷
   rw 50 q6 ∷
   rw 49 q6 ∷
   rw 48 q6 ∷
   rw 47 q6 ∷
   rw 46 q6 ∷
   rw 45 q6 ∷
   rw 44 q6 ∷
   rw 43 q6 ∷
   rw 42 q6 ∷
   rw 41 q6 ∷
   rw 40 q6 ∷
   rw 39 q6 ∷
   rw 38 q6 ∷
   rw 37 q6 ∷
   rw 36 q6 ∷
   rw 35 q6 ∷
   rw 34 q6 ∷
   rw 33 q1 ∷
   re 34 3 (CX02 ∷ []) ∷
   rw 32 q6 ∷
   rw 31 q6 ∷
   rw 30 q6 ∷
   rw 29 q6 ∷
   rw 28 q6 ∷
   rw 27 q6 ∷
   rw 26 q7 ∷
   rw 25 q8 ∷
   rw 24 q6 ∷
   rw 23 q6 ∷
   rw 22 q6 ∷
   rw 21 q2 ∷
   rw 20 q6 ∷
   rw 19 q7 ∷
   rw 18 q6 ∷
   rw 17 q6 ∷
   rw 16 q1 ∷
   re 17 3 (CX02 ∷ []) ∷
   rw 15 q6 ∷
   rw 14 q6 ∷
   rw 13 q6 ∷
   rw 12 q6 ∷
   rw 11 q6 ∷
   rw 10 q6 ∷
   rw 9 q8 ∷
   rw 8 q7 ∷
   rw 7 q6 ∷
   rw 6 q6 ∷
   rw 5 q6 ∷
   rw 4 q1 ∷
   re 5 3 (CX02 ∷ []) ∷
   re 3 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 5 q4 ∷
   re 2 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 4 q4 ∷
   re 1 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 3 q4 ∷
   re 0 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 2 q4 ∷
   rw 81 q9 ∷
   re 80 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw⁻ 82 q10 ∷
   rw 81 q11 ∷
   rw⁻ 80 q10 ∷
   re 81 3 (CK30 ∷ []) ∷
   rw⁻ 79 q12 ∷
   rw 78 q13 ∷
   rw 77 q13 ∷
   rw 76 q13 ∷
   rw 75 q13 ∷
   rw 74 q13 ∷
   rw 73 q13 ∷
   rw 72 q14 ∷
   rw 71 q15 ∷
   rw 70 q13 ∷
   rw 69 q13 ∷
   rw 68 q13 ∷
   rw 67 q16 ∷
   rw 66 q17 ∷
   rw 65 q17 ∷
   rw 64 q17 ∷
   rw 63 q17 ∷
   rw 62 q17 ∷
   rw 61 q17 ∷
   rw 60 q17 ∷
   rw 59 q17 ∷
   rw 58 q17 ∷
   rw 57 q11 ∷
   rw⁻ 56 q18 ∷
   rw⁻ 55 q18 ∷
   rw⁻ 54 q18 ∷
   rw⁻ 53 q18 ∷
   rw 52 q17 ∷
   rw 51 q17 ∷
   rw 50 q17 ∷
   rw 49 q17 ∷
   rw 48 q17 ∷
   rw 47 q17 ∷
   rw 46 q17 ∷
   rw 45 q17 ∷
   rw 44 q17 ∷
   rw 43 q17 ∷
   rw 42 q17 ∷
   rw 41 q17 ∷
   rw 40 q17 ∷
   rw 39 q17 ∷
   rw 38 q17 ∷
   rw 37 q17 ∷
   rw 36 q17 ∷
   rw 35 q17 ∷
   rw 34 q16 ∷
   rw 33 q17 ∷
   rw 32 q17 ∷
   rw 31 q17 ∷
   rw 30 q17 ∷
   rw 29 q17 ∷
   rw 28 q17 ∷
   rw 27 q11 ∷
   rw⁻ 26 q18 ∷
   rw 25 q17 ∷
   rw 24 q17 ∷
   rw 23 q17 ∷
   re 22 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q10 ∷
   rw 23 q11 ∷
   rw⁻ 22 q10 ∷
   re 23 3 (CK30 ∷ []) ∷
   rw 21 q17 ∷
   rw 20 q11 ∷
   rw 19 q17 ∷
   rw 18 q17 ∷
   rw 17 q16 ∷
   rw 16 q17 ∷
   rw 15 q17 ∷
   rw 14 q17 ∷
   rw 13 q17 ∷
   rw 12 q17 ∷
   rw 11 q17 ∷
   rw⁻ 10 q18 ∷
   rw 9 q11 ∷
   rw 8 q17 ∷
   rw 7 q17 ∷
   rw 6 q17 ∷
   rw 5 q16 ∷
   rw 4 q13 ∷
   rw 3 q14 ∷
   rw 2 q13 ∷
   rw 1 q13 ∷
   rw 2 q19 ∷
   rw 1 q20 ∷
   rw 2 q20 ∷
   rw 3 q21 ∷
   rw 4 q20 ∷
   rw 5 q21 ∷
   rw 6 q21 ∷
   rw 7 q22 ∷
   rw 8 q23 ∷
   rw 9 q18 ∷
   rw 10 q23 ∷
   rw 11 q18 ∷
   rw 12 q24 ∷
   rw 13 q24 ∷
   rw 14 q24 ∷
   rw 15 q23 ∷
   rw 16 q18 ∷
   rw 17 q24 ∷
   rw 18 q24 ∷
   rw 19 q24 ∷
   rw 20 q24 ∷
   rw 21 q24 ∷
   rw 22 q24 ∷
   rw 23 q22 ∷
   rw 24 q24 ∷
   rw 25 q24 ∷
   rw 26 q23 ∷
   rw 27 q24 ∷
   rw 28 q23 ∷
   rw 29 q23 ∷
   re 31 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 30 q25 ∷
   rw 31 q26 ∷
   rw 32 q22 ∷
   rw 33 q27 ∷
   rw 34 q22 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q10 ∷
   rw 36 q28 ∷
   rw 37 q10 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q25 ∷
   rw 37 q29 ∷
   rw 30 q9 ∷
   rw 31 q25 ∷
   rw 32 q26 ∷
   rw 33 q30 ∷
   rw 34 q27 ∷
   rw 35 q30 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q10 ∷
   rw 37 q24 ∷
   rw 38 q10 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 37 q25 ∷
   rw 38 q31 ∷
   rw 31 q32 ∷
   re 31 8 (Toff312 ∷ []) ∷
   re 30 3 (Toff302 ∷ []) ∷
   rw 31 q20 ∷
   rw 32 q20 ∷
   rw 33 q20 ∷
   rw 34 q21 ∷
   rw 35 q20 ∷
   rw 36 q20 ∷
   re 38 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 37 q10 ∷
   rw 38 q22 ∷
   rw 39 q10 ∷
   re 37 3 (CX03 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q10 ∷
   rw 39 q24 ∷
   rw 40 q10 ∷
   re 38 3 (CS13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q10 ∷
   rw 40 q24 ∷
   rw 41 q10 ∷
   re 39 3 (CS13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q10 ∷
   rw 41 q24 ∷
   rw 42 q10 ∷
   re 40 3 (CS13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q10 ∷
   rw 42 q24 ∷
   rw 43 q10 ∷
   re 41 3 (CS13 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q10 ∷
   rw 43 q24 ∷
   rw 44 q10 ∷
   re 42 3 (CS13 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q10 ∷
   rw 44 q24 ∷
   rw 45 q10 ∷
   re 43 3 (CS13 ∷ []) ∷
   re 45 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 44 q10 ∷
   rw 45 q23 ∷
   rw 46 q10 ∷
   re 44 3 (CK31 ∷ []) ∷
   rw 45 q12 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q10 ∷
   rw 47 q24 ∷
   rw 48 q10 ∷
   re 46 3 (CS13 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q10 ∷
   rw 48 q24 ∷
   rw 49 q10 ∷
   re 47 3 (CS13 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q10 ∷
   rw 49 q24 ∷
   rw 50 q10 ∷
   re 48 3 (CS13 ∷ []) ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q10 ∷
   rw 50 q24 ∷
   rw 51 q10 ∷
   re 49 3 (CS13 ∷ []) ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q10 ∷
   rw 51 q24 ∷
   rw 52 q10 ∷
   re 50 3 (CS13 ∷ []) ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q10 ∷
   rw 52 q24 ∷
   rw 53 q10 ∷
   re 51 3 (CS13 ∷ []) ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q10 ∷
   rw 53 q24 ∷
   rw 54 q10 ∷
   re 52 3 (CS13 ∷ []) ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q10 ∷
   rw 54 q24 ∷
   rw 55 q10 ∷
   re 53 3 (CS13 ∷ []) ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 54 q10 ∷
   rw 55 q24 ∷
   rw 56 q10 ∷
   re 54 3 (CS13 ∷ []) ∷
   re 56 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 55 q10 ∷
   rw 56 q22 ∷
   rw 57 q10 ∷
   re 55 3 (CX03 ∷ []) ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q10 ∷
   rw 57 q24 ∷
   rw 58 q10 ∷
   re 56 3 (CS13 ∷ []) ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q10 ∷
   rw 58 q24 ∷
   rw 59 q10 ∷
   re 57 3 (CS13 ∷ []) ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 58 q10 ∷
   rw 59 q24 ∷
   rw 60 q10 ∷
   re 58 3 (CS13 ∷ []) ∷
   re 60 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 59 q10 ∷
   rw 60 q23 ∷
   rw 61 q10 ∷
   re 59 3 (CK31 ∷ []) ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q10 ∷
   rw 61 q24 ∷
   rw 62 q10 ∷
   re 60 3 (CS13 ∷ []) ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 61 q10 ∷
   rw 62 q24 ∷
   rw 63 q10 ∷
   re 61 3 (CS13 ∷ []) ∷
   re 63 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 62 q25 ∷
   rw 63 q26 ∷
   rw 64 q22 ∷
   rw 65 q27 ∷
   rw 66 q22 ∷
   re 68 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 67 q10 ∷
   rw 68 q28 ∷
   rw 69 q10 ∷
   re 67 3 (CS03 ∷ []) ∷
   rw 68 q25 ∷
   rw 69 q29 ∷
   rw 62 q9 ∷
   rw 63 q25 ∷
   rw 64 q26 ∷
   rw 65 q30 ∷
   rw 66 q27 ∷
   rw 67 q30 ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 68 q10 ∷
   rw 69 q24 ∷
   rw 70 q10 ∷
   re 68 3 (CS13 ∷ []) ∷
   rw 69 q25 ∷
   rw 70 q31 ∷
   rw 63 q32 ∷
   re 63 8 (Toff312 ∷ []) ∷
   re 62 3 (Toff302 ∷ []) ∷
   rw 63 q20 ∷
   rw 64 q20 ∷
   rw 65 q21 ∷
   rw 66 q20 ∷
   rw 67 q21 ∷
   rw 68 q21 ∷
   re 70 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 69 q10 ∷
   rw 70 q22 ∷
   rw 71 q10 ∷
   re 69 3 (CX03 ∷ []) ∷
   re 71 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 70 q10 ∷
   rw 71 q23 ∷
   rw 72 q10 ∷
   re 70 3 (CK31 ∷ []) ∷
   rw 71 q12 ∷
   re 73 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 72 q10 ∷
   rw 73 q23 ∷
   rw 74 q10 ∷
   re 72 3 (CK31 ∷ []) ∷
   rw 73 q12 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q10 ∷
   rw 75 q24 ∷
   rw 76 q10 ∷
   re 74 3 (CS13 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q10 ∷
   rw 76 q24 ∷
   rw 77 q10 ∷
   re 75 3 (CS13 ∷ []) ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q10 ∷
   rw 77 q24 ∷
   rw 78 q10 ∷
   re 76 3 (CS13 ∷ []) ∷
   re 78 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 77 q10 ∷
   rw 78 q23 ∷
   rw 79 q10 ∷
   re 77 3 (CK31 ∷ []) ∷
   rw 78 q12 ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q10 ∷
   rw 80 q24 ∷
   rw 81 q10 ∷
   re 79 3 (CS13 ∷ []) ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 80 q10 ∷
   rw 81 q24 ∷
   rw 82 q10 ∷
   re 80 3 (CS13 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 81 q10 ∷
   rw 82 q24 ∷
   rw 83 q10 ∷
   re 81 3 (CS13 ∷ []) ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 82 q10 ∷
   rw 83 q24 ∷
   rw 84 q10 ∷
   re 82 3 (CS13 ∷ []) ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 83 q10 ∷
   rw 84 q24 ∷
   rw 85 q10 ∷
   re 83 3 (CS13 ∷ []) ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 84 q10 ∷
   rw 85 q24 ∷
   rw 86 q10 ∷
   re 84 3 (CS13 ∷ []) ∷
   re 86 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 85 q10 ∷
   rw 86 q22 ∷
   rw 87 q10 ∷
   re 85 3 (CX03 ∷ []) ∷
   re 87 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 86 q10 ∷
   rw 87 q24 ∷
   rw 88 q10 ∷
   re 86 3 (CS13 ∷ []) ∷
   re 88 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 87 q10 ∷
   rw 88 q24 ∷
   rw 89 q10 ∷
   re 87 3 (CS13 ∷ []) ∷
   re 89 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 88 q10 ∷
   rw 89 q23 ∷
   rw 90 q10 ∷
   re 88 3 (CK31 ∷ []) ∷
   re 90 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 89 q10 ∷
   rw 90 q24 ∷
   rw 91 q10 ∷
   re 89 3 (CS13 ∷ []) ∷
   re 91 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 90 q10 ∷
   rw 91 q23 ∷
   rw 92 q10 ∷
   re 90 3 (CK31 ∷ []) ∷
   re 92 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 91 q10 ∷
   rw 92 q23 ∷
   rw 93 q10 ∷
   re 91 3 (CK31 ∷ []) ∷
   rw 92 q33 ∷
   rw 2 q1 ∷
   re 0 3 (CS02 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS02 ∷ []) ∷
   rw 4 q1 ∷
   re 2 3 (CK02 ∷ []) ∷
   rw 5 q1 ∷
   re 3 3 (CS02 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CK02 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CK02 ∷ []) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 q4 ∷
   rw 7 q34 ∷
   rw 8 q35 ∷
   rw 9 q34 ∷
   rw 10 q35 ∷
   rw 11 q36 ∷
   rw 12 q36 ∷
   rw 13 q36 ∷
   rw 14 q34 ∷
   rw 15 q35 ∷
   rw 16 q36 ∷
   rw 17 q36 ∷
   rw 18 q36 ∷
   rw 19 q36 ∷
   rw 20 q36 ∷
   rw 21 q36 ∷
   re 23 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 22 q4 ∷
   rw 23 q36 ∷
   rw 24 q36 ∷
   rw 25 q34 ∷
   rw 26 q36 ∷
   rw 27 q34 ∷
   rw 28 q34 ∷
   re 30 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) ∷
   re 31 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 30 q25 ∷
   rw 31 q26 ∷
   rw 32 q22 ∷
   rw 33 q27 ∷
   rw 34 q22 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q10 ∷
   rw 36 q28 ∷
   rw 37 q10 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q25 ∷
   rw 37 q29 ∷
   rw 38 q33 ∷
   rw 29 q37 ∷
   rw 30 q38 ∷
   re 32 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 31 q4 ∷
   rw 32 q39 ∷
   re 34 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 33 q4 ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q40 ∷
   rw⁻ 36 q41 ∷
   rw 37 q42 ∷
   re 34 5 (CS03 ∷ []) ∷
   rw 35 q37 ∷
   rw⁻ 36 q43 ∷
   rw 29 q44 ∷
   rw 30 q45 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q46 ∷
   rw⁻ 32 q47 ∷
   re 34 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 33 q46 ∷
   rw⁻ 34 q47 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q46 ∷
   rw 36 q45 ∷
   rw⁻ 37 q48 ∷
   rw 30 q49 ∷
   re 30 8 (Toff201 ∷ []) ∷
   re 29 3 (Toff301 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CS02 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CS02 ∷ []) ∷
   rw 34 q1 ∷
   re 32 3 (CS02 ∷ []) ∷
   rw 35 q1 ∷
   re 33 3 (CK02 ∷ []) ∷
   rw 36 q1 ∷
   re 34 3 (CS02 ∷ []) ∷
   rw 37 q1 ∷
   re 35 3 (CS02 ∷ []) ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q40 ∷
   rw⁻ 38 q47 ∷
   rw 39 q42 ∷
   re 36 5 (CX03 ∷ []) ∷
   rw 37 q50 ∷
   rw 38 q50 ∷
   rw 39 q50 ∷
   rw 40 q50 ∷
   rw 41 q50 ∷
   rw 42 q50 ∷
   rw 43 q51 ∷
   rw 44 q3 ∷
   rw 45 q50 ∷
   rw 46 q50 ∷
   rw 47 q50 ∷
   rw 48 q50 ∷
   rw 49 q50 ∷
   rw 50 q50 ∷
   rw 51 q50 ∷
   rw 52 q50 ∷
   rw 53 q50 ∷
   re 55 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q40 ∷
   rw⁻ 56 q47 ∷
   rw 57 q42 ∷
   re 54 5 (CX03 ∷ []) ∷
   rw 55 q50 ∷
   rw 56 q50 ∷
   rw 57 q50 ∷
   rw 58 q51 ∷
   rw 59 q50 ∷
   rw 60 q50 ∷
   re 62 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) ∷
   re 63 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 62 q25 ∷
   rw 63 q26 ∷
   rw 64 q22 ∷
   rw 65 q27 ∷
   rw 66 q22 ∷
   re 68 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 67 q10 ∷
   rw 68 q28 ∷
   rw 69 q10 ∷
   re 67 3 (CS03 ∷ []) ∷
   rw 68 q25 ∷
   rw 69 q29 ∷
   rw 70 q33 ∷
   rw 61 q37 ∷
   rw 62 q38 ∷
   re 64 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 63 q4 ∷
   rw 64 q39 ∷
   re 66 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 65 q4 ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 66 q40 ∷
   rw⁻ 68 q41 ∷
   rw 69 q42 ∷
   re 66 5 (CS03 ∷ []) ∷
   rw 67 q37 ∷
   rw⁻ 68 q43 ∷
   rw 61 q44 ∷
   rw 62 q45 ∷
   re 64 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 63 q46 ∷
   rw⁻ 64 q47 ∷
   re 66 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 65 q46 ∷
   rw⁻ 66 q47 ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q46 ∷
   rw 68 q45 ∷
   rw⁻ 69 q48 ∷
   rw 62 q49 ∷
   re 62 8 (Toff201 ∷ []) ∷
   re 61 3 (Toff301 ∷ []) ∷
   rw 64 q1 ∷
   re 62 3 (CS02 ∷ []) ∷
   rw 65 q1 ∷
   re 63 3 (CS02 ∷ []) ∷
   rw 66 q1 ∷
   re 64 3 (CK02 ∷ []) ∷
   rw 67 q1 ∷
   re 65 3 (CS02 ∷ []) ∷
   rw 68 q1 ∷
   re 66 3 (CK02 ∷ []) ∷
   rw 69 q1 ∷
   re 67 3 (CK02 ∷ []) ∷
   re 69 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 68 q40 ∷
   rw⁻ 70 q47 ∷
   rw 71 q42 ∷
   re 68 5 (CX03 ∷ []) ∷
   rw 69 q51 ∷
   rw 70 q3 ∷
   rw 71 q51 ∷
   rw 72 q3 ∷
   rw 73 q50 ∷
   rw 74 q50 ∷
   rw 75 q50 ∷
   rw 76 q51 ∷
   rw 77 q3 ∷
   rw 78 q50 ∷
   rw 79 q50 ∷
   rw 80 q50 ∷
   rw 81 q50 ∷
   rw 82 q50 ∷
   rw 83 q50 ∷
   re 85 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 84 q40 ∷
   rw⁻ 86 q47 ∷
   rw 87 q42 ∷
   re 84 5 (CX03 ∷ []) ∷
   rw 85 q50 ∷
   rw 86 q50 ∷
   rw 87 q51 ∷
   rw 88 q50 ∷
   rw 89 q51 ∷
   rw 90 q51 ∷
   rw 91 q4 ∷ []) Eq.refl

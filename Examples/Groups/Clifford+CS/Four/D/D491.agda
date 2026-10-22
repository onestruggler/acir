{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D491 (W : Ws) where

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
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 1302 W
  q3 : Eqn
  q3 = wE 476 W
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q6 : Eqn
  q6 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q7 : Eqn
  q7 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q8 : Eqn
  q8 = wE 12 W
  q9 : Eqn
  q9 = wE 280 W
  q10 : Eqn
  q10 = eqn (Sw12 ∷ S3 ∷ []) (S3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (S))
  q11 : Eqn
  q11 = wE 14 W
  q12 : Eqn
  q12 = eqn (S0 ∷ Sw12 ∷ []) (Sw12 ∷ S0 ∷ []) (low₁-comm (S) (Swap))
  q13 : Eqn
  q13 = wE 16 W
  q14 : Eqn
  q14 = wE 757 W
  q15 : Eqn
  q15 = wE 479 W
  q16 : Eqn
  q16 = wE 5 W
  q17 : Eqn
  q17 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q18 : Eqn
  q18 = wE 273 W
  q19 : Eqn
  q19 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q20 : Eqn
  q20 = wE 216 W
  q21 : Eqn
  q21 = wE 480 W
  q22 : Eqn
  q22 = wE 481 W
  q23 : Eqn
  q23 = wE 74 W
  q24 : Eqn
  q24 = wE 10 W
  q25 : Eqn
  q25 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q26 : Eqn
  q26 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))
  q27 : Eqn
  q27 = wE 219 W
  q28 : Eqn
  q28 = wE 327 W
  q29 : Eqn
  q29 = wE 30 W
  q30 : Eqn
  q30 = wE 275 W
  q31 : Eqn
  q31 = wE 25 W
  q32 : Eqn
  q32 = eqn (Sw01 ∷ K3 ∷ []) (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑)))
  q33 : Eqn
  q33 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q34 : Eqn
  q34 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q35 : Eqn
  q35 = wE 27 W
  q36 : Eqn
  q36 = wE 122 W
  q37 : Eqn
  q37 = wE 24 W
  q38 : Eqn
  q38 = wE 124 W
  q39 : Eqn
  q39 = wE 337 W

-- AXIOM LF @3012 part0: 500 steps
lem-AXIOM-LF-at3012-part0 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S0 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ Toff302 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-AXIOM-LF-at3012-part0 = derive (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S0 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK23 ∷ []) (Sw23 ∷ Sw12 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ Toff302 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw 80 q1 ∷
   rw 79 q2 ∷
   rw 78 q3 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q4 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q4 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q4 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q4 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q4 ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q4 ∷
   re 71 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 73 q4 ∷
   rw 70 q5 ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 71 q4 ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 70 q4 ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 69 q4 ∷
   rw 66 q6 ∷
   re 65 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 67 q4 ∷
   re 64 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 66 q4 ∷
   re 63 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 65 q4 ∷
   re 62 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 64 q4 ∷
   re 61 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 63 q4 ∷
   re 60 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 62 q4 ∷
   re 59 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 61 q4 ∷
   re 58 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 60 q4 ∷
   re 57 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 59 q4 ∷
   re 56 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 58 q4 ∷
   rw 55 q7 ∷
   rw 54 q7 ∷
   rw 53 q7 ∷
   rw 52 q7 ∷
   re 51 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 53 q4 ∷
   re 50 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 52 q4 ∷
   re 49 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 51 q4 ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 50 q4 ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 49 q4 ∷
   re 46 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 48 q4 ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q4 ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 46 q4 ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 45 q4 ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q4 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q4 ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q4 ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 41 q4 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q4 ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q4 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q4 ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q4 ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q4 ∷
   rw 33 q6 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q4 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q4 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q4 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q4 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q4 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q4 ∷
   re 26 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 28 q4 ∷
   rw 25 q7 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   rw 21 q2 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   re 19 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 21 q4 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q4 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q4 ∷
   rw 16 q6 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q4 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q4 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q4 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q4 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q4 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q4 ∷
   rw 9 q7 ∷
   re 8 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 10 q4 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q4 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q4 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q4 ∷
   rw 4 q6 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q4 ∷
   re 2 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw 81 q8 ∷
   rw 80 q9 ∷
   rw⁻ 79 q10 ∷
   re 78 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 80 q11 ∷
   re 77 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 79 q11 ∷
   re 76 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 78 q11 ∷
   re 75 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 77 q11 ∷
   re 74 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 76 q11 ∷
   re 73 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 75 q11 ∷
   re 72 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 74 q11 ∷
   rw 71 q12 ∷
   re 70 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 72 q11 ∷
   re 69 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 71 q11 ∷
   re 68 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 70 q11 ∷
   rw 67 q8 ∷
   re 68 3 (CX02 ∷ []) ∷
   rw 66 q13 ∷
   rw 65 q13 ∷
   rw 64 q13 ∷
   rw 63 q13 ∷
   rw 62 q13 ∷
   rw 61 q13 ∷
   rw 60 q13 ∷
   rw 59 q13 ∷
   rw 58 q13 ∷
   rw 57 q14 ∷
   rw 56 q15 ∷
   rw 55 q15 ∷
   rw 54 q15 ∷
   rw 53 q15 ∷
   rw 52 q13 ∷
   rw 51 q13 ∷
   rw 50 q13 ∷
   rw 49 q13 ∷
   rw 48 q13 ∷
   rw 47 q13 ∷
   rw 46 q13 ∷
   rw 45 q13 ∷
   rw 44 q13 ∷
   rw 43 q13 ∷
   rw 42 q13 ∷
   rw 41 q13 ∷
   rw 40 q13 ∷
   rw 39 q13 ∷
   rw 38 q13 ∷
   rw 37 q13 ∷
   rw 36 q13 ∷
   rw 35 q13 ∷
   rw 34 q8 ∷
   re 35 3 (CX02 ∷ []) ∷
   rw 33 q13 ∷
   rw 32 q13 ∷
   rw 31 q13 ∷
   rw 30 q13 ∷
   rw 29 q13 ∷
   rw 28 q13 ∷
   rw 27 q14 ∷
   rw 26 q15 ∷
   rw 25 q13 ∷
   rw 24 q13 ∷
   rw 23 q13 ∷
   rw 22 q9 ∷
   rw 21 q13 ∷
   rw 20 q14 ∷
   rw 19 q13 ∷
   rw 18 q13 ∷
   rw 17 q8 ∷
   re 18 3 (CX02 ∷ []) ∷
   rw 16 q13 ∷
   rw 15 q13 ∷
   rw 14 q13 ∷
   rw 13 q13 ∷
   rw 12 q13 ∷
   rw 11 q13 ∷
   rw 10 q15 ∷
   rw 9 q14 ∷
   rw 8 q13 ∷
   rw 7 q13 ∷
   rw 6 q13 ∷
   rw 5 q8 ∷
   re 6 3 (CX02 ∷ []) ∷
   re 4 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 6 q11 ∷
   re 3 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 5 q11 ∷
   re 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 4 q11 ∷
   re 1 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 3 q11 ∷
   rw 82 q16 ∷
   re 81 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw⁻ 83 q17 ∷
   rw 82 q18 ∷
   rw⁻ 81 q17 ∷
   re 82 3 (CK30 ∷ []) ∷
   rw⁻ 80 q19 ∷
   rw 79 q20 ∷
   rw 78 q20 ∷
   rw 77 q20 ∷
   rw 76 q20 ∷
   rw 75 q20 ∷
   rw 74 q20 ∷
   rw 73 q21 ∷
   rw 72 q22 ∷
   rw 71 q20 ∷
   rw 70 q20 ∷
   rw 69 q20 ∷
   rw 68 q23 ∷
   rw 67 q24 ∷
   rw 66 q24 ∷
   rw 65 q24 ∷
   rw 64 q24 ∷
   rw 63 q24 ∷
   rw 62 q24 ∷
   rw 61 q24 ∷
   rw 60 q24 ∷
   rw 59 q24 ∷
   rw 58 q18 ∷
   rw⁻ 57 q25 ∷
   rw⁻ 56 q25 ∷
   rw⁻ 55 q25 ∷
   rw⁻ 54 q25 ∷
   rw 53 q24 ∷
   rw 52 q24 ∷
   rw 51 q24 ∷
   rw 50 q24 ∷
   rw 49 q24 ∷
   rw 48 q24 ∷
   rw 47 q24 ∷
   rw 46 q24 ∷
   rw 45 q24 ∷
   rw 44 q24 ∷
   rw 43 q24 ∷
   rw 42 q24 ∷
   rw 41 q24 ∷
   rw 40 q24 ∷
   rw 39 q24 ∷
   rw 38 q24 ∷
   rw 37 q24 ∷
   rw 36 q24 ∷
   rw 35 q23 ∷
   rw 34 q24 ∷
   rw 33 q24 ∷
   rw 32 q24 ∷
   rw 31 q24 ∷
   rw 30 q24 ∷
   rw 29 q24 ∷
   rw 28 q18 ∷
   rw⁻ 27 q25 ∷
   rw 26 q24 ∷
   rw 25 q24 ∷
   rw 24 q24 ∷
   re 23 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q17 ∷
   rw 24 q18 ∷
   rw⁻ 23 q17 ∷
   re 24 3 (CK30 ∷ []) ∷
   rw 22 q24 ∷
   rw 21 q18 ∷
   rw 20 q24 ∷
   rw 19 q24 ∷
   rw 18 q23 ∷
   rw 17 q24 ∷
   rw 16 q24 ∷
   rw 15 q24 ∷
   rw 14 q24 ∷
   rw 13 q24 ∷
   rw 12 q24 ∷
   rw⁻ 11 q25 ∷
   rw 10 q18 ∷
   rw 9 q24 ∷
   rw 8 q24 ∷
   rw 7 q24 ∷
   rw 6 q23 ∷
   rw 5 q20 ∷
   rw 4 q21 ∷
   rw 3 q20 ∷
   rw 2 q20 ∷
   rw 3 q26 ∷
   rw 2 q27 ∷
   rw 3 q27 ∷
   rw 4 q28 ∷
   rw 5 q27 ∷
   rw 6 q28 ∷
   rw 7 q28 ∷
   rw 8 q29 ∷
   rw 9 q30 ∷
   rw 10 q25 ∷
   rw 11 q30 ∷
   rw 12 q25 ∷
   rw 13 q31 ∷
   rw 14 q31 ∷
   rw 15 q31 ∷
   rw 16 q30 ∷
   rw 17 q25 ∷
   rw 18 q31 ∷
   rw 19 q31 ∷
   rw 20 q31 ∷
   rw 21 q31 ∷
   rw 22 q31 ∷
   rw 23 q31 ∷
   rw 24 q29 ∷
   rw 25 q31 ∷
   rw 26 q31 ∷
   rw 27 q30 ∷
   rw 28 q31 ∷
   rw 29 q30 ∷
   rw 30 q30 ∷
   re 32 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 31 q32 ∷
   rw 32 q33 ∷
   rw 33 q29 ∷
   rw 34 q34 ∷
   rw 35 q29 ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q17 ∷
   rw 37 q35 ∷
   rw 38 q17 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q32 ∷
   rw 38 q36 ∷
   rw 31 q16 ∷
   rw 32 q32 ∷
   rw 33 q33 ∷
   rw 34 q37 ∷
   rw 35 q34 ∷
   rw 36 q37 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q17 ∷
   rw 38 q31 ∷
   rw 39 q17 ∷
   re 37 3 (CS13 ∷ []) ∷
   rw 38 q32 ∷
   rw 39 q38 ∷
   rw 32 q39 ∷
   re 32 8 (Toff312 ∷ []) ∷
   re 31 3 (Toff302 ∷ []) ∷
   rw 32 q27 ∷
   rw 33 q27 ∷
   rw 34 q27 ∷
   rw 35 q28 ∷
   rw 36 q27 ∷
   rw 37 q27 ∷
   re 39 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 38 q17 ∷
   rw 39 q29 ∷
   rw 40 q17 ∷
   re 38 3 (CX03 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q17 ∷
   rw 40 q31 ∷
   rw 41 q17 ∷
   re 39 3 (CS13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q17 ∷
   rw 41 q31 ∷
   rw 42 q17 ∷
   re 40 3 (CS13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q17 ∷
   rw 42 q31 ∷
   rw 43 q17 ∷
   re 41 3 (CS13 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q17 ∷
   rw 43 q31 ∷
   rw 44 q17 ∷
   re 42 3 (CS13 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q17 ∷
   rw 44 q31 ∷
   rw 45 q17 ∷
   re 43 3 (CS13 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q17 ∷
   rw 45 q31 ∷
   rw 46 q17 ∷
   re 44 3 (CS13 ∷ []) ∷
   re 46 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 45 q17 ∷
   rw 46 q30 ∷
   rw 47 q17 ∷
   re 45 3 (CK31 ∷ []) ∷
   rw 46 q19 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q17 ∷
   rw 48 q31 ∷
   rw 49 q17 ∷
   re 47 3 (CS13 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q17 ∷
   rw 49 q31 ∷
   rw 50 q17 ∷
   re 48 3 (CS13 ∷ []) ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q17 ∷
   rw 50 q31 ∷
   rw 51 q17 ∷
   re 49 3 (CS13 ∷ []) ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q17 ∷
   rw 51 q31 ∷
   rw 52 q17 ∷
   re 50 3 (CS13 ∷ []) ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q17 ∷
   rw 52 q31 ∷
   rw 53 q17 ∷
   re 51 3 (CS13 ∷ []) ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q17 ∷
   rw 53 q31 ∷
   rw 54 q17 ∷
   re 52 3 (CS13 ∷ []) ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q17 ∷
   rw 54 q31 ∷
   rw 55 q17 ∷
   re 53 3 (CS13 ∷ []) ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 54 q17 ∷
   rw 55 q31 ∷
   rw 56 q17 ∷
   re 54 3 (CS13 ∷ []) ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 55 q17 ∷
   rw 56 q31 ∷
   rw 57 q17 ∷
   re 55 3 (CS13 ∷ []) ∷
   re 57 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 56 q17 ∷
   rw 57 q29 ∷
   rw 58 q17 ∷
   re 56 3 (CX03 ∷ []) ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q17 ∷
   rw 58 q31 ∷
   rw 59 q17 ∷
   re 57 3 (CS13 ∷ []) ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 58 q17 ∷
   rw 59 q31 ∷
   rw 60 q17 ∷ []) Eq.refl

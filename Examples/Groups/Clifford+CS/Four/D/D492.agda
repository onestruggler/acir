{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D492 (W : Ws) where

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
  q1 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q2 : Eqn
  q2 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q3 : Eqn
  q3 = eqn (Sw01 ∷ CK20 ∷ []) (CK21 ∷ Sw01 ∷ []) (wn 275 W)
  q4 : Eqn
  q4 = eqn (Sw01 ∷ K3 ∷ []) (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑)))
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q7 : Eqn
  q7 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q8 : Eqn
  q8 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) (wn 122 W)
  q10 : Eqn
  q10 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q13 : Eqn
  q13 = eqn (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (wn 337 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) (wn 219 W)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ CK10 ∷ []) (CK01 ∷ Sw01 ∷ []) (wn 327 W)
  q16 : Eqn
  q16 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q17 : Eqn
  q17 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q18 : Eqn
  q18 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q19 : Eqn
  q19 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q20 : Eqn
  q20 = eqn (Sw12 ∷ CK21 ∷ []) (CK12 ∷ Sw12 ∷ []) (wn 355 W)
  q21 : Eqn
  q21 = eqn (Sw12 ∷ S2 ∷ []) (S1 ∷ Sw12 ∷ []) (wn 343 W)
  q22 : Eqn
  q22 = eqn (Sw12 ∷ CS12 ∷ []) (CS12 ∷ Sw12 ∷ []) (wn 18 W)
  q23 : Eqn
  q23 = eqn (Sw12 ∷ K3 ∷ []) (K3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (K))
  q24 : Eqn
  q24 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q25 : Eqn
  q25 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q26 : Eqn
  q26 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q27 : Eqn
  q27 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q28 : Eqn
  q28 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q29 : Eqn
  q29 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q30 : Eqn
  q30 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q31 : Eqn
  q31 = eqn (Sw23 ∷ K3 ∷ []) (K2 ∷ Sw23 ∷ []) (wn 336 W)
  q32 : Eqn
  q32 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q33 : Eqn
  q33 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q34 : Eqn
  q34 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q35 : Eqn
  q35 = eqn (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (wn 368 W)
  q36 : Eqn
  q36 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q37 : Eqn
  q37 = eqn (Sw12 ∷ CK31 ∷ []) (CK32 ∷ Sw12 ∷ []) (wn 359 W)
  q38 : Eqn
  q38 = eqn (Sw12 ∷ S3 ∷ []) (S3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (S))
  q39 : Eqn
  q39 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q40 : Eqn
  q40 = eqn (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) (wn 335 W)
  q41 : Eqn
  q41 = eqn (Sw23 ∷ CS23 ∷ []) (CS23 ∷ Sw23 ∷ []) (wn 71 W)
  q42 : Eqn
  q42 = eqn (Sw23 ∷ CK32 ∷ []) (CK23 ∷ Sw23 ∷ []) (wn 382 W)
  q43 : Eqn
  q43 = eqn (Sw23 ∷ S3 ∷ []) (S2 ∷ Sw23 ∷ []) (wn 372 W)

-- AXIOM LF @3012 part1: 500 steps
lem-AXIOM-LF-at3012-part1 : ⟪ (Sw23 ∷ Sw12 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ Toff302 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ Toff201 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ Sw23 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw23 ∷ []) ⟫ʷ
lem-AXIOM-LF-at3012-part1 = derive (Sw23 ∷ Sw12 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ Toff302 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ Toff201 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ Sw23 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw23 ∷ [])
  (re 58 3 (CS13 ∷ []) ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q1 ∷
   rw 60 q2 ∷
   rw 61 q1 ∷
   re 59 3 (CS13 ∷ []) ∷
   re 61 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 60 q1 ∷
   rw 61 q3 ∷
   rw 62 q1 ∷
   re 60 3 (CK31 ∷ []) ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 61 q1 ∷
   rw 62 q2 ∷
   rw 63 q1 ∷
   re 61 3 (CS13 ∷ []) ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 62 q1 ∷
   rw 63 q2 ∷
   rw 64 q1 ∷
   re 62 3 (CS13 ∷ []) ∷
   re 64 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 63 q4 ∷
   rw 64 q5 ∷
   rw 65 q6 ∷
   rw 66 q7 ∷
   rw 67 q6 ∷
   re 69 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 68 q1 ∷
   rw 69 q8 ∷
   rw 70 q1 ∷
   re 68 3 (CS03 ∷ []) ∷
   rw 69 q4 ∷
   rw 70 q9 ∷
   rw 63 q10 ∷
   rw 64 q4 ∷
   rw 65 q5 ∷
   rw 66 q11 ∷
   rw 67 q7 ∷
   rw 68 q11 ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 69 q1 ∷
   rw 70 q2 ∷
   rw 71 q1 ∷
   re 69 3 (CS13 ∷ []) ∷
   rw 70 q4 ∷
   rw 71 q12 ∷
   rw 64 q13 ∷
   re 64 8 (Toff312 ∷ []) ∷
   re 63 3 (Toff302 ∷ []) ∷
   rw 64 q14 ∷
   rw 65 q14 ∷
   rw 66 q15 ∷
   rw 67 q14 ∷
   rw 68 q15 ∷
   rw 69 q15 ∷
   re 71 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 70 q1 ∷
   rw 71 q6 ∷
   rw 72 q1 ∷
   re 70 3 (CX03 ∷ []) ∷
   re 72 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 71 q1 ∷
   rw 72 q3 ∷
   rw 73 q1 ∷
   re 71 3 (CK31 ∷ []) ∷
   rw 72 q16 ∷
   re 74 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 73 q1 ∷
   rw 74 q3 ∷
   rw 75 q1 ∷
   re 73 3 (CK31 ∷ []) ∷
   rw 74 q16 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q1 ∷
   rw 76 q2 ∷
   rw 77 q1 ∷
   re 75 3 (CS13 ∷ []) ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q1 ∷
   rw 77 q2 ∷
   rw 78 q1 ∷
   re 76 3 (CS13 ∷ []) ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q1 ∷
   rw 78 q2 ∷
   rw 79 q1 ∷
   re 77 3 (CS13 ∷ []) ∷
   re 79 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 78 q1 ∷
   rw 79 q3 ∷
   rw 80 q1 ∷
   re 78 3 (CK31 ∷ []) ∷
   rw 79 q16 ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 80 q1 ∷
   rw 81 q2 ∷
   rw 82 q1 ∷
   re 80 3 (CS13 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 81 q1 ∷
   rw 82 q2 ∷
   rw 83 q1 ∷
   re 81 3 (CS13 ∷ []) ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 82 q1 ∷
   rw 83 q2 ∷
   rw 84 q1 ∷
   re 82 3 (CS13 ∷ []) ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 83 q1 ∷
   rw 84 q2 ∷
   rw 85 q1 ∷
   re 83 3 (CS13 ∷ []) ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 84 q1 ∷
   rw 85 q2 ∷
   rw 86 q1 ∷
   re 84 3 (CS13 ∷ []) ∷
   re 86 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 85 q1 ∷
   rw 86 q2 ∷
   rw 87 q1 ∷
   re 85 3 (CS13 ∷ []) ∷
   re 87 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 86 q1 ∷
   rw 87 q6 ∷
   rw 88 q1 ∷
   re 86 3 (CX03 ∷ []) ∷
   re 88 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 87 q1 ∷
   rw 88 q2 ∷
   rw 89 q1 ∷
   re 87 3 (CS13 ∷ []) ∷
   re 89 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 88 q1 ∷
   rw 89 q2 ∷
   rw 90 q1 ∷
   re 88 3 (CS13 ∷ []) ∷
   re 90 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 89 q1 ∷
   rw 90 q3 ∷
   rw 91 q1 ∷
   re 89 3 (CK31 ∷ []) ∷
   re 91 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 90 q1 ∷
   rw 91 q2 ∷
   rw 92 q1 ∷
   re 90 3 (CS13 ∷ []) ∷
   re 92 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 91 q1 ∷
   rw 92 q3 ∷
   rw 93 q1 ∷
   re 91 3 (CK31 ∷ []) ∷
   re 93 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 92 q1 ∷
   rw 93 q3 ∷
   rw 94 q1 ∷
   re 92 3 (CK31 ∷ []) ∷
   rw 93 q17 ∷
   rw 3 q18 ∷
   re 1 3 (CS02 ∷ []) ∷
   rw 4 q18 ∷
   re 2 3 (CS02 ∷ []) ∷
   rw 5 q18 ∷
   re 3 3 (CK02 ∷ []) ∷
   rw 6 q18 ∷
   re 4 3 (CS02 ∷ []) ∷
   rw 7 q18 ∷
   re 5 3 (CK02 ∷ []) ∷
   rw 8 q18 ∷
   re 6 3 (CK02 ∷ []) ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 7 q19 ∷
   rw 8 q20 ∷
   rw 9 q21 ∷
   rw 10 q20 ∷
   rw 11 q21 ∷
   rw 12 q22 ∷
   rw 13 q22 ∷
   rw 14 q22 ∷
   rw 15 q20 ∷
   rw 16 q21 ∷
   rw 17 q22 ∷
   rw 18 q22 ∷
   rw 19 q22 ∷
   rw 20 q22 ∷
   rw 21 q22 ∷
   rw 22 q22 ∷
   re 24 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 23 q19 ∷
   rw 24 q22 ∷
   rw 25 q22 ∷
   rw 26 q20 ∷
   rw 27 q22 ∷
   rw 28 q20 ∷
   rw 29 q20 ∷
   re 31 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) ∷
   re 32 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 31 q4 ∷
   rw 32 q5 ∷
   rw 33 q6 ∷
   rw 34 q7 ∷
   rw 35 q6 ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
   rw 37 q8 ∷
   rw 38 q1 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q4 ∷
   rw 38 q9 ∷
   rw 39 q17 ∷
   rw 30 q23 ∷
   rw 31 q24 ∷
   re 33 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 32 q19 ∷
   rw 33 q25 ∷
   re 35 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 34 q19 ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q26 ∷
   rw⁻ 37 q27 ∷
   rw 38 q28 ∷
   re 35 5 (CS03 ∷ []) ∷
   rw 36 q23 ∷
   rw⁻ 37 q29 ∷
   rw 30 q30 ∷
   rw 31 q31 ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q32 ∷
   rw⁻ 33 q33 ∷
   re 35 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 34 q32 ∷
   rw⁻ 35 q33 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q32 ∷
   rw 37 q31 ∷
   rw⁻ 38 q34 ∷
   rw 31 q35 ∷
   re 31 8 (Toff201 ∷ []) ∷
   re 30 3 (Toff301 ∷ []) ∷
   rw 33 q18 ∷
   re 31 3 (CS02 ∷ []) ∷
   rw 34 q18 ∷
   re 32 3 (CS02 ∷ []) ∷
   rw 35 q18 ∷
   re 33 3 (CS02 ∷ []) ∷
   rw 36 q18 ∷
   re 34 3 (CK02 ∷ []) ∷
   rw 37 q18 ∷
   re 35 3 (CS02 ∷ []) ∷
   rw 38 q18 ∷
   re 36 3 (CS02 ∷ []) ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q26 ∷
   rw⁻ 39 q33 ∷
   rw 40 q28 ∷
   re 37 5 (CX03 ∷ []) ∷
   rw 38 q36 ∷
   rw 39 q36 ∷
   rw 40 q36 ∷
   rw 41 q36 ∷
   rw 42 q36 ∷
   rw 43 q36 ∷
   rw 44 q37 ∷
   rw 45 q38 ∷
   rw 46 q36 ∷
   rw 47 q36 ∷
   rw 48 q36 ∷
   rw 49 q36 ∷
   rw 50 q36 ∷
   rw 51 q36 ∷
   rw 52 q36 ∷
   rw 53 q36 ∷
   rw 54 q36 ∷
   re 56 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q26 ∷
   rw⁻ 57 q33 ∷
   rw 58 q28 ∷
   re 55 5 (CX03 ∷ []) ∷
   rw 56 q36 ∷
   rw 57 q36 ∷
   rw 58 q36 ∷
   rw 59 q37 ∷
   rw 60 q36 ∷
   rw 61 q36 ∷
   re 63 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) ∷
   re 64 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 63 q4 ∷
   rw 64 q5 ∷
   rw 65 q6 ∷
   rw 66 q7 ∷
   rw 67 q6 ∷
   re 69 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 68 q1 ∷
   rw 69 q8 ∷
   rw 70 q1 ∷
   re 68 3 (CS03 ∷ []) ∷
   rw 69 q4 ∷
   rw 70 q9 ∷
   rw 71 q17 ∷
   rw 62 q23 ∷
   rw 63 q24 ∷
   re 65 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 64 q19 ∷
   rw 65 q25 ∷
   re 67 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 66 q19 ∷
   re 68 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 67 q26 ∷
   rw⁻ 69 q27 ∷
   rw 70 q28 ∷
   re 67 5 (CS03 ∷ []) ∷
   rw 68 q23 ∷
   rw⁻ 69 q29 ∷
   rw 62 q30 ∷
   rw 63 q31 ∷
   re 65 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 64 q32 ∷
   rw⁻ 65 q33 ∷
   re 67 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 66 q32 ∷
   rw⁻ 67 q33 ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 68 q32 ∷
   rw 69 q31 ∷
   rw⁻ 70 q34 ∷
   rw 63 q35 ∷
   re 63 8 (Toff201 ∷ []) ∷
   re 62 3 (Toff301 ∷ []) ∷
   rw 65 q18 ∷
   re 63 3 (CS02 ∷ []) ∷
   rw 66 q18 ∷
   re 64 3 (CS02 ∷ []) ∷
   rw 67 q18 ∷
   re 65 3 (CK02 ∷ []) ∷
   rw 68 q18 ∷
   re 66 3 (CS02 ∷ []) ∷
   rw 69 q18 ∷
   re 67 3 (CK02 ∷ []) ∷
   rw 70 q18 ∷
   re 68 3 (CK02 ∷ []) ∷
   re 70 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 69 q26 ∷
   rw⁻ 71 q33 ∷
   rw 72 q28 ∷
   re 69 5 (CX03 ∷ []) ∷
   rw 70 q37 ∷
   rw 71 q38 ∷
   rw 72 q37 ∷
   rw 73 q38 ∷
   rw 74 q36 ∷
   rw 75 q36 ∷
   rw 76 q36 ∷
   rw 77 q37 ∷
   rw 78 q38 ∷
   rw 79 q36 ∷
   rw 80 q36 ∷
   rw 81 q36 ∷
   rw 82 q36 ∷
   rw 83 q36 ∷
   rw 84 q36 ∷
   re 86 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 85 q26 ∷
   rw⁻ 87 q33 ∷
   rw 88 q28 ∷
   re 85 5 (CX03 ∷ []) ∷
   rw 86 q36 ∷
   rw 87 q36 ∷
   rw 88 q37 ∷
   rw 89 q36 ∷
   rw 90 q37 ∷
   rw 91 q37 ∷
   rw 92 q19 ∷
   rw 2 q30 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 3 q30 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 4 q30 ∷
   re 2 3 (CK03 ∷ []) ∷
   rw 5 q30 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 6 q30 ∷
   re 4 3 (CK03 ∷ []) ∷
   rw 7 q30 ∷
   re 5 3 (CK03 ∷ []) ∷
   rw⁻ 6 q33 ∷
   rw 9 q30 ∷
   re 7 3 (CK13 ∷ []) ∷
   rw⁻ 8 q39 ∷
   rw 11 q30 ∷
   re 9 3 (CK13 ∷ []) ∷
   rw⁻ 10 q39 ∷
   rw 13 q30 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 14 q30 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 15 q30 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 16 q30 ∷
   re 14 3 (CK13 ∷ []) ∷
   rw⁻ 15 q39 ∷
   rw 18 q30 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw 19 q30 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 20 q30 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 21 q30 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 22 q30 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 23 q30 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw⁻ 22 q33 ∷
   rw 25 q30 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 26 q30 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 27 q30 ∷
   re 25 3 (CK13 ∷ []) ∷
   rw 28 q30 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 29 q30 ∷
   re 27 3 (CK13 ∷ []) ∷
   rw 30 q30 ∷
   re 28 3 (CK13 ∷ []) ∷
   re 30 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 31 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 30 q40 ∷
   rw 33 q30 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw⁻ 32 q33 ∷
   rw 35 q30 ∷
   re 33 3 (CS13⁻ ∷ []) ∷
   rw⁻ 34 q33 ∷
   rw 37 q30 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q40 ∷
   rw⁻ 37 q34 ∷
   rw 38 q32 ∷
   rw 29 q31 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q32 ∷
   rw⁻ 31 q33 ∷
   re 33 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 32 q32 ∷
   rw⁻ 33 q33 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q32 ∷
   rw 35 q31 ∷
   rw⁻ 36 q34 ∷
   rw 29 q35 ∷
   re 29 8 (Toff201 ∷ []) ∷
   rw 32 q30 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 33 q30 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 34 q30 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 35 q30 ∷
   re 33 3 (CK03 ∷ []) ∷
   rw 36 q30 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 37 q30 ∷
   re 35 3 (CS03 ∷ []) ∷
   re 37 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 36 q32 ∷
   rw 37 q41 ∷
   rw 38 q41 ∷
   rw 39 q41 ∷
   rw 40 q41 ∷
   rw 41 q41 ∷
   rw 42 q41 ∷
   rw 43 q42 ∷
   rw 44 q43 ∷
   rw 45 q41 ∷
   rw 46 q41 ∷
   rw 47 q41 ∷
   rw 48 q41 ∷
   rw 49 q41 ∷
   rw 50 q41 ∷
   rw 51 q41 ∷
   rw 52 q41 ∷
   rw 53 q41 ∷
   re 55 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 54 q32 ∷
   rw 55 q41 ∷
   rw 56 q41 ∷
   rw 57 q41 ∷
   rw 58 q42 ∷
   rw 59 q41 ∷
   rw 60 q41 ∷
   re 62 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 63 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 62 q40 ∷
   rw 65 q30 ∷
   re 63 3 (CS13 ∷ []) ∷
   rw⁻ 64 q33 ∷
   rw 67 q30 ∷ []) Eq.refl

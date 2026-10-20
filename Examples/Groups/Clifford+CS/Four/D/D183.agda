{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D183 (W : Ws) where

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
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn (Sw23 ∷ CX23 ∷ []) (CX32 ∷ Sw23 ∷ []) (wn 378 W)
  q3 : Eqn
  q3 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q4 : Eqn
  q4 = eqn (Sw23 ∷ S3 ∷ []) (S2 ∷ Sw23 ∷ []) (wn 372 W)
  q5 : Eqn
  q5 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q7 : Eqn
  q7 = eqn (Sw01 ∷ CK20 ∷ []) (CK21 ∷ Sw01 ∷ []) (wn 275 W)
  q8 : Eqn
  q8 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ CK10 ∷ []) (CK01 ∷ Sw01 ∷ []) (wn 327 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ S1 ∷ []) (S0 ∷ Sw01 ∷ []) (wn 315 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) (wn 219 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q16 : Eqn
  q16 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) (wn 122 W)
  q18 : Eqn
  q18 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q20 : Eqn
  q20 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q21 : Eqn
  q21 = eqn (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wn 334 W)
  q22 : Eqn
  q22 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q23 : Eqn
  q23 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q24 : Eqn
  q24 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q25 : Eqn
  q25 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q26 : Eqn
  q26 = eqn (Sw12 ∷ CK31 ∷ []) (CK32 ∷ Sw12 ∷ []) (wn 359 W)
  q27 : Eqn
  q27 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q28 : Eqn
  q28 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))
  q29 : Eqn
  q29 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q30 : Eqn
  q30 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q31 : Eqn
  q31 = eqn (S0 ∷ Sw12 ∷ []) (Sw12 ∷ S0 ∷ []) (low₁-comm (S) (Swap))
  q32 : Eqn
  q32 = eqn (Sw12 ∷ K2 ∷ []) (K1 ∷ Sw12 ∷ []) (wn 345 W)
  q33 : Eqn
  q33 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q34 : Eqn
  q34 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q35 : Eqn
  q35 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q36 : Eqn
  q36 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q37 : Eqn
  q37 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q38 : Eqn
  q38 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q39 : Eqn
  q39 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q40 : Eqn
  q40 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q41 : Eqn
  q41 = eqn (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 196 W)
  q42 : Eqn
  q42 = eqn (Sw12 ∷ CX32 ∷ []) (CX31 ∷ Sw12 ∷ []) (wn 114 W)
  q43 : Eqn
  q43 = eqn (Sw12 ∷ CS12 ∷ []) (CS12 ∷ Sw12 ∷ []) (wn 18 W)
  q44 : Eqn
  q44 = eqn (Sw12 ∷ CK21 ∷ []) (CK12 ∷ Sw12 ∷ []) (wn 355 W)
  q45 : Eqn
  q45 = eqn (Sw12 ∷ S2 ∷ []) (S1 ∷ Sw12 ∷ []) (wn 343 W)

-- AXIOM LF @2301 part2: 477 steps
lem-AXIOM-LF-at2301-part2 : ⟪ (Sw12 ∷ Sw01 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ Toff213 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ Toff213 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Toff103 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ Toff103 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) ⟫ʷ
lem-AXIOM-LF-at2301-part2 = derive (Sw12 ∷ Sw01 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ Toff213 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ Toff213 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Toff103 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ Toff103 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  (re 68 3 (CK30 ∷ []) ∷
   rw 71 q1 ∷
   re 69 3 (CK30 ∷ []) ∷
   rw 70 q2 ∷
   re 72 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 71 q3 ∷
   rw 72 q4 ∷
   re 74 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 73 q3 ∷
   rw 74 q4 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q3 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q3 ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q3 ∷
   re 79 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 78 q3 ∷
   rw 79 q4 ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 80 q3 ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 81 q3 ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 82 q3 ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 83 q3 ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 84 q3 ∷
   re 86 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 85 q3 ∷
   rw 86 q2 ∷
   re 88 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 87 q3 ∷
   re 89 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 88 q3 ∷
   re 90 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 89 q3 ∷
   re 91 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 90 q3 ∷
   re 92 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 91 q3 ∷
   re 93 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 92 q3 ∷
   rw 93 q3 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   rw 2 q6 ∷
   rw 3 q5 ∷
   re 1 3 (CS13 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   rw 4 q5 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 4 q7 ∷
   rw 5 q5 ∷
   re 3 3 (CK31 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 4 3 (CS13 ∷ []) ∷
   re 6 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q7 ∷
   rw 7 q5 ∷
   re 5 3 (CK31 ∷ []) ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q7 ∷
   rw 8 q5 ∷
   re 6 3 (CK31 ∷ []) ∷
   re 8 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q8 ∷
   rw 9 q5 ∷
   re 7 3 (CX30 ∷ []) ∷
   rw 8 q9 ∷
   rw 9 q10 ∷
   rw 10 q9 ∷
   rw 11 q10 ∷
   rw 12 q11 ∷
   rw 13 q11 ∷
   rw 14 q11 ∷
   rw 15 q9 ∷
   rw 16 q10 ∷
   rw 17 q11 ∷
   rw 18 q11 ∷
   rw 19 q11 ∷
   rw 20 q11 ∷
   rw 21 q11 ∷
   rw 22 q11 ∷
   re 24 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 23 q5 ∷
   rw 24 q8 ∷
   rw 25 q5 ∷
   re 23 3 (CX30 ∷ []) ∷
   rw 24 q11 ∷
   rw 25 q11 ∷
   rw 26 q9 ∷
   rw 27 q11 ∷
   rw 28 q9 ∷
   rw 29 q9 ∷
   re 31 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 30 q12 ∷
   rw 31 q13 ∷
   rw 32 q14 ∷
   rw 33 q15 ∷
   rw 34 q14 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q5 ∷
   rw 36 q16 ∷
   rw 37 q5 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q12 ∷
   rw 37 q17 ∷
   rw 30 q18 ∷
   rw 31 q12 ∷
   rw 32 q13 ∷
   rw 33 q19 ∷
   rw 34 q15 ∷
   rw 35 q19 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q5 ∷
   rw 37 q6 ∷
   rw 38 q5 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 37 q12 ∷
   rw 38 q20 ∷
   rw 31 q21 ∷
   re 31 8 (Toff213 ∷ []) ∷
   re 30 3 (Toff203 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q5 ∷
   rw 32 q6 ∷
   rw 33 q5 ∷
   re 31 3 (CS13 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q5 ∷
   rw 33 q6 ∷
   rw 34 q5 ∷
   re 32 3 (CS13 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q5 ∷
   rw 34 q6 ∷
   rw 35 q5 ∷
   re 33 3 (CS13 ∷ []) ∷
   re 35 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 34 q5 ∷
   rw 35 q7 ∷
   rw 36 q5 ∷
   re 34 3 (CK31 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q5 ∷
   rw 36 q6 ∷
   rw 37 q5 ∷
   re 35 3 (CS13 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q5 ∷
   rw 37 q6 ∷
   rw 38 q5 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 37 q22 ∷
   rw 38 q6 ∷
   rw 39 q6 ∷
   rw 40 q6 ∷
   rw 41 q6 ∷
   rw 42 q6 ∷
   rw 43 q6 ∷
   rw 44 q7 ∷
   rw 45 q23 ∷
   rw 46 q6 ∷
   rw 47 q6 ∷
   rw 48 q6 ∷
   rw 49 q6 ∷
   rw 50 q6 ∷
   rw 51 q6 ∷
   rw 52 q6 ∷
   rw 53 q6 ∷
   rw 54 q6 ∷
   rw 55 q22 ∷
   rw 56 q6 ∷
   rw 57 q6 ∷
   rw 58 q6 ∷
   rw 59 q7 ∷
   rw 60 q6 ∷
   rw 61 q6 ∷
   re 63 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 62 q12 ∷
   rw 63 q13 ∷
   rw 64 q14 ∷
   rw 65 q15 ∷
   rw 66 q14 ∷
   re 68 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 67 q5 ∷
   rw 68 q16 ∷
   rw 69 q5 ∷
   re 67 3 (CS03 ∷ []) ∷
   rw 68 q12 ∷
   rw 69 q17 ∷
   rw 62 q18 ∷
   rw 63 q12 ∷
   rw 64 q13 ∷
   rw 65 q19 ∷
   rw 66 q15 ∷
   rw 67 q19 ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 68 q5 ∷
   rw 69 q6 ∷
   rw 70 q5 ∷
   re 68 3 (CS13 ∷ []) ∷
   rw 69 q12 ∷
   rw 70 q20 ∷
   rw 63 q21 ∷
   re 63 8 (Toff213 ∷ []) ∷
   re 62 3 (Toff203 ∷ []) ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 63 q5 ∷
   rw 64 q6 ∷
   rw 65 q5 ∷
   re 63 3 (CS13 ∷ []) ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 64 q5 ∷
   rw 65 q6 ∷
   rw 66 q5 ∷
   re 64 3 (CS13 ∷ []) ∷
   re 66 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 65 q5 ∷
   rw 66 q7 ∷
   rw 67 q5 ∷
   re 65 3 (CK31 ∷ []) ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 66 q5 ∷
   rw 67 q6 ∷
   rw 68 q5 ∷
   re 66 3 (CS13 ∷ []) ∷
   re 68 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 67 q5 ∷
   rw 68 q7 ∷
   rw 69 q5 ∷
   re 67 3 (CK31 ∷ []) ∷
   re 69 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 68 q5 ∷
   rw 69 q7 ∷
   rw 70 q5 ∷
   re 68 3 (CK31 ∷ []) ∷
   rw 69 q22 ∷
   rw 70 q7 ∷
   rw 71 q23 ∷
   rw 72 q7 ∷
   rw 73 q23 ∷
   rw 74 q6 ∷
   rw 75 q6 ∷
   rw 76 q6 ∷
   rw 77 q7 ∷
   rw 78 q23 ∷
   rw 79 q6 ∷
   rw 80 q6 ∷
   rw 81 q6 ∷
   rw 82 q6 ∷
   rw 83 q6 ∷
   rw 84 q6 ∷
   rw 85 q22 ∷
   rw 86 q6 ∷
   rw 87 q6 ∷
   rw 88 q7 ∷
   rw 89 q6 ∷
   rw 90 q7 ∷
   rw 91 q7 ∷
   rw 92 q24 ∷
   rw 0 q25 ∷
   rw 1 q25 ∷
   rw 2 q26 ∷
   rw 3 q25 ∷
   rw 4 q26 ∷
   rw 5 q26 ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 6 q27 ∷
   rw⁻ 8 q28 ∷
   rw 9 q29 ∷
   re 6 5 (CX30 ∷ []) ∷
   rw 9 q30 ∷
   re 7 3 (CK02 ∷ []) ∷
   rw⁻ 8 q31 ∷
   rw 11 q30 ∷
   re 9 3 (CK02 ∷ []) ∷
   rw⁻ 10 q31 ∷
   rw 13 q30 ∷
   re 11 3 (CS02 ∷ []) ∷
   rw 14 q30 ∷
   re 12 3 (CS02 ∷ []) ∷
   rw 15 q30 ∷
   re 13 3 (CS02 ∷ []) ∷
   rw 16 q30 ∷
   re 14 3 (CK02 ∷ []) ∷
   rw⁻ 15 q31 ∷
   rw 18 q30 ∷
   re 16 3 (CS02 ∷ []) ∷
   rw 19 q30 ∷
   re 17 3 (CS02 ∷ []) ∷
   rw 20 q30 ∷
   re 18 3 (CS02 ∷ []) ∷
   rw 21 q30 ∷
   re 19 3 (CS02 ∷ []) ∷
   rw 22 q30 ∷
   re 20 3 (CS02 ∷ []) ∷
   rw 23 q30 ∷
   re 21 3 (CS02 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q27 ∷
   rw⁻ 24 q28 ∷
   rw 25 q29 ∷
   re 22 5 (CX30 ∷ []) ∷
   rw 25 q30 ∷
   re 23 3 (CS02 ∷ []) ∷
   rw 26 q30 ∷
   re 24 3 (CS02 ∷ []) ∷
   rw 27 q30 ∷
   re 25 3 (CK02 ∷ []) ∷
   rw 28 q30 ∷
   re 26 3 (CS02 ∷ []) ∷
   rw 29 q30 ∷
   re 27 3 (CK02 ∷ []) ∷
   rw 30 q30 ∷
   re 28 3 (CK02 ∷ []) ∷
   re 30 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 31 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 30 q12 ∷
   rw 31 q13 ∷
   rw 32 q14 ∷
   rw 33 q15 ∷
   rw 34 q14 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q5 ∷
   rw 36 q16 ∷
   rw 37 q5 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q12 ∷
   rw 37 q17 ∷
   rw 38 q24 ∷
   rw 29 q32 ∷
   rw 30 q33 ∷
   re 32 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 31 q34 ∷
   rw 32 q35 ∷
   re 34 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 33 q34 ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q27 ∷
   rw⁻ 36 q36 ∷
   rw 37 q29 ∷
   re 34 5 (CS03 ∷ []) ∷
   rw 35 q32 ∷
   rw⁻ 36 q37 ∷
   rw 29 q1 ∷
   rw⁻ 30 q38 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q3 ∷
   rw⁻ 32 q39 ∷
   re 34 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 33 q3 ∷
   rw⁻ 34 q39 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q3 ∷
   rw⁻ 36 q38 ∷
   rw⁻ 37 q40 ∷
   rw 30 q41 ∷
   re 30 8 (Toff102 ∷ []) ∷
   re 29 3 (Toff103 ∷ []) ∷
   rw 30 q25 ∷
   rw 31 q25 ∷
   rw 32 q25 ∷
   rw 33 q26 ∷
   rw 34 q25 ∷
   rw 35 q25 ∷
   rw 36 q42 ∷
   rw 37 q43 ∷
   rw 38 q43 ∷
   rw 39 q43 ∷
   rw 40 q43 ∷
   rw 41 q43 ∷
   rw 42 q43 ∷
   rw 43 q44 ∷
   rw 44 q45 ∷
   rw 45 q43 ∷
   rw 46 q43 ∷
   rw 47 q43 ∷
   rw 48 q43 ∷
   rw 49 q43 ∷
   rw 50 q43 ∷
   rw 51 q43 ∷
   rw 52 q43 ∷
   rw 53 q43 ∷
   rw 54 q42 ∷
   rw 55 q43 ∷
   rw 56 q43 ∷
   rw 57 q43 ∷
   rw 58 q44 ∷
   rw 59 q43 ∷
   rw 60 q43 ∷
   re 62 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 63 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 62 q12 ∷
   rw 63 q13 ∷
   rw 64 q14 ∷
   rw 65 q15 ∷
   rw 66 q14 ∷
   re 68 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 67 q5 ∷
   rw 68 q16 ∷
   rw 69 q5 ∷
   re 67 3 (CS03 ∷ []) ∷
   rw 68 q12 ∷
   rw 69 q17 ∷
   rw 70 q24 ∷
   rw 61 q32 ∷
   rw 62 q33 ∷
   re 64 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 63 q34 ∷
   rw 64 q35 ∷
   re 66 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 65 q34 ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 66 q27 ∷
   rw⁻ 68 q36 ∷
   rw 69 q29 ∷
   re 66 5 (CS03 ∷ []) ∷
   rw 67 q32 ∷
   rw⁻ 68 q37 ∷
   rw 61 q1 ∷
   rw⁻ 62 q38 ∷
   re 64 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 63 q3 ∷
   rw⁻ 64 q39 ∷
   re 66 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 65 q3 ∷
   rw⁻ 66 q39 ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q3 ∷
   rw⁻ 68 q38 ∷
   rw⁻ 69 q40 ∷
   rw 62 q41 ∷
   re 62 8 (Toff102 ∷ []) ∷
   re 61 3 (Toff103 ∷ []) ∷
   rw 62 q25 ∷
   rw 63 q25 ∷
   rw 64 q26 ∷
   rw 65 q25 ∷
   rw 66 q26 ∷
   rw 67 q26 ∷
   rw 68 q42 ∷
   rw 69 q44 ∷
   rw 70 q45 ∷
   rw 71 q44 ∷
   rw 72 q45 ∷
   rw 73 q43 ∷
   rw 74 q43 ∷
   rw 75 q43 ∷
   rw 76 q44 ∷
   rw 77 q45 ∷
   rw 78 q43 ∷
   rw 79 q43 ∷
   rw 80 q43 ∷
   rw 81 q43 ∷
   rw 82 q43 ∷
   rw 83 q43 ∷
   rw 84 q42 ∷
   rw 85 q43 ∷
   rw 86 q43 ∷
   rw 87 q44 ∷
   rw 88 q43 ∷
   rw 89 q44 ∷
   rw 90 q44 ∷
   rw 91 q34 ∷ []) Eq.refl

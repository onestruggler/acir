{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D027 (W : Ws) where

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
  q1 = wE 5 W
  q2 : Eqn
  q2 = wE 273 W
  q3 : Eqn
  q3 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q4 : Eqn
  q4 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = wE 10 W
  q6 : Eqn
  q6 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q7 : Eqn
  q7 = wE 6 W
  q8 : Eqn
  q8 = wE 216 W
  q9 : Eqn
  q9 = wE 480 W
  q10 : Eqn
  q10 = wE 481 W
  q11 : Eqn
  q11 = wE 1 W
  q12 : Eqn
  q12 = wE 476 W
  q13 : Eqn
  q13 = wE 3 W
  q14 : Eqn
  q14 = wE 464 W
  q15 : Eqn
  q15 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q16 : Eqn
  q16 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q17 : Eqn
  q17 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q18 : Eqn
  q18 = wE 12 W
  q19 : Eqn
  q19 = wE 22 W
  q20 : Eqn
  q20 = wE 23 W
  q21 : Eqn
  q21 = eqn (Sw12 ∷ S3 ∷ []) (S3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (S))
  q22 : Eqn
  q22 = wE 14 W
  q23 : Eqn
  q23 = wE 477 W
  q24 : Eqn
  q24 = wE 478 W
  q25 : Eqn
  q25 = wE 479 W
  q26 : Eqn
  q26 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))
  q27 : Eqn
  q27 = wE 50 W
  q28 : Eqn
  q28 = wE 343 W
  q29 : Eqn
  q29 = eqn (Sw12 ∷ K3 ∷ []) (K3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (K))
  q30 : Eqn
  q30 = wE 49 W
  q31 : Eqn
  q31 = wE 51 W
  q32 : Eqn
  q32 = wE 20 W
  q33 : Eqn
  q33 = wE 364 W
  q34 : Eqn
  q34 = wE 369 W
  q35 : Eqn
  q35 = wE 157 W

-- AXIOM LF @1302 part0: 500 steps
lem-AXIOM-LF-at1302-part0 : ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S2 ∷ CK21 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ Toff312 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) ⟫ʷ
lem-AXIOM-LF-at1302-part0 = derive (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S2 ∷ CK21 ∷ []) (Sw01 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ Toff312 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  (rw 80 q1 ∷
   rw 79 q2 ∷
   rw⁻ 78 q3 ∷
   re 77 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 79 q4 ∷
   rw 78 q5 ∷
   rw⁻ 77 q4 ∷
   re 78 3 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 78 q4 ∷
   rw 77 q5 ∷
   rw⁻ 76 q4 ∷
   re 77 3 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 77 q4 ∷
   rw 76 q5 ∷
   rw⁻ 75 q4 ∷
   re 76 3 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 76 q4 ∷
   rw 75 q5 ∷
   rw⁻ 74 q4 ∷
   re 75 3 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 75 q4 ∷
   rw 74 q5 ∷
   rw⁻ 73 q4 ∷
   re 74 3 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 74 q4 ∷
   rw 73 q5 ∷
   rw⁻ 72 q4 ∷
   re 73 3 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw⁻ 73 q4 ∷
   rw 72 q2 ∷
   rw⁻ 71 q4 ∷
   re 72 3 (CK30 ∷ []) ∷
   rw⁻ 70 q6 ∷
   re 69 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 71 q4 ∷
   rw 70 q5 ∷
   rw⁻ 69 q4 ∷
   re 70 3 (CS03 ∷ []) ∷
   re 68 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 70 q4 ∷
   rw 69 q5 ∷
   rw⁻ 68 q4 ∷
   re 69 3 (CS03 ∷ []) ∷
   re 67 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 69 q4 ∷
   rw 68 q5 ∷
   rw⁻ 67 q4 ∷
   re 68 3 (CS03 ∷ []) ∷
   re 66 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 68 q4 ∷
   rw 67 q7 ∷
   rw⁻ 66 q4 ∷
   re 67 3 (CX31 ∷ []) ∷
   rw 65 q8 ∷
   rw 64 q8 ∷
   rw 63 q8 ∷
   rw 62 q8 ∷
   rw 61 q8 ∷
   rw 60 q8 ∷
   rw 59 q8 ∷
   rw 58 q8 ∷
   rw 57 q8 ∷
   rw 56 q9 ∷
   rw 55 q10 ∷
   rw 54 q10 ∷
   rw 53 q10 ∷
   rw 52 q10 ∷
   rw 51 q8 ∷
   rw 50 q8 ∷
   rw 49 q8 ∷
   rw 48 q8 ∷
   rw 47 q8 ∷
   rw 46 q8 ∷
   rw 45 q8 ∷
   rw 44 q8 ∷
   rw 43 q8 ∷
   rw 42 q8 ∷
   rw 41 q8 ∷
   rw 40 q8 ∷
   rw 39 q8 ∷
   rw 38 q8 ∷
   rw 37 q8 ∷
   rw 36 q8 ∷
   rw 35 q8 ∷
   rw 34 q8 ∷
   re 33 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q4 ∷
   rw 34 q7 ∷
   rw⁻ 33 q4 ∷
   re 34 3 (CX31 ∷ []) ∷
   rw 32 q8 ∷
   rw 31 q8 ∷
   rw 30 q8 ∷
   rw 29 q8 ∷
   rw 28 q8 ∷
   rw 27 q8 ∷
   rw 26 q9 ∷
   rw 25 q10 ∷
   rw 24 q8 ∷
   rw 23 q8 ∷
   rw 22 q8 ∷
   rw 21 q2 ∷
   rw 20 q8 ∷
   rw 19 q9 ∷
   rw 18 q8 ∷
   rw 17 q8 ∷
   re 16 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q4 ∷
   rw 17 q7 ∷
   rw⁻ 16 q4 ∷
   re 17 3 (CX31 ∷ []) ∷
   rw 15 q8 ∷
   rw 14 q8 ∷
   rw 13 q8 ∷
   rw 12 q8 ∷
   rw 11 q8 ∷
   rw 10 q8 ∷
   rw 9 q10 ∷
   rw 8 q9 ∷
   rw 7 q8 ∷
   rw 6 q8 ∷
   rw 5 q8 ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 5 q7 ∷
   rw⁻ 4 q4 ∷
   re 5 3 (CX31 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 4 q5 ∷
   rw⁻ 3 q4 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 2 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 3 q2 ∷
   rw⁻ 2 q4 ∷
   re 3 3 (CK30 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 2 q5 ∷
   rw⁻ 1 q4 ∷
   re 2 3 (CS03 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 1 q5 ∷
   rw⁻ 0 q4 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 81 q11 ∷
   rw 80 q11 ∷
   re 81 3 (CK30 ∷ []) ∷
   rw 79 q12 ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 80 q13 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q13 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q13 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q13 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q13 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q13 ∷
   re 72 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 74 q13 ∷
   rw 71 q14 ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 72 q13 ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 71 q13 ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 70 q13 ∷
   re 67 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 69 q13 ∷
   rw 66 q15 ∷
   rw 65 q15 ∷
   rw 64 q15 ∷
   rw 63 q15 ∷
   rw 62 q15 ∷
   rw 61 q15 ∷
   rw 60 q15 ∷
   rw 59 q15 ∷
   rw 58 q15 ∷
   rw 57 q16 ∷
   rw 56 q17 ∷
   rw 55 q17 ∷
   rw 54 q17 ∷
   rw 53 q17 ∷
   rw 52 q15 ∷
   rw 51 q15 ∷
   rw 50 q15 ∷
   rw 49 q15 ∷
   rw 48 q15 ∷
   rw 47 q15 ∷
   rw 46 q15 ∷
   rw 45 q15 ∷
   rw 44 q15 ∷
   rw 43 q15 ∷
   rw 42 q15 ∷
   rw 41 q15 ∷
   rw 40 q15 ∷
   rw 39 q15 ∷
   rw 38 q15 ∷
   rw 37 q15 ∷
   rw 36 q15 ∷
   rw 35 q15 ∷
   re 34 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 36 q13 ∷
   rw 33 q15 ∷
   rw 32 q15 ∷
   rw 31 q15 ∷
   rw 30 q15 ∷
   rw 29 q15 ∷
   rw 28 q15 ∷
   rw 27 q16 ∷
   rw 26 q17 ∷
   rw 25 q15 ∷
   rw 24 q15 ∷
   rw 23 q15 ∷
   rw 22 q11 ∷
   re 23 3 (CK30 ∷ []) ∷
   rw 21 q15 ∷
   rw 20 q16 ∷
   rw 19 q15 ∷
   rw 18 q15 ∷
   re 17 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 19 q13 ∷
   rw 16 q15 ∷
   rw 15 q15 ∷
   rw 14 q15 ∷
   rw 13 q15 ∷
   rw 12 q15 ∷
   rw 11 q15 ∷
   rw 10 q17 ∷
   rw 9 q16 ∷
   rw 8 q15 ∷
   rw 7 q15 ∷
   rw 6 q15 ∷
   re 5 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 7 q13 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q13 ∷
   re 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 5 q13 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q13 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q13 ∷
   rw 82 q18 ∷
   re 81 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 84 q19 ∷
   rw 83 q16 ∷
   rw 81 q20 ∷
   re 82 5 (CK30 ∷ []) ∷
   rw⁻ 80 q21 ∷
   re 79 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 81 q22 ∷
   re 78 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 80 q22 ∷
   re 77 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 79 q22 ∷
   re 76 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 78 q22 ∷
   re 75 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 77 q22 ∷
   re 74 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 76 q22 ∷
   re 73 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 75 q22 ∷
   rw 72 q23 ∷
   re 71 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 73 q22 ∷
   re 70 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 72 q22 ∷
   re 69 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 71 q22 ∷
   rw 68 q24 ∷
   rw 67 q18 ∷
   re 68 3 (CS02 ∷ []) ∷
   rw 66 q18 ∷
   re 67 3 (CS02 ∷ []) ∷
   rw 65 q18 ∷
   re 66 3 (CS02 ∷ []) ∷
   rw 64 q18 ∷
   re 65 3 (CS02 ∷ []) ∷
   rw 63 q18 ∷
   re 64 3 (CS02 ∷ []) ∷
   rw 62 q18 ∷
   re 63 3 (CS02 ∷ []) ∷
   rw 61 q18 ∷
   re 62 3 (CS02 ∷ []) ∷
   rw 60 q18 ∷
   re 61 3 (CS02 ∷ []) ∷
   rw 59 q18 ∷
   re 60 3 (CS02 ∷ []) ∷
   rw 58 q18 ∷
   re 59 3 (CK20 ∷ []) ∷
   rw 57 q25 ∷
   rw 56 q25 ∷
   rw 55 q25 ∷
   rw 54 q25 ∷
   rw 53 q18 ∷
   re 54 3 (CS02 ∷ []) ∷
   rw 52 q18 ∷
   re 53 3 (CS02 ∷ []) ∷
   rw 51 q18 ∷
   re 52 3 (CS02 ∷ []) ∷
   rw 50 q18 ∷
   re 51 3 (CS02 ∷ []) ∷
   rw 49 q18 ∷
   re 50 3 (CS02 ∷ []) ∷
   rw 48 q18 ∷
   re 49 3 (CS02 ∷ []) ∷
   rw 47 q18 ∷
   re 48 3 (CS02 ∷ []) ∷
   rw 46 q18 ∷
   re 47 3 (CS02 ∷ []) ∷
   rw 45 q18 ∷
   re 46 3 (CS02 ∷ []) ∷
   rw 44 q18 ∷
   re 45 3 (CS02 ∷ []) ∷
   rw 43 q18 ∷
   re 44 3 (CS02 ∷ []) ∷
   rw 42 q18 ∷
   re 43 3 (CS02 ∷ []) ∷
   rw 41 q18 ∷
   re 42 3 (CS02 ∷ []) ∷
   rw 40 q18 ∷
   re 41 3 (CS02 ∷ []) ∷
   rw 39 q18 ∷
   re 40 3 (CS02 ∷ []) ∷
   rw 38 q18 ∷
   re 39 3 (CS02 ∷ []) ∷
   rw 37 q18 ∷
   re 38 3 (CS02 ∷ []) ∷
   rw 36 q18 ∷
   re 37 3 (CS02 ∷ []) ∷
   rw 35 q24 ∷
   rw 34 q18 ∷
   re 35 3 (CS02 ∷ []) ∷
   rw 33 q18 ∷
   re 34 3 (CS02 ∷ []) ∷
   rw 32 q18 ∷
   re 33 3 (CS02 ∷ []) ∷
   rw 31 q18 ∷
   re 32 3 (CS02 ∷ []) ∷
   rw 30 q18 ∷
   re 31 3 (CS02 ∷ []) ∷
   rw 29 q18 ∷
   re 30 3 (CS02 ∷ []) ∷
   rw 28 q18 ∷
   re 29 3 (CK20 ∷ []) ∷
   rw 27 q25 ∷
   rw 26 q18 ∷
   re 27 3 (CS02 ∷ []) ∷
   rw 25 q18 ∷
   re 26 3 (CS02 ∷ []) ∷
   rw 24 q18 ∷
   re 25 3 (CS02 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q19 ∷
   rw 25 q16 ∷
   rw 23 q20 ∷
   re 24 5 (CK30 ∷ []) ∷
   rw 22 q18 ∷
   re 23 3 (CS02 ∷ []) ∷
   rw 21 q18 ∷
   re 22 3 (CK20 ∷ []) ∷
   rw 20 q18 ∷
   re 21 3 (CS02 ∷ []) ∷
   rw 19 q18 ∷
   re 20 3 (CS02 ∷ []) ∷
   rw 18 q24 ∷
   rw 17 q18 ∷
   re 18 3 (CS02 ∷ []) ∷
   rw 16 q18 ∷
   re 17 3 (CS02 ∷ []) ∷
   rw 15 q18 ∷
   re 16 3 (CS02 ∷ []) ∷
   rw 14 q18 ∷
   re 15 3 (CS02 ∷ []) ∷
   rw 13 q18 ∷
   re 14 3 (CS02 ∷ []) ∷
   rw 12 q18 ∷
   re 13 3 (CS02 ∷ []) ∷
   rw 11 q25 ∷
   rw 10 q18 ∷
   re 11 3 (CK20 ∷ []) ∷
   rw 9 q18 ∷
   re 10 3 (CS02 ∷ []) ∷
   rw 8 q18 ∷
   re 9 3 (CS02 ∷ []) ∷
   rw 7 q18 ∷
   re 8 3 (CS02 ∷ []) ∷
   rw 6 q24 ∷
   re 5 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 q22 ∷
   re 4 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 6 q22 ∷
   re 3 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 5 q22 ∷
   re 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 4 q22 ∷
   rw 3 q26 ∷
   rw 4 q18 ∷
   re 2 3 (CS02 ∷ []) ∷
   rw 5 q18 ∷
   re 3 3 (CS02 ∷ []) ∷
   rw 6 q18 ∷
   re 4 3 (CK20 ∷ []) ∷
   rw 7 q18 ∷
   re 5 3 (CS02 ∷ []) ∷
   rw 8 q18 ∷
   re 6 3 (CK20 ∷ []) ∷
   rw 9 q18 ∷
   re 7 3 (CK20 ∷ []) ∷
   rw 8 q27 ∷
   re 10 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 9 q22 ∷
   rw 10 q28 ∷
   re 12 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 11 q22 ∷
   rw 12 q28 ∷
   re 14 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 13 q22 ∷
   re 15 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 14 q22 ∷
   re 16 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 15 q22 ∷
   re 17 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 16 q22 ∷
   rw 17 q28 ∷
   re 19 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 18 q22 ∷
   re 20 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 19 q22 ∷
   re 21 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 20 q22 ∷
   re 22 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 21 q22 ∷
   re 23 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 22 q22 ∷
   re 24 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 23 q22 ∷
   rw 24 q27 ∷
   re 26 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 25 q22 ∷
   re 27 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 26 q22 ∷
   re 28 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 27 q22 ∷
   re 29 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 28 q22 ∷
   re 30 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 29 q22 ∷
   re 31 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 30 q22 ∷
   re 32 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 31 q29 ∷
   rw 32 q30 ∷
   rw 33 q27 ∷
   rw 34 q31 ∷
   rw 35 q27 ∷
   rw 36 q32 ∷
   rw 37 q29 ∷
   rw 38 q33 ∷
   rw 31 q34 ∷
   re 31 8 (Toff312 ∷ []) ∷
   rw 34 q18 ∷
   re 32 3 (CS02 ∷ []) ∷
   rw 35 q18 ∷
   re 33 3 (CS02 ∷ []) ∷
   rw 36 q18 ∷
   re 34 3 (CS02 ∷ []) ∷
   rw 37 q18 ∷
   re 35 3 (CK20 ∷ []) ∷
   rw 38 q18 ∷
   re 36 3 (CS02 ∷ []) ∷
   rw 39 q18 ∷
   re 37 3 (CS02 ∷ []) ∷
   rw 38 q35 ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q19 ∷
   rw⁻ 41 q15 ∷
   rw 42 q20 ∷
   re 39 5 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q19 ∷
   rw⁻ 42 q15 ∷
   rw 43 q20 ∷
   re 40 5 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q19 ∷
   rw⁻ 43 q15 ∷ []) Eq.refl

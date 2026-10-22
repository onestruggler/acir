{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D081 (W : Ws) where

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
  q2 = wE 479 W
  q3 : Eqn
  q3 = wE 14 W
  q4 : Eqn
  q4 = wE 477 W
  q5 : Eqn
  q5 = wE 37 W
  q6 : Eqn
  q6 = wE 22 W
  q7 : Eqn
  q7 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q8 : Eqn
  q8 = wE 23 W
  q9 : Eqn
  q9 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q10 : Eqn
  q10 = eqn (Sw12 ∷ S3 ∷ []) (S3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (S))
  q11 : Eqn
  q11 = wE 1 W
  q12 : Eqn
  q12 = wE 476 W
  q13 : Eqn
  q13 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q14 : Eqn
  q14 = wE 3 W
  q15 : Eqn
  q15 = wE 464 W
  q16 : Eqn
  q16 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))
  q17 : Eqn
  q17 = wE 151 W
  q18 : Eqn
  q18 = wE 336 W
  q19 : Eqn
  q19 = wE 71 W
  q20 : Eqn
  q20 = wE 72 W
  q21 : Eqn
  q21 = eqn (ι1 ∷ Sw23 ∷ []) (Sw23 ∷ ι1 ∷ []) (low-comm ((iI ↑)) (Swap))
  q22 : Eqn
  q22 = wE 386 W
  q23 : Eqn
  q23 = wE 372 W
  q24 : Eqn
  q24 = wE 157 W
  q25 : Eqn
  q25 = wE 345 W
  q26 : Eqn
  q26 = wE 49 W
  q27 : Eqn
  q27 = wE 50 W
  q28 : Eqn
  q28 = wE 51 W
  q29 : Eqn
  q29 = wE 20 W
  q30 : Eqn
  q30 = wE 364 W
  q31 : Eqn
  q31 = wE 367 W
  q32 : Eqn
  q32 = wE 343 W

-- AXIOM LF @0231: 869 steps
lem-AXIOM-LF-at0231 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ Toff123 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ Toff123 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-AXIOM-LF-at0231 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ Toff123 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ Toff123 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 80 q1 ∷
   rw 79 q1 ∷
   re 80 3 (CK20 ∷ []) ∷
   rw 78 q2 ∷
   re 77 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 79 q3 ∷
   re 76 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 78 q3 ∷
   re 75 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 77 q3 ∷
   re 74 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 76 q3 ∷
   re 73 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 75 q3 ∷
   re 72 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 74 q3 ∷
   re 71 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 73 q3 ∷
   rw 70 q4 ∷
   re 69 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 71 q3 ∷
   re 68 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 70 q3 ∷
   re 67 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 69 q3 ∷
   rw 66 q5 ∷
   re 65 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 68 q6 ∷
   rw 67 q7 ∷
   rw 65 q8 ∷
   re 66 5 (CS03 ∷ []) ∷
   re 64 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 67 q6 ∷
   rw 66 q7 ∷
   rw 64 q8 ∷
   re 65 5 (CS03 ∷ []) ∷
   re 63 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 66 q6 ∷
   rw 65 q7 ∷
   rw 63 q8 ∷
   re 64 5 (CS03 ∷ []) ∷
   re 62 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 65 q6 ∷
   rw 64 q7 ∷
   rw 62 q8 ∷
   re 63 5 (CS03 ∷ []) ∷
   re 61 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 64 q6 ∷
   rw 63 q7 ∷
   rw 61 q8 ∷
   re 62 5 (CS03 ∷ []) ∷
   re 60 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 63 q6 ∷
   rw 62 q7 ∷
   rw 60 q8 ∷
   re 61 5 (CS03 ∷ []) ∷
   re 59 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 62 q6 ∷
   rw 61 q7 ∷
   rw 59 q8 ∷
   re 60 5 (CS03 ∷ []) ∷
   re 58 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 61 q6 ∷
   rw 60 q7 ∷
   rw 58 q8 ∷
   re 59 5 (CS03 ∷ []) ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 60 q6 ∷
   rw 59 q7 ∷
   rw 57 q8 ∷
   re 58 5 (CS03 ∷ []) ∷
   re 56 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q6 ∷
   rw 58 q9 ∷
   rw 56 q8 ∷
   re 57 5 (CK30 ∷ []) ∷
   rw⁻ 55 q10 ∷
   rw⁻ 54 q10 ∷
   rw⁻ 53 q10 ∷
   rw⁻ 52 q10 ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q6 ∷
   rw 53 q7 ∷
   rw 51 q8 ∷
   re 52 5 (CS03 ∷ []) ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q6 ∷
   rw 52 q7 ∷
   rw 50 q8 ∷
   re 51 5 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q6 ∷
   rw 51 q7 ∷
   rw 49 q8 ∷
   re 50 5 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q6 ∷
   rw 50 q7 ∷
   rw 48 q8 ∷
   re 49 5 (CS03 ∷ []) ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q6 ∷
   rw 49 q7 ∷
   rw 47 q8 ∷
   re 48 5 (CS03 ∷ []) ∷
   re 46 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q6 ∷
   rw 48 q7 ∷
   rw 46 q8 ∷
   re 47 5 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q6 ∷
   rw 47 q7 ∷
   rw 45 q8 ∷
   re 46 5 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q6 ∷
   rw 46 q7 ∷
   rw 44 q8 ∷
   re 45 5 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q6 ∷
   rw 45 q7 ∷
   rw 43 q8 ∷
   re 44 5 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q6 ∷
   rw 44 q7 ∷
   rw 42 q8 ∷
   re 43 5 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q6 ∷
   rw 43 q7 ∷
   rw 41 q8 ∷
   re 42 5 (CS03 ∷ []) ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q6 ∷
   rw 42 q7 ∷
   rw 40 q8 ∷
   re 41 5 (CS03 ∷ []) ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q6 ∷
   rw 41 q7 ∷
   rw 39 q8 ∷
   re 40 5 (CS03 ∷ []) ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q6 ∷
   rw 40 q7 ∷
   rw 38 q8 ∷
   re 39 5 (CS03 ∷ []) ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q6 ∷
   rw 39 q7 ∷
   rw 37 q8 ∷
   re 38 5 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q6 ∷
   rw 38 q7 ∷
   rw 36 q8 ∷
   re 37 5 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q6 ∷
   rw 37 q7 ∷
   rw 35 q8 ∷
   re 36 5 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q6 ∷
   rw 36 q7 ∷
   rw 34 q8 ∷
   re 35 5 (CS03 ∷ []) ∷
   rw 33 q5 ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q6 ∷
   rw 34 q7 ∷
   rw 32 q8 ∷
   re 33 5 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q6 ∷
   rw 33 q7 ∷
   rw 31 q8 ∷
   re 32 5 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q6 ∷
   rw 32 q7 ∷
   rw 30 q8 ∷
   re 31 5 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q6 ∷
   rw 31 q7 ∷
   rw 29 q8 ∷
   re 30 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q6 ∷
   rw 30 q7 ∷
   rw 28 q8 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q6 ∷
   rw 29 q7 ∷
   rw 27 q8 ∷
   re 28 5 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q6 ∷
   rw 28 q9 ∷
   rw 26 q8 ∷
   re 27 5 (CK30 ∷ []) ∷
   rw⁻ 25 q10 ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q6 ∷
   rw 26 q7 ∷
   rw 24 q8 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   rw 25 q7 ∷
   rw 23 q8 ∷
   re 24 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q6 ∷
   rw 24 q7 ∷
   rw 22 q8 ∷
   re 23 5 (CS03 ∷ []) ∷
   rw 21 q1 ∷
   re 22 3 (CK20 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q6 ∷
   rw 22 q7 ∷
   rw 20 q8 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q6 ∷
   rw 21 q9 ∷
   rw 19 q8 ∷
   re 20 5 (CK30 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   rw 20 q7 ∷
   rw 18 q8 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q6 ∷
   rw 19 q7 ∷
   rw 17 q8 ∷
   re 18 5 (CS03 ∷ []) ∷
   rw 16 q5 ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q6 ∷
   rw 17 q7 ∷
   rw 15 q8 ∷
   re 16 5 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q6 ∷
   rw 16 q7 ∷
   rw 14 q8 ∷
   re 15 5 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q6 ∷
   rw 15 q7 ∷
   rw 13 q8 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q6 ∷
   rw 14 q7 ∷
   rw 12 q8 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   rw 13 q7 ∷
   rw 11 q8 ∷
   re 12 5 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q6 ∷
   rw 12 q7 ∷
   rw 10 q8 ∷
   re 11 5 (CS03 ∷ []) ∷
   rw⁻ 9 q10 ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   rw 10 q9 ∷
   rw 8 q8 ∷
   re 9 5 (CK30 ∷ []) ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 9 q7 ∷
   rw 7 q8 ∷
   re 8 5 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 8 q7 ∷
   rw 6 q8 ∷
   re 7 5 (CS03 ∷ []) ∷
   re 5 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 7 q7 ∷
   rw 5 q8 ∷
   re 6 5 (CS03 ∷ []) ∷
   rw 4 q5 ∷
   re 3 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 5 q3 ∷
   re 2 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 4 q3 ∷
   re 1 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 3 q3 ∷
   re 0 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 2 q3 ∷
   rw 81 q11 ∷
   rw 80 q11 ∷
   re 81 3 (CK30 ∷ []) ∷
   rw 79 q12 ∷
   rw 78 q7 ∷
   rw 77 q7 ∷
   rw 76 q7 ∷
   rw 75 q7 ∷
   rw 74 q7 ∷
   rw 73 q7 ∷
   rw 72 q9 ∷
   rw 71 q13 ∷
   rw 70 q7 ∷
   rw 69 q7 ∷
   rw 68 q7 ∷
   re 67 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 69 q14 ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 68 q14 ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q14 ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 66 q14 ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 65 q14 ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 64 q14 ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 63 q14 ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 62 q14 ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 61 q14 ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q14 ∷
   re 57 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 59 q14 ∷
   rw 56 q15 ∷
   rw 55 q15 ∷
   rw 54 q15 ∷
   rw 53 q15 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 54 q14 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q14 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q14 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q14 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q14 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q14 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q14 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q14 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q14 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q14 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q14 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q14 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q14 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q14 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q14 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q14 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q14 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q14 ∷
   re 34 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 36 q14 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q14 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q14 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q14 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q14 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q14 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q14 ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 29 q14 ∷
   rw 26 q15 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q14 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q14 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q14 ∷
   rw 22 q11 ∷
   re 23 3 (CK30 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q14 ∷
   re 20 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 22 q14 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q14 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q14 ∷
   re 17 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 19 q14 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q14 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q14 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q14 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q14 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q14 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q14 ∷
   rw 10 q15 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 11 q14 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q14 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q14 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q14 ∷
   re 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 7 q14 ∷
   rw 4 q7 ∷
   rw 3 q9 ∷
   rw 2 q7 ∷
   rw 1 q7 ∷
   rw 2 q16 ∷
   rw⁻ 1 q7 ∷
   rw⁻ 2 q7 ∷
   rw⁻ 3 q9 ∷
   rw⁻ 4 q7 ∷
   rw⁻ 5 q9 ∷
   rw⁻ 6 q9 ∷
   rw 9 q11 ∷
   re 7 3 (CX13 ∷ []) ∷
   rw 10 q11 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q17 ∷
   rw 12 q11 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q17 ∷
   rw 14 q11 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 15 q11 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 16 q11 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 17 q11 ∷
   re 15 3 (CK30 ∷ []) ∷
   rw 16 q17 ∷
   rw 19 q11 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 20 q11 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 21 q11 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 22 q11 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 23 q11 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 24 q11 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 25 q11 ∷
   re 23 3 (CX13 ∷ []) ∷
   rw 26 q11 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 27 q11 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 28 q11 ∷
   re 26 3 (CK30 ∷ []) ∷
   rw 29 q11 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 30 q11 ∷
   re 28 3 (CK30 ∷ []) ∷
   rw 31 q11 ∷
   re 29 3 (CK30 ∷ []) ∷
   re 31 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 30 q18 ∷
   rw 31 q19 ∷
   rw 34 q11 ∷
   re 32 3 (CX13 ∷ []) ∷
   rw 33 q20 ∷
   rw 36 q11 ∷
   re 34 3 (CX13 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q14 ∷
   rw 36 q18 ∷
   rw⁻ 37 q21 ∷
   rw 30 q22 ∷
   re 30 8 (Toff213 ∷ []) ∷
   rw⁻ 31 q7 ∷
   rw⁻ 32 q7 ∷
   rw⁻ 33 q7 ∷
   rw⁻ 34 q9 ∷
   rw⁻ 35 q7 ∷
   rw⁻ 36 q7 ∷
   re 38 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 37 q14 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q14 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q14 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q14 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q14 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q14 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q14 ∷
   re 45 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 44 q14 ∷
   rw 45 q23 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q14 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q14 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q14 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q14 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q14 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q14 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q14 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q14 ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 54 q14 ∷
   re 56 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 55 q14 ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q14 ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q14 ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 58 q14 ∷
   re 60 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 59 q14 ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q14 ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 61 q14 ∷
   re 63 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 62 q18 ∷
   rw 63 q19 ∷
   rw 66 q11 ∷
   re 64 3 (CX13 ∷ []) ∷
   rw 65 q20 ∷
   rw 68 q11 ∷
   re 66 3 (CX13 ∷ []) ∷
   re 68 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 67 q14 ∷
   rw 68 q18 ∷
   rw⁻ 69 q21 ∷
   rw 62 q22 ∷
   re 62 8 (Toff213 ∷ []) ∷
   rw⁻ 63 q7 ∷
   rw⁻ 64 q7 ∷
   rw⁻ 65 q9 ∷
   rw⁻ 66 q7 ∷
   rw⁻ 67 q9 ∷
   rw⁻ 68 q9 ∷
   re 70 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 69 q14 ∷
   re 71 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 70 q14 ∷
   rw 71 q23 ∷
   re 73 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 72 q14 ∷
   rw 73 q23 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q14 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q14 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q14 ∷
   re 78 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 77 q14 ∷
   rw 78 q23 ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q14 ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 80 q14 ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 81 q14 ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 82 q14 ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 83 q14 ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 84 q14 ∷
   re 86 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 85 q14 ∷
   re 87 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 86 q14 ∷
   re 88 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 87 q14 ∷
   re 89 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 88 q14 ∷
   re 90 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 89 q14 ∷
   re 91 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 90 q14 ∷
   re 92 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 91 q14 ∷
   rw 92 q14 ∷
   rw 2 q1 ∷
   re 0 3 (CS02 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS02 ∷ []) ∷
   rw 4 q1 ∷
   re 2 3 (CK20 ∷ []) ∷
   rw 5 q1 ∷
   re 3 3 (CS02 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CK20 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CK20 ∷ []) ∷
   rw 6 q24 ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw⁻ 9 q9 ∷
   rw 10 q8 ∷
   re 7 5 (CK30 ∷ []) ∷
   rw 8 q10 ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw⁻ 11 q9 ∷
   rw 12 q8 ∷
   re 9 5 (CK30 ∷ []) ∷
   rw 10 q10 ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   rw⁻ 13 q7 ∷
   rw 14 q8 ∷
   re 11 5 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw⁻ 14 q7 ∷
   rw 15 q8 ∷
   re 12 5 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q6 ∷
   rw⁻ 15 q7 ∷
   rw 16 q8 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   rw⁻ 16 q9 ∷
   rw 17 q8 ∷
   re 14 5 (CK30 ∷ []) ∷
   rw 15 q10 ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q6 ∷
   rw⁻ 18 q7 ∷
   rw 19 q8 ∷
   re 16 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q6 ∷
   rw⁻ 19 q7 ∷
   rw 20 q8 ∷
   re 17 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q6 ∷
   rw⁻ 20 q7 ∷
   rw 21 q8 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q6 ∷
   rw⁻ 21 q7 ∷
   rw 22 q8 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q6 ∷
   rw⁻ 22 q7 ∷
   rw 23 q8 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   rw⁻ 23 q7 ∷
   rw 24 q8 ∷
   re 21 5 (CS03 ∷ []) ∷
   rw 22 q24 ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q6 ∷
   rw⁻ 25 q7 ∷
   rw 26 q8 ∷
   re 23 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   rw⁻ 26 q7 ∷
   rw 27 q8 ∷
   re 24 5 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q6 ∷
   rw⁻ 27 q9 ∷
   rw 28 q8 ∷
   re 25 5 (CK30 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   rw⁻ 28 q7 ∷
   rw 29 q8 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q6 ∷
   rw⁻ 29 q9 ∷
   rw 30 q8 ∷
   re 27 5 (CK30 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q6 ∷
   rw⁻ 30 q9 ∷
   rw 31 q8 ∷
   re 28 5 (CK30 ∷ []) ∷
   re 30 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 29 q25 ∷
   rw 30 q26 ∷
   rw 31 q27 ∷
   rw 32 q28 ∷
   rw 33 q27 ∷
   rw 34 q29 ∷
   rw 35 q25 ∷
   rw 36 q30 ∷
   rw 29 q31 ∷
   re 29 8 (Toff123 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CS02 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CS02 ∷ []) ∷
   rw 34 q1 ∷
   re 32 3 (CS02 ∷ []) ∷
   rw 35 q1 ∷
   re 33 3 (CK20 ∷ []) ∷
   rw 36 q1 ∷
   re 34 3 (CS02 ∷ []) ∷
   rw 37 q1 ∷
   re 35 3 (CS02 ∷ []) ∷
   rw 36 q27 ∷
   re 38 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 37 q3 ∷
   re 39 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 38 q3 ∷
   re 40 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 39 q3 ∷
   re 41 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 40 q3 ∷
   re 42 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 41 q3 ∷
   re 43 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 42 q3 ∷
   re 44 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 43 q3 ∷
   rw 44 q32 ∷
   re 46 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 45 q3 ∷
   re 47 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 46 q3 ∷
   re 48 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 47 q3 ∷
   re 49 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 48 q3 ∷
   re 50 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 49 q3 ∷
   re 51 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 50 q3 ∷
   re 52 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 51 q3 ∷
   re 53 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 52 q3 ∷
   re 54 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 53 q3 ∷
   rw 54 q27 ∷
   re 56 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 55 q3 ∷
   re 57 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 56 q3 ∷
   re 58 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 57 q3 ∷
   re 59 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 58 q3 ∷
   re 60 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 59 q3 ∷
   re 61 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 60 q3 ∷
   re 62 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 61 q25 ∷
   rw 62 q26 ∷
   rw 63 q27 ∷
   rw 64 q28 ∷
   rw 65 q27 ∷
   rw 66 q29 ∷
   rw 67 q25 ∷
   rw 68 q30 ∷
   rw 61 q31 ∷
   re 61 8 (Toff123 ∷ []) ∷
   rw 64 q1 ∷
   re 62 3 (CS02 ∷ []) ∷
   rw 65 q1 ∷
   re 63 3 (CS02 ∷ []) ∷
   rw 66 q1 ∷
   re 64 3 (CK20 ∷ []) ∷
   rw 67 q1 ∷
   re 65 3 (CS02 ∷ []) ∷
   rw 68 q1 ∷
   re 66 3 (CK20 ∷ []) ∷
   rw 69 q1 ∷
   re 67 3 (CK20 ∷ []) ∷
   rw 68 q27 ∷
   re 70 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 69 q3 ∷
   rw 70 q32 ∷
   re 72 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 71 q3 ∷
   rw 72 q32 ∷
   re 74 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 73 q3 ∷
   re 75 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 74 q3 ∷
   re 76 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 75 q3 ∷
   re 77 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 76 q3 ∷
   rw 77 q32 ∷
   re 79 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 78 q3 ∷
   re 80 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 79 q3 ∷
   re 81 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 80 q3 ∷
   re 82 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 81 q3 ∷
   re 83 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 82 q3 ∷
   re 84 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 83 q3 ∷
   rw 84 q27 ∷
   re 86 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 85 q3 ∷
   re 87 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 86 q3 ∷
   re 88 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 87 q3 ∷
   re 89 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 88 q3 ∷
   re 90 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 89 q3 ∷
   re 91 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 90 q3 ∷
   rw 91 q3 ∷ []) Eq.refl

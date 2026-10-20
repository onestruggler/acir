{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D464 (W : Ws) where

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
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = eqn (CK21 ∷ Sw01 ∷ []) (Sw01 ∷ CK20 ∷ []) (wn 273 W)
  q4 : Eqn
  q4 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q5 : Eqn
  q5 = eqn (CS01 ∷ Sw01 ∷ []) (Sw01 ∷ CS01 ∷ []) (wn 216 W)
  q6 : Eqn
  q6 = eqn (CK01 ∷ Sw01 ∷ []) (Sw01 ∷ CK10 ∷ []) (wn 480 W)
  q7 : Eqn
  q7 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wn 481 W)
  q8 : Eqn
  q8 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q9 : Eqn
  q9 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q11 : Eqn
  q11 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))
  q12 : Eqn
  q12 = eqn (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) (wn 219 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CK10 ∷ []) (CK01 ∷ Sw01 ∷ []) (wn 327 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ CK20 ∷ []) (CK21 ∷ Sw01 ∷ []) (wn 275 W)
  q16 : Eqn
  q16 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ K3 ∷ []) (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑)))
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q19 : Eqn
  q19 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q20 : Eqn
  q20 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q21 : Eqn
  q21 = eqn (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) (wn 122 W)
  q22 : Eqn
  q22 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q23 : Eqn
  q23 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q24 : Eqn
  q24 = eqn (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (wn 337 W)
  q25 : Eqn
  q25 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)

-- AXIOM LF @1023: 414 steps
lem-AXIOM-LF-at1023 : ⟪ (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK31 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ Toff302 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ Toff302 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX03 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) ⟫ʷ
lem-AXIOM-LF-at1023 = derive (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK31 ∷ []) (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ Toff302 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ Toff302 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX03 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ [])
  (rw 80 q1 ∷
   re 79 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw⁻ 81 q2 ∷
   rw 80 q3 ∷
   rw⁻ 79 q2 ∷
   re 80 3 (CK30 ∷ []) ∷
   rw⁻ 78 q4 ∷
   rw 77 q5 ∷
   rw 76 q5 ∷
   rw 75 q5 ∷
   rw 74 q5 ∷
   rw 73 q5 ∷
   rw 72 q5 ∷
   rw 71 q6 ∷
   rw 70 q7 ∷
   rw 69 q5 ∷
   rw 68 q5 ∷
   rw 67 q5 ∷
   rw 66 q8 ∷
   rw 65 q9 ∷
   rw 64 q9 ∷
   rw 63 q9 ∷
   rw 62 q9 ∷
   rw 61 q9 ∷
   rw 60 q9 ∷
   rw 59 q9 ∷
   rw 58 q9 ∷
   rw 57 q9 ∷
   rw 56 q3 ∷
   rw⁻ 55 q10 ∷
   rw⁻ 54 q10 ∷
   rw⁻ 53 q10 ∷
   rw⁻ 52 q10 ∷
   rw 51 q9 ∷
   rw 50 q9 ∷
   rw 49 q9 ∷
   rw 48 q9 ∷
   rw 47 q9 ∷
   rw 46 q9 ∷
   rw 45 q9 ∷
   rw 44 q9 ∷
   rw 43 q9 ∷
   rw 42 q9 ∷
   rw 41 q9 ∷
   rw 40 q9 ∷
   rw 39 q9 ∷
   rw 38 q9 ∷
   rw 37 q9 ∷
   rw 36 q9 ∷
   rw 35 q9 ∷
   rw 34 q9 ∷
   rw 33 q8 ∷
   rw 32 q9 ∷
   rw 31 q9 ∷
   rw 30 q9 ∷
   rw 29 q9 ∷
   rw 28 q9 ∷
   rw 27 q9 ∷
   rw 26 q3 ∷
   rw⁻ 25 q10 ∷
   rw 24 q9 ∷
   rw 23 q9 ∷
   rw 22 q9 ∷
   re 21 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q2 ∷
   rw 22 q3 ∷
   rw⁻ 21 q2 ∷
   re 22 3 (CK30 ∷ []) ∷
   rw 20 q9 ∷
   rw 19 q3 ∷
   rw 18 q9 ∷
   rw 17 q9 ∷
   rw 16 q8 ∷
   rw 15 q9 ∷
   rw 14 q9 ∷
   rw 13 q9 ∷
   rw 12 q9 ∷
   rw 11 q9 ∷
   rw 10 q9 ∷
   rw⁻ 9 q10 ∷
   rw 8 q3 ∷
   rw 7 q9 ∷
   rw 6 q9 ∷
   rw 5 q9 ∷
   rw 4 q8 ∷
   rw 3 q5 ∷
   rw 2 q6 ∷
   rw 1 q5 ∷
   rw 0 q5 ∷
   rw 1 q11 ∷
   rw 0 q12 ∷
   rw 1 q12 ∷
   rw 2 q13 ∷
   rw 3 q12 ∷
   rw 4 q13 ∷
   rw 5 q13 ∷
   rw 6 q14 ∷
   rw 7 q15 ∷
   rw 8 q10 ∷
   rw 9 q15 ∷
   rw 10 q10 ∷
   rw 11 q16 ∷
   rw 12 q16 ∷
   rw 13 q16 ∷
   rw 14 q15 ∷
   rw 15 q10 ∷
   rw 16 q16 ∷
   rw 17 q16 ∷
   rw 18 q16 ∷
   rw 19 q16 ∷
   rw 20 q16 ∷
   rw 21 q16 ∷
   rw 22 q14 ∷
   rw 23 q16 ∷
   rw 24 q16 ∷
   rw 25 q15 ∷
   rw 26 q16 ∷
   rw 27 q15 ∷
   rw 28 q15 ∷
   re 30 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 29 q17 ∷
   rw 30 q18 ∷
   rw 31 q14 ∷
   rw 32 q19 ∷
   rw 33 q14 ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   rw 35 q20 ∷
   rw 36 q2 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 35 q17 ∷
   rw 36 q21 ∷
   rw 29 q1 ∷
   rw 30 q17 ∷
   rw 31 q18 ∷
   rw 32 q22 ∷
   rw 33 q19 ∷
   rw 34 q22 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   rw 36 q16 ∷
   rw 37 q2 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw 36 q17 ∷
   rw 37 q23 ∷
   rw 30 q24 ∷
   re 30 8 (Toff312 ∷ []) ∷
   re 29 3 (Toff302 ∷ []) ∷
   rw 30 q12 ∷
   rw 31 q12 ∷
   rw 32 q12 ∷
   rw 33 q13 ∷
   rw 34 q12 ∷
   rw 35 q12 ∷
   re 37 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   rw 37 q14 ∷
   rw 38 q2 ∷
   re 36 3 (CX03 ∷ []) ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q2 ∷
   rw 38 q16 ∷
   rw 39 q2 ∷
   re 37 3 (CS13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q2 ∷
   rw 39 q16 ∷
   rw 40 q2 ∷
   re 38 3 (CS13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q2 ∷
   rw 40 q16 ∷
   rw 41 q2 ∷
   re 39 3 (CS13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q2 ∷
   rw 41 q16 ∷
   rw 42 q2 ∷
   re 40 3 (CS13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q2 ∷
   rw 42 q16 ∷
   rw 43 q2 ∷
   re 41 3 (CS13 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q2 ∷
   rw 43 q16 ∷
   rw 44 q2 ∷
   re 42 3 (CS13 ∷ []) ∷
   re 44 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 43 q2 ∷
   rw 44 q15 ∷
   rw 45 q2 ∷
   re 43 3 (CK31 ∷ []) ∷
   rw 44 q4 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q2 ∷
   rw 46 q16 ∷
   rw 47 q2 ∷
   re 45 3 (CS13 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q2 ∷
   rw 47 q16 ∷
   rw 48 q2 ∷
   re 46 3 (CS13 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q2 ∷
   rw 48 q16 ∷
   rw 49 q2 ∷
   re 47 3 (CS13 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q2 ∷
   rw 49 q16 ∷
   rw 50 q2 ∷
   re 48 3 (CS13 ∷ []) ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q2 ∷
   rw 50 q16 ∷
   rw 51 q2 ∷
   re 49 3 (CS13 ∷ []) ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q2 ∷
   rw 51 q16 ∷
   rw 52 q2 ∷
   re 50 3 (CS13 ∷ []) ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q2 ∷
   rw 52 q16 ∷
   rw 53 q2 ∷
   re 51 3 (CS13 ∷ []) ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q2 ∷
   rw 53 q16 ∷
   rw 54 q2 ∷
   re 52 3 (CS13 ∷ []) ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q2 ∷
   rw 54 q16 ∷
   rw 55 q2 ∷
   re 53 3 (CS13 ∷ []) ∷
   re 55 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 54 q2 ∷
   rw 55 q14 ∷
   rw 56 q2 ∷
   re 54 3 (CX03 ∷ []) ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 55 q2 ∷
   rw 56 q16 ∷
   rw 57 q2 ∷
   re 55 3 (CS13 ∷ []) ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q2 ∷
   rw 57 q16 ∷
   rw 58 q2 ∷
   re 56 3 (CS13 ∷ []) ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q2 ∷
   rw 58 q16 ∷
   rw 59 q2 ∷
   re 57 3 (CS13 ∷ []) ∷
   re 59 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 58 q2 ∷
   rw 59 q15 ∷
   rw 60 q2 ∷
   re 58 3 (CK31 ∷ []) ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q2 ∷
   rw 60 q16 ∷
   rw 61 q2 ∷
   re 59 3 (CS13 ∷ []) ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q2 ∷
   rw 61 q16 ∷
   rw 62 q2 ∷
   re 60 3 (CS13 ∷ []) ∷
   re 62 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 61 q17 ∷
   rw 62 q18 ∷
   rw 63 q14 ∷
   rw 64 q19 ∷
   rw 65 q14 ∷
   re 67 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 66 q2 ∷
   rw 67 q20 ∷
   rw 68 q2 ∷
   re 66 3 (CS03 ∷ []) ∷
   rw 67 q17 ∷
   rw 68 q21 ∷
   rw 61 q1 ∷
   rw 62 q17 ∷
   rw 63 q18 ∷
   rw 64 q22 ∷
   rw 65 q19 ∷
   rw 66 q22 ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q2 ∷
   rw 68 q16 ∷
   rw 69 q2 ∷
   re 67 3 (CS13 ∷ []) ∷
   rw 68 q17 ∷
   rw 69 q23 ∷
   rw 62 q24 ∷
   re 62 8 (Toff312 ∷ []) ∷
   re 61 3 (Toff302 ∷ []) ∷
   rw 62 q12 ∷
   rw 63 q12 ∷
   rw 64 q13 ∷
   rw 65 q12 ∷
   rw 66 q13 ∷
   rw 67 q13 ∷
   re 69 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 68 q2 ∷
   rw 69 q14 ∷
   rw 70 q2 ∷
   re 68 3 (CX03 ∷ []) ∷
   re 70 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 69 q2 ∷
   rw 70 q15 ∷
   rw 71 q2 ∷
   re 69 3 (CK31 ∷ []) ∷
   rw 70 q4 ∷
   re 72 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 71 q2 ∷
   rw 72 q15 ∷
   rw 73 q2 ∷
   re 71 3 (CK31 ∷ []) ∷
   rw 72 q4 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 73 q2 ∷
   rw 74 q16 ∷
   rw 75 q2 ∷
   re 73 3 (CS13 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q2 ∷
   rw 75 q16 ∷
   rw 76 q2 ∷
   re 74 3 (CS13 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q2 ∷
   rw 76 q16 ∷
   rw 77 q2 ∷
   re 75 3 (CS13 ∷ []) ∷
   re 77 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 76 q2 ∷
   rw 77 q15 ∷
   rw 78 q2 ∷
   re 76 3 (CK31 ∷ []) ∷
   rw 77 q4 ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q2 ∷
   rw 79 q16 ∷
   rw 80 q2 ∷
   re 78 3 (CS13 ∷ []) ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q2 ∷
   rw 80 q16 ∷
   rw 81 q2 ∷
   re 79 3 (CS13 ∷ []) ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 80 q2 ∷
   rw 81 q16 ∷
   rw 82 q2 ∷
   re 80 3 (CS13 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 81 q2 ∷
   rw 82 q16 ∷
   rw 83 q2 ∷
   re 81 3 (CS13 ∷ []) ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 82 q2 ∷
   rw 83 q16 ∷
   rw 84 q2 ∷
   re 82 3 (CS13 ∷ []) ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 83 q2 ∷
   rw 84 q16 ∷
   rw 85 q2 ∷
   re 83 3 (CS13 ∷ []) ∷
   re 85 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 84 q2 ∷
   rw 85 q14 ∷
   rw 86 q2 ∷
   re 84 3 (CX03 ∷ []) ∷
   re 86 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 85 q2 ∷
   rw 86 q16 ∷
   rw 87 q2 ∷
   re 85 3 (CS13 ∷ []) ∷
   re 87 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 86 q2 ∷
   rw 87 q16 ∷
   rw 88 q2 ∷
   re 86 3 (CS13 ∷ []) ∷
   re 88 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 87 q2 ∷
   rw 88 q15 ∷
   rw 89 q2 ∷
   re 87 3 (CK31 ∷ []) ∷
   re 89 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 88 q2 ∷
   rw 89 q16 ∷
   rw 90 q2 ∷
   re 88 3 (CS13 ∷ []) ∷
   re 90 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 89 q2 ∷
   rw 90 q15 ∷
   rw 91 q2 ∷
   re 89 3 (CK31 ∷ []) ∷
   re 91 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 90 q2 ∷
   rw 91 q15 ∷
   rw 92 q2 ∷
   re 90 3 (CK31 ∷ []) ∷
   rw 91 q25 ∷ []) Eq.refl

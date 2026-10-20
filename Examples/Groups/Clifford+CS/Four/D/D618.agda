{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D618 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D593 W using (lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-TOFF302-X0 ; lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-vs-X0-TOFF301-X0)
open import Examples.Groups.Clifford+CS.Four.D.D594 W using (lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-TOFF301-X0 ; lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-TOFF301-X0)

private
  q1 : Eqn
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ K3 ∷ []) (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑)))
  q3 : Eqn
  q3 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q4 : Eqn
  q4 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q8 : Eqn
  q8 = eqn (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) (wn 122 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q10 : Eqn
  q10 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q11 : Eqn
  q11 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q12 : Eqn
  q12 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q13 : Eqn
  q13 = eqn (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (wn 337 W)
  q14 : Eqn
  q14 = eqn (Toff312 ∷ []) (X1 ∷ X1 ∷ Toff312 ∷ X1 ∷ X1 ∷ []) (wn 1800 W)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) (wn 317 W)
  q16 : Eqn
  q16 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q18 : Eqn
  q18 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q19 : Eqn
  q19 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q20 : Eqn
  q20 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q21 : Eqn
  q21 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q22 : Eqn
  q22 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q23 : Eqn
  q23 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q24 : Eqn
  q24 = eqn (CK01 ∷ Sw23 ∷ []) (Sw23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (Swap))
  q25 : Eqn
  q25 = eqn (X0 ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X0 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X0 ∷ []) (wn 1853 W)
  q26 : Eqn
  q26 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)
  q27 : Eqn
  q27 = eqn (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (X0 ∷ Toff302 ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-TOFF302-X0
  q28 : Eqn
  q28 = eqn (X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) (X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X0 ∷ X0 ∷ []) (wn 1854 W)
  q29 : Eqn
  q29 = eqn (X0 ∷ Sw01 ∷ []) (Sw01 ∷ X1 ∷ []) (wn 1106 W)
  q30 : Eqn
  q30 = eqn (X1 ∷ X1 ∷ Toff312 ∷ X1 ∷ X1 ∷ []) (Toff312 ∷ []) (wn 1803 W)

-- pass [TOFF302] [X0 CS01 CS01 CS01 CK01 CS01 CS01 CX03 CS13 CS13 CS13 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CS13 CK31 CS13 CS13 X0]: 365 steps
lem-pass-TOFF302-vs-X0-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-X0 : ⟪ (Toff302 ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ Toff302 ∷ []) ⟫ʷ
lem-pass-TOFF302-vs-X0-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-X0 = derive (Toff302 ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ []) (X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ Toff302 ∷ [])
  (rw 1 q1 ∷
   re 0 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) ∷
   re 1 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q2 ∷
   rw 7 q8 ∷
   rw 8 q9 ∷
   rw 7 q10 ∷
   rw⁻ 6 q2 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q6 ∷
   rw 6 q11 ∷
   rw⁻ 5 q6 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 4 q12 ∷
   rw⁻ 3 q5 ∷
   rw 2 q12 ∷
   rw⁻ 1 q3 ∷
   rw⁻ 0 q2 ∷
   rw 1 q13 ∷
   re 1 8 (Toff312 ∷ []) ∷
   rw 1 q14 ∷
   rw 0 q15 ∷
   rw 1 q15 ∷
   re 3 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 2 q2 ∷
   rw 3 q3 ∷
   rw 4 q4 ∷
   rw 5 q5 ∷
   rw 6 q4 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 8 q7 ∷
   rw 9 q6 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q2 ∷
   rw 9 q8 ∷
   rw 2 q1 ∷
   rw 3 q2 ∷
   rw 4 q3 ∷
   rw 5 q16 ∷
   rw 6 q5 ∷
   rw 7 q16 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 9 q17 ∷
   rw 10 q6 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 9 q2 ∷
   rw 10 q18 ∷
   rw 3 q13 ∷
   re 3 8 (Toff312 ∷ []) ∷
   re 2 3 (Toff302 ∷ []) ∷
   rw 3 q15 ∷
   rw 4 q15 ∷
   rw 5 q9 ∷
   rw 38 q19 ∷
   rw 37 q20 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q21 ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q21 ∷
   re 34 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 36 q21 ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q21 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q21 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q21 ∷
   re 30 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 32 q21 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q21 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q21 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q21 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q21 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q21 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q21 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q21 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q21 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q21 ∷
   rw 20 q22 ∷
   re 19 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 21 q21 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q21 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q21 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q21 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q21 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q21 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q21 ∷
   re 12 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 14 q21 ∷
   rw 11 q23 ∷
   rw 10 q23 ∷
   rw 9 q24 ∷
   rw 8 q23 ∷
   rw 7 q23 ∷
   rw 6 q23 ∷
   rw 5 q20 ∷
   rw 4 q20 ∷
   rw 5 q25 ∷
   rw⁻ 4 q23 ∷
   rw⁻ 5 q23 ∷
   rw⁻ 6 q23 ∷
   rw⁻ 7 q24 ∷
   rw⁻ 8 q23 ∷
   rw⁻ 9 q23 ∷
   rw 12 q19 ∷
   re 10 3 (CX03 ∷ []) ∷
   rw 13 q19 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 14 q19 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 15 q19 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 16 q19 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 17 q19 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw 18 q19 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw 19 q19 ∷
   re 17 3 (CK31 ∷ []) ∷
   rw 18 q26 ∷
   rw 21 q19 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 22 q19 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 23 q19 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 24 q19 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 25 q19 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 26 q19 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 27 q19 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 28 q19 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 29 q19 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 30 q19 ∷
   re 28 3 (CX03 ∷ []) ∷
   rw 31 q19 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 32 q19 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw 33 q19 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 34 q19 ∷
   re 32 3 (CK31 ∷ []) ∷
   rw 35 q19 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw 36 q19 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw⁻ 35 q20 ∷
   rw 36 q21 ∷
   rw⁻ 1 q27 ∷
   rw 32 q19 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q21 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q21 ∷
   re 29 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 31 q21 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q21 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q21 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q21 ∷
   re 25 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 27 q21 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q21 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q21 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q21 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q21 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q21 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q21 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q21 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q21 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q21 ∷
   rw 15 q22 ∷
   re 14 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 16 q21 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q21 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q21 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q21 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q21 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q21 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q21 ∷
   re 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 9 q21 ∷
   rw 6 q23 ∷
   rw 5 q23 ∷
   rw 4 q24 ∷
   rw 3 q23 ∷
   rw 2 q23 ∷
   rw 1 q23 ∷
   rw 0 q20 ∷
   rw 1 q28 ∷
   rw⁻ 0 q20 ∷
   rw⁻ 1 q23 ∷
   rw⁻ 2 q23 ∷
   rw⁻ 3 q23 ∷
   rw⁻ 4 q24 ∷
   rw⁻ 5 q23 ∷
   rw⁻ 6 q23 ∷
   rw 9 q19 ∷
   re 7 3 (CX03 ∷ []) ∷
   rw 10 q19 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 11 q19 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 12 q19 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 13 q19 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 14 q19 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 15 q19 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 16 q19 ∷
   re 14 3 (CK31 ∷ []) ∷
   rw 15 q26 ∷
   rw 18 q19 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw 19 q19 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 20 q19 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 21 q19 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 22 q19 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 23 q19 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 24 q19 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 25 q19 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 26 q19 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 27 q19 ∷
   re 25 3 (CX03 ∷ []) ∷
   rw 28 q19 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 29 q19 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 30 q19 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 31 q19 ∷
   re 29 3 (CK31 ∷ []) ∷
   rw 32 q19 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw 33 q19 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw⁻ 32 q20 ∷
   rw⁻ 33 q20 ∷
   rw 34 q21 ∷
   rw 38 q1 ∷
   rw 37 q29 ∷
   rw 36 q29 ∷
   re 35 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) ∷
   re 36 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 35 q2 ∷
   rw 36 q3 ∷
   rw 37 q4 ∷
   rw 38 q5 ∷
   rw 39 q4 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q6 ∷
   rw 41 q7 ∷
   rw 42 q6 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q2 ∷
   rw 42 q8 ∷
   rw 43 q9 ∷
   rw 42 q10 ∷
   rw⁻ 41 q2 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q6 ∷
   rw 41 q11 ∷
   rw⁻ 40 q6 ∷
   re 41 3 (CS13 ∷ []) ∷
   rw 39 q12 ∷
   rw⁻ 38 q5 ∷
   rw 37 q12 ∷
   rw⁻ 36 q3 ∷
   rw⁻ 35 q2 ∷
   rw 36 q13 ∷
   re 36 8 (Toff312 ∷ []) ∷
   rw 34 q29 ∷
   rw 33 q29 ∷
   rw 34 q30 ∷
   re 34 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 33 q2 ∷
   rw 34 q3 ∷
   rw 35 q4 ∷
   rw 36 q5 ∷
   rw 37 q4 ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q6 ∷
   rw 39 q7 ∷
   rw 40 q6 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 39 q2 ∷
   rw 40 q8 ∷
   rw 33 q1 ∷
   rw 34 q2 ∷
   rw 35 q3 ∷
   rw 36 q16 ∷
   rw 37 q5 ∷
   rw 38 q16 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q6 ∷
   rw 40 q17 ∷
   rw 41 q6 ∷
   re 39 3 (CS13 ∷ []) ∷
   rw 40 q2 ∷
   rw 41 q18 ∷
   rw 34 q13 ∷
   re 34 8 (Toff312 ∷ []) ∷
   re 33 3 (Toff302 ∷ []) ∷
   rw 34 q9 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = eqn (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) (wn 335 W)
  q32 : Eqn
  q32 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q33 : Eqn
  q33 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q34 : Eqn
  q34 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wn 1294 W)
  q35 : Eqn
  q35 = eqn (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (wn 368 W)
  q36 : Eqn
  q36 = eqn (Toff201 ∷ []) (X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ []) (wn 1855 W)
  q37 : Eqn
  q37 = eqn (Sw23 ∷ K3 ∷ []) (K2 ∷ Sw23 ∷ []) (wn 336 W)
  q38 : Eqn
  q38 = eqn (X0 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ []) (wn 1856 W)
  q39 : Eqn
  q39 = eqn (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ Toff301 ∷ X0 ∷ []) (X0 ∷ Toff301 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-vs-X0-TOFF301-X0
  q40 : Eqn
  q40 = eqn (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ X0 ∷ []) (wn 1857 W)
  q41 : Eqn
  q41 = eqn (X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ []) (Toff201 ∷ []) (wn 1858 W)

-- pass [TOFF301] [X0 CS02 CS02 CK02 CS02 CK02 CK02 CX01 CK12 S1 CK12 S1 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CX01 CS12 CS12 CK12 CS12 CK12 CK12 X0]: 125 steps
lem-pass-TOFF301-vs-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0 : ⟪ (Toff301 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ Toff301 ∷ []) ⟫ʷ
lem-pass-TOFF301-vs-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0 = derive (Toff301 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ []) (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ Toff301 ∷ [])
  (rw 1 q19 ∷
   re 0 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 1 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 0 q31 ∷
   rw 3 q19 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q32 ∷
   rw 5 q19 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q32 ∷
   rw 7 q19 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q31 ∷
   rw⁻ 7 q33 ∷
   rw 8 q21 ∷
   rw 7 q33 ∷
   rw 6 q34 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q21 ∷
   rw 4 q32 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q21 ∷
   rw 2 q32 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q21 ∷
   rw 0 q34 ∷
   rw 1 q35 ∷
   re 1 8 (Toff201 ∷ []) ∷
   rw 1 q36 ∷
   rw⁻ 0 q20 ∷
   rw⁻ 1 q20 ∷
   re 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 2 q31 ∷
   rw 5 q19 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q32 ∷
   rw 7 q19 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q32 ∷
   rw 9 q19 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q31 ∷
   rw⁻ 9 q33 ∷
   rw 2 q19 ∷
   rw 3 q37 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q21 ∷
   rw⁻ 5 q32 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q21 ∷
   rw⁻ 7 q32 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   rw 9 q37 ∷
   rw⁻ 10 q33 ∷
   rw 3 q35 ∷
   re 3 8 (Toff201 ∷ []) ∷
   re 2 3 (Toff301 ∷ []) ∷
   rw⁻ 3 q20 ∷
   rw⁻ 4 q20 ∷
   rw 5 q21 ∷
   rw 4 q38 ∷
   rw⁻ 1 q39 ∷
   rw 0 q40 ∷
   rw 36 q19 ∷
   rw 35 q20 ∷
   rw 34 q20 ∷
   re 33 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 34 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 33 q31 ∷
   rw 36 q19 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw⁻ 35 q32 ∷
   rw 38 q19 ∷
   re 36 3 (CS13⁻ ∷ []) ∷
   rw⁻ 37 q32 ∷
   rw 40 q19 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 39 q31 ∷
   rw⁻ 40 q33 ∷
   rw 41 q21 ∷
   rw 40 q33 ∷
   rw 39 q34 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q21 ∷
   rw 37 q32 ∷
   re 36 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 38 q21 ∷
   rw 35 q32 ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q21 ∷
   rw 33 q34 ∷
   rw 34 q35 ∷
   re 34 8 (Toff201 ∷ []) ∷
   rw 32 q20 ∷
   rw 31 q20 ∷
   rw 32 q41 ∷
   re 32 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 31 q31 ∷
   rw 34 q19 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw⁻ 33 q32 ∷
   rw 36 q19 ∷
   re 34 3 (CS13⁻ ∷ []) ∷
   rw⁻ 35 q32 ∷
   rw 38 q19 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q31 ∷
   rw⁻ 38 q33 ∷
   rw 31 q19 ∷
   rw 32 q37 ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q21 ∷
   rw⁻ 34 q32 ∷
   re 36 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 35 q21 ∷
   rw⁻ 36 q32 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q21 ∷
   rw 38 q37 ∷
   rw⁻ 39 q33 ∷
   rw 32 q35 ∷
   re 32 8 (Toff201 ∷ []) ∷
   re 31 3 (Toff301 ∷ []) ∷
   rw 32 q21 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = eqn (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ Toff301 ∷ X0 ∷ []) (X0 ∷ Toff301 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) (lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-TOFF301-X0)

-- Bar(SSKSKK;0,3->2) passes factors of X0 TOFF301 X0: 1 steps
lem-Bar⟨SSKSKK03-⟶2⟩-passes-factors-of-X0-TOFF301-X0 : ⟪ (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ Toff301 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff301 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK03-⟶2⟩-passes-factors-of-X0-TOFF301-X0 = derive (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ Toff301 ∷ X0 ∷ []) (X0 ∷ Toff301 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ [])
  (rw 0 q42 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ Toff301 ∷ X0 ∷ []) (X0 ∷ Toff301 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-TOFF301-X0)

-- Bar(SSSKSS;0,3->2) passes factors of X0 TOFF301 X0: 1 steps
lem-Bar⟨SSSKSS03-⟶2⟩-passes-factors-of-X0-TOFF301-X0 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ Toff301 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff301 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS03-⟶2⟩-passes-factors-of-X0-TOFF301-X0 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ Toff301 ∷ X0 ∷ []) (X0 ∷ Toff301 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  (rw 0 q43 ∷ []) Eq.refl

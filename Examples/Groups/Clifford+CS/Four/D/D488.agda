{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D488 (W : Ws) where

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
  q3 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q4 : Eqn
  q4 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q6 : Eqn
  q6 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q7 : Eqn
  q7 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q8 : Eqn
  q8 = eqn (CK02 ∷ Sw01 ∷ []) (Sw01 ∷ CK12 ∷ []) (wn 772 W)
  q9 : Eqn
  q9 = eqn (CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS13 ∷ []) (CS13 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (wn 1299 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CK12 ∷ []) (CK02 ∷ Sw01 ∷ []) (wn 329 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)

-- pass [CS02 CS02 CS02 CK02 CS02 CS02 CX03 CS23 CS23 CS23 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CS23 CK32 CS23 CS23] [CS03]: 91 steps
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CS03 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CS03 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS03 ∷ []) (CS03 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  (rw 32 q1 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q2 ∷
   rw 32 q3 ∷
   rw⁻ 31 q2 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw⁻ 30 q4 ∷
   rw⁻ 29 q4 ∷
   rw⁻ 28 q5 ∷
   rw⁻ 27 q4 ∷
   rw⁻ 26 q4 ∷
   rw⁻ 25 q4 ∷
   re 24 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q2 ∷
   rw 25 q6 ∷
   rw⁻ 24 q2 ∷
   re 25 3 (CX13 ∷ []) ∷
   rw⁻ 23 q4 ∷
   rw⁻ 22 q4 ∷
   rw⁻ 21 q4 ∷
   rw⁻ 20 q4 ∷
   rw⁻ 19 q4 ∷
   rw⁻ 18 q4 ∷
   rw⁻ 17 q4 ∷
   rw⁻ 16 q4 ∷
   rw⁻ 15 q4 ∷
   rw⁻ 14 q7 ∷
   rw⁻ 13 q5 ∷
   rw⁻ 12 q4 ∷
   rw⁻ 11 q4 ∷
   rw⁻ 10 q4 ∷
   rw⁻ 9 q4 ∷
   rw⁻ 8 q4 ∷
   rw⁻ 7 q4 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw 7 q6 ∷
   rw⁻ 6 q2 ∷
   re 7 3 (CX13 ∷ []) ∷
   rw 5 q3 ∷
   rw 4 q3 ∷
   rw 3 q8 ∷
   rw 2 q3 ∷
   rw 1 q3 ∷
   rw 0 q3 ∷
   rw 1 q9 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q2 ∷
   rw 1 q10 ∷
   rw 2 q2 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q10 ∷
   rw 2 q10 ∷
   rw 3 q10 ∷
   rw 4 q11 ∷
   rw 5 q10 ∷
   rw 6 q10 ∷
   re 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   rw 8 q12 ∷
   rw 9 q2 ∷
   re 7 3 (CX03 ∷ []) ∷
   rw 8 q4 ∷
   rw 9 q4 ∷
   rw 10 q4 ∷
   rw 11 q4 ∷
   rw 12 q4 ∷
   rw 13 q4 ∷
   rw 14 q5 ∷
   rw 15 q7 ∷
   rw 16 q4 ∷
   rw 17 q4 ∷
   rw 18 q4 ∷
   rw 19 q4 ∷
   rw 20 q4 ∷
   rw 21 q4 ∷
   rw 22 q4 ∷
   rw 23 q4 ∷
   rw 24 q4 ∷
   re 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   rw 26 q12 ∷
   rw 27 q2 ∷
   re 25 3 (CX03 ∷ []) ∷
   rw 26 q4 ∷
   rw 27 q4 ∷
   rw 28 q4 ∷
   rw 29 q5 ∷
   rw 30 q4 ∷
   rw 31 q4 ∷
   rw 32 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q15 : Eqn
  q15 = eqn (CS01 ∷ CK32 ∷ []) (CK32 ∷ CS01 ∷ []) (low-comm (CS) (CK₁₀))
  q16 : Eqn
  q16 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q17 : Eqn
  q17 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q18 : Eqn
  q18 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q19 : Eqn
  q19 = eqn (CX02 ∷ CS01 ∷ []) (CS01 ∷ CX02 ∷ []) (wn 1288 W)
  q20 : Eqn
  q20 = eqn (CS01 ∷ S3 ∷ []) (S3 ∷ CS01 ∷ []) (low-comm (CS) ((S ↑)))
  q21 : Eqn
  q21 = eqn (CS02 ∷ CS01 ∷ []) (CS01 ∷ CS02 ∷ []) (wn 245 W)
  q22 : Eqn
  q22 = eqn (CK02 ∷ CS01 ∷ []) (CS01 ∷ CK02 ∷ []) (wn 1289 W)

-- pass [CS02 CS02 CS02 CK02 CS02 CS02 CX03 CS23 CS23 CS23 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CS23 CK32 CS23 CS23] [CS01]: 47 steps
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CS01 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CS01 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS01 ∷ []) (CS01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  (rw⁻ 30 q14 ∷
   rw⁻ 29 q14 ∷
   rw⁻ 28 q15 ∷
   rw⁻ 27 q14 ∷
   rw⁻ 26 q14 ∷
   rw⁻ 25 q14 ∷
   rw 26 q16 ∷
   rw 25 q17 ∷
   re 24 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 26 q18 ∷
   rw 25 q19 ∷
   rw⁻ 24 q17 ∷
   rw 27 q16 ∷
   re 25 3 (CX03 ∷ []) ∷
   rw 26 q18 ∷
   rw⁻ 23 q14 ∷
   rw⁻ 22 q14 ∷
   rw⁻ 21 q14 ∷
   rw⁻ 20 q14 ∷
   rw⁻ 19 q14 ∷
   rw⁻ 18 q14 ∷
   rw⁻ 17 q14 ∷
   rw⁻ 16 q14 ∷
   rw⁻ 15 q14 ∷
   rw⁻ 14 q20 ∷
   rw⁻ 13 q15 ∷
   rw⁻ 12 q14 ∷
   rw⁻ 11 q14 ∷
   rw⁻ 10 q14 ∷
   rw⁻ 9 q14 ∷
   rw⁻ 8 q14 ∷
   rw⁻ 7 q14 ∷
   rw 8 q16 ∷
   rw 7 q17 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 8 q18 ∷
   rw 7 q19 ∷
   rw⁻ 6 q17 ∷
   rw 9 q16 ∷
   re 7 3 (CX03 ∷ []) ∷
   rw 8 q18 ∷
   rw 5 q21 ∷
   rw 4 q21 ∷
   rw 3 q22 ∷
   rw 2 q21 ∷
   rw 1 q21 ∷
   rw 0 q21 ∷ []) Eq.refl

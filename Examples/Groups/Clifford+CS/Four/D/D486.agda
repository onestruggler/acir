{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D486 (W : Ws) where

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
  q1 = eqn (CS01⁻ ∷ CK32 ∷ []) (CK32 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CK₁₀))
  q2 : Eqn
  q2 = eqn (CS01⁻ ∷ CS23 ∷ []) (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS))
  q3 : Eqn
  q3 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q4 : Eqn
  q4 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q5 : Eqn
  q5 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q6 : Eqn
  q6 = eqn (CX02 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CX02 ∷ []) (wn 1291 W)
  q7 : Eqn
  q7 = eqn (CS01⁻ ∷ S3 ∷ []) (S3 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((S ↑)))
  q8 : Eqn
  q8 = eqn (CK02 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CK02 ∷ []) (wn 1292 W)
  q9 : Eqn
  q9 = eqn (CS02 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS02 ∷ []) (wn 246 W)

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX03 CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CK32 CS23 CK32 CK32] [CSd01]: 45 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-CSd01 : ⟪ (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-CSd01 = derive (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ [])
  (rw⁻ 28 q1 ∷
   rw⁻ 27 q1 ∷
   rw⁻ 26 q2 ∷
   rw⁻ 25 q1 ∷
   rw⁻ 24 q2 ∷
   rw⁻ 23 q2 ∷
   rw 24 q3 ∷
   rw 23 q4 ∷
   re 22 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 24 q5 ∷
   rw 23 q6 ∷
   rw⁻ 22 q4 ∷
   rw 25 q3 ∷
   re 23 3 (CX03 ∷ []) ∷
   rw 24 q5 ∷
   rw⁻ 21 q2 ∷
   rw⁻ 20 q2 ∷
   rw⁻ 19 q2 ∷
   rw⁻ 18 q2 ∷
   rw⁻ 17 q2 ∷
   rw⁻ 16 q2 ∷
   rw⁻ 15 q7 ∷
   rw⁻ 14 q1 ∷
   rw⁻ 13 q2 ∷
   rw⁻ 12 q2 ∷
   rw⁻ 11 q2 ∷
   rw⁻ 10 q7 ∷
   rw⁻ 9 q1 ∷
   rw⁻ 8 q7 ∷
   rw⁻ 7 q1 ∷
   rw 8 q3 ∷
   rw 7 q4 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 7 q6 ∷
   rw⁻ 6 q4 ∷
   rw 9 q3 ∷
   re 7 3 (CX03 ∷ []) ∷
   rw 8 q5 ∷
   rw 5 q8 ∷
   rw 4 q8 ∷
   rw 3 q9 ∷
   rw 2 q8 ∷
   rw 1 q9 ∷
   rw 0 q9 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q11 : Eqn
  q11 = eqn (X0 ∷ Sw01 ∷ []) (Sw01 ∷ X1 ∷ []) (wn 1106 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q13 : Eqn
  q13 = eqn (CK02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK12⁻ ∷ []) (wn 1228 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q15 : Eqn
  q15 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q16 : Eqn
  q16 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q18 : Eqn
  q18 = eqn (CK02 ∷ Sw01 ∷ []) (Sw01 ∷ CK12 ∷ []) (wn 772 W)
  q19 : Eqn
  q19 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q20 : Eqn
  q20 = eqn (CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (X1 ∷ CK13⁻ ∷ X1 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) (wn 1293 W)
  q21 : Eqn
  q21 = eqn (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) (wn 317 W)
  q22 : Eqn
  q22 = eqn (Sw01 ∷ CK12⁻ ∷ []) (CK02⁻ ∷ Sw01 ∷ []) (wn 330 W)
  q23 : Eqn
  q23 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q24 : Eqn
  q24 = eqn (Sw01 ∷ CK12 ∷ []) (CK02 ∷ Sw01 ∷ []) (wn 329 W)
  q25 : Eqn
  q25 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q26 : Eqn
  q26 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX03 CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CK32 CS23 CK32 CK32] [X0 CKd03 X0]: 91 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CKd03-X0 : ⟪ (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CKd03-X0 = derive (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ []) (X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ [])
  (rw 32 q10 ∷
   rw 31 q11 ∷
   re 30 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q12 ∷
   rw 31 q13 ∷
   rw⁻ 30 q12 ∷
   re 31 3 (CK13⁻ ∷ []) ∷
   rw 29 q11 ∷
   rw⁻ 28 q14 ∷
   rw⁻ 27 q14 ∷
   rw⁻ 26 q15 ∷
   rw⁻ 25 q14 ∷
   rw⁻ 24 q15 ∷
   rw⁻ 23 q15 ∷
   re 22 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q12 ∷
   rw 23 q16 ∷
   rw⁻ 22 q12 ∷
   re 23 3 (CX13 ∷ []) ∷
   rw⁻ 21 q15 ∷
   rw⁻ 20 q15 ∷
   rw⁻ 19 q15 ∷
   rw⁻ 18 q15 ∷
   rw⁻ 17 q15 ∷
   rw⁻ 16 q15 ∷
   rw⁻ 15 q17 ∷
   rw⁻ 14 q14 ∷
   rw⁻ 13 q15 ∷
   rw⁻ 12 q15 ∷
   rw⁻ 11 q15 ∷
   rw⁻ 10 q17 ∷
   rw⁻ 9 q14 ∷
   rw⁻ 8 q17 ∷
   rw⁻ 7 q14 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q12 ∷
   rw 7 q16 ∷
   rw⁻ 6 q12 ∷
   re 7 3 (CX13 ∷ []) ∷
   rw 5 q18 ∷
   rw 4 q18 ∷
   rw 3 q19 ∷
   rw 2 q18 ∷
   rw 1 q19 ∷
   rw 0 q19 ∷
   rw 1 q20 ∷
   rw 0 q21 ∷
   re 2 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 1 q12 ∷
   rw 2 q22 ∷
   rw 3 q12 ∷
   re 1 3 (CK03⁻ ∷ []) ∷
   rw 2 q21 ∷
   rw 3 q23 ∷
   rw 4 q23 ∷
   rw 5 q24 ∷
   rw 6 q23 ∷
   rw 7 q24 ∷
   rw 8 q24 ∷
   re 10 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q25 ∷
   rw 11 q12 ∷
   re 9 3 (CX03 ∷ []) ∷
   rw 10 q14 ∷
   rw 11 q17 ∷
   rw 12 q14 ∷
   rw 13 q17 ∷
   rw 14 q15 ∷
   rw 15 q15 ∷
   rw 16 q15 ∷
   rw 17 q14 ∷
   rw 18 q17 ∷
   rw 19 q15 ∷
   rw 20 q15 ∷
   rw 21 q15 ∷
   rw 22 q15 ∷
   rw 23 q15 ∷
   rw 24 q15 ∷
   re 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q12 ∷
   rw 26 q25 ∷
   rw 27 q12 ∷
   re 25 3 (CX03 ∷ []) ∷
   rw 26 q15 ∷
   rw 27 q15 ∷
   rw 28 q14 ∷
   rw 29 q15 ∷
   rw 30 q14 ∷
   rw 31 q14 ∷
   rw 32 q26 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q28 : Eqn
  q28 = eqn (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) (wn 335 W)
  q29 : Eqn
  q29 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q30 : Eqn
  q30 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q31 : Eqn
  q31 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wn 1294 W)
  q32 : Eqn
  q32 = eqn (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (wn 368 W)
  q33 : Eqn
  q33 = eqn (Toff201 ∷ X0 ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ Toff201 ∷ X0 ∷ Toff201 ∷ []) (wn 1295 W)
  q34 : Eqn
  q34 = eqn (Sw23 ∷ K3 ∷ []) (K2 ∷ Sw23 ∷ []) (wn 336 W)

-- pass [TOFF301] [X0 TOFF301 X0]: 115 steps
lem-pass-TOFF301-vs-X0-TOFF301-X0 : ⟪ (Toff301 ∷ X0 ∷ Toff301 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff301 ∷ X0 ∷ Toff301 ∷ []) ⟫ʷ
lem-pass-TOFF301-vs-X0-TOFF301-X0 = derive (Toff301 ∷ X0 ∷ Toff301 ∷ X0 ∷ []) (X0 ∷ Toff301 ∷ X0 ∷ Toff301 ∷ [])
  (rw 4 q3 ∷
   rw 3 q27 ∷
   re 2 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 2 q28 ∷
   rw 5 q3 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q29 ∷
   rw 7 q3 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q29 ∷
   rw 9 q3 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q28 ∷
   rw⁻ 9 q30 ∷
   rw 10 q5 ∷
   rw 9 q30 ∷
   rw 8 q31 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 6 q29 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 4 q29 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 2 q31 ∷
   rw 3 q32 ∷
   re 3 8 (Toff201 ∷ []) ∷
   rw 1 q27 ∷
   re 0 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 1 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 0 q28 ∷
   rw 3 q3 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q29 ∷
   rw 5 q3 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q29 ∷
   rw 7 q3 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q28 ∷
   rw⁻ 7 q30 ∷
   rw 8 q5 ∷
   rw 7 q30 ∷
   rw 6 q31 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 4 q29 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 2 q29 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q31 ∷
   rw 1 q32 ∷
   re 1 8 (Toff201 ∷ []) ∷
   rw 1 q33 ∷
   rw⁻ 0 q27 ∷
   re 2 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 1 q28 ∷
   rw 4 q3 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q29 ∷
   rw 6 q3 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q29 ∷
   rw 8 q3 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q28 ∷
   rw⁻ 8 q30 ∷
   rw 1 q3 ∷
   rw 2 q34 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw⁻ 4 q29 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q29 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q34 ∷
   rw⁻ 9 q30 ∷
   rw 2 q32 ∷
   re 2 8 (Toff201 ∷ []) ∷
   re 1 3 (Toff301 ∷ []) ∷
   rw⁻ 2 q27 ∷
   re 4 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 3 q28 ∷
   rw 6 q3 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q29 ∷
   rw 8 q3 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q29 ∷
   rw 10 q3 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q28 ∷
   rw⁻ 10 q30 ∷
   rw 3 q3 ∷
   rw 4 q34 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q29 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw⁻ 8 q29 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 10 q34 ∷
   rw⁻ 11 q30 ∷
   rw 4 q32 ∷
   re 4 8 (Toff201 ∷ []) ∷
   re 3 3 (Toff301 ∷ []) ∷
   rw 4 q5 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = eqn (CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ CK13 ∷ X1 ∷ []) (X1 ∷ CK13 ∷ X1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (wn 1296 W)

-- pass [CS02 CS02 CS02 CK02 CS02 CS02 CX03 CS23 CS23 CS23 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CS23 CK32 CS23 CS23] [X0 CK03 X0]: 95 steps
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-CK03-X0 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-CK03-X0 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  (rw 34 q10 ∷
   rw 33 q11 ∷
   re 32 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q12 ∷
   rw 33 q18 ∷
   rw⁻ 32 q12 ∷
   re 33 3 (CK13 ∷ []) ∷
   rw 31 q11 ∷
   rw⁻ 30 q15 ∷
   rw⁻ 29 q15 ∷
   rw⁻ 28 q14 ∷
   rw⁻ 27 q15 ∷
   rw⁻ 26 q15 ∷
   rw⁻ 25 q15 ∷
   re 24 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q12 ∷
   rw 25 q16 ∷
   rw⁻ 24 q12 ∷
   re 25 3 (CX13 ∷ []) ∷
   rw⁻ 23 q15 ∷
   rw⁻ 22 q15 ∷
   rw⁻ 21 q15 ∷
   rw⁻ 20 q15 ∷
   rw⁻ 19 q15 ∷
   rw⁻ 18 q15 ∷
   rw⁻ 17 q15 ∷
   rw⁻ 16 q15 ∷
   rw⁻ 15 q15 ∷
   rw⁻ 14 q17 ∷
   rw⁻ 13 q14 ∷
   rw⁻ 12 q15 ∷
   rw⁻ 11 q15 ∷
   rw⁻ 10 q15 ∷
   rw⁻ 9 q15 ∷
   rw⁻ 8 q15 ∷
   rw⁻ 7 q15 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q12 ∷
   rw 7 q16 ∷
   rw⁻ 6 q12 ∷
   re 7 3 (CX13 ∷ []) ∷
   rw 5 q19 ∷
   rw 4 q19 ∷
   rw 3 q18 ∷
   rw 2 q19 ∷
   rw 1 q19 ∷
   rw 0 q19 ∷
   rw 1 q35 ∷
   rw 0 q21 ∷
   re 2 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 1 q12 ∷
   rw 2 q24 ∷
   rw 3 q12 ∷
   re 1 3 (CK03 ∷ []) ∷
   rw 2 q21 ∷
   rw 3 q23 ∷
   rw 4 q23 ∷
   rw 5 q23 ∷
   rw 6 q24 ∷
   rw 7 q23 ∷
   rw 8 q23 ∷
   re 10 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q25 ∷
   rw 11 q12 ∷
   re 9 3 (CX03 ∷ []) ∷
   rw 10 q15 ∷
   rw 11 q15 ∷
   rw 12 q15 ∷
   rw 13 q15 ∷
   rw 14 q15 ∷
   rw 15 q15 ∷
   rw 16 q14 ∷
   rw 17 q17 ∷
   rw 18 q15 ∷
   rw 19 q15 ∷
   rw 20 q15 ∷
   rw 21 q15 ∷
   rw 22 q15 ∷
   rw 23 q15 ∷
   rw 24 q15 ∷
   rw 25 q15 ∷
   rw 26 q15 ∷
   re 28 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 27 q12 ∷
   rw 28 q25 ∷
   rw 29 q12 ∷
   re 27 3 (CX03 ∷ []) ∷
   rw 28 q15 ∷
   rw 29 q15 ∷
   rw 30 q15 ∷
   rw 31 q14 ∷
   rw 32 q15 ∷
   rw 33 q15 ∷
   rw 34 q26 ∷ []) Eq.refl

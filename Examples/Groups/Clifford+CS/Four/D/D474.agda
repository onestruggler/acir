{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D474 (W : Ws) where

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
  q1 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wn 65 W)
  q2 : Eqn
  q2 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q3 : Eqn
  q3 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)
  q4 : Eqn
  q4 = eqn (CK31 ∷ Sw12 ∷ []) (Sw12 ∷ CK32 ∷ []) (wn 279 W)
  q5 : Eqn
  q5 = eqn (CS01 ∷ CK32 ∷ []) (CK32 ∷ CS01 ∷ []) (low-comm (CS) (CK₁₀))
  q6 : Eqn
  q6 = eqn (CK32 ∷ Sw12 ∷ []) (Sw12 ∷ CK31 ∷ []) (wn 280 W)
  q7 : Eqn
  q7 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q8 : Eqn
  q8 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q10 : Eqn
  q10 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q11 : Eqn
  q11 = eqn (CX13 ∷ CS12 ∷ []) (CS12 ∷ CX13 ∷ []) (wn 606 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q15 : Eqn
  q15 = eqn (CS02 ∷ S3 ∷ []) (S3 ∷ CS02 ∷ []) (low₃-comm ((Swap ↑ • CS • Swap ↑)) (S))
  q16 : Eqn
  q16 = eqn (CS01 ∷ CS02 ∷ []) (CS02 ∷ CS01 ∷ []) (wn 95 W)
  q17 : Eqn
  q17 = eqn (CK01 ∷ CS02 ∷ []) (CS02 ∷ CK01 ∷ []) (wn 1226 W)

-- pass [CS01 CS01 CS01 CK01 CS01 CS01 CX03 CS13 CS13 CS13 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CS13 CK31 CS13 CS13] [CS02]: 147 steps
lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CS02 : ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CS02 = derive (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS02 ∷ []) (CS02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  (re 31 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 30 q1 ∷
   rw⁻ 31 q2 ∷
   rw 32 q3 ∷
   re 30 3 (CS02 ∷ []) ∷
   re 30 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 29 q1 ∷
   rw⁻ 30 q2 ∷
   rw 31 q3 ∷
   re 29 3 (CS02 ∷ []) ∷
   re 29 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 28 q4 ∷
   rw⁻ 29 q5 ∷
   rw 30 q6 ∷
   re 28 3 (CS02 ∷ []) ∷
   re 28 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 27 q1 ∷
   rw⁻ 28 q2 ∷
   rw 29 q3 ∷
   re 27 3 (CS02 ∷ []) ∷
   re 27 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 26 q1 ∷
   rw⁻ 27 q2 ∷
   rw 28 q3 ∷
   re 26 3 (CS02 ∷ []) ∷
   re 26 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 25 q1 ∷
   rw⁻ 26 q2 ∷
   rw 27 q3 ∷
   re 25 3 (CS02 ∷ []) ∷
   rw 26 q7 ∷
   rw 25 q8 ∷
   re 24 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q9 ∷
   rw 25 q10 ∷
   rw⁻ 24 q9 ∷
   re 25 3 (CX13 ∷ []) ∷
   rw 25 q11 ∷
   rw 24 q12 ∷
   re 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q9 ∷
   rw 26 q13 ∷
   rw 27 q9 ∷
   re 25 3 (CX03 ∷ []) ∷
   rw 26 q14 ∷
   re 24 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 23 q1 ∷
   rw⁻ 24 q2 ∷
   rw 25 q3 ∷
   re 23 3 (CS02 ∷ []) ∷
   re 23 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 22 q1 ∷
   rw⁻ 23 q2 ∷
   rw 24 q3 ∷
   re 22 3 (CS02 ∷ []) ∷
   re 22 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 21 q1 ∷
   rw⁻ 22 q2 ∷
   rw 23 q3 ∷
   re 21 3 (CS02 ∷ []) ∷
   re 21 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 20 q1 ∷
   rw⁻ 21 q2 ∷
   rw 22 q3 ∷
   re 20 3 (CS02 ∷ []) ∷
   re 20 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 19 q1 ∷
   rw⁻ 20 q2 ∷
   rw 21 q3 ∷
   re 19 3 (CS02 ∷ []) ∷
   re 19 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 18 q1 ∷
   rw⁻ 19 q2 ∷
   rw 20 q3 ∷
   re 18 3 (CS02 ∷ []) ∷
   re 18 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 17 q1 ∷
   rw⁻ 18 q2 ∷
   rw 19 q3 ∷
   re 17 3 (CS02 ∷ []) ∷
   re 17 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 16 q1 ∷
   rw⁻ 17 q2 ∷
   rw 18 q3 ∷
   re 16 3 (CS02 ∷ []) ∷
   re 16 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 15 q1 ∷
   rw⁻ 16 q2 ∷
   rw 17 q3 ∷
   re 15 3 (CS02 ∷ []) ∷
   rw⁻ 14 q15 ∷
   re 14 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 13 q4 ∷
   rw⁻ 14 q5 ∷
   rw 15 q6 ∷
   re 13 3 (CS02 ∷ []) ∷
   re 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 12 q1 ∷
   rw⁻ 13 q2 ∷
   rw 14 q3 ∷
   re 12 3 (CS02 ∷ []) ∷
   re 12 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 11 q1 ∷
   rw⁻ 12 q2 ∷
   rw 13 q3 ∷
   re 11 3 (CS02 ∷ []) ∷
   re 11 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 10 q1 ∷
   rw⁻ 11 q2 ∷
   rw 12 q3 ∷
   re 10 3 (CS02 ∷ []) ∷
   re 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 9 q1 ∷
   rw⁻ 10 q2 ∷
   rw 11 q3 ∷
   re 9 3 (CS02 ∷ []) ∷
   re 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 8 q1 ∷
   rw⁻ 9 q2 ∷
   rw 10 q3 ∷
   re 8 3 (CS02 ∷ []) ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 q1 ∷
   rw⁻ 8 q2 ∷
   rw 9 q3 ∷
   re 7 3 (CS02 ∷ []) ∷
   rw 8 q7 ∷
   rw 7 q8 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q9 ∷
   rw 7 q10 ∷
   rw⁻ 6 q9 ∷
   re 7 3 (CX13 ∷ []) ∷
   rw 7 q11 ∷
   rw 6 q12 ∷
   re 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 7 q9 ∷
   rw 8 q13 ∷
   rw 9 q9 ∷
   re 7 3 (CX03 ∷ []) ∷
   rw 8 q14 ∷
   rw 5 q16 ∷
   rw 4 q16 ∷
   rw 3 q17 ∷
   rw 2 q16 ∷
   rw 1 q16 ∷
   rw 0 q16 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q19 : Eqn
  q19 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q20 : Eqn
  q20 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q21 : Eqn
  q21 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q22 : Eqn
  q22 = eqn (CK01 ∷ Sw23 ∷ []) (Sw23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (Swap))
  q23 : Eqn
  q23 = eqn (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) (CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ []) (wn 1238 W)
  q24 : Eqn
  q24 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q25 : Eqn
  q25 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q26 : Eqn
  q26 = eqn (CK01 ∷ CX32 ∷ []) (CX32 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₁₀))
  q27 : Eqn
  q27 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q28 : Eqn
  q28 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q29 : Eqn
  q29 = eqn (CX31 ∷ CX32 ∷ []) (CX32 ∷ CX31 ∷ []) (wn 892 W)
  q30 : Eqn
  q30 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q31 : Eqn
  q31 = eqn (S0 ∷ CX32 ∷ []) (CX32 ∷ S0 ∷ []) (low₁-comm (S) ((CX₁₀ ↑)))
  q32 : Eqn
  q32 = eqn (CS13 ∷ CX32 ∷ []) (CX32 ∷ CS13 ∷ []) (wn 894 W)
  q33 : Eqn
  q33 = eqn (CK31 ∷ CX32 ∷ []) (CX32 ∷ CK31 ∷ []) (wn 893 W)
  q34 : Eqn
  q34 = eqn (CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) (wn 1239 W)
  q35 : Eqn
  q35 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)

-- pass [CS01 CS01 CS01 CK01 CS01 CS01 CX03 CS13 CS13 CS13 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CS13 CK31 CS13 CS13] [CX32]: 253 steps
lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CX32 : ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CX32 = derive (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  (rw 31 q18 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q19 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q19 ∷
   re 28 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 30 q19 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q19 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q19 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q19 ∷
   re 24 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 26 q19 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q19 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q19 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q19 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q19 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q19 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q19 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q19 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q19 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q19 ∷
   rw 14 q20 ∷
   re 13 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 15 q19 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q19 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q19 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q19 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q19 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q19 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q19 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 8 q19 ∷
   rw 5 q21 ∷
   rw 4 q21 ∷
   rw 3 q22 ∷
   rw 2 q21 ∷
   rw 1 q21 ∷
   rw 0 q21 ∷
   rw 1 q23 ∷
   rw 2 q18 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw 3 q18 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 4 q18 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 5 q18 ∷
   re 3 3 (CK31 ∷ []) ∷
   rw 6 q18 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 7 q18 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 8 q18 ∷
   re 6 3 (CX30 ∷ []) ∷
   rw⁻ 7 q21 ∷
   rw⁻ 8 q21 ∷
   rw⁻ 9 q21 ∷
   rw⁻ 10 q21 ∷
   rw⁻ 11 q21 ∷
   rw⁻ 12 q21 ∷
   rw⁻ 13 q22 ∷
   rw⁻ 14 q24 ∷
   rw⁻ 15 q21 ∷
   rw⁻ 16 q21 ∷
   rw⁻ 17 q21 ∷
   rw⁻ 18 q21 ∷
   rw⁻ 19 q21 ∷
   rw⁻ 20 q21 ∷
   rw⁻ 21 q21 ∷
   rw⁻ 22 q21 ∷
   rw⁻ 23 q21 ∷
   rw 26 q18 ∷
   re 24 3 (CX30 ∷ []) ∷
   rw⁻ 25 q21 ∷
   rw⁻ 26 q21 ∷
   rw⁻ 27 q21 ∷
   rw⁻ 28 q22 ∷
   rw⁻ 29 q21 ∷
   rw⁻ 30 q21 ∷
   rw 31 q19 ∷
   rw 30 q25 ∷
   rw 29 q25 ∷
   rw 28 q26 ∷
   rw 27 q25 ∷
   rw 26 q25 ∷
   rw 25 q25 ∷
   rw 26 q7 ∷
   rw⁻ 25 q27 ∷
   re 24 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q9 ∷
   rw 25 q28 ∷
   rw⁻ 24 q9 ∷
   re 25 3 (CX31 ∷ []) ∷
   rw 25 q29 ∷
   rw 24 q27 ∷
   re 26 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 25 q9 ∷
   rw 26 q30 ∷
   rw 27 q9 ∷
   re 25 3 (CX30 ∷ []) ∷
   rw 26 q14 ∷
   rw 23 q25 ∷
   rw 22 q25 ∷
   rw 21 q25 ∷
   rw 20 q25 ∷
   rw 19 q25 ∷
   rw 18 q25 ∷
   rw 17 q25 ∷
   rw 16 q25 ∷
   rw 15 q25 ∷
   rw 14 q31 ∷
   rw 13 q26 ∷
   rw 12 q25 ∷
   rw 11 q25 ∷
   rw 10 q25 ∷
   rw 9 q25 ∷
   rw 8 q25 ∷
   rw 7 q25 ∷
   rw 8 q7 ∷
   rw⁻ 7 q27 ∷
   re 6 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q9 ∷
   rw 7 q28 ∷
   rw⁻ 6 q9 ∷
   re 7 3 (CX31 ∷ []) ∷
   rw 7 q29 ∷
   rw 6 q27 ∷
   re 8 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 7 q9 ∷
   rw 8 q30 ∷
   rw 9 q9 ∷
   re 7 3 (CX30 ∷ []) ∷
   rw 8 q14 ∷
   rw 5 q32 ∷
   rw 4 q32 ∷
   rw 3 q33 ∷
   rw 2 q32 ∷
   rw 1 q32 ∷
   rw 0 q32 ∷
   rw 32 q18 ∷
   rw 31 q21 ∷
   rw 30 q21 ∷
   rw 29 q22 ∷
   rw 28 q21 ∷
   rw 27 q21 ∷
   rw 26 q21 ∷
   re 25 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 27 q19 ∷
   rw 24 q21 ∷
   rw 23 q21 ∷
   rw 22 q21 ∷
   rw 21 q21 ∷
   rw 20 q21 ∷
   rw 19 q21 ∷
   rw 18 q21 ∷
   rw 17 q21 ∷
   rw 16 q21 ∷
   rw 15 q24 ∷
   rw 14 q22 ∷
   rw 13 q21 ∷
   rw 12 q21 ∷
   rw 11 q21 ∷
   rw 10 q21 ∷
   rw 9 q21 ∷
   rw 8 q21 ∷
   re 7 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 9 q19 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q19 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q19 ∷
   re 4 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 6 q19 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q19 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q19 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q19 ∷
   rw 2 q34 ∷
   rw⁻ 1 q21 ∷
   rw⁻ 2 q21 ∷
   rw⁻ 3 q21 ∷
   rw⁻ 4 q22 ∷
   rw⁻ 5 q21 ∷
   rw⁻ 6 q21 ∷
   rw 9 q18 ∷
   re 7 3 (CX03 ∷ []) ∷
   rw 10 q18 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 11 q18 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 12 q18 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 13 q18 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 14 q18 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 15 q18 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 16 q18 ∷
   re 14 3 (CK31 ∷ []) ∷
   rw 15 q35 ∷
   rw 18 q18 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw 19 q18 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 20 q18 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 21 q18 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 22 q18 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 23 q18 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 24 q18 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 25 q18 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 26 q18 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 27 q18 ∷
   re 25 3 (CX03 ∷ []) ∷
   rw 28 q18 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 29 q18 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 30 q18 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 31 q18 ∷
   re 29 3 (CK31 ∷ []) ∷
   rw 32 q18 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw 33 q18 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 32 q19 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (CS01⁻ ∷ CS23 ∷ []) (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS))
  q37 : Eqn
  q37 = eqn (CS01⁻ ∷ CK32 ∷ []) (CK32 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CK₁₀))
  q38 : Eqn
  q38 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q39 : Eqn
  q39 = eqn (CX13 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CX13 ∷ []) (wn 608 W)
  q40 : Eqn
  q40 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q41 : Eqn
  q41 = eqn (CS02⁻ ∷ S3 ∷ []) (S3 ∷ CS02⁻ ∷ []) (low₃-comm ((Swap ↑ • (CS • CS • CS) • Swap ↑)) (S))
  q42 : Eqn
  q42 = eqn (CS01 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS01 ∷ []) (wn 88 W)
  q43 : Eqn
  q43 = eqn (CK01 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CK01 ∷ []) (wn 1227 W)

-- pass [CS01 CS01 CS01 CK01 CS01 CS01 CX03 CS13 CS13 CS13 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CS13 CK31 CS13 CS13] [CSd02]: 147 steps
lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CSd02 : ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CSd02 = derive (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  (re 31 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 30 q1 ∷
   rw⁻ 31 q36 ∷
   rw 32 q3 ∷
   re 30 3 (CS02⁻ ∷ []) ∷
   re 30 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 29 q1 ∷
   rw⁻ 30 q36 ∷
   rw 31 q3 ∷
   re 29 3 (CS02⁻ ∷ []) ∷
   re 29 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 28 q4 ∷
   rw⁻ 29 q37 ∷
   rw 30 q6 ∷
   re 28 3 (CS02⁻ ∷ []) ∷
   re 28 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 27 q1 ∷
   rw⁻ 28 q36 ∷
   rw 29 q3 ∷
   re 27 3 (CS02⁻ ∷ []) ∷
   re 27 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 26 q1 ∷
   rw⁻ 27 q36 ∷
   rw 28 q3 ∷
   re 26 3 (CS02⁻ ∷ []) ∷
   re 26 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 25 q1 ∷
   rw⁻ 26 q36 ∷
   rw 27 q3 ∷
   re 25 3 (CS02⁻ ∷ []) ∷
   rw 26 q7 ∷
   rw 25 q38 ∷
   re 24 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q9 ∷
   rw 25 q10 ∷
   rw⁻ 24 q9 ∷
   re 25 3 (CX13 ∷ []) ∷
   rw 25 q39 ∷
   rw 24 q40 ∷
   re 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q9 ∷
   rw 26 q13 ∷
   rw 27 q9 ∷
   re 25 3 (CX03 ∷ []) ∷
   rw 26 q14 ∷
   re 24 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 23 q1 ∷
   rw⁻ 24 q36 ∷
   rw 25 q3 ∷
   re 23 3 (CS02⁻ ∷ []) ∷
   re 23 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 22 q1 ∷
   rw⁻ 23 q36 ∷
   rw 24 q3 ∷
   re 22 3 (CS02⁻ ∷ []) ∷
   re 22 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 21 q1 ∷
   rw⁻ 22 q36 ∷
   rw 23 q3 ∷
   re 21 3 (CS02⁻ ∷ []) ∷
   re 21 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 20 q1 ∷
   rw⁻ 21 q36 ∷
   rw 22 q3 ∷
   re 20 3 (CS02⁻ ∷ []) ∷
   re 20 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 19 q1 ∷
   rw⁻ 20 q36 ∷
   rw 21 q3 ∷
   re 19 3 (CS02⁻ ∷ []) ∷
   re 19 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 18 q1 ∷
   rw⁻ 19 q36 ∷
   rw 20 q3 ∷
   re 18 3 (CS02⁻ ∷ []) ∷
   re 18 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 17 q1 ∷
   rw⁻ 18 q36 ∷
   rw 19 q3 ∷
   re 17 3 (CS02⁻ ∷ []) ∷
   re 17 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 16 q1 ∷
   rw⁻ 17 q36 ∷
   rw 18 q3 ∷
   re 16 3 (CS02⁻ ∷ []) ∷
   re 16 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 15 q1 ∷
   rw⁻ 16 q36 ∷
   rw 17 q3 ∷
   re 15 3 (CS02⁻ ∷ []) ∷
   rw⁻ 14 q41 ∷
   re 14 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 13 q4 ∷
   rw⁻ 14 q37 ∷
   rw 15 q6 ∷
   re 13 3 (CS02⁻ ∷ []) ∷
   re 13 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 12 q1 ∷
   rw⁻ 13 q36 ∷
   rw 14 q3 ∷
   re 12 3 (CS02⁻ ∷ []) ∷
   re 12 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 11 q1 ∷
   rw⁻ 12 q36 ∷
   rw 13 q3 ∷
   re 11 3 (CS02⁻ ∷ []) ∷
   re 11 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 10 q1 ∷
   rw⁻ 11 q36 ∷
   rw 12 q3 ∷
   re 10 3 (CS02⁻ ∷ []) ∷
   re 10 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 9 q1 ∷
   rw⁻ 10 q36 ∷
   rw 11 q3 ∷
   re 9 3 (CS02⁻ ∷ []) ∷
   re 9 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 8 q1 ∷
   rw⁻ 9 q36 ∷
   rw 10 q3 ∷
   re 8 3 (CS02⁻ ∷ []) ∷
   re 8 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 7 q1 ∷
   rw⁻ 8 q36 ∷
   rw 9 q3 ∷
   re 7 3 (CS02⁻ ∷ []) ∷
   rw 8 q7 ∷
   rw 7 q38 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q9 ∷
   rw 7 q10 ∷
   rw⁻ 6 q9 ∷
   re 7 3 (CX13 ∷ []) ∷
   rw 7 q39 ∷
   rw 6 q40 ∷
   re 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 7 q9 ∷
   rw 8 q13 ∷
   rw 9 q9 ∷
   re 7 3 (CX03 ∷ []) ∷
   rw 8 q14 ∷
   rw 5 q42 ∷
   rw 4 q42 ∷
   rw 3 q43 ∷
   rw 2 q42 ∷
   rw 1 q42 ∷
   rw 0 q42 ∷ []) Eq.refl

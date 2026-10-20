{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D246 (W : Ws) where

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
  q2 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q3 : Eqn
  q3 = eqn (CK31 ∷ X2 ∷ []) (X2 ∷ CK31 ∷ []) (wn 630 W)
  q4 : Eqn
  q4 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q6 : Eqn
  q6 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q7 : Eqn
  q7 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q8 : Eqn
  q8 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q9 : Eqn
  q9 = eqn (CK10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((CS • CS • CS)))
  q10 : Eqn
  q10 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q11 : Eqn
  q11 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q12 : Eqn
  q12 = eqn (Sw12 ∷ CK31⁻ ∷ []) (CK32⁻ ∷ Sw12 ∷ []) (wn 360 W)
  q13 : Eqn
  q13 = eqn (CK10 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((S ↑ • CK₁₀)))
  q14 : Eqn
  q14 = eqn (Sw12 ∷ CK32⁻ ∷ []) (CK31⁻ ∷ Sw12 ∷ []) (wn 362 W)
  q15 : Eqn
  q15 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q16 : Eqn
  q16 = eqn (CK10 ∷ CS23 ∷ []) (CS23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CS))
  q17 : Eqn
  q17 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q18 : Eqn
  q18 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q19 : Eqn
  q19 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q20 : Eqn
  q20 = eqn (CS13 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ []) (wn 629 W)
  q21 : Eqn
  q21 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q22 : Eqn
  q22 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q23 : Eqn
  q23 = eqn (CS01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CS01 ∷ []) (low-comm (CS) ((S ↑ • CK₁₀)))
  q24 : Eqn
  q24 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q25 : Eqn
  q25 = eqn (CX23 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ CX23 ∷ []) (wn 751 W)
  q26 : Eqn
  q26 = eqn (CS02 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ CS02 ∷ []) (wn 753 W)
  q27 : Eqn
  q27 = eqn (CK20 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ CK20 ∷ []) (wn 752 W)

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X2 CSd12 CKd21 CS12 CS12 X2] part2: 466 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd12-CKd21-CS12-CS12-X2-part2 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd12-CKd21-CS12-CS12-X2-part2 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw⁻ 15 q1 ∷
   rw 14 q2 ∷
   rw⁻ 13 q1 ∷
   re 14 3 (CK31 ∷ []) ∷
   rw 14 q3 ∷
   rw 13 q4 ∷
   re 15 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 14 q1 ∷
   rw 15 q5 ∷
   rw 16 q1 ∷
   re 14 3 (CK30 ∷ []) ∷
   rw 15 q6 ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q7 ∷
   re 18 3 (CS13⁻ ∷ []) ∷
   rw 17 q8 ∷
   rw 16 q9 ∷
   rw 15 q10 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q11 ∷
   re 15 5 (CK30 ∷ []) ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q7 ∷
   re 19 3 (CK31⁻ ∷ []) ∷
   rw 18 q12 ∷
   rw 17 q13 ∷
   rw 16 q14 ∷
   re 16 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q11 ∷
   re 16 5 (CK30 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q7 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 19 q15 ∷
   rw 18 q16 ∷
   rw 17 q17 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q11 ∷
   re 17 5 (CK30 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q7 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 20 q15 ∷
   rw 19 q16 ∷
   rw 18 q17 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q11 ∷
   re 18 5 (CK30 ∷ []) ∷
   rw 20 q18 ∷
   rw⁻ 19 q4 ∷
   re 18 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q1 ∷
   rw 19 q2 ∷
   rw⁻ 18 q1 ∷
   re 19 3 (CK31 ∷ []) ∷
   rw 19 q3 ∷
   rw 18 q4 ∷
   re 20 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 19 q1 ∷
   rw 20 q5 ∷
   rw 21 q1 ∷
   re 19 3 (CK30 ∷ []) ∷
   rw 20 q6 ∷
   rw 14 q18 ∷
   rw⁻ 13 q4 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q1 ∷
   rw 13 q19 ∷
   rw⁻ 12 q1 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 13 q20 ∷
   rw 12 q4 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q1 ∷
   rw 14 q21 ∷
   rw 15 q1 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q6 ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q7 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw 16 q8 ∷
   rw 15 q22 ∷
   rw 14 q10 ∷
   re 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q11 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q7 ∷
   re 18 3 (CK31⁻ ∷ []) ∷
   rw 17 q12 ∷
   rw 16 q23 ∷
   rw 15 q14 ∷
   re 15 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q11 ∷
   re 15 5 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q7 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 18 q15 ∷
   rw 17 q24 ∷
   rw 16 q17 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q11 ∷
   re 16 5 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q7 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 19 q15 ∷
   rw 18 q24 ∷
   rw 17 q17 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q11 ∷
   re 17 5 (CS03 ∷ []) ∷
   rw 19 q18 ∷
   rw⁻ 18 q4 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q1 ∷
   rw 18 q19 ∷
   rw⁻ 17 q1 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 18 q20 ∷
   rw 17 q4 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q1 ∷
   rw 19 q21 ∷
   rw 20 q1 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 19 q6 ∷
   rw 13 q18 ∷
   rw⁻ 12 q4 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q1 ∷
   rw 12 q19 ∷
   rw⁻ 11 q1 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 12 q20 ∷
   rw 11 q4 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q1 ∷
   rw 13 q21 ∷
   rw 14 q1 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q6 ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q7 ∷
   re 16 3 (CS13⁻ ∷ []) ∷
   rw 15 q8 ∷
   rw 14 q22 ∷
   rw 13 q10 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q11 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q7 ∷
   re 17 3 (CK31⁻ ∷ []) ∷
   rw 16 q12 ∷
   rw 15 q23 ∷
   rw 14 q14 ∷
   re 14 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q11 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q7 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 17 q15 ∷
   rw 16 q24 ∷
   rw 15 q17 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q11 ∷
   re 15 5 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q7 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 18 q15 ∷
   rw 17 q24 ∷
   rw 16 q17 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q11 ∷
   re 16 5 (CS03 ∷ []) ∷
   rw 18 q18 ∷
   rw⁻ 17 q4 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q1 ∷
   rw 17 q19 ∷
   rw⁻ 16 q1 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 17 q20 ∷
   rw 16 q4 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q1 ∷
   rw 18 q21 ∷
   rw 19 q1 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 18 q6 ∷
   rw 12 q18 ∷
   rw⁻ 11 q4 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q1 ∷
   rw 11 q19 ∷
   rw⁻ 10 q1 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 11 q20 ∷
   rw 10 q4 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q1 ∷
   rw 12 q21 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q6 ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q7 ∷
   re 15 3 (CS13⁻ ∷ []) ∷
   rw 14 q8 ∷
   rw 13 q22 ∷
   rw 12 q10 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q11 ∷
   re 12 5 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q7 ∷
   re 16 3 (CK31⁻ ∷ []) ∷
   rw 15 q12 ∷
   rw 14 q23 ∷
   rw 13 q14 ∷
   re 13 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q11 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q7 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 16 q15 ∷
   rw 15 q24 ∷
   rw 14 q17 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q11 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q7 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 17 q15 ∷
   rw 16 q24 ∷
   rw 15 q17 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q11 ∷
   re 15 5 (CS03 ∷ []) ∷
   rw 17 q18 ∷
   rw⁻ 16 q4 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q1 ∷
   rw 16 q19 ∷
   rw⁻ 15 q1 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw 16 q20 ∷
   rw 15 q4 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q1 ∷
   rw 17 q21 ∷
   rw 18 q1 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 17 q6 ∷
   rw 11 q18 ∷
   rw⁻ 10 q4 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q1 ∷
   rw 10 q19 ∷
   rw⁻ 9 q1 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 10 q20 ∷
   rw 9 q4 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q1 ∷
   rw 11 q21 ∷
   rw 12 q1 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q6 ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q7 ∷
   re 14 3 (CS13⁻ ∷ []) ∷
   rw 13 q8 ∷
   rw 12 q22 ∷
   rw 11 q10 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q11 ∷
   re 11 5 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q7 ∷
   re 15 3 (CK31⁻ ∷ []) ∷
   rw 14 q12 ∷
   rw 13 q23 ∷
   rw 12 q14 ∷
   re 12 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q11 ∷
   re 12 5 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q7 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw 15 q15 ∷
   rw 14 q24 ∷
   rw 13 q17 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q11 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q7 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 16 q15 ∷
   rw 15 q24 ∷
   rw 14 q17 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q11 ∷
   re 14 5 (CS03 ∷ []) ∷
   rw 16 q18 ∷
   rw⁻ 15 q4 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q1 ∷
   rw 15 q19 ∷
   rw⁻ 14 q1 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw 15 q20 ∷
   rw 14 q4 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q1 ∷
   rw 16 q21 ∷
   rw 17 q1 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 16 q6 ∷
   rw 10 q18 ∷
   rw⁻ 9 q4 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q1 ∷
   rw 9 q19 ∷
   rw⁻ 8 q1 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 9 q20 ∷
   rw 8 q4 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q1 ∷
   rw 10 q21 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q6 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q7 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw 12 q8 ∷
   rw 11 q22 ∷
   rw 10 q10 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q11 ∷
   re 10 5 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q7 ∷
   re 14 3 (CK31⁻ ∷ []) ∷
   rw 13 q12 ∷
   rw 12 q23 ∷
   rw 11 q14 ∷
   re 11 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q11 ∷
   re 11 5 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q7 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw 14 q15 ∷
   rw 13 q24 ∷
   rw 12 q17 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q11 ∷
   re 12 5 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q7 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw 15 q15 ∷
   rw 14 q24 ∷
   rw 13 q17 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q11 ∷
   re 13 5 (CS03 ∷ []) ∷
   rw 15 q18 ∷
   rw⁻ 14 q4 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q1 ∷
   rw 14 q19 ∷
   rw⁻ 13 q1 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 14 q20 ∷
   rw 13 q4 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q1 ∷
   rw 15 q21 ∷
   rw 16 q1 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q6 ∷
   rw 9 q18 ∷
   rw⁻ 8 q4 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q1 ∷
   rw 8 q19 ∷
   rw⁻ 7 q1 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 8 q20 ∷
   rw 7 q4 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q1 ∷
   rw 9 q21 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q6 ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q7 ∷
   re 12 3 (CS13⁻ ∷ []) ∷
   rw 11 q8 ∷
   rw 10 q22 ∷
   rw 9 q10 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q11 ∷
   re 9 5 (CS03 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q7 ∷
   re 13 3 (CK31⁻ ∷ []) ∷
   rw 12 q12 ∷
   rw 11 q23 ∷
   rw 10 q14 ∷
   re 10 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q11 ∷
   re 10 5 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q7 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 13 q15 ∷
   rw 12 q24 ∷
   rw 11 q17 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q11 ∷
   re 11 5 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q7 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw 14 q15 ∷
   rw 13 q24 ∷
   rw 12 q17 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q11 ∷
   re 12 5 (CS03 ∷ []) ∷
   rw 14 q18 ∷
   rw⁻ 13 q4 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q1 ∷
   rw 13 q19 ∷
   rw⁻ 12 q1 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 13 q20 ∷
   rw 12 q4 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q1 ∷
   rw 14 q21 ∷
   rw 15 q1 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q6 ∷
   rw 6 q25 ∷
   rw 5 q26 ∷
   rw 4 q26 ∷
   rw 3 q27 ∷
   rw 2 q26 ∷
   rw 1 q26 ∷
   rw 0 q26 ∷ []) Eq.refl

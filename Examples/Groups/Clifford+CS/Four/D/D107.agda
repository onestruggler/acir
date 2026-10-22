{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D107 (W : Ws) where

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
  q1 = wE 27 W
  q2 : Eqn
  q2 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = wE 31 W
  q4 : Eqn
  q4 = wE 1 W
  q5 : Eqn
  q5 = wE 360 W
  q6 : Eqn
  q6 = eqn (CS01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CS01 ∷ []) (low-comm (CS) ((S ↑ • CK₁₀)))
  q7 : Eqn
  q7 = wE 362 W
  q8 : Eqn
  q8 = wE 3 W
  q9 : Eqn
  q9 = wE 5 W
  q10 : Eqn
  q10 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q11 : Eqn
  q11 = wE 7 W
  q12 : Eqn
  q12 = wE 629 W
  q13 : Eqn
  q13 = wE 645 W
  q14 : Eqn
  q14 = wE 503 W
  q15 : Eqn
  q15 = wE 646 W
  q16 : Eqn
  q16 = wE 502 W

-- pass [CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 S3 S3 S3 CK30 S3 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03] [X2 CKd21 X2] part3: 200 steps
lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-X2-CKd21-X2-part3 : ⟪ (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CK21⁻ ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-X2-CKd21-X2-part3 = derive (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CK21⁻ ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ [])
  (rw 22 q1 ∷
   rw 23 q2 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 22 q3 ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q4 ∷
   re 25 3 (CK31⁻ ∷ []) ∷
   rw 24 q5 ∷
   rw 23 q6 ∷
   rw 22 q7 ∷
   re 22 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q8 ∷
   re 22 5 (CS03 ∷ []) ∷
   rw 24 q9 ∷
   rw⁻ 23 q10 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q2 ∷
   rw 23 q11 ∷
   rw⁻ 22 q2 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 23 q12 ∷
   rw 22 q10 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q2 ∷
   rw 24 q1 ∷
   rw 25 q2 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 24 q3 ∷
   rw 21 q9 ∷
   rw⁻ 20 q10 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q2 ∷
   rw 20 q11 ∷
   rw⁻ 19 q2 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 20 q12 ∷
   rw 19 q10 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   rw 21 q1 ∷
   rw 22 q2 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 21 q3 ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   re 24 3 (CK31⁻ ∷ []) ∷
   rw 23 q5 ∷
   rw 22 q6 ∷
   rw 21 q7 ∷
   re 21 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q8 ∷
   re 21 5 (CS03 ∷ []) ∷
   rw 23 q9 ∷
   rw⁻ 22 q10 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q2 ∷
   rw 22 q11 ∷
   rw⁻ 21 q2 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 22 q12 ∷
   rw 21 q10 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   rw 23 q1 ∷
   rw 24 q2 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 23 q3 ∷
   rw 20 q9 ∷
   rw⁻ 19 q10 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q2 ∷
   rw 19 q11 ∷
   rw⁻ 18 q2 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 19 q12 ∷
   rw 18 q10 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   rw 20 q1 ∷
   rw 21 q2 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 20 q3 ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   re 23 3 (CK31⁻ ∷ []) ∷
   rw 22 q5 ∷
   rw 21 q6 ∷
   rw 20 q7 ∷
   re 20 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q8 ∷
   re 20 5 (CS03 ∷ []) ∷
   rw 22 q9 ∷
   rw⁻ 21 q10 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q2 ∷
   rw 21 q11 ∷
   rw⁻ 20 q2 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 21 q12 ∷
   rw 20 q10 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q2 ∷
   rw 22 q1 ∷
   rw 23 q2 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 22 q3 ∷
   rw 19 q9 ∷
   rw⁻ 18 q10 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q2 ∷
   rw 18 q11 ∷
   rw⁻ 17 q2 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 18 q12 ∷
   rw 17 q10 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q2 ∷
   rw 19 q1 ∷
   rw 20 q2 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 19 q3 ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   re 22 3 (CK31⁻ ∷ []) ∷
   rw 21 q5 ∷
   rw 20 q6 ∷
   rw 19 q7 ∷
   re 19 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q8 ∷
   re 19 5 (CS03 ∷ []) ∷
   rw 21 q9 ∷
   rw⁻ 20 q10 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q2 ∷
   rw 20 q11 ∷
   rw⁻ 19 q2 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 20 q12 ∷
   rw 19 q10 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   rw 21 q1 ∷
   rw 22 q2 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 21 q3 ∷
   rw 18 q9 ∷
   rw⁻ 17 q10 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q2 ∷
   rw 17 q11 ∷
   rw⁻ 16 q2 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 17 q12 ∷
   rw 16 q10 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   rw 18 q1 ∷
   rw 19 q2 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 18 q3 ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q4 ∷
   re 21 3 (CK31⁻ ∷ []) ∷
   rw 20 q5 ∷
   rw 19 q6 ∷
   rw 18 q7 ∷
   re 18 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q8 ∷
   re 18 5 (CS03 ∷ []) ∷
   rw 20 q9 ∷
   rw⁻ 19 q10 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q2 ∷
   rw 19 q11 ∷
   rw⁻ 18 q2 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 19 q12 ∷
   rw 18 q10 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   rw 20 q1 ∷
   rw 21 q2 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 20 q3 ∷
   rw 15 q13 ∷
   rw 14 q14 ∷
   rw 13 q14 ∷
   rw 12 q14 ∷
   rw 11 q14 ∷
   rw 10 q14 ∷
   rw 9 q14 ∷
   rw 8 q15 ∷
   rw 7 q16 ∷
   rw 6 q14 ∷
   rw 5 q14 ∷
   rw 4 q14 ∷
   rw 3 q15 ∷
   rw 2 q16 ∷
   rw 1 q15 ∷
   rw 0 q16 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = wE 647 W
  q18 : Eqn
  q18 = wE 107 W
  q19 : Eqn
  q19 = eqn (CS01 ∷ CZ23 ∷ []) (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ))
  q20 : Eqn
  q20 = wE 108 W
  q21 : Eqn
  q21 = eqn (CK10⁻ ∷ CZ23 ∷ []) (CZ23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CZ))
  q22 : Eqn
  q22 = eqn (CS01⁻ ∷ CZ23 ∷ []) (CZ23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CZ))
  q23 : Eqn
  q23 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q24 : Eqn
  q24 = wE 137 W
  q25 : Eqn
  q25 = wE 76 W
  q26 : Eqn
  q26 = wE 648 W
  q27 : Eqn
  q27 = wE 29 W
  q28 : Eqn
  q28 = wE 139 W
  q29 : Eqn
  q29 = wE 649 W
  q30 : Eqn
  q30 = wE 113 W
  q31 : Eqn
  q31 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q32 : Eqn
  q32 = wE 114 W
  q33 : Eqn
  q33 = eqn (CK10⁻ ∷ CX32 ∷ []) (CX32 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q34 : Eqn
  q34 = eqn (CS01⁻ ∷ CX32 ∷ []) (CX32 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₁₀))
  q35 : Eqn
  q35 = wE 650 W
  q36 : Eqn
  q36 = wE 651 W

-- groups [CSd02 CKd20 CS02 CS02] [X2 CK21 X2 CZ13 CS23 CS12 CX31 CSd12 CX31 X2 CKd21 X2]: 197 steps
lem-groups-CSd02-CKd20-CS02-CS02-vs-X2-CK21-X2-CZ13-CS23-CS12-CX31-CSd12-CX31-X2-CKd21-X2 : ⟪ (CS02⁻ ∷ CK20⁻ ∷ CS02 ∷ CS02 ∷ X2 ∷ CK21 ∷ X2 ∷ CZ13 ∷ CS23 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ CZ13 ∷ CS23 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-groups-CSd02-CKd20-CS02-CS02-vs-X2-CK21-X2-CZ13-CS23-CS12-CX31-CSd12-CX31-X2-CKd21-X2 = derive (CS02⁻ ∷ CK20⁻ ∷ CS02 ∷ CS02 ∷ X2 ∷ CK21 ∷ X2 ∷ CZ13 ∷ CS23 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ CZ13 ∷ CS23 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02 ∷ CS02 ∷ [])
  (rw 0 q17 ∷
   re 7 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 6 q4 ∷
   re 7 3 (CS03 ∷ []) ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q4 ∷
   re 11 3 (CZ13 ∷ []) ∷
   rw 10 q18 ∷
   rw 9 q19 ∷
   rw 8 q20 ∷
   re 8 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 7 q8 ∷
   re 8 5 (CS03 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q8 ∷
   re 6 3 (CZ13 ∷ []) ∷
   re 6 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 5 q4 ∷
   re 6 3 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 12 q4 ∷
   re 10 3 (CZ13 ∷ []) ∷
   rw 9 q18 ∷
   rw 8 q19 ∷
   rw 7 q20 ∷
   re 7 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 6 q8 ∷
   re 7 5 (CS03 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q8 ∷
   re 5 3 (CZ13 ∷ []) ∷
   re 5 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   re 5 3 (CK30⁻ ∷ []) ∷
   re 5 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 11 q4 ∷
   re 9 3 (CZ13 ∷ []) ∷
   rw 8 q18 ∷
   rw 7 q21 ∷
   rw 6 q20 ∷
   re 6 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 5 q8 ∷
   re 6 5 (CK30⁻ ∷ []) ∷
   re 6 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   re 4 3 (CZ13 ∷ []) ∷
   re 4 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   re 4 3 (CS03⁻ ∷ []) ∷
   re 4 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q4 ∷
   re 8 3 (CZ13 ∷ []) ∷
   rw 7 q18 ∷
   rw 6 q22 ∷
   rw 5 q20 ∷
   re 5 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 4 q8 ∷
   re 5 5 (CS03⁻ ∷ []) ∷
   re 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q8 ∷
   re 3 3 (CZ13 ∷ []) ∷
   rw 9 q9 ∷
   rw⁻ 8 q23 ∷
   rw 7 q11 ∷
   rw 6 q11 ∷
   rw 5 q24 ∷
   rw 4 q25 ∷
   rw 5 q26 ∷
   rw 4 q23 ∷
   rw 5 q27 ∷
   rw 6 q28 ∷
   rw 7 q1 ∷
   rw 8 q1 ∷
   rw 9 q3 ∷
   rw 5 q29 ∷
   re 10 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 9 q4 ∷
   re 10 3 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q4 ∷
   re 14 3 (CX31 ∷ []) ∷
   rw 13 q30 ∷
   rw 12 q31 ∷
   rw 11 q32 ∷
   re 11 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 10 q8 ∷
   re 11 5 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q8 ∷
   re 9 3 (CX31 ∷ []) ∷
   re 9 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q4 ∷
   re 9 3 (CS03 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q4 ∷
   re 13 3 (CX31 ∷ []) ∷
   rw 12 q30 ∷
   rw 11 q31 ∷
   rw 10 q32 ∷
   re 10 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 9 q8 ∷
   re 10 5 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q8 ∷
   re 8 3 (CX31 ∷ []) ∷
   re 8 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 7 q4 ∷
   re 8 3 (CK30⁻ ∷ []) ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q4 ∷
   re 12 3 (CX31 ∷ []) ∷
   rw 11 q30 ∷
   rw 10 q33 ∷
   rw 9 q32 ∷
   re 9 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   re 9 5 (CK30⁻ ∷ []) ∷
   re 9 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q8 ∷
   re 7 3 (CX31 ∷ []) ∷
   re 7 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 6 q4 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q4 ∷
   re 11 3 (CX31 ∷ []) ∷
   rw 10 q30 ∷
   rw 9 q34 ∷
   rw 8 q32 ∷
   re 8 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 7 q8 ∷
   re 8 5 (CS03⁻ ∷ []) ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q8 ∷
   re 6 3 (CX31 ∷ []) ∷
   rw 7 q35 ∷
   re 12 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 11 q4 ∷
   re 12 3 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q4 ∷
   re 16 3 (CX31 ∷ []) ∷
   rw 15 q30 ∷
   rw 14 q31 ∷
   rw 13 q32 ∷
   re 13 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 12 q8 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q8 ∷
   re 11 3 (CX31 ∷ []) ∷
   re 11 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 10 q4 ∷
   re 11 3 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q4 ∷
   re 15 3 (CX31 ∷ []) ∷
   rw 14 q30 ∷
   rw 13 q31 ∷
   rw 12 q32 ∷
   re 12 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 11 q8 ∷
   re 12 5 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q8 ∷
   re 10 3 (CX31 ∷ []) ∷
   re 10 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 9 q4 ∷
   re 10 3 (CK30⁻ ∷ []) ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q4 ∷
   re 14 3 (CX31 ∷ []) ∷
   rw 13 q30 ∷
   rw 12 q33 ∷
   rw 11 q32 ∷
   re 11 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 10 q8 ∷
   re 11 5 (CK30⁻ ∷ []) ∷
   re 11 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q8 ∷
   re 9 3 (CX31 ∷ []) ∷
   re 9 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q4 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q4 ∷
   re 13 3 (CX31 ∷ []) ∷
   rw 12 q30 ∷
   rw 11 q34 ∷
   rw 10 q32 ∷
   re 10 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 9 q8 ∷
   re 10 5 (CS03⁻ ∷ []) ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q8 ∷
   re 8 3 (CX31 ∷ []) ∷
   rw 9 q36 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = wE 652 W

-- pass [TOFF123] [X2 TOFF123 X2]: 1 steps
lem-pass-TOFF123-vs-X2-TOFF123-X2 : ⟪ (Toff123 ∷ X2 ∷ Toff123 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff123 ∷ X2 ∷ Toff123 ∷ []) ⟫ʷ
lem-pass-TOFF123-vs-X2-TOFF123-X2 = derive (Toff123 ∷ X2 ∷ Toff123 ∷ X2 ∷ []) (X2 ∷ Toff123 ∷ X2 ∷ Toff123 ∷ [])
  (rw 0 q37 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = wE 653 W

-- groups [CX21] [X2 TOFF123 X2]: 1 steps
lem-groups-CX21-vs-X2-TOFF123-X2 : ⟪ (CX21 ∷ X2 ∷ Toff123 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff123 ∷ X2 ∷ CX21 ∷ []) ⟫ʷ
lem-groups-CX21-vs-X2-TOFF123-X2 = derive (CX21 ∷ X2 ∷ Toff123 ∷ X2 ∷ []) (X2 ∷ Toff123 ∷ X2 ∷ CX21 ∷ [])
  (rw 0 q38 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = wE 654 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 CK21 X2]: 1 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK21-X2 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK21-X2 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 0 q39 ∷ []) Eq.refl

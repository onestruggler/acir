{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D226 (W : Ws) where

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
  q1 = eqn (CS13 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ []) (wn 629 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q3 : Eqn
  q3 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q5 : Eqn
  q5 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q6 : Eqn
  q6 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q7 : Eqn
  q7 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q8 : Eqn
  q8 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q9 : Eqn
  q9 = eqn (Sw12 ∷ CX31 ∷ []) (CX32 ∷ Sw12 ∷ []) (wn 113 W)
  q10 : Eqn
  q10 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q11 : Eqn
  q11 = eqn (Sw12 ∷ CX32 ∷ []) (CX31 ∷ Sw12 ∷ []) (wn 114 W)
  q12 : Eqn
  q12 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q13 : Eqn
  q13 = eqn (X2 ∷ S3 ∷ []) (S3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (S))
  q14 : Eqn
  q14 = eqn (CX21 ∷ S3 ∷ []) (S3 ∷ CX21 ∷ []) (low₃-comm ((CX₁₀ ↑)) (S))
  q15 : Eqn
  q15 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q16 : Eqn
  q16 = eqn (CK31 ∷ X2 ∷ []) (X2 ∷ CK31 ∷ []) (wn 630 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q18 : Eqn
  q18 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q19 : Eqn
  q19 = eqn (CX23 ∷ X2 ∷ CX21 ∷ X2 ∷ []) (X2 ∷ CX21 ∷ X2 ∷ CX23 ∷ []) (wn 673 W)
  q20 : Eqn
  q20 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X2 ∷ CX21 ∷ X2 ∷ []) (X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (wn 557 W)
  q21 : Eqn
  q21 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q22 : Eqn
  q22 = eqn (CK10⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap))
  q23 : Eqn
  q23 = eqn (S1⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (Swap))
  q24 : Eqn
  q24 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (wn 558 W)
  q25 : Eqn
  q25 = eqn (CS01⁻ ∷ CX23 ∷ []) (CX23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₀₁))
  q26 : Eqn
  q26 = eqn (S1⁻ ∷ CX23 ∷ []) (CX23 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (CX₀₁))
  q27 : Eqn
  q27 = eqn (CK10⁻ ∷ CX23 ∷ []) (CX23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₀₁))
  q28 : Eqn
  q28 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q29 : Eqn
  q29 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (wn 559 W)
  q30 : Eqn
  q30 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)

-- Bar(SSSKSS;2,3->0) passes white iX via V2 conjugates 1 part8: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part8 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ X2 ∷ Sw01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part8 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ X2 ∷ Sw01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ [])
  (re 59 3 (CS13 ∷ []) ∷
   rw 59 q1 ∷
   rw 58 q2 ∷
   re 60 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 59 q3 ∷
   rw 60 q4 ∷
   rw 61 q3 ∷
   re 59 3 (CS03 ∷ []) ∷
   rw 60 q5 ∷
   rw 57 q6 ∷
   rw⁻ 56 q2 ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 57 q3 ∷
   rw 56 q7 ∷
   rw⁻ 55 q3 ∷
   re 56 3 (CS13 ∷ []) ∷
   rw 56 q1 ∷
   rw 55 q2 ∷
   re 57 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 56 q3 ∷
   rw 57 q4 ∷
   rw 58 q3 ∷
   re 56 3 (CS03 ∷ []) ∷
   rw 57 q5 ∷
   re 56 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 62 q8 ∷
   re 60 3 (CX31 ∷ []) ∷
   rw 59 q9 ∷
   rw 58 q10 ∷
   rw 57 q11 ∷
   re 57 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 56 q12 ∷
   re 57 5 (CS03 ∷ []) ∷
   rw 59 q6 ∷
   rw⁻ 58 q2 ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 59 q3 ∷
   rw 58 q7 ∷
   rw⁻ 57 q3 ∷
   re 58 3 (CS13 ∷ []) ∷
   rw 58 q1 ∷
   rw 57 q2 ∷
   re 59 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 58 q3 ∷
   rw 59 q4 ∷
   rw 60 q3 ∷
   re 58 3 (CS03 ∷ []) ∷
   rw 59 q5 ∷
   rw 56 q6 ∷
   rw⁻ 55 q2 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 56 q3 ∷
   rw 55 q7 ∷
   rw⁻ 54 q3 ∷
   re 55 3 (CS13 ∷ []) ∷
   rw 55 q1 ∷
   rw 54 q2 ∷
   re 56 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 55 q3 ∷
   rw 56 q4 ∷
   rw 57 q3 ∷
   re 55 3 (CS03 ∷ []) ∷
   rw 56 q5 ∷
   re 55 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 61 q8 ∷
   re 59 3 (CX31 ∷ []) ∷
   rw 58 q9 ∷
   rw 57 q10 ∷
   rw 56 q11 ∷
   re 56 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 55 q12 ∷
   re 56 5 (CS03 ∷ []) ∷
   rw 58 q6 ∷
   rw⁻ 57 q2 ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 58 q3 ∷
   rw 57 q7 ∷
   rw⁻ 56 q3 ∷
   re 57 3 (CS13 ∷ []) ∷
   rw 57 q1 ∷
   rw 56 q2 ∷
   re 58 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 57 q3 ∷
   rw 58 q4 ∷
   rw 59 q3 ∷
   re 57 3 (CS03 ∷ []) ∷
   rw 58 q5 ∷
   rw⁻ 53 q13 ∷
   rw⁻ 54 q14 ∷
   rw⁻ 55 q13 ∷
   rw 54 q6 ∷
   rw⁻ 53 q2 ∷
   re 52 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 54 q3 ∷
   rw 53 q15 ∷
   rw⁻ 52 q3 ∷
   re 53 3 (CK31 ∷ []) ∷
   rw 53 q16 ∷
   rw 52 q2 ∷
   re 54 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 53 q3 ∷
   rw 54 q17 ∷
   rw 55 q3 ∷
   re 53 3 (CK30 ∷ []) ∷
   rw 54 q5 ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q8 ∷
   re 57 3 (CX31 ∷ []) ∷
   rw 56 q9 ∷
   rw 55 q18 ∷
   rw 54 q11 ∷
   re 54 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 53 q12 ∷
   re 54 5 (CK30 ∷ []) ∷
   rw 56 q6 ∷
   rw⁻ 55 q2 ∷
   re 54 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 56 q3 ∷
   rw 55 q15 ∷
   rw⁻ 54 q3 ∷
   re 55 3 (CK31 ∷ []) ∷
   rw 55 q16 ∷
   rw 54 q2 ∷
   re 56 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 55 q3 ∷
   rw 56 q17 ∷
   rw 57 q3 ∷
   re 55 3 (CK30 ∷ []) ∷
   rw 56 q5 ∷
   rw 53 q6 ∷
   rw⁻ 52 q2 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q3 ∷
   rw 52 q7 ∷
   rw⁻ 51 q3 ∷
   re 52 3 (CS13 ∷ []) ∷
   rw 52 q1 ∷
   rw 51 q2 ∷
   re 53 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 52 q3 ∷
   rw 53 q4 ∷
   rw 54 q3 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw 53 q5 ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q8 ∷
   re 56 3 (CX31 ∷ []) ∷
   rw 55 q9 ∷
   rw 54 q10 ∷
   rw 53 q11 ∷
   re 53 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 52 q12 ∷
   re 53 5 (CS03 ∷ []) ∷
   rw 55 q6 ∷
   rw⁻ 54 q2 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 55 q3 ∷
   rw 54 q7 ∷
   rw⁻ 53 q3 ∷
   re 54 3 (CS13 ∷ []) ∷
   rw 54 q1 ∷
   rw 53 q2 ∷
   re 55 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 54 q3 ∷
   rw 55 q4 ∷
   rw 56 q3 ∷
   re 54 3 (CS03 ∷ []) ∷
   rw 55 q5 ∷
   rw 52 q6 ∷
   rw⁻ 51 q2 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q3 ∷
   rw 51 q7 ∷
   rw⁻ 50 q3 ∷
   re 51 3 (CS13 ∷ []) ∷
   rw 51 q1 ∷
   rw 50 q2 ∷
   re 52 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 51 q3 ∷
   rw 52 q4 ∷
   rw 53 q3 ∷
   re 51 3 (CS03 ∷ []) ∷
   rw 52 q5 ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 57 q8 ∷
   re 55 3 (CX31 ∷ []) ∷
   rw 54 q9 ∷
   rw 53 q10 ∷
   rw 52 q11 ∷
   re 52 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 51 q12 ∷
   re 52 5 (CS03 ∷ []) ∷
   rw 54 q6 ∷
   rw⁻ 53 q2 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 54 q3 ∷
   rw 53 q7 ∷
   rw⁻ 52 q3 ∷
   re 53 3 (CS13 ∷ []) ∷
   rw 53 q1 ∷
   rw 52 q2 ∷
   re 54 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 53 q3 ∷
   rw 54 q4 ∷
   rw 55 q3 ∷
   re 53 3 (CS03 ∷ []) ∷
   rw 54 q5 ∷
   rw 51 q6 ∷
   rw⁻ 50 q2 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q3 ∷
   rw 50 q7 ∷
   rw⁻ 49 q3 ∷
   re 50 3 (CS13 ∷ []) ∷
   rw 50 q1 ∷
   rw 49 q2 ∷
   re 51 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 50 q3 ∷
   rw 51 q4 ∷
   rw 52 q3 ∷
   re 50 3 (CS03 ∷ []) ∷
   rw 51 q5 ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q8 ∷
   re 54 3 (CX31 ∷ []) ∷
   rw 53 q9 ∷
   rw 52 q10 ∷
   rw 51 q11 ∷
   re 51 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 50 q12 ∷
   re 51 5 (CS03 ∷ []) ∷
   rw 53 q6 ∷
   rw⁻ 52 q2 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q3 ∷
   rw 52 q7 ∷
   rw⁻ 51 q3 ∷
   re 52 3 (CS13 ∷ []) ∷
   rw 52 q1 ∷
   rw 51 q2 ∷
   re 53 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 52 q3 ∷
   rw 53 q4 ∷
   rw 54 q3 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw 53 q5 ∷
   rw 50 q6 ∷
   rw⁻ 49 q2 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q3 ∷
   rw 49 q7 ∷
   rw⁻ 48 q3 ∷
   re 49 3 (CS13 ∷ []) ∷
   rw 49 q1 ∷
   rw 48 q2 ∷
   re 50 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 49 q3 ∷
   rw 50 q4 ∷
   rw 51 q3 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 50 q5 ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q8 ∷
   re 53 3 (CX31 ∷ []) ∷
   rw 52 q9 ∷
   rw 51 q10 ∷
   rw 50 q11 ∷
   re 50 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 49 q12 ∷
   re 50 5 (CS03 ∷ []) ∷
   rw 52 q6 ∷
   rw⁻ 51 q2 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q3 ∷
   rw 51 q7 ∷
   rw⁻ 50 q3 ∷
   re 51 3 (CS13 ∷ []) ∷
   rw 51 q1 ∷
   rw 50 q2 ∷
   re 52 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 51 q3 ∷
   rw 52 q4 ∷
   rw 53 q3 ∷
   re 51 3 (CS03 ∷ []) ∷
   rw 52 q5 ∷
   rw 49 q6 ∷
   rw⁻ 48 q2 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q3 ∷
   rw 48 q7 ∷
   rw⁻ 47 q3 ∷
   re 48 3 (CS13 ∷ []) ∷
   rw 48 q1 ∷
   rw 47 q2 ∷
   re 49 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 48 q3 ∷
   rw 49 q4 ∷
   rw 50 q3 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 49 q5 ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q8 ∷
   re 52 3 (CX31 ∷ []) ∷
   rw 51 q9 ∷
   rw 50 q10 ∷
   rw 49 q11 ∷
   re 49 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 48 q12 ∷
   re 49 5 (CS03 ∷ []) ∷
   rw 51 q6 ∷
   rw⁻ 50 q2 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q3 ∷
   rw 50 q7 ∷
   rw⁻ 49 q3 ∷
   re 50 3 (CS13 ∷ []) ∷
   rw 50 q1 ∷
   rw 49 q2 ∷
   re 51 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 50 q3 ∷
   rw 51 q4 ∷
   rw 52 q3 ∷
   re 50 3 (CS03 ∷ []) ∷
   rw 51 q5 ∷
   rw 48 q6 ∷
   rw⁻ 47 q2 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q3 ∷
   rw 47 q7 ∷
   rw⁻ 46 q3 ∷
   re 47 3 (CS13 ∷ []) ∷
   rw 47 q1 ∷
   rw 46 q2 ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q3 ∷
   rw 48 q4 ∷
   rw 49 q3 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 48 q5 ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q8 ∷
   re 51 3 (CX31 ∷ []) ∷
   rw 50 q9 ∷
   rw 49 q10 ∷
   rw 48 q11 ∷
   re 48 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 47 q12 ∷
   re 48 5 (CS03 ∷ []) ∷
   rw 50 q6 ∷
   rw⁻ 49 q2 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q3 ∷
   rw 49 q7 ∷
   rw⁻ 48 q3 ∷
   re 49 3 (CS13 ∷ []) ∷
   rw 49 q1 ∷
   rw 48 q2 ∷
   re 50 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 49 q3 ∷
   rw 50 q4 ∷
   rw 51 q3 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 50 q5 ∷
   rw 45 q19 ∷
   rw 39 q20 ∷
   rw 84 q8 ∷
   rw 83 q21 ∷
   rw 82 q21 ∷
   rw 81 q21 ∷
   rw 80 q22 ∷
   rw 79 q23 ∷
   rw 78 q21 ∷
   rw 77 q21 ∷
   rw 76 q21 ∷
   rw 75 q21 ∷
   rw 74 q21 ∷
   rw 73 q21 ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q12 ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 73 q12 ∷
   re 70 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 72 q12 ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 71 q12 ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 70 q12 ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 69 q12 ∷
   rw 68 q24 ∷
   rw⁻ 67 q21 ∷
   rw⁻ 68 q21 ∷
   rw⁻ 69 q21 ∷
   rw⁻ 70 q21 ∷
   rw⁻ 71 q21 ∷
   rw⁻ 72 q21 ∷
   rw⁻ 73 q23 ∷
   rw⁻ 74 q22 ∷
   rw⁻ 75 q21 ∷
   rw⁻ 76 q21 ∷
   rw⁻ 77 q21 ∷
   rw 80 q8 ∷
   re 78 3 (CS03 ∷ []) ∷
   rw 81 q8 ∷
   re 79 3 (CS03 ∷ []) ∷
   rw 82 q8 ∷
   re 80 3 (CS03 ∷ []) ∷
   rw 83 q8 ∷
   re 81 3 (CK30 ∷ []) ∷
   rw 84 q8 ∷
   re 82 3 (CS03 ∷ []) ∷
   rw 85 q8 ∷
   re 83 3 (CS03 ∷ []) ∷
   rw 84 q12 ∷
   rw⁻ 66 q25 ∷
   rw⁻ 67 q25 ∷
   rw⁻ 68 q25 ∷
   rw⁻ 69 q25 ∷
   rw⁻ 70 q25 ∷
   rw⁻ 71 q25 ∷
   rw⁻ 72 q26 ∷
   rw⁻ 73 q27 ∷
   rw⁻ 74 q25 ∷
   rw⁻ 75 q25 ∷
   rw⁻ 76 q25 ∷
   rw 77 q8 ∷
   rw 76 q21 ∷
   rw 75 q21 ∷
   rw 74 q21 ∷
   rw 73 q22 ∷
   rw 72 q23 ∷
   rw 71 q21 ∷
   rw 70 q21 ∷
   rw 69 q21 ∷
   rw 68 q21 ∷
   rw 67 q21 ∷
   rw 66 q21 ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q12 ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 66 q12 ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 65 q12 ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 64 q12 ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 63 q12 ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 62 q12 ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 61 q12 ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q12 ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q12 ∷
   rw 56 q28 ∷
   re 55 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 57 q12 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q12 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 55 q12 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 54 q12 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q12 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q12 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q12 ∷
   rw 50 q29 ∷
   rw⁻ 49 q21 ∷
   rw⁻ 50 q21 ∷
   rw⁻ 51 q21 ∷
   rw⁻ 52 q21 ∷
   rw⁻ 53 q21 ∷
   rw⁻ 54 q21 ∷
   rw⁻ 55 q23 ∷
   rw⁻ 56 q22 ∷
   rw⁻ 57 q21 ∷
   rw⁻ 58 q21 ∷
   rw⁻ 59 q21 ∷
   rw 62 q8 ∷
   re 60 3 (CS03 ∷ []) ∷
   rw 63 q8 ∷
   re 61 3 (CS03 ∷ []) ∷
   rw 64 q8 ∷
   re 62 3 (CS03 ∷ []) ∷
   rw 65 q8 ∷
   re 63 3 (CS03 ∷ []) ∷
   rw 66 q8 ∷
   re 64 3 (CS03 ∷ []) ∷
   rw 67 q8 ∷
   re 65 3 (CS03 ∷ []) ∷
   rw 68 q8 ∷
   re 66 3 (CK30 ∷ []) ∷
   rw 67 q30 ∷
   rw 70 q8 ∷
   re 68 3 (CS03 ∷ []) ∷
   rw 71 q8 ∷ []) Eq.refl

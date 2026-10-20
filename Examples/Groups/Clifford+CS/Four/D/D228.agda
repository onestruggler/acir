{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D228 (W : Ws) where

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
  q2 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q3 : Eqn
  q3 = eqn (CS13 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ []) (wn 629 W)
  q4 : Eqn
  q4 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q6 : Eqn
  q6 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q7 : Eqn
  q7 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q8 : Eqn
  q8 = eqn (Sw12 ∷ CX31 ∷ []) (CX32 ∷ Sw12 ∷ []) (wn 113 W)
  q9 : Eqn
  q9 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q10 : Eqn
  q10 = eqn (Sw12 ∷ CX32 ∷ []) (CX31 ∷ Sw12 ∷ []) (wn 114 W)
  q11 : Eqn
  q11 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q12 : Eqn
  q12 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
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
  q21 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q22 : Eqn
  q22 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q23 : Eqn
  q23 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q24 : Eqn
  q24 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))

-- Bar(SSSKSS;2,3->0) passes white iX via V2 conjugates 1 part10: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part10 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ CX21 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ Sw01 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part10 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ CX21 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ Sw01 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ [])
  (rw⁻ 72 q1 ∷
   rw 71 q2 ∷
   rw⁻ 70 q1 ∷
   re 71 3 (CS13 ∷ []) ∷
   rw 71 q3 ∷
   rw 70 q4 ∷
   re 72 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 71 q1 ∷
   rw 72 q5 ∷
   rw 73 q1 ∷
   re 71 3 (CS03 ∷ []) ∷
   rw 72 q6 ∷
   re 71 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 77 q7 ∷
   re 75 3 (CX31 ∷ []) ∷
   rw 74 q8 ∷
   rw 73 q9 ∷
   rw 72 q10 ∷
   re 72 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 71 q11 ∷
   re 72 5 (CS03 ∷ []) ∷
   rw 74 q12 ∷
   rw⁻ 73 q4 ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 74 q1 ∷
   rw 73 q2 ∷
   rw⁻ 72 q1 ∷
   re 73 3 (CS13 ∷ []) ∷
   rw 73 q3 ∷
   rw 72 q4 ∷
   re 74 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 73 q1 ∷
   rw 74 q5 ∷
   rw 75 q1 ∷
   re 73 3 (CS03 ∷ []) ∷
   rw 74 q6 ∷
   rw 71 q12 ∷
   rw⁻ 70 q4 ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 71 q1 ∷
   rw 70 q2 ∷
   rw⁻ 69 q1 ∷
   re 70 3 (CS13 ∷ []) ∷
   rw 70 q3 ∷
   rw 69 q4 ∷
   re 71 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 70 q1 ∷
   rw 71 q5 ∷
   rw 72 q1 ∷
   re 70 3 (CS03 ∷ []) ∷
   rw 71 q6 ∷
   re 70 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 76 q7 ∷
   re 74 3 (CX31 ∷ []) ∷
   rw 73 q8 ∷
   rw 72 q9 ∷
   rw 71 q10 ∷
   re 71 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 70 q11 ∷
   re 71 5 (CS03 ∷ []) ∷
   rw 73 q12 ∷
   rw⁻ 72 q4 ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 73 q1 ∷
   rw 72 q2 ∷
   rw⁻ 71 q1 ∷
   re 72 3 (CS13 ∷ []) ∷
   rw 72 q3 ∷
   rw 71 q4 ∷
   re 73 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 72 q1 ∷
   rw 73 q5 ∷
   rw 74 q1 ∷
   re 72 3 (CS03 ∷ []) ∷
   rw 73 q6 ∷
   rw 70 q12 ∷
   rw⁻ 69 q4 ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 70 q1 ∷
   rw 69 q2 ∷
   rw⁻ 68 q1 ∷
   re 69 3 (CS13 ∷ []) ∷
   rw 69 q3 ∷
   rw 68 q4 ∷
   re 70 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 69 q1 ∷
   rw 70 q5 ∷
   rw 71 q1 ∷
   re 69 3 (CS03 ∷ []) ∷
   rw 70 q6 ∷
   re 69 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 75 q7 ∷
   re 73 3 (CX31 ∷ []) ∷
   rw 72 q8 ∷
   rw 71 q9 ∷
   rw 70 q10 ∷
   re 70 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 69 q11 ∷
   re 70 5 (CS03 ∷ []) ∷
   rw 72 q12 ∷
   rw⁻ 71 q4 ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 72 q1 ∷
   rw 71 q2 ∷
   rw⁻ 70 q1 ∷
   re 71 3 (CS13 ∷ []) ∷
   rw 71 q3 ∷
   rw 70 q4 ∷
   re 72 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 71 q1 ∷
   rw 72 q5 ∷
   rw 73 q1 ∷
   re 71 3 (CS03 ∷ []) ∷
   rw 72 q6 ∷
   rw⁻ 67 q13 ∷
   rw⁻ 68 q14 ∷
   rw⁻ 69 q13 ∷
   rw 68 q12 ∷
   rw⁻ 67 q4 ∷
   re 66 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 68 q1 ∷
   rw 67 q15 ∷
   rw⁻ 66 q1 ∷
   re 67 3 (CK31 ∷ []) ∷
   rw 67 q16 ∷
   rw 66 q4 ∷
   re 68 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 67 q1 ∷
   rw 68 q17 ∷
   rw 69 q1 ∷
   re 67 3 (CK30 ∷ []) ∷
   rw 68 q6 ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q7 ∷
   re 71 3 (CX31 ∷ []) ∷
   rw 70 q8 ∷
   rw 69 q18 ∷
   rw 68 q10 ∷
   re 68 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 67 q11 ∷
   re 68 5 (CK30 ∷ []) ∷
   rw 70 q12 ∷
   rw⁻ 69 q4 ∷
   re 68 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 70 q1 ∷
   rw 69 q15 ∷
   rw⁻ 68 q1 ∷
   re 69 3 (CK31 ∷ []) ∷
   rw 69 q16 ∷
   rw 68 q4 ∷
   re 70 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 69 q1 ∷
   rw 70 q17 ∷
   rw 71 q1 ∷
   re 69 3 (CK30 ∷ []) ∷
   rw 70 q6 ∷
   rw 67 q12 ∷
   rw⁻ 66 q4 ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 67 q1 ∷
   rw 66 q2 ∷
   rw⁻ 65 q1 ∷
   re 66 3 (CS13 ∷ []) ∷
   rw 66 q3 ∷
   rw 65 q4 ∷
   re 67 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 66 q1 ∷
   rw 67 q5 ∷
   rw 68 q1 ∷
   re 66 3 (CS03 ∷ []) ∷
   rw 67 q6 ∷
   re 66 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 72 q7 ∷
   re 70 3 (CX31 ∷ []) ∷
   rw 69 q8 ∷
   rw 68 q9 ∷
   rw 67 q10 ∷
   re 67 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 66 q11 ∷
   re 67 5 (CS03 ∷ []) ∷
   rw 69 q12 ∷
   rw⁻ 68 q4 ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 69 q1 ∷
   rw 68 q2 ∷
   rw⁻ 67 q1 ∷
   re 68 3 (CS13 ∷ []) ∷
   rw 68 q3 ∷
   rw 67 q4 ∷
   re 69 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 68 q1 ∷
   rw 69 q5 ∷
   rw 70 q1 ∷
   re 68 3 (CS03 ∷ []) ∷
   rw 69 q6 ∷
   rw 66 q12 ∷
   rw⁻ 65 q4 ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 66 q1 ∷
   rw 65 q2 ∷
   rw⁻ 64 q1 ∷
   re 65 3 (CS13 ∷ []) ∷
   rw 65 q3 ∷
   rw 64 q4 ∷
   re 66 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 65 q1 ∷
   rw 66 q5 ∷
   rw 67 q1 ∷
   re 65 3 (CS03 ∷ []) ∷
   rw 66 q6 ∷
   re 65 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q7 ∷
   re 69 3 (CX31 ∷ []) ∷
   rw 68 q8 ∷
   rw 67 q9 ∷
   rw 66 q10 ∷
   re 66 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 65 q11 ∷
   re 66 5 (CS03 ∷ []) ∷
   rw 68 q12 ∷
   rw⁻ 67 q4 ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 68 q1 ∷
   rw 67 q2 ∷
   rw⁻ 66 q1 ∷
   re 67 3 (CS13 ∷ []) ∷
   rw 67 q3 ∷
   rw 66 q4 ∷
   re 68 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 67 q1 ∷
   rw 68 q5 ∷
   rw 69 q1 ∷
   re 67 3 (CS03 ∷ []) ∷
   rw 68 q6 ∷
   rw 65 q12 ∷
   rw⁻ 64 q4 ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 65 q1 ∷
   rw 64 q2 ∷
   rw⁻ 63 q1 ∷
   re 64 3 (CS13 ∷ []) ∷
   rw 64 q3 ∷
   rw 63 q4 ∷
   re 65 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 64 q1 ∷
   rw 65 q5 ∷
   rw 66 q1 ∷
   re 64 3 (CS03 ∷ []) ∷
   rw 65 q6 ∷
   re 64 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 70 q7 ∷
   re 68 3 (CX31 ∷ []) ∷
   rw 67 q8 ∷
   rw 66 q9 ∷
   rw 65 q10 ∷
   re 65 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 64 q11 ∷
   re 65 5 (CS03 ∷ []) ∷
   rw 67 q12 ∷
   rw⁻ 66 q4 ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 67 q1 ∷
   rw 66 q2 ∷
   rw⁻ 65 q1 ∷
   re 66 3 (CS13 ∷ []) ∷
   rw 66 q3 ∷
   rw 65 q4 ∷
   re 67 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 66 q1 ∷
   rw 67 q5 ∷
   rw 68 q1 ∷
   re 66 3 (CS03 ∷ []) ∷
   rw 67 q6 ∷
   rw 64 q12 ∷
   rw⁻ 63 q4 ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 64 q1 ∷
   rw 63 q2 ∷
   rw⁻ 62 q1 ∷
   re 63 3 (CS13 ∷ []) ∷
   rw 63 q3 ∷
   rw 62 q4 ∷
   re 64 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 63 q1 ∷
   rw 64 q5 ∷
   rw 65 q1 ∷
   re 63 3 (CS03 ∷ []) ∷
   rw 64 q6 ∷
   re 63 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 69 q7 ∷
   re 67 3 (CX31 ∷ []) ∷
   rw 66 q8 ∷
   rw 65 q9 ∷
   rw 64 q10 ∷
   re 64 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 63 q11 ∷
   re 64 5 (CS03 ∷ []) ∷
   rw 66 q12 ∷
   rw⁻ 65 q4 ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 66 q1 ∷
   rw 65 q2 ∷
   rw⁻ 64 q1 ∷
   re 65 3 (CS13 ∷ []) ∷
   rw 65 q3 ∷
   rw 64 q4 ∷
   re 66 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 65 q1 ∷
   rw 66 q5 ∷
   rw 67 q1 ∷
   re 65 3 (CS03 ∷ []) ∷
   rw 66 q6 ∷
   rw 63 q12 ∷
   rw⁻ 62 q4 ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 63 q1 ∷
   rw 62 q2 ∷
   rw⁻ 61 q1 ∷
   re 62 3 (CS13 ∷ []) ∷
   rw 62 q3 ∷
   rw 61 q4 ∷
   re 63 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 62 q1 ∷
   rw 63 q5 ∷
   rw 64 q1 ∷
   re 62 3 (CS03 ∷ []) ∷
   rw 63 q6 ∷
   re 62 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 68 q7 ∷
   re 66 3 (CX31 ∷ []) ∷
   rw 65 q8 ∷
   rw 64 q9 ∷
   rw 63 q10 ∷
   re 63 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 62 q11 ∷
   re 63 5 (CS03 ∷ []) ∷
   rw 65 q12 ∷
   rw⁻ 64 q4 ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 65 q1 ∷
   rw 64 q2 ∷
   rw⁻ 63 q1 ∷
   re 64 3 (CS13 ∷ []) ∷
   rw 64 q3 ∷
   rw 63 q4 ∷
   re 65 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 64 q1 ∷
   rw 65 q5 ∷
   rw 66 q1 ∷
   re 64 3 (CS03 ∷ []) ∷
   rw 65 q6 ∷
   rw 62 q12 ∷
   rw⁻ 61 q4 ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 62 q1 ∷
   rw 61 q2 ∷
   rw⁻ 60 q1 ∷
   re 61 3 (CS13 ∷ []) ∷
   rw 61 q3 ∷
   rw 60 q4 ∷
   re 62 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 61 q1 ∷
   rw 62 q5 ∷
   rw 63 q1 ∷
   re 61 3 (CS03 ∷ []) ∷
   rw 62 q6 ∷
   re 61 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 67 q7 ∷
   re 65 3 (CX31 ∷ []) ∷
   rw 64 q8 ∷
   rw 63 q9 ∷
   rw 62 q10 ∷
   re 62 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 61 q11 ∷
   re 62 5 (CS03 ∷ []) ∷
   rw 64 q12 ∷
   rw⁻ 63 q4 ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 64 q1 ∷
   rw 63 q2 ∷
   rw⁻ 62 q1 ∷
   re 63 3 (CS13 ∷ []) ∷
   rw 63 q3 ∷
   rw 62 q4 ∷
   re 64 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 63 q1 ∷
   rw 64 q5 ∷
   rw 65 q1 ∷
   re 63 3 (CS03 ∷ []) ∷
   rw 64 q6 ∷
   rw 59 q19 ∷
   rw 53 q20 ∷
   rw 93 q12 ∷
   rw⁻ 92 q4 ∷
   rw 91 q21 ∷
   rw 90 q21 ∷
   rw 89 q22 ∷
   rw 88 q21 ∷
   rw⁻ 87 q4 ∷
   re 86 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 88 q1 ∷
   rw 87 q2 ∷
   rw⁻ 86 q1 ∷
   re 87 3 (CS13 ∷ []) ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 87 q1 ∷
   rw 86 q2 ∷
   rw⁻ 85 q1 ∷
   re 86 3 (CS13 ∷ []) ∷
   re 84 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 86 q1 ∷
   rw 85 q15 ∷
   rw⁻ 84 q1 ∷
   re 85 3 (CK31 ∷ []) ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 85 q1 ∷
   rw 84 q2 ∷
   rw⁻ 83 q1 ∷
   re 84 3 (CS13 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 84 q1 ∷
   rw 83 q2 ∷
   rw⁻ 82 q1 ∷
   re 83 3 (CS13 ∷ []) ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 83 q1 ∷
   rw 82 q2 ∷
   rw⁻ 81 q1 ∷
   re 82 3 (CS13 ∷ []) ∷
   rw⁻ 80 q23 ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 81 q1 ∷
   rw 80 q2 ∷
   rw⁻ 79 q1 ∷
   re 80 3 (CS13 ∷ []) ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 80 q1 ∷
   rw 79 q2 ∷
   rw⁻ 78 q1 ∷
   re 79 3 (CS13 ∷ []) ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 79 q1 ∷
   rw 78 q2 ∷
   rw⁻ 77 q1 ∷
   re 78 3 (CS13 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 78 q1 ∷
   rw 77 q2 ∷
   rw⁻ 76 q1 ∷
   re 77 3 (CS13 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 77 q1 ∷
   rw 76 q2 ∷
   rw⁻ 75 q1 ∷
   re 76 3 (CS13 ∷ []) ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 76 q1 ∷
   rw 75 q2 ∷
   rw⁻ 74 q1 ∷
   re 75 3 (CS13 ∷ []) ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 75 q1 ∷
   rw 74 q2 ∷
   rw⁻ 73 q1 ∷
   re 74 3 (CS13 ∷ []) ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 74 q1 ∷
   rw 73 q2 ∷
   rw⁻ 72 q1 ∷
   re 73 3 (CS13 ∷ []) ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 73 q1 ∷
   rw 72 q2 ∷
   rw⁻ 71 q1 ∷
   re 72 3 (CS13 ∷ []) ∷
   rw⁻ 70 q24 ∷
   re 69 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 71 q1 ∷
   rw 70 q15 ∷
   rw⁻ 69 q1 ∷
   re 70 3 (CK31 ∷ []) ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 70 q1 ∷
   rw 69 q2 ∷
   rw⁻ 68 q1 ∷
   re 69 3 (CS13 ∷ []) ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 69 q1 ∷
   rw 68 q2 ∷
   rw⁻ 67 q1 ∷
   re 68 3 (CS13 ∷ []) ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 68 q1 ∷
   rw 67 q2 ∷
   rw⁻ 66 q1 ∷
   re 67 3 (CS13 ∷ []) ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 67 q1 ∷
   rw 66 q2 ∷
   rw⁻ 65 q1 ∷ []) Eq.refl

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D223 (W : Ws) where

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
  q1 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q2 : Eqn
  q2 = wE 114 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 5 W
  q5 : Eqn
  q5 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = wE 7 W
  q8 : Eqn
  q8 = wE 629 W
  q9 : Eqn
  q9 = wE 27 W
  q10 : Eqn
  q10 = wE 31 W
  q11 : Eqn
  q11 = wE 1 W
  q12 : Eqn
  q12 = wE 113 W
  q13 : Eqn
  q13 = eqn (X2 ∷ S3 ∷ []) (S3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (S))
  q14 : Eqn
  q14 = eqn (CX21 ∷ S3 ∷ []) (S3 ∷ CX21 ∷ []) (low₃-comm ((CX₁₀ ↑)) (S))
  q15 : Eqn
  q15 = wE 140 W
  q16 : Eqn
  q16 = wE 630 W
  q17 : Eqn
  q17 = wE 142 W
  q18 : Eqn
  q18 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q19 : Eqn
  q19 = wE 673 W
  q20 : Eqn
  q20 = wE 557 W
  q21 : Eqn
  q21 = wE 76 W
  q22 : Eqn
  q22 = wE 137 W
  q23 : Eqn
  q23 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q24 : Eqn
  q24 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))

-- Bar(SSSKSS;2,3->0) passes white iX via V2 conjugates 1 part5: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part5 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CX32 ∷ Sw12 ∷ Sw23 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ Sw01 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ Sw01 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part5 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CX32 ∷ Sw12 ∷ Sw23 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ Sw01 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ Sw01 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ [])
  (rw 41 q1 ∷
   rw 40 q2 ∷
   re 40 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 39 q3 ∷
   re 40 5 (CS03 ∷ []) ∷
   rw 42 q4 ∷
   rw⁻ 41 q5 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q6 ∷
   rw 41 q7 ∷
   rw⁻ 40 q6 ∷
   re 41 3 (CS13 ∷ []) ∷
   rw 41 q8 ∷
   rw 40 q5 ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 41 q6 ∷
   rw 42 q9 ∷
   rw 43 q6 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 42 q10 ∷
   rw 39 q4 ∷
   rw⁻ 38 q5 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q6 ∷
   rw 38 q7 ∷
   rw⁻ 37 q6 ∷
   re 38 3 (CS13 ∷ []) ∷
   rw 38 q8 ∷
   rw 37 q5 ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q6 ∷
   rw 39 q9 ∷
   rw 40 q6 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 39 q10 ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q11 ∷
   re 42 3 (CX31 ∷ []) ∷
   rw 41 q12 ∷
   rw 40 q1 ∷
   rw 39 q2 ∷
   re 39 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 38 q3 ∷
   re 39 5 (CS03 ∷ []) ∷
   rw 41 q4 ∷
   rw⁻ 40 q5 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q6 ∷
   rw 40 q7 ∷
   rw⁻ 39 q6 ∷
   re 40 3 (CS13 ∷ []) ∷
   rw 40 q8 ∷
   rw 39 q5 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q6 ∷
   rw 41 q9 ∷
   rw 42 q6 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q10 ∷
   rw 38 q4 ∷
   rw⁻ 37 q5 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q6 ∷
   rw 37 q7 ∷
   rw⁻ 36 q6 ∷
   re 37 3 (CS13 ∷ []) ∷
   rw 37 q8 ∷
   rw 36 q5 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q6 ∷
   rw 38 q9 ∷
   rw 39 q6 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 38 q10 ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q11 ∷
   re 41 3 (CX31 ∷ []) ∷
   rw 40 q12 ∷
   rw 39 q1 ∷
   rw 38 q2 ∷
   re 38 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 37 q3 ∷
   re 38 5 (CS03 ∷ []) ∷
   rw 40 q4 ∷
   rw⁻ 39 q5 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q6 ∷
   rw 39 q7 ∷
   rw⁻ 38 q6 ∷
   re 39 3 (CS13 ∷ []) ∷
   rw 39 q8 ∷
   rw 38 q5 ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q6 ∷
   rw 40 q9 ∷
   rw 41 q6 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 40 q10 ∷
   rw⁻ 35 q13 ∷
   rw⁻ 36 q14 ∷
   rw⁻ 37 q13 ∷
   rw 36 q4 ∷
   rw⁻ 35 q5 ∷
   re 34 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q6 ∷
   rw 35 q15 ∷
   rw⁻ 34 q6 ∷
   re 35 3 (CK31 ∷ []) ∷
   rw 35 q16 ∷
   rw 34 q5 ∷
   re 36 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 35 q6 ∷
   rw 36 q17 ∷
   rw 37 q6 ∷
   re 35 3 (CK30 ∷ []) ∷
   rw 36 q10 ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q11 ∷
   re 39 3 (CX31 ∷ []) ∷
   rw 38 q12 ∷
   rw 37 q18 ∷
   rw 36 q2 ∷
   re 36 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 35 q3 ∷
   re 36 5 (CK30 ∷ []) ∷
   rw 38 q4 ∷
   rw⁻ 37 q5 ∷
   re 36 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q6 ∷
   rw 37 q15 ∷
   rw⁻ 36 q6 ∷
   re 37 3 (CK31 ∷ []) ∷
   rw 37 q16 ∷
   rw 36 q5 ∷
   re 38 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 37 q6 ∷
   rw 38 q17 ∷
   rw 39 q6 ∷
   re 37 3 (CK30 ∷ []) ∷
   rw 38 q10 ∷
   rw 35 q4 ∷
   rw⁻ 34 q5 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q6 ∷
   rw 34 q7 ∷
   rw⁻ 33 q6 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw 34 q8 ∷
   rw 33 q5 ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q6 ∷
   rw 35 q9 ∷
   rw 36 q6 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 35 q10 ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q11 ∷
   re 38 3 (CX31 ∷ []) ∷
   rw 37 q12 ∷
   rw 36 q1 ∷
   rw 35 q2 ∷
   re 35 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 34 q3 ∷
   re 35 5 (CS03 ∷ []) ∷
   rw 37 q4 ∷
   rw⁻ 36 q5 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q6 ∷
   rw 36 q7 ∷
   rw⁻ 35 q6 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 36 q8 ∷
   rw 35 q5 ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q6 ∷
   rw 37 q9 ∷
   rw 38 q6 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q10 ∷
   rw 34 q4 ∷
   rw⁻ 33 q5 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q6 ∷
   rw 33 q7 ∷
   rw⁻ 32 q6 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw 33 q8 ∷
   rw 32 q5 ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q6 ∷
   rw 34 q9 ∷
   rw 35 q6 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 34 q10 ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q11 ∷
   re 37 3 (CX31 ∷ []) ∷
   rw 36 q12 ∷
   rw 35 q1 ∷
   rw 34 q2 ∷
   re 34 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 33 q3 ∷
   re 34 5 (CS03 ∷ []) ∷
   rw 36 q4 ∷
   rw⁻ 35 q5 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q6 ∷
   rw 35 q7 ∷
   rw⁻ 34 q6 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw 35 q8 ∷
   rw 34 q5 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q6 ∷
   rw 36 q9 ∷
   rw 37 q6 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q10 ∷
   rw 33 q4 ∷
   rw⁻ 32 q5 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q6 ∷
   rw 32 q7 ∷
   rw⁻ 31 q6 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw 32 q8 ∷
   rw 31 q5 ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q6 ∷
   rw 33 q9 ∷
   rw 34 q6 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 33 q10 ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q11 ∷
   re 36 3 (CX31 ∷ []) ∷
   rw 35 q12 ∷
   rw 34 q1 ∷
   rw 33 q2 ∷
   re 33 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 32 q3 ∷
   re 33 5 (CS03 ∷ []) ∷
   rw 35 q4 ∷
   rw⁻ 34 q5 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q6 ∷
   rw 34 q7 ∷
   rw⁻ 33 q6 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw 34 q8 ∷
   rw 33 q5 ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q6 ∷
   rw 35 q9 ∷
   rw 36 q6 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 35 q10 ∷
   rw 32 q4 ∷
   rw⁻ 31 q5 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q6 ∷
   rw 31 q7 ∷
   rw⁻ 30 q6 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 31 q8 ∷
   rw 30 q5 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q6 ∷
   rw 32 q9 ∷
   rw 33 q6 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 32 q10 ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q11 ∷
   re 35 3 (CX31 ∷ []) ∷
   rw 34 q12 ∷
   rw 33 q1 ∷
   rw 32 q2 ∷
   re 32 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 31 q3 ∷
   re 32 5 (CS03 ∷ []) ∷
   rw 34 q4 ∷
   rw⁻ 33 q5 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q6 ∷
   rw 33 q7 ∷
   rw⁻ 32 q6 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw 33 q8 ∷
   rw 32 q5 ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q6 ∷
   rw 34 q9 ∷
   rw 35 q6 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 34 q10 ∷
   rw 31 q4 ∷
   rw⁻ 30 q5 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q6 ∷
   rw 30 q7 ∷
   rw⁻ 29 q6 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw 30 q8 ∷
   rw 29 q5 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q6 ∷
   rw 31 q9 ∷
   rw 32 q6 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 31 q10 ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q11 ∷
   re 34 3 (CX31 ∷ []) ∷
   rw 33 q12 ∷
   rw 32 q1 ∷
   rw 31 q2 ∷
   re 31 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 30 q3 ∷
   re 31 5 (CS03 ∷ []) ∷
   rw 33 q4 ∷
   rw⁻ 32 q5 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q6 ∷
   rw 32 q7 ∷
   rw⁻ 31 q6 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw 32 q8 ∷
   rw 31 q5 ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q6 ∷
   rw 33 q9 ∷
   rw 34 q6 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 33 q10 ∷
   rw 30 q4 ∷
   rw⁻ 29 q5 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q6 ∷
   rw 29 q7 ∷
   rw⁻ 28 q6 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 29 q8 ∷
   rw 28 q5 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q6 ∷
   rw 30 q9 ∷
   rw 31 q6 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 30 q10 ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q11 ∷
   re 33 3 (CX31 ∷ []) ∷
   rw 32 q12 ∷
   rw 31 q1 ∷
   rw 30 q2 ∷
   re 30 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 29 q3 ∷
   re 30 5 (CS03 ∷ []) ∷
   rw 32 q4 ∷
   rw⁻ 31 q5 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q6 ∷
   rw 31 q7 ∷
   rw⁻ 30 q6 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 31 q8 ∷
   rw 30 q5 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q6 ∷
   rw 32 q9 ∷
   rw 33 q6 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 32 q10 ∷
   rw 27 q19 ∷
   rw 21 q20 ∷
   rw 61 q4 ∷
   rw⁻ 60 q5 ∷
   rw 59 q21 ∷
   rw 58 q21 ∷
   rw 57 q22 ∷
   rw 56 q21 ∷
   rw⁻ 55 q5 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 56 q6 ∷
   rw 55 q7 ∷
   rw⁻ 54 q6 ∷
   re 55 3 (CS13 ∷ []) ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 55 q6 ∷
   rw 54 q7 ∷
   rw⁻ 53 q6 ∷
   re 54 3 (CS13 ∷ []) ∷
   re 52 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 54 q6 ∷
   rw 53 q15 ∷
   rw⁻ 52 q6 ∷
   re 53 3 (CK31 ∷ []) ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q6 ∷
   rw 52 q7 ∷
   rw⁻ 51 q6 ∷
   re 52 3 (CS13 ∷ []) ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q6 ∷
   rw 51 q7 ∷
   rw⁻ 50 q6 ∷
   re 51 3 (CS13 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q6 ∷
   rw 50 q7 ∷
   rw⁻ 49 q6 ∷
   re 50 3 (CS13 ∷ []) ∷
   rw⁻ 48 q23 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q6 ∷
   rw 48 q7 ∷
   rw⁻ 47 q6 ∷
   re 48 3 (CS13 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q6 ∷
   rw 47 q7 ∷
   rw⁻ 46 q6 ∷
   re 47 3 (CS13 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q6 ∷
   rw 46 q7 ∷
   rw⁻ 45 q6 ∷
   re 46 3 (CS13 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q6 ∷
   rw 45 q7 ∷
   rw⁻ 44 q6 ∷
   re 45 3 (CS13 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q6 ∷
   rw 44 q7 ∷
   rw⁻ 43 q6 ∷
   re 44 3 (CS13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q6 ∷
   rw 43 q7 ∷
   rw⁻ 42 q6 ∷
   re 43 3 (CS13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q6 ∷
   rw 42 q7 ∷
   rw⁻ 41 q6 ∷
   re 42 3 (CS13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q6 ∷
   rw 41 q7 ∷
   rw⁻ 40 q6 ∷
   re 41 3 (CS13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q6 ∷
   rw 40 q7 ∷
   rw⁻ 39 q6 ∷
   re 40 3 (CS13 ∷ []) ∷
   rw⁻ 38 q24 ∷
   re 37 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q6 ∷
   rw 38 q15 ∷
   rw⁻ 37 q6 ∷
   re 38 3 (CK31 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q6 ∷
   rw 37 q7 ∷
   rw⁻ 36 q6 ∷
   re 37 3 (CS13 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q6 ∷
   rw 36 q7 ∷
   rw⁻ 35 q6 ∷
   re 36 3 (CS13 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q6 ∷
   rw 35 q7 ∷
   rw⁻ 34 q6 ∷
   re 35 3 (CS13 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q6 ∷
   rw 34 q7 ∷
   rw⁻ 33 q6 ∷
   re 34 3 (CS13 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q6 ∷
   rw 33 q7 ∷
   rw⁻ 32 q6 ∷
   re 33 3 (CS13 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q6 ∷
   rw 32 q7 ∷
   rw⁻ 31 q6 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw⁻ 30 q23 ∷
   rw 29 q7 ∷
   rw 28 q7 ∷
   rw 27 q15 ∷
   rw 26 q7 ∷ []) Eq.refl

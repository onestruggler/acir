{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D222 (W : Ws) where

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
  q1 = eqn (CS01⁻ ∷ CX23 ∷ []) (CX23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₀₁))
  q2 : Eqn
  q2 = eqn (S1⁻ ∷ CX23 ∷ []) (CX23 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (CX₀₁))
  q3 : Eqn
  q3 = eqn (CK10⁻ ∷ CX23 ∷ []) (CX23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₀₁))
  q4 : Eqn
  q4 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (wn 558 W)
  q5 : Eqn
  q5 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q6 : Eqn
  q6 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q9 : Eqn
  q9 = eqn (CS13 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ []) (wn 629 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q12 : Eqn
  q12 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q13 : Eqn
  q13 = eqn (Sw12 ∷ CX31 ∷ []) (CX32 ∷ Sw12 ∷ []) (wn 113 W)
  q14 : Eqn
  q14 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q15 : Eqn
  q15 = eqn (Sw12 ∷ CX32 ∷ []) (CX31 ∷ Sw12 ∷ []) (wn 114 W)
  q16 : Eqn
  q16 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q17 : Eqn
  q17 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q18 : Eqn
  q18 = eqn (CK31 ∷ X2 ∷ []) (X2 ∷ CK31 ∷ []) (wn 630 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q20 : Eqn
  q20 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q21 : Eqn
  q21 = eqn (CX23 ∷ X2 ∷ CX21 ∷ X2 ∷ []) (X2 ∷ CX21 ∷ X2 ∷ CX23 ∷ []) (wn 673 W)

-- Bar(SSSKSS;2,3->0) passes white iX via V2 conjugates 1 part4: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part4 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CX32 ∷ Sw12 ∷ Sw23 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part4 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CX32 ∷ Sw12 ∷ Sw23 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ [])
  (rw⁻ 16 q1 ∷
   rw⁻ 17 q1 ∷
   rw⁻ 18 q1 ∷
   rw⁻ 19 q1 ∷
   rw⁻ 20 q1 ∷
   rw⁻ 21 q1 ∷
   rw⁻ 22 q2 ∷
   rw⁻ 23 q3 ∷
   rw⁻ 24 q1 ∷
   rw⁻ 25 q1 ∷
   rw⁻ 26 q1 ∷
   rw 10 q4 ∷
   rw 53 q5 ∷
   rw⁻ 52 q6 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q7 ∷
   rw 52 q8 ∷
   rw⁻ 51 q7 ∷
   re 52 3 (CS13 ∷ []) ∷
   rw 52 q9 ∷
   rw 51 q6 ∷
   re 53 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 52 q7 ∷
   rw 53 q10 ∷
   rw 54 q7 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw 53 q11 ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q12 ∷
   re 56 3 (CX31 ∷ []) ∷
   rw 55 q13 ∷
   rw 54 q14 ∷
   rw 53 q15 ∷
   re 53 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 52 q16 ∷
   re 53 5 (CS03 ∷ []) ∷
   rw 55 q5 ∷
   rw⁻ 54 q6 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 55 q7 ∷
   rw 54 q8 ∷
   rw⁻ 53 q7 ∷
   re 54 3 (CS13 ∷ []) ∷
   rw 54 q9 ∷
   rw 53 q6 ∷
   re 55 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 54 q7 ∷
   rw 55 q10 ∷
   rw 56 q7 ∷
   re 54 3 (CS03 ∷ []) ∷
   rw 55 q11 ∷
   rw 52 q5 ∷
   rw⁻ 51 q6 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q7 ∷
   rw 51 q8 ∷
   rw⁻ 50 q7 ∷
   re 51 3 (CS13 ∷ []) ∷
   rw 51 q9 ∷
   rw 50 q6 ∷
   re 52 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 51 q7 ∷
   rw 52 q10 ∷
   rw 53 q7 ∷
   re 51 3 (CS03 ∷ []) ∷
   rw 52 q11 ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 57 q12 ∷
   re 55 3 (CX31 ∷ []) ∷
   rw 54 q13 ∷
   rw 53 q14 ∷
   rw 52 q15 ∷
   re 52 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 51 q16 ∷
   re 52 5 (CS03 ∷ []) ∷
   rw 54 q5 ∷
   rw⁻ 53 q6 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 54 q7 ∷
   rw 53 q8 ∷
   rw⁻ 52 q7 ∷
   re 53 3 (CS13 ∷ []) ∷
   rw 53 q9 ∷
   rw 52 q6 ∷
   re 54 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 53 q7 ∷
   rw 54 q10 ∷
   rw 55 q7 ∷
   re 53 3 (CS03 ∷ []) ∷
   rw 54 q11 ∷
   rw 51 q5 ∷
   rw⁻ 50 q6 ∷
   re 49 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q7 ∷
   rw 50 q17 ∷
   rw⁻ 49 q7 ∷
   re 50 3 (CK31 ∷ []) ∷
   rw 50 q18 ∷
   rw 49 q6 ∷
   re 51 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 50 q7 ∷
   rw 51 q19 ∷
   rw 52 q7 ∷
   re 50 3 (CK30 ∷ []) ∷
   rw 51 q11 ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q12 ∷
   re 54 3 (CX31 ∷ []) ∷
   rw 53 q13 ∷
   rw 52 q20 ∷
   rw 51 q15 ∷
   re 51 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 50 q16 ∷
   re 51 5 (CK30 ∷ []) ∷
   rw 53 q5 ∷
   rw⁻ 52 q6 ∷
   re 51 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q7 ∷
   rw 52 q17 ∷
   rw⁻ 51 q7 ∷
   re 52 3 (CK31 ∷ []) ∷
   rw 52 q18 ∷
   rw 51 q6 ∷
   re 53 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 52 q7 ∷
   rw 53 q19 ∷
   rw 54 q7 ∷
   re 52 3 (CK30 ∷ []) ∷
   rw 53 q11 ∷
   rw 50 q5 ∷
   rw⁻ 49 q6 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q7 ∷
   rw 49 q8 ∷
   rw⁻ 48 q7 ∷
   re 49 3 (CS13 ∷ []) ∷
   rw 49 q9 ∷
   rw 48 q6 ∷
   re 50 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 49 q7 ∷
   rw 50 q10 ∷
   rw 51 q7 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 50 q11 ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q12 ∷
   re 53 3 (CX31 ∷ []) ∷
   rw 52 q13 ∷
   rw 51 q14 ∷
   rw 50 q15 ∷
   re 50 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 49 q16 ∷
   re 50 5 (CS03 ∷ []) ∷
   rw 52 q5 ∷
   rw⁻ 51 q6 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q7 ∷
   rw 51 q8 ∷
   rw⁻ 50 q7 ∷
   re 51 3 (CS13 ∷ []) ∷
   rw 51 q9 ∷
   rw 50 q6 ∷
   re 52 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 51 q7 ∷
   rw 52 q10 ∷
   rw 53 q7 ∷
   re 51 3 (CS03 ∷ []) ∷
   rw 52 q11 ∷
   rw 49 q5 ∷
   rw⁻ 48 q6 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q7 ∷
   rw 48 q8 ∷
   rw⁻ 47 q7 ∷
   re 48 3 (CS13 ∷ []) ∷
   rw 48 q9 ∷
   rw 47 q6 ∷
   re 49 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 48 q7 ∷
   rw 49 q10 ∷
   rw 50 q7 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 49 q11 ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q12 ∷
   re 52 3 (CX31 ∷ []) ∷
   rw 51 q13 ∷
   rw 50 q14 ∷
   rw 49 q15 ∷
   re 49 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 48 q16 ∷
   re 49 5 (CS03 ∷ []) ∷
   rw 51 q5 ∷
   rw⁻ 50 q6 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q7 ∷
   rw 50 q8 ∷
   rw⁻ 49 q7 ∷
   re 50 3 (CS13 ∷ []) ∷
   rw 50 q9 ∷
   rw 49 q6 ∷
   re 51 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 50 q7 ∷
   rw 51 q10 ∷
   rw 52 q7 ∷
   re 50 3 (CS03 ∷ []) ∷
   rw 51 q11 ∷
   rw 48 q5 ∷
   rw⁻ 47 q6 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q7 ∷
   rw 47 q8 ∷
   rw⁻ 46 q7 ∷
   re 47 3 (CS13 ∷ []) ∷
   rw 47 q9 ∷
   rw 46 q6 ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q7 ∷
   rw 48 q10 ∷
   rw 49 q7 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 48 q11 ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q12 ∷
   re 51 3 (CX31 ∷ []) ∷
   rw 50 q13 ∷
   rw 49 q14 ∷
   rw 48 q15 ∷
   re 48 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 47 q16 ∷
   re 48 5 (CS03 ∷ []) ∷
   rw 50 q5 ∷
   rw⁻ 49 q6 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q7 ∷
   rw 49 q8 ∷
   rw⁻ 48 q7 ∷
   re 49 3 (CS13 ∷ []) ∷
   rw 49 q9 ∷
   rw 48 q6 ∷
   re 50 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 49 q7 ∷
   rw 50 q10 ∷
   rw 51 q7 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 50 q11 ∷
   rw 45 q21 ∷
   rw 46 q5 ∷
   rw⁻ 45 q6 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q7 ∷
   rw 45 q8 ∷
   rw⁻ 44 q7 ∷
   re 45 3 (CS13 ∷ []) ∷
   rw 45 q9 ∷
   rw 44 q6 ∷
   re 46 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 45 q7 ∷
   rw 46 q10 ∷
   rw 47 q7 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 46 q11 ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q12 ∷
   re 49 3 (CX31 ∷ []) ∷
   rw 48 q13 ∷
   rw 47 q14 ∷
   rw 46 q15 ∷
   re 46 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 45 q16 ∷
   re 46 5 (CS03 ∷ []) ∷
   rw 48 q5 ∷
   rw⁻ 47 q6 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q7 ∷
   rw 47 q8 ∷
   rw⁻ 46 q7 ∷
   re 47 3 (CS13 ∷ []) ∷
   rw 47 q9 ∷
   rw 46 q6 ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q7 ∷
   rw 48 q10 ∷
   rw 49 q7 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 48 q11 ∷
   rw 45 q5 ∷
   rw⁻ 44 q6 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q7 ∷
   rw 44 q8 ∷
   rw⁻ 43 q7 ∷
   re 44 3 (CS13 ∷ []) ∷
   rw 44 q9 ∷
   rw 43 q6 ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q7 ∷
   rw 45 q10 ∷
   rw 46 q7 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 45 q11 ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q12 ∷
   re 48 3 (CX31 ∷ []) ∷
   rw 47 q13 ∷
   rw 46 q14 ∷
   rw 45 q15 ∷
   re 45 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 44 q16 ∷
   re 45 5 (CS03 ∷ []) ∷
   rw 47 q5 ∷
   rw⁻ 46 q6 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q7 ∷
   rw 46 q8 ∷
   rw⁻ 45 q7 ∷
   re 46 3 (CS13 ∷ []) ∷
   rw 46 q9 ∷
   rw 45 q6 ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 46 q7 ∷
   rw 47 q10 ∷
   rw 48 q7 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 47 q11 ∷
   rw 44 q5 ∷
   rw⁻ 43 q6 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q7 ∷
   rw 43 q8 ∷
   rw⁻ 42 q7 ∷
   re 43 3 (CS13 ∷ []) ∷
   rw 43 q9 ∷
   rw 42 q6 ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q7 ∷
   rw 44 q10 ∷
   rw 45 q7 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 44 q11 ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q12 ∷
   re 47 3 (CX31 ∷ []) ∷
   rw 46 q13 ∷
   rw 45 q14 ∷
   rw 44 q15 ∷
   re 44 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 43 q16 ∷
   re 44 5 (CS03 ∷ []) ∷
   rw 46 q5 ∷
   rw⁻ 45 q6 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q7 ∷
   rw 45 q8 ∷
   rw⁻ 44 q7 ∷
   re 45 3 (CS13 ∷ []) ∷
   rw 45 q9 ∷
   rw 44 q6 ∷
   re 46 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 45 q7 ∷
   rw 46 q10 ∷
   rw 47 q7 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 46 q11 ∷
   rw 43 q5 ∷
   rw⁻ 42 q6 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q7 ∷
   rw 42 q8 ∷
   rw⁻ 41 q7 ∷
   re 42 3 (CS13 ∷ []) ∷
   rw 42 q9 ∷
   rw 41 q6 ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q7 ∷
   rw 43 q10 ∷
   rw 44 q7 ∷
   re 42 3 (CS03 ∷ []) ∷
   rw 43 q11 ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q12 ∷
   re 46 3 (CX31 ∷ []) ∷
   rw 45 q13 ∷
   rw 44 q14 ∷
   rw 43 q15 ∷
   re 43 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 42 q16 ∷
   re 43 5 (CS03 ∷ []) ∷
   rw 45 q5 ∷
   rw⁻ 44 q6 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q7 ∷
   rw 44 q8 ∷
   rw⁻ 43 q7 ∷
   re 44 3 (CS13 ∷ []) ∷
   rw 44 q9 ∷
   rw 43 q6 ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q7 ∷
   rw 45 q10 ∷
   rw 46 q7 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 45 q11 ∷
   rw 42 q5 ∷
   rw⁻ 41 q6 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q7 ∷
   rw 41 q8 ∷
   rw⁻ 40 q7 ∷
   re 41 3 (CS13 ∷ []) ∷
   rw 41 q9 ∷
   rw 40 q6 ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 41 q7 ∷
   rw 42 q10 ∷
   rw 43 q7 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 42 q11 ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q12 ∷
   re 45 3 (CX31 ∷ []) ∷
   rw 44 q13 ∷
   rw 43 q14 ∷
   rw 42 q15 ∷
   re 42 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 41 q16 ∷
   re 42 5 (CS03 ∷ []) ∷
   rw 44 q5 ∷
   rw⁻ 43 q6 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q7 ∷
   rw 43 q8 ∷
   rw⁻ 42 q7 ∷
   re 43 3 (CS13 ∷ []) ∷
   rw 43 q9 ∷
   rw 42 q6 ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q7 ∷
   rw 44 q10 ∷
   rw 45 q7 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 44 q11 ∷
   rw 41 q5 ∷
   rw⁻ 40 q6 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q7 ∷
   rw 40 q8 ∷
   rw⁻ 39 q7 ∷
   re 40 3 (CS13 ∷ []) ∷
   rw 40 q9 ∷
   rw 39 q6 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q7 ∷
   rw 41 q10 ∷
   rw 42 q7 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q11 ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q12 ∷
   re 44 3 (CX31 ∷ []) ∷
   rw 43 q13 ∷
   rw 42 q14 ∷
   rw 41 q15 ∷
   re 41 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 40 q16 ∷
   re 41 5 (CS03 ∷ []) ∷
   rw 43 q5 ∷
   rw⁻ 42 q6 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q7 ∷
   rw 42 q8 ∷
   rw⁻ 41 q7 ∷
   re 42 3 (CS13 ∷ []) ∷
   rw 42 q9 ∷
   rw 41 q6 ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q7 ∷
   rw 43 q10 ∷
   rw 44 q7 ∷
   re 42 3 (CS03 ∷ []) ∷
   rw 43 q11 ∷
   rw 40 q5 ∷
   rw⁻ 39 q6 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q7 ∷
   rw 39 q8 ∷
   rw⁻ 38 q7 ∷
   re 39 3 (CS13 ∷ []) ∷
   rw 39 q9 ∷
   rw 38 q6 ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q7 ∷
   rw 40 q10 ∷
   rw 41 q7 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 40 q11 ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q12 ∷
   re 43 3 (CX31 ∷ []) ∷
   rw 42 q13 ∷ []) Eq.refl

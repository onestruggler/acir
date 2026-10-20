{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D161 (W : Ws) where

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
  q6 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q7 : Eqn
  q7 = eqn (Sw12 ∷ CX31 ∷ []) (CX32 ∷ Sw12 ∷ []) (wn 113 W)
  q8 : Eqn
  q8 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q9 : Eqn
  q9 = eqn (Sw12 ∷ CX32 ∷ []) (CX31 ∷ Sw12 ∷ []) (wn 114 W)
  q10 : Eqn
  q10 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q11 : Eqn
  q11 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q12 : Eqn
  q12 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
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
  q20 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ CX21 ∷ X2 ∷ []) (X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (wn 488 W)
  q21 : Eqn
  q21 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q22 : Eqn
  q22 = eqn (CK10⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap))
  q23 : Eqn
  q23 = eqn (S1⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (Swap))
  q24 : Eqn
  q24 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (wn 489 W)
  q25 : Eqn
  q25 = eqn (CS01⁻ ∷ CX23 ∷ []) (CX23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₀₁))
  q26 : Eqn
  q26 = eqn (S1⁻ ∷ CX23 ∷ []) (CX23 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (CX₀₁))
  q27 : Eqn
  q27 = eqn (CK10⁻ ∷ CX23 ∷ []) (CX23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₀₁))
  q28 : Eqn
  q28 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q29 : Eqn
  q29 = eqn (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (wn 490 W)
  q30 : Eqn
  q30 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)

-- Bar(SSKSKK;2,3->0) passes white iX via V2 conjugates 1 part7: 500 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part7 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ CX21 ∷ X2 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ X2 ∷ CX21 ∷ X2 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part7 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ CX21 ∷ X2 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ X2 ∷ CX21 ∷ X2 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ [])
  (rw 52 q1 ∷
   rw 51 q2 ∷
   re 53 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 52 q3 ∷
   rw 53 q4 ∷
   rw 54 q3 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw 53 q5 ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q6 ∷
   re 56 3 (CX31 ∷ []) ∷
   rw 55 q7 ∷
   rw 54 q8 ∷
   rw 53 q9 ∷
   re 53 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 52 q10 ∷
   re 53 5 (CS03 ∷ []) ∷
   rw 55 q11 ∷
   rw⁻ 54 q2 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 55 q3 ∷
   rw 54 q12 ∷
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
   rw 52 q11 ∷
   rw⁻ 51 q2 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q3 ∷
   rw 51 q12 ∷
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
   rw 57 q6 ∷
   re 55 3 (CX31 ∷ []) ∷
   rw 54 q7 ∷
   rw 53 q8 ∷
   rw 52 q9 ∷
   re 52 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 51 q10 ∷
   re 52 5 (CS03 ∷ []) ∷
   rw 54 q11 ∷
   rw⁻ 53 q2 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 54 q3 ∷
   rw 53 q12 ∷
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
   rw⁻ 49 q13 ∷
   rw⁻ 50 q14 ∷
   rw⁻ 51 q13 ∷
   rw 50 q11 ∷
   rw⁻ 49 q2 ∷
   re 48 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q3 ∷
   rw 49 q15 ∷
   rw⁻ 48 q3 ∷
   re 49 3 (CK31 ∷ []) ∷
   rw 49 q16 ∷
   rw 48 q2 ∷
   re 50 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 49 q3 ∷
   rw 50 q17 ∷
   rw 51 q3 ∷
   re 49 3 (CK30 ∷ []) ∷
   rw 50 q5 ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q6 ∷
   re 53 3 (CX31 ∷ []) ∷
   rw 52 q7 ∷
   rw 51 q18 ∷
   rw 50 q9 ∷
   re 50 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 49 q10 ∷
   re 50 5 (CK30 ∷ []) ∷
   rw 52 q11 ∷
   rw⁻ 51 q2 ∷
   re 50 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q3 ∷
   rw 51 q15 ∷
   rw⁻ 50 q3 ∷
   re 51 3 (CK31 ∷ []) ∷
   rw 51 q16 ∷
   rw 50 q2 ∷
   re 52 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 51 q3 ∷
   rw 52 q17 ∷
   rw 53 q3 ∷
   re 51 3 (CK30 ∷ []) ∷
   rw 52 q5 ∷
   rw⁻ 47 q13 ∷
   rw⁻ 48 q14 ∷
   rw⁻ 49 q13 ∷
   rw 48 q11 ∷
   rw⁻ 47 q2 ∷
   re 46 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q3 ∷
   rw 47 q15 ∷
   rw⁻ 46 q3 ∷
   re 47 3 (CK31 ∷ []) ∷
   rw 47 q16 ∷
   rw 46 q2 ∷
   re 48 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 47 q3 ∷
   rw 48 q17 ∷
   rw 49 q3 ∷
   re 47 3 (CK30 ∷ []) ∷
   rw 48 q5 ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q6 ∷
   re 51 3 (CX31 ∷ []) ∷
   rw 50 q7 ∷
   rw 49 q18 ∷
   rw 48 q9 ∷
   re 48 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 47 q10 ∷
   re 48 5 (CK30 ∷ []) ∷
   rw 50 q11 ∷
   rw⁻ 49 q2 ∷
   re 48 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q3 ∷
   rw 49 q15 ∷
   rw⁻ 48 q3 ∷
   re 49 3 (CK31 ∷ []) ∷
   rw 49 q16 ∷
   rw 48 q2 ∷
   re 50 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 49 q3 ∷
   rw 50 q17 ∷
   rw 51 q3 ∷
   re 49 3 (CK30 ∷ []) ∷
   rw 50 q5 ∷
   rw 45 q19 ∷
   rw 39 q20 ∷
   rw 82 q6 ∷
   rw 81 q21 ∷
   rw 80 q21 ∷
   rw 79 q21 ∷
   rw 78 q22 ∷
   rw 77 q23 ∷
   rw 76 q21 ∷
   rw 75 q21 ∷
   rw 74 q21 ∷
   rw 73 q21 ∷
   rw 72 q21 ∷
   rw 71 q21 ∷
   re 70 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 72 q10 ∷
   re 69 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 71 q10 ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 70 q10 ∷
   re 67 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 69 q10 ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 68 q10 ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q10 ∷
   rw 66 q24 ∷
   rw⁻ 65 q21 ∷
   rw⁻ 66 q21 ∷
   rw⁻ 67 q21 ∷
   rw⁻ 68 q21 ∷
   rw⁻ 69 q21 ∷
   rw⁻ 70 q21 ∷
   rw⁻ 71 q23 ∷
   rw⁻ 72 q22 ∷
   rw⁻ 73 q21 ∷
   rw⁻ 74 q21 ∷
   rw⁻ 75 q21 ∷
   rw 78 q6 ∷
   re 76 3 (CS03 ∷ []) ∷
   rw 79 q6 ∷
   re 77 3 (CS03 ∷ []) ∷
   rw 80 q6 ∷
   re 78 3 (CK30 ∷ []) ∷
   rw 81 q6 ∷
   re 79 3 (CS03 ∷ []) ∷
   rw 82 q6 ∷
   re 80 3 (CK30 ∷ []) ∷
   rw 83 q6 ∷
   re 81 3 (CK30 ∷ []) ∷
   rw 82 q10 ∷
   rw⁻ 64 q25 ∷
   rw⁻ 65 q25 ∷
   rw⁻ 66 q25 ∷
   rw⁻ 67 q25 ∷
   rw⁻ 68 q25 ∷
   rw⁻ 69 q25 ∷
   rw⁻ 70 q26 ∷
   rw⁻ 71 q27 ∷
   rw⁻ 72 q25 ∷
   rw⁻ 73 q25 ∷
   rw⁻ 74 q25 ∷
   rw 75 q6 ∷
   rw 74 q21 ∷
   rw 73 q21 ∷
   rw 72 q21 ∷
   rw 71 q22 ∷
   rw 70 q23 ∷
   rw 69 q21 ∷
   rw 68 q21 ∷
   rw 67 q21 ∷
   rw 66 q21 ∷
   rw 65 q21 ∷
   rw 64 q21 ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 65 q10 ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 64 q10 ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 63 q10 ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 62 q10 ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 61 q10 ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q10 ∷
   rw 57 q28 ∷
   re 56 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 58 q10 ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q10 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q10 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 55 q10 ∷
   rw 52 q28 ∷
   re 51 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 53 q10 ∷
   rw 50 q28 ∷
   re 49 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 51 q10 ∷
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
   rw 62 q6 ∷
   re 60 3 (CK30 ∷ []) ∷
   rw 61 q30 ∷
   rw 64 q6 ∷
   re 62 3 (CK30 ∷ []) ∷
   rw 63 q30 ∷
   rw 66 q6 ∷
   re 64 3 (CS03 ∷ []) ∷
   rw 67 q6 ∷
   re 65 3 (CS03 ∷ []) ∷
   rw 68 q6 ∷
   re 66 3 (CS03 ∷ []) ∷
   rw 69 q6 ∷
   re 67 3 (CK30 ∷ []) ∷
   rw 68 q30 ∷
   rw 71 q6 ∷
   re 69 3 (CS03 ∷ []) ∷
   rw 72 q6 ∷
   re 70 3 (CS03 ∷ []) ∷
   rw 73 q6 ∷
   re 71 3 (CS03 ∷ []) ∷
   rw 74 q6 ∷
   re 72 3 (CS03 ∷ []) ∷
   rw 75 q6 ∷
   re 73 3 (CS03 ∷ []) ∷
   rw 76 q6 ∷
   re 74 3 (CS03 ∷ []) ∷
   rw 75 q10 ∷
   rw⁻ 48 q25 ∷
   rw⁻ 49 q25 ∷
   rw⁻ 50 q25 ∷
   rw⁻ 51 q25 ∷
   rw⁻ 52 q25 ∷
   rw⁻ 53 q25 ∷
   rw⁻ 54 q26 ∷
   rw⁻ 55 q27 ∷
   rw⁻ 56 q25 ∷
   rw⁻ 57 q25 ∷
   rw⁻ 58 q25 ∷
   rw 42 q24 ∷
   rw 83 q11 ∷
   rw⁻ 82 q2 ∷
   re 81 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 83 q3 ∷
   rw 82 q15 ∷
   rw⁻ 81 q3 ∷
   re 82 3 (CK31 ∷ []) ∷
   rw 82 q16 ∷
   rw 81 q2 ∷
   re 83 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 82 q3 ∷
   rw 83 q17 ∷
   rw 84 q3 ∷
   re 82 3 (CK30 ∷ []) ∷
   rw 83 q5 ∷
   re 82 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 88 q6 ∷
   re 86 3 (CX31 ∷ []) ∷
   rw 85 q7 ∷
   rw 84 q18 ∷
   rw 83 q9 ∷
   re 83 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 82 q10 ∷
   re 83 5 (CK30 ∷ []) ∷
   rw 85 q11 ∷
   rw⁻ 84 q2 ∷
   re 83 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 85 q3 ∷
   rw 84 q15 ∷
   rw⁻ 83 q3 ∷
   re 84 3 (CK31 ∷ []) ∷
   rw 84 q16 ∷
   rw 83 q2 ∷
   re 85 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 84 q3 ∷
   rw 85 q17 ∷
   rw 86 q3 ∷
   re 84 3 (CK30 ∷ []) ∷
   rw 85 q5 ∷
   rw 82 q11 ∷
   rw⁻ 81 q2 ∷
   re 80 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 82 q3 ∷
   rw 81 q15 ∷
   rw⁻ 80 q3 ∷
   re 81 3 (CK31 ∷ []) ∷
   rw 81 q16 ∷
   rw 80 q2 ∷
   re 82 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 81 q3 ∷
   rw 82 q17 ∷
   rw 83 q3 ∷
   re 81 3 (CK30 ∷ []) ∷
   rw 82 q5 ∷
   re 81 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 87 q6 ∷
   re 85 3 (CX31 ∷ []) ∷
   rw 84 q7 ∷
   rw 83 q18 ∷
   rw 82 q9 ∷
   re 82 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 81 q10 ∷
   re 82 5 (CK30 ∷ []) ∷
   rw 84 q11 ∷
   rw⁻ 83 q2 ∷
   re 82 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 84 q3 ∷
   rw 83 q15 ∷
   rw⁻ 82 q3 ∷
   re 83 3 (CK31 ∷ []) ∷
   rw 83 q16 ∷
   rw 82 q2 ∷
   re 84 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 83 q3 ∷
   rw 84 q17 ∷
   rw 85 q3 ∷
   re 83 3 (CK30 ∷ []) ∷
   rw 84 q5 ∷
   rw 81 q11 ∷
   rw⁻ 80 q2 ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 81 q3 ∷
   rw 80 q12 ∷
   rw⁻ 79 q3 ∷
   re 80 3 (CS13 ∷ []) ∷
   rw 80 q1 ∷
   rw 79 q2 ∷
   re 81 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 80 q3 ∷
   rw 81 q4 ∷
   rw 82 q3 ∷
   re 80 3 (CS03 ∷ []) ∷
   rw 81 q5 ∷
   re 80 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 86 q6 ∷
   re 84 3 (CX31 ∷ []) ∷
   rw 83 q7 ∷
   rw 82 q8 ∷
   rw 81 q9 ∷
   re 81 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 80 q10 ∷
   re 81 5 (CS03 ∷ []) ∷
   rw 83 q11 ∷
   rw⁻ 82 q2 ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 83 q3 ∷
   rw 82 q12 ∷
   rw⁻ 81 q3 ∷
   re 82 3 (CS13 ∷ []) ∷
   rw 82 q1 ∷
   rw 81 q2 ∷
   re 83 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 82 q3 ∷
   rw 83 q4 ∷
   rw 84 q3 ∷
   re 82 3 (CS03 ∷ []) ∷
   rw 83 q5 ∷
   rw 80 q11 ∷
   rw⁻ 79 q2 ∷
   re 78 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 80 q3 ∷
   rw 79 q15 ∷
   rw⁻ 78 q3 ∷
   re 79 3 (CK31 ∷ []) ∷
   rw 79 q16 ∷
   rw 78 q2 ∷
   re 80 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 79 q3 ∷
   rw 80 q17 ∷
   rw 81 q3 ∷
   re 79 3 (CK30 ∷ []) ∷
   rw 80 q5 ∷
   re 79 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 85 q6 ∷
   re 83 3 (CX31 ∷ []) ∷
   rw 82 q7 ∷
   rw 81 q18 ∷
   rw 80 q9 ∷
   re 80 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 79 q10 ∷
   re 80 5 (CK30 ∷ []) ∷
   rw 82 q11 ∷
   rw⁻ 81 q2 ∷
   re 80 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 82 q3 ∷
   rw 81 q15 ∷
   rw⁻ 80 q3 ∷
   re 81 3 (CK31 ∷ []) ∷
   rw 81 q16 ∷
   rw 80 q2 ∷
   re 82 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 81 q3 ∷
   rw 82 q17 ∷
   rw 83 q3 ∷
   re 81 3 (CK30 ∷ []) ∷
   rw 82 q5 ∷
   rw 79 q11 ∷
   rw⁻ 78 q2 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 79 q3 ∷
   rw 78 q12 ∷
   rw⁻ 77 q3 ∷
   re 78 3 (CS13 ∷ []) ∷
   rw 78 q1 ∷
   rw 77 q2 ∷
   re 79 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 78 q3 ∷
   rw 79 q4 ∷
   rw 80 q3 ∷
   re 78 3 (CS03 ∷ []) ∷
   rw 79 q5 ∷
   re 78 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 84 q6 ∷
   re 82 3 (CX31 ∷ []) ∷
   rw 81 q7 ∷
   rw 80 q8 ∷
   rw 79 q9 ∷
   re 79 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 78 q10 ∷
   re 79 5 (CS03 ∷ []) ∷
   rw 81 q11 ∷
   rw⁻ 80 q2 ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 81 q3 ∷
   rw 80 q12 ∷
   rw⁻ 79 q3 ∷
   re 80 3 (CS13 ∷ []) ∷
   rw 80 q1 ∷
   rw 79 q2 ∷
   re 81 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 80 q3 ∷
   rw 81 q4 ∷ []) Eq.refl

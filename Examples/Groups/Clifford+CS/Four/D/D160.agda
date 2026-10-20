{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D160 (W : Ws) where

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
  q1 = eqn (Sw12 ∷ CX31 ∷ []) (CX32 ∷ Sw12 ∷ []) (wn 113 W)
  q2 : Eqn
  q2 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q3 : Eqn
  q3 = eqn (Sw12 ∷ CX32 ∷ []) (CX31 ∷ Sw12 ∷ []) (wn 114 W)
  q4 : Eqn
  q4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q5 : Eqn
  q5 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q6 : Eqn
  q6 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q9 : Eqn
  q9 = eqn (CK31 ∷ X2 ∷ []) (X2 ∷ CK31 ∷ []) (wn 630 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q12 : Eqn
  q12 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q13 : Eqn
  q13 = eqn (CS13 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ []) (wn 629 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q15 : Eqn
  q15 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q16 : Eqn
  q16 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q17 : Eqn
  q17 = eqn (CX23 ∷ X2 ∷ CX21 ∷ X2 ∷ []) (X2 ∷ CX21 ∷ X2 ∷ CX23 ∷ []) (wn 673 W)
  q18 : Eqn
  q18 = eqn (X2 ∷ S3 ∷ []) (S3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (S))
  q19 : Eqn
  q19 = eqn (CX21 ∷ S3 ∷ []) (S3 ∷ CX21 ∷ []) (low₃-comm ((CX₁₀ ↑)) (S))

-- Bar(SSKSKK;2,3->0) passes white iX via V2 conjugates 1 part6: 500 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part6 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ CX31 ∷ Sw23 ∷ X2 ∷ CK30 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ CX21 ∷ X2 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part6 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ CX31 ∷ Sw23 ∷ X2 ∷ CK30 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ CX21 ∷ X2 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ [])
  (rw 70 q1 ∷
   rw 69 q2 ∷
   rw 68 q3 ∷
   re 68 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 67 q4 ∷
   re 68 5 (CK30 ∷ []) ∷
   rw 70 q5 ∷
   rw⁻ 69 q6 ∷
   re 68 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 70 q7 ∷
   rw 69 q8 ∷
   rw⁻ 68 q7 ∷
   re 69 3 (CK31 ∷ []) ∷
   rw 69 q9 ∷
   rw 68 q6 ∷
   re 70 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 69 q7 ∷
   rw 70 q10 ∷
   rw 71 q7 ∷
   re 69 3 (CK30 ∷ []) ∷
   rw 70 q11 ∷
   rw 67 q5 ∷
   rw⁻ 66 q6 ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 67 q7 ∷
   rw 66 q12 ∷
   rw⁻ 65 q7 ∷
   re 66 3 (CS13 ∷ []) ∷
   rw 66 q13 ∷
   rw 65 q6 ∷
   re 67 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 66 q7 ∷
   rw 67 q14 ∷
   rw 68 q7 ∷
   re 66 3 (CS03 ∷ []) ∷
   rw 67 q11 ∷
   re 66 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 72 q15 ∷
   re 70 3 (CX31 ∷ []) ∷
   rw 69 q1 ∷
   rw 68 q16 ∷
   rw 67 q3 ∷
   re 67 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 66 q4 ∷
   re 67 5 (CS03 ∷ []) ∷
   rw 69 q5 ∷
   rw⁻ 68 q6 ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 69 q7 ∷
   rw 68 q12 ∷
   rw⁻ 67 q7 ∷
   re 68 3 (CS13 ∷ []) ∷
   rw 68 q13 ∷
   rw 67 q6 ∷
   re 69 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 68 q7 ∷
   rw 69 q14 ∷
   rw 70 q7 ∷
   re 68 3 (CS03 ∷ []) ∷
   rw 69 q11 ∷
   rw 66 q5 ∷
   rw⁻ 65 q6 ∷
   re 64 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 66 q7 ∷
   rw 65 q8 ∷
   rw⁻ 64 q7 ∷
   re 65 3 (CK31 ∷ []) ∷
   rw 65 q9 ∷
   rw 64 q6 ∷
   re 66 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 65 q7 ∷
   rw 66 q10 ∷
   rw 67 q7 ∷
   re 65 3 (CK30 ∷ []) ∷
   rw 66 q11 ∷
   re 65 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q15 ∷
   re 69 3 (CX31 ∷ []) ∷
   rw 68 q1 ∷
   rw 67 q2 ∷
   rw 66 q3 ∷
   re 66 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 65 q4 ∷
   re 66 5 (CK30 ∷ []) ∷
   rw 68 q5 ∷
   rw⁻ 67 q6 ∷
   re 66 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 68 q7 ∷
   rw 67 q8 ∷
   rw⁻ 66 q7 ∷
   re 67 3 (CK31 ∷ []) ∷
   rw 67 q9 ∷
   rw 66 q6 ∷
   re 68 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 67 q7 ∷
   rw 68 q10 ∷
   rw 69 q7 ∷
   re 67 3 (CK30 ∷ []) ∷
   rw 68 q11 ∷
   rw 65 q5 ∷
   rw⁻ 64 q6 ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 65 q7 ∷
   rw 64 q12 ∷
   rw⁻ 63 q7 ∷
   re 64 3 (CS13 ∷ []) ∷
   rw 64 q13 ∷
   rw 63 q6 ∷
   re 65 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 64 q7 ∷
   rw 65 q14 ∷
   rw 66 q7 ∷
   re 64 3 (CS03 ∷ []) ∷
   rw 65 q11 ∷
   re 64 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 70 q15 ∷
   re 68 3 (CX31 ∷ []) ∷
   rw 67 q1 ∷
   rw 66 q16 ∷
   rw 65 q3 ∷
   re 65 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 64 q4 ∷
   re 65 5 (CS03 ∷ []) ∷
   rw 67 q5 ∷
   rw⁻ 66 q6 ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 67 q7 ∷
   rw 66 q12 ∷
   rw⁻ 65 q7 ∷
   re 66 3 (CS13 ∷ []) ∷
   rw 66 q13 ∷
   rw 65 q6 ∷
   re 67 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 66 q7 ∷
   rw 67 q14 ∷
   rw 68 q7 ∷
   re 66 3 (CS03 ∷ []) ∷
   rw 67 q11 ∷
   rw 64 q5 ∷
   rw⁻ 63 q6 ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 64 q7 ∷
   rw 63 q12 ∷
   rw⁻ 62 q7 ∷
   re 63 3 (CS13 ∷ []) ∷
   rw 63 q13 ∷
   rw 62 q6 ∷
   re 64 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 63 q7 ∷
   rw 64 q14 ∷
   rw 65 q7 ∷
   re 63 3 (CS03 ∷ []) ∷
   rw 64 q11 ∷
   re 63 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 69 q15 ∷
   re 67 3 (CX31 ∷ []) ∷
   rw 66 q1 ∷
   rw 65 q16 ∷
   rw 64 q3 ∷
   re 64 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 63 q4 ∷
   re 64 5 (CS03 ∷ []) ∷
   rw 66 q5 ∷
   rw⁻ 65 q6 ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 66 q7 ∷
   rw 65 q12 ∷
   rw⁻ 64 q7 ∷
   re 65 3 (CS13 ∷ []) ∷
   rw 65 q13 ∷
   rw 64 q6 ∷
   re 66 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 65 q7 ∷
   rw 66 q14 ∷
   rw 67 q7 ∷
   re 65 3 (CS03 ∷ []) ∷
   rw 66 q11 ∷
   rw 61 q17 ∷
   rw 62 q5 ∷
   rw⁻ 61 q6 ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 62 q7 ∷
   rw 61 q12 ∷
   rw⁻ 60 q7 ∷
   re 61 3 (CS13 ∷ []) ∷
   rw 61 q13 ∷
   rw 60 q6 ∷
   re 62 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 61 q7 ∷
   rw 62 q14 ∷
   rw 63 q7 ∷
   re 61 3 (CS03 ∷ []) ∷
   rw 62 q11 ∷
   re 61 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 67 q15 ∷
   re 65 3 (CX31 ∷ []) ∷
   rw 64 q1 ∷
   rw 63 q16 ∷
   rw 62 q3 ∷
   re 62 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 61 q4 ∷
   re 62 5 (CS03 ∷ []) ∷
   rw 64 q5 ∷
   rw⁻ 63 q6 ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 64 q7 ∷
   rw 63 q12 ∷
   rw⁻ 62 q7 ∷
   re 63 3 (CS13 ∷ []) ∷
   rw 63 q13 ∷
   rw 62 q6 ∷
   re 64 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 63 q7 ∷
   rw 64 q14 ∷
   rw 65 q7 ∷
   re 63 3 (CS03 ∷ []) ∷
   rw 64 q11 ∷
   rw 61 q5 ∷
   rw⁻ 60 q6 ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 61 q7 ∷
   rw 60 q12 ∷
   rw⁻ 59 q7 ∷
   re 60 3 (CS13 ∷ []) ∷
   rw 60 q13 ∷
   rw 59 q6 ∷
   re 61 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 60 q7 ∷
   rw 61 q14 ∷
   rw 62 q7 ∷
   re 60 3 (CS03 ∷ []) ∷
   rw 61 q11 ∷
   re 60 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 66 q15 ∷
   re 64 3 (CX31 ∷ []) ∷
   rw 63 q1 ∷
   rw 62 q16 ∷
   rw 61 q3 ∷
   re 61 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 60 q4 ∷
   re 61 5 (CS03 ∷ []) ∷
   rw 63 q5 ∷
   rw⁻ 62 q6 ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 63 q7 ∷
   rw 62 q12 ∷
   rw⁻ 61 q7 ∷
   re 62 3 (CS13 ∷ []) ∷
   rw 62 q13 ∷
   rw 61 q6 ∷
   re 63 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 62 q7 ∷
   rw 63 q14 ∷
   rw 64 q7 ∷
   re 62 3 (CS03 ∷ []) ∷
   rw 63 q11 ∷
   rw 60 q5 ∷
   rw⁻ 59 q6 ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 60 q7 ∷
   rw 59 q12 ∷
   rw⁻ 58 q7 ∷
   re 59 3 (CS13 ∷ []) ∷
   rw 59 q13 ∷
   rw 58 q6 ∷
   re 60 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 59 q7 ∷
   rw 60 q14 ∷
   rw 61 q7 ∷
   re 59 3 (CS03 ∷ []) ∷
   rw 60 q11 ∷
   re 59 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 65 q15 ∷
   re 63 3 (CX31 ∷ []) ∷
   rw 62 q1 ∷
   rw 61 q16 ∷
   rw 60 q3 ∷
   re 60 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 59 q4 ∷
   re 60 5 (CS03 ∷ []) ∷
   rw 62 q5 ∷
   rw⁻ 61 q6 ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 62 q7 ∷
   rw 61 q12 ∷
   rw⁻ 60 q7 ∷
   re 61 3 (CS13 ∷ []) ∷
   rw 61 q13 ∷
   rw 60 q6 ∷
   re 62 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 61 q7 ∷
   rw 62 q14 ∷
   rw 63 q7 ∷
   re 61 3 (CS03 ∷ []) ∷
   rw 62 q11 ∷
   rw 59 q5 ∷
   rw⁻ 58 q6 ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 59 q7 ∷
   rw 58 q12 ∷
   rw⁻ 57 q7 ∷
   re 58 3 (CS13 ∷ []) ∷
   rw 58 q13 ∷
   rw 57 q6 ∷
   re 59 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 58 q7 ∷
   rw 59 q14 ∷
   rw 60 q7 ∷
   re 58 3 (CS03 ∷ []) ∷
   rw 59 q11 ∷
   re 58 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 64 q15 ∷
   re 62 3 (CX31 ∷ []) ∷
   rw 61 q1 ∷
   rw 60 q16 ∷
   rw 59 q3 ∷
   re 59 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 58 q4 ∷
   re 59 5 (CS03 ∷ []) ∷
   rw 61 q5 ∷
   rw⁻ 60 q6 ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 61 q7 ∷
   rw 60 q12 ∷
   rw⁻ 59 q7 ∷
   re 60 3 (CS13 ∷ []) ∷
   rw 60 q13 ∷
   rw 59 q6 ∷
   re 61 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 60 q7 ∷
   rw 61 q14 ∷
   rw 62 q7 ∷
   re 60 3 (CS03 ∷ []) ∷
   rw 61 q11 ∷
   rw 58 q5 ∷
   rw⁻ 57 q6 ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 58 q7 ∷
   rw 57 q12 ∷
   rw⁻ 56 q7 ∷
   re 57 3 (CS13 ∷ []) ∷
   rw 57 q13 ∷
   rw 56 q6 ∷
   re 58 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 57 q7 ∷
   rw 58 q14 ∷
   rw 59 q7 ∷
   re 57 3 (CS03 ∷ []) ∷
   rw 58 q11 ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 63 q15 ∷
   re 61 3 (CX31 ∷ []) ∷
   rw 60 q1 ∷
   rw 59 q16 ∷
   rw 58 q3 ∷
   re 58 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 57 q4 ∷
   re 58 5 (CS03 ∷ []) ∷
   rw 60 q5 ∷
   rw⁻ 59 q6 ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 60 q7 ∷
   rw 59 q12 ∷
   rw⁻ 58 q7 ∷
   re 59 3 (CS13 ∷ []) ∷
   rw 59 q13 ∷
   rw 58 q6 ∷
   re 60 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 59 q7 ∷
   rw 60 q14 ∷
   rw 61 q7 ∷
   re 59 3 (CS03 ∷ []) ∷
   rw 60 q11 ∷
   rw 57 q5 ∷
   rw⁻ 56 q6 ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 57 q7 ∷
   rw 56 q12 ∷
   rw⁻ 55 q7 ∷
   re 56 3 (CS13 ∷ []) ∷
   rw 56 q13 ∷
   rw 55 q6 ∷
   re 57 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 56 q7 ∷
   rw 57 q14 ∷
   rw 58 q7 ∷
   re 56 3 (CS03 ∷ []) ∷
   rw 57 q11 ∷
   re 56 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 62 q15 ∷
   re 60 3 (CX31 ∷ []) ∷
   rw 59 q1 ∷
   rw 58 q16 ∷
   rw 57 q3 ∷
   re 57 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 56 q4 ∷
   re 57 5 (CS03 ∷ []) ∷
   rw 59 q5 ∷
   rw⁻ 58 q6 ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 59 q7 ∷
   rw 58 q12 ∷
   rw⁻ 57 q7 ∷
   re 58 3 (CS13 ∷ []) ∷
   rw 58 q13 ∷
   rw 57 q6 ∷
   re 59 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 58 q7 ∷
   rw 59 q14 ∷
   rw 60 q7 ∷
   re 58 3 (CS03 ∷ []) ∷
   rw 59 q11 ∷
   rw⁻ 54 q18 ∷
   rw⁻ 55 q19 ∷
   rw⁻ 56 q18 ∷
   rw 55 q5 ∷
   rw⁻ 54 q6 ∷
   re 53 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 55 q7 ∷
   rw 54 q8 ∷
   rw⁻ 53 q7 ∷
   re 54 3 (CK31 ∷ []) ∷
   rw 54 q9 ∷
   rw 53 q6 ∷
   re 55 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 54 q7 ∷
   rw 55 q10 ∷
   rw 56 q7 ∷
   re 54 3 (CK30 ∷ []) ∷
   rw 55 q11 ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 60 q15 ∷
   re 58 3 (CX31 ∷ []) ∷
   rw 57 q1 ∷
   rw 56 q2 ∷
   rw 55 q3 ∷
   re 55 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 54 q4 ∷
   re 55 5 (CK30 ∷ []) ∷
   rw 57 q5 ∷
   rw⁻ 56 q6 ∷
   re 55 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 57 q7 ∷
   rw 56 q8 ∷
   rw⁻ 55 q7 ∷
   re 56 3 (CK31 ∷ []) ∷
   rw 56 q9 ∷
   rw 55 q6 ∷
   re 57 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 56 q7 ∷
   rw 57 q10 ∷
   rw 58 q7 ∷
   re 56 3 (CK30 ∷ []) ∷
   rw 57 q11 ∷
   rw 54 q5 ∷
   rw⁻ 53 q6 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 54 q7 ∷
   rw 53 q12 ∷
   rw⁻ 52 q7 ∷
   re 53 3 (CS13 ∷ []) ∷
   rw 53 q13 ∷
   rw 52 q6 ∷
   re 54 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 53 q7 ∷
   rw 54 q14 ∷
   rw 55 q7 ∷
   re 53 3 (CS03 ∷ []) ∷
   rw 54 q11 ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q15 ∷
   re 57 3 (CX31 ∷ []) ∷
   rw 56 q1 ∷
   rw 55 q16 ∷
   rw 54 q3 ∷
   re 54 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 53 q4 ∷
   re 54 5 (CS03 ∷ []) ∷
   rw 56 q5 ∷
   rw⁻ 55 q6 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 56 q7 ∷
   rw 55 q12 ∷
   rw⁻ 54 q7 ∷
   re 55 3 (CS13 ∷ []) ∷
   rw 55 q13 ∷
   rw 54 q6 ∷
   re 56 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 55 q7 ∷
   rw 56 q14 ∷
   rw 57 q7 ∷
   re 55 3 (CS03 ∷ []) ∷
   rw 56 q11 ∷
   rw 53 q5 ∷
   rw⁻ 52 q6 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q7 ∷
   rw 52 q12 ∷
   rw⁻ 51 q7 ∷
   re 52 3 (CS13 ∷ []) ∷ []) Eq.refl

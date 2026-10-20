{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D156 (W : Ws) where

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
  q1 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q2 : Eqn
  q2 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q3 : Eqn
  q3 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q4 : Eqn
  q4 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q6 : Eqn
  q6 = eqn (CS13 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ []) (wn 629 W)
  q7 : Eqn
  q7 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q8 : Eqn
  q8 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q9 : Eqn
  q9 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q10 : Eqn
  q10 = eqn (Sw12 ∷ CX31 ∷ []) (CX32 ∷ Sw12 ∷ []) (wn 113 W)
  q11 : Eqn
  q11 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q12 : Eqn
  q12 = eqn (Sw12 ∷ CX32 ∷ []) (CX31 ∷ Sw12 ∷ []) (wn 114 W)
  q13 : Eqn
  q13 = eqn (CX23 ∷ X2 ∷ CX21 ∷ X2 ∷ []) (X2 ∷ CX21 ∷ X2 ∷ CX23 ∷ []) (wn 673 W)
  q14 : Eqn
  q14 = eqn (X2 ∷ S3 ∷ []) (S3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (S))
  q15 : Eqn
  q15 = eqn (CX21 ∷ S3 ∷ []) (S3 ∷ CX21 ∷ []) (low₃-comm ((CX₁₀ ↑)) (S))
  q16 : Eqn
  q16 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q17 : Eqn
  q17 = eqn (CK31 ∷ X2 ∷ []) (X2 ∷ CK31 ∷ []) (wn 630 W)
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q19 : Eqn
  q19 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))

-- Bar(SSKSKK;2,3->0) passes white iX via V2 conjugates 1 part2: 500 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part2 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ X2 ∷ Sw23 ∷ CX31 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ X2 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ Sw23 ∷ CK20 ∷ Sw01 ∷ Sw23 ∷ X2 ∷ Sw01 ∷ CX21 ∷ X2 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part2 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ X2 ∷ Sw23 ∷ CX31 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ X2 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ Sw23 ∷ CK20 ∷ Sw01 ∷ Sw23 ∷ X2 ∷ Sw01 ∷ CX21 ∷ X2 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ [])
  (re 33 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 33 5 (CS03 ∷ []) ∷
   rw 35 q2 ∷
   rw⁻ 34 q3 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q4 ∷
   rw 34 q5 ∷
   rw⁻ 33 q4 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw 34 q6 ∷
   rw 33 q3 ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q4 ∷
   rw 35 q7 ∷
   rw 36 q4 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 35 q8 ∷
   rw 32 q2 ∷
   rw⁻ 31 q3 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q4 ∷
   rw 31 q5 ∷
   rw⁻ 30 q4 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 31 q6 ∷
   rw 30 q3 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q4 ∷
   rw 32 q7 ∷
   rw 33 q4 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 32 q8 ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q9 ∷
   re 35 3 (CX31 ∷ []) ∷
   rw 34 q10 ∷
   rw 33 q11 ∷
   rw 32 q12 ∷
   re 32 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   re 32 5 (CS03 ∷ []) ∷
   rw 34 q2 ∷
   rw⁻ 33 q3 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q4 ∷
   rw 33 q5 ∷
   rw⁻ 32 q4 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw 33 q6 ∷
   rw 32 q3 ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q4 ∷
   rw 34 q7 ∷
   rw 35 q4 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 34 q8 ∷
   rw 29 q13 ∷
   rw 30 q2 ∷
   rw⁻ 29 q3 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q4 ∷
   rw 29 q5 ∷
   rw⁻ 28 q4 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 29 q6 ∷
   rw 28 q3 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q4 ∷
   rw 30 q7 ∷
   rw 31 q4 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 30 q8 ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q9 ∷
   re 33 3 (CX31 ∷ []) ∷
   rw 32 q10 ∷
   rw 31 q11 ∷
   rw 30 q12 ∷
   re 30 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   re 30 5 (CS03 ∷ []) ∷
   rw 32 q2 ∷
   rw⁻ 31 q3 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q4 ∷
   rw 31 q5 ∷
   rw⁻ 30 q4 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 31 q6 ∷
   rw 30 q3 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q4 ∷
   rw 32 q7 ∷
   rw 33 q4 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 32 q8 ∷
   rw 29 q2 ∷
   rw⁻ 28 q3 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q4 ∷
   rw 28 q5 ∷
   rw⁻ 27 q4 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 28 q6 ∷
   rw 27 q3 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q4 ∷
   rw 29 q7 ∷
   rw 30 q4 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 29 q8 ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q9 ∷
   re 32 3 (CX31 ∷ []) ∷
   rw 31 q10 ∷
   rw 30 q11 ∷
   rw 29 q12 ∷
   re 29 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   re 29 5 (CS03 ∷ []) ∷
   rw 31 q2 ∷
   rw⁻ 30 q3 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q4 ∷
   rw 30 q5 ∷
   rw⁻ 29 q4 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw 30 q6 ∷
   rw 29 q3 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q4 ∷
   rw 31 q7 ∷
   rw 32 q4 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 31 q8 ∷
   rw 28 q2 ∷
   rw⁻ 27 q3 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q4 ∷
   rw 27 q5 ∷
   rw⁻ 26 q4 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 27 q6 ∷
   rw 26 q3 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q4 ∷
   rw 28 q7 ∷
   rw 29 q4 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 28 q8 ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q9 ∷
   re 31 3 (CX31 ∷ []) ∷
   rw 30 q10 ∷
   rw 29 q11 ∷
   rw 28 q12 ∷
   re 28 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   re 28 5 (CS03 ∷ []) ∷
   rw 30 q2 ∷
   rw⁻ 29 q3 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q4 ∷
   rw 29 q5 ∷
   rw⁻ 28 q4 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 29 q6 ∷
   rw 28 q3 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q4 ∷
   rw 30 q7 ∷
   rw 31 q4 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 30 q8 ∷
   rw 27 q2 ∷
   rw⁻ 26 q3 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q4 ∷
   rw 26 q5 ∷
   rw⁻ 25 q4 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 26 q6 ∷
   rw 25 q3 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   rw 27 q7 ∷
   rw 28 q4 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 27 q8 ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q9 ∷
   re 30 3 (CX31 ∷ []) ∷
   rw 29 q10 ∷
   rw 28 q11 ∷
   rw 27 q12 ∷
   re 27 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   re 27 5 (CS03 ∷ []) ∷
   rw 29 q2 ∷
   rw⁻ 28 q3 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q4 ∷
   rw 28 q5 ∷
   rw⁻ 27 q4 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 28 q6 ∷
   rw 27 q3 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q4 ∷
   rw 29 q7 ∷
   rw 30 q4 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 29 q8 ∷
   rw 26 q2 ∷
   rw⁻ 25 q3 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q4 ∷
   rw 25 q5 ∷
   rw⁻ 24 q4 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 25 q6 ∷
   rw 24 q3 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   rw 26 q7 ∷
   rw 27 q4 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 26 q8 ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q9 ∷
   re 29 3 (CX31 ∷ []) ∷
   rw 28 q10 ∷
   rw 27 q11 ∷
   rw 26 q12 ∷
   re 26 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 26 5 (CS03 ∷ []) ∷
   rw 28 q2 ∷
   rw⁻ 27 q3 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q4 ∷
   rw 27 q5 ∷
   rw⁻ 26 q4 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 27 q6 ∷
   rw 26 q3 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q4 ∷
   rw 28 q7 ∷
   rw 29 q4 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 28 q8 ∷
   rw 25 q2 ∷
   rw⁻ 24 q3 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q4 ∷
   rw 24 q5 ∷
   rw⁻ 23 q4 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 24 q6 ∷
   rw 23 q3 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   rw 25 q7 ∷
   rw 26 q4 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 25 q8 ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q9 ∷
   re 28 3 (CX31 ∷ []) ∷
   rw 27 q10 ∷
   rw 26 q11 ∷
   rw 25 q12 ∷
   re 25 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   re 25 5 (CS03 ∷ []) ∷
   rw 27 q2 ∷
   rw⁻ 26 q3 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q4 ∷
   rw 26 q5 ∷
   rw⁻ 25 q4 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 26 q6 ∷
   rw 25 q3 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   rw 27 q7 ∷
   rw 28 q4 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 27 q8 ∷
   rw⁻ 22 q14 ∷
   rw⁻ 23 q15 ∷
   rw⁻ 24 q14 ∷
   rw 23 q2 ∷
   rw⁻ 22 q3 ∷
   re 21 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q4 ∷
   rw 22 q16 ∷
   rw⁻ 21 q4 ∷
   re 22 3 (CK31 ∷ []) ∷
   rw 22 q17 ∷
   rw 21 q3 ∷
   re 23 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   rw 23 q18 ∷
   rw 24 q4 ∷
   re 22 3 (CK30 ∷ []) ∷
   rw 23 q8 ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q9 ∷
   re 26 3 (CX31 ∷ []) ∷
   rw 25 q10 ∷
   rw 24 q19 ∷
   rw 23 q12 ∷
   re 23 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 22 q1 ∷
   re 23 5 (CK30 ∷ []) ∷
   rw 25 q2 ∷
   rw⁻ 24 q3 ∷
   re 23 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q4 ∷
   rw 24 q16 ∷
   rw⁻ 23 q4 ∷
   re 24 3 (CK31 ∷ []) ∷
   rw 24 q17 ∷
   rw 23 q3 ∷
   re 25 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   rw 25 q18 ∷
   rw 26 q4 ∷
   re 24 3 (CK30 ∷ []) ∷
   rw 25 q8 ∷
   rw 22 q2 ∷
   rw⁻ 21 q3 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q4 ∷
   rw 21 q5 ∷
   rw⁻ 20 q4 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 21 q6 ∷
   rw 20 q3 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q4 ∷
   rw 22 q7 ∷
   rw 23 q4 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 22 q8 ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q9 ∷
   re 25 3 (CX31 ∷ []) ∷
   rw 24 q10 ∷
   rw 23 q11 ∷
   rw 22 q12 ∷
   re 22 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 21 q1 ∷
   re 22 5 (CS03 ∷ []) ∷
   rw 24 q2 ∷
   rw⁻ 23 q3 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q4 ∷
   rw 23 q5 ∷
   rw⁻ 22 q4 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 23 q6 ∷
   rw 22 q3 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q4 ∷
   rw 24 q7 ∷
   rw 25 q4 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 24 q8 ∷
   rw 21 q2 ∷
   rw⁻ 20 q3 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q4 ∷
   rw 20 q5 ∷
   rw⁻ 19 q4 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 20 q6 ∷
   rw 19 q3 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q4 ∷
   rw 21 q7 ∷
   rw 22 q4 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 21 q8 ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q9 ∷
   re 24 3 (CX31 ∷ []) ∷
   rw 23 q10 ∷
   rw 22 q11 ∷
   rw 21 q12 ∷
   re 21 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 20 q1 ∷
   re 21 5 (CS03 ∷ []) ∷
   rw 23 q2 ∷
   rw⁻ 22 q3 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q4 ∷
   rw 22 q5 ∷
   rw⁻ 21 q4 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 22 q6 ∷
   rw 21 q3 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   rw 23 q7 ∷
   rw 24 q4 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 23 q8 ∷
   rw 20 q2 ∷
   rw⁻ 19 q3 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q4 ∷
   rw 19 q5 ∷
   rw⁻ 18 q4 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 19 q6 ∷
   rw 18 q3 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q4 ∷
   rw 20 q7 ∷
   rw 21 q4 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 20 q8 ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q9 ∷
   re 23 3 (CX31 ∷ []) ∷
   rw 22 q10 ∷
   rw 21 q11 ∷
   rw 20 q12 ∷
   re 20 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 19 q1 ∷
   re 20 5 (CS03 ∷ []) ∷
   rw 22 q2 ∷
   rw⁻ 21 q3 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q4 ∷
   rw 21 q5 ∷
   rw⁻ 20 q4 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 21 q6 ∷
   rw 20 q3 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q4 ∷
   rw 22 q7 ∷
   rw 23 q4 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 22 q8 ∷
   rw⁻ 17 q14 ∷
   rw⁻ 18 q15 ∷
   rw⁻ 19 q14 ∷
   rw 18 q2 ∷
   rw⁻ 17 q3 ∷
   re 16 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q4 ∷
   rw 17 q16 ∷
   rw⁻ 16 q4 ∷
   re 17 3 (CK31 ∷ []) ∷
   rw 17 q17 ∷
   rw 16 q3 ∷
   re 18 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 17 q4 ∷
   rw 18 q18 ∷
   rw 19 q4 ∷
   re 17 3 (CK30 ∷ []) ∷
   rw 18 q8 ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q9 ∷
   re 21 3 (CX31 ∷ []) ∷
   rw 20 q10 ∷
   rw 19 q19 ∷
   rw 18 q12 ∷
   re 18 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 17 q1 ∷
   re 18 5 (CK30 ∷ []) ∷
   rw 20 q2 ∷
   rw⁻ 19 q3 ∷
   re 18 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q4 ∷
   rw 19 q16 ∷
   rw⁻ 18 q4 ∷
   re 19 3 (CK31 ∷ []) ∷
   rw 19 q17 ∷
   rw 18 q3 ∷
   re 20 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 19 q4 ∷
   rw 20 q18 ∷
   rw 21 q4 ∷
   re 19 3 (CK30 ∷ []) ∷
   rw 20 q8 ∷
   rw⁻ 15 q14 ∷
   rw⁻ 16 q15 ∷
   rw⁻ 17 q14 ∷
   rw 16 q2 ∷
   rw⁻ 15 q3 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q4 ∷ []) Eq.refl

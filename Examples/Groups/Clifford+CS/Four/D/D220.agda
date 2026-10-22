{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D220 (W : Ws) where

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
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 113 W
  q3 : Eqn
  q3 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q4 : Eqn
  q4 = wE 114 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 5 W
  q7 : Eqn
  q7 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q8 : Eqn
  q8 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q9 : Eqn
  q9 = wE 7 W
  q10 : Eqn
  q10 = wE 629 W
  q11 : Eqn
  q11 = wE 27 W
  q12 : Eqn
  q12 = wE 31 W
  q13 : Eqn
  q13 = wE 140 W
  q14 : Eqn
  q14 = wE 630 W
  q15 : Eqn
  q15 = wE 142 W
  q16 : Eqn
  q16 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q17 : Eqn
  q17 = wE 673 W

-- Bar(SSSKSS;2,3->0) passes white iX via V2 conjugates 1 part2: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part2 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ X2 ∷ CS03 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ CX21 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part2 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ X2 ∷ CS03 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ CX21 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ [])
  (re 38 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   re 42 3 (CX31 ∷ []) ∷
   rw 41 q2 ∷
   rw 40 q3 ∷
   rw 39 q4 ∷
   re 39 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 38 q5 ∷
   re 39 5 (CS03 ∷ []) ∷
   rw 41 q6 ∷
   rw⁻ 40 q7 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q8 ∷
   rw 40 q9 ∷
   rw⁻ 39 q8 ∷
   re 40 3 (CS13 ∷ []) ∷
   rw 40 q10 ∷
   rw 39 q7 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q8 ∷
   rw 41 q11 ∷
   rw 42 q8 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q12 ∷
   rw 38 q6 ∷
   rw⁻ 37 q7 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q8 ∷
   rw 37 q9 ∷
   rw⁻ 36 q8 ∷
   re 37 3 (CS13 ∷ []) ∷
   rw 37 q10 ∷
   rw 36 q7 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q8 ∷
   rw 38 q11 ∷
   rw 39 q8 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 38 q12 ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   re 41 3 (CX31 ∷ []) ∷
   rw 40 q2 ∷
   rw 39 q3 ∷
   rw 38 q4 ∷
   re 38 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 37 q5 ∷
   re 38 5 (CS03 ∷ []) ∷
   rw 40 q6 ∷
   rw⁻ 39 q7 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q8 ∷
   rw 39 q9 ∷
   rw⁻ 38 q8 ∷
   re 39 3 (CS13 ∷ []) ∷
   rw 39 q10 ∷
   rw 38 q7 ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q8 ∷
   rw 40 q11 ∷
   rw 41 q8 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 40 q12 ∷
   rw 37 q6 ∷
   rw⁻ 36 q7 ∷
   re 35 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q8 ∷
   rw 36 q13 ∷
   rw⁻ 35 q8 ∷
   re 36 3 (CK31 ∷ []) ∷
   rw 36 q14 ∷
   rw 35 q7 ∷
   re 37 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 36 q8 ∷
   rw 37 q15 ∷
   rw 38 q8 ∷
   re 36 3 (CK30 ∷ []) ∷
   rw 37 q12 ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   re 40 3 (CX31 ∷ []) ∷
   rw 39 q2 ∷
   rw 38 q16 ∷
   rw 37 q4 ∷
   re 37 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 36 q5 ∷
   re 37 5 (CK30 ∷ []) ∷
   rw 39 q6 ∷
   rw⁻ 38 q7 ∷
   re 37 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q8 ∷
   rw 38 q13 ∷
   rw⁻ 37 q8 ∷
   re 38 3 (CK31 ∷ []) ∷
   rw 38 q14 ∷
   rw 37 q7 ∷
   re 39 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 38 q8 ∷
   rw 39 q15 ∷
   rw 40 q8 ∷
   re 38 3 (CK30 ∷ []) ∷
   rw 39 q12 ∷
   rw 36 q6 ∷
   rw⁻ 35 q7 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q8 ∷
   rw 35 q9 ∷
   rw⁻ 34 q8 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw 35 q10 ∷
   rw 34 q7 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q8 ∷
   rw 36 q11 ∷
   rw 37 q8 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q12 ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   re 39 3 (CX31 ∷ []) ∷
   rw 38 q2 ∷
   rw 37 q3 ∷
   rw 36 q4 ∷
   re 36 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 35 q5 ∷
   re 36 5 (CS03 ∷ []) ∷
   rw 38 q6 ∷
   rw⁻ 37 q7 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q8 ∷
   rw 37 q9 ∷
   rw⁻ 36 q8 ∷
   re 37 3 (CS13 ∷ []) ∷
   rw 37 q10 ∷
   rw 36 q7 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q8 ∷
   rw 38 q11 ∷
   rw 39 q8 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 38 q12 ∷
   rw 35 q6 ∷
   rw⁻ 34 q7 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q8 ∷
   rw 34 q9 ∷
   rw⁻ 33 q8 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw 34 q10 ∷
   rw 33 q7 ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q8 ∷
   rw 35 q11 ∷
   rw 36 q8 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 35 q12 ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   re 38 3 (CX31 ∷ []) ∷
   rw 37 q2 ∷
   rw 36 q3 ∷
   rw 35 q4 ∷
   re 35 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 34 q5 ∷
   re 35 5 (CS03 ∷ []) ∷
   rw 37 q6 ∷
   rw⁻ 36 q7 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q8 ∷
   rw 36 q9 ∷
   rw⁻ 35 q8 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 36 q10 ∷
   rw 35 q7 ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q8 ∷
   rw 37 q11 ∷
   rw 38 q8 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q12 ∷
   rw 34 q6 ∷
   rw⁻ 33 q7 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q8 ∷
   rw 33 q9 ∷
   rw⁻ 32 q8 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw 33 q10 ∷
   rw 32 q7 ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q8 ∷
   rw 34 q11 ∷
   rw 35 q8 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 34 q12 ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q1 ∷
   re 37 3 (CX31 ∷ []) ∷
   rw 36 q2 ∷
   rw 35 q3 ∷
   rw 34 q4 ∷
   re 34 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 33 q5 ∷
   re 34 5 (CS03 ∷ []) ∷
   rw 36 q6 ∷
   rw⁻ 35 q7 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q8 ∷
   rw 35 q9 ∷
   rw⁻ 34 q8 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw 35 q10 ∷
   rw 34 q7 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q8 ∷
   rw 36 q11 ∷
   rw 37 q8 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q12 ∷
   rw 31 q17 ∷
   rw 32 q6 ∷
   rw⁻ 31 q7 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q8 ∷
   rw 31 q9 ∷
   rw⁻ 30 q8 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 31 q10 ∷
   rw 30 q7 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q8 ∷
   rw 32 q11 ∷
   rw 33 q8 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 32 q12 ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q1 ∷
   re 35 3 (CX31 ∷ []) ∷
   rw 34 q2 ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   re 32 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 31 q5 ∷
   re 32 5 (CS03 ∷ []) ∷
   rw 34 q6 ∷
   rw⁻ 33 q7 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q8 ∷
   rw 33 q9 ∷
   rw⁻ 32 q8 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw 33 q10 ∷
   rw 32 q7 ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q8 ∷
   rw 34 q11 ∷
   rw 35 q8 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 34 q12 ∷
   rw 31 q6 ∷
   rw⁻ 30 q7 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q8 ∷
   rw 30 q9 ∷
   rw⁻ 29 q8 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw 30 q10 ∷
   rw 29 q7 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q8 ∷
   rw 31 q11 ∷
   rw 32 q8 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 31 q12 ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
   re 34 3 (CX31 ∷ []) ∷
   rw 33 q2 ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   re 31 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 30 q5 ∷
   re 31 5 (CS03 ∷ []) ∷
   rw 33 q6 ∷
   rw⁻ 32 q7 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q8 ∷
   rw 32 q9 ∷
   rw⁻ 31 q8 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw 32 q10 ∷
   rw 31 q7 ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q8 ∷
   rw 33 q11 ∷
   rw 34 q8 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 33 q12 ∷
   rw 30 q6 ∷
   rw⁻ 29 q7 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q8 ∷
   rw 29 q9 ∷
   rw⁻ 28 q8 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 29 q10 ∷
   rw 28 q7 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q8 ∷
   rw 30 q11 ∷
   rw 31 q8 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 30 q12 ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   re 33 3 (CX31 ∷ []) ∷
   rw 32 q2 ∷
   rw 31 q3 ∷
   rw 30 q4 ∷
   re 30 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 29 q5 ∷
   re 30 5 (CS03 ∷ []) ∷
   rw 32 q6 ∷
   rw⁻ 31 q7 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q8 ∷
   rw 31 q9 ∷
   rw⁻ 30 q8 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 31 q10 ∷
   rw 30 q7 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q8 ∷
   rw 32 q11 ∷
   rw 33 q8 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 32 q12 ∷
   rw 29 q6 ∷
   rw⁻ 28 q7 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q8 ∷
   rw 28 q9 ∷
   rw⁻ 27 q8 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 28 q10 ∷
   rw 27 q7 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q8 ∷
   rw 29 q11 ∷
   rw 30 q8 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 29 q12 ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   re 32 3 (CX31 ∷ []) ∷
   rw 31 q2 ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   re 29 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 28 q5 ∷
   re 29 5 (CS03 ∷ []) ∷
   rw 31 q6 ∷
   rw⁻ 30 q7 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q8 ∷
   rw 30 q9 ∷
   rw⁻ 29 q8 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw 30 q10 ∷
   rw 29 q7 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q8 ∷
   rw 31 q11 ∷
   rw 32 q8 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 31 q12 ∷
   rw 28 q6 ∷
   rw⁻ 27 q7 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q8 ∷
   rw 27 q9 ∷
   rw⁻ 26 q8 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 27 q10 ∷
   rw 26 q7 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q8 ∷
   rw 28 q11 ∷
   rw 29 q8 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 28 q12 ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CX31 ∷ []) ∷
   rw 30 q2 ∷
   rw 29 q3 ∷
   rw 28 q4 ∷
   re 28 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 27 q5 ∷
   re 28 5 (CS03 ∷ []) ∷
   rw 30 q6 ∷
   rw⁻ 29 q7 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q8 ∷
   rw 29 q9 ∷
   rw⁻ 28 q8 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 29 q10 ∷
   rw 28 q7 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q8 ∷
   rw 30 q11 ∷
   rw 31 q8 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 30 q12 ∷
   rw 27 q6 ∷
   rw⁻ 26 q7 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q8 ∷
   rw 26 q9 ∷
   rw⁻ 25 q8 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 26 q10 ∷
   rw 25 q7 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q8 ∷
   rw 27 q11 ∷
   rw 28 q8 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 27 q12 ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CX31 ∷ []) ∷
   rw 29 q2 ∷
   rw 28 q3 ∷
   rw 27 q4 ∷
   re 27 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 26 q5 ∷
   re 27 5 (CS03 ∷ []) ∷
   rw 29 q6 ∷
   rw⁻ 28 q7 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q8 ∷
   rw 28 q9 ∷
   rw⁻ 27 q8 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 28 q10 ∷
   rw 27 q7 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q8 ∷
   rw 29 q11 ∷
   rw 30 q8 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 29 q12 ∷
   rw 26 q6 ∷
   rw⁻ 25 q7 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q8 ∷
   rw 25 q9 ∷
   rw⁻ 24 q8 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 25 q10 ∷
   rw 24 q7 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q8 ∷
   rw 26 q11 ∷
   rw 27 q8 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 26 q12 ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   re 29 3 (CX31 ∷ []) ∷
   rw 28 q2 ∷
   rw 27 q3 ∷
   rw 26 q4 ∷
   re 26 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 25 q5 ∷
   re 26 5 (CS03 ∷ []) ∷
   rw 28 q6 ∷
   rw⁻ 27 q7 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q8 ∷
   rw 27 q9 ∷
   rw⁻ 26 q8 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 27 q10 ∷
   rw 26 q7 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q8 ∷
   rw 28 q11 ∷
   rw 29 q8 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 28 q12 ∷
   rw 25 q6 ∷
   rw⁻ 24 q7 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q8 ∷
   rw 24 q9 ∷
   rw⁻ 23 q8 ∷
   re 24 3 (CS13 ∷ []) ∷ []) Eq.refl

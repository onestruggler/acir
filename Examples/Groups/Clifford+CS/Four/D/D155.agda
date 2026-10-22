{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D155 (W : Ws) where

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
  q1 = wE 140 W
  q2 : Eqn
  q2 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = wE 630 W
  q4 : Eqn
  q4 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q5 : Eqn
  q5 = wE 142 W
  q6 : Eqn
  q6 = wE 31 W
  q7 : Eqn
  q7 = wE 5 W
  q8 : Eqn
  q8 = wE 7 W
  q9 : Eqn
  q9 = wE 629 W
  q10 : Eqn
  q10 = wE 27 W
  q11 : Eqn
  q11 = wE 1 W
  q12 : Eqn
  q12 = wE 21 W
  q13 : Eqn
  q13 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q14 : Eqn
  q14 = wE 51 W
  q15 : Eqn
  q15 = wE 3 W
  q16 : Eqn
  q16 = eqn (X2 ∷ S3 ∷ []) (S3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (S))
  q17 : Eqn
  q17 = eqn (CS12⁻ ∷ S3 ∷ []) (S3 ∷ CS12⁻ ∷ []) (low₃-comm (((CS • CS • CS) ↑)) (S))
  q18 : Eqn
  q18 = eqn (CK10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((CS • CS • CS)))
  q19 : Eqn
  q19 = wE 739 W
  q20 : Eqn
  q20 = wE 483 W
  q21 : Eqn
  q21 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q22 : Eqn
  q22 = eqn (CK10⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap))
  q23 : Eqn
  q23 = wE 484 W
  q24 : Eqn
  q24 = eqn (CS01⁻ ∷ CX23 ∷ []) (CX23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₀₁))
  q25 : Eqn
  q25 = eqn (CK10⁻ ∷ CX23 ∷ []) (CX23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₀₁))
  q26 : Eqn
  q26 = wE 464 W
  q27 : Eqn
  q27 = wE 485 W
  q28 : Eqn
  q28 = wE 151 W
  q29 : Eqn
  q29 = wE 113 W
  q30 : Eqn
  q30 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q31 : Eqn
  q31 = wE 114 W
  q32 : Eqn
  q32 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))

-- Bar(SSKSKK;2,3->0) passes white iX via V2 conjugates 1 part1: 500 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part1 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS12⁻ ∷ Sw23 ∷ CK20 ∷ Sw01 ∷ Sw23 ∷ X2 ∷ Sw01 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ X2 ∷ Sw23 ∷ CX31 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ X2 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part1 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS12⁻ ∷ Sw23 ∷ CK20 ∷ Sw01 ∷ Sw23 ∷ X2 ∷ Sw01 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ X2 ∷ Sw23 ∷ CX31 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ X2 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ [])
  (rw 17 q1 ∷
   rw⁻ 16 q2 ∷
   re 17 3 (CK31 ∷ []) ∷
   rw 17 q3 ∷
   rw 16 q4 ∷
   re 18 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   rw 18 q5 ∷
   rw 19 q2 ∷
   re 17 3 (CK30 ∷ []) ∷
   rw 18 q6 ∷
   rw 15 q7 ∷
   rw⁻ 14 q4 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q2 ∷
   rw 14 q8 ∷
   rw⁻ 13 q2 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 14 q9 ∷
   rw 13 q4 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q2 ∷
   rw 15 q10 ∷
   rw 16 q2 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q6 ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q11 ∷
   re 18 3 (CS13⁻ ∷ []) ∷
   rw 17 q12 ∷
   rw 16 q13 ∷
   rw 15 q14 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q15 ∷
   re 15 5 (CS03 ∷ []) ∷
   rw 17 q7 ∷
   rw⁻ 16 q4 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q2 ∷
   rw 16 q8 ∷
   rw⁻ 15 q2 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw 16 q9 ∷
   rw 15 q4 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q2 ∷
   rw 17 q10 ∷
   rw 18 q2 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 17 q6 ∷
   rw 14 q7 ∷
   rw⁻ 13 q4 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw 13 q8 ∷
   rw⁻ 12 q2 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 13 q9 ∷
   rw 12 q4 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q2 ∷
   rw 14 q10 ∷
   rw 15 q2 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q6 ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q11 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw 16 q12 ∷
   rw 15 q13 ∷
   rw 14 q14 ∷
   re 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q15 ∷
   re 14 5 (CS03 ∷ []) ∷
   rw 16 q7 ∷
   rw⁻ 15 q4 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q2 ∷
   rw 15 q8 ∷
   rw⁻ 14 q2 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw 15 q9 ∷
   rw 14 q4 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q2 ∷
   rw 16 q10 ∷
   rw 17 q2 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 16 q6 ∷
   rw 13 q7 ∷
   rw⁻ 12 q4 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q2 ∷
   rw 12 q8 ∷
   rw⁻ 11 q2 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 12 q9 ∷
   rw 11 q4 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   rw 13 q10 ∷
   rw 14 q2 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q6 ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q11 ∷
   re 16 3 (CS13⁻ ∷ []) ∷
   rw 15 q12 ∷
   rw 14 q13 ∷
   rw 13 q14 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q15 ∷
   re 13 5 (CS03 ∷ []) ∷
   rw 15 q7 ∷
   rw⁻ 14 q4 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q2 ∷
   rw 14 q8 ∷
   rw⁻ 13 q2 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 14 q9 ∷
   rw 13 q4 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q2 ∷
   rw 15 q10 ∷
   rw 16 q2 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q6 ∷
   rw⁻ 10 q16 ∷
   rw⁻ 11 q17 ∷
   rw⁻ 12 q16 ∷
   rw 11 q7 ∷
   rw⁻ 10 q4 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q2 ∷
   rw 10 q1 ∷
   rw⁻ 9 q2 ∷
   re 10 3 (CK31 ∷ []) ∷
   rw 10 q3 ∷
   rw 9 q4 ∷
   re 11 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   rw 11 q5 ∷
   rw 12 q2 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q6 ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q11 ∷
   re 14 3 (CS13⁻ ∷ []) ∷
   rw 13 q12 ∷
   rw 12 q18 ∷
   rw 11 q14 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q15 ∷
   re 11 5 (CK30 ∷ []) ∷
   rw 13 q7 ∷
   rw⁻ 12 q4 ∷
   re 11 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q2 ∷
   rw 12 q1 ∷
   rw⁻ 11 q2 ∷
   re 12 3 (CK31 ∷ []) ∷
   rw 12 q3 ∷
   rw 11 q4 ∷
   re 13 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   rw 13 q5 ∷
   rw 14 q2 ∷
   re 12 3 (CK30 ∷ []) ∷
   rw 13 q6 ∷
   rw⁻ 8 q16 ∷
   rw⁻ 9 q17 ∷
   rw⁻ 10 q16 ∷
   rw 9 q7 ∷
   rw⁻ 8 q4 ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q2 ∷
   rw 8 q1 ∷
   rw⁻ 7 q2 ∷
   re 8 3 (CK31 ∷ []) ∷
   rw 8 q3 ∷
   rw 7 q4 ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   rw 9 q5 ∷
   rw 10 q2 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q6 ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q11 ∷
   re 12 3 (CS13⁻ ∷ []) ∷
   rw 11 q12 ∷
   rw 10 q18 ∷
   rw 9 q14 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q15 ∷
   re 9 5 (CK30 ∷ []) ∷
   rw 11 q7 ∷
   rw⁻ 10 q4 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q2 ∷
   rw 10 q1 ∷
   rw⁻ 9 q2 ∷
   re 10 3 (CK31 ∷ []) ∷
   rw 10 q3 ∷
   rw 9 q4 ∷
   re 11 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   rw 11 q5 ∷
   rw 12 q2 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q6 ∷
   rw 6 q19 ∷
   rw 0 q20 ∷
   rw 36 q11 ∷
   rw 35 q21 ∷
   rw 34 q21 ∷
   rw 33 q22 ∷
   rw 32 q21 ∷
   re 31 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 33 q15 ∷
   re 30 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 32 q15 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q15 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q15 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q15 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q15 ∷
   rw 27 q23 ∷
   rw⁻ 26 q21 ∷
   rw⁻ 27 q22 ∷
   rw⁻ 28 q21 ∷
   rw⁻ 29 q21 ∷
   rw 32 q11 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 33 q11 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 34 q11 ∷
   re 32 3 (CK30 ∷ []) ∷
   rw 35 q11 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 36 q11 ∷
   re 34 3 (CK30 ∷ []) ∷
   rw 37 q11 ∷
   re 35 3 (CK30 ∷ []) ∷
   rw 36 q15 ∷
   rw⁻ 25 q24 ∷
   rw⁻ 26 q25 ∷
   rw⁻ 27 q24 ∷
   rw⁻ 28 q24 ∷
   rw 29 q11 ∷
   rw 28 q21 ∷
   rw 27 q21 ∷
   rw 26 q22 ∷
   rw 25 q21 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q15 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q15 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q15 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q15 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q15 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q15 ∷
   rw 18 q26 ∷
   re 17 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 19 q15 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q15 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q15 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q15 ∷
   rw 13 q26 ∷
   re 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 14 q15 ∷
   rw 11 q26 ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 12 q15 ∷
   rw 11 q27 ∷
   rw⁻ 10 q21 ∷
   rw⁻ 11 q22 ∷
   rw⁻ 12 q21 ∷
   rw⁻ 13 q21 ∷
   rw 16 q11 ∷
   re 14 3 (CK30 ∷ []) ∷
   rw 15 q28 ∷
   rw 18 q11 ∷
   re 16 3 (CK30 ∷ []) ∷
   rw 17 q28 ∷
   rw 20 q11 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 21 q11 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 22 q11 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 23 q11 ∷
   re 21 3 (CK30 ∷ []) ∷
   rw 22 q28 ∷
   rw 25 q11 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q11 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 27 q11 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 28 q11 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q11 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 30 q11 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 29 q15 ∷
   rw⁻ 9 q24 ∷
   rw⁻ 10 q25 ∷
   rw⁻ 11 q24 ∷
   rw⁻ 12 q24 ∷
   rw 3 q23 ∷
   rw 37 q7 ∷
   rw⁻ 36 q4 ∷
   re 35 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q2 ∷
   rw 36 q1 ∷
   rw⁻ 35 q2 ∷
   re 36 3 (CK31 ∷ []) ∷
   rw 36 q3 ∷
   rw 35 q4 ∷
   re 37 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   rw 37 q5 ∷
   rw 38 q2 ∷
   re 36 3 (CK30 ∷ []) ∷
   rw 37 q6 ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q11 ∷
   re 40 3 (CX31 ∷ []) ∷
   rw 39 q29 ∷
   rw 38 q30 ∷
   rw 37 q31 ∷
   re 37 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 36 q15 ∷
   re 37 5 (CK30 ∷ []) ∷
   rw 39 q7 ∷
   rw⁻ 38 q4 ∷
   re 37 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q2 ∷
   rw 38 q1 ∷
   rw⁻ 37 q2 ∷
   re 38 3 (CK31 ∷ []) ∷
   rw 38 q3 ∷
   rw 37 q4 ∷
   re 39 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 38 q2 ∷
   rw 39 q5 ∷
   rw 40 q2 ∷
   re 38 3 (CK30 ∷ []) ∷
   rw 39 q6 ∷
   rw 36 q7 ∷
   rw⁻ 35 q4 ∷
   re 34 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q2 ∷
   rw 35 q1 ∷
   rw⁻ 34 q2 ∷
   re 35 3 (CK31 ∷ []) ∷
   rw 35 q3 ∷
   rw 34 q4 ∷
   re 36 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   rw 36 q5 ∷
   rw 37 q2 ∷
   re 35 3 (CK30 ∷ []) ∷
   rw 36 q6 ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q11 ∷
   re 39 3 (CX31 ∷ []) ∷
   rw 38 q29 ∷
   rw 37 q30 ∷
   rw 36 q31 ∷
   re 36 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 35 q15 ∷
   re 36 5 (CK30 ∷ []) ∷
   rw 38 q7 ∷
   rw⁻ 37 q4 ∷
   re 36 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q2 ∷
   rw 37 q1 ∷
   rw⁻ 36 q2 ∷
   re 37 3 (CK31 ∷ []) ∷
   rw 37 q3 ∷
   rw 36 q4 ∷
   re 38 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 37 q2 ∷
   rw 38 q5 ∷
   rw 39 q2 ∷
   re 37 3 (CK30 ∷ []) ∷
   rw 38 q6 ∷
   rw 35 q7 ∷
   rw⁻ 34 q4 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q2 ∷
   rw 34 q8 ∷
   rw⁻ 33 q2 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw 34 q9 ∷
   rw 33 q4 ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   rw 35 q10 ∷
   rw 36 q2 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 35 q6 ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q11 ∷
   re 38 3 (CX31 ∷ []) ∷
   rw 37 q29 ∷
   rw 36 q32 ∷
   rw 35 q31 ∷
   re 35 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 34 q15 ∷
   re 35 5 (CS03 ∷ []) ∷
   rw 37 q7 ∷
   rw⁻ 36 q4 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q2 ∷
   rw 36 q8 ∷
   rw⁻ 35 q2 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 36 q9 ∷
   rw 35 q4 ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   rw 37 q10 ∷
   rw 38 q2 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q6 ∷
   rw 34 q7 ∷
   rw⁻ 33 q4 ∷
   re 32 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q2 ∷
   rw 33 q1 ∷
   rw⁻ 32 q2 ∷
   re 33 3 (CK31 ∷ []) ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   re 34 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 33 q2 ∷
   rw 34 q5 ∷
   rw 35 q2 ∷
   re 33 3 (CK30 ∷ []) ∷
   rw 34 q6 ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q11 ∷
   re 37 3 (CX31 ∷ []) ∷
   rw 36 q29 ∷
   rw 35 q30 ∷
   rw 34 q31 ∷
   re 34 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 33 q15 ∷
   re 34 5 (CK30 ∷ []) ∷
   rw 36 q7 ∷
   rw⁻ 35 q4 ∷
   re 34 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q2 ∷
   rw 35 q1 ∷
   rw⁻ 34 q2 ∷
   re 35 3 (CK31 ∷ []) ∷
   rw 35 q3 ∷
   rw 34 q4 ∷
   re 36 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   rw 36 q5 ∷
   rw 37 q2 ∷
   re 35 3 (CK30 ∷ []) ∷
   rw 36 q6 ∷
   rw 33 q7 ∷
   rw⁻ 32 q4 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q2 ∷
   rw 32 q8 ∷
   rw⁻ 31 q2 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw 32 q9 ∷
   rw 31 q4 ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q2 ∷
   rw 33 q10 ∷
   rw 34 q2 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 33 q6 ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q11 ∷
   re 36 3 (CX31 ∷ []) ∷
   rw 35 q29 ∷
   rw 34 q32 ∷
   rw 33 q31 ∷ []) Eq.refl

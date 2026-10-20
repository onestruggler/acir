{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D219 (W : Ws) where

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
  q9 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q10 : Eqn
  q10 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q11 : Eqn
  q11 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q12 : Eqn
  q12 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q13 : Eqn
  q13 = eqn (X2 ∷ S3 ∷ []) (S3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (S))
  q14 : Eqn
  q14 = eqn (CS12⁻ ∷ S3 ∷ []) (S3 ∷ CS12⁻ ∷ []) (low₃-comm (((CS • CS • CS) ↑)) (S))
  q15 : Eqn
  q15 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q16 : Eqn
  q16 = eqn (CK31 ∷ X2 ∷ []) (X2 ∷ CK31 ∷ []) (wn 630 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q18 : Eqn
  q18 = eqn (CK10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((CS • CS • CS)))
  q19 : Eqn
  q19 = eqn (CX23 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CX23 ∷ []) (wn 739 W)
  q20 : Eqn
  q20 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (wn 554 W)
  q21 : Eqn
  q21 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q22 : Eqn
  q22 = eqn (CK10⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap))
  q23 : Eqn
  q23 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (wn 555 W)
  q24 : Eqn
  q24 = eqn (CS01⁻ ∷ CX23 ∷ []) (CX23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₀₁))
  q25 : Eqn
  q25 = eqn (CK10⁻ ∷ CX23 ∷ []) (CX23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₀₁))
  q26 : Eqn
  q26 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q27 : Eqn
  q27 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (wn 556 W)
  q28 : Eqn
  q28 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)

-- Bar(SSSKSS;2,3->0) passes white iX via V2 conjugates 1 part1: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part1 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS12⁻ ∷ Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ X2 ∷ CS03 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part1 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS12⁻ ∷ Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ X2 ∷ CS03 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ [])
  (rw 20 q1 ∷
   rw 19 q2 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   rw 21 q4 ∷
   rw 22 q3 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 21 q5 ∷
   rw 18 q6 ∷
   rw⁻ 17 q2 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q3 ∷
   rw 17 q7 ∷
   rw⁻ 16 q3 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 17 q1 ∷
   rw 16 q2 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   rw 18 q4 ∷
   rw 19 q3 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 18 q5 ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q8 ∷
   re 21 3 (CS13⁻ ∷ []) ∷
   rw 20 q9 ∷
   rw 19 q10 ∷
   rw 18 q11 ∷
   re 18 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q12 ∷
   re 18 5 (CS03 ∷ []) ∷
   rw 20 q6 ∷
   rw⁻ 19 q2 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q3 ∷
   rw 19 q7 ∷
   rw⁻ 18 q3 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 19 q1 ∷
   rw 18 q2 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   rw 20 q4 ∷
   rw 21 q3 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 20 q5 ∷
   rw 17 q6 ∷
   rw⁻ 16 q2 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q3 ∷
   rw 16 q7 ∷
   rw⁻ 15 q3 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw 16 q1 ∷
   rw 15 q2 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q3 ∷
   rw 17 q4 ∷
   rw 18 q3 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 17 q5 ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q8 ∷
   re 20 3 (CS13⁻ ∷ []) ∷
   rw 19 q9 ∷
   rw 18 q10 ∷
   rw 17 q11 ∷
   re 17 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q12 ∷
   re 17 5 (CS03 ∷ []) ∷
   rw 19 q6 ∷
   rw⁻ 18 q2 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q3 ∷
   rw 18 q7 ∷
   rw⁻ 17 q3 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 18 q1 ∷
   rw 17 q2 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   rw 19 q4 ∷
   rw 20 q3 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 19 q5 ∷
   rw⁻ 14 q13 ∷
   rw⁻ 15 q14 ∷
   rw⁻ 16 q13 ∷
   rw 15 q6 ∷
   rw⁻ 14 q2 ∷
   re 13 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q3 ∷
   rw 14 q15 ∷
   rw⁻ 13 q3 ∷
   re 14 3 (CK31 ∷ []) ∷
   rw 14 q16 ∷
   rw 13 q2 ∷
   re 15 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 14 q3 ∷
   rw 15 q17 ∷
   rw 16 q3 ∷
   re 14 3 (CK30 ∷ []) ∷
   rw 15 q5 ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q8 ∷
   re 18 3 (CS13⁻ ∷ []) ∷
   rw 17 q9 ∷
   rw 16 q18 ∷
   rw 15 q11 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q12 ∷
   re 15 5 (CK30 ∷ []) ∷
   rw 17 q6 ∷
   rw⁻ 16 q2 ∷
   re 15 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q3 ∷
   rw 16 q15 ∷
   rw⁻ 15 q3 ∷
   re 16 3 (CK31 ∷ []) ∷
   rw 16 q16 ∷
   rw 15 q2 ∷
   re 17 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 16 q3 ∷
   rw 17 q17 ∷
   rw 18 q3 ∷
   re 16 3 (CK30 ∷ []) ∷
   rw 17 q5 ∷
   rw 14 q6 ∷
   rw⁻ 13 q2 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q3 ∷
   rw 13 q7 ∷
   rw⁻ 12 q3 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 13 q1 ∷
   rw 12 q2 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q3 ∷
   rw 14 q4 ∷
   rw 15 q3 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q5 ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q8 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw 16 q9 ∷
   rw 15 q10 ∷
   rw 14 q11 ∷
   re 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q12 ∷
   re 14 5 (CS03 ∷ []) ∷
   rw 16 q6 ∷
   rw⁻ 15 q2 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q3 ∷
   rw 15 q7 ∷
   rw⁻ 14 q3 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw 15 q1 ∷
   rw 14 q2 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   rw 16 q4 ∷
   rw 17 q3 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 16 q5 ∷
   rw 13 q6 ∷
   rw⁻ 12 q2 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q3 ∷
   rw 12 q7 ∷
   rw⁻ 11 q3 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 12 q1 ∷
   rw 11 q2 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q3 ∷
   rw 13 q4 ∷
   rw 14 q3 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q5 ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q8 ∷
   re 16 3 (CS13⁻ ∷ []) ∷
   rw 15 q9 ∷
   rw 14 q10 ∷
   rw 13 q11 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q12 ∷
   re 13 5 (CS03 ∷ []) ∷
   rw 15 q6 ∷
   rw⁻ 14 q2 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q3 ∷
   rw 14 q7 ∷
   rw⁻ 13 q3 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 14 q1 ∷
   rw 13 q2 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q3 ∷
   rw 15 q4 ∷
   rw 16 q3 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q5 ∷
   rw 12 q6 ∷
   rw⁻ 11 q2 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q3 ∷
   rw 11 q7 ∷
   rw⁻ 10 q3 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 11 q1 ∷
   rw 10 q2 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q3 ∷
   rw 12 q4 ∷
   rw 13 q3 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q5 ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q8 ∷
   re 15 3 (CS13⁻ ∷ []) ∷
   rw 14 q9 ∷
   rw 13 q10 ∷
   rw 12 q11 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q12 ∷
   re 12 5 (CS03 ∷ []) ∷
   rw 14 q6 ∷
   rw⁻ 13 q2 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q3 ∷
   rw 13 q7 ∷
   rw⁻ 12 q3 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 13 q1 ∷
   rw 12 q2 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q3 ∷
   rw 14 q4 ∷
   rw 15 q3 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q5 ∷
   rw 11 q6 ∷
   rw⁻ 10 q2 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q3 ∷
   rw 10 q7 ∷
   rw⁻ 9 q3 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 10 q1 ∷
   rw 9 q2 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q3 ∷
   rw 11 q4 ∷
   rw 12 q3 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q5 ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q8 ∷
   re 14 3 (CS13⁻ ∷ []) ∷
   rw 13 q9 ∷
   rw 12 q10 ∷
   rw 11 q11 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q12 ∷
   re 11 5 (CS03 ∷ []) ∷
   rw 13 q6 ∷
   rw⁻ 12 q2 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q3 ∷
   rw 12 q7 ∷
   rw⁻ 11 q3 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 12 q1 ∷
   rw 11 q2 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q3 ∷
   rw 13 q4 ∷
   rw 14 q3 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q5 ∷
   rw 10 q6 ∷
   rw⁻ 9 q2 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q3 ∷
   rw 9 q7 ∷
   rw⁻ 8 q3 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 9 q1 ∷
   rw 8 q2 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q3 ∷
   rw 10 q4 ∷
   rw 11 q3 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q5 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q8 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw 12 q9 ∷
   rw 11 q10 ∷
   rw 10 q11 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   re 10 5 (CS03 ∷ []) ∷
   rw 12 q6 ∷
   rw⁻ 11 q2 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q3 ∷
   rw 11 q7 ∷
   rw⁻ 10 q3 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 11 q1 ∷
   rw 10 q2 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q3 ∷
   rw 12 q4 ∷
   rw 13 q3 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q5 ∷
   rw 9 q6 ∷
   rw⁻ 8 q2 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q3 ∷
   rw 8 q7 ∷
   rw⁻ 7 q3 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 8 q1 ∷
   rw 7 q2 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   rw 9 q4 ∷
   rw 10 q3 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q5 ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q8 ∷
   re 12 3 (CS13⁻ ∷ []) ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw 9 q11 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q12 ∷
   re 9 5 (CS03 ∷ []) ∷
   rw 11 q6 ∷
   rw⁻ 10 q2 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q3 ∷
   rw 10 q7 ∷
   rw⁻ 9 q3 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 10 q1 ∷
   rw 9 q2 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q3 ∷
   rw 11 q4 ∷
   rw 12 q3 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q5 ∷
   rw 6 q19 ∷
   rw 0 q20 ∷
   rw 38 q8 ∷
   rw 37 q21 ∷
   rw 36 q21 ∷
   rw 35 q22 ∷
   rw 34 q21 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q12 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q12 ∷
   re 31 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 33 q12 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q12 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q12 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q12 ∷
   rw 29 q23 ∷
   rw⁻ 28 q21 ∷
   rw⁻ 29 q22 ∷
   rw⁻ 30 q21 ∷
   rw⁻ 31 q21 ∷
   rw 34 q8 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 35 q8 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 36 q8 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 37 q8 ∷
   re 35 3 (CK30 ∷ []) ∷
   rw 38 q8 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 39 q8 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 38 q12 ∷
   rw⁻ 27 q24 ∷
   rw⁻ 28 q25 ∷
   rw⁻ 29 q24 ∷
   rw⁻ 30 q24 ∷
   rw 31 q8 ∷
   rw 30 q21 ∷
   rw 29 q21 ∷
   rw 28 q22 ∷
   rw 27 q21 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q12 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q12 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q12 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q12 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q12 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q12 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q12 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q12 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q12 ∷
   rw 17 q26 ∷
   re 16 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 18 q12 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q12 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q12 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q12 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q12 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q12 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q12 ∷
   rw 11 q27 ∷
   rw⁻ 10 q21 ∷
   rw⁻ 11 q22 ∷
   rw⁻ 12 q21 ∷
   rw⁻ 13 q21 ∷
   rw 16 q8 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 17 q8 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 18 q8 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 19 q8 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 20 q8 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 21 q8 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 22 q8 ∷
   re 20 3 (CK30 ∷ []) ∷
   rw 21 q28 ∷
   rw 24 q8 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 25 q8 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q8 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 27 q8 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 28 q8 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q8 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 30 q8 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 31 q8 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q8 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 31 q12 ∷
   rw⁻ 9 q24 ∷
   rw⁻ 10 q25 ∷
   rw⁻ 11 q24 ∷
   rw⁻ 12 q24 ∷
   rw 3 q23 ∷
   rw 39 q6 ∷
   rw⁻ 38 q2 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q3 ∷
   rw 38 q7 ∷
   rw⁻ 37 q3 ∷
   re 38 3 (CS13 ∷ []) ∷
   rw 38 q1 ∷
   rw 37 q2 ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q3 ∷
   rw 39 q4 ∷
   rw 40 q3 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 39 q5 ∷ []) Eq.refl

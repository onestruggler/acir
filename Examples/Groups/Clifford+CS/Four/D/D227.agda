{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D227 (W : Ws) where

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
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q3 : Eqn
  q3 = eqn (CS01⁻ ∷ CX23 ∷ []) (CX23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₀₁))
  q4 : Eqn
  q4 = eqn (S1⁻ ∷ CX23 ∷ []) (CX23 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (CX₀₁))
  q5 : Eqn
  q5 = eqn (CK10⁻ ∷ CX23 ∷ []) (CX23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₀₁))
  q6 : Eqn
  q6 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (wn 558 W)
  q7 : Eqn
  q7 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q8 : Eqn
  q8 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q9 : Eqn
  q9 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q10 : Eqn
  q10 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q11 : Eqn
  q11 = eqn (CS13 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ []) (wn 629 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q14 : Eqn
  q14 = eqn (Sw12 ∷ CX31 ∷ []) (CX32 ∷ Sw12 ∷ []) (wn 113 W)
  q15 : Eqn
  q15 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q16 : Eqn
  q16 = eqn (Sw12 ∷ CX32 ∷ []) (CX31 ∷ Sw12 ∷ []) (wn 114 W)
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

-- Bar(SSSKSS;2,3->0) passes white iX via V2 conjugates 1 part9: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part9 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ CX21 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part9 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ CX21 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ [])
  (re 69 3 (CS03 ∷ []) ∷
   rw 72 q1 ∷
   re 70 3 (CS03 ∷ []) ∷
   rw 73 q1 ∷
   re 71 3 (CS03 ∷ []) ∷
   rw 74 q1 ∷
   re 72 3 (CS03 ∷ []) ∷
   rw 75 q1 ∷
   re 73 3 (CS03 ∷ []) ∷
   rw 76 q1 ∷
   re 74 3 (CS03 ∷ []) ∷
   rw 77 q1 ∷
   re 75 3 (CS03 ∷ []) ∷
   rw 78 q1 ∷
   re 76 3 (CS03 ∷ []) ∷
   rw 77 q2 ∷
   rw⁻ 48 q3 ∷
   rw⁻ 49 q3 ∷
   rw⁻ 50 q3 ∷
   rw⁻ 51 q3 ∷
   rw⁻ 52 q3 ∷
   rw⁻ 53 q3 ∷
   rw⁻ 54 q4 ∷
   rw⁻ 55 q5 ∷
   rw⁻ 56 q3 ∷
   rw⁻ 57 q3 ∷
   rw⁻ 58 q3 ∷
   rw 42 q6 ∷
   rw 85 q7 ∷
   rw⁻ 84 q8 ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 85 q9 ∷
   rw 84 q10 ∷
   rw⁻ 83 q9 ∷
   re 84 3 (CS13 ∷ []) ∷
   rw 84 q11 ∷
   rw 83 q8 ∷
   re 85 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 84 q9 ∷
   rw 85 q12 ∷
   rw 86 q9 ∷
   re 84 3 (CS03 ∷ []) ∷
   rw 85 q13 ∷
   re 84 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 90 q1 ∷
   re 88 3 (CX31 ∷ []) ∷
   rw 87 q14 ∷
   rw 86 q15 ∷
   rw 85 q16 ∷
   re 85 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 84 q2 ∷
   re 85 5 (CS03 ∷ []) ∷
   rw 87 q7 ∷
   rw⁻ 86 q8 ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 87 q9 ∷
   rw 86 q10 ∷
   rw⁻ 85 q9 ∷
   re 86 3 (CS13 ∷ []) ∷
   rw 86 q11 ∷
   rw 85 q8 ∷
   re 87 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 86 q9 ∷
   rw 87 q12 ∷
   rw 88 q9 ∷
   re 86 3 (CS03 ∷ []) ∷
   rw 87 q13 ∷
   rw 84 q7 ∷
   rw⁻ 83 q8 ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 84 q9 ∷
   rw 83 q10 ∷
   rw⁻ 82 q9 ∷
   re 83 3 (CS13 ∷ []) ∷
   rw 83 q11 ∷
   rw 82 q8 ∷
   re 84 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 83 q9 ∷
   rw 84 q12 ∷
   rw 85 q9 ∷
   re 83 3 (CS03 ∷ []) ∷
   rw 84 q13 ∷
   re 83 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 89 q1 ∷
   re 87 3 (CX31 ∷ []) ∷
   rw 86 q14 ∷
   rw 85 q15 ∷
   rw 84 q16 ∷
   re 84 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 83 q2 ∷
   re 84 5 (CS03 ∷ []) ∷
   rw 86 q7 ∷
   rw⁻ 85 q8 ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 86 q9 ∷
   rw 85 q10 ∷
   rw⁻ 84 q9 ∷
   re 85 3 (CS13 ∷ []) ∷
   rw 85 q11 ∷
   rw 84 q8 ∷
   re 86 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 85 q9 ∷
   rw 86 q12 ∷
   rw 87 q9 ∷
   re 85 3 (CS03 ∷ []) ∷
   rw 86 q13 ∷
   rw 83 q7 ∷
   rw⁻ 82 q8 ∷
   re 81 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 83 q9 ∷
   rw 82 q17 ∷
   rw⁻ 81 q9 ∷
   re 82 3 (CK31 ∷ []) ∷
   rw 82 q18 ∷
   rw 81 q8 ∷
   re 83 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 82 q9 ∷
   rw 83 q19 ∷
   rw 84 q9 ∷
   re 82 3 (CK30 ∷ []) ∷
   rw 83 q13 ∷
   re 82 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 88 q1 ∷
   re 86 3 (CX31 ∷ []) ∷
   rw 85 q14 ∷
   rw 84 q20 ∷
   rw 83 q16 ∷
   re 83 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 82 q2 ∷
   re 83 5 (CK30 ∷ []) ∷
   rw 85 q7 ∷
   rw⁻ 84 q8 ∷
   re 83 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 85 q9 ∷
   rw 84 q17 ∷
   rw⁻ 83 q9 ∷
   re 84 3 (CK31 ∷ []) ∷
   rw 84 q18 ∷
   rw 83 q8 ∷
   re 85 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 84 q9 ∷
   rw 85 q19 ∷
   rw 86 q9 ∷
   re 84 3 (CK30 ∷ []) ∷
   rw 85 q13 ∷
   rw 82 q7 ∷
   rw⁻ 81 q8 ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 82 q9 ∷
   rw 81 q10 ∷
   rw⁻ 80 q9 ∷
   re 81 3 (CS13 ∷ []) ∷
   rw 81 q11 ∷
   rw 80 q8 ∷
   re 82 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 81 q9 ∷
   rw 82 q12 ∷
   rw 83 q9 ∷
   re 81 3 (CS03 ∷ []) ∷
   rw 82 q13 ∷
   re 81 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 87 q1 ∷
   re 85 3 (CX31 ∷ []) ∷
   rw 84 q14 ∷
   rw 83 q15 ∷
   rw 82 q16 ∷
   re 82 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 81 q2 ∷
   re 82 5 (CS03 ∷ []) ∷
   rw 84 q7 ∷
   rw⁻ 83 q8 ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 84 q9 ∷
   rw 83 q10 ∷
   rw⁻ 82 q9 ∷
   re 83 3 (CS13 ∷ []) ∷
   rw 83 q11 ∷
   rw 82 q8 ∷
   re 84 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 83 q9 ∷
   rw 84 q12 ∷
   rw 85 q9 ∷
   re 83 3 (CS03 ∷ []) ∷
   rw 84 q13 ∷
   rw 81 q7 ∷
   rw⁻ 80 q8 ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 81 q9 ∷
   rw 80 q10 ∷
   rw⁻ 79 q9 ∷
   re 80 3 (CS13 ∷ []) ∷
   rw 80 q11 ∷
   rw 79 q8 ∷
   re 81 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 80 q9 ∷
   rw 81 q12 ∷
   rw 82 q9 ∷
   re 80 3 (CS03 ∷ []) ∷
   rw 81 q13 ∷
   re 80 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 86 q1 ∷
   re 84 3 (CX31 ∷ []) ∷
   rw 83 q14 ∷
   rw 82 q15 ∷
   rw 81 q16 ∷
   re 81 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 80 q2 ∷
   re 81 5 (CS03 ∷ []) ∷
   rw 83 q7 ∷
   rw⁻ 82 q8 ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 83 q9 ∷
   rw 82 q10 ∷
   rw⁻ 81 q9 ∷
   re 82 3 (CS13 ∷ []) ∷
   rw 82 q11 ∷
   rw 81 q8 ∷
   re 83 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 82 q9 ∷
   rw 83 q12 ∷
   rw 84 q9 ∷
   re 82 3 (CS03 ∷ []) ∷
   rw 83 q13 ∷
   rw 80 q7 ∷
   rw⁻ 79 q8 ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 80 q9 ∷
   rw 79 q10 ∷
   rw⁻ 78 q9 ∷
   re 79 3 (CS13 ∷ []) ∷
   rw 79 q11 ∷
   rw 78 q8 ∷
   re 80 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 79 q9 ∷
   rw 80 q12 ∷
   rw 81 q9 ∷
   re 79 3 (CS03 ∷ []) ∷
   rw 80 q13 ∷
   re 79 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 85 q1 ∷
   re 83 3 (CX31 ∷ []) ∷
   rw 82 q14 ∷
   rw 81 q15 ∷
   rw 80 q16 ∷
   re 80 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 79 q2 ∷
   re 80 5 (CS03 ∷ []) ∷
   rw 82 q7 ∷
   rw⁻ 81 q8 ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 82 q9 ∷
   rw 81 q10 ∷
   rw⁻ 80 q9 ∷
   re 81 3 (CS13 ∷ []) ∷
   rw 81 q11 ∷
   rw 80 q8 ∷
   re 82 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 81 q9 ∷
   rw 82 q12 ∷
   rw 83 q9 ∷
   re 81 3 (CS03 ∷ []) ∷
   rw 82 q13 ∷
   rw 77 q21 ∷
   rw 78 q7 ∷
   rw⁻ 77 q8 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 78 q9 ∷
   rw 77 q10 ∷
   rw⁻ 76 q9 ∷
   re 77 3 (CS13 ∷ []) ∷
   rw 77 q11 ∷
   rw 76 q8 ∷
   re 78 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 77 q9 ∷
   rw 78 q12 ∷
   rw 79 q9 ∷
   re 77 3 (CS03 ∷ []) ∷
   rw 78 q13 ∷
   re 77 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 83 q1 ∷
   re 81 3 (CX31 ∷ []) ∷
   rw 80 q14 ∷
   rw 79 q15 ∷
   rw 78 q16 ∷
   re 78 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 77 q2 ∷
   re 78 5 (CS03 ∷ []) ∷
   rw 80 q7 ∷
   rw⁻ 79 q8 ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 80 q9 ∷
   rw 79 q10 ∷
   rw⁻ 78 q9 ∷
   re 79 3 (CS13 ∷ []) ∷
   rw 79 q11 ∷
   rw 78 q8 ∷
   re 80 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 79 q9 ∷
   rw 80 q12 ∷
   rw 81 q9 ∷
   re 79 3 (CS03 ∷ []) ∷
   rw 80 q13 ∷
   rw 77 q7 ∷
   rw⁻ 76 q8 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 77 q9 ∷
   rw 76 q10 ∷
   rw⁻ 75 q9 ∷
   re 76 3 (CS13 ∷ []) ∷
   rw 76 q11 ∷
   rw 75 q8 ∷
   re 77 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 76 q9 ∷
   rw 77 q12 ∷
   rw 78 q9 ∷
   re 76 3 (CS03 ∷ []) ∷
   rw 77 q13 ∷
   re 76 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 82 q1 ∷
   re 80 3 (CX31 ∷ []) ∷
   rw 79 q14 ∷
   rw 78 q15 ∷
   rw 77 q16 ∷
   re 77 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 76 q2 ∷
   re 77 5 (CS03 ∷ []) ∷
   rw 79 q7 ∷
   rw⁻ 78 q8 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 79 q9 ∷
   rw 78 q10 ∷
   rw⁻ 77 q9 ∷
   re 78 3 (CS13 ∷ []) ∷
   rw 78 q11 ∷
   rw 77 q8 ∷
   re 79 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 78 q9 ∷
   rw 79 q12 ∷
   rw 80 q9 ∷
   re 78 3 (CS03 ∷ []) ∷
   rw 79 q13 ∷
   rw 76 q7 ∷
   rw⁻ 75 q8 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 76 q9 ∷
   rw 75 q10 ∷
   rw⁻ 74 q9 ∷
   re 75 3 (CS13 ∷ []) ∷
   rw 75 q11 ∷
   rw 74 q8 ∷
   re 76 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 75 q9 ∷
   rw 76 q12 ∷
   rw 77 q9 ∷
   re 75 3 (CS03 ∷ []) ∷
   rw 76 q13 ∷
   re 75 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 81 q1 ∷
   re 79 3 (CX31 ∷ []) ∷
   rw 78 q14 ∷
   rw 77 q15 ∷
   rw 76 q16 ∷
   re 76 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 75 q2 ∷
   re 76 5 (CS03 ∷ []) ∷
   rw 78 q7 ∷
   rw⁻ 77 q8 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 78 q9 ∷
   rw 77 q10 ∷
   rw⁻ 76 q9 ∷
   re 77 3 (CS13 ∷ []) ∷
   rw 77 q11 ∷
   rw 76 q8 ∷
   re 78 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 77 q9 ∷
   rw 78 q12 ∷
   rw 79 q9 ∷
   re 77 3 (CS03 ∷ []) ∷
   rw 78 q13 ∷
   rw 75 q7 ∷
   rw⁻ 74 q8 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 75 q9 ∷
   rw 74 q10 ∷
   rw⁻ 73 q9 ∷
   re 74 3 (CS13 ∷ []) ∷
   rw 74 q11 ∷
   rw 73 q8 ∷
   re 75 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 74 q9 ∷
   rw 75 q12 ∷
   rw 76 q9 ∷
   re 74 3 (CS03 ∷ []) ∷
   rw 75 q13 ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 80 q1 ∷
   re 78 3 (CX31 ∷ []) ∷
   rw 77 q14 ∷
   rw 76 q15 ∷
   rw 75 q16 ∷
   re 75 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 74 q2 ∷
   re 75 5 (CS03 ∷ []) ∷
   rw 77 q7 ∷
   rw⁻ 76 q8 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 77 q9 ∷
   rw 76 q10 ∷
   rw⁻ 75 q9 ∷
   re 76 3 (CS13 ∷ []) ∷
   rw 76 q11 ∷
   rw 75 q8 ∷
   re 77 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 76 q9 ∷
   rw 77 q12 ∷
   rw 78 q9 ∷
   re 76 3 (CS03 ∷ []) ∷
   rw 77 q13 ∷
   rw 74 q7 ∷
   rw⁻ 73 q8 ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 74 q9 ∷
   rw 73 q10 ∷
   rw⁻ 72 q9 ∷
   re 73 3 (CS13 ∷ []) ∷
   rw 73 q11 ∷
   rw 72 q8 ∷
   re 74 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 73 q9 ∷
   rw 74 q12 ∷
   rw 75 q9 ∷
   re 73 3 (CS03 ∷ []) ∷
   rw 74 q13 ∷
   re 73 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 79 q1 ∷
   re 77 3 (CX31 ∷ []) ∷
   rw 76 q14 ∷
   rw 75 q15 ∷
   rw 74 q16 ∷
   re 74 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 73 q2 ∷
   re 74 5 (CS03 ∷ []) ∷
   rw 76 q7 ∷
   rw⁻ 75 q8 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 76 q9 ∷
   rw 75 q10 ∷
   rw⁻ 74 q9 ∷
   re 75 3 (CS13 ∷ []) ∷
   rw 75 q11 ∷
   rw 74 q8 ∷
   re 76 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 75 q9 ∷
   rw 76 q12 ∷
   rw 77 q9 ∷
   re 75 3 (CS03 ∷ []) ∷
   rw 76 q13 ∷
   rw 73 q7 ∷
   rw⁻ 72 q8 ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 73 q9 ∷
   rw 72 q10 ∷
   rw⁻ 71 q9 ∷
   re 72 3 (CS13 ∷ []) ∷
   rw 72 q11 ∷
   rw 71 q8 ∷
   re 73 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 72 q9 ∷
   rw 73 q12 ∷
   rw 74 q9 ∷
   re 72 3 (CS03 ∷ []) ∷
   rw 73 q13 ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 78 q1 ∷
   re 76 3 (CX31 ∷ []) ∷
   rw 75 q14 ∷
   rw 74 q15 ∷
   rw 73 q16 ∷
   re 73 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 72 q2 ∷
   re 73 5 (CS03 ∷ []) ∷
   rw 75 q7 ∷
   rw⁻ 74 q8 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 75 q9 ∷
   rw 74 q10 ∷
   rw⁻ 73 q9 ∷
   re 74 3 (CS13 ∷ []) ∷
   rw 74 q11 ∷
   rw 73 q8 ∷
   re 75 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 74 q9 ∷
   rw 75 q12 ∷
   rw 76 q9 ∷
   re 74 3 (CS03 ∷ []) ∷
   rw 75 q13 ∷
   rw 72 q7 ∷
   rw⁻ 71 q8 ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷ []) Eq.refl

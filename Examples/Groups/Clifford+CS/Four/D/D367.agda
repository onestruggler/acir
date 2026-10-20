{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D367 (W : Ws) where

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
  q1 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
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
  q21 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q22 : Eqn
  q22 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q23 : Eqn
  q23 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q24 : Eqn
  q24 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (wn 566 W)
  q25 : Eqn
  q25 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q26 : Eqn
  q26 = eqn (S1 ∷ CX23 ∷ []) (CX23 ∷ S1 ∷ []) (low-comm ((S ↑)) (CX₀₁))
  q27 : Eqn
  q27 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q28 : Eqn
  q28 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q29 : Eqn
  q29 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (wn 567 W)

-- Bar(SSSKSS;2,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,1->0) part4: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part4 : ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ X2 ∷ Sw01 ∷ CX21 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part4 = derive (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ X2 ∷ Sw01 ∷ CX21 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw 79 q1 ∷
   rw⁻ 78 q2 ∷
   re 79 3 (CS13 ∷ []) ∷
   rw 79 q3 ∷
   rw 78 q4 ∷
   re 80 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 79 q2 ∷
   rw 80 q5 ∷
   rw 81 q2 ∷
   re 79 3 (CS03 ∷ []) ∷
   rw 80 q6 ∷
   re 79 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 85 q7 ∷
   re 83 3 (CX31 ∷ []) ∷
   rw 82 q8 ∷
   rw 81 q9 ∷
   rw 80 q10 ∷
   re 80 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 79 q11 ∷
   re 80 5 (CS03 ∷ []) ∷
   rw 82 q12 ∷
   rw⁻ 81 q4 ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 82 q2 ∷
   rw 81 q1 ∷
   rw⁻ 80 q2 ∷
   re 81 3 (CS13 ∷ []) ∷
   rw 81 q3 ∷
   rw 80 q4 ∷
   re 82 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 81 q2 ∷
   rw 82 q5 ∷
   rw 83 q2 ∷
   re 81 3 (CS03 ∷ []) ∷
   rw 82 q6 ∷
   rw 79 q12 ∷
   rw⁻ 78 q4 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 79 q2 ∷
   rw 78 q1 ∷
   rw⁻ 77 q2 ∷
   re 78 3 (CS13 ∷ []) ∷
   rw 78 q3 ∷
   rw 77 q4 ∷
   re 79 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 78 q2 ∷
   rw 79 q5 ∷
   rw 80 q2 ∷
   re 78 3 (CS03 ∷ []) ∷
   rw 79 q6 ∷
   re 78 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 84 q7 ∷
   re 82 3 (CX31 ∷ []) ∷
   rw 81 q8 ∷
   rw 80 q9 ∷
   rw 79 q10 ∷
   re 79 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 78 q11 ∷
   re 79 5 (CS03 ∷ []) ∷
   rw 81 q12 ∷
   rw⁻ 80 q4 ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 81 q2 ∷
   rw 80 q1 ∷
   rw⁻ 79 q2 ∷
   re 80 3 (CS13 ∷ []) ∷
   rw 80 q3 ∷
   rw 79 q4 ∷
   re 81 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 80 q2 ∷
   rw 81 q5 ∷
   rw 82 q2 ∷
   re 80 3 (CS03 ∷ []) ∷
   rw 81 q6 ∷
   rw⁻ 76 q13 ∷
   rw⁻ 77 q14 ∷
   rw⁻ 78 q13 ∷
   rw 77 q12 ∷
   rw⁻ 76 q4 ∷
   re 75 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 77 q2 ∷
   rw 76 q15 ∷
   rw⁻ 75 q2 ∷
   re 76 3 (CK31 ∷ []) ∷
   rw 76 q16 ∷
   rw 75 q4 ∷
   re 77 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 76 q2 ∷
   rw 77 q17 ∷
   rw 78 q2 ∷
   re 76 3 (CK30 ∷ []) ∷
   rw 77 q6 ∷
   re 76 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 82 q7 ∷
   re 80 3 (CX31 ∷ []) ∷
   rw 79 q8 ∷
   rw 78 q18 ∷
   rw 77 q10 ∷
   re 77 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 76 q11 ∷
   re 77 5 (CK30 ∷ []) ∷
   rw 79 q12 ∷
   rw⁻ 78 q4 ∷
   re 77 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 79 q2 ∷
   rw 78 q15 ∷
   rw⁻ 77 q2 ∷
   re 78 3 (CK31 ∷ []) ∷
   rw 78 q16 ∷
   rw 77 q4 ∷
   re 79 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 78 q2 ∷
   rw 79 q17 ∷
   rw 80 q2 ∷
   re 78 3 (CK30 ∷ []) ∷
   rw 79 q6 ∷
   rw 76 q12 ∷
   rw⁻ 75 q4 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 76 q2 ∷
   rw 75 q1 ∷
   rw⁻ 74 q2 ∷
   re 75 3 (CS13 ∷ []) ∷
   rw 75 q3 ∷
   rw 74 q4 ∷
   re 76 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 75 q2 ∷
   rw 76 q5 ∷
   rw 77 q2 ∷
   re 75 3 (CS03 ∷ []) ∷
   rw 76 q6 ∷
   re 75 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 81 q7 ∷
   re 79 3 (CX31 ∷ []) ∷
   rw 78 q8 ∷
   rw 77 q9 ∷
   rw 76 q10 ∷
   re 76 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 75 q11 ∷
   re 76 5 (CS03 ∷ []) ∷
   rw 78 q12 ∷
   rw⁻ 77 q4 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 78 q2 ∷
   rw 77 q1 ∷
   rw⁻ 76 q2 ∷
   re 77 3 (CS13 ∷ []) ∷
   rw 77 q3 ∷
   rw 76 q4 ∷
   re 78 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 77 q2 ∷
   rw 78 q5 ∷
   rw 79 q2 ∷
   re 77 3 (CS03 ∷ []) ∷
   rw 78 q6 ∷
   rw 75 q12 ∷
   rw⁻ 74 q4 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 75 q2 ∷
   rw 74 q1 ∷
   rw⁻ 73 q2 ∷
   re 74 3 (CS13 ∷ []) ∷
   rw 74 q3 ∷
   rw 73 q4 ∷
   re 75 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 74 q2 ∷
   rw 75 q5 ∷
   rw 76 q2 ∷
   re 74 3 (CS03 ∷ []) ∷
   rw 75 q6 ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 80 q7 ∷
   re 78 3 (CX31 ∷ []) ∷
   rw 77 q8 ∷
   rw 76 q9 ∷
   rw 75 q10 ∷
   re 75 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 74 q11 ∷
   re 75 5 (CS03 ∷ []) ∷
   rw 77 q12 ∷
   rw⁻ 76 q4 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 77 q2 ∷
   rw 76 q1 ∷
   rw⁻ 75 q2 ∷
   re 76 3 (CS13 ∷ []) ∷
   rw 76 q3 ∷
   rw 75 q4 ∷
   re 77 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 76 q2 ∷
   rw 77 q5 ∷
   rw 78 q2 ∷
   re 76 3 (CS03 ∷ []) ∷
   rw 77 q6 ∷
   rw 74 q12 ∷
   rw⁻ 73 q4 ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 74 q2 ∷
   rw 73 q1 ∷
   rw⁻ 72 q2 ∷
   re 73 3 (CS13 ∷ []) ∷
   rw 73 q3 ∷
   rw 72 q4 ∷
   re 74 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 73 q2 ∷
   rw 74 q5 ∷
   rw 75 q2 ∷
   re 73 3 (CS03 ∷ []) ∷
   rw 74 q6 ∷
   re 73 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 79 q7 ∷
   re 77 3 (CX31 ∷ []) ∷
   rw 76 q8 ∷
   rw 75 q9 ∷
   rw 74 q10 ∷
   re 74 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 73 q11 ∷
   re 74 5 (CS03 ∷ []) ∷
   rw 76 q12 ∷
   rw⁻ 75 q4 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 76 q2 ∷
   rw 75 q1 ∷
   rw⁻ 74 q2 ∷
   re 75 3 (CS13 ∷ []) ∷
   rw 75 q3 ∷
   rw 74 q4 ∷
   re 76 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 75 q2 ∷
   rw 76 q5 ∷
   rw 77 q2 ∷
   re 75 3 (CS03 ∷ []) ∷
   rw 76 q6 ∷
   rw 73 q12 ∷
   rw⁻ 72 q4 ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 73 q2 ∷
   rw 72 q1 ∷
   rw⁻ 71 q2 ∷
   re 72 3 (CS13 ∷ []) ∷
   rw 72 q3 ∷
   rw 71 q4 ∷
   re 73 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 72 q2 ∷
   rw 73 q5 ∷
   rw 74 q2 ∷
   re 72 3 (CS03 ∷ []) ∷
   rw 73 q6 ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 78 q7 ∷
   re 76 3 (CX31 ∷ []) ∷
   rw 75 q8 ∷
   rw 74 q9 ∷
   rw 73 q10 ∷
   re 73 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 72 q11 ∷
   re 73 5 (CS03 ∷ []) ∷
   rw 75 q12 ∷
   rw⁻ 74 q4 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 75 q2 ∷
   rw 74 q1 ∷
   rw⁻ 73 q2 ∷
   re 74 3 (CS13 ∷ []) ∷
   rw 74 q3 ∷
   rw 73 q4 ∷
   re 75 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 74 q2 ∷
   rw 75 q5 ∷
   rw 76 q2 ∷
   re 74 3 (CS03 ∷ []) ∷
   rw 75 q6 ∷
   rw 72 q12 ∷
   rw⁻ 71 q4 ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 72 q2 ∷
   rw 71 q1 ∷
   rw⁻ 70 q2 ∷
   re 71 3 (CS13 ∷ []) ∷
   rw 71 q3 ∷
   rw 70 q4 ∷
   re 72 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 71 q2 ∷
   rw 72 q5 ∷
   rw 73 q2 ∷
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
   rw⁻ 74 q2 ∷
   rw 73 q1 ∷
   rw⁻ 72 q2 ∷
   re 73 3 (CS13 ∷ []) ∷
   rw 73 q3 ∷
   rw 72 q4 ∷
   re 74 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 73 q2 ∷
   rw 74 q5 ∷
   rw 75 q2 ∷
   re 73 3 (CS03 ∷ []) ∷
   rw 74 q6 ∷
   rw 71 q12 ∷
   rw⁻ 70 q4 ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 71 q2 ∷
   rw 70 q1 ∷
   rw⁻ 69 q2 ∷
   re 70 3 (CS13 ∷ []) ∷
   rw 70 q3 ∷
   rw 69 q4 ∷
   re 71 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 70 q2 ∷
   rw 71 q5 ∷
   rw 72 q2 ∷
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
   rw⁻ 73 q2 ∷
   rw 72 q1 ∷
   rw⁻ 71 q2 ∷
   re 72 3 (CS13 ∷ []) ∷
   rw 72 q3 ∷
   rw 71 q4 ∷
   re 73 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 72 q2 ∷
   rw 73 q5 ∷
   rw 74 q2 ∷
   re 72 3 (CS03 ∷ []) ∷
   rw 73 q6 ∷
   rw 68 q19 ∷
   rw 62 q20 ∷
   rw 111 q7 ∷
   rw 110 q21 ∷
   rw 109 q21 ∷
   rw 108 q21 ∷
   rw 107 q21 ∷
   rw 106 q21 ∷
   rw 105 q21 ∷
   rw 104 q22 ∷
   rw 103 q23 ∷
   rw 102 q21 ∷
   rw 101 q21 ∷
   rw 100 q21 ∷
   rw 99 q22 ∷
   rw 98 q23 ∷
   rw 97 q22 ∷
   rw 96 q23 ∷
   re 95 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 97 q11 ∷
   re 94 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 96 q11 ∷
   re 93 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 95 q11 ∷
   re 92 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 94 q11 ∷
   re 91 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 93 q11 ∷
   re 90 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 92 q11 ∷
   rw 91 q24 ∷
   rw⁻ 90 q23 ∷
   rw⁻ 91 q22 ∷
   rw⁻ 92 q23 ∷
   rw⁻ 93 q22 ∷
   rw⁻ 94 q21 ∷
   rw⁻ 95 q21 ∷
   rw⁻ 96 q21 ∷
   rw⁻ 97 q23 ∷
   rw⁻ 98 q22 ∷
   rw⁻ 99 q21 ∷
   rw⁻ 100 q21 ∷
   rw⁻ 101 q21 ∷
   rw⁻ 102 q21 ∷
   rw⁻ 103 q21 ∷
   rw⁻ 104 q21 ∷
   rw 107 q7 ∷
   re 105 3 (CS03 ∷ []) ∷
   rw 108 q7 ∷
   re 106 3 (CS03 ∷ []) ∷
   rw 109 q7 ∷
   re 107 3 (CS03 ∷ []) ∷
   rw 110 q7 ∷
   re 108 3 (CK30 ∷ []) ∷
   rw 111 q7 ∷
   re 109 3 (CS03 ∷ []) ∷
   rw 112 q7 ∷
   re 110 3 (CS03 ∷ []) ∷
   rw 111 q11 ∷
   rw⁻ 89 q25 ∷
   rw⁻ 90 q26 ∷
   rw⁻ 91 q25 ∷
   rw⁻ 92 q26 ∷
   rw⁻ 93 q27 ∷
   rw⁻ 94 q27 ∷
   rw⁻ 95 q27 ∷
   rw⁻ 96 q25 ∷
   rw⁻ 97 q26 ∷
   rw⁻ 98 q27 ∷
   rw⁻ 99 q27 ∷
   rw⁻ 100 q27 ∷
   rw⁻ 101 q27 ∷
   rw⁻ 102 q27 ∷
   rw⁻ 103 q27 ∷
   rw 104 q7 ∷
   rw 103 q21 ∷
   rw 102 q21 ∷
   rw 101 q21 ∷
   rw 100 q21 ∷
   rw 99 q21 ∷
   rw 98 q21 ∷
   rw 97 q22 ∷
   rw 96 q23 ∷
   rw 95 q21 ∷
   rw 94 q21 ∷
   rw 93 q21 ∷
   rw 92 q22 ∷
   rw 91 q23 ∷
   rw 90 q22 ∷
   rw 89 q23 ∷
   re 88 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 90 q11 ∷
   re 87 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 89 q11 ∷
   re 86 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 88 q11 ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 87 q11 ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 86 q11 ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 85 q11 ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 84 q11 ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 83 q11 ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 82 q11 ∷
   rw 79 q28 ∷
   re 78 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 80 q11 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q11 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q11 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q11 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q11 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q11 ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q11 ∷
   rw 73 q29 ∷
   rw⁻ 72 q23 ∷
   rw⁻ 73 q22 ∷
   rw⁻ 74 q23 ∷
   rw⁻ 75 q22 ∷
   rw⁻ 76 q21 ∷
   rw⁻ 77 q21 ∷
   rw⁻ 78 q21 ∷
   rw⁻ 79 q23 ∷
   rw⁻ 80 q22 ∷
   rw⁻ 81 q21 ∷
   rw⁻ 82 q21 ∷
   rw⁻ 83 q21 ∷
   rw⁻ 84 q21 ∷
   rw⁻ 85 q21 ∷
   rw⁻ 86 q21 ∷
   rw 89 q7 ∷
   re 87 3 (CS03 ∷ []) ∷
   rw 90 q7 ∷
   re 88 3 (CS03 ∷ []) ∷
   rw 91 q7 ∷
   re 89 3 (CS03 ∷ []) ∷
   rw 92 q7 ∷
   re 90 3 (CS03 ∷ []) ∷
   rw 93 q7 ∷
   re 91 3 (CS03 ∷ []) ∷
   rw 94 q7 ∷ []) Eq.refl

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D113 (W : Ws) where

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
  q1 = wE 13 W
  q2 : Eqn
  q2 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q3 : Eqn
  q3 = wE 78 W
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = eqn (CX21 ∷ S3 ∷ []) (S3 ∷ CX21 ∷ []) (low₃-comm ((CX₁₀ ↑)) (S))
  q6 : Eqn
  q6 = wE 1 W
  q7 : Eqn
  q7 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q8 : Eqn
  q8 = wE 464 W
  q9 : Eqn
  q9 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q10 : Eqn
  q10 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q11 : Eqn
  q11 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q12 : Eqn
  q12 = wE 666 W
  q13 : Eqn
  q13 = wE 151 W
  q14 : Eqn
  q14 = wE 5 W
  q15 : Eqn
  q15 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q16 : Eqn
  q16 = wE 7 W
  q17 : Eqn
  q17 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q18 : Eqn
  q18 = wE 140 W
  q19 : Eqn
  q19 = wE 667 W
  q20 : Eqn
  q20 = wE 142 W
  q21 : Eqn
  q21 = wE 27 W
  q22 : Eqn
  q22 = wE 31 W

-- Bar(SSSKSS;2,1->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,3->0) part3: 451 steps
lem-Bar⟨SSSKSS21-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~23-⟶0⟩-part3 : ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sw23 ∷ CX31 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ X2 ∷ CX23 ∷ X2 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS21-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~23-⟶0⟩-part3 = derive (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sw23 ∷ CX31 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ X2 ∷ CX23 ∷ X2 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 90 q1 ∷
   rw⁻ 91 q2 ∷
   rw 92 q3 ∷
   re 93 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 95 q4 ∷
   re 89 5 (CK30 ∷ []) ∷
   rw 90 q5 ∷
   re 92 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 91 q6 ∷
   re 92 3 (CX31 ∷ []) ∷
   rw 92 q1 ∷
   rw⁻ 93 q2 ∷
   rw 94 q3 ∷
   re 95 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 97 q4 ∷
   re 91 5 (CK30 ∷ []) ∷
   rw 92 q5 ∷
   re 94 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 93 q6 ∷
   re 94 3 (CX31 ∷ []) ∷
   rw 94 q1 ∷
   rw⁻ 95 q7 ∷
   rw 96 q3 ∷
   re 97 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 99 q4 ∷
   re 93 5 (CS03 ∷ []) ∷
   re 95 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 94 q6 ∷
   re 95 3 (CX31 ∷ []) ∷
   rw 95 q1 ∷
   rw⁻ 96 q7 ∷
   rw 97 q3 ∷
   re 98 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 100 q4 ∷
   re 94 5 (CS03 ∷ []) ∷
   re 96 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 95 q6 ∷
   re 96 3 (CX31 ∷ []) ∷
   rw 96 q1 ∷
   rw⁻ 97 q7 ∷
   rw 98 q3 ∷
   re 99 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 101 q4 ∷
   re 95 5 (CS03 ∷ []) ∷
   re 97 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 96 q6 ∷
   re 97 3 (CX31 ∷ []) ∷
   rw 97 q1 ∷
   rw⁻ 98 q2 ∷
   rw 99 q3 ∷
   re 100 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 102 q4 ∷
   re 96 5 (CK30 ∷ []) ∷
   rw 97 q5 ∷
   re 99 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 98 q6 ∷
   re 99 3 (CX31 ∷ []) ∷
   rw 99 q1 ∷
   rw⁻ 100 q7 ∷
   rw 101 q3 ∷
   re 102 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 104 q4 ∷
   re 98 5 (CS03 ∷ []) ∷
   re 100 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 99 q6 ∷
   re 100 3 (CX31 ∷ []) ∷
   rw 100 q1 ∷
   rw⁻ 101 q7 ∷
   rw 102 q3 ∷
   re 103 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 105 q4 ∷
   re 99 5 (CS03 ∷ []) ∷
   re 101 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 100 q6 ∷
   re 101 3 (CX31 ∷ []) ∷
   rw 101 q1 ∷
   rw⁻ 102 q7 ∷
   rw 103 q3 ∷
   re 104 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 106 q4 ∷
   re 100 5 (CS03 ∷ []) ∷
   re 102 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 101 q6 ∷
   re 102 3 (CX31 ∷ []) ∷
   rw 102 q1 ∷
   rw⁻ 103 q7 ∷
   rw 104 q3 ∷
   re 105 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 107 q4 ∷
   re 101 5 (CS03 ∷ []) ∷
   re 103 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 102 q6 ∷
   re 103 3 (CX31 ∷ []) ∷
   rw 103 q1 ∷
   rw⁻ 104 q7 ∷
   rw 105 q3 ∷
   re 106 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 108 q4 ∷
   re 102 5 (CS03 ∷ []) ∷
   re 104 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 103 q6 ∷
   re 104 3 (CX31 ∷ []) ∷
   rw 104 q1 ∷
   rw⁻ 105 q7 ∷
   rw 106 q3 ∷
   re 107 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 109 q4 ∷
   re 103 5 (CS03 ∷ []) ∷
   rw 104 q6 ∷
   re 103 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 105 q4 ∷
   re 102 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 104 q4 ∷
   re 101 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 103 q4 ∷
   re 100 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 102 q4 ∷
   re 99 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 101 q4 ∷
   re 98 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 100 q4 ∷
   rw 97 q8 ∷
   re 96 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 98 q4 ∷
   re 95 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 97 q4 ∷
   re 94 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 96 q4 ∷
   re 93 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 95 q4 ∷
   rw 92 q8 ∷
   re 91 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 93 q4 ∷
   rw 90 q8 ∷
   re 89 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 91 q4 ∷
   rw 88 q9 ∷
   rw 87 q9 ∷
   rw 86 q9 ∷
   rw 85 q9 ∷
   rw 84 q9 ∷
   rw 83 q9 ∷
   rw 82 q9 ∷
   rw 81 q9 ∷
   rw 80 q9 ∷
   rw 79 q10 ∷
   rw 78 q11 ∷
   rw 77 q9 ∷
   rw 76 q9 ∷
   rw 75 q9 ∷
   rw 74 q9 ∷
   rw 73 q9 ∷
   rw 72 q9 ∷
   rw 73 q12 ∷
   rw 74 q6 ∷
   re 72 3 (CK30 ∷ []) ∷
   rw 73 q13 ∷
   rw 76 q6 ∷
   re 74 3 (CK30 ∷ []) ∷
   rw 75 q13 ∷
   rw 78 q6 ∷
   re 76 3 (CS03 ∷ []) ∷
   rw 79 q6 ∷
   re 77 3 (CS03 ∷ []) ∷
   rw 80 q6 ∷
   re 78 3 (CS03 ∷ []) ∷
   rw 81 q6 ∷
   re 79 3 (CK30 ∷ []) ∷
   rw 80 q13 ∷
   rw 83 q6 ∷
   re 81 3 (CS03 ∷ []) ∷
   rw 84 q6 ∷
   re 82 3 (CS03 ∷ []) ∷
   rw 85 q6 ∷
   re 83 3 (CS03 ∷ []) ∷
   rw 86 q6 ∷
   re 84 3 (CS03 ∷ []) ∷
   rw 87 q6 ∷
   re 85 3 (CS03 ∷ []) ∷
   rw 88 q6 ∷
   re 86 3 (CS03 ∷ []) ∷
   rw⁻ 87 q9 ∷
   rw⁻ 88 q9 ∷
   rw⁻ 89 q9 ∷
   rw⁻ 90 q9 ∷
   rw⁻ 91 q9 ∷
   rw⁻ 92 q9 ∷
   rw⁻ 93 q11 ∷
   rw⁻ 94 q10 ∷
   rw⁻ 95 q9 ∷
   rw⁻ 96 q9 ∷
   rw⁻ 97 q9 ∷
   rw⁻ 98 q9 ∷
   rw⁻ 99 q9 ∷
   rw⁻ 100 q9 ∷
   rw⁻ 101 q9 ∷
   rw⁻ 102 q9 ∷
   rw⁻ 103 q9 ∷
   rw 104 q4 ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q6 ∷
   re 72 3 (CX31 ∷ []) ∷
   rw 72 q1 ∷
   rw⁻ 73 q2 ∷
   rw 74 q3 ∷
   re 75 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 77 q4 ∷
   re 71 5 (CK30 ∷ []) ∷
   rw 72 q5 ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q6 ∷
   re 74 3 (CX31 ∷ []) ∷
   rw 74 q1 ∷
   rw⁻ 75 q2 ∷
   rw 76 q3 ∷
   re 77 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 79 q4 ∷
   re 73 5 (CK30 ∷ []) ∷
   rw 74 q5 ∷
   re 76 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 75 q6 ∷
   re 76 3 (CX31 ∷ []) ∷
   rw 76 q1 ∷
   rw⁻ 77 q7 ∷
   rw 78 q3 ∷
   re 79 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 81 q4 ∷
   re 75 5 (CS03 ∷ []) ∷
   re 77 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 76 q6 ∷
   re 77 3 (CX31 ∷ []) ∷
   rw 77 q1 ∷
   rw⁻ 78 q7 ∷
   rw 79 q3 ∷
   re 80 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 82 q4 ∷
   re 76 5 (CS03 ∷ []) ∷
   re 78 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 77 q6 ∷
   re 78 3 (CX31 ∷ []) ∷
   rw 78 q1 ∷
   rw⁻ 79 q7 ∷
   rw 80 q3 ∷
   re 81 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 83 q4 ∷
   re 77 5 (CS03 ∷ []) ∷
   re 79 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 78 q6 ∷
   re 79 3 (CX31 ∷ []) ∷
   rw 79 q1 ∷
   rw⁻ 80 q2 ∷
   rw 81 q3 ∷
   re 82 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 84 q4 ∷
   re 78 5 (CK30 ∷ []) ∷
   rw 79 q5 ∷
   re 81 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 80 q6 ∷
   re 81 3 (CX31 ∷ []) ∷
   rw 81 q1 ∷
   rw⁻ 82 q7 ∷
   rw 83 q3 ∷
   re 84 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 86 q4 ∷
   re 80 5 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 81 q6 ∷
   re 82 3 (CX31 ∷ []) ∷
   rw 82 q1 ∷
   rw⁻ 83 q7 ∷
   rw 84 q3 ∷
   re 85 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 87 q4 ∷
   re 81 5 (CS03 ∷ []) ∷
   re 83 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 82 q6 ∷
   re 83 3 (CX31 ∷ []) ∷
   rw 83 q1 ∷
   rw⁻ 84 q7 ∷
   rw 85 q3 ∷
   re 86 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 88 q4 ∷
   re 82 5 (CS03 ∷ []) ∷
   re 84 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 83 q6 ∷
   re 84 3 (CX31 ∷ []) ∷
   rw 84 q1 ∷
   rw⁻ 85 q7 ∷
   rw 86 q3 ∷
   re 87 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 89 q4 ∷
   re 83 5 (CS03 ∷ []) ∷
   re 85 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 84 q6 ∷
   re 85 3 (CX31 ∷ []) ∷
   rw 85 q1 ∷
   rw⁻ 86 q7 ∷
   rw 87 q3 ∷
   re 88 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 90 q4 ∷
   re 84 5 (CS03 ∷ []) ∷
   re 86 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 85 q6 ∷
   re 86 3 (CX31 ∷ []) ∷
   rw 86 q1 ∷
   rw⁻ 87 q7 ∷
   rw 88 q3 ∷
   re 89 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 91 q4 ∷
   re 85 5 (CS03 ∷ []) ∷
   rw 86 q14 ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 87 q15 ∷
   rw 86 q16 ∷
   rw⁻ 85 q15 ∷
   re 86 3 (CS13 ∷ []) ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 86 q15 ∷
   rw 85 q16 ∷
   rw⁻ 84 q15 ∷
   re 85 3 (CS13 ∷ []) ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 85 q15 ∷
   rw 84 q16 ∷
   rw⁻ 83 q15 ∷
   re 84 3 (CS13 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 84 q15 ∷
   rw 83 q16 ∷
   rw⁻ 82 q15 ∷
   re 83 3 (CS13 ∷ []) ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 83 q15 ∷
   rw 82 q16 ∷
   rw⁻ 81 q15 ∷
   re 82 3 (CS13 ∷ []) ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 82 q15 ∷
   rw 81 q16 ∷
   rw⁻ 80 q15 ∷
   re 81 3 (CS13 ∷ []) ∷
   rw⁻ 79 q17 ∷
   re 78 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 80 q15 ∷
   rw 79 q18 ∷
   rw⁻ 78 q15 ∷
   re 79 3 (CK31 ∷ []) ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 79 q15 ∷
   rw 78 q16 ∷
   rw⁻ 77 q15 ∷
   re 78 3 (CS13 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 78 q15 ∷
   rw 77 q16 ∷
   rw⁻ 76 q15 ∷
   re 77 3 (CS13 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 77 q15 ∷
   rw 76 q16 ∷
   rw⁻ 75 q15 ∷
   re 76 3 (CS13 ∷ []) ∷
   rw⁻ 74 q17 ∷
   re 73 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 75 q15 ∷
   rw 74 q18 ∷
   rw⁻ 73 q15 ∷
   re 74 3 (CK31 ∷ []) ∷
   rw⁻ 72 q17 ∷
   re 71 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 73 q15 ∷
   rw 72 q18 ∷
   rw⁻ 71 q15 ∷
   re 72 3 (CK31 ∷ []) ∷
   rw 70 q16 ∷
   rw 69 q16 ∷
   rw 68 q18 ∷
   rw 67 q16 ∷
   rw 66 q16 ∷
   rw 65 q16 ∷
   rw 66 q19 ∷
   re 66 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 65 q15 ∷
   rw 66 q20 ∷
   rw 67 q15 ∷
   re 65 3 (CK30 ∷ []) ∷
   rw 66 q17 ∷
   re 68 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 67 q15 ∷
   rw 68 q20 ∷
   rw 69 q15 ∷
   re 67 3 (CK30 ∷ []) ∷
   rw 68 q17 ∷
   re 70 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 69 q15 ∷
   rw 70 q21 ∷
   rw 71 q15 ∷
   re 69 3 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 70 q15 ∷
   rw 71 q21 ∷
   rw 72 q15 ∷
   re 70 3 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 71 q15 ∷
   rw 72 q21 ∷
   rw 73 q15 ∷
   re 71 3 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 72 q15 ∷
   rw 73 q20 ∷
   rw 74 q15 ∷
   re 72 3 (CK30 ∷ []) ∷
   rw 73 q17 ∷
   re 75 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 74 q15 ∷
   rw 75 q21 ∷
   rw 76 q15 ∷
   re 74 3 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 75 q15 ∷
   rw 76 q21 ∷
   rw 77 q15 ∷
   re 75 3 (CS03 ∷ []) ∷
   re 77 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 76 q15 ∷
   rw 77 q21 ∷
   rw 78 q15 ∷
   re 76 3 (CS03 ∷ []) ∷
   re 78 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 77 q15 ∷
   rw 78 q21 ∷
   rw 79 q15 ∷
   re 77 3 (CS03 ∷ []) ∷
   re 79 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 78 q15 ∷
   rw 79 q21 ∷
   rw 80 q15 ∷
   re 78 3 (CS03 ∷ []) ∷
   re 80 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 79 q15 ∷
   rw 80 q21 ∷
   rw 81 q15 ∷
   re 79 3 (CS03 ∷ []) ∷
   rw 80 q21 ∷
   rw 81 q21 ∷
   rw 82 q21 ∷
   rw 83 q20 ∷
   rw 84 q21 ∷
   rw 85 q21 ∷
   rw 86 q22 ∷ []) Eq.refl

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D350 (W : Ws) where

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
  q1 = wE 27 W
  q2 : Eqn
  q2 = wE 142 W
  q3 : Eqn
  q3 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q4 : Eqn
  q4 = wE 31 W
  q5 : Eqn
  q5 = wE 1 W
  q6 : Eqn
  q6 = wE 36 W
  q7 : Eqn
  q7 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q8 : Eqn
  q8 = wE 37 W
  q9 : Eqn
  q9 = wE 3 W
  q10 : Eqn
  q10 = eqn (CX12 ∷ S3 ∷ []) (S3 ∷ CX12 ∷ []) (low₃-comm ((CX₀₁ ↑)) (S))
  q11 : Eqn
  q11 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q12 : Eqn
  q12 = wE 464 W
  q13 : Eqn
  q13 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q14 : Eqn
  q14 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q15 : Eqn
  q15 = wE 617 W
  q16 : Eqn
  q16 = wE 151 W

-- Bar(SSKSKK;1,2->0) passes groups of WBar(KiKiSSSKiSSSSSS;~1,3->0) part5: 191 steps
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part5 : ⟪ (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ X1 ∷ CX13 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ Sw01 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ X1 ∷ CX13 ∷ X1 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part5 = derive (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ X1 ∷ CX13 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ Sw01 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ X1 ∷ CX13 ∷ X1 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 92 q1 ∷
   rw 93 q1 ∷
   rw 94 q2 ∷
   rw 95 q3 ∷
   rw 96 q1 ∷
   rw 97 q1 ∷
   rw 98 q1 ∷
   rw 99 q1 ∷
   rw 100 q1 ∷
   rw 101 q1 ∷
   rw 102 q4 ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q5 ∷
   re 72 3 (CX13 ∷ []) ∷
   rw 72 q6 ∷
   rw⁻ 73 q7 ∷
   rw 74 q8 ∷
   re 75 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 77 q9 ∷
   re 71 5 (CK30 ∷ []) ∷
   rw 72 q10 ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q5 ∷
   re 74 3 (CX13 ∷ []) ∷
   rw 74 q6 ∷
   rw⁻ 75 q7 ∷
   rw 76 q8 ∷
   re 77 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 79 q9 ∷
   re 73 5 (CK30 ∷ []) ∷
   rw 74 q10 ∷
   re 76 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 75 q5 ∷
   re 76 3 (CX13 ∷ []) ∷
   rw 76 q6 ∷
   rw⁻ 77 q11 ∷
   rw 78 q8 ∷
   re 79 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 81 q9 ∷
   re 75 5 (CS03 ∷ []) ∷
   re 77 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 76 q5 ∷
   re 77 3 (CX13 ∷ []) ∷
   rw 77 q6 ∷
   rw⁻ 78 q11 ∷
   rw 79 q8 ∷
   re 80 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 82 q9 ∷
   re 76 5 (CS03 ∷ []) ∷
   re 78 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 77 q5 ∷
   re 78 3 (CX13 ∷ []) ∷
   rw 78 q6 ∷
   rw⁻ 79 q11 ∷
   rw 80 q8 ∷
   re 81 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 83 q9 ∷
   re 77 5 (CS03 ∷ []) ∷
   re 79 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 78 q5 ∷
   re 79 3 (CX13 ∷ []) ∷
   rw 79 q6 ∷
   rw⁻ 80 q7 ∷
   rw 81 q8 ∷
   re 82 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 84 q9 ∷
   re 78 5 (CK30 ∷ []) ∷
   rw 79 q10 ∷
   re 81 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 80 q5 ∷
   re 81 3 (CX13 ∷ []) ∷
   rw 81 q6 ∷
   rw⁻ 82 q11 ∷
   rw 83 q8 ∷
   re 84 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 86 q9 ∷
   re 80 5 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 81 q5 ∷
   re 82 3 (CX13 ∷ []) ∷
   rw 82 q6 ∷
   rw⁻ 83 q11 ∷
   rw 84 q8 ∷
   re 85 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 87 q9 ∷
   re 81 5 (CS03 ∷ []) ∷
   re 83 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 82 q5 ∷
   re 83 3 (CX13 ∷ []) ∷
   rw 83 q6 ∷
   rw⁻ 84 q11 ∷
   rw 85 q8 ∷
   re 86 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 88 q9 ∷
   re 82 5 (CS03 ∷ []) ∷
   re 84 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 83 q5 ∷
   re 84 3 (CX13 ∷ []) ∷
   rw 84 q6 ∷
   rw⁻ 85 q11 ∷
   rw 86 q8 ∷
   re 87 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 89 q9 ∷
   re 83 5 (CS03 ∷ []) ∷
   re 85 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 84 q5 ∷
   re 85 3 (CX13 ∷ []) ∷
   rw 85 q6 ∷
   rw⁻ 86 q11 ∷
   rw 87 q8 ∷
   re 88 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 90 q9 ∷
   re 84 5 (CS03 ∷ []) ∷
   re 86 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 85 q5 ∷
   re 86 3 (CX13 ∷ []) ∷
   rw 86 q6 ∷
   rw⁻ 87 q11 ∷
   rw 88 q8 ∷
   re 89 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 91 q9 ∷
   re 85 5 (CS03 ∷ []) ∷
   rw 86 q5 ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 87 q9 ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 86 q9 ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 85 q9 ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 84 q9 ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 83 q9 ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 82 q9 ∷
   rw 79 q12 ∷
   re 78 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 80 q9 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q9 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q9 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q9 ∷
   rw 74 q12 ∷
   re 73 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 75 q9 ∷
   rw 72 q12 ∷
   re 71 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 73 q9 ∷
   rw 70 q13 ∷
   rw 69 q13 ∷
   rw 68 q14 ∷
   rw 67 q13 ∷
   rw 66 q14 ∷
   rw 65 q14 ∷
   rw 66 q15 ∷
   rw 67 q5 ∷
   re 65 3 (CK30 ∷ []) ∷
   rw 66 q16 ∷
   rw 69 q5 ∷
   re 67 3 (CK30 ∷ []) ∷
   rw 68 q16 ∷
   rw 71 q5 ∷
   re 69 3 (CS03 ∷ []) ∷
   rw 72 q5 ∷
   re 70 3 (CS03 ∷ []) ∷
   rw 73 q5 ∷
   re 71 3 (CS03 ∷ []) ∷
   rw 74 q5 ∷
   re 72 3 (CK30 ∷ []) ∷
   rw 73 q16 ∷
   rw 76 q5 ∷
   re 74 3 (CS03 ∷ []) ∷
   rw 77 q5 ∷
   re 75 3 (CS03 ∷ []) ∷
   rw 78 q5 ∷
   re 76 3 (CS03 ∷ []) ∷
   rw 79 q5 ∷
   re 77 3 (CS03 ∷ []) ∷
   rw 80 q5 ∷
   re 78 3 (CS03 ∷ []) ∷
   rw 81 q5 ∷
   re 79 3 (CS03 ∷ []) ∷
   rw⁻ 80 q14 ∷
   rw⁻ 81 q14 ∷
   rw⁻ 82 q13 ∷
   rw⁻ 83 q14 ∷
   rw⁻ 84 q13 ∷
   rw⁻ 85 q13 ∷
   rw 86 q9 ∷ []) Eq.refl

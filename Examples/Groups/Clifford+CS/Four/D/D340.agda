{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D340 (W : Ws) where

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
  q1 = wE 37 W
  q2 : Eqn
  q2 = wE 3 W
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 36 W
  q5 : Eqn
  q5 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q6 : Eqn
  q6 = eqn (CX12 ∷ S3 ∷ []) (S3 ∷ CX12 ∷ []) (low₃-comm ((CX₀₁ ↑)) (S))
  q7 : Eqn
  q7 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q8 : Eqn
  q8 = wE 5 W
  q9 : Eqn
  q9 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q10 : Eqn
  q10 = wE 7 W
  q11 : Eqn
  q11 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q12 : Eqn
  q12 = wE 140 W
  q13 : Eqn
  q13 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q14 : Eqn
  q14 = wE 961 W
  q15 : Eqn
  q15 = wE 27 W

-- Bar(SSKSKK;1,2->0) passes groups of WBar(SSSSSSKiSSSSSSSSS;~1,3->0) part2: 500 steps
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part2 : ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CX23 ∷ Sw12 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CS03 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part2 = derive (X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CX23 ∷ Sw12 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) (X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CS03 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ [])
  (rw 66 q1 ∷
   re 67 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 69 q2 ∷
   re 63 5 (CS03 ∷ []) ∷
   re 65 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 64 q3 ∷
   re 65 3 (CX13 ∷ []) ∷
   rw 65 q4 ∷
   rw⁻ 66 q5 ∷
   rw 67 q1 ∷
   re 68 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 70 q2 ∷
   re 64 5 (CS03 ∷ []) ∷
   re 66 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 65 q3 ∷
   re 66 3 (CX13 ∷ []) ∷
   rw 66 q4 ∷
   rw⁻ 67 q5 ∷
   rw 68 q1 ∷
   re 69 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 71 q2 ∷
   re 65 5 (CS03 ∷ []) ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 66 q3 ∷
   re 67 3 (CX13 ∷ []) ∷
   rw 67 q4 ∷
   rw⁻ 68 q5 ∷
   rw 69 q1 ∷
   re 70 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 72 q2 ∷
   re 66 5 (CS03 ∷ []) ∷
   re 68 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 67 q3 ∷
   re 68 3 (CX13 ∷ []) ∷
   rw 68 q4 ∷
   rw⁻ 69 q5 ∷
   rw 70 q1 ∷
   re 71 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 73 q2 ∷
   re 67 5 (CS03 ∷ []) ∷
   re 69 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 68 q3 ∷
   re 69 3 (CX13 ∷ []) ∷
   rw 69 q4 ∷
   rw⁻ 70 q5 ∷
   rw 71 q1 ∷
   re 72 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 74 q2 ∷
   re 68 5 (CS03 ∷ []) ∷
   re 70 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 69 q3 ∷
   re 70 3 (CX13 ∷ []) ∷
   rw 70 q4 ∷
   rw⁻ 71 q5 ∷
   rw 72 q1 ∷
   re 73 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 75 q2 ∷
   re 69 5 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 70 q3 ∷
   re 71 3 (CX13 ∷ []) ∷
   rw 71 q4 ∷
   rw⁻ 72 q5 ∷
   rw 73 q1 ∷
   re 74 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 76 q2 ∷
   re 70 5 (CS03 ∷ []) ∷
   rw 71 q6 ∷
   rw 72 q6 ∷
   rw 73 q6 ∷
   re 75 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 74 q3 ∷
   re 75 3 (CX13 ∷ []) ∷
   rw 75 q4 ∷
   rw⁻ 76 q7 ∷
   rw 77 q1 ∷
   re 78 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 80 q2 ∷
   re 74 5 (CK30 ∷ []) ∷
   rw 75 q6 ∷
   re 77 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 76 q3 ∷
   re 77 3 (CX13 ∷ []) ∷
   rw 77 q4 ∷
   rw⁻ 78 q5 ∷
   rw 79 q1 ∷
   re 80 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 82 q2 ∷
   re 76 5 (CS03 ∷ []) ∷
   re 78 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 77 q3 ∷
   re 78 3 (CX13 ∷ []) ∷
   rw 78 q4 ∷
   rw⁻ 79 q5 ∷
   rw 80 q1 ∷
   re 81 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 83 q2 ∷
   re 77 5 (CS03 ∷ []) ∷
   re 79 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 78 q3 ∷
   re 79 3 (CX13 ∷ []) ∷
   rw 79 q4 ∷
   rw⁻ 80 q5 ∷
   rw 81 q1 ∷
   re 82 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 84 q2 ∷
   re 78 5 (CS03 ∷ []) ∷
   re 80 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 79 q3 ∷
   re 80 3 (CX13 ∷ []) ∷
   rw 80 q4 ∷
   rw⁻ 81 q5 ∷
   rw 82 q1 ∷
   re 83 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 85 q2 ∷
   re 79 5 (CS03 ∷ []) ∷
   re 81 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 80 q3 ∷
   re 81 3 (CX13 ∷ []) ∷
   rw 81 q4 ∷
   rw⁻ 82 q5 ∷
   rw 83 q1 ∷
   re 84 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 86 q2 ∷
   re 80 5 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 81 q3 ∷
   re 82 3 (CX13 ∷ []) ∷
   rw 82 q4 ∷
   rw⁻ 83 q5 ∷
   rw 84 q1 ∷
   re 85 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 87 q2 ∷
   re 81 5 (CS03 ∷ []) ∷
   re 83 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 82 q3 ∷
   re 83 3 (CX13 ∷ []) ∷
   rw 83 q4 ∷
   rw⁻ 84 q5 ∷
   rw 85 q1 ∷
   re 86 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 88 q2 ∷
   re 82 5 (CS03 ∷ []) ∷
   re 84 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 83 q3 ∷
   re 84 3 (CX13 ∷ []) ∷
   rw 84 q4 ∷
   rw⁻ 85 q5 ∷
   rw 86 q1 ∷
   re 87 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 89 q2 ∷
   re 83 5 (CS03 ∷ []) ∷
   re 85 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 84 q3 ∷
   re 85 3 (CX13 ∷ []) ∷
   rw 85 q4 ∷
   rw⁻ 86 q5 ∷
   rw 87 q1 ∷
   re 88 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 90 q2 ∷
   re 84 5 (CS03 ∷ []) ∷
   re 86 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 85 q3 ∷
   re 86 3 (CX13 ∷ []) ∷
   rw 86 q4 ∷
   rw⁻ 87 q5 ∷
   rw 88 q1 ∷
   re 89 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 91 q2 ∷
   re 85 5 (CS03 ∷ []) ∷
   re 87 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 86 q3 ∷
   re 87 3 (CX13 ∷ []) ∷
   rw 87 q4 ∷
   rw⁻ 88 q5 ∷
   rw 89 q1 ∷
   re 90 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 92 q2 ∷
   re 86 5 (CS03 ∷ []) ∷
   re 88 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 87 q3 ∷
   re 88 3 (CX13 ∷ []) ∷
   rw 88 q4 ∷
   rw⁻ 89 q5 ∷
   rw 90 q1 ∷
   re 91 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 93 q2 ∷
   re 87 5 (CS03 ∷ []) ∷
   re 89 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 88 q3 ∷
   re 89 3 (CX13 ∷ []) ∷
   rw 89 q4 ∷
   rw⁻ 90 q5 ∷
   rw 91 q1 ∷
   re 92 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 94 q2 ∷
   re 88 5 (CS03 ∷ []) ∷
   re 90 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 89 q3 ∷
   re 90 3 (CX13 ∷ []) ∷
   rw 90 q4 ∷
   rw⁻ 91 q5 ∷
   rw 92 q1 ∷
   re 93 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 95 q2 ∷
   re 89 5 (CS03 ∷ []) ∷
   re 91 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 90 q3 ∷
   re 91 3 (CX13 ∷ []) ∷
   rw 91 q4 ∷
   rw⁻ 92 q5 ∷
   rw 93 q1 ∷
   re 94 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 96 q2 ∷
   re 90 5 (CS03 ∷ []) ∷
   re 92 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 91 q3 ∷
   re 92 3 (CX13 ∷ []) ∷
   rw 92 q4 ∷
   rw⁻ 93 q5 ∷
   rw 94 q1 ∷
   re 95 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 97 q2 ∷
   re 91 5 (CS03 ∷ []) ∷
   re 93 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 92 q3 ∷
   re 93 3 (CX13 ∷ []) ∷
   rw 93 q4 ∷
   rw⁻ 94 q5 ∷
   rw 95 q1 ∷
   re 96 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 98 q2 ∷
   re 92 5 (CS03 ∷ []) ∷
   re 94 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 93 q3 ∷
   re 94 3 (CX13 ∷ []) ∷
   rw 94 q4 ∷
   rw⁻ 95 q5 ∷
   rw 96 q1 ∷
   re 97 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 99 q2 ∷
   re 93 5 (CS03 ∷ []) ∷
   rw 94 q8 ∷
   re 93 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 95 q9 ∷
   rw 94 q10 ∷
   rw⁻ 93 q9 ∷
   re 94 3 (CS13 ∷ []) ∷
   re 92 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 94 q9 ∷
   rw 93 q10 ∷
   rw⁻ 92 q9 ∷
   re 93 3 (CS13 ∷ []) ∷
   re 91 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 93 q9 ∷
   rw 92 q10 ∷
   rw⁻ 91 q9 ∷
   re 92 3 (CS13 ∷ []) ∷
   re 90 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 92 q9 ∷
   rw 91 q10 ∷
   rw⁻ 90 q9 ∷
   re 91 3 (CS13 ∷ []) ∷
   re 89 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 91 q9 ∷
   rw 90 q10 ∷
   rw⁻ 89 q9 ∷
   re 90 3 (CS13 ∷ []) ∷
   re 88 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 90 q9 ∷
   rw 89 q10 ∷
   rw⁻ 88 q9 ∷
   re 89 3 (CS13 ∷ []) ∷
   re 87 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 89 q9 ∷
   rw 88 q10 ∷
   rw⁻ 87 q9 ∷
   re 88 3 (CS13 ∷ []) ∷
   re 86 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 88 q9 ∷
   rw 87 q10 ∷
   rw⁻ 86 q9 ∷
   re 87 3 (CS13 ∷ []) ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 87 q9 ∷
   rw 86 q10 ∷
   rw⁻ 85 q9 ∷
   re 86 3 (CS13 ∷ []) ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 86 q9 ∷
   rw 85 q10 ∷
   rw⁻ 84 q9 ∷
   re 85 3 (CS13 ∷ []) ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 85 q9 ∷
   rw 84 q10 ∷
   rw⁻ 83 q9 ∷
   re 84 3 (CS13 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 84 q9 ∷
   rw 83 q10 ∷
   rw⁻ 82 q9 ∷
   re 83 3 (CS13 ∷ []) ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 83 q9 ∷
   rw 82 q10 ∷
   rw⁻ 81 q9 ∷
   re 82 3 (CS13 ∷ []) ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 82 q9 ∷
   rw 81 q10 ∷
   rw⁻ 80 q9 ∷
   re 81 3 (CS13 ∷ []) ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 81 q9 ∷
   rw 80 q10 ∷
   rw⁻ 79 q9 ∷
   re 80 3 (CS13 ∷ []) ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 80 q9 ∷
   rw 79 q10 ∷
   rw⁻ 78 q9 ∷
   re 79 3 (CS13 ∷ []) ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 79 q9 ∷
   rw 78 q10 ∷
   rw⁻ 77 q9 ∷
   re 78 3 (CS13 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 78 q9 ∷
   rw 77 q10 ∷
   rw⁻ 76 q9 ∷
   re 77 3 (CS13 ∷ []) ∷
   rw⁻ 75 q11 ∷
   re 74 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 76 q9 ∷
   rw 75 q12 ∷
   rw⁻ 74 q9 ∷
   re 75 3 (CK31 ∷ []) ∷
   rw⁻ 73 q11 ∷
   rw⁻ 72 q11 ∷
   rw⁻ 71 q11 ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 72 q9 ∷
   rw 71 q10 ∷
   rw⁻ 70 q9 ∷
   re 71 3 (CS13 ∷ []) ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 71 q9 ∷
   rw 70 q10 ∷
   rw⁻ 69 q9 ∷
   re 70 3 (CS13 ∷ []) ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 70 q9 ∷
   rw 69 q10 ∷
   rw⁻ 68 q9 ∷
   re 69 3 (CS13 ∷ []) ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 69 q9 ∷
   rw 68 q10 ∷
   rw⁻ 67 q9 ∷
   re 68 3 (CS13 ∷ []) ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 68 q9 ∷
   rw 67 q10 ∷
   rw⁻ 66 q9 ∷
   re 67 3 (CS13 ∷ []) ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 67 q9 ∷
   rw 66 q10 ∷
   rw⁻ 65 q9 ∷
   re 66 3 (CS13 ∷ []) ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 66 q9 ∷
   rw 65 q10 ∷
   rw⁻ 64 q9 ∷
   re 65 3 (CS13 ∷ []) ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 65 q9 ∷
   rw 64 q10 ∷
   rw⁻ 63 q9 ∷
   re 64 3 (CS13 ∷ []) ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 64 q9 ∷
   rw 63 q10 ∷
   rw⁻ 62 q9 ∷
   re 63 3 (CS13 ∷ []) ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 63 q9 ∷
   rw 62 q10 ∷
   rw⁻ 61 q9 ∷
   re 62 3 (CS13 ∷ []) ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 62 q9 ∷
   rw 61 q10 ∷
   rw⁻ 60 q9 ∷
   re 61 3 (CS13 ∷ []) ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 61 q9 ∷
   rw 60 q10 ∷
   rw⁻ 59 q9 ∷
   re 60 3 (CS13 ∷ []) ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 60 q9 ∷
   rw 59 q10 ∷
   rw⁻ 58 q9 ∷
   re 59 3 (CS13 ∷ []) ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 59 q9 ∷
   rw 58 q10 ∷
   rw⁻ 57 q9 ∷
   re 58 3 (CS13 ∷ []) ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 58 q9 ∷
   rw 57 q10 ∷
   rw⁻ 56 q9 ∷
   re 57 3 (CS13 ∷ []) ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 57 q9 ∷
   rw 56 q10 ∷
   rw⁻ 55 q9 ∷
   re 56 3 (CS13 ∷ []) ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 56 q9 ∷
   rw 55 q10 ∷
   rw⁻ 54 q9 ∷
   re 55 3 (CS13 ∷ []) ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 55 q9 ∷
   rw 54 q10 ∷
   rw⁻ 53 q9 ∷
   re 54 3 (CS13 ∷ []) ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 54 q9 ∷
   rw 53 q10 ∷
   rw⁻ 52 q9 ∷
   re 53 3 (CS13 ∷ []) ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q9 ∷
   rw 52 q10 ∷
   rw⁻ 51 q9 ∷
   re 52 3 (CS13 ∷ []) ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q9 ∷
   rw 51 q10 ∷
   rw⁻ 50 q9 ∷
   re 51 3 (CS13 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q9 ∷
   rw 50 q10 ∷
   rw⁻ 49 q9 ∷
   re 50 3 (CS13 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q9 ∷
   rw 49 q10 ∷
   rw⁻ 48 q9 ∷
   re 49 3 (CS13 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q9 ∷
   rw 48 q10 ∷
   rw⁻ 47 q9 ∷
   re 48 3 (CS13 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q9 ∷
   rw 47 q10 ∷
   rw⁻ 46 q9 ∷
   re 47 3 (CS13 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q9 ∷
   rw 46 q10 ∷
   rw⁻ 45 q9 ∷
   re 46 3 (CS13 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q9 ∷
   rw 45 q10 ∷
   rw⁻ 44 q9 ∷
   re 45 3 (CS13 ∷ []) ∷
   rw 43 q10 ∷
   rw 42 q10 ∷
   rw 41 q10 ∷
   rw 40 q10 ∷
   rw 39 q10 ∷
   rw 38 q10 ∷
   rw⁻ 37 q13 ∷
   rw 36 q12 ∷
   rw 35 q10 ∷
   rw 34 q10 ∷
   rw 33 q10 ∷
   rw⁻ 32 q13 ∷
   rw 31 q12 ∷
   rw⁻ 30 q13 ∷
   rw 29 q12 ∷
   rw 30 q14 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q9 ∷
   rw 30 q15 ∷
   rw 31 q9 ∷
   re 29 3 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q9 ∷ []) Eq.refl

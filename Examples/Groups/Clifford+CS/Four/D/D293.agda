{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D293 (W : Ws) where

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
  q3 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q4 : Eqn
  q4 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q5 : Eqn
  q5 = eqn (CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ []) (CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ []) (wn 885 W)
  q6 : Eqn
  q6 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q7 : Eqn
  q7 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q8 : Eqn
  q8 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q10 : Eqn
  q10 = eqn (CX13 ∷ Sw12 ∷ []) (Sw12 ∷ CX23 ∷ []) (wn 36 W)
  q11 : Eqn
  q11 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q12 : Eqn
  q12 = eqn (CX23 ∷ Sw12 ∷ []) (Sw12 ∷ CX13 ∷ []) (wn 37 W)
  q13 : Eqn
  q13 = eqn (CX13 ∷ S2 ∷ []) (S2 ∷ CX13 ∷ []) (wn 883 W)
  q14 : Eqn
  q14 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q15 : Eqn
  q15 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (wn 617 W)

-- Bar(SSKSKK;1,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~1,2->0) part4: 195 steps
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part4 : ⟪ (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ X1 ∷ CX12 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part4 = derive (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ X1 ∷ CX12 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 85 q1 ∷
   rw⁻ 84 q2 ∷
   re 85 3 (CS13 ∷ []) ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 85 q2 ∷
   rw 84 q1 ∷
   rw⁻ 83 q2 ∷
   re 84 3 (CS13 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 84 q2 ∷
   rw 83 q1 ∷
   rw⁻ 82 q2 ∷
   re 83 3 (CS13 ∷ []) ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 83 q2 ∷
   rw 82 q1 ∷
   rw⁻ 81 q2 ∷
   re 82 3 (CS13 ∷ []) ∷
   rw⁻ 80 q3 ∷
   re 79 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 81 q2 ∷
   rw 80 q4 ∷
   rw⁻ 79 q2 ∷
   re 80 3 (CK31 ∷ []) ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 80 q2 ∷
   rw 79 q1 ∷
   rw⁻ 78 q2 ∷
   re 79 3 (CS13 ∷ []) ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 79 q2 ∷
   rw 78 q1 ∷
   rw⁻ 77 q2 ∷
   re 78 3 (CS13 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 78 q2 ∷
   rw 77 q1 ∷
   rw⁻ 76 q2 ∷
   re 77 3 (CS13 ∷ []) ∷
   rw⁻ 75 q3 ∷
   re 74 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 76 q2 ∷
   rw 75 q4 ∷
   rw⁻ 74 q2 ∷
   re 75 3 (CK31 ∷ []) ∷
   rw⁻ 73 q3 ∷
   re 72 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 74 q2 ∷
   rw 73 q4 ∷
   rw⁻ 72 q2 ∷
   re 73 3 (CK31 ∷ []) ∷
   rw 73 q5 ∷
   rw 72 q6 ∷
   rw 73 q7 ∷
   rw 74 q6 ∷
   rw 75 q7 ∷
   rw 76 q8 ∷
   rw 77 q8 ∷
   rw 78 q8 ∷
   rw 79 q6 ∷
   rw 80 q7 ∷
   rw 81 q8 ∷
   rw 82 q8 ∷
   rw 83 q8 ∷
   rw 84 q8 ∷
   rw 85 q8 ∷
   rw 86 q8 ∷
   re 88 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 87 q2 ∷
   rw 88 q6 ∷
   rw 89 q2 ∷
   re 87 3 (CK30 ∷ []) ∷
   rw 88 q3 ∷
   re 90 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 89 q2 ∷
   rw 90 q6 ∷
   rw 91 q2 ∷
   re 89 3 (CK30 ∷ []) ∷
   rw 90 q3 ∷
   re 92 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 91 q2 ∷
   rw 92 q8 ∷
   rw 93 q2 ∷
   re 91 3 (CS03 ∷ []) ∷
   re 93 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 92 q2 ∷
   rw 93 q8 ∷
   rw 94 q2 ∷
   re 92 3 (CS03 ∷ []) ∷
   re 94 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 93 q2 ∷
   rw 94 q8 ∷
   rw 95 q2 ∷
   re 93 3 (CS03 ∷ []) ∷
   re 95 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 94 q2 ∷
   rw 95 q6 ∷
   rw 96 q2 ∷
   re 94 3 (CK30 ∷ []) ∷
   rw 95 q3 ∷
   re 97 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 96 q2 ∷
   rw 97 q8 ∷
   rw 98 q2 ∷
   re 96 3 (CS03 ∷ []) ∷
   re 98 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 97 q2 ∷
   rw 98 q8 ∷
   rw 99 q2 ∷
   re 97 3 (CS03 ∷ []) ∷
   re 99 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 98 q2 ∷
   rw 99 q8 ∷
   rw 100 q2 ∷
   re 98 3 (CS03 ∷ []) ∷
   re 100 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 99 q2 ∷
   rw 100 q8 ∷
   rw 101 q2 ∷
   re 99 3 (CS03 ∷ []) ∷
   re 101 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 100 q2 ∷
   rw 101 q8 ∷
   rw 102 q2 ∷
   re 100 3 (CS03 ∷ []) ∷
   re 102 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 101 q2 ∷
   rw 102 q8 ∷
   rw 103 q2 ∷
   re 101 3 (CS03 ∷ []) ∷
   rw 102 q9 ∷
   re 72 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 71 q10 ∷
   rw⁻ 72 q11 ∷
   rw 73 q12 ∷
   re 71 3 (CK20 ∷ []) ∷
   rw 72 q13 ∷
   re 74 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 73 q10 ∷
   rw⁻ 74 q11 ∷
   rw 75 q12 ∷
   re 73 3 (CK20 ∷ []) ∷
   rw 74 q13 ∷
   re 76 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 75 q10 ∷
   rw⁻ 76 q14 ∷
   rw 77 q12 ∷
   re 75 3 (CS02 ∷ []) ∷
   re 77 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 76 q10 ∷
   rw⁻ 77 q14 ∷
   rw 78 q12 ∷
   re 76 3 (CS02 ∷ []) ∷
   re 78 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 77 q10 ∷
   rw⁻ 78 q14 ∷
   rw 79 q12 ∷
   re 77 3 (CS02 ∷ []) ∷
   re 79 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 78 q10 ∷
   rw⁻ 79 q11 ∷
   rw 80 q12 ∷
   re 78 3 (CK20 ∷ []) ∷
   rw 79 q13 ∷
   re 81 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 80 q10 ∷
   rw⁻ 81 q14 ∷
   rw 82 q12 ∷
   re 80 3 (CS02 ∷ []) ∷
   re 82 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 81 q10 ∷
   rw⁻ 82 q14 ∷
   rw 83 q12 ∷
   re 81 3 (CS02 ∷ []) ∷
   re 83 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 82 q10 ∷
   rw⁻ 83 q14 ∷
   rw 84 q12 ∷
   re 82 3 (CS02 ∷ []) ∷
   re 84 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 83 q10 ∷
   rw⁻ 84 q14 ∷
   rw 85 q12 ∷
   re 83 3 (CS02 ∷ []) ∷
   re 85 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 84 q10 ∷
   rw⁻ 85 q14 ∷
   rw 86 q12 ∷
   re 84 3 (CS02 ∷ []) ∷
   re 86 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 85 q10 ∷
   rw⁻ 86 q14 ∷
   rw 87 q12 ∷
   re 85 3 (CS02 ∷ []) ∷
   rw 65 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q17 : Eqn
  q17 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q18 : Eqn
  q18 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q19 : Eqn
  q19 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q20 : Eqn
  q20 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q21 : Eqn
  q21 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q22 : Eqn
  q22 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CX12 ∷ X1 ∷ []) (X1 ∷ CX12 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (wn 886 W)
  q23 : Eqn
  q23 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [X1 CX13 X1]: 109 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CX13-X1 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ CX13 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CX13 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CX13-X1 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ CX13 ∷ X1 ∷ []) (X1 ∷ CX13 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 32 q16 ∷
   rw 31 q17 ∷
   re 30 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 32 q18 ∷
   rw 29 q17 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q18 ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 29 q18 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q18 ∷
   re 25 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 27 q18 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q18 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q18 ∷
   re 22 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 24 q18 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q18 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q18 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q18 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q18 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q18 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q18 ∷
   rw 15 q19 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 16 q18 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q18 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q18 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q18 ∷
   rw 10 q19 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 11 q18 ∷
   rw 8 q19 ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 9 q18 ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 8 q18 ∷
   rw 5 q20 ∷
   rw 4 q20 ∷
   rw 3 q21 ∷
   rw 2 q20 ∷
   rw 1 q21 ∷
   rw 0 q21 ∷
   rw 1 q22 ∷
   rw⁻ 0 q17 ∷
   rw 3 q16 ∷
   re 1 3 (CX13 ∷ []) ∷
   rw⁻ 2 q17 ∷
   rw⁻ 3 q21 ∷
   rw⁻ 4 q21 ∷
   rw⁻ 5 q20 ∷
   rw⁻ 6 q21 ∷
   rw⁻ 7 q20 ∷
   rw⁻ 8 q20 ∷
   rw 11 q16 ∷
   re 9 3 (CX13 ∷ []) ∷
   rw 12 q16 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q23 ∷
   rw 14 q16 ∷
   re 12 3 (CK30 ∷ []) ∷
   rw 13 q23 ∷
   rw 16 q16 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 17 q16 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 18 q16 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 19 q16 ∷
   re 17 3 (CK30 ∷ []) ∷
   rw 18 q23 ∷
   rw 21 q16 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 22 q16 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 23 q16 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 24 q16 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 25 q16 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q16 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 27 q16 ∷
   re 25 3 (CX13 ∷ []) ∷
   rw 28 q16 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q16 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 30 q16 ∷
   re 28 3 (CK30 ∷ []) ∷
   rw 31 q16 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q16 ∷
   re 30 3 (CK30 ∷ []) ∷
   rw 33 q16 ∷
   re 31 3 (CK30 ∷ []) ∷
   rw 32 q18 ∷ []) Eq.refl

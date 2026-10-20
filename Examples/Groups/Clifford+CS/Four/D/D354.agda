{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D354 (W : Ws) where

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
  q2 = eqn (Sw12 ∷ CX31 ∷ []) (CX32 ∷ Sw12 ∷ []) (wn 113 W)
  q3 : Eqn
  q3 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q4 : Eqn
  q4 = eqn (Sw12 ∷ CX32 ∷ []) (CX31 ∷ Sw12 ∷ []) (wn 114 W)
  q5 : Eqn
  q5 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q6 : Eqn
  q6 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q7 : Eqn
  q7 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q8 : Eqn
  q8 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q9 : Eqn
  q9 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q10 : Eqn
  q10 = eqn (CS13 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ []) (wn 629 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
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

-- Bar(SSKSKK;2,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,1->0) part3: 500 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part3 : ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ X2 ∷ CS03 ∷ CX21 ∷ X2 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ X2 ∷ CX21 ∷ X2 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part3 = derive (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ X2 ∷ CS03 ∷ CX21 ∷ X2 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ X2 ∷ CX21 ∷ X2 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  (re 86 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 92 q1 ∷
   re 90 3 (CX31 ∷ []) ∷
   rw 89 q2 ∷
   rw 88 q3 ∷
   rw 87 q4 ∷
   re 87 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 86 q5 ∷
   re 87 5 (CS03 ∷ []) ∷
   rw 89 q6 ∷
   rw⁻ 88 q7 ∷
   re 87 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 89 q8 ∷
   rw 88 q9 ∷
   rw⁻ 87 q8 ∷
   re 88 3 (CS13 ∷ []) ∷
   rw 88 q10 ∷
   rw 87 q7 ∷
   re 89 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 88 q8 ∷
   rw 89 q11 ∷
   rw 90 q8 ∷
   re 88 3 (CS03 ∷ []) ∷
   rw 89 q12 ∷
   rw 84 q13 ∷
   rw 85 q6 ∷
   rw⁻ 84 q7 ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 85 q8 ∷
   rw 84 q9 ∷
   rw⁻ 83 q8 ∷
   re 84 3 (CS13 ∷ []) ∷
   rw 84 q10 ∷
   rw 83 q7 ∷
   re 85 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 84 q8 ∷
   rw 85 q11 ∷
   rw 86 q8 ∷
   re 84 3 (CS03 ∷ []) ∷
   rw 85 q12 ∷
   re 84 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 90 q1 ∷
   re 88 3 (CX31 ∷ []) ∷
   rw 87 q2 ∷
   rw 86 q3 ∷
   rw 85 q4 ∷
   re 85 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 84 q5 ∷
   re 85 5 (CS03 ∷ []) ∷
   rw 87 q6 ∷
   rw⁻ 86 q7 ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 87 q8 ∷
   rw 86 q9 ∷
   rw⁻ 85 q8 ∷
   re 86 3 (CS13 ∷ []) ∷
   rw 86 q10 ∷
   rw 85 q7 ∷
   re 87 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 86 q8 ∷
   rw 87 q11 ∷
   rw 88 q8 ∷
   re 86 3 (CS03 ∷ []) ∷
   rw 87 q12 ∷
   rw 84 q6 ∷
   rw⁻ 83 q7 ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 84 q8 ∷
   rw 83 q9 ∷
   rw⁻ 82 q8 ∷
   re 83 3 (CS13 ∷ []) ∷
   rw 83 q10 ∷
   rw 82 q7 ∷
   re 84 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 83 q8 ∷
   rw 84 q11 ∷
   rw 85 q8 ∷
   re 83 3 (CS03 ∷ []) ∷
   rw 84 q12 ∷
   re 83 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 89 q1 ∷
   re 87 3 (CX31 ∷ []) ∷
   rw 86 q2 ∷
   rw 85 q3 ∷
   rw 84 q4 ∷
   re 84 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 83 q5 ∷
   re 84 5 (CS03 ∷ []) ∷
   rw 86 q6 ∷
   rw⁻ 85 q7 ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 86 q8 ∷
   rw 85 q9 ∷
   rw⁻ 84 q8 ∷
   re 85 3 (CS13 ∷ []) ∷
   rw 85 q10 ∷
   rw 84 q7 ∷
   re 86 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 85 q8 ∷
   rw 86 q11 ∷
   rw 87 q8 ∷
   re 85 3 (CS03 ∷ []) ∷
   rw 86 q12 ∷
   rw 83 q6 ∷
   rw⁻ 82 q7 ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 83 q8 ∷
   rw 82 q9 ∷
   rw⁻ 81 q8 ∷
   re 82 3 (CS13 ∷ []) ∷
   rw 82 q10 ∷
   rw 81 q7 ∷
   re 83 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 82 q8 ∷
   rw 83 q11 ∷
   rw 84 q8 ∷
   re 82 3 (CS03 ∷ []) ∷
   rw 83 q12 ∷
   re 82 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 88 q1 ∷
   re 86 3 (CX31 ∷ []) ∷
   rw 85 q2 ∷
   rw 84 q3 ∷
   rw 83 q4 ∷
   re 83 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 82 q5 ∷
   re 83 5 (CS03 ∷ []) ∷
   rw 85 q6 ∷
   rw⁻ 84 q7 ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 85 q8 ∷
   rw 84 q9 ∷
   rw⁻ 83 q8 ∷
   re 84 3 (CS13 ∷ []) ∷
   rw 84 q10 ∷
   rw 83 q7 ∷
   re 85 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 84 q8 ∷
   rw 85 q11 ∷
   rw 86 q8 ∷
   re 84 3 (CS03 ∷ []) ∷
   rw 85 q12 ∷
   rw 82 q6 ∷
   rw⁻ 81 q7 ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 82 q8 ∷
   rw 81 q9 ∷
   rw⁻ 80 q8 ∷
   re 81 3 (CS13 ∷ []) ∷
   rw 81 q10 ∷
   rw 80 q7 ∷
   re 82 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 81 q8 ∷
   rw 82 q11 ∷
   rw 83 q8 ∷
   re 81 3 (CS03 ∷ []) ∷
   rw 82 q12 ∷
   re 81 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 87 q1 ∷
   re 85 3 (CX31 ∷ []) ∷
   rw 84 q2 ∷
   rw 83 q3 ∷
   rw 82 q4 ∷
   re 82 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 81 q5 ∷
   re 82 5 (CS03 ∷ []) ∷
   rw 84 q6 ∷
   rw⁻ 83 q7 ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 84 q8 ∷
   rw 83 q9 ∷
   rw⁻ 82 q8 ∷
   re 83 3 (CS13 ∷ []) ∷
   rw 83 q10 ∷
   rw 82 q7 ∷
   re 84 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 83 q8 ∷
   rw 84 q11 ∷
   rw 85 q8 ∷
   re 83 3 (CS03 ∷ []) ∷
   rw 84 q12 ∷
   rw 81 q6 ∷
   rw⁻ 80 q7 ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 81 q8 ∷
   rw 80 q9 ∷
   rw⁻ 79 q8 ∷
   re 80 3 (CS13 ∷ []) ∷
   rw 80 q10 ∷
   rw 79 q7 ∷
   re 81 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 80 q8 ∷
   rw 81 q11 ∷
   rw 82 q8 ∷
   re 80 3 (CS03 ∷ []) ∷
   rw 81 q12 ∷
   re 80 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 86 q1 ∷
   re 84 3 (CX31 ∷ []) ∷
   rw 83 q2 ∷
   rw 82 q3 ∷
   rw 81 q4 ∷
   re 81 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 80 q5 ∷
   re 81 5 (CS03 ∷ []) ∷
   rw 83 q6 ∷
   rw⁻ 82 q7 ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 83 q8 ∷
   rw 82 q9 ∷
   rw⁻ 81 q8 ∷
   re 82 3 (CS13 ∷ []) ∷
   rw 82 q10 ∷
   rw 81 q7 ∷
   re 83 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 82 q8 ∷
   rw 83 q11 ∷
   rw 84 q8 ∷
   re 82 3 (CS03 ∷ []) ∷
   rw 83 q12 ∷
   rw 80 q6 ∷
   rw⁻ 79 q7 ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 80 q8 ∷
   rw 79 q9 ∷
   rw⁻ 78 q8 ∷
   re 79 3 (CS13 ∷ []) ∷
   rw 79 q10 ∷
   rw 78 q7 ∷
   re 80 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 79 q8 ∷
   rw 80 q11 ∷
   rw 81 q8 ∷
   re 79 3 (CS03 ∷ []) ∷
   rw 80 q12 ∷
   re 79 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 85 q1 ∷
   re 83 3 (CX31 ∷ []) ∷
   rw 82 q2 ∷
   rw 81 q3 ∷
   rw 80 q4 ∷
   re 80 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 79 q5 ∷
   re 80 5 (CS03 ∷ []) ∷
   rw 82 q6 ∷
   rw⁻ 81 q7 ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 82 q8 ∷
   rw 81 q9 ∷
   rw⁻ 80 q8 ∷
   re 81 3 (CS13 ∷ []) ∷
   rw 81 q10 ∷
   rw 80 q7 ∷
   re 82 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 81 q8 ∷
   rw 82 q11 ∷
   rw 83 q8 ∷
   re 81 3 (CS03 ∷ []) ∷
   rw 82 q12 ∷
   rw⁻ 77 q14 ∷
   rw⁻ 78 q15 ∷
   rw⁻ 79 q14 ∷
   rw 78 q6 ∷
   rw⁻ 77 q7 ∷
   re 76 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 78 q8 ∷
   rw 77 q16 ∷
   rw⁻ 76 q8 ∷
   re 77 3 (CK31 ∷ []) ∷
   rw 77 q17 ∷
   rw 76 q7 ∷
   re 78 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 77 q8 ∷
   rw 78 q18 ∷
   rw 79 q8 ∷
   re 77 3 (CK30 ∷ []) ∷
   rw 78 q12 ∷
   re 77 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 83 q1 ∷
   re 81 3 (CX31 ∷ []) ∷
   rw 80 q2 ∷
   rw 79 q19 ∷
   rw 78 q4 ∷
   re 78 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 77 q5 ∷
   re 78 5 (CK30 ∷ []) ∷
   rw 80 q6 ∷
   rw⁻ 79 q7 ∷
   re 78 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 80 q8 ∷
   rw 79 q16 ∷
   rw⁻ 78 q8 ∷
   re 79 3 (CK31 ∷ []) ∷
   rw 79 q17 ∷
   rw 78 q7 ∷
   re 80 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 79 q8 ∷
   rw 80 q18 ∷
   rw 81 q8 ∷
   re 79 3 (CK30 ∷ []) ∷
   rw 80 q12 ∷
   rw 77 q6 ∷
   rw⁻ 76 q7 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 77 q8 ∷
   rw 76 q9 ∷
   rw⁻ 75 q8 ∷
   re 76 3 (CS13 ∷ []) ∷
   rw 76 q10 ∷
   rw 75 q7 ∷
   re 77 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 76 q8 ∷
   rw 77 q11 ∷
   rw 78 q8 ∷
   re 76 3 (CS03 ∷ []) ∷
   rw 77 q12 ∷
   re 76 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 82 q1 ∷
   re 80 3 (CX31 ∷ []) ∷
   rw 79 q2 ∷
   rw 78 q3 ∷
   rw 77 q4 ∷
   re 77 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 76 q5 ∷
   re 77 5 (CS03 ∷ []) ∷
   rw 79 q6 ∷
   rw⁻ 78 q7 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 79 q8 ∷
   rw 78 q9 ∷
   rw⁻ 77 q8 ∷
   re 78 3 (CS13 ∷ []) ∷
   rw 78 q10 ∷
   rw 77 q7 ∷
   re 79 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 78 q8 ∷
   rw 79 q11 ∷
   rw 80 q8 ∷
   re 78 3 (CS03 ∷ []) ∷
   rw 79 q12 ∷
   rw 76 q6 ∷
   rw⁻ 75 q7 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 76 q8 ∷
   rw 75 q9 ∷
   rw⁻ 74 q8 ∷
   re 75 3 (CS13 ∷ []) ∷
   rw 75 q10 ∷
   rw 74 q7 ∷
   re 76 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 75 q8 ∷
   rw 76 q11 ∷
   rw 77 q8 ∷
   re 75 3 (CS03 ∷ []) ∷
   rw 76 q12 ∷
   re 75 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 81 q1 ∷
   re 79 3 (CX31 ∷ []) ∷
   rw 78 q2 ∷
   rw 77 q3 ∷
   rw 76 q4 ∷
   re 76 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 75 q5 ∷
   re 76 5 (CS03 ∷ []) ∷
   rw 78 q6 ∷
   rw⁻ 77 q7 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 78 q8 ∷
   rw 77 q9 ∷
   rw⁻ 76 q8 ∷
   re 77 3 (CS13 ∷ []) ∷
   rw 77 q10 ∷
   rw 76 q7 ∷
   re 78 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 77 q8 ∷
   rw 78 q11 ∷
   rw 79 q8 ∷
   re 77 3 (CS03 ∷ []) ∷
   rw 78 q12 ∷
   rw 75 q6 ∷
   rw⁻ 74 q7 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 75 q8 ∷
   rw 74 q9 ∷
   rw⁻ 73 q8 ∷
   re 74 3 (CS13 ∷ []) ∷
   rw 74 q10 ∷
   rw 73 q7 ∷
   re 75 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 74 q8 ∷
   rw 75 q11 ∷
   rw 76 q8 ∷
   re 74 3 (CS03 ∷ []) ∷
   rw 75 q12 ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 80 q1 ∷
   re 78 3 (CX31 ∷ []) ∷
   rw 77 q2 ∷
   rw 76 q3 ∷
   rw 75 q4 ∷
   re 75 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 74 q5 ∷
   re 75 5 (CS03 ∷ []) ∷
   rw 77 q6 ∷
   rw⁻ 76 q7 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 77 q8 ∷
   rw 76 q9 ∷
   rw⁻ 75 q8 ∷
   re 76 3 (CS13 ∷ []) ∷
   rw 76 q10 ∷
   rw 75 q7 ∷
   re 77 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 76 q8 ∷
   rw 77 q11 ∷
   rw 78 q8 ∷
   re 76 3 (CS03 ∷ []) ∷
   rw 77 q12 ∷
   rw⁻ 72 q14 ∷
   rw⁻ 73 q15 ∷
   rw⁻ 74 q14 ∷
   rw 73 q6 ∷
   rw⁻ 72 q7 ∷
   re 71 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 73 q8 ∷
   rw 72 q16 ∷
   rw⁻ 71 q8 ∷
   re 72 3 (CK31 ∷ []) ∷
   rw 72 q17 ∷
   rw 71 q7 ∷
   re 73 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 72 q8 ∷
   rw 73 q18 ∷
   rw 74 q8 ∷
   re 72 3 (CK30 ∷ []) ∷
   rw 73 q12 ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 78 q1 ∷
   re 76 3 (CX31 ∷ []) ∷
   rw 75 q2 ∷
   rw 74 q19 ∷
   rw 73 q4 ∷
   re 73 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 72 q5 ∷
   re 73 5 (CK30 ∷ []) ∷
   rw 75 q6 ∷
   rw⁻ 74 q7 ∷
   re 73 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 75 q8 ∷
   rw 74 q16 ∷
   rw⁻ 73 q8 ∷
   re 74 3 (CK31 ∷ []) ∷
   rw 74 q17 ∷
   rw 73 q7 ∷
   re 75 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 74 q8 ∷
   rw 75 q18 ∷
   rw 76 q8 ∷
   re 74 3 (CK30 ∷ []) ∷
   rw 75 q12 ∷
   rw⁻ 70 q14 ∷
   rw⁻ 71 q15 ∷
   rw⁻ 72 q14 ∷
   rw 71 q6 ∷
   rw⁻ 70 q7 ∷
   re 69 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 71 q8 ∷
   rw 70 q16 ∷
   rw⁻ 69 q8 ∷
   re 70 3 (CK31 ∷ []) ∷
   rw 70 q17 ∷
   rw 69 q7 ∷
   re 71 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 70 q8 ∷
   rw 71 q18 ∷
   rw 72 q8 ∷
   re 70 3 (CK30 ∷ []) ∷
   rw 71 q12 ∷
   re 70 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 76 q1 ∷
   re 74 3 (CX31 ∷ []) ∷
   rw 73 q2 ∷
   rw 72 q19 ∷
   rw 71 q4 ∷
   re 71 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 70 q5 ∷
   re 71 5 (CK30 ∷ []) ∷
   rw 73 q6 ∷
   rw⁻ 72 q7 ∷
   re 71 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 73 q8 ∷
   rw 72 q16 ∷
   rw⁻ 71 q8 ∷
   re 72 3 (CK31 ∷ []) ∷
   rw 72 q17 ∷
   rw 71 q7 ∷
   re 73 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 72 q8 ∷
   rw 73 q18 ∷
   rw 74 q8 ∷ []) Eq.refl

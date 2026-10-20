{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D349 (W : Ws) where

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
  q1 = eqn (CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ []) (wn 880 W)
  q2 : Eqn
  q2 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q3 : Eqn
  q3 = eqn (Sw12 ∷ CX13 ∷ []) (CX23 ∷ Sw12 ∷ []) (wn 157 W)
  q4 : Eqn
  q4 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q5 : Eqn
  q5 = eqn (Sw12 ∷ CX23 ∷ []) (CX13 ∷ Sw12 ∷ []) (wn 158 W)
  q6 : Eqn
  q6 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q7 : Eqn
  q7 = eqn (X1 ∷ S2 ∷ []) (S2 ∷ X1 ∷ []) (low-comm ((X ↑)) (S))
  q8 : Eqn
  q8 = eqn (S2 ∷ CX13 ∷ []) (CX13 ∷ S2 ∷ []) (wn 625 W)
  q9 : Eqn
  q9 = eqn (CK20 ∷ X1 ∷ []) (X1 ∷ CK20 ∷ []) (wn 879 W)
  q10 : Eqn
  q10 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q11 : Eqn
  q11 = eqn (CX12 ∷ X1 ∷ CX13 ∷ X1 ∷ []) (X1 ∷ CX13 ∷ X1 ∷ CX12 ∷ []) (wn 956 W)
  q12 : Eqn
  q12 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q13 : Eqn
  q13 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q14 : Eqn
  q14 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q15 : Eqn
  q15 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ CX12 ∷ X1 ∷ []) (X1 ∷ CX12 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (wn 882 W)
  q16 : Eqn
  q16 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q18 : Eqn
  q18 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q20 : Eqn
  q20 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q21 : Eqn
  q21 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ []) (CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (wn 619 W)
  q22 : Eqn
  q22 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q23 : Eqn
  q23 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q24 : Eqn
  q24 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q25 : Eqn
  q25 = eqn (CX13 ∷ Sw12 ∷ []) (Sw12 ∷ CX23 ∷ []) (wn 36 W)
  q26 : Eqn
  q26 = eqn (CX23 ∷ Sw12 ∷ []) (Sw12 ∷ CX13 ∷ []) (wn 37 W)
  q27 : Eqn
  q27 = eqn (CX12 ∷ S3 ∷ []) (S3 ∷ CX12 ∷ []) (low₃-comm ((CX₀₁ ↑)) (S))
  q28 : Eqn
  q28 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q29 : Eqn
  q29 = eqn (CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ []) (CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ []) (wn 966 W)

-- Bar(SSKSKK;1,2->0) passes groups of WBar(KiKiSSSKiSSSSSS;~1,3->0) part4: 500 steps
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part4 : ⟪ (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ X1 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS02 ∷ X1 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ X1 ∷ CX13 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ Sw01 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part4 = derive (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ X1 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS02 ∷ X1 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ X1 ∷ CX13 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ Sw01 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (re 76 3 (CX13 ∷ []) ∷
   rw 77 q1 ∷
   rw 74 q1 ∷
   re 76 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 75 q2 ∷
   re 76 3 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 82 q2 ∷
   re 80 3 (CX13 ∷ []) ∷
   rw 79 q3 ∷
   rw 78 q4 ∷
   rw 77 q5 ∷
   re 77 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 76 q6 ∷
   re 77 5 (CS03 ∷ []) ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q6 ∷
   re 75 3 (CX13 ∷ []) ∷
   rw 76 q1 ∷
   rw 73 q1 ∷
   re 75 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 74 q2 ∷
   re 75 3 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 81 q2 ∷
   re 79 3 (CX13 ∷ []) ∷
   rw 78 q3 ∷
   rw 77 q4 ∷
   rw 76 q5 ∷
   re 76 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 75 q6 ∷
   re 76 5 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q6 ∷
   re 74 3 (CX13 ∷ []) ∷
   rw 75 q1 ∷
   rw⁻ 72 q7 ∷
   rw 73 q8 ∷
   rw⁻ 74 q7 ∷
   rw 71 q9 ∷
   re 73 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 72 q2 ∷
   re 73 3 (CK30 ∷ []) ∷
   re 73 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 79 q2 ∷
   re 77 3 (CX13 ∷ []) ∷
   rw 76 q3 ∷
   rw 75 q10 ∷
   rw 74 q5 ∷
   re 74 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 73 q6 ∷
   re 74 5 (CK30 ∷ []) ∷
   re 74 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 76 q6 ∷
   re 72 3 (CX13 ∷ []) ∷
   rw 73 q9 ∷
   rw⁻ 70 q7 ∷
   rw 71 q8 ∷
   rw⁻ 72 q7 ∷
   rw 69 q9 ∷
   re 71 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 70 q2 ∷
   re 71 3 (CK30 ∷ []) ∷
   re 71 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 77 q2 ∷
   re 75 3 (CX13 ∷ []) ∷
   rw 74 q3 ∷
   rw 73 q10 ∷
   rw 72 q5 ∷
   re 72 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 71 q6 ∷
   re 72 5 (CK30 ∷ []) ∷
   re 72 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 74 q6 ∷
   re 70 3 (CX13 ∷ []) ∷
   rw 71 q9 ∷
   rw 68 q11 ∷
   rw 71 q2 ∷
   rw 70 q12 ∷
   re 69 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 71 q6 ∷
   rw 68 q12 ∷
   rw 67 q13 ∷
   rw 66 q13 ∷
   rw 65 q14 ∷
   rw 64 q13 ∷
   rw 63 q14 ∷
   rw 62 q14 ∷
   rw 63 q15 ∷
   rw⁻ 62 q12 ∷
   rw 65 q2 ∷
   re 63 3 (CX13 ∷ []) ∷
   rw⁻ 64 q12 ∷
   rw⁻ 65 q14 ∷
   rw⁻ 66 q14 ∷
   rw⁻ 67 q13 ∷
   rw⁻ 68 q14 ∷
   rw⁻ 69 q13 ∷
   rw⁻ 70 q13 ∷
   rw 71 q6 ∷
   rw 109 q16 ∷
   re 108 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 110 q17 ∷
   rw 109 q18 ∷
   rw⁻ 108 q17 ∷
   re 109 3 (CS13 ∷ []) ∷
   re 107 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 109 q17 ∷
   rw 108 q18 ∷
   rw⁻ 107 q17 ∷
   re 108 3 (CS13 ∷ []) ∷
   re 106 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 108 q17 ∷
   rw 107 q18 ∷
   rw⁻ 106 q17 ∷
   re 107 3 (CS13 ∷ []) ∷
   re 105 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 107 q17 ∷
   rw 106 q18 ∷
   rw⁻ 105 q17 ∷
   re 106 3 (CS13 ∷ []) ∷
   re 104 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 106 q17 ∷
   rw 105 q18 ∷
   rw⁻ 104 q17 ∷
   re 105 3 (CS13 ∷ []) ∷
   re 103 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 105 q17 ∷
   rw 104 q18 ∷
   rw⁻ 103 q17 ∷
   re 104 3 (CS13 ∷ []) ∷
   rw⁻ 102 q19 ∷
   re 101 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 103 q17 ∷
   rw 102 q20 ∷
   rw⁻ 101 q17 ∷
   re 102 3 (CK31 ∷ []) ∷
   re 100 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 102 q17 ∷
   rw 101 q18 ∷
   rw⁻ 100 q17 ∷
   re 101 3 (CS13 ∷ []) ∷
   re 99 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 101 q17 ∷
   rw 100 q18 ∷
   rw⁻ 99 q17 ∷
   re 100 3 (CS13 ∷ []) ∷
   re 98 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 100 q17 ∷
   rw 99 q18 ∷
   rw⁻ 98 q17 ∷
   re 99 3 (CS13 ∷ []) ∷
   rw⁻ 97 q19 ∷
   re 96 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 98 q17 ∷
   rw 97 q20 ∷
   rw⁻ 96 q17 ∷
   re 97 3 (CK31 ∷ []) ∷
   rw⁻ 95 q19 ∷
   re 94 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 96 q17 ∷
   rw 95 q20 ∷
   rw⁻ 94 q17 ∷
   re 95 3 (CK31 ∷ []) ∷
   rw 93 q20 ∷
   rw 92 q20 ∷
   rw 91 q18 ∷
   rw 90 q20 ∷
   rw 89 q18 ∷
   rw 88 q18 ∷
   rw 89 q21 ∷
   re 89 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 88 q17 ∷
   rw 89 q22 ∷
   rw 90 q17 ∷
   re 88 3 (CK30 ∷ []) ∷
   rw 89 q19 ∷
   re 91 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 90 q17 ∷
   rw 91 q22 ∷
   rw 92 q17 ∷
   re 90 3 (CK30 ∷ []) ∷
   rw 91 q19 ∷
   re 93 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 92 q17 ∷
   rw 93 q23 ∷
   rw 94 q17 ∷
   re 92 3 (CS03 ∷ []) ∷
   re 94 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 93 q17 ∷
   rw 94 q23 ∷
   rw 95 q17 ∷
   re 93 3 (CS03 ∷ []) ∷
   re 95 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 94 q17 ∷
   rw 95 q23 ∷
   rw 96 q17 ∷
   re 94 3 (CS03 ∷ []) ∷
   re 96 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 95 q17 ∷
   rw 96 q22 ∷
   rw 97 q17 ∷
   re 95 3 (CK30 ∷ []) ∷
   rw 96 q19 ∷
   re 98 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 97 q17 ∷
   rw 98 q23 ∷
   rw 99 q17 ∷
   re 97 3 (CS03 ∷ []) ∷
   re 99 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 98 q17 ∷
   rw 99 q23 ∷
   rw 100 q17 ∷
   re 98 3 (CS03 ∷ []) ∷
   re 100 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 99 q17 ∷
   rw 100 q23 ∷
   rw 101 q17 ∷
   re 99 3 (CS03 ∷ []) ∷
   re 101 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 100 q17 ∷
   rw 101 q23 ∷
   rw 102 q17 ∷
   re 100 3 (CS03 ∷ []) ∷
   re 102 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 101 q17 ∷
   rw 102 q23 ∷
   rw 103 q17 ∷
   re 101 3 (CS03 ∷ []) ∷
   re 103 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 102 q17 ∷
   rw 103 q23 ∷
   rw 104 q17 ∷
   re 102 3 (CS03 ∷ []) ∷
   rw 103 q23 ∷
   rw 104 q23 ∷
   rw 105 q22 ∷
   rw 106 q23 ∷
   rw 107 q22 ∷
   rw 108 q22 ∷
   rw 109 q24 ∷
   re 88 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 87 q2 ∷
   re 88 3 (CX13 ∷ []) ∷
   rw 88 q25 ∷
   rw⁻ 89 q10 ∷
   rw 90 q26 ∷
   re 91 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 93 q6 ∷
   re 87 5 (CK30 ∷ []) ∷
   rw 88 q27 ∷
   re 90 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 89 q2 ∷
   re 90 3 (CX13 ∷ []) ∷
   rw 90 q25 ∷
   rw⁻ 91 q10 ∷
   rw 92 q26 ∷
   re 93 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 95 q6 ∷
   re 89 5 (CK30 ∷ []) ∷
   rw 90 q27 ∷
   re 92 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 91 q2 ∷
   re 92 3 (CX13 ∷ []) ∷
   rw 92 q25 ∷
   rw⁻ 93 q4 ∷
   rw 94 q26 ∷
   re 95 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 97 q6 ∷
   re 91 5 (CS03 ∷ []) ∷
   re 93 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 92 q2 ∷
   re 93 3 (CX13 ∷ []) ∷
   rw 93 q25 ∷
   rw⁻ 94 q4 ∷
   rw 95 q26 ∷
   re 96 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 98 q6 ∷
   re 92 5 (CS03 ∷ []) ∷
   re 94 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 93 q2 ∷
   re 94 3 (CX13 ∷ []) ∷
   rw 94 q25 ∷
   rw⁻ 95 q4 ∷
   rw 96 q26 ∷
   re 97 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 99 q6 ∷
   re 93 5 (CS03 ∷ []) ∷
   re 95 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 94 q2 ∷
   re 95 3 (CX13 ∷ []) ∷
   rw 95 q25 ∷
   rw⁻ 96 q10 ∷
   rw 97 q26 ∷
   re 98 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 100 q6 ∷
   re 94 5 (CK30 ∷ []) ∷
   rw 95 q27 ∷
   re 97 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 96 q2 ∷
   re 97 3 (CX13 ∷ []) ∷
   rw 97 q25 ∷
   rw⁻ 98 q4 ∷
   rw 99 q26 ∷
   re 100 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 102 q6 ∷
   re 96 5 (CS03 ∷ []) ∷
   re 98 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 97 q2 ∷
   re 98 3 (CX13 ∷ []) ∷
   rw 98 q25 ∷
   rw⁻ 99 q4 ∷
   rw 100 q26 ∷
   re 101 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 103 q6 ∷
   re 97 5 (CS03 ∷ []) ∷
   re 99 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 98 q2 ∷
   re 99 3 (CX13 ∷ []) ∷
   rw 99 q25 ∷
   rw⁻ 100 q4 ∷
   rw 101 q26 ∷
   re 102 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 104 q6 ∷
   re 98 5 (CS03 ∷ []) ∷
   re 100 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 99 q2 ∷
   re 100 3 (CX13 ∷ []) ∷
   rw 100 q25 ∷
   rw⁻ 101 q4 ∷
   rw 102 q26 ∷
   re 103 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 105 q6 ∷
   re 99 5 (CS03 ∷ []) ∷
   re 101 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 100 q2 ∷
   re 101 3 (CX13 ∷ []) ∷
   rw 101 q25 ∷
   rw⁻ 102 q4 ∷
   rw 103 q26 ∷
   re 104 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 106 q6 ∷
   re 100 5 (CS03 ∷ []) ∷
   re 102 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 101 q2 ∷
   re 102 3 (CX13 ∷ []) ∷
   rw 102 q25 ∷
   rw⁻ 103 q4 ∷
   rw 104 q26 ∷
   re 105 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 107 q6 ∷
   re 101 5 (CS03 ∷ []) ∷
   rw 102 q16 ∷
   re 101 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 103 q17 ∷
   rw 102 q18 ∷
   rw⁻ 101 q17 ∷
   re 102 3 (CS13 ∷ []) ∷
   re 100 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 102 q17 ∷
   rw 101 q18 ∷
   rw⁻ 100 q17 ∷
   re 101 3 (CS13 ∷ []) ∷
   re 99 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 101 q17 ∷
   rw 100 q18 ∷
   rw⁻ 99 q17 ∷
   re 100 3 (CS13 ∷ []) ∷
   re 98 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 100 q17 ∷
   rw 99 q18 ∷
   rw⁻ 98 q17 ∷
   re 99 3 (CS13 ∷ []) ∷
   re 97 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 99 q17 ∷
   rw 98 q18 ∷
   rw⁻ 97 q17 ∷
   re 98 3 (CS13 ∷ []) ∷
   re 96 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 98 q17 ∷
   rw 97 q18 ∷
   rw⁻ 96 q17 ∷
   re 97 3 (CS13 ∷ []) ∷
   rw⁻ 95 q19 ∷
   re 94 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 96 q17 ∷
   rw 95 q20 ∷
   rw⁻ 94 q17 ∷
   re 95 3 (CK31 ∷ []) ∷
   re 93 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 95 q17 ∷
   rw 94 q18 ∷
   rw⁻ 93 q17 ∷
   re 94 3 (CS13 ∷ []) ∷
   re 92 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 94 q17 ∷
   rw 93 q18 ∷
   rw⁻ 92 q17 ∷
   re 93 3 (CS13 ∷ []) ∷
   re 91 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 93 q17 ∷
   rw 92 q18 ∷
   rw⁻ 91 q17 ∷
   re 92 3 (CS13 ∷ []) ∷
   rw⁻ 90 q19 ∷
   re 89 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 91 q17 ∷
   rw 90 q20 ∷
   rw⁻ 89 q17 ∷
   re 90 3 (CK31 ∷ []) ∷
   rw⁻ 88 q19 ∷
   re 87 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 89 q17 ∷
   rw 88 q20 ∷
   rw⁻ 87 q17 ∷
   re 88 3 (CK31 ∷ []) ∷
   rw 86 q18 ∷
   rw 85 q18 ∷
   rw 84 q18 ∷
   rw 83 q18 ∷
   rw 82 q18 ∷
   rw 81 q18 ∷
   rw⁻ 80 q28 ∷
   rw 79 q20 ∷
   rw 78 q18 ∷
   rw 77 q18 ∷
   rw 76 q18 ∷
   rw⁻ 75 q28 ∷
   rw 74 q20 ∷
   rw⁻ 73 q28 ∷
   rw 72 q20 ∷
   rw 73 q29 ∷
   re 73 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 72 q17 ∷
   rw 73 q22 ∷
   rw 74 q17 ∷
   re 72 3 (CK30 ∷ []) ∷
   rw 73 q19 ∷
   re 75 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 74 q17 ∷
   rw 75 q22 ∷
   rw 76 q17 ∷
   re 74 3 (CK30 ∷ []) ∷
   rw 75 q19 ∷
   re 77 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 76 q17 ∷
   rw 77 q23 ∷
   rw 78 q17 ∷
   re 76 3 (CS03 ∷ []) ∷
   re 78 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 77 q17 ∷
   rw 78 q23 ∷
   rw 79 q17 ∷
   re 77 3 (CS03 ∷ []) ∷
   re 79 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 78 q17 ∷
   rw 79 q23 ∷
   rw 80 q17 ∷
   re 78 3 (CS03 ∷ []) ∷
   re 80 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 79 q17 ∷
   rw 80 q22 ∷
   rw 81 q17 ∷
   re 79 3 (CK30 ∷ []) ∷
   rw 80 q19 ∷
   re 82 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 81 q17 ∷
   rw 82 q23 ∷
   rw 83 q17 ∷
   re 81 3 (CS03 ∷ []) ∷
   re 83 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 82 q17 ∷
   rw 83 q23 ∷
   rw 84 q17 ∷
   re 82 3 (CS03 ∷ []) ∷
   re 84 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 83 q17 ∷
   rw 84 q23 ∷
   rw 85 q17 ∷
   re 83 3 (CS03 ∷ []) ∷
   re 85 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 84 q17 ∷
   rw 85 q23 ∷
   rw 86 q17 ∷
   re 84 3 (CS03 ∷ []) ∷
   re 86 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 85 q17 ∷
   rw 86 q23 ∷
   rw 87 q17 ∷
   re 85 3 (CS03 ∷ []) ∷
   re 87 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 86 q17 ∷
   rw 87 q23 ∷
   rw 88 q17 ∷
   re 86 3 (CS03 ∷ []) ∷
   rw 87 q22 ∷
   rw 88 q28 ∷
   rw 89 q22 ∷
   rw 90 q28 ∷
   rw 91 q23 ∷ []) Eq.refl

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D343 (W : Ws) where

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
  q1 = wE 3 W
  q2 : Eqn
  q2 = wE 880 W
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 157 W
  q5 : Eqn
  q5 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q6 : Eqn
  q6 = wE 158 W
  q7 : Eqn
  q7 = eqn (X1 ∷ S2 ∷ []) (S2 ∷ X1 ∷ []) (low-comm ((X ↑)) (S))
  q8 : Eqn
  q8 = wE 625 W
  q9 : Eqn
  q9 = wE 879 W
  q10 : Eqn
  q10 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q11 : Eqn
  q11 = wE 956 W
  q12 : Eqn
  q12 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q13 : Eqn
  q13 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q14 : Eqn
  q14 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q15 : Eqn
  q15 = wE 882 W
  q16 : Eqn
  q16 = wE 5 W
  q17 : Eqn
  q17 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q18 : Eqn
  q18 = wE 7 W
  q19 : Eqn
  q19 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q20 : Eqn
  q20 = wE 140 W
  q21 : Eqn
  q21 = wE 963 W
  q22 : Eqn
  q22 = wE 27 W
  q23 : Eqn
  q23 = wE 142 W
  q24 : Eqn
  q24 = wE 31 W
  q25 : Eqn
  q25 = wE 36 W
  q26 : Eqn
  q26 = wE 37 W
  q27 : Eqn
  q27 = eqn (CX12 ∷ S3 ∷ []) (S3 ∷ CX12 ∷ []) (low₃-comm ((CX₀₁ ↑)) (S))

-- Bar(SSKSKK;1,2->0) passes groups of WBar(SSSSSSKiSSSSSSSSS;~1,3->0) part5: 500 steps
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part5 : ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X1 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X1 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X1 ∷ CX13 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ CX13 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part5 = derive (X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X1 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X1 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) (X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X1 ∷ CX13 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ CX13 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (re 95 5 (CS03 ∷ []) ∷
   re 95 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 97 q1 ∷
   re 93 3 (CX13 ∷ []) ∷
   rw 94 q2 ∷
   rw 91 q2 ∷
   re 93 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 92 q3 ∷
   re 93 3 (CS03 ∷ []) ∷
   re 93 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 99 q3 ∷
   re 97 3 (CX13 ∷ []) ∷
   rw 96 q4 ∷
   rw 95 q5 ∷
   rw 94 q6 ∷
   re 94 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 93 q1 ∷
   re 94 5 (CS03 ∷ []) ∷
   re 94 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 96 q1 ∷
   re 92 3 (CX13 ∷ []) ∷
   rw 93 q2 ∷
   rw 90 q2 ∷
   re 92 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 91 q3 ∷
   re 92 3 (CS03 ∷ []) ∷
   re 92 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 98 q3 ∷
   re 96 3 (CX13 ∷ []) ∷
   rw 95 q4 ∷
   rw 94 q5 ∷
   rw 93 q6 ∷
   re 93 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 92 q1 ∷
   re 93 5 (CS03 ∷ []) ∷
   re 93 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 95 q1 ∷
   re 91 3 (CX13 ∷ []) ∷
   rw 92 q2 ∷
   rw 89 q2 ∷
   re 91 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 90 q3 ∷
   re 91 3 (CS03 ∷ []) ∷
   re 91 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 97 q3 ∷
   re 95 3 (CX13 ∷ []) ∷
   rw 94 q4 ∷
   rw 93 q5 ∷
   rw 92 q6 ∷
   re 92 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 91 q1 ∷
   re 92 5 (CS03 ∷ []) ∷
   re 92 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 94 q1 ∷
   re 90 3 (CX13 ∷ []) ∷
   rw 91 q2 ∷
   rw 88 q2 ∷
   re 90 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 89 q3 ∷
   re 90 3 (CS03 ∷ []) ∷
   re 90 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 96 q3 ∷
   re 94 3 (CX13 ∷ []) ∷
   rw 93 q4 ∷
   rw 92 q5 ∷
   rw 91 q6 ∷
   re 91 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 90 q1 ∷
   re 91 5 (CS03 ∷ []) ∷
   re 91 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 93 q1 ∷
   re 89 3 (CX13 ∷ []) ∷
   rw 90 q2 ∷
   rw⁻ 87 q7 ∷
   rw 88 q8 ∷
   rw⁻ 89 q7 ∷
   rw 86 q9 ∷
   re 88 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 87 q3 ∷
   re 88 3 (CK30 ∷ []) ∷
   re 88 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 94 q3 ∷
   re 92 3 (CX13 ∷ []) ∷
   rw 91 q4 ∷
   rw 90 q10 ∷
   rw 89 q6 ∷
   re 89 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 88 q1 ∷
   re 89 5 (CK30 ∷ []) ∷
   re 89 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 91 q1 ∷
   re 87 3 (CX13 ∷ []) ∷
   rw 88 q9 ∷
   rw 85 q2 ∷
   re 87 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 86 q3 ∷
   re 87 3 (CS03 ∷ []) ∷
   re 87 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 93 q3 ∷
   re 91 3 (CX13 ∷ []) ∷
   rw 90 q4 ∷
   rw 89 q5 ∷
   rw 88 q6 ∷
   re 88 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 87 q1 ∷
   re 88 5 (CS03 ∷ []) ∷
   re 88 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 90 q1 ∷
   re 86 3 (CX13 ∷ []) ∷
   rw 87 q2 ∷
   rw 84 q2 ∷
   re 86 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 85 q3 ∷
   re 86 3 (CS03 ∷ []) ∷
   re 86 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 92 q3 ∷
   re 90 3 (CX13 ∷ []) ∷
   rw 89 q4 ∷
   rw 88 q5 ∷
   rw 87 q6 ∷
   re 87 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 86 q1 ∷
   re 87 5 (CS03 ∷ []) ∷
   re 87 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 89 q1 ∷
   re 85 3 (CX13 ∷ []) ∷
   rw 86 q2 ∷
   rw 83 q2 ∷
   re 85 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 84 q3 ∷
   re 85 3 (CS03 ∷ []) ∷
   re 85 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 91 q3 ∷
   re 89 3 (CX13 ∷ []) ∷
   rw 88 q4 ∷
   rw 87 q5 ∷
   rw 86 q6 ∷
   re 86 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 85 q1 ∷
   re 86 5 (CS03 ∷ []) ∷
   re 86 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 88 q1 ∷
   re 84 3 (CX13 ∷ []) ∷
   rw 85 q2 ∷
   rw⁻ 82 q7 ∷
   rw 83 q8 ∷
   rw⁻ 84 q7 ∷
   rw 81 q9 ∷
   re 83 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 82 q3 ∷
   re 83 3 (CK30 ∷ []) ∷
   re 83 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 89 q3 ∷
   re 87 3 (CX13 ∷ []) ∷
   rw 86 q4 ∷
   rw 85 q10 ∷
   rw 84 q6 ∷
   re 84 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 83 q1 ∷
   re 84 5 (CK30 ∷ []) ∷
   re 84 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 86 q1 ∷
   re 82 3 (CX13 ∷ []) ∷
   rw 83 q9 ∷
   rw⁻ 80 q7 ∷
   rw 81 q8 ∷
   rw⁻ 82 q7 ∷
   rw 79 q9 ∷
   re 81 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 80 q3 ∷
   re 81 3 (CK30 ∷ []) ∷
   re 81 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 87 q3 ∷
   re 85 3 (CX13 ∷ []) ∷
   rw 84 q4 ∷
   rw 83 q10 ∷
   rw 82 q6 ∷
   re 82 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 81 q1 ∷
   re 82 5 (CK30 ∷ []) ∷
   re 82 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 84 q1 ∷
   re 80 3 (CX13 ∷ []) ∷
   rw 81 q9 ∷
   rw 78 q11 ∷
   rw 81 q3 ∷
   rw 80 q12 ∷
   re 79 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 81 q1 ∷
   rw 78 q12 ∷
   rw 77 q13 ∷
   rw 76 q13 ∷
   rw 75 q14 ∷
   rw 74 q13 ∷
   rw 73 q14 ∷
   rw 72 q14 ∷
   rw 73 q15 ∷
   rw⁻ 72 q12 ∷
   rw 75 q3 ∷
   re 73 3 (CX13 ∷ []) ∷
   rw⁻ 74 q12 ∷
   rw⁻ 75 q14 ∷
   rw⁻ 76 q14 ∷
   rw⁻ 77 q13 ∷
   rw⁻ 78 q14 ∷
   rw⁻ 79 q13 ∷
   rw⁻ 80 q13 ∷
   rw 81 q1 ∷
   rw 121 q16 ∷
   re 120 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 122 q17 ∷
   rw 121 q18 ∷
   rw⁻ 120 q17 ∷
   re 121 3 (CS13 ∷ []) ∷
   re 119 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 121 q17 ∷
   rw 120 q18 ∷
   rw⁻ 119 q17 ∷
   re 120 3 (CS13 ∷ []) ∷
   re 118 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 120 q17 ∷
   rw 119 q18 ∷
   rw⁻ 118 q17 ∷
   re 119 3 (CS13 ∷ []) ∷
   re 117 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 119 q17 ∷
   rw 118 q18 ∷
   rw⁻ 117 q17 ∷
   re 118 3 (CS13 ∷ []) ∷
   re 116 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 118 q17 ∷
   rw 117 q18 ∷
   rw⁻ 116 q17 ∷
   re 117 3 (CS13 ∷ []) ∷
   re 115 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 117 q17 ∷
   rw 116 q18 ∷
   rw⁻ 115 q17 ∷
   re 116 3 (CS13 ∷ []) ∷
   re 114 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 116 q17 ∷
   rw 115 q18 ∷
   rw⁻ 114 q17 ∷
   re 115 3 (CS13 ∷ []) ∷
   re 113 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 115 q17 ∷
   rw 114 q18 ∷
   rw⁻ 113 q17 ∷
   re 114 3 (CS13 ∷ []) ∷
   re 112 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 114 q17 ∷
   rw 113 q18 ∷
   rw⁻ 112 q17 ∷
   re 113 3 (CS13 ∷ []) ∷
   rw⁻ 111 q19 ∷
   re 110 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 112 q17 ∷
   rw 111 q20 ∷
   rw⁻ 110 q17 ∷
   re 111 3 (CK31 ∷ []) ∷
   re 109 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 111 q17 ∷
   rw 110 q18 ∷
   rw⁻ 109 q17 ∷
   re 110 3 (CS13 ∷ []) ∷
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
   rw 103 q20 ∷
   rw 102 q20 ∷
   rw 101 q18 ∷
   rw 100 q20 ∷
   rw 99 q18 ∷
   rw 98 q18 ∷
   rw 99 q21 ∷
   re 99 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 98 q17 ∷
   rw 99 q22 ∷
   rw 100 q17 ∷
   re 98 3 (CS03 ∷ []) ∷
   re 100 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 99 q17 ∷
   rw 100 q22 ∷
   rw 101 q17 ∷
   re 99 3 (CS03 ∷ []) ∷
   re 101 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 100 q17 ∷
   rw 101 q22 ∷
   rw 102 q17 ∷
   re 100 3 (CS03 ∷ []) ∷
   re 102 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 101 q17 ∷
   rw 102 q22 ∷
   rw 103 q17 ∷
   re 101 3 (CS03 ∷ []) ∷
   re 103 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 102 q17 ∷
   rw 103 q22 ∷
   rw 104 q17 ∷
   re 102 3 (CS03 ∷ []) ∷
   re 104 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 103 q17 ∷
   rw 104 q22 ∷
   rw 105 q17 ∷
   re 103 3 (CS03 ∷ []) ∷
   re 105 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 104 q17 ∷
   rw 105 q23 ∷
   rw 106 q17 ∷
   re 104 3 (CK30 ∷ []) ∷
   rw 105 q19 ∷
   re 107 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 106 q17 ∷
   rw 107 q22 ∷
   rw 108 q17 ∷
   re 106 3 (CS03 ∷ []) ∷
   re 108 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 107 q17 ∷
   rw 108 q22 ∷
   rw 109 q17 ∷
   re 107 3 (CS03 ∷ []) ∷
   re 109 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 108 q17 ∷
   rw 109 q22 ∷
   rw 110 q17 ∷
   re 108 3 (CS03 ∷ []) ∷
   re 110 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 109 q17 ∷
   rw 110 q22 ∷
   rw 111 q17 ∷
   re 109 3 (CS03 ∷ []) ∷
   re 111 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 110 q17 ∷
   rw 111 q22 ∷
   rw 112 q17 ∷
   re 110 3 (CS03 ∷ []) ∷
   re 112 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 111 q17 ∷
   rw 112 q22 ∷
   rw 113 q17 ∷
   re 111 3 (CS03 ∷ []) ∷
   re 113 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 112 q17 ∷
   rw 113 q22 ∷
   rw 114 q17 ∷
   re 112 3 (CS03 ∷ []) ∷
   re 114 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 113 q17 ∷
   rw 114 q22 ∷
   rw 115 q17 ∷
   re 113 3 (CS03 ∷ []) ∷
   re 115 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 114 q17 ∷
   rw 115 q22 ∷
   rw 116 q17 ∷
   re 114 3 (CS03 ∷ []) ∷
   rw 115 q22 ∷
   rw 116 q22 ∷
   rw 117 q23 ∷
   rw 118 q22 ∷
   rw 119 q23 ∷
   rw 120 q23 ∷
   rw 121 q24 ∷
   re 98 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 97 q3 ∷
   re 98 3 (CX13 ∷ []) ∷
   rw 98 q25 ∷
   rw⁻ 99 q5 ∷
   rw 100 q26 ∷
   re 101 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 103 q1 ∷
   re 97 5 (CS03 ∷ []) ∷
   re 99 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 98 q3 ∷
   re 99 3 (CX13 ∷ []) ∷
   rw 99 q25 ∷
   rw⁻ 100 q5 ∷
   rw 101 q26 ∷
   re 102 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 104 q1 ∷
   re 98 5 (CS03 ∷ []) ∷
   re 100 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 99 q3 ∷
   re 100 3 (CX13 ∷ []) ∷
   rw 100 q25 ∷
   rw⁻ 101 q5 ∷
   rw 102 q26 ∷
   re 103 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 105 q1 ∷
   re 99 5 (CS03 ∷ []) ∷
   re 101 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 100 q3 ∷
   re 101 3 (CX13 ∷ []) ∷
   rw 101 q25 ∷
   rw⁻ 102 q5 ∷
   rw 103 q26 ∷
   re 104 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 106 q1 ∷
   re 100 5 (CS03 ∷ []) ∷
   re 102 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 101 q3 ∷
   re 102 3 (CX13 ∷ []) ∷
   rw 102 q25 ∷
   rw⁻ 103 q5 ∷
   rw 104 q26 ∷
   re 105 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 107 q1 ∷
   re 101 5 (CS03 ∷ []) ∷
   re 103 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 102 q3 ∷
   re 103 3 (CX13 ∷ []) ∷
   rw 103 q25 ∷
   rw⁻ 104 q5 ∷
   rw 105 q26 ∷
   re 106 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 108 q1 ∷
   re 102 5 (CS03 ∷ []) ∷
   re 104 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 103 q3 ∷
   re 104 3 (CX13 ∷ []) ∷
   rw 104 q25 ∷
   rw⁻ 105 q10 ∷
   rw 106 q26 ∷
   re 107 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 109 q1 ∷
   re 103 5 (CK30 ∷ []) ∷
   rw 104 q27 ∷
   re 106 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 105 q3 ∷
   re 106 3 (CX13 ∷ []) ∷
   rw 106 q25 ∷
   rw⁻ 107 q5 ∷
   rw 108 q26 ∷
   re 109 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 111 q1 ∷
   re 105 5 (CS03 ∷ []) ∷
   re 107 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 106 q3 ∷
   re 107 3 (CX13 ∷ []) ∷
   rw 107 q25 ∷
   rw⁻ 108 q5 ∷
   rw 109 q26 ∷
   re 110 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 112 q1 ∷
   re 106 5 (CS03 ∷ []) ∷
   re 108 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 107 q3 ∷
   re 108 3 (CX13 ∷ []) ∷
   rw 108 q25 ∷
   rw⁻ 109 q5 ∷
   rw 110 q26 ∷
   re 111 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 113 q1 ∷
   re 107 5 (CS03 ∷ []) ∷
   re 109 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 108 q3 ∷
   re 109 3 (CX13 ∷ []) ∷
   rw 109 q25 ∷
   rw⁻ 110 q5 ∷
   rw 111 q26 ∷
   re 112 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 114 q1 ∷
   re 108 5 (CS03 ∷ []) ∷
   re 110 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 109 q3 ∷
   re 110 3 (CX13 ∷ []) ∷
   rw 110 q25 ∷
   rw⁻ 111 q5 ∷
   rw 112 q26 ∷
   re 113 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 115 q1 ∷
   re 109 5 (CS03 ∷ []) ∷
   re 111 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 110 q3 ∷
   re 111 3 (CX13 ∷ []) ∷
   rw 111 q25 ∷
   rw⁻ 112 q5 ∷
   rw 113 q26 ∷ []) Eq.refl

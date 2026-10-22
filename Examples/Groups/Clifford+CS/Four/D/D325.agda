{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D325 (W : Ws) where

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
  q1 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 157 W
  q5 : Eqn
  q5 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q6 : Eqn
  q6 = wE 158 W
  q7 : Eqn
  q7 = wE 880 W
  q8 : Eqn
  q8 = wE 879 W
  q9 : Eqn
  q9 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q10 : Eqn
  q10 = wE 881 W
  q11 : Eqn
  q11 = eqn (X1 ∷ S3 ∷ []) (S3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((S ↑)))
  q12 : Eqn
  q12 = eqn (CX12 ∷ S3 ∷ []) (S3 ∷ CX12 ∷ []) (low₃-comm ((CX₀₁ ↑)) (S))

-- Bar(SSSKSS;1,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~1,2->0) part3: 500 steps
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part3 : ⟪ (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ Sw23 ∷ X1 ∷ CS02 ∷ Sw23 ∷ CX12 ∷ X1 ∷ CS03 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ X1 ∷ Sw23 ∷ CX13 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part3 = derive (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ Sw23 ∷ X1 ∷ CS02 ∷ Sw23 ∷ CX12 ∷ X1 ∷ CS03 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ X1 ∷ Sw23 ∷ CX13 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ [])
  (rw⁻ 91 q1 ∷
   rw 94 q2 ∷
   re 92 3 (CS03 ∷ []) ∷
   rw 93 q3 ∷
   re 92 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 98 q2 ∷
   re 96 3 (CX13 ∷ []) ∷
   rw 95 q4 ∷
   rw 94 q5 ∷
   rw 93 q6 ∷
   re 93 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 92 q3 ∷
   re 93 5 (CS03 ∷ []) ∷
   rw 95 q2 ∷
   rw 94 q1 ∷
   re 93 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 95 q3 ∷
   rw 94 q7 ∷
   rw⁻ 93 q1 ∷
   rw 96 q2 ∷
   re 94 3 (CS03 ∷ []) ∷
   rw 95 q3 ∷
   rw 92 q2 ∷
   rw 91 q1 ∷
   re 90 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 92 q3 ∷
   rw 91 q8 ∷
   rw⁻ 90 q1 ∷
   rw 93 q2 ∷
   re 91 3 (CK30 ∷ []) ∷
   rw 92 q3 ∷
   re 91 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 97 q2 ∷
   re 95 3 (CX13 ∷ []) ∷
   rw 94 q4 ∷
   rw 93 q9 ∷
   rw 92 q6 ∷
   re 92 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 91 q3 ∷
   re 92 5 (CK30 ∷ []) ∷
   rw 94 q2 ∷
   rw 93 q1 ∷
   re 92 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 94 q3 ∷
   rw 93 q8 ∷
   rw⁻ 92 q1 ∷
   rw 95 q2 ∷
   re 93 3 (CK30 ∷ []) ∷
   rw 94 q3 ∷
   rw 91 q2 ∷
   rw 90 q1 ∷
   re 89 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 91 q3 ∷
   rw 90 q7 ∷
   rw⁻ 89 q1 ∷
   rw 92 q2 ∷
   re 90 3 (CS03 ∷ []) ∷
   rw 91 q3 ∷
   re 90 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 96 q2 ∷
   re 94 3 (CX13 ∷ []) ∷
   rw 93 q4 ∷
   rw 92 q5 ∷
   rw 91 q6 ∷
   re 91 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 90 q3 ∷
   re 91 5 (CS03 ∷ []) ∷
   rw 93 q2 ∷
   rw 92 q1 ∷
   re 91 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 93 q3 ∷
   rw 92 q7 ∷
   rw⁻ 91 q1 ∷
   rw 94 q2 ∷
   re 92 3 (CS03 ∷ []) ∷
   rw 93 q3 ∷
   rw 90 q2 ∷
   rw 89 q1 ∷
   re 88 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 90 q3 ∷
   rw 89 q7 ∷
   rw⁻ 88 q1 ∷
   rw 91 q2 ∷
   re 89 3 (CS03 ∷ []) ∷
   rw 90 q3 ∷
   re 89 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 95 q2 ∷
   re 93 3 (CX13 ∷ []) ∷
   rw 92 q4 ∷
   rw 91 q5 ∷
   rw 90 q6 ∷
   re 90 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 89 q3 ∷
   re 90 5 (CS03 ∷ []) ∷
   rw 92 q2 ∷
   rw 91 q1 ∷
   re 90 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 92 q3 ∷
   rw 91 q7 ∷
   rw⁻ 90 q1 ∷
   rw 93 q2 ∷
   re 91 3 (CS03 ∷ []) ∷
   rw 92 q3 ∷
   rw 89 q2 ∷
   rw 88 q1 ∷
   re 87 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 89 q3 ∷
   rw 88 q7 ∷
   rw⁻ 87 q1 ∷
   rw 90 q2 ∷
   re 88 3 (CS03 ∷ []) ∷
   rw 89 q3 ∷
   re 88 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 94 q2 ∷
   re 92 3 (CX13 ∷ []) ∷
   rw 91 q4 ∷
   rw 90 q5 ∷
   rw 89 q6 ∷
   re 89 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 88 q3 ∷
   re 89 5 (CS03 ∷ []) ∷
   rw 91 q2 ∷
   rw 90 q1 ∷
   re 89 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 91 q3 ∷
   rw 90 q7 ∷
   rw⁻ 89 q1 ∷
   rw 92 q2 ∷
   re 90 3 (CS03 ∷ []) ∷
   rw 91 q3 ∷
   rw 86 q10 ∷
   rw 87 q2 ∷
   rw 86 q1 ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 87 q3 ∷
   rw 86 q7 ∷
   rw⁻ 85 q1 ∷
   rw 88 q2 ∷
   re 86 3 (CS03 ∷ []) ∷
   rw 87 q3 ∷
   re 86 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 92 q2 ∷
   re 90 3 (CX13 ∷ []) ∷
   rw 89 q4 ∷
   rw 88 q5 ∷
   rw 87 q6 ∷
   re 87 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 86 q3 ∷
   re 87 5 (CS03 ∷ []) ∷
   rw 89 q2 ∷
   rw 88 q1 ∷
   re 87 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 89 q3 ∷
   rw 88 q7 ∷
   rw⁻ 87 q1 ∷
   rw 90 q2 ∷
   re 88 3 (CS03 ∷ []) ∷
   rw 89 q3 ∷
   rw 86 q2 ∷
   rw 85 q1 ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 86 q3 ∷
   rw 85 q7 ∷
   rw⁻ 84 q1 ∷
   rw 87 q2 ∷
   re 85 3 (CS03 ∷ []) ∷
   rw 86 q3 ∷
   re 85 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 91 q2 ∷
   re 89 3 (CX13 ∷ []) ∷
   rw 88 q4 ∷
   rw 87 q5 ∷
   rw 86 q6 ∷
   re 86 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 85 q3 ∷
   re 86 5 (CS03 ∷ []) ∷
   rw 88 q2 ∷
   rw 87 q1 ∷
   re 86 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 88 q3 ∷
   rw 87 q7 ∷
   rw⁻ 86 q1 ∷
   rw 89 q2 ∷
   re 87 3 (CS03 ∷ []) ∷
   rw 88 q3 ∷
   rw 85 q2 ∷
   rw 84 q1 ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 85 q3 ∷
   rw 84 q7 ∷
   rw⁻ 83 q1 ∷
   rw 86 q2 ∷
   re 84 3 (CS03 ∷ []) ∷
   rw 85 q3 ∷
   re 84 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 90 q2 ∷
   re 88 3 (CX13 ∷ []) ∷
   rw 87 q4 ∷
   rw 86 q5 ∷
   rw 85 q6 ∷
   re 85 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 84 q3 ∷
   re 85 5 (CS03 ∷ []) ∷
   rw 87 q2 ∷
   rw 86 q1 ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 87 q3 ∷
   rw 86 q7 ∷
   rw⁻ 85 q1 ∷
   rw 88 q2 ∷
   re 86 3 (CS03 ∷ []) ∷
   rw 87 q3 ∷
   rw 84 q2 ∷
   rw 83 q1 ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 84 q3 ∷
   rw 83 q7 ∷
   rw⁻ 82 q1 ∷
   rw 85 q2 ∷
   re 83 3 (CS03 ∷ []) ∷
   rw 84 q3 ∷
   re 83 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 89 q2 ∷
   re 87 3 (CX13 ∷ []) ∷
   rw 86 q4 ∷
   rw 85 q5 ∷
   rw 84 q6 ∷
   re 84 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 83 q3 ∷
   re 84 5 (CS03 ∷ []) ∷
   rw 86 q2 ∷
   rw 85 q1 ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 86 q3 ∷
   rw 85 q7 ∷
   rw⁻ 84 q1 ∷
   rw 87 q2 ∷
   re 85 3 (CS03 ∷ []) ∷
   rw 86 q3 ∷
   rw 83 q2 ∷
   rw 82 q1 ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 83 q3 ∷
   rw 82 q7 ∷
   rw⁻ 81 q1 ∷
   rw 84 q2 ∷
   re 82 3 (CS03 ∷ []) ∷
   rw 83 q3 ∷
   re 82 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 88 q2 ∷
   re 86 3 (CX13 ∷ []) ∷
   rw 85 q4 ∷
   rw 84 q5 ∷
   rw 83 q6 ∷
   re 83 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 82 q3 ∷
   re 83 5 (CS03 ∷ []) ∷
   rw 85 q2 ∷
   rw 84 q1 ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 85 q3 ∷
   rw 84 q7 ∷
   rw⁻ 83 q1 ∷
   rw 86 q2 ∷
   re 84 3 (CS03 ∷ []) ∷
   rw 85 q3 ∷
   rw 82 q2 ∷
   rw 81 q1 ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 82 q3 ∷
   rw 81 q7 ∷
   rw⁻ 80 q1 ∷
   rw 83 q2 ∷
   re 81 3 (CS03 ∷ []) ∷
   rw 82 q3 ∷
   re 81 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 87 q2 ∷
   re 85 3 (CX13 ∷ []) ∷
   rw 84 q4 ∷
   rw 83 q5 ∷
   rw 82 q6 ∷
   re 82 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 81 q3 ∷
   re 82 5 (CS03 ∷ []) ∷
   rw 84 q2 ∷
   rw 83 q1 ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 84 q3 ∷
   rw 83 q7 ∷
   rw⁻ 82 q1 ∷
   rw 85 q2 ∷
   re 83 3 (CS03 ∷ []) ∷
   rw 84 q3 ∷
   rw 81 q2 ∷
   rw 80 q1 ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 81 q3 ∷
   rw 80 q7 ∷
   rw⁻ 79 q1 ∷
   rw 82 q2 ∷
   re 80 3 (CS03 ∷ []) ∷
   rw 81 q3 ∷
   re 80 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 86 q2 ∷
   re 84 3 (CX13 ∷ []) ∷
   rw 83 q4 ∷
   rw 82 q5 ∷
   rw 81 q6 ∷
   re 81 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 80 q3 ∷
   re 81 5 (CS03 ∷ []) ∷
   rw 83 q2 ∷
   rw 82 q1 ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 83 q3 ∷
   rw 82 q7 ∷
   rw⁻ 81 q1 ∷
   rw 84 q2 ∷
   re 82 3 (CS03 ∷ []) ∷
   rw 83 q3 ∷
   rw 80 q2 ∷
   rw 79 q1 ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 80 q3 ∷
   rw 79 q7 ∷
   rw⁻ 78 q1 ∷
   rw 81 q2 ∷
   re 79 3 (CS03 ∷ []) ∷
   rw 80 q3 ∷
   re 79 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 85 q2 ∷
   re 83 3 (CX13 ∷ []) ∷
   rw 82 q4 ∷
   rw 81 q5 ∷
   rw 80 q6 ∷
   re 80 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 79 q3 ∷
   re 80 5 (CS03 ∷ []) ∷
   rw 82 q2 ∷
   rw 81 q1 ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 82 q3 ∷
   rw 81 q7 ∷
   rw⁻ 80 q1 ∷
   rw 83 q2 ∷
   re 81 3 (CS03 ∷ []) ∷
   rw 82 q3 ∷
   rw 79 q2 ∷
   rw 78 q1 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q3 ∷
   rw 78 q7 ∷
   rw⁻ 77 q1 ∷
   rw 80 q2 ∷
   re 78 3 (CS03 ∷ []) ∷
   rw 79 q3 ∷
   re 78 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 84 q2 ∷
   re 82 3 (CX13 ∷ []) ∷
   rw 81 q4 ∷
   rw 80 q5 ∷
   rw 79 q6 ∷
   re 79 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 78 q3 ∷
   re 79 5 (CS03 ∷ []) ∷
   rw 81 q2 ∷
   rw 80 q1 ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 81 q3 ∷
   rw 80 q7 ∷
   rw⁻ 79 q1 ∷
   rw 82 q2 ∷
   re 80 3 (CS03 ∷ []) ∷
   rw 81 q3 ∷
   rw⁻ 76 q11 ∷
   rw⁻ 77 q12 ∷
   rw⁻ 78 q11 ∷
   rw 77 q2 ∷
   rw 76 q1 ∷
   re 75 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 77 q3 ∷
   rw 76 q8 ∷
   rw⁻ 75 q1 ∷
   rw 78 q2 ∷
   re 76 3 (CK30 ∷ []) ∷
   rw 77 q3 ∷
   re 76 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 82 q2 ∷
   re 80 3 (CX13 ∷ []) ∷
   rw 79 q4 ∷
   rw 78 q9 ∷
   rw 77 q6 ∷
   re 77 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 76 q3 ∷
   re 77 5 (CK30 ∷ []) ∷
   rw 79 q2 ∷
   rw 78 q1 ∷
   re 77 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 79 q3 ∷
   rw 78 q8 ∷
   rw⁻ 77 q1 ∷
   rw 80 q2 ∷
   re 78 3 (CK30 ∷ []) ∷
   rw 79 q3 ∷
   rw 76 q2 ∷
   rw 75 q1 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q3 ∷
   rw 75 q7 ∷
   rw⁻ 74 q1 ∷
   rw 77 q2 ∷
   re 75 3 (CS03 ∷ []) ∷
   rw 76 q3 ∷
   re 75 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 81 q2 ∷
   re 79 3 (CX13 ∷ []) ∷
   rw 78 q4 ∷
   rw 77 q5 ∷
   rw 76 q6 ∷
   re 76 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 75 q3 ∷
   re 76 5 (CS03 ∷ []) ∷
   rw 78 q2 ∷
   rw 77 q1 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q3 ∷
   rw 77 q7 ∷
   rw⁻ 76 q1 ∷
   rw 79 q2 ∷
   re 77 3 (CS03 ∷ []) ∷
   rw 78 q3 ∷
   rw 75 q2 ∷
   rw 74 q1 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q3 ∷
   rw 74 q7 ∷
   rw⁻ 73 q1 ∷
   rw 76 q2 ∷
   re 74 3 (CS03 ∷ []) ∷
   rw 75 q3 ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 80 q2 ∷
   re 78 3 (CX13 ∷ []) ∷
   rw 77 q4 ∷
   rw 76 q5 ∷
   rw 75 q6 ∷
   re 75 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 74 q3 ∷
   re 75 5 (CS03 ∷ []) ∷
   rw 77 q2 ∷
   rw 76 q1 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q3 ∷
   rw 76 q7 ∷
   rw⁻ 75 q1 ∷
   rw 78 q2 ∷
   re 76 3 (CS03 ∷ []) ∷
   rw 77 q3 ∷
   rw 74 q2 ∷
   rw 73 q1 ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q3 ∷
   rw 73 q7 ∷
   rw⁻ 72 q1 ∷
   rw 75 q2 ∷
   re 73 3 (CS03 ∷ []) ∷
   rw 74 q3 ∷
   re 73 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 79 q2 ∷
   re 77 3 (CX13 ∷ []) ∷
   rw 76 q4 ∷
   rw 75 q5 ∷
   rw 74 q6 ∷
   re 74 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 73 q3 ∷
   re 74 5 (CS03 ∷ []) ∷
   rw 76 q2 ∷
   rw 75 q1 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q3 ∷
   rw 75 q7 ∷
   rw⁻ 74 q1 ∷
   rw 77 q2 ∷
   re 75 3 (CS03 ∷ []) ∷
   rw 76 q3 ∷
   rw 73 q2 ∷
   rw 72 q1 ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 73 q3 ∷
   rw 72 q7 ∷
   rw⁻ 71 q1 ∷
   rw 74 q2 ∷
   re 72 3 (CS03 ∷ []) ∷
   rw 73 q3 ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 78 q2 ∷
   re 76 3 (CX13 ∷ []) ∷
   rw 75 q4 ∷
   rw 74 q5 ∷
   rw 73 q6 ∷ []) Eq.refl

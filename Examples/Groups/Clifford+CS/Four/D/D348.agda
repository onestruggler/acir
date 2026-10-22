{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D348 (W : Ws) where

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
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 36 W
  q4 : Eqn
  q4 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q5 : Eqn
  q5 = wE 37 W
  q6 : Eqn
  q6 = eqn (CX12 ∷ S3 ∷ []) (S3 ∷ CX12 ∷ []) (low₃-comm ((CX₀₁ ↑)) (S))
  q7 : Eqn
  q7 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q8 : Eqn
  q8 = wE 464 W
  q9 : Eqn
  q9 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q10 : Eqn
  q10 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q11 : Eqn
  q11 = wE 614 W
  q12 : Eqn
  q12 = wE 151 W
  q13 : Eqn
  q13 = wE 879 W
  q14 : Eqn
  q14 = wE 157 W
  q15 : Eqn
  q15 = wE 158 W
  q16 : Eqn
  q16 = wE 880 W
  q17 : Eqn
  q17 = wE 956 W
  q18 : Eqn
  q18 = eqn (X1 ∷ S2 ∷ []) (S2 ∷ X1 ∷ []) (low-comm ((X ↑)) (S))
  q19 : Eqn
  q19 = wE 625 W

-- Bar(SSKSKK;1,2->0) passes groups of WBar(KiKiSSSKiSSSSSS;~1,3->0) part3: 500 steps
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part3 : ⟪ (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ CX13 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CX13 ∷ X1 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ X1 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS02 ∷ X1 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part3 = derive (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ CX13 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CX13 ∷ X1 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ X1 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS02 ∷ X1 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ [])
  (re 53 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 55 q1 ∷
   re 49 5 (CS03 ∷ []) ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q2 ∷
   re 51 3 (CX13 ∷ []) ∷
   rw 51 q3 ∷
   rw⁻ 52 q4 ∷
   rw 53 q5 ∷
   re 54 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 56 q1 ∷
   re 50 5 (CS03 ∷ []) ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q2 ∷
   re 52 3 (CX13 ∷ []) ∷
   rw 52 q3 ∷
   rw⁻ 53 q4 ∷
   rw 54 q5 ∷
   re 55 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 57 q1 ∷
   re 51 5 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q2 ∷
   re 53 3 (CX13 ∷ []) ∷
   rw 53 q3 ∷
   rw⁻ 54 q4 ∷
   rw 55 q5 ∷
   re 56 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 58 q1 ∷
   re 52 5 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q2 ∷
   re 54 3 (CX13 ∷ []) ∷
   rw 54 q3 ∷
   rw⁻ 55 q4 ∷
   rw 56 q5 ∷
   re 57 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 59 q1 ∷
   re 53 5 (CS03 ∷ []) ∷
   re 55 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q2 ∷
   re 55 3 (CX13 ∷ []) ∷
   rw 55 q3 ∷
   rw⁻ 56 q4 ∷
   rw 57 q5 ∷
   re 58 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 60 q1 ∷
   re 54 5 (CS03 ∷ []) ∷
   re 56 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q2 ∷
   re 56 3 (CX13 ∷ []) ∷
   rw 56 q3 ∷
   rw⁻ 57 q4 ∷
   rw 58 q5 ∷
   re 59 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 61 q1 ∷
   re 55 5 (CS03 ∷ []) ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q2 ∷
   re 57 3 (CX13 ∷ []) ∷
   rw 57 q3 ∷
   rw⁻ 58 q4 ∷
   rw 59 q5 ∷
   re 60 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 62 q1 ∷
   re 56 5 (CS03 ∷ []) ∷
   re 58 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 57 q2 ∷
   re 58 3 (CX13 ∷ []) ∷
   rw 58 q3 ∷
   rw⁻ 59 q4 ∷
   rw 60 q5 ∷
   re 61 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 63 q1 ∷
   re 57 5 (CS03 ∷ []) ∷
   rw 58 q6 ∷
   rw 59 q6 ∷
   rw 60 q6 ∷
   re 62 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 61 q2 ∷
   re 62 3 (CX13 ∷ []) ∷
   rw 62 q3 ∷
   rw⁻ 63 q7 ∷
   rw 64 q5 ∷
   re 65 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 67 q1 ∷
   re 61 5 (CK30 ∷ []) ∷
   rw 62 q6 ∷
   rw 63 q6 ∷
   rw 64 q6 ∷
   rw 65 q6 ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 66 q2 ∷
   re 67 3 (CX13 ∷ []) ∷
   rw 67 q3 ∷
   rw⁻ 68 q7 ∷
   rw 69 q5 ∷
   re 70 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 72 q1 ∷
   re 66 5 (CK30 ∷ []) ∷
   rw 67 q6 ∷
   rw 68 q2 ∷
   rw 67 q8 ∷
   re 66 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 68 q1 ∷
   rw 65 q8 ∷
   rw 64 q8 ∷
   rw 63 q8 ∷
   rw 62 q8 ∷
   re 61 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 63 q1 ∷
   rw 60 q8 ∷
   rw 59 q8 ∷
   rw 58 q8 ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q1 ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 58 q1 ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q1 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q1 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 55 q1 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 54 q1 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q1 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q1 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q1 ∷
   rw 48 q8 ∷
   re 47 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   rw 46 q8 ∷
   rw 45 q8 ∷
   rw 44 q8 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q1 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q1 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q1 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q1 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   rw 25 q9 ∷
   rw 24 q9 ∷
   rw 23 q10 ∷
   rw 22 q9 ∷
   rw 21 q10 ∷
   rw 20 q10 ∷
   rw 21 q11 ∷
   rw 22 q2 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 23 q2 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 24 q2 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 25 q2 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q2 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 27 q2 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 28 q2 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q2 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 30 q2 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 31 q2 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q2 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 33 q2 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 34 q2 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 35 q2 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 36 q2 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 37 q2 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 38 q2 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 39 q2 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 38 q12 ∷
   rw 39 q12 ∷
   rw 40 q12 ∷
   rw 43 q2 ∷
   re 41 3 (CK30 ∷ []) ∷
   rw 42 q12 ∷
   rw 45 q2 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 46 q2 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 47 q2 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 48 q2 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 49 q2 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 50 q2 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 51 q2 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 52 q2 ∷
   re 50 3 (CS03 ∷ []) ∷
   rw 53 q2 ∷
   re 51 3 (CS03 ∷ []) ∷
   rw 52 q12 ∷
   rw 53 q12 ∷
   rw 54 q12 ∷
   rw 57 q2 ∷
   re 55 3 (CK30 ∷ []) ∷
   rw 56 q12 ∷
   rw 57 q12 ∷
   rw 58 q12 ∷
   rw 59 q12 ∷
   rw 62 q2 ∷
   re 60 3 (CK30 ∷ []) ∷
   rw 61 q12 ∷
   rw⁻ 62 q10 ∷
   rw⁻ 63 q10 ∷
   rw⁻ 64 q9 ∷
   rw⁻ 65 q10 ∷
   rw⁻ 66 q9 ∷
   rw⁻ 67 q9 ∷
   rw 68 q1 ∷
   rw 90 q13 ∷
   re 92 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 91 q2 ∷
   re 92 3 (CK30 ∷ []) ∷
   re 92 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 98 q2 ∷
   re 96 3 (CX13 ∷ []) ∷
   rw 95 q14 ∷
   rw 94 q7 ∷
   rw 93 q15 ∷
   re 93 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 92 q1 ∷
   re 93 5 (CK30 ∷ []) ∷
   re 93 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 95 q1 ∷
   re 91 3 (CX13 ∷ []) ∷
   rw 92 q13 ∷
   rw 89 q13 ∷
   re 91 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 90 q2 ∷
   re 91 3 (CK30 ∷ []) ∷
   re 91 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 97 q2 ∷
   re 95 3 (CX13 ∷ []) ∷
   rw 94 q14 ∷
   rw 93 q7 ∷
   rw 92 q15 ∷
   re 92 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 91 q1 ∷
   re 92 5 (CK30 ∷ []) ∷
   re 92 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 94 q1 ∷
   re 90 3 (CX13 ∷ []) ∷
   rw 91 q13 ∷
   rw 88 q16 ∷
   re 90 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 89 q2 ∷
   re 90 3 (CS03 ∷ []) ∷
   re 90 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 96 q2 ∷
   re 94 3 (CX13 ∷ []) ∷
   rw 93 q14 ∷
   rw 92 q4 ∷
   rw 91 q15 ∷
   re 91 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 90 q1 ∷
   re 91 5 (CS03 ∷ []) ∷
   re 91 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 93 q1 ∷
   re 89 3 (CX13 ∷ []) ∷
   rw 90 q16 ∷
   rw 87 q13 ∷
   re 89 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 88 q2 ∷
   re 89 3 (CK30 ∷ []) ∷
   re 89 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 95 q2 ∷
   re 93 3 (CX13 ∷ []) ∷
   rw 92 q14 ∷
   rw 91 q7 ∷
   rw 90 q15 ∷
   re 90 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 89 q1 ∷
   re 90 5 (CK30 ∷ []) ∷
   re 90 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 92 q1 ∷
   re 88 3 (CX13 ∷ []) ∷
   rw 89 q13 ∷
   rw 86 q16 ∷
   re 88 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 87 q2 ∷
   re 88 3 (CS03 ∷ []) ∷
   re 88 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 94 q2 ∷
   re 92 3 (CX13 ∷ []) ∷
   rw 91 q14 ∷
   rw 90 q4 ∷
   rw 89 q15 ∷
   re 89 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 88 q1 ∷
   re 89 5 (CS03 ∷ []) ∷
   re 89 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 91 q1 ∷
   re 87 3 (CX13 ∷ []) ∷
   rw 88 q16 ∷
   rw 85 q16 ∷
   re 87 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 86 q2 ∷
   re 87 3 (CS03 ∷ []) ∷
   re 87 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 93 q2 ∷
   re 91 3 (CX13 ∷ []) ∷
   rw 90 q14 ∷
   rw 89 q4 ∷
   rw 88 q15 ∷
   re 88 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 87 q1 ∷
   re 88 5 (CS03 ∷ []) ∷
   re 88 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 90 q1 ∷
   re 86 3 (CX13 ∷ []) ∷
   rw 87 q16 ∷
   rw 84 q17 ∷
   rw 83 q16 ∷
   re 85 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 84 q2 ∷
   re 85 3 (CS03 ∷ []) ∷
   re 85 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 91 q2 ∷
   re 89 3 (CX13 ∷ []) ∷
   rw 88 q14 ∷
   rw 87 q4 ∷
   rw 86 q15 ∷
   re 86 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 85 q1 ∷
   re 86 5 (CS03 ∷ []) ∷
   re 86 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 88 q1 ∷
   re 84 3 (CX13 ∷ []) ∷
   rw 85 q16 ∷
   rw 82 q16 ∷
   re 84 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 83 q2 ∷
   re 84 3 (CS03 ∷ []) ∷
   re 84 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 90 q2 ∷
   re 88 3 (CX13 ∷ []) ∷
   rw 87 q14 ∷
   rw 86 q4 ∷
   rw 85 q15 ∷
   re 85 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 84 q1 ∷
   re 85 5 (CS03 ∷ []) ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 87 q1 ∷
   re 83 3 (CX13 ∷ []) ∷
   rw 84 q16 ∷
   rw 81 q16 ∷
   re 83 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 82 q2 ∷
   re 83 3 (CS03 ∷ []) ∷
   re 83 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 89 q2 ∷
   re 87 3 (CX13 ∷ []) ∷
   rw 86 q14 ∷
   rw 85 q4 ∷
   rw 84 q15 ∷
   re 84 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 83 q1 ∷
   re 84 5 (CS03 ∷ []) ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 86 q1 ∷
   re 82 3 (CX13 ∷ []) ∷
   rw 83 q16 ∷
   rw 80 q16 ∷
   re 82 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 81 q2 ∷
   re 82 3 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 88 q2 ∷
   re 86 3 (CX13 ∷ []) ∷
   rw 85 q14 ∷
   rw 84 q4 ∷
   rw 83 q15 ∷
   re 83 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 82 q1 ∷
   re 83 5 (CS03 ∷ []) ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 85 q1 ∷
   re 81 3 (CX13 ∷ []) ∷
   rw 82 q16 ∷
   rw 79 q16 ∷
   re 81 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 80 q2 ∷
   re 81 3 (CS03 ∷ []) ∷
   re 81 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 87 q2 ∷
   re 85 3 (CX13 ∷ []) ∷
   rw 84 q14 ∷
   rw 83 q4 ∷
   rw 82 q15 ∷
   re 82 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 81 q1 ∷
   re 82 5 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 84 q1 ∷
   re 80 3 (CX13 ∷ []) ∷
   rw 81 q16 ∷
   rw 78 q16 ∷
   re 80 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 79 q2 ∷
   re 80 3 (CS03 ∷ []) ∷
   re 80 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 86 q2 ∷
   re 84 3 (CX13 ∷ []) ∷
   rw 83 q14 ∷
   rw 82 q4 ∷
   rw 81 q15 ∷
   re 81 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 80 q1 ∷
   re 81 5 (CS03 ∷ []) ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 83 q1 ∷
   re 79 3 (CX13 ∷ []) ∷
   rw 80 q16 ∷
   rw⁻ 77 q18 ∷
   rw 78 q19 ∷
   rw⁻ 79 q18 ∷
   rw 76 q13 ∷
   re 78 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 77 q2 ∷
   re 78 3 (CK30 ∷ []) ∷
   re 78 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 84 q2 ∷
   re 82 3 (CX13 ∷ []) ∷
   rw 81 q14 ∷
   rw 80 q7 ∷
   rw 79 q15 ∷
   re 79 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 78 q1 ∷
   re 79 5 (CK30 ∷ []) ∷
   re 79 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 81 q1 ∷
   re 77 3 (CX13 ∷ []) ∷
   rw 78 q13 ∷
   rw 75 q16 ∷
   re 77 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 76 q2 ∷
   re 77 3 (CS03 ∷ []) ∷
   re 77 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 83 q2 ∷
   re 81 3 (CX13 ∷ []) ∷
   rw 80 q14 ∷
   rw 79 q4 ∷
   rw 78 q15 ∷
   re 78 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 77 q1 ∷
   re 78 5 (CS03 ∷ []) ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 80 q1 ∷ []) Eq.refl

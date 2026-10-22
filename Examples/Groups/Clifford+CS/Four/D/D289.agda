{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D289 (W : Ws) where

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
  q1 = wE 1 W
  q2 : Eqn
  q2 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q3 : Eqn
  q3 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q4 : Eqn
  q4 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q5 : Eqn
  q5 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 464 W
  q8 : Eqn
  q8 = wE 878 W
  q9 : Eqn
  q9 = wE 151 W
  q10 : Eqn
  q10 = wE 879 W
  q11 : Eqn
  q11 = wE 157 W
  q12 : Eqn
  q12 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q13 : Eqn
  q13 = wE 158 W
  q14 : Eqn
  q14 = wE 880 W
  q15 : Eqn
  q15 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q16 : Eqn
  q16 = wE 881 W
  q17 : Eqn
  q17 = eqn (X1 ∷ S3 ∷ []) (S3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((S ↑)))
  q18 : Eqn
  q18 = eqn (CX12 ∷ S3 ∷ []) (S3 ∷ CX12 ∷ []) (low₃-comm ((CX₀₁ ↑)) (S))

-- Bar(SSKSKK;1,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~1,2->0) part0: 500 steps
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part0 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ X1 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CX12 ∷ X1 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part0 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ X1 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CX12 ∷ X1 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ [])
  (rw 46 q1 ∷
   rw 45 q2 ∷
   rw 44 q3 ∷
   rw 43 q3 ∷
   rw 42 q3 ∷
   rw 41 q3 ∷
   rw 40 q3 ∷
   rw 39 q3 ∷
   rw 38 q4 ∷
   rw 37 q5 ∷
   rw 36 q3 ∷
   rw 35 q3 ∷
   rw 34 q3 ∷
   rw 33 q4 ∷
   rw 32 q5 ∷
   rw 31 q4 ∷
   rw 30 q5 ∷
   rw 29 q2 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q6 ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 29 q6 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q6 ∷
   re 25 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 27 q6 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q6 ∷
   re 22 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q6 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q6 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q6 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q6 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q6 ∷
   rw 15 q7 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 16 q6 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q6 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q6 ∷
   rw 10 q7 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   rw 8 q7 ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q5 ∷
   rw 4 q5 ∷
   rw 3 q3 ∷
   rw 2 q5 ∷
   rw 1 q3 ∷
   rw 0 q3 ∷
   rw 1 q8 ∷
   rw⁻ 0 q2 ∷
   rw⁻ 1 q5 ∷
   rw⁻ 2 q4 ∷
   rw⁻ 3 q5 ∷
   rw⁻ 4 q4 ∷
   rw⁻ 5 q3 ∷
   rw⁻ 6 q3 ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw⁻ 9 q4 ∷
   rw⁻ 10 q3 ∷
   rw⁻ 11 q3 ∷
   rw⁻ 12 q3 ∷
   rw⁻ 13 q3 ∷
   rw⁻ 14 q3 ∷
   rw⁻ 15 q3 ∷
   rw⁻ 16 q2 ∷
   rw⁻ 17 q3 ∷
   rw⁻ 18 q3 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 20 q3 ∷
   rw⁻ 21 q5 ∷
   rw⁻ 22 q5 ∷
   rw 25 q1 ∷
   re 23 3 (CX13 ∷ []) ∷
   rw 26 q1 ∷
   re 24 3 (CK30 ∷ []) ∷
   rw 25 q9 ∷
   rw 28 q1 ∷
   re 26 3 (CK30 ∷ []) ∷
   rw 27 q9 ∷
   rw 30 q1 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 31 q1 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CK30 ∷ []) ∷
   rw 32 q9 ∷
   rw 35 q1 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 36 q1 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 37 q1 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 38 q1 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 39 q1 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 40 q1 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 41 q1 ∷
   re 39 3 (CX13 ∷ []) ∷
   rw 42 q1 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 43 q1 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 44 q1 ∷
   re 42 3 (CK30 ∷ []) ∷
   rw 45 q1 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 46 q1 ∷
   re 44 3 (CK30 ∷ []) ∷
   rw 47 q1 ∷
   re 45 3 (CK30 ∷ []) ∷
   rw 46 q6 ∷
   rw 47 q1 ∷
   rw 46 q2 ∷
   re 45 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 47 q6 ∷
   rw 46 q10 ∷
   rw⁻ 45 q2 ∷
   rw 48 q1 ∷
   re 46 3 (CK30 ∷ []) ∷
   rw 47 q6 ∷
   re 46 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q1 ∷
   re 50 3 (CX13 ∷ []) ∷
   rw 49 q11 ∷
   rw 48 q12 ∷
   rw 47 q13 ∷
   re 47 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 46 q6 ∷
   re 47 5 (CK30 ∷ []) ∷
   rw 49 q1 ∷
   rw 48 q2 ∷
   re 47 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 49 q6 ∷
   rw 48 q10 ∷
   rw⁻ 47 q2 ∷
   rw 50 q1 ∷
   re 48 3 (CK30 ∷ []) ∷
   rw 49 q6 ∷
   rw 46 q1 ∷
   rw 45 q2 ∷
   re 44 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 46 q6 ∷
   rw 45 q10 ∷
   rw⁻ 44 q2 ∷
   rw 47 q1 ∷
   re 45 3 (CK30 ∷ []) ∷
   rw 46 q6 ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q1 ∷
   re 49 3 (CX13 ∷ []) ∷
   rw 48 q11 ∷
   rw 47 q12 ∷
   rw 46 q13 ∷
   re 46 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 45 q6 ∷
   re 46 5 (CK30 ∷ []) ∷
   rw 48 q1 ∷
   rw 47 q2 ∷
   re 46 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 48 q6 ∷
   rw 47 q10 ∷
   rw⁻ 46 q2 ∷
   rw 49 q1 ∷
   re 47 3 (CK30 ∷ []) ∷
   rw 48 q6 ∷
   rw 45 q1 ∷
   rw 44 q2 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q6 ∷
   rw 44 q14 ∷
   rw⁻ 43 q2 ∷
   rw 46 q1 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 45 q6 ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q1 ∷
   re 48 3 (CX13 ∷ []) ∷
   rw 47 q11 ∷
   rw 46 q15 ∷
   rw 45 q13 ∷
   re 45 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 44 q6 ∷
   re 45 5 (CS03 ∷ []) ∷
   rw 47 q1 ∷
   rw 46 q2 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q6 ∷
   rw 46 q14 ∷
   rw⁻ 45 q2 ∷
   rw 48 q1 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 47 q6 ∷
   rw 44 q1 ∷
   rw 43 q2 ∷
   re 42 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 44 q6 ∷
   rw 43 q10 ∷
   rw⁻ 42 q2 ∷
   rw 45 q1 ∷
   re 43 3 (CK30 ∷ []) ∷
   rw 44 q6 ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   re 47 3 (CX13 ∷ []) ∷
   rw 46 q11 ∷
   rw 45 q12 ∷
   rw 44 q13 ∷
   re 44 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 43 q6 ∷
   re 44 5 (CK30 ∷ []) ∷
   rw 46 q1 ∷
   rw 45 q2 ∷
   re 44 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 46 q6 ∷
   rw 45 q10 ∷
   rw⁻ 44 q2 ∷
   rw 47 q1 ∷
   re 45 3 (CK30 ∷ []) ∷
   rw 46 q6 ∷
   rw 43 q1 ∷
   rw 42 q2 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q6 ∷
   rw 42 q14 ∷
   rw⁻ 41 q2 ∷
   rw 44 q1 ∷
   re 42 3 (CS03 ∷ []) ∷
   rw 43 q6 ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q1 ∷
   re 46 3 (CX13 ∷ []) ∷
   rw 45 q11 ∷
   rw 44 q15 ∷
   rw 43 q13 ∷
   re 43 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 42 q6 ∷
   re 43 5 (CS03 ∷ []) ∷
   rw 45 q1 ∷
   rw 44 q2 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q6 ∷
   rw 44 q14 ∷
   rw⁻ 43 q2 ∷
   rw 46 q1 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 45 q6 ∷
   rw 42 q1 ∷
   rw 41 q2 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q6 ∷
   rw 41 q14 ∷
   rw⁻ 40 q2 ∷
   rw 43 q1 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 42 q6 ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   re 45 3 (CX13 ∷ []) ∷
   rw 44 q11 ∷
   rw 43 q15 ∷
   rw 42 q13 ∷
   re 42 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 41 q6 ∷
   re 42 5 (CS03 ∷ []) ∷
   rw 44 q1 ∷
   rw 43 q2 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q6 ∷
   rw 43 q14 ∷
   rw⁻ 42 q2 ∷
   rw 45 q1 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 44 q6 ∷
   rw 39 q16 ∷
   rw 40 q1 ∷
   rw 39 q2 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q6 ∷
   rw 39 q14 ∷
   rw⁻ 38 q2 ∷
   rw 41 q1 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 40 q6 ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q1 ∷
   re 43 3 (CX13 ∷ []) ∷
   rw 42 q11 ∷
   rw 41 q15 ∷
   rw 40 q13 ∷
   re 40 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 39 q6 ∷
   re 40 5 (CS03 ∷ []) ∷
   rw 42 q1 ∷
   rw 41 q2 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q6 ∷
   rw 41 q14 ∷
   rw⁻ 40 q2 ∷
   rw 43 q1 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 42 q6 ∷
   rw 39 q1 ∷
   rw 38 q2 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q6 ∷
   rw 38 q14 ∷
   rw⁻ 37 q2 ∷
   rw 40 q1 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 39 q6 ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   re 42 3 (CX13 ∷ []) ∷
   rw 41 q11 ∷
   rw 40 q15 ∷
   rw 39 q13 ∷
   re 39 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 38 q6 ∷
   re 39 5 (CS03 ∷ []) ∷
   rw 41 q1 ∷
   rw 40 q2 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q6 ∷
   rw 40 q14 ∷
   rw⁻ 39 q2 ∷
   rw 42 q1 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q6 ∷
   rw 38 q1 ∷
   rw 37 q2 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q6 ∷
   rw 37 q14 ∷
   rw⁻ 36 q2 ∷
   rw 39 q1 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 38 q6 ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   re 41 3 (CX13 ∷ []) ∷
   rw 40 q11 ∷
   rw 39 q15 ∷
   rw 38 q13 ∷
   re 38 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 37 q6 ∷
   re 38 5 (CS03 ∷ []) ∷
   rw 40 q1 ∷
   rw 39 q2 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q6 ∷
   rw 39 q14 ∷
   rw⁻ 38 q2 ∷
   rw 41 q1 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 40 q6 ∷
   rw 37 q1 ∷
   rw 36 q2 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q6 ∷
   rw 36 q14 ∷
   rw⁻ 35 q2 ∷
   rw 38 q1 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q6 ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   re 40 3 (CX13 ∷ []) ∷
   rw 39 q11 ∷
   rw 38 q15 ∷
   rw 37 q13 ∷
   re 37 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 36 q6 ∷
   re 37 5 (CS03 ∷ []) ∷
   rw 39 q1 ∷
   rw 38 q2 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q6 ∷
   rw 38 q14 ∷
   rw⁻ 37 q2 ∷
   rw 40 q1 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 39 q6 ∷
   rw 36 q1 ∷
   rw 35 q2 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q6 ∷
   rw 35 q14 ∷
   rw⁻ 34 q2 ∷
   rw 37 q1 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q6 ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   re 39 3 (CX13 ∷ []) ∷
   rw 38 q11 ∷
   rw 37 q15 ∷
   rw 36 q13 ∷
   re 36 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 35 q6 ∷
   re 36 5 (CS03 ∷ []) ∷
   rw 38 q1 ∷
   rw 37 q2 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q6 ∷
   rw 37 q14 ∷
   rw⁻ 36 q2 ∷
   rw 39 q1 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 38 q6 ∷
   rw 35 q1 ∷
   rw 34 q2 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q6 ∷
   rw 34 q14 ∷
   rw⁻ 33 q2 ∷
   rw 36 q1 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 35 q6 ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   re 38 3 (CX13 ∷ []) ∷
   rw 37 q11 ∷
   rw 36 q15 ∷
   rw 35 q13 ∷
   re 35 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 34 q6 ∷
   re 35 5 (CS03 ∷ []) ∷
   rw 37 q1 ∷
   rw 36 q2 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q6 ∷
   rw 36 q14 ∷
   rw⁻ 35 q2 ∷
   rw 38 q1 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q6 ∷
   rw⁻ 32 q17 ∷
   rw⁻ 33 q18 ∷
   rw⁻ 34 q17 ∷
   rw 33 q1 ∷
   rw 32 q2 ∷
   re 31 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 33 q6 ∷
   rw 32 q10 ∷
   rw⁻ 31 q2 ∷
   rw 34 q1 ∷
   re 32 3 (CK30 ∷ []) ∷
   rw 33 q6 ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q1 ∷
   re 36 3 (CX13 ∷ []) ∷
   rw 35 q11 ∷
   rw 34 q12 ∷
   rw 33 q13 ∷
   re 33 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 32 q6 ∷
   re 33 5 (CK30 ∷ []) ∷
   rw 35 q1 ∷
   rw 34 q2 ∷
   re 33 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 35 q6 ∷
   rw 34 q10 ∷
   rw⁻ 33 q2 ∷
   rw 36 q1 ∷
   re 34 3 (CK30 ∷ []) ∷
   rw 35 q6 ∷
   rw 32 q1 ∷
   rw 31 q2 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q6 ∷
   rw 31 q14 ∷
   rw⁻ 30 q2 ∷
   rw 33 q1 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 32 q6 ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷ []) Eq.refl

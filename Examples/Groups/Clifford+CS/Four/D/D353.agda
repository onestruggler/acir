{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D353 (W : Ws) where

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
  q2 = wE 968 W
  q3 : Eqn
  q3 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q4 : Eqn
  q4 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q5 : Eqn
  q5 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q6 : Eqn
  q6 = wE 1 W
  q7 : Eqn
  q7 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q8 : Eqn
  q8 = eqn (S1 ∷ CX23 ∷ []) (CX23 ∷ S1 ∷ []) (low-comm ((S ↑)) (CX₀₁))
  q9 : Eqn
  q9 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q10 : Eqn
  q10 = wE 464 W
  q11 : Eqn
  q11 = wE 969 W
  q12 : Eqn
  q12 = wE 151 W
  q13 : Eqn
  q13 = wE 5 W
  q14 : Eqn
  q14 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q15 : Eqn
  q15 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q16 : Eqn
  q16 = wE 140 W
  q17 : Eqn
  q17 = wE 630 W
  q18 : Eqn
  q18 = wE 142 W
  q19 : Eqn
  q19 = wE 31 W
  q20 : Eqn
  q20 = wE 113 W
  q21 : Eqn
  q21 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q22 : Eqn
  q22 = wE 114 W
  q23 : Eqn
  q23 = wE 7 W
  q24 : Eqn
  q24 = wE 629 W
  q25 : Eqn
  q25 = wE 27 W
  q26 : Eqn
  q26 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))

-- Bar(SSKSKK;2,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,1->0) part2: 500 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part2 : ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ Sw23 ∷ CK20 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ Sw23 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ X2 ∷ CS03 ∷ CX21 ∷ X2 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part2 = derive (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ Sw23 ∷ CK20 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ Sw23 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ X2 ∷ CS03 ∷ CX21 ∷ X2 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  (re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q1 ∷
   re 45 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q1 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q1 ∷
   rw 44 q2 ∷
   rw⁻ 43 q3 ∷
   rw⁻ 44 q3 ∷
   rw⁻ 45 q3 ∷
   rw⁻ 46 q3 ∷
   rw⁻ 47 q3 ∷
   rw⁻ 48 q3 ∷
   rw⁻ 49 q3 ∷
   rw⁻ 50 q3 ∷
   rw⁻ 51 q3 ∷
   rw⁻ 52 q3 ∷
   rw⁻ 53 q3 ∷
   rw⁻ 54 q3 ∷
   rw⁻ 55 q3 ∷
   rw⁻ 56 q3 ∷
   rw⁻ 57 q3 ∷
   rw⁻ 58 q3 ∷
   rw⁻ 59 q3 ∷
   rw⁻ 60 q3 ∷
   rw⁻ 61 q4 ∷
   rw⁻ 62 q4 ∷
   rw⁻ 63 q4 ∷
   rw⁻ 64 q5 ∷
   rw⁻ 65 q4 ∷
   rw⁻ 66 q3 ∷
   rw⁻ 67 q3 ∷
   rw⁻ 68 q3 ∷
   rw⁻ 69 q3 ∷
   rw⁻ 70 q3 ∷
   rw⁻ 71 q3 ∷
   rw⁻ 72 q3 ∷
   rw⁻ 73 q3 ∷
   rw⁻ 74 q3 ∷
   rw⁻ 75 q4 ∷
   rw⁻ 76 q4 ∷
   rw⁻ 77 q4 ∷
   rw⁻ 78 q5 ∷
   rw⁻ 79 q4 ∷
   rw⁻ 80 q4 ∷
   rw⁻ 81 q4 ∷
   rw⁻ 82 q4 ∷
   rw⁻ 83 q5 ∷
   rw⁻ 84 q4 ∷
   rw 87 q6 ∷
   re 85 3 (CS03 ∷ []) ∷
   rw 88 q6 ∷
   re 86 3 (CS03 ∷ []) ∷
   rw 89 q6 ∷
   re 87 3 (CK30 ∷ []) ∷
   rw 90 q6 ∷
   re 88 3 (CS03 ∷ []) ∷
   rw 91 q6 ∷
   re 89 3 (CK30 ∷ []) ∷
   rw 92 q6 ∷
   re 90 3 (CK30 ∷ []) ∷
   rw 91 q1 ∷
   rw⁻ 42 q7 ∷
   rw⁻ 43 q7 ∷
   rw⁻ 44 q7 ∷
   rw⁻ 45 q7 ∷
   rw⁻ 46 q7 ∷
   rw⁻ 47 q7 ∷
   rw⁻ 48 q7 ∷
   rw⁻ 49 q7 ∷
   rw⁻ 50 q7 ∷
   rw⁻ 51 q7 ∷
   rw⁻ 52 q7 ∷
   rw⁻ 53 q7 ∷
   rw⁻ 54 q7 ∷
   rw⁻ 55 q7 ∷
   rw⁻ 56 q7 ∷
   rw⁻ 57 q7 ∷
   rw⁻ 58 q7 ∷
   rw⁻ 59 q7 ∷
   rw⁻ 60 q8 ∷
   rw⁻ 61 q8 ∷
   rw⁻ 62 q8 ∷
   rw⁻ 63 q9 ∷
   rw⁻ 64 q8 ∷
   rw⁻ 65 q7 ∷
   rw⁻ 66 q7 ∷
   rw⁻ 67 q7 ∷
   rw⁻ 68 q7 ∷
   rw⁻ 69 q7 ∷
   rw⁻ 70 q7 ∷
   rw⁻ 71 q7 ∷
   rw⁻ 72 q7 ∷
   rw⁻ 73 q7 ∷
   rw⁻ 74 q8 ∷
   rw⁻ 75 q8 ∷
   rw⁻ 76 q8 ∷
   rw⁻ 77 q9 ∷
   rw⁻ 78 q8 ∷
   rw⁻ 79 q8 ∷
   rw⁻ 80 q8 ∷
   rw⁻ 81 q8 ∷
   rw⁻ 82 q9 ∷
   rw⁻ 83 q8 ∷
   rw 84 q6 ∷
   rw 83 q4 ∷
   rw 82 q5 ∷
   rw 81 q4 ∷
   rw 80 q4 ∷
   rw 79 q4 ∷
   rw 78 q4 ∷
   rw 77 q5 ∷
   rw 76 q4 ∷
   rw 75 q4 ∷
   rw 74 q4 ∷
   rw 73 q3 ∷
   rw 72 q3 ∷
   rw 71 q3 ∷
   rw 70 q3 ∷
   rw 69 q3 ∷
   rw 68 q3 ∷
   rw 67 q3 ∷
   rw 66 q3 ∷
   rw 65 q3 ∷
   rw 64 q4 ∷
   rw 63 q5 ∷
   rw 62 q4 ∷
   rw 61 q4 ∷
   rw 60 q4 ∷
   rw 59 q3 ∷
   rw 58 q3 ∷
   rw 57 q3 ∷
   rw 56 q3 ∷
   rw 55 q3 ∷
   rw 54 q3 ∷
   rw 53 q3 ∷
   rw 52 q3 ∷
   rw 51 q3 ∷
   rw 50 q3 ∷
   rw 49 q3 ∷
   rw 48 q3 ∷
   rw 47 q3 ∷
   rw 46 q3 ∷
   rw 45 q3 ∷
   rw 44 q3 ∷
   rw 43 q3 ∷
   rw 42 q3 ∷
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
   rw 35 q10 ∷
   re 34 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   rw 30 q10 ∷
   re 29 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   rw 28 q10 ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   rw 28 q11 ∷
   rw⁻ 27 q3 ∷
   rw⁻ 28 q3 ∷
   rw⁻ 29 q3 ∷
   rw⁻ 30 q3 ∷
   rw⁻ 31 q3 ∷
   rw⁻ 32 q3 ∷
   rw⁻ 33 q3 ∷
   rw⁻ 34 q3 ∷
   rw⁻ 35 q3 ∷
   rw⁻ 36 q3 ∷
   rw⁻ 37 q3 ∷
   rw⁻ 38 q3 ∷
   rw⁻ 39 q3 ∷
   rw⁻ 40 q3 ∷
   rw⁻ 41 q3 ∷
   rw⁻ 42 q3 ∷
   rw⁻ 43 q3 ∷
   rw⁻ 44 q3 ∷
   rw⁻ 45 q4 ∷
   rw⁻ 46 q4 ∷
   rw⁻ 47 q4 ∷
   rw⁻ 48 q5 ∷
   rw⁻ 49 q4 ∷
   rw⁻ 50 q3 ∷
   rw⁻ 51 q3 ∷
   rw⁻ 52 q3 ∷
   rw⁻ 53 q3 ∷
   rw⁻ 54 q3 ∷
   rw⁻ 55 q3 ∷
   rw⁻ 56 q3 ∷
   rw⁻ 57 q3 ∷
   rw⁻ 58 q3 ∷
   rw⁻ 59 q4 ∷
   rw⁻ 60 q4 ∷
   rw⁻ 61 q4 ∷
   rw⁻ 62 q5 ∷
   rw⁻ 63 q4 ∷
   rw⁻ 64 q4 ∷
   rw⁻ 65 q4 ∷
   rw⁻ 66 q4 ∷
   rw⁻ 67 q5 ∷
   rw⁻ 68 q4 ∷
   rw 71 q6 ∷
   re 69 3 (CK30 ∷ []) ∷
   rw 70 q12 ∷
   rw 73 q6 ∷
   re 71 3 (CK30 ∷ []) ∷
   rw 72 q12 ∷
   rw 75 q6 ∷
   re 73 3 (CS03 ∷ []) ∷
   rw 76 q6 ∷
   re 74 3 (CS03 ∷ []) ∷
   rw 77 q6 ∷
   re 75 3 (CS03 ∷ []) ∷
   rw 78 q6 ∷
   re 76 3 (CK30 ∷ []) ∷
   rw 77 q12 ∷
   rw 80 q6 ∷
   re 78 3 (CS03 ∷ []) ∷
   rw 81 q6 ∷
   re 79 3 (CS03 ∷ []) ∷
   rw 82 q6 ∷
   re 80 3 (CS03 ∷ []) ∷
   rw 83 q6 ∷
   re 81 3 (CS03 ∷ []) ∷
   rw 84 q6 ∷
   re 82 3 (CS03 ∷ []) ∷
   rw 85 q6 ∷
   re 83 3 (CS03 ∷ []) ∷
   rw 84 q1 ∷
   rw⁻ 26 q7 ∷
   rw⁻ 27 q7 ∷
   rw⁻ 28 q7 ∷
   rw⁻ 29 q7 ∷
   rw⁻ 30 q7 ∷
   rw⁻ 31 q7 ∷
   rw⁻ 32 q7 ∷
   rw⁻ 33 q7 ∷
   rw⁻ 34 q7 ∷
   rw⁻ 35 q7 ∷
   rw⁻ 36 q7 ∷
   rw⁻ 37 q7 ∷
   rw⁻ 38 q7 ∷
   rw⁻ 39 q7 ∷
   rw⁻ 40 q7 ∷
   rw⁻ 41 q7 ∷
   rw⁻ 42 q7 ∷
   rw⁻ 43 q7 ∷
   rw⁻ 44 q8 ∷
   rw⁻ 45 q8 ∷
   rw⁻ 46 q8 ∷
   rw⁻ 47 q9 ∷
   rw⁻ 48 q8 ∷
   rw⁻ 49 q7 ∷
   rw⁻ 50 q7 ∷
   rw⁻ 51 q7 ∷
   rw⁻ 52 q7 ∷
   rw⁻ 53 q7 ∷
   rw⁻ 54 q7 ∷
   rw⁻ 55 q7 ∷
   rw⁻ 56 q7 ∷
   rw⁻ 57 q7 ∷
   rw⁻ 58 q8 ∷
   rw⁻ 59 q8 ∷
   rw⁻ 60 q8 ∷
   rw⁻ 61 q9 ∷
   rw⁻ 62 q8 ∷
   rw⁻ 63 q8 ∷
   rw⁻ 64 q8 ∷
   rw⁻ 65 q8 ∷
   rw⁻ 66 q9 ∷
   rw⁻ 67 q8 ∷
   rw 20 q2 ∷
   rw 92 q13 ∷
   rw⁻ 91 q14 ∷
   re 90 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 92 q15 ∷
   rw 91 q16 ∷
   rw⁻ 90 q15 ∷
   re 91 3 (CK31 ∷ []) ∷
   rw 91 q17 ∷
   rw 90 q14 ∷
   re 92 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 91 q15 ∷
   rw 92 q18 ∷
   rw 93 q15 ∷
   re 91 3 (CK30 ∷ []) ∷
   rw 92 q19 ∷
   re 91 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 97 q6 ∷
   re 95 3 (CX31 ∷ []) ∷
   rw 94 q20 ∷
   rw 93 q21 ∷
   rw 92 q22 ∷
   re 92 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 91 q1 ∷
   re 92 5 (CK30 ∷ []) ∷
   rw 94 q13 ∷
   rw⁻ 93 q14 ∷
   re 92 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 94 q15 ∷
   rw 93 q16 ∷
   rw⁻ 92 q15 ∷
   re 93 3 (CK31 ∷ []) ∷
   rw 93 q17 ∷
   rw 92 q14 ∷
   re 94 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 93 q15 ∷
   rw 94 q18 ∷
   rw 95 q15 ∷
   re 93 3 (CK30 ∷ []) ∷
   rw 94 q19 ∷
   rw 91 q13 ∷
   rw⁻ 90 q14 ∷
   re 89 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 91 q15 ∷
   rw 90 q16 ∷
   rw⁻ 89 q15 ∷
   re 90 3 (CK31 ∷ []) ∷
   rw 90 q17 ∷
   rw 89 q14 ∷
   re 91 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 90 q15 ∷
   rw 91 q18 ∷
   rw 92 q15 ∷
   re 90 3 (CK30 ∷ []) ∷
   rw 91 q19 ∷
   re 90 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 96 q6 ∷
   re 94 3 (CX31 ∷ []) ∷
   rw 93 q20 ∷
   rw 92 q21 ∷
   rw 91 q22 ∷
   re 91 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 90 q1 ∷
   re 91 5 (CK30 ∷ []) ∷
   rw 93 q13 ∷
   rw⁻ 92 q14 ∷
   re 91 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 93 q15 ∷
   rw 92 q16 ∷
   rw⁻ 91 q15 ∷
   re 92 3 (CK31 ∷ []) ∷
   rw 92 q17 ∷
   rw 91 q14 ∷
   re 93 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 92 q15 ∷
   rw 93 q18 ∷
   rw 94 q15 ∷
   re 92 3 (CK30 ∷ []) ∷
   rw 93 q19 ∷
   rw 90 q13 ∷
   rw⁻ 89 q14 ∷
   re 88 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 90 q15 ∷
   rw 89 q23 ∷
   rw⁻ 88 q15 ∷
   re 89 3 (CS13 ∷ []) ∷
   rw 89 q24 ∷
   rw 88 q14 ∷
   re 90 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 89 q15 ∷
   rw 90 q25 ∷
   rw 91 q15 ∷
   re 89 3 (CS03 ∷ []) ∷
   rw 90 q19 ∷
   re 89 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 95 q6 ∷
   re 93 3 (CX31 ∷ []) ∷
   rw 92 q20 ∷
   rw 91 q26 ∷
   rw 90 q22 ∷
   re 90 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 89 q1 ∷
   re 90 5 (CS03 ∷ []) ∷
   rw 92 q13 ∷
   rw⁻ 91 q14 ∷
   re 90 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 92 q15 ∷
   rw 91 q23 ∷
   rw⁻ 90 q15 ∷
   re 91 3 (CS13 ∷ []) ∷
   rw 91 q24 ∷
   rw 90 q14 ∷
   re 92 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 91 q15 ∷
   rw 92 q25 ∷
   rw 93 q15 ∷
   re 91 3 (CS03 ∷ []) ∷
   rw 92 q19 ∷
   rw 89 q13 ∷
   rw⁻ 88 q14 ∷
   re 87 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 89 q15 ∷
   rw 88 q16 ∷
   rw⁻ 87 q15 ∷
   re 88 3 (CK31 ∷ []) ∷
   rw 88 q17 ∷
   rw 87 q14 ∷
   re 89 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 88 q15 ∷
   rw 89 q18 ∷
   rw 90 q15 ∷
   re 88 3 (CK30 ∷ []) ∷
   rw 89 q19 ∷
   re 88 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 94 q6 ∷
   re 92 3 (CX31 ∷ []) ∷
   rw 91 q20 ∷
   rw 90 q21 ∷
   rw 89 q22 ∷
   re 89 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 88 q1 ∷
   re 89 5 (CK30 ∷ []) ∷
   rw 91 q13 ∷
   rw⁻ 90 q14 ∷
   re 89 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 91 q15 ∷
   rw 90 q16 ∷
   rw⁻ 89 q15 ∷
   re 90 3 (CK31 ∷ []) ∷
   rw 90 q17 ∷
   rw 89 q14 ∷
   re 91 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 90 q15 ∷
   rw 91 q18 ∷
   rw 92 q15 ∷
   re 90 3 (CK30 ∷ []) ∷
   rw 91 q19 ∷
   rw 88 q13 ∷
   rw⁻ 87 q14 ∷
   re 86 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 88 q15 ∷
   rw 87 q23 ∷
   rw⁻ 86 q15 ∷
   re 87 3 (CS13 ∷ []) ∷
   rw 87 q24 ∷
   rw 86 q14 ∷
   re 88 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 87 q15 ∷
   rw 88 q25 ∷
   rw 89 q15 ∷
   re 87 3 (CS03 ∷ []) ∷
   rw 88 q19 ∷
   re 87 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 93 q6 ∷
   re 91 3 (CX31 ∷ []) ∷
   rw 90 q20 ∷
   rw 89 q26 ∷
   rw 88 q22 ∷
   re 88 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 87 q1 ∷
   re 88 5 (CS03 ∷ []) ∷
   rw 90 q13 ∷
   rw⁻ 89 q14 ∷
   re 88 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 90 q15 ∷
   rw 89 q23 ∷
   rw⁻ 88 q15 ∷
   re 89 3 (CS13 ∷ []) ∷
   rw 89 q24 ∷
   rw 88 q14 ∷
   re 90 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 89 q15 ∷
   rw 90 q25 ∷
   rw 91 q15 ∷
   re 89 3 (CS03 ∷ []) ∷
   rw 90 q19 ∷
   rw 87 q13 ∷
   rw⁻ 86 q14 ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 87 q15 ∷
   rw 86 q23 ∷
   rw⁻ 85 q15 ∷
   re 86 3 (CS13 ∷ []) ∷
   rw 86 q24 ∷
   rw 85 q14 ∷
   re 87 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 86 q15 ∷
   rw 87 q25 ∷
   rw 88 q15 ∷
   re 86 3 (CS03 ∷ []) ∷
   rw 87 q19 ∷ []) Eq.refl

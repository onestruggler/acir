{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D110 (W : Ws) where

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
  q1 = wE 660 W
  q2 : Eqn
  q2 = eqn (CS01 ∷ X2 ∷ []) (X2 ∷ CS01 ∷ []) (low-comm (CS) (X))
  q3 : Eqn
  q3 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q4 : Eqn
  q4 = eqn (CK10 ∷ X2 ∷ []) (X2 ∷ CK10 ∷ []) (low-comm (CK₁₀) (X))
  q5 : Eqn
  q5 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q6 : Eqn
  q6 = wE 612 W
  q7 : Eqn
  q7 = eqn (S1 ∷ X2 ∷ []) (X2 ∷ S1 ∷ []) (low-comm ((S ↑)) (X))
  q8 : Eqn
  q8 = eqn (S1 ∷ CX23 ∷ []) (CX23 ∷ S1 ∷ []) (low-comm ((S ↑)) (CX₀₁))
  q9 : Eqn
  q9 = wE 5 W
  q10 : Eqn
  q10 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q12 : Eqn
  q12 = wE 7 W
  q13 : Eqn
  q13 = wE 140 W
  q14 : Eqn
  q14 = wE 661 W
  q15 : Eqn
  q15 = wE 27 W
  q16 : Eqn
  q16 = wE 142 W
  q17 : Eqn
  q17 = wE 31 W
  q18 : Eqn
  q18 = wE 1 W
  q19 : Eqn
  q19 = wE 464 W
  q20 : Eqn
  q20 = wE 3 W
  q21 : Eqn
  q21 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q22 : Eqn
  q22 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q23 : Eqn
  q23 = wE 662 W
  q24 : Eqn
  q24 = wE 151 W
  q25 : Eqn
  q25 = wE 13 W
  q26 : Eqn
  q26 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q27 : Eqn
  q27 = wE 78 W
  q28 : Eqn
  q28 = eqn (CX21 ∷ S3 ∷ []) (S3 ∷ CX21 ∷ []) (low₃-comm ((CX₁₀ ↑)) (S))
  q29 : Eqn
  q29 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))

-- Bar(SSSKSS;2,1->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,3->0) part0: 500 steps
lem-Bar⟨SSSKSS21-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~23-⟶0⟩-part0 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ X2 ∷ CX23 ∷ X2 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX23 ∷ X2 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS21-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~23-⟶0⟩-part0 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ X2 ∷ CX23 ∷ X2 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX23 ∷ X2 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ [])
  (rw 0 q1 ∷
   rw 47 q2 ∷
   rw 48 q3 ∷
   rw 49 q2 ∷
   rw 46 q2 ∷
   rw 47 q3 ∷
   rw 48 q2 ∷
   rw 45 q4 ∷
   rw 46 q5 ∷
   rw 47 q4 ∷
   rw 44 q2 ∷
   rw 45 q3 ∷
   rw 46 q2 ∷
   rw 43 q2 ∷
   rw 44 q3 ∷
   rw 45 q2 ∷
   rw 42 q2 ∷
   rw 43 q3 ∷
   rw 44 q2 ∷
   rw 41 q6 ∷
   rw 40 q2 ∷
   rw 41 q3 ∷
   rw 42 q2 ∷
   rw 39 q2 ∷
   rw 40 q3 ∷
   rw 41 q2 ∷
   rw 38 q2 ∷
   rw 39 q3 ∷
   rw 40 q2 ∷
   rw 37 q2 ∷
   rw 38 q3 ∷
   rw 39 q2 ∷
   rw 36 q2 ∷
   rw 37 q3 ∷
   rw 38 q2 ∷
   rw 35 q2 ∷
   rw 36 q3 ∷
   rw 37 q2 ∷
   rw 34 q2 ∷
   rw 35 q3 ∷
   rw 36 q2 ∷
   rw 33 q2 ∷
   rw 34 q3 ∷
   rw 35 q2 ∷
   rw 32 q2 ∷
   rw 33 q3 ∷
   rw 34 q2 ∷
   rw 31 q7 ∷
   rw 32 q8 ∷
   rw 33 q7 ∷
   rw 30 q4 ∷
   rw 31 q5 ∷
   rw 32 q4 ∷
   rw 29 q2 ∷
   rw 30 q3 ∷
   rw 31 q2 ∷
   rw 28 q2 ∷
   rw 29 q3 ∷
   rw 30 q2 ∷
   rw 27 q2 ∷
   rw 28 q3 ∷
   rw 29 q2 ∷
   rw 26 q2 ∷
   rw 27 q3 ∷
   rw 28 q2 ∷
   rw 25 q2 ∷
   rw 26 q3 ∷
   rw 27 q2 ∷
   rw 24 q2 ∷
   rw 25 q3 ∷
   rw 26 q2 ∷
   rw 23 q6 ∷
   rw 26 q9 ∷
   rw⁻ 25 q10 ∷
   rw⁻ 24 q11 ∷
   rw⁻ 23 q10 ∷
   rw 22 q12 ∷
   rw 21 q12 ∷
   rw 20 q13 ∷
   rw 19 q12 ∷
   rw 18 q12 ∷
   rw 17 q12 ∷
   rw 18 q14 ∷
   rw 17 q10 ∷
   rw 18 q11 ∷
   rw 19 q10 ∷
   rw 20 q15 ∷
   rw 21 q15 ∷
   rw 22 q15 ∷
   rw 23 q16 ∷
   rw 24 q15 ∷
   rw 25 q15 ∷
   rw 26 q17 ∷
   rw 93 q18 ∷
   rw 92 q19 ∷
   re 91 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 93 q20 ∷
   rw 90 q19 ∷
   rw 89 q19 ∷
   rw 88 q19 ∷
   rw 87 q19 ∷
   re 86 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 88 q20 ∷
   rw 85 q19 ∷
   rw 84 q19 ∷
   rw 83 q19 ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 84 q20 ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 83 q20 ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 82 q20 ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 81 q20 ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 80 q20 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q20 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q20 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q20 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q20 ∷
   rw 73 q19 ∷
   re 72 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 74 q20 ∷
   rw 71 q19 ∷
   rw 70 q19 ∷
   rw 69 q19 ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 70 q20 ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 69 q20 ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 68 q20 ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q20 ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 66 q20 ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 65 q20 ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 64 q20 ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 63 q20 ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 62 q20 ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 61 q20 ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q20 ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q20 ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 58 q20 ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q20 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q20 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 55 q20 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 54 q20 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q20 ∷
   rw 50 q21 ∷
   rw 49 q21 ∷
   rw 48 q22 ∷
   rw 47 q21 ∷
   rw 46 q21 ∷
   rw 45 q21 ∷
   rw 46 q23 ∷
   rw 47 q18 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 48 q18 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 49 q18 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 50 q18 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 51 q18 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 52 q18 ∷
   re 50 3 (CS03 ∷ []) ∷
   rw 53 q18 ∷
   re 51 3 (CS03 ∷ []) ∷
   rw 54 q18 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw 55 q18 ∷
   re 53 3 (CS03 ∷ []) ∷
   rw 56 q18 ∷
   re 54 3 (CS03 ∷ []) ∷
   rw 57 q18 ∷
   re 55 3 (CS03 ∷ []) ∷
   rw 58 q18 ∷
   re 56 3 (CS03 ∷ []) ∷
   rw 59 q18 ∷
   re 57 3 (CS03 ∷ []) ∷
   rw 60 q18 ∷
   re 58 3 (CS03 ∷ []) ∷
   rw 61 q18 ∷
   re 59 3 (CS03 ∷ []) ∷
   rw 62 q18 ∷
   re 60 3 (CS03 ∷ []) ∷
   rw 63 q18 ∷
   re 61 3 (CS03 ∷ []) ∷
   rw 64 q18 ∷
   re 62 3 (CS03 ∷ []) ∷
   rw 63 q24 ∷
   rw 64 q24 ∷
   rw 65 q24 ∷
   rw 68 q18 ∷
   re 66 3 (CK30 ∷ []) ∷
   rw 67 q24 ∷
   rw 70 q18 ∷
   re 68 3 (CS03 ∷ []) ∷
   rw 71 q18 ∷
   re 69 3 (CS03 ∷ []) ∷
   rw 72 q18 ∷
   re 70 3 (CS03 ∷ []) ∷
   rw 73 q18 ∷
   re 71 3 (CS03 ∷ []) ∷
   rw 74 q18 ∷
   re 72 3 (CS03 ∷ []) ∷
   rw 75 q18 ∷
   re 73 3 (CS03 ∷ []) ∷
   rw 76 q18 ∷
   re 74 3 (CS03 ∷ []) ∷
   rw 77 q18 ∷
   re 75 3 (CS03 ∷ []) ∷
   rw 78 q18 ∷
   re 76 3 (CS03 ∷ []) ∷
   rw 77 q24 ∷
   rw 78 q24 ∷
   rw 79 q24 ∷
   rw 82 q18 ∷
   re 80 3 (CK30 ∷ []) ∷
   rw 81 q24 ∷
   rw 82 q24 ∷
   rw 83 q24 ∷
   rw 84 q24 ∷
   rw 87 q18 ∷
   re 85 3 (CK30 ∷ []) ∷
   rw 86 q24 ∷
   rw⁻ 87 q21 ∷
   rw⁻ 88 q21 ∷
   rw⁻ 89 q21 ∷
   rw⁻ 90 q22 ∷
   rw⁻ 91 q21 ∷
   rw⁻ 92 q21 ∷
   rw 93 q20 ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q18 ∷
   re 45 3 (CX31 ∷ []) ∷
   rw 45 q25 ∷
   rw⁻ 46 q26 ∷
   rw 47 q27 ∷
   re 48 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 50 q20 ∷
   re 44 5 (CS03 ∷ []) ∷
   re 46 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q18 ∷
   re 46 3 (CX31 ∷ []) ∷
   rw 46 q25 ∷
   rw⁻ 47 q26 ∷
   rw 48 q27 ∷
   re 49 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 51 q20 ∷
   re 45 5 (CS03 ∷ []) ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q18 ∷
   re 47 3 (CX31 ∷ []) ∷
   rw 47 q25 ∷
   rw⁻ 48 q26 ∷
   rw 49 q27 ∷
   re 50 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 52 q20 ∷
   re 46 5 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q18 ∷
   re 48 3 (CX31 ∷ []) ∷
   rw 48 q25 ∷
   rw⁻ 49 q26 ∷
   rw 50 q27 ∷
   re 51 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 53 q20 ∷
   re 47 5 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q18 ∷
   re 49 3 (CX31 ∷ []) ∷
   rw 49 q25 ∷
   rw⁻ 50 q26 ∷
   rw 51 q27 ∷
   re 52 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 54 q20 ∷
   re 48 5 (CS03 ∷ []) ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q18 ∷
   re 50 3 (CX31 ∷ []) ∷
   rw 50 q25 ∷
   rw⁻ 51 q26 ∷
   rw 52 q27 ∷
   re 53 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 55 q20 ∷
   re 49 5 (CS03 ∷ []) ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q18 ∷
   re 51 3 (CX31 ∷ []) ∷
   rw 51 q25 ∷
   rw⁻ 52 q26 ∷
   rw 53 q27 ∷
   re 54 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 56 q20 ∷
   re 50 5 (CS03 ∷ []) ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q18 ∷
   re 52 3 (CX31 ∷ []) ∷
   rw 52 q25 ∷
   rw⁻ 53 q26 ∷
   rw 54 q27 ∷
   re 55 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 57 q20 ∷
   re 51 5 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q18 ∷
   re 53 3 (CX31 ∷ []) ∷
   rw 53 q25 ∷
   rw⁻ 54 q26 ∷
   rw 55 q27 ∷
   re 56 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 58 q20 ∷
   re 52 5 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q18 ∷
   re 54 3 (CX31 ∷ []) ∷
   rw 54 q25 ∷
   rw⁻ 55 q26 ∷
   rw 56 q27 ∷
   re 57 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 59 q20 ∷
   re 53 5 (CS03 ∷ []) ∷
   re 55 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q18 ∷
   re 55 3 (CX31 ∷ []) ∷
   rw 55 q25 ∷
   rw⁻ 56 q26 ∷
   rw 57 q27 ∷
   re 58 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 60 q20 ∷
   re 54 5 (CS03 ∷ []) ∷
   re 56 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q18 ∷
   re 56 3 (CX31 ∷ []) ∷
   rw 56 q25 ∷
   rw⁻ 57 q26 ∷
   rw 58 q27 ∷
   re 59 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 61 q20 ∷
   re 55 5 (CS03 ∷ []) ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q18 ∷
   re 57 3 (CX31 ∷ []) ∷
   rw 57 q25 ∷
   rw⁻ 58 q26 ∷
   rw 59 q27 ∷
   re 60 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 62 q20 ∷
   re 56 5 (CS03 ∷ []) ∷
   re 58 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 57 q18 ∷
   re 58 3 (CX31 ∷ []) ∷
   rw 58 q25 ∷
   rw⁻ 59 q26 ∷
   rw 60 q27 ∷
   re 61 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 63 q20 ∷
   re 57 5 (CS03 ∷ []) ∷
   re 59 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q18 ∷
   re 59 3 (CX31 ∷ []) ∷
   rw 59 q25 ∷
   rw⁻ 60 q26 ∷
   rw 61 q27 ∷
   re 62 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 64 q20 ∷
   re 58 5 (CS03 ∷ []) ∷
   re 60 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q18 ∷
   re 60 3 (CX31 ∷ []) ∷
   rw 60 q25 ∷
   rw⁻ 61 q26 ∷
   rw 62 q27 ∷
   re 63 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 65 q20 ∷
   re 59 5 (CS03 ∷ []) ∷
   re 61 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 60 q18 ∷
   re 61 3 (CX31 ∷ []) ∷
   rw 61 q25 ∷
   rw⁻ 62 q26 ∷
   rw 63 q27 ∷
   re 64 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 66 q20 ∷
   re 60 5 (CS03 ∷ []) ∷
   re 62 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 61 q18 ∷
   re 62 3 (CX31 ∷ []) ∷
   rw 62 q25 ∷
   rw⁻ 63 q26 ∷
   rw 64 q27 ∷
   re 65 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 67 q20 ∷
   re 61 5 (CS03 ∷ []) ∷
   rw 62 q28 ∷
   rw 63 q28 ∷
   rw 64 q28 ∷
   re 66 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 65 q18 ∷
   re 66 3 (CX31 ∷ []) ∷
   rw 66 q25 ∷
   rw⁻ 67 q29 ∷
   rw 68 q27 ∷
   re 69 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 71 q20 ∷
   re 65 5 (CK30 ∷ []) ∷
   rw 66 q28 ∷
   re 68 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 67 q18 ∷
   re 68 3 (CX31 ∷ []) ∷
   rw 68 q25 ∷
   rw⁻ 69 q26 ∷
   rw 70 q27 ∷
   re 71 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 73 q20 ∷
   re 67 5 (CS03 ∷ []) ∷
   re 69 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 68 q18 ∷
   re 69 3 (CX31 ∷ []) ∷
   rw 69 q25 ∷
   rw⁻ 70 q26 ∷
   rw 71 q27 ∷
   re 72 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 74 q20 ∷
   re 68 5 (CS03 ∷ []) ∷
   re 70 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 69 q18 ∷
   re 70 3 (CX31 ∷ []) ∷
   rw 70 q25 ∷
   rw⁻ 71 q26 ∷
   rw 72 q27 ∷
   re 73 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 75 q20 ∷
   re 69 5 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 70 q18 ∷
   re 71 3 (CX31 ∷ []) ∷
   rw 71 q25 ∷
   rw⁻ 72 q26 ∷
   rw 73 q27 ∷
   re 74 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 76 q20 ∷
   re 70 5 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q18 ∷
   re 72 3 (CX31 ∷ []) ∷
   rw 72 q25 ∷
   rw⁻ 73 q26 ∷
   rw 74 q27 ∷
   re 75 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 77 q20 ∷
   re 71 5 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 72 q18 ∷
   re 73 3 (CX31 ∷ []) ∷
   rw 73 q25 ∷
   rw⁻ 74 q26 ∷
   rw 75 q27 ∷
   re 76 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 78 q20 ∷
   re 72 5 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q18 ∷
   re 74 3 (CX31 ∷ []) ∷
   rw 74 q25 ∷
   rw⁻ 75 q26 ∷
   rw 76 q27 ∷
   re 77 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 79 q20 ∷
   re 73 5 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 74 q18 ∷
   re 75 3 (CX31 ∷ []) ∷
   rw 75 q25 ∷
   rw⁻ 76 q26 ∷
   rw 77 q27 ∷
   re 78 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 80 q20 ∷
   re 74 5 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷ []) Eq.refl

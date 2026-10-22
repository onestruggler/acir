{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D282 (W : Ws) where

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
  q2 = wE 173 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 464 W
  q5 : Eqn
  q5 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q6 : Eqn
  q6 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q7 : Eqn
  q7 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q8 : Eqn
  q8 = wE 660 W
  q9 : Eqn
  q9 = wE 175 W
  q10 : Eqn
  q10 = wE 151 W
  q11 : Eqn
  q11 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q12 : Eqn
  q12 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q13 : Eqn
  q13 = eqn (CK10 ∷ X3 ∷ []) (X3 ∷ CK10 ∷ []) (low-comm (CK₁₀) ((X ↑)))
  q14 : Eqn
  q14 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q15 : Eqn
  q15 = wE 537 W
  q16 : Eqn
  q16 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q17 : Eqn
  q17 = eqn (S1 ∷ CX32 ∷ []) (CX32 ∷ S1 ∷ []) (low-comm ((S ↑)) (CX₁₀))
  q18 : Eqn
  q18 = wE 5 W
  q19 : Eqn
  q19 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q20 : Eqn
  q20 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q21 : Eqn
  q21 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q22 : Eqn
  q22 = wE 7 W
  q23 : Eqn
  q23 = wE 140 W
  q24 : Eqn
  q24 = wE 796 W
  q25 : Eqn
  q25 = wE 27 W
  q26 : Eqn
  q26 = wE 142 W
  q27 : Eqn
  q27 = wE 31 W
  q28 : Eqn
  q28 = wE 662 W
  q29 : Eqn
  q29 = wE 13 W
  q30 : Eqn
  q30 = wE 78 W
  q31 : Eqn
  q31 = wE 762 W
  q32 : Eqn
  q32 = wE 663 W

-- Bar(SSSKSS;3,1->0) passes groups of WBar(KiKiSSSKiSSSSSS;~3,2->0) part0: 500 steps
lem-Bar⟨SSSKSS31-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~32-⟶0⟩-part0 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ X3 ∷ CX32 ∷ X3 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw12 ∷ CX32 ∷ CS01 ∷ Sw12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CX32 ∷ X3 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS31-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~32-⟶0⟩-part0 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ X3 ∷ CX32 ∷ X3 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (X3 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw12 ∷ CX32 ∷ CS01 ∷ Sw12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CX32 ∷ X3 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ [])
  (rw 48 q1 ∷
   rw 47 q2 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q3 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q3 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q3 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q3 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q3 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q3 ∷
   rw 40 q4 ∷
   re 39 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 41 q3 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q3 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q3 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q3 ∷
   rw 35 q4 ∷
   re 34 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 36 q3 ∷
   rw 33 q4 ∷
   re 32 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 34 q3 ∷
   rw 31 q2 ∷
   rw 30 q5 ∷
   rw 29 q5 ∷
   rw 28 q6 ∷
   rw 27 q5 ∷
   rw 26 q5 ∷
   rw 25 q5 ∷
   re 24 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 26 q3 ∷
   rw 23 q5 ∷
   rw 22 q5 ∷
   rw 21 q5 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   rw 16 q5 ∷
   rw 15 q5 ∷
   rw 14 q7 ∷
   rw 13 q6 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q5 ∷
   rw 9 q5 ∷
   rw 8 q5 ∷
   rw 7 q5 ∷
   re 6 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   re 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q3 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q3 ∷
   rw 1 q8 ∷
   rw 0 q9 ∷
   rw 3 q1 ∷
   re 1 3 (CK30 ∷ []) ∷
   rw 2 q10 ∷
   rw 5 q1 ∷
   re 3 3 (CK30 ∷ []) ∷
   rw 4 q10 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 10 q1 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q10 ∷
   rw 12 q1 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 14 q1 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 15 q1 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 16 q1 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 17 q1 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 16 q9 ∷
   rw 19 q1 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 20 q1 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 21 q1 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 22 q1 ∷
   re 20 3 (CK30 ∷ []) ∷
   rw 23 q1 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 24 q1 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 25 q1 ∷
   re 23 3 (CX31 ∷ []) ∷
   rw⁻ 24 q5 ∷
   rw⁻ 25 q5 ∷
   rw⁻ 26 q5 ∷
   rw⁻ 27 q5 ∷
   rw⁻ 28 q5 ∷
   rw⁻ 29 q5 ∷
   rw⁻ 30 q6 ∷
   rw⁻ 31 q7 ∷
   rw⁻ 32 q5 ∷
   rw⁻ 33 q5 ∷
   rw⁻ 34 q5 ∷
   rw⁻ 35 q5 ∷
   rw⁻ 36 q5 ∷
   rw⁻ 37 q5 ∷
   rw⁻ 38 q5 ∷
   rw⁻ 39 q5 ∷
   rw⁻ 40 q5 ∷
   rw 43 q1 ∷
   re 41 3 (CX31 ∷ []) ∷
   rw⁻ 42 q5 ∷
   rw⁻ 43 q5 ∷
   rw⁻ 44 q5 ∷
   rw⁻ 45 q6 ∷
   rw⁻ 46 q5 ∷
   rw⁻ 47 q5 ∷
   rw 48 q3 ∷
   rw 47 q11 ∷
   rw 48 q12 ∷
   rw 49 q11 ∷
   rw 46 q11 ∷
   rw 47 q12 ∷
   rw 48 q11 ∷
   rw 45 q13 ∷
   rw 46 q14 ∷
   rw 47 q13 ∷
   rw 44 q11 ∷
   rw 45 q12 ∷
   rw 46 q11 ∷
   rw 43 q11 ∷
   rw 44 q12 ∷
   rw 45 q11 ∷
   rw 42 q11 ∷
   rw 43 q12 ∷
   rw 44 q11 ∷
   rw 41 q15 ∷
   rw 40 q11 ∷
   rw 41 q12 ∷
   rw 42 q11 ∷
   rw 39 q11 ∷
   rw 40 q12 ∷
   rw 41 q11 ∷
   rw 38 q11 ∷
   rw 39 q12 ∷
   rw 40 q11 ∷
   rw 37 q11 ∷
   rw 38 q12 ∷
   rw 39 q11 ∷
   rw 36 q11 ∷
   rw 37 q12 ∷
   rw 38 q11 ∷
   rw 35 q11 ∷
   rw 36 q12 ∷
   rw 37 q11 ∷
   rw 34 q11 ∷
   rw 35 q12 ∷
   rw 36 q11 ∷
   rw 33 q11 ∷
   rw 34 q12 ∷
   rw 35 q11 ∷
   rw 32 q11 ∷
   rw 33 q12 ∷
   rw 34 q11 ∷
   rw 31 q16 ∷
   rw 32 q17 ∷
   rw 33 q16 ∷
   rw 30 q13 ∷
   rw 31 q14 ∷
   rw 32 q13 ∷
   rw 29 q11 ∷
   rw 30 q12 ∷
   rw 31 q11 ∷
   rw 28 q11 ∷
   rw 29 q12 ∷
   rw 30 q11 ∷
   rw 27 q11 ∷
   rw 28 q12 ∷
   rw 29 q11 ∷
   rw 26 q11 ∷
   rw 27 q12 ∷
   rw 28 q11 ∷
   rw 25 q11 ∷
   rw 26 q12 ∷
   rw 27 q11 ∷
   rw 24 q11 ∷
   rw 25 q12 ∷
   rw 26 q11 ∷
   rw 23 q15 ∷
   rw 26 q18 ∷
   rw⁻ 25 q19 ∷
   rw⁻ 24 q20 ∷
   rw⁻ 23 q19 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q21 ∷
   rw 23 q22 ∷
   rw⁻ 22 q21 ∷
   re 23 3 (CS13 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q21 ∷
   rw 22 q22 ∷
   rw⁻ 21 q21 ∷
   re 22 3 (CS13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q21 ∷
   rw 21 q23 ∷
   rw⁻ 20 q21 ∷
   re 21 3 (CK31 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q21 ∷
   rw 20 q22 ∷
   rw⁻ 19 q21 ∷
   re 20 3 (CS13 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q21 ∷
   rw 19 q22 ∷
   rw⁻ 18 q21 ∷
   re 19 3 (CS13 ∷ []) ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q21 ∷
   rw 18 q22 ∷
   rw⁻ 17 q21 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 18 q24 ∷
   rw 17 q19 ∷
   rw 18 q20 ∷
   rw 19 q19 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q21 ∷
   rw 21 q25 ∷
   rw 22 q21 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q21 ∷
   rw 22 q25 ∷
   rw 23 q21 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q21 ∷
   rw 23 q25 ∷
   rw 24 q21 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 23 q21 ∷
   rw 24 q26 ∷
   rw 25 q21 ∷
   re 23 3 (CK30 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q21 ∷
   rw 25 q25 ∷
   rw 26 q21 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q21 ∷
   rw 26 q25 ∷
   rw 27 q21 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 26 q27 ∷
   rw 45 q28 ∷
   re 45 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 44 q29 ∷
   rw⁻ 45 q12 ∷
   rw 46 q30 ∷
   re 44 3 (CS02 ∷ []) ∷
   re 46 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 45 q29 ∷
   rw⁻ 46 q12 ∷
   rw 47 q30 ∷
   re 45 3 (CS02 ∷ []) ∷
   re 47 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 46 q29 ∷
   rw⁻ 47 q12 ∷
   rw 48 q30 ∷
   re 46 3 (CS02 ∷ []) ∷
   re 48 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 47 q29 ∷
   rw⁻ 48 q12 ∷
   rw 49 q30 ∷
   re 47 3 (CS02 ∷ []) ∷
   re 49 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 48 q29 ∷
   rw⁻ 49 q12 ∷
   rw 50 q30 ∷
   re 48 3 (CS02 ∷ []) ∷
   re 50 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 49 q29 ∷
   rw⁻ 50 q12 ∷
   rw 51 q30 ∷
   re 49 3 (CS02 ∷ []) ∷
   re 51 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 50 q29 ∷
   rw⁻ 51 q12 ∷
   rw 52 q30 ∷
   re 50 3 (CS02 ∷ []) ∷
   re 52 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 51 q29 ∷
   rw⁻ 52 q12 ∷
   rw 53 q30 ∷
   re 51 3 (CS02 ∷ []) ∷
   re 53 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 52 q29 ∷
   rw⁻ 53 q12 ∷
   rw 54 q30 ∷
   re 52 3 (CS02 ∷ []) ∷
   re 54 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 53 q29 ∷
   rw⁻ 54 q12 ∷
   rw 55 q30 ∷
   re 53 3 (CS02 ∷ []) ∷
   re 55 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 54 q29 ∷
   rw⁻ 55 q12 ∷
   rw 56 q30 ∷
   re 54 3 (CS02 ∷ []) ∷
   re 56 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 55 q29 ∷
   rw⁻ 56 q12 ∷
   rw 57 q30 ∷
   re 55 3 (CS02 ∷ []) ∷
   re 57 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 56 q29 ∷
   rw⁻ 57 q12 ∷
   rw 58 q30 ∷
   re 56 3 (CS02 ∷ []) ∷
   re 58 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 57 q29 ∷
   rw⁻ 58 q12 ∷
   rw 59 q30 ∷
   re 57 3 (CS02 ∷ []) ∷
   re 59 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 58 q29 ∷
   rw⁻ 59 q12 ∷
   rw 60 q30 ∷
   re 58 3 (CS02 ∷ []) ∷
   re 60 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 59 q29 ∷
   rw⁻ 60 q12 ∷
   rw 61 q30 ∷
   re 59 3 (CS02 ∷ []) ∷
   re 61 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 60 q29 ∷
   rw⁻ 61 q12 ∷
   rw 62 q30 ∷
   re 60 3 (CS02 ∷ []) ∷
   re 62 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 61 q29 ∷
   rw⁻ 62 q12 ∷
   rw 63 q30 ∷
   re 61 3 (CS02 ∷ []) ∷
   rw 62 q31 ∷
   rw 63 q31 ∷
   rw 64 q31 ∷
   re 66 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 65 q29 ∷
   rw⁻ 66 q14 ∷
   rw 67 q30 ∷
   re 65 3 (CK20 ∷ []) ∷
   rw 66 q31 ∷
   re 68 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 67 q29 ∷
   rw⁻ 68 q12 ∷
   rw 69 q30 ∷
   re 67 3 (CS02 ∷ []) ∷
   re 69 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 68 q29 ∷
   rw⁻ 69 q12 ∷
   rw 70 q30 ∷
   re 68 3 (CS02 ∷ []) ∷
   re 70 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 69 q29 ∷
   rw⁻ 70 q12 ∷
   rw 71 q30 ∷
   re 69 3 (CS02 ∷ []) ∷
   re 71 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 70 q29 ∷
   rw⁻ 71 q12 ∷
   rw 72 q30 ∷
   re 70 3 (CS02 ∷ []) ∷
   re 72 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 71 q29 ∷
   rw⁻ 72 q12 ∷
   rw 73 q30 ∷
   re 71 3 (CS02 ∷ []) ∷
   re 73 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 72 q29 ∷
   rw⁻ 73 q12 ∷
   rw 74 q30 ∷
   re 72 3 (CS02 ∷ []) ∷
   re 74 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 73 q29 ∷
   rw⁻ 74 q12 ∷
   rw 75 q30 ∷
   re 73 3 (CS02 ∷ []) ∷
   re 75 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 74 q29 ∷
   rw⁻ 75 q12 ∷
   rw 76 q30 ∷
   re 74 3 (CS02 ∷ []) ∷
   re 76 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 75 q29 ∷
   rw⁻ 76 q12 ∷
   rw 77 q30 ∷
   re 75 3 (CS02 ∷ []) ∷
   rw 76 q31 ∷
   rw 77 q31 ∷
   rw 78 q31 ∷
   re 80 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 79 q29 ∷
   rw⁻ 80 q14 ∷
   rw 81 q30 ∷
   re 79 3 (CK20 ∷ []) ∷
   rw 80 q31 ∷
   rw 81 q31 ∷
   rw 82 q31 ∷
   rw 83 q31 ∷
   re 85 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 84 q29 ∷
   rw⁻ 85 q14 ∷
   rw 86 q30 ∷
   re 84 3 (CK20 ∷ []) ∷
   rw 85 q31 ∷
   rw 27 q32 ∷
   re 27 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 26 q29 ∷
   rw⁻ 27 q12 ∷
   rw 28 q30 ∷
   re 26 3 (CS02 ∷ []) ∷
   re 28 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 27 q29 ∷
   rw⁻ 28 q12 ∷
   rw 29 q30 ∷
   re 27 3 (CS02 ∷ []) ∷
   re 29 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 28 q29 ∷
   rw⁻ 29 q12 ∷
   rw 30 q30 ∷
   re 28 3 (CS02 ∷ []) ∷
   re 30 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 29 q29 ∷
   rw⁻ 30 q12 ∷
   rw 31 q30 ∷
   re 29 3 (CS02 ∷ []) ∷
   re 31 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 30 q29 ∷
   rw⁻ 31 q12 ∷
   rw 32 q30 ∷
   re 30 3 (CS02 ∷ []) ∷
   re 32 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 31 q29 ∷
   rw⁻ 32 q12 ∷
   rw 33 q30 ∷
   re 31 3 (CS02 ∷ []) ∷
   re 33 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 32 q29 ∷
   rw⁻ 33 q12 ∷
   rw 34 q30 ∷
   re 32 3 (CS02 ∷ []) ∷
   re 34 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 33 q29 ∷
   rw⁻ 34 q12 ∷
   rw 35 q30 ∷
   re 33 3 (CS02 ∷ []) ∷
   re 35 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 34 q29 ∷
   rw⁻ 35 q12 ∷
   rw 36 q30 ∷
   re 34 3 (CS02 ∷ []) ∷
   re 36 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 35 q29 ∷
   rw⁻ 36 q12 ∷
   rw 37 q30 ∷
   re 35 3 (CS02 ∷ []) ∷
   re 37 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 36 q29 ∷
   rw⁻ 37 q12 ∷
   rw 38 q30 ∷
   re 36 3 (CS02 ∷ []) ∷
   re 38 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 37 q29 ∷ []) Eq.refl

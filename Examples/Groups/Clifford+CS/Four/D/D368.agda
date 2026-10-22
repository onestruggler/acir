{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D368 (W : Ws) where

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
  q2 = wE 151 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q5 : Eqn
  q5 = eqn (S1 ∷ CX23 ∷ []) (CX23 ∷ S1 ∷ []) (low-comm ((S ↑)) (CX₀₁))
  q6 : Eqn
  q6 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q7 : Eqn
  q7 = wE 566 W

-- Bar(SSSKSS;2,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,1->0) part5: 39 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part5 : ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part5 = derive (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (re 92 3 (CS03 ∷ []) ∷
   rw 95 q1 ∷
   re 93 3 (CK30 ∷ []) ∷
   rw 94 q2 ∷
   rw 97 q1 ∷
   re 95 3 (CS03 ∷ []) ∷
   rw 98 q1 ∷
   re 96 3 (CS03 ∷ []) ∷
   rw 99 q1 ∷
   re 97 3 (CS03 ∷ []) ∷
   rw 100 q1 ∷
   re 98 3 (CS03 ∷ []) ∷
   rw 101 q1 ∷
   re 99 3 (CS03 ∷ []) ∷
   rw 102 q1 ∷
   re 100 3 (CS03 ∷ []) ∷
   rw 103 q1 ∷
   re 101 3 (CS03 ∷ []) ∷
   rw 104 q1 ∷
   re 102 3 (CS03 ∷ []) ∷
   rw 105 q1 ∷
   re 103 3 (CS03 ∷ []) ∷
   rw 104 q3 ∷
   rw⁻ 71 q4 ∷
   rw⁻ 72 q5 ∷
   rw⁻ 73 q4 ∷
   rw⁻ 74 q5 ∷
   rw⁻ 75 q6 ∷
   rw⁻ 76 q6 ∷
   rw⁻ 77 q6 ∷
   rw⁻ 78 q4 ∷
   rw⁻ 79 q5 ∷
   rw⁻ 80 q6 ∷
   rw⁻ 81 q6 ∷
   rw⁻ 82 q6 ∷
   rw⁻ 83 q6 ∷
   rw⁻ 84 q6 ∷
   rw⁻ 85 q6 ∷
   rw 65 q7 ∷ []) Eq.refl

private
  q8 : Eqn
  q8 = wE 5 W
  q9 : Eqn
  q9 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q11 : Eqn
  q11 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q12 : Eqn
  q12 = wE 7 W
  q13 : Eqn
  q13 = wE 140 W
  q14 : Eqn
  q14 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q15 : Eqn
  q15 = wE 988 W
  q16 : Eqn
  q16 = wE 27 W
  q17 : Eqn
  q17 = wE 142 W
  q18 : Eqn
  q18 = wE 31 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X2 CX23 X2]: 247 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CX23-X2 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX23 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CX23-X2 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX23 ∷ X2 ∷ []) (X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw 34 q8 ∷
   rw⁻ 33 q9 ∷
   rw⁻ 32 q10 ∷
   rw⁻ 31 q9 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q11 ∷
   rw 31 q12 ∷
   rw⁻ 30 q11 ∷
   re 31 3 (CS13 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q11 ∷
   rw 30 q12 ∷
   rw⁻ 29 q11 ∷
   re 30 3 (CS13 ∷ []) ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q11 ∷
   rw 29 q13 ∷
   rw⁻ 28 q11 ∷
   re 29 3 (CK31 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q11 ∷
   rw 28 q12 ∷
   rw⁻ 27 q11 ∷
   re 28 3 (CS13 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q11 ∷
   rw 27 q12 ∷
   rw⁻ 26 q11 ∷
   re 27 3 (CS13 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q11 ∷
   rw 26 q12 ∷
   rw⁻ 25 q11 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw⁻ 24 q10 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q11 ∷
   rw 24 q12 ∷
   rw⁻ 23 q11 ∷
   re 24 3 (CS13 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q11 ∷
   rw 23 q12 ∷
   rw⁻ 22 q11 ∷
   re 23 3 (CS13 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q11 ∷
   rw 22 q12 ∷
   rw⁻ 21 q11 ∷
   re 22 3 (CS13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q11 ∷
   rw 21 q12 ∷
   rw⁻ 20 q11 ∷
   re 21 3 (CS13 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q11 ∷
   rw 20 q12 ∷
   rw⁻ 19 q11 ∷
   re 20 3 (CS13 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q11 ∷
   rw 19 q12 ∷
   rw⁻ 18 q11 ∷
   re 19 3 (CS13 ∷ []) ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q11 ∷
   rw 18 q12 ∷
   rw⁻ 17 q11 ∷
   re 18 3 (CS13 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q11 ∷
   rw 17 q12 ∷
   rw⁻ 16 q11 ∷
   re 17 3 (CS13 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q11 ∷
   rw 16 q12 ∷
   rw⁻ 15 q11 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw⁻ 14 q14 ∷
   re 13 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q11 ∷
   rw 14 q13 ∷
   rw⁻ 13 q11 ∷
   re 14 3 (CK31 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q11 ∷
   rw 13 q12 ∷
   rw⁻ 12 q11 ∷
   re 13 3 (CS13 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q11 ∷
   rw 12 q12 ∷
   rw⁻ 11 q11 ∷
   re 12 3 (CS13 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q11 ∷
   rw 11 q12 ∷
   rw⁻ 10 q11 ∷
   re 11 3 (CS13 ∷ []) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q11 ∷
   rw 10 q12 ∷
   rw⁻ 9 q11 ∷
   re 10 3 (CS13 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q11 ∷
   rw 9 q12 ∷
   rw⁻ 8 q11 ∷
   re 9 3 (CS13 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q11 ∷
   rw 8 q12 ∷
   rw⁻ 7 q11 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 6 q10 ∷
   rw 5 q12 ∷
   rw 4 q12 ∷
   rw 3 q13 ∷
   rw 2 q12 ∷
   rw 1 q12 ∷
   rw 0 q12 ∷
   rw 1 q15 ∷
   rw 0 q9 ∷
   rw 1 q10 ∷
   rw 2 q9 ∷
   rw 3 q16 ∷
   rw 4 q16 ∷
   rw 5 q16 ∷
   rw 6 q17 ∷
   rw 7 q16 ∷
   rw 8 q16 ∷
   rw 9 q10 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q11 ∷
   rw 11 q16 ∷
   rw 12 q11 ∷
   re 10 3 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q11 ∷
   rw 12 q16 ∷
   rw 13 q11 ∷
   re 11 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q11 ∷
   rw 13 q16 ∷
   rw 14 q11 ∷
   re 12 3 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q11 ∷
   rw 14 q16 ∷
   rw 15 q11 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q11 ∷
   rw 15 q16 ∷
   rw 16 q11 ∷
   re 14 3 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q11 ∷
   rw 16 q16 ∷
   rw 17 q11 ∷
   re 15 3 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 16 q11 ∷
   rw 17 q17 ∷
   rw 18 q11 ∷
   re 16 3 (CK30 ∷ []) ∷
   rw 17 q14 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q11 ∷
   rw 19 q16 ∷
   rw 20 q11 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q11 ∷
   rw 20 q16 ∷
   rw 21 q11 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q11 ∷
   rw 21 q16 ∷
   rw 22 q11 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q11 ∷
   rw 22 q16 ∷
   rw 23 q11 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q11 ∷
   rw 23 q16 ∷
   rw 24 q11 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q11 ∷
   rw 24 q16 ∷
   rw 25 q11 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q11 ∷
   rw 25 q16 ∷
   rw 26 q11 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q11 ∷
   rw 26 q16 ∷
   rw 27 q11 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q11 ∷
   rw 27 q16 ∷
   rw 28 q11 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 27 q10 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q11 ∷
   rw 29 q16 ∷
   rw 30 q11 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q11 ∷
   rw 30 q16 ∷
   rw 31 q11 ∷
   re 29 3 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q11 ∷
   rw 31 q16 ∷
   rw 32 q11 ∷
   re 30 3 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 31 q11 ∷
   rw 32 q17 ∷
   rw 33 q11 ∷
   re 31 3 (CK30 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q11 ∷
   rw 33 q16 ∷
   rw 34 q11 ∷
   re 32 3 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q11 ∷
   rw 34 q16 ∷
   rw 35 q11 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 34 q18 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = wE 989 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X2 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX20 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S0 S0 S0 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S0 S0 S0 CK01 S0 S0 S0 S0 CK01 S0 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 X2]: 1 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX20-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-S0-S0-S0-CK01-S0-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-X2 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX20-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-S0-S0-S0-CK01-S0-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-X2 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ []) (X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 0 q19 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = eqn (CK10 ∷ X2 ∷ []) (X2 ∷ CK10 ∷ []) (low-comm (CK₁₀) (X))
  q21 : Eqn
  q21 = eqn (CS01 ∷ X2 ∷ []) (X2 ∷ CS01 ∷ []) (low-comm (CS) (X))
  q22 : Eqn
  q22 = wE 612 W
  q23 : Eqn
  q23 = eqn (S1 ∷ X2 ∷ []) (X2 ∷ S1 ∷ []) (low-comm ((S ↑)) (X))
  q24 : Eqn
  q24 = wE 990 W
  q25 : Eqn
  q25 = wE 991 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X2 CX23 X2]: 131 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CX23-X2 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CX23 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CX23-X2 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CX23 ∷ X2 ∷ []) (X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 28 q20 ∷
   rw 29 q4 ∷
   rw 30 q20 ∷
   rw 27 q20 ∷
   rw 28 q4 ∷
   rw 29 q20 ∷
   rw 26 q21 ∷
   rw 27 q6 ∷
   rw 28 q21 ∷
   rw 25 q20 ∷
   rw 26 q4 ∷
   rw 27 q20 ∷
   rw 24 q21 ∷
   rw 25 q6 ∷
   rw 26 q21 ∷
   rw 23 q21 ∷
   rw 24 q6 ∷
   rw 25 q21 ∷
   rw 22 q22 ∷
   rw 21 q21 ∷
   rw 22 q6 ∷
   rw 23 q21 ∷
   rw 20 q21 ∷
   rw 21 q6 ∷
   rw 22 q21 ∷
   rw 19 q21 ∷
   rw 20 q6 ∷
   rw 21 q21 ∷
   rw 18 q21 ∷
   rw 19 q6 ∷
   rw 20 q21 ∷
   rw 17 q21 ∷
   rw 18 q6 ∷
   rw 19 q21 ∷
   rw 16 q21 ∷
   rw 17 q6 ∷
   rw 18 q21 ∷
   rw 15 q23 ∷
   rw 16 q5 ∷
   rw 17 q23 ∷
   rw 14 q20 ∷
   rw 15 q4 ∷
   rw 16 q20 ∷
   rw 13 q21 ∷
   rw 14 q6 ∷
   rw 15 q21 ∷
   rw 12 q21 ∷
   rw 13 q6 ∷
   rw 14 q21 ∷
   rw 11 q21 ∷
   rw 12 q6 ∷
   rw 13 q21 ∷
   rw 10 q23 ∷
   rw 11 q5 ∷
   rw 12 q23 ∷
   rw 9 q20 ∷
   rw 10 q4 ∷
   rw 11 q20 ∷
   rw 8 q23 ∷
   rw 9 q5 ∷
   rw 10 q23 ∷
   rw 7 q20 ∷
   rw 8 q4 ∷
   rw 9 q20 ∷
   rw 6 q22 ∷
   rw 9 q8 ∷
   rw⁻ 8 q9 ∷
   rw⁻ 7 q10 ∷
   rw⁻ 6 q9 ∷
   rw 5 q13 ∷
   rw 6 q24 ∷
   rw 5 q9 ∷
   rw 6 q10 ∷
   rw 7 q9 ∷
   rw 8 q17 ∷
   rw 9 q18 ∷
   rw 8 q8 ∷
   rw⁻ 7 q9 ∷
   rw⁻ 6 q10 ∷
   rw⁻ 5 q9 ∷
   rw 4 q13 ∷
   rw 5 q24 ∷
   rw 4 q9 ∷
   rw 5 q10 ∷
   rw 6 q9 ∷
   rw 7 q17 ∷
   rw 8 q18 ∷
   rw 7 q8 ∷
   rw⁻ 6 q9 ∷
   rw⁻ 5 q10 ∷
   rw⁻ 4 q9 ∷
   rw 3 q12 ∷
   rw 4 q25 ∷
   rw 3 q9 ∷
   rw 4 q10 ∷
   rw 5 q9 ∷
   rw 6 q16 ∷
   rw 7 q18 ∷
   rw 6 q8 ∷
   rw⁻ 5 q9 ∷
   rw⁻ 4 q10 ∷
   rw⁻ 3 q9 ∷
   rw 2 q13 ∷
   rw 3 q24 ∷
   rw 2 q9 ∷
   rw 3 q10 ∷
   rw 4 q9 ∷
   rw 5 q17 ∷
   rw 6 q18 ∷
   rw 5 q8 ∷
   rw⁻ 4 q9 ∷
   rw⁻ 3 q10 ∷
   rw⁻ 2 q9 ∷
   rw 1 q12 ∷
   rw 2 q25 ∷
   rw 1 q9 ∷
   rw 2 q10 ∷
   rw 3 q9 ∷
   rw 4 q16 ∷
   rw 5 q18 ∷
   rw 4 q8 ∷
   rw⁻ 3 q9 ∷
   rw⁻ 2 q10 ∷
   rw⁻ 1 q9 ∷
   rw 0 q12 ∷
   rw 1 q25 ∷
   rw 0 q9 ∷
   rw 1 q10 ∷
   rw 2 q9 ∷
   rw 3 q16 ∷
   rw 4 q18 ∷ []) Eq.refl

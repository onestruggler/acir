{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D265 (W : Ws) where

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
  q1 = wE 13 W
  q2 : Eqn
  q2 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q3 : Eqn
  q3 = wE 78 W
  q4 : Eqn
  q4 = wE 5 W
  q5 : Eqn
  q5 = wE 7 W
  q6 : Eqn
  q6 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q7 : Eqn
  q7 = wE 140 W
  q8 : Eqn
  q8 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q9 : Eqn
  q9 = wE 763 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = wE 27 W
  q12 : Eqn
  q12 = wE 31 W

-- Bar(SSKSKK;3,1->0) passes groups of WBar(KiKiSSSKiSSSSSS;~3,2->0) part2: 97 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~32-⟶0⟩-part2 : ⟪ (X3 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX31 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ X3 ∷ CX32 ∷ X3 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~32-⟶0⟩-part2 = derive (X3 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX31 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (X3 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ X3 ∷ CX32 ∷ X3 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 85 q1 ∷
   rw⁻ 86 q2 ∷
   rw 87 q3 ∷
   re 85 3 (CS02 ∷ []) ∷
   rw 86 q4 ∷
   rw 85 q5 ∷
   rw 84 q5 ∷
   rw 83 q5 ∷
   rw 82 q5 ∷
   rw 81 q5 ∷
   rw 80 q5 ∷
   rw⁻ 79 q6 ∷
   rw 78 q7 ∷
   rw 77 q5 ∷
   rw 76 q5 ∷
   rw 75 q5 ∷
   rw⁻ 74 q6 ∷
   rw 73 q7 ∷
   rw⁻ 72 q6 ∷
   rw 71 q7 ∷
   re 70 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 72 q8 ∷
   rw 71 q7 ∷
   rw⁻ 70 q8 ∷
   re 71 3 (CK31 ∷ []) ∷
   re 69 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 71 q8 ∷
   rw 70 q7 ∷
   rw⁻ 69 q8 ∷
   re 70 3 (CK31 ∷ []) ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 70 q8 ∷
   rw 69 q5 ∷
   rw⁻ 68 q8 ∷
   re 69 3 (CS13 ∷ []) ∷
   re 67 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 69 q8 ∷
   rw 68 q7 ∷
   rw⁻ 67 q8 ∷
   re 68 3 (CK31 ∷ []) ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 68 q8 ∷
   rw 67 q5 ∷
   rw⁻ 66 q8 ∷
   re 67 3 (CS13 ∷ []) ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 67 q8 ∷
   rw 66 q5 ∷
   rw⁻ 65 q8 ∷
   re 66 3 (CS13 ∷ []) ∷
   rw 66 q9 ∷
   rw 65 q10 ∷
   rw 66 q6 ∷
   rw 67 q10 ∷
   rw 68 q6 ∷
   rw 69 q11 ∷
   rw 70 q11 ∷
   rw 71 q11 ∷
   rw 72 q10 ∷
   rw 73 q6 ∷
   rw 74 q11 ∷
   rw 75 q11 ∷
   rw 76 q11 ∷
   rw 77 q11 ∷
   rw 78 q11 ∷
   rw 79 q11 ∷
   re 81 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 80 q8 ∷
   rw 81 q11 ∷
   rw 82 q8 ∷
   re 80 3 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 81 q8 ∷
   rw 82 q11 ∷
   rw 83 q8 ∷
   re 81 3 (CS03 ∷ []) ∷
   re 83 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 82 q8 ∷
   rw 83 q10 ∷
   rw 84 q8 ∷
   re 82 3 (CK30 ∷ []) ∷
   re 84 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 83 q8 ∷
   rw 84 q11 ∷
   rw 85 q8 ∷
   re 83 3 (CS03 ∷ []) ∷
   re 85 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 84 q8 ∷
   rw 85 q10 ∷
   rw 86 q8 ∷
   re 84 3 (CK30 ∷ []) ∷
   re 86 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 85 q8 ∷
   rw 86 q10 ∷
   rw 87 q8 ∷
   re 85 3 (CK30 ∷ []) ∷
   rw 86 q12 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = wE 1 W
  q14 : Eqn
  q14 = wE 173 W
  q15 : Eqn
  q15 = wE 3 W
  q16 : Eqn
  q16 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q17 : Eqn
  q17 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q18 : Eqn
  q18 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q19 : Eqn
  q19 = wE 620 W
  q20 : Eqn
  q20 = wE 175 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CX31 X3]: 85 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CX31-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CX31 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CX31 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CX31-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CX31 ∷ X3 ∷ []) (X3 ∷ CX31 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 32 q13 ∷
   rw 31 q14 ∷
   re 30 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 32 q15 ∷
   rw 29 q14 ∷
   rw 28 q16 ∷
   rw 27 q16 ∷
   rw 26 q17 ∷
   rw 25 q16 ∷
   rw 24 q17 ∷
   rw 23 q17 ∷
   re 22 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 24 q15 ∷
   rw 21 q17 ∷
   rw 20 q17 ∷
   rw 19 q17 ∷
   rw 18 q17 ∷
   rw 17 q17 ∷
   rw 16 q17 ∷
   rw 15 q18 ∷
   rw 14 q16 ∷
   rw 13 q17 ∷
   rw 12 q17 ∷
   rw 11 q17 ∷
   rw 10 q18 ∷
   rw 9 q16 ∷
   rw 8 q18 ∷
   rw 7 q16 ∷
   re 6 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q15 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 7 q15 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 6 q15 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q15 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 4 q15 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q15 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q15 ∷
   rw 1 q19 ∷
   rw 0 q20 ∷
   rw 3 q13 ∷
   re 1 3 (CX31 ∷ []) ∷
   rw 2 q20 ∷
   rw 5 q13 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 6 q13 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 7 q13 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 8 q13 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 9 q13 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 10 q13 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 11 q13 ∷
   re 9 3 (CX31 ∷ []) ∷
   rw⁻ 10 q16 ∷
   rw⁻ 11 q18 ∷
   rw⁻ 12 q16 ∷
   rw⁻ 13 q18 ∷
   rw⁻ 14 q17 ∷
   rw⁻ 15 q17 ∷
   rw⁻ 16 q17 ∷
   rw⁻ 17 q16 ∷
   rw⁻ 18 q18 ∷
   rw⁻ 19 q17 ∷
   rw⁻ 20 q17 ∷
   rw⁻ 21 q17 ∷
   rw⁻ 22 q17 ∷
   rw⁻ 23 q17 ∷
   rw⁻ 24 q17 ∷
   rw 27 q13 ∷
   re 25 3 (CX31 ∷ []) ∷
   rw⁻ 26 q17 ∷
   rw⁻ 27 q17 ∷
   rw⁻ 28 q16 ∷
   rw⁻ 29 q17 ∷
   rw⁻ 30 q16 ∷
   rw⁻ 31 q16 ∷
   rw 32 q15 ∷ []) Eq.refl

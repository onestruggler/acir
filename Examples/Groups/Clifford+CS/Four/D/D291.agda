{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D291 (W : Ws) where

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
  q1 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q2 : Eqn
  q2 = wE 7 W
  q3 : Eqn
  q3 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q4 : Eqn
  q4 = wE 140 W
  q5 : Eqn
  q5 = wE 884 W
  q6 : Eqn
  q6 = wE 27 W
  q7 : Eqn
  q7 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q8 : Eqn
  q8 = wE 142 W
  q9 : Eqn
  q9 = wE 31 W
  q10 : Eqn
  q10 = wE 36 W
  q11 : Eqn
  q11 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q12 : Eqn
  q12 = wE 37 W
  q13 : Eqn
  q13 = wE 883 W
  q14 : Eqn
  q14 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q15 : Eqn
  q15 = wE 614 W
  q16 : Eqn
  q16 = wE 1 W
  q17 : Eqn
  q17 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q18 : Eqn
  q18 = wE 3 W
  q19 : Eqn
  q19 = wE 879 W
  q20 : Eqn
  q20 = wE 157 W
  q21 : Eqn
  q21 = wE 158 W
  q22 : Eqn
  q22 = wE 880 W
  q23 : Eqn
  q23 = wE 881 W

-- Bar(SSKSKK;1,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~1,2->0) part2: 500 steps
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part2 : ⟪ (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ Sw01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X1 ∷ CX12 ∷ CS03 ∷ X1 ∷ Sw23 ∷ Sw23 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part2 = derive (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ Sw01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X1 ∷ CX12 ∷ CS03 ∷ X1 ∷ Sw23 ∷ Sw23 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ [])
  (re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q1 ∷
   rw 39 q2 ∷
   rw⁻ 38 q1 ∷
   re 39 3 (CS13 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q1 ∷
   rw 38 q2 ∷
   rw⁻ 37 q1 ∷
   re 38 3 (CS13 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q1 ∷
   rw 37 q2 ∷
   rw⁻ 36 q1 ∷
   re 37 3 (CS13 ∷ []) ∷
   rw⁻ 35 q3 ∷
   re 34 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q1 ∷
   rw 35 q4 ∷
   rw⁻ 34 q1 ∷
   re 35 3 (CK31 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q1 ∷
   rw 34 q2 ∷
   rw⁻ 33 q1 ∷
   re 34 3 (CS13 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q1 ∷
   rw 33 q2 ∷
   rw⁻ 32 q1 ∷
   re 33 3 (CS13 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q1 ∷
   rw 32 q2 ∷
   rw⁻ 31 q1 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw⁻ 30 q3 ∷
   re 29 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q1 ∷
   rw 30 q4 ∷
   rw⁻ 29 q1 ∷
   re 30 3 (CK31 ∷ []) ∷
   rw⁻ 28 q3 ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q1 ∷
   rw 28 q4 ∷
   rw⁻ 27 q1 ∷
   re 28 3 (CK31 ∷ []) ∷
   rw 28 q5 ∷
   rw 27 q6 ∷
   rw 28 q6 ∷
   rw 29 q6 ∷
   rw 30 q6 ∷
   rw 31 q6 ∷
   rw 32 q6 ∷
   rw 33 q6 ∷
   rw 34 q6 ∷
   rw 35 q6 ∷
   rw 36 q6 ∷
   rw 37 q6 ∷
   rw 38 q6 ∷
   rw 39 q6 ∷
   rw 40 q6 ∷
   rw 41 q6 ∷
   rw 42 q6 ∷
   rw 43 q6 ∷
   rw 44 q6 ∷
   rw 45 q7 ∷
   rw 46 q7 ∷
   rw 47 q7 ∷
   rw 48 q8 ∷
   rw 49 q7 ∷
   rw 50 q6 ∷
   rw 51 q6 ∷
   rw 52 q6 ∷
   rw 53 q6 ∷
   rw 54 q6 ∷
   rw 55 q6 ∷
   rw 56 q6 ∷
   rw 57 q6 ∷
   rw 58 q6 ∷
   rw 59 q7 ∷
   rw 60 q7 ∷
   rw 61 q7 ∷
   rw 62 q8 ∷
   rw 63 q7 ∷
   rw 64 q7 ∷
   rw 65 q7 ∷
   rw 66 q7 ∷
   rw 67 q8 ∷
   rw 68 q7 ∷
   re 70 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 69 q1 ∷
   rw 70 q8 ∷
   rw 71 q1 ∷
   re 69 3 (CK30 ∷ []) ∷
   rw 70 q3 ∷
   re 72 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 71 q1 ∷
   rw 72 q8 ∷
   rw 73 q1 ∷
   re 71 3 (CK30 ∷ []) ∷
   rw 72 q3 ∷
   re 74 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 73 q1 ∷
   rw 74 q6 ∷
   rw 75 q1 ∷
   re 73 3 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 74 q1 ∷
   rw 75 q6 ∷
   rw 76 q1 ∷
   re 74 3 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 75 q1 ∷
   rw 76 q6 ∷
   rw 77 q1 ∷
   re 75 3 (CS03 ∷ []) ∷
   re 77 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 76 q1 ∷
   rw 77 q8 ∷
   rw 78 q1 ∷
   re 76 3 (CK30 ∷ []) ∷
   rw 77 q3 ∷
   re 79 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 78 q1 ∷
   rw 79 q6 ∷
   rw 80 q1 ∷
   re 78 3 (CS03 ∷ []) ∷
   re 80 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 79 q1 ∷
   rw 80 q6 ∷
   rw 81 q1 ∷
   re 79 3 (CS03 ∷ []) ∷
   re 81 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 80 q1 ∷
   rw 81 q6 ∷
   rw 82 q1 ∷
   re 80 3 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 81 q1 ∷
   rw 82 q6 ∷
   rw 83 q1 ∷
   re 81 3 (CS03 ∷ []) ∷
   re 83 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 82 q1 ∷
   rw 83 q6 ∷
   rw 84 q1 ∷
   re 82 3 (CS03 ∷ []) ∷
   re 84 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 83 q1 ∷
   rw 84 q6 ∷
   rw 85 q1 ∷
   re 83 3 (CS03 ∷ []) ∷
   rw 84 q9 ∷
   re 27 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 26 q10 ∷
   rw⁻ 27 q11 ∷
   rw 28 q12 ∷
   re 26 3 (CS02 ∷ []) ∷
   re 28 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 27 q10 ∷
   rw⁻ 28 q11 ∷
   rw 29 q12 ∷
   re 27 3 (CS02 ∷ []) ∷
   re 29 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 28 q10 ∷
   rw⁻ 29 q11 ∷
   rw 30 q12 ∷
   re 28 3 (CS02 ∷ []) ∷
   re 30 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 29 q10 ∷
   rw⁻ 30 q11 ∷
   rw 31 q12 ∷
   re 29 3 (CS02 ∷ []) ∷
   re 31 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 30 q10 ∷
   rw⁻ 31 q11 ∷
   rw 32 q12 ∷
   re 30 3 (CS02 ∷ []) ∷
   re 32 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 31 q10 ∷
   rw⁻ 32 q11 ∷
   rw 33 q12 ∷
   re 31 3 (CS02 ∷ []) ∷
   re 33 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 32 q10 ∷
   rw⁻ 33 q11 ∷
   rw 34 q12 ∷
   re 32 3 (CS02 ∷ []) ∷
   re 34 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 33 q10 ∷
   rw⁻ 34 q11 ∷
   rw 35 q12 ∷
   re 33 3 (CS02 ∷ []) ∷
   re 35 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 34 q10 ∷
   rw⁻ 35 q11 ∷
   rw 36 q12 ∷
   re 34 3 (CS02 ∷ []) ∷
   re 36 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 35 q10 ∷
   rw⁻ 36 q11 ∷
   rw 37 q12 ∷
   re 35 3 (CS02 ∷ []) ∷
   re 37 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 36 q10 ∷
   rw⁻ 37 q11 ∷
   rw 38 q12 ∷
   re 36 3 (CS02 ∷ []) ∷
   re 38 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 37 q10 ∷
   rw⁻ 38 q11 ∷
   rw 39 q12 ∷
   re 37 3 (CS02 ∷ []) ∷
   re 39 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 38 q10 ∷
   rw⁻ 39 q11 ∷
   rw 40 q12 ∷
   re 38 3 (CS02 ∷ []) ∷
   re 40 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 39 q10 ∷
   rw⁻ 40 q11 ∷
   rw 41 q12 ∷
   re 39 3 (CS02 ∷ []) ∷
   re 41 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 40 q10 ∷
   rw⁻ 41 q11 ∷
   rw 42 q12 ∷
   re 40 3 (CS02 ∷ []) ∷
   re 42 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 41 q10 ∷
   rw⁻ 42 q11 ∷
   rw 43 q12 ∷
   re 41 3 (CS02 ∷ []) ∷
   re 43 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 42 q10 ∷
   rw⁻ 43 q11 ∷
   rw 44 q12 ∷
   re 42 3 (CS02 ∷ []) ∷
   re 44 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 43 q10 ∷
   rw⁻ 44 q11 ∷
   rw 45 q12 ∷
   re 43 3 (CS02 ∷ []) ∷
   rw 44 q13 ∷
   rw 45 q13 ∷
   rw 46 q13 ∷
   re 48 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 47 q10 ∷
   rw⁻ 48 q14 ∷
   rw 49 q12 ∷
   re 47 3 (CK20 ∷ []) ∷
   rw 48 q13 ∷
   re 50 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 49 q10 ∷
   rw⁻ 50 q11 ∷
   rw 51 q12 ∷
   re 49 3 (CS02 ∷ []) ∷
   re 51 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 50 q10 ∷
   rw⁻ 51 q11 ∷
   rw 52 q12 ∷
   re 50 3 (CS02 ∷ []) ∷
   re 52 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 51 q10 ∷
   rw⁻ 52 q11 ∷
   rw 53 q12 ∷
   re 51 3 (CS02 ∷ []) ∷
   re 53 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 52 q10 ∷
   rw⁻ 53 q11 ∷
   rw 54 q12 ∷
   re 52 3 (CS02 ∷ []) ∷
   re 54 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 53 q10 ∷
   rw⁻ 54 q11 ∷
   rw 55 q12 ∷
   re 53 3 (CS02 ∷ []) ∷
   re 55 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 54 q10 ∷
   rw⁻ 55 q11 ∷
   rw 56 q12 ∷
   re 54 3 (CS02 ∷ []) ∷
   re 56 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 55 q10 ∷
   rw⁻ 56 q11 ∷
   rw 57 q12 ∷
   re 55 3 (CS02 ∷ []) ∷
   re 57 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 56 q10 ∷
   rw⁻ 57 q11 ∷
   rw 58 q12 ∷
   re 56 3 (CS02 ∷ []) ∷
   re 58 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 57 q10 ∷
   rw⁻ 58 q11 ∷
   rw 59 q12 ∷
   re 57 3 (CS02 ∷ []) ∷
   rw 58 q13 ∷
   rw 59 q13 ∷
   rw 60 q13 ∷
   re 62 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 61 q10 ∷
   rw⁻ 62 q14 ∷
   rw 63 q12 ∷
   re 61 3 (CK20 ∷ []) ∷
   rw 62 q13 ∷
   rw 63 q13 ∷
   rw 64 q13 ∷
   rw 65 q13 ∷
   re 67 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 66 q10 ∷
   rw⁻ 67 q14 ∷
   rw 68 q12 ∷
   re 66 3 (CK20 ∷ []) ∷
   rw 67 q13 ∷
   rw 20 q15 ∷
   rw 92 q16 ∷
   rw 91 q17 ∷
   re 90 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 92 q18 ∷
   rw 91 q19 ∷
   rw⁻ 90 q17 ∷
   rw 93 q16 ∷
   re 91 3 (CK30 ∷ []) ∷
   rw 92 q18 ∷
   re 91 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 97 q16 ∷
   re 95 3 (CX13 ∷ []) ∷
   rw 94 q20 ∷
   rw 93 q14 ∷
   rw 92 q21 ∷
   re 92 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 91 q18 ∷
   re 92 5 (CK30 ∷ []) ∷
   rw 94 q16 ∷
   rw 93 q17 ∷
   re 92 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 94 q18 ∷
   rw 93 q19 ∷
   rw⁻ 92 q17 ∷
   rw 95 q16 ∷
   re 93 3 (CK30 ∷ []) ∷
   rw 94 q18 ∷
   rw 91 q16 ∷
   rw 90 q17 ∷
   re 89 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 91 q18 ∷
   rw 90 q19 ∷
   rw⁻ 89 q17 ∷
   rw 92 q16 ∷
   re 90 3 (CK30 ∷ []) ∷
   rw 91 q18 ∷
   re 90 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 96 q16 ∷
   re 94 3 (CX13 ∷ []) ∷
   rw 93 q20 ∷
   rw 92 q14 ∷
   rw 91 q21 ∷
   re 91 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 90 q18 ∷
   re 91 5 (CK30 ∷ []) ∷
   rw 93 q16 ∷
   rw 92 q17 ∷
   re 91 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 93 q18 ∷
   rw 92 q19 ∷
   rw⁻ 91 q17 ∷
   rw 94 q16 ∷
   re 92 3 (CK30 ∷ []) ∷
   rw 93 q18 ∷
   rw 90 q16 ∷
   rw 89 q17 ∷
   re 88 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 90 q18 ∷
   rw 89 q22 ∷
   rw⁻ 88 q17 ∷
   rw 91 q16 ∷
   re 89 3 (CS03 ∷ []) ∷
   rw 90 q18 ∷
   re 89 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 95 q16 ∷
   re 93 3 (CX13 ∷ []) ∷
   rw 92 q20 ∷
   rw 91 q11 ∷
   rw 90 q21 ∷
   re 90 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 89 q18 ∷
   re 90 5 (CS03 ∷ []) ∷
   rw 92 q16 ∷
   rw 91 q17 ∷
   re 90 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 92 q18 ∷
   rw 91 q22 ∷
   rw⁻ 90 q17 ∷
   rw 93 q16 ∷
   re 91 3 (CS03 ∷ []) ∷
   rw 92 q18 ∷
   rw 89 q16 ∷
   rw 88 q17 ∷
   re 87 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 89 q18 ∷
   rw 88 q19 ∷
   rw⁻ 87 q17 ∷
   rw 90 q16 ∷
   re 88 3 (CK30 ∷ []) ∷
   rw 89 q18 ∷
   re 88 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 94 q16 ∷
   re 92 3 (CX13 ∷ []) ∷
   rw 91 q20 ∷
   rw 90 q14 ∷
   rw 89 q21 ∷
   re 89 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 88 q18 ∷
   re 89 5 (CK30 ∷ []) ∷
   rw 91 q16 ∷
   rw 90 q17 ∷
   re 89 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 91 q18 ∷
   rw 90 q19 ∷
   rw⁻ 89 q17 ∷
   rw 92 q16 ∷
   re 90 3 (CK30 ∷ []) ∷
   rw 91 q18 ∷
   rw 88 q16 ∷
   rw 87 q17 ∷
   re 86 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 88 q18 ∷
   rw 87 q22 ∷
   rw⁻ 86 q17 ∷
   rw 89 q16 ∷
   re 87 3 (CS03 ∷ []) ∷
   rw 88 q18 ∷
   re 87 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 93 q16 ∷
   re 91 3 (CX13 ∷ []) ∷
   rw 90 q20 ∷
   rw 89 q11 ∷
   rw 88 q21 ∷
   re 88 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 87 q18 ∷
   re 88 5 (CS03 ∷ []) ∷
   rw 90 q16 ∷
   rw 89 q17 ∷
   re 88 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 90 q18 ∷
   rw 89 q22 ∷
   rw⁻ 88 q17 ∷
   rw 91 q16 ∷
   re 89 3 (CS03 ∷ []) ∷
   rw 90 q18 ∷
   rw 87 q16 ∷
   rw 86 q17 ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 87 q18 ∷
   rw 86 q22 ∷
   rw⁻ 85 q17 ∷
   rw 88 q16 ∷
   re 86 3 (CS03 ∷ []) ∷
   rw 87 q18 ∷
   re 86 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 92 q16 ∷
   re 90 3 (CX13 ∷ []) ∷
   rw 89 q20 ∷
   rw 88 q11 ∷
   rw 87 q21 ∷
   re 87 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 86 q18 ∷
   re 87 5 (CS03 ∷ []) ∷
   rw 89 q16 ∷
   rw 88 q17 ∷
   re 87 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 89 q18 ∷
   rw 88 q22 ∷
   rw⁻ 87 q17 ∷
   rw 90 q16 ∷
   re 88 3 (CS03 ∷ []) ∷
   rw 89 q18 ∷
   rw 84 q23 ∷
   rw 85 q16 ∷
   rw 84 q17 ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 85 q18 ∷
   rw 84 q22 ∷
   rw⁻ 83 q17 ∷
   rw 86 q16 ∷
   re 84 3 (CS03 ∷ []) ∷
   rw 85 q18 ∷
   re 84 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 90 q16 ∷
   re 88 3 (CX13 ∷ []) ∷
   rw 87 q20 ∷
   rw 86 q11 ∷
   rw 85 q21 ∷
   re 85 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 84 q18 ∷
   re 85 5 (CS03 ∷ []) ∷
   rw 87 q16 ∷ []) Eq.refl

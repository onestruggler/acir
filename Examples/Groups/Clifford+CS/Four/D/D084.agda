{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D084 (W : Ws) where

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
  q1 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q2 : Eqn
  q2 = eqn (CX21 ∷ S3 ∷ []) (S3 ∷ CX21 ∷ []) (low₃-comm ((CX₁₀ ↑)) (S))
  q3 : Eqn
  q3 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q4 : Eqn
  q4 = eqn (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) (wn 13 W)
  q5 : Eqn
  q5 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q6 : Eqn
  q6 = eqn (CX32 ∷ Sw12 ∷ []) (Sw12 ∷ CX31 ∷ []) (wn 78 W)
  q7 : Eqn
  q7 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q8 : Eqn
  q8 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q9 : Eqn
  q9 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q10 : Eqn
  q10 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q11 : Eqn
  q11 = eqn (CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (wn 615 W)
  q12 : Eqn
  q12 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)
  q13 : Eqn
  q13 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q14 : Eqn
  q14 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q16 : Eqn
  q16 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q17 : Eqn
  q17 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)

-- Bar(SSKSKK;2,1->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,3->0) part1: 500 steps
lem-Bar⟨SSKSKK21-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~23-⟶0⟩-part1 : ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw23 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CX23 ∷ X2 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ Sw23 ∷ CK20 ∷ Sw01 ∷ Sw23 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ Sw01 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CX23 ∷ X2 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK21-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~23-⟶0⟩-part1 = derive (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw23 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CX23 ∷ X2 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ Sw23 ∷ CK20 ∷ Sw01 ∷ Sw23 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ Sw01 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CX23 ∷ X2 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ [])
  (rw 79 q1 ∷
   re 73 5 (CS03 ∷ []) ∷
   rw 74 q2 ∷
   rw 75 q2 ∷
   rw 76 q2 ∷
   re 78 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 77 q3 ∷
   re 78 3 (CX31 ∷ []) ∷
   rw 78 q4 ∷
   rw⁻ 79 q5 ∷
   rw 80 q6 ∷
   re 81 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 83 q1 ∷
   re 77 5 (CK30 ∷ []) ∷
   rw 78 q2 ∷
   rw 79 q2 ∷
   rw 80 q2 ∷
   rw 81 q2 ∷
   re 83 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 82 q3 ∷
   re 83 3 (CX31 ∷ []) ∷
   rw 83 q4 ∷
   rw⁻ 84 q5 ∷
   rw 85 q6 ∷
   re 86 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 88 q1 ∷
   re 82 5 (CK30 ∷ []) ∷
   rw 83 q2 ∷
   rw 84 q3 ∷
   rw 83 q7 ∷
   re 82 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 84 q1 ∷
   rw 81 q7 ∷
   rw 80 q7 ∷
   rw 79 q7 ∷
   rw 78 q7 ∷
   re 77 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 79 q1 ∷
   rw 76 q7 ∷
   rw 75 q7 ∷
   rw 74 q7 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q1 ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q1 ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 73 q1 ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 72 q1 ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 71 q1 ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 70 q1 ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 69 q1 ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 68 q1 ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q1 ∷
   rw 64 q7 ∷
   re 63 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 65 q1 ∷
   rw 62 q7 ∷
   rw 61 q7 ∷
   rw 60 q7 ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 61 q1 ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q1 ∷
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
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q1 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q1 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q1 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q1 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   rw 41 q8 ∷
   rw 40 q8 ∷
   rw 39 q8 ∷
   rw 38 q8 ∷
   rw 37 q8 ∷
   rw 36 q8 ∷
   rw 35 q9 ∷
   rw 34 q10 ∷
   rw 33 q8 ∷
   rw 32 q8 ∷
   rw 31 q8 ∷
   rw 30 q9 ∷
   rw 29 q10 ∷
   rw 28 q9 ∷
   rw 27 q10 ∷
   rw 28 q11 ∷
   rw 29 q3 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 30 q3 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 31 q3 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q3 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 33 q3 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 34 q3 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 35 q3 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 36 q3 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 37 q3 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 38 q3 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 39 q3 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 40 q3 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 41 q3 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 42 q3 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 43 q3 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 44 q3 ∷
   re 42 3 (CS03 ∷ []) ∷
   rw 45 q3 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 46 q3 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 45 q12 ∷
   rw 46 q12 ∷
   rw 47 q12 ∷
   rw 50 q3 ∷
   re 48 3 (CK30 ∷ []) ∷
   rw 49 q12 ∷
   rw 52 q3 ∷
   re 50 3 (CS03 ∷ []) ∷
   rw 53 q3 ∷
   re 51 3 (CS03 ∷ []) ∷
   rw 54 q3 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw 55 q3 ∷
   re 53 3 (CS03 ∷ []) ∷
   rw 56 q3 ∷
   re 54 3 (CS03 ∷ []) ∷
   rw 57 q3 ∷
   re 55 3 (CS03 ∷ []) ∷
   rw 58 q3 ∷
   re 56 3 (CS03 ∷ []) ∷
   rw 59 q3 ∷
   re 57 3 (CS03 ∷ []) ∷
   rw 60 q3 ∷
   re 58 3 (CS03 ∷ []) ∷
   rw 59 q12 ∷
   rw 60 q12 ∷
   rw 61 q12 ∷
   rw 64 q3 ∷
   re 62 3 (CK30 ∷ []) ∷
   rw 63 q12 ∷
   rw 64 q12 ∷
   rw 65 q12 ∷
   rw 66 q12 ∷
   rw 69 q3 ∷
   re 67 3 (CK30 ∷ []) ∷
   rw 68 q12 ∷
   rw⁻ 69 q10 ∷
   rw⁻ 70 q9 ∷
   rw⁻ 71 q10 ∷
   rw⁻ 72 q9 ∷
   rw⁻ 73 q8 ∷
   rw⁻ 74 q8 ∷
   rw⁻ 75 q8 ∷
   rw⁻ 76 q10 ∷
   rw⁻ 77 q9 ∷
   rw⁻ 78 q8 ∷
   rw⁻ 79 q8 ∷
   rw⁻ 80 q8 ∷
   rw⁻ 81 q8 ∷
   rw⁻ 82 q8 ∷
   rw⁻ 83 q8 ∷
   rw 84 q1 ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q3 ∷
   re 27 3 (CX31 ∷ []) ∷
   rw 27 q4 ∷
   rw⁻ 28 q13 ∷
   rw 29 q6 ∷
   re 30 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q3 ∷
   re 28 3 (CX31 ∷ []) ∷
   rw 28 q4 ∷
   rw⁻ 29 q13 ∷
   rw 30 q6 ∷
   re 31 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q3 ∷
   re 29 3 (CX31 ∷ []) ∷
   rw 29 q4 ∷
   rw⁻ 30 q13 ∷
   rw 31 q6 ∷
   re 32 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   re 28 5 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q3 ∷
   re 30 3 (CX31 ∷ []) ∷
   rw 30 q4 ∷
   rw⁻ 31 q13 ∷
   rw 32 q6 ∷
   re 33 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q3 ∷
   re 31 3 (CX31 ∷ []) ∷
   rw 31 q4 ∷
   rw⁻ 32 q13 ∷
   rw 33 q6 ∷
   re 34 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
   re 30 5 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q3 ∷
   re 32 3 (CX31 ∷ []) ∷
   rw 32 q4 ∷
   rw⁻ 33 q13 ∷
   rw 34 q6 ∷
   re 35 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 37 q1 ∷
   re 31 5 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q3 ∷
   re 33 3 (CX31 ∷ []) ∷
   rw 33 q4 ∷
   rw⁻ 34 q13 ∷
   rw 35 q6 ∷
   re 36 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 38 q1 ∷
   re 32 5 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q3 ∷
   re 34 3 (CX31 ∷ []) ∷
   rw 34 q4 ∷
   rw⁻ 35 q13 ∷
   rw 36 q6 ∷
   re 37 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 39 q1 ∷
   re 33 5 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q3 ∷
   re 35 3 (CX31 ∷ []) ∷
   rw 35 q4 ∷
   rw⁻ 36 q13 ∷
   rw 37 q6 ∷
   re 38 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   re 34 5 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q3 ∷
   re 36 3 (CX31 ∷ []) ∷
   rw 36 q4 ∷
   rw⁻ 37 q13 ∷
   rw 38 q6 ∷
   re 39 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   re 35 5 (CS03 ∷ []) ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q3 ∷
   re 37 3 (CX31 ∷ []) ∷
   rw 37 q4 ∷
   rw⁻ 38 q13 ∷
   rw 39 q6 ∷
   re 40 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   re 36 5 (CS03 ∷ []) ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q3 ∷
   re 38 3 (CX31 ∷ []) ∷
   rw 38 q4 ∷
   rw⁻ 39 q13 ∷
   rw 40 q6 ∷
   re 41 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   re 37 5 (CS03 ∷ []) ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q3 ∷
   re 39 3 (CX31 ∷ []) ∷
   rw 39 q4 ∷
   rw⁻ 40 q13 ∷
   rw 41 q6 ∷
   re 42 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   re 38 5 (CS03 ∷ []) ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q3 ∷
   re 40 3 (CX31 ∷ []) ∷
   rw 40 q4 ∷
   rw⁻ 41 q13 ∷
   rw 42 q6 ∷
   re 43 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 45 q1 ∷
   re 39 5 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q3 ∷
   re 41 3 (CX31 ∷ []) ∷
   rw 41 q4 ∷
   rw⁻ 42 q13 ∷
   rw 43 q6 ∷
   re 44 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 46 q1 ∷
   re 40 5 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q3 ∷
   re 42 3 (CX31 ∷ []) ∷
   rw 42 q4 ∷
   rw⁻ 43 q13 ∷
   rw 44 q6 ∷
   re 45 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   re 41 5 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q3 ∷
   re 43 3 (CX31 ∷ []) ∷
   rw 43 q4 ∷
   rw⁻ 44 q13 ∷
   rw 45 q6 ∷
   re 46 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 48 q1 ∷
   re 42 5 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q3 ∷
   re 44 3 (CX31 ∷ []) ∷
   rw 44 q4 ∷
   rw⁻ 45 q13 ∷
   rw 46 q6 ∷
   re 47 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   re 43 5 (CS03 ∷ []) ∷
   rw 44 q2 ∷
   rw 45 q2 ∷
   rw 46 q2 ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q3 ∷
   re 48 3 (CX31 ∷ []) ∷
   rw 48 q4 ∷
   rw⁻ 49 q5 ∷
   rw 50 q6 ∷
   re 51 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 53 q1 ∷
   re 47 5 (CK30 ∷ []) ∷
   rw 48 q2 ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q3 ∷
   re 50 3 (CX31 ∷ []) ∷
   rw 50 q4 ∷
   rw⁻ 51 q13 ∷
   rw 52 q6 ∷
   re 53 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 55 q1 ∷
   re 49 5 (CS03 ∷ []) ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q3 ∷
   re 51 3 (CX31 ∷ []) ∷
   rw 51 q4 ∷
   rw⁻ 52 q13 ∷
   rw 53 q6 ∷
   re 54 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 56 q1 ∷
   re 50 5 (CS03 ∷ []) ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q3 ∷
   re 52 3 (CX31 ∷ []) ∷
   rw 52 q4 ∷
   rw⁻ 53 q13 ∷
   rw 54 q6 ∷
   re 55 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 57 q1 ∷
   re 51 5 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q3 ∷
   re 53 3 (CX31 ∷ []) ∷
   rw 53 q4 ∷
   rw⁻ 54 q13 ∷
   rw 55 q6 ∷
   re 56 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 58 q1 ∷
   re 52 5 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q3 ∷
   re 54 3 (CX31 ∷ []) ∷
   rw 54 q4 ∷
   rw⁻ 55 q13 ∷
   rw 56 q6 ∷
   re 57 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 59 q1 ∷
   re 53 5 (CS03 ∷ []) ∷
   re 55 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q3 ∷
   re 55 3 (CX31 ∷ []) ∷
   rw 55 q4 ∷
   rw⁻ 56 q13 ∷
   rw 57 q6 ∷
   re 58 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 60 q1 ∷
   re 54 5 (CS03 ∷ []) ∷
   re 56 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q3 ∷
   re 56 3 (CX31 ∷ []) ∷
   rw 56 q4 ∷
   rw⁻ 57 q13 ∷
   rw 58 q6 ∷
   re 59 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 61 q1 ∷
   re 55 5 (CS03 ∷ []) ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q3 ∷
   re 57 3 (CX31 ∷ []) ∷
   rw 57 q4 ∷
   rw⁻ 58 q13 ∷
   rw 59 q6 ∷
   re 60 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 62 q1 ∷
   re 56 5 (CS03 ∷ []) ∷
   re 58 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 57 q3 ∷
   re 58 3 (CX31 ∷ []) ∷
   rw 58 q4 ∷
   rw⁻ 59 q13 ∷
   rw 60 q6 ∷
   re 61 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 63 q1 ∷
   re 57 5 (CS03 ∷ []) ∷
   rw 58 q2 ∷
   rw 59 q2 ∷
   rw 60 q2 ∷
   re 62 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 61 q3 ∷
   re 62 3 (CX31 ∷ []) ∷
   rw 62 q4 ∷
   rw⁻ 63 q5 ∷
   rw 64 q6 ∷
   re 65 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 67 q1 ∷
   re 61 5 (CK30 ∷ []) ∷
   rw 62 q2 ∷
   rw 63 q2 ∷
   rw 64 q2 ∷
   rw 65 q2 ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 66 q3 ∷
   re 67 3 (CX31 ∷ []) ∷
   rw 67 q4 ∷
   rw⁻ 68 q5 ∷
   rw 69 q6 ∷
   re 70 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 72 q1 ∷
   re 66 5 (CK30 ∷ []) ∷
   rw 67 q2 ∷
   rw 68 q14 ∷
   rw⁻ 67 q15 ∷
   re 66 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 68 q16 ∷
   rw 67 q17 ∷
   rw⁻ 66 q16 ∷
   re 67 3 (CK31 ∷ []) ∷
   rw⁻ 65 q15 ∷
   rw⁻ 64 q15 ∷
   rw⁻ 63 q15 ∷
   rw⁻ 62 q15 ∷
   re 61 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 63 q16 ∷ []) Eq.refl

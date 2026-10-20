{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D111 (W : Ws) where

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
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) (wn 13 W)
  q3 : Eqn
  q3 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q4 : Eqn
  q4 = eqn (CX32 ∷ Sw12 ∷ []) (Sw12 ∷ CX31 ∷ []) (wn 78 W)
  q5 : Eqn
  q5 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q6 : Eqn
  q6 = eqn (CX21 ∷ S3 ∷ []) (S3 ∷ CX21 ∷ []) (low₃-comm ((CX₁₀ ↑)) (S))
  q7 : Eqn
  q7 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q8 : Eqn
  q8 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q9 : Eqn
  q9 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q10 : Eqn
  q10 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q11 : Eqn
  q11 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q12 : Eqn
  q12 = eqn (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (wn 663 W)
  q13 : Eqn
  q13 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)
  q14 : Eqn
  q14 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))

-- Bar(SSSKSS;2,1->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,3->0) part1: 500 steps
lem-Bar⟨SSSKSS21-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~23-⟶0⟩-part1 : ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX23 ∷ X2 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ S3 ∷ Sw01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX23 ∷ X2 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS21-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~23-⟶0⟩-part1 = derive (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX23 ∷ X2 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ S3 ∷ Sw01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX23 ∷ X2 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ [])
  (rw 75 q1 ∷
   re 76 3 (CX31 ∷ []) ∷
   rw 76 q2 ∷
   rw⁻ 77 q3 ∷
   rw 78 q4 ∷
   re 79 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 81 q5 ∷
   re 75 5 (CS03 ∷ []) ∷
   rw 76 q6 ∷
   rw 77 q6 ∷
   rw 78 q6 ∷
   re 80 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 79 q1 ∷
   re 80 3 (CX31 ∷ []) ∷
   rw 80 q2 ∷
   rw⁻ 81 q7 ∷
   rw 82 q4 ∷
   re 83 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 85 q5 ∷
   re 79 5 (CK30 ∷ []) ∷
   rw 80 q6 ∷
   rw 81 q6 ∷
   rw 82 q6 ∷
   rw 83 q6 ∷
   re 85 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 84 q1 ∷
   re 85 3 (CX31 ∷ []) ∷
   rw 85 q2 ∷
   rw⁻ 86 q7 ∷
   rw 87 q4 ∷
   re 88 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 90 q5 ∷
   re 84 5 (CK30 ∷ []) ∷
   rw 85 q6 ∷
   rw 86 q1 ∷
   rw 85 q8 ∷
   re 84 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 86 q5 ∷
   rw 83 q8 ∷
   rw 82 q8 ∷
   rw 81 q8 ∷
   rw 80 q8 ∷
   re 79 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 81 q5 ∷
   rw 78 q8 ∷
   rw 77 q8 ∷
   rw 76 q8 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q5 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q5 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q5 ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q5 ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 73 q5 ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 72 q5 ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 71 q5 ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 70 q5 ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 69 q5 ∷
   rw 66 q8 ∷
   re 65 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 67 q5 ∷
   rw 64 q8 ∷
   rw 63 q8 ∷
   rw 62 q8 ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 63 q5 ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 62 q5 ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 61 q5 ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q5 ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q5 ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 58 q5 ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q5 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q5 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 55 q5 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 54 q5 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q5 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q5 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q5 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q5 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q5 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q5 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q5 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q5 ∷
   rw 43 q9 ∷
   rw 42 q9 ∷
   rw 41 q9 ∷
   rw 40 q9 ∷
   rw 39 q9 ∷
   rw 38 q9 ∷
   rw 37 q9 ∷
   rw 36 q9 ∷
   rw 35 q9 ∷
   rw 34 q10 ∷
   rw 33 q11 ∷
   rw 32 q9 ∷
   rw 31 q9 ∷
   rw 30 q9 ∷
   rw 29 q9 ∷
   rw 28 q9 ∷
   rw 27 q9 ∷
   rw 28 q12 ∷
   rw 29 q1 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 30 q1 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 31 q1 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 34 q1 ∷
   re 32 3 (CS03 ∷ []) ∷
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
   re 39 3 (CS03 ∷ []) ∷
   rw 42 q1 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 43 q1 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 44 q1 ∷
   re 42 3 (CS03 ∷ []) ∷
   rw 45 q1 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 46 q1 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 45 q13 ∷
   rw 46 q13 ∷
   rw 47 q13 ∷
   rw 50 q1 ∷
   re 48 3 (CK30 ∷ []) ∷
   rw 49 q13 ∷
   rw 52 q1 ∷
   re 50 3 (CS03 ∷ []) ∷
   rw 53 q1 ∷
   re 51 3 (CS03 ∷ []) ∷
   rw 54 q1 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw 55 q1 ∷
   re 53 3 (CS03 ∷ []) ∷
   rw 56 q1 ∷
   re 54 3 (CS03 ∷ []) ∷
   rw 57 q1 ∷
   re 55 3 (CS03 ∷ []) ∷
   rw 58 q1 ∷
   re 56 3 (CS03 ∷ []) ∷
   rw 59 q1 ∷
   re 57 3 (CS03 ∷ []) ∷
   rw 60 q1 ∷
   re 58 3 (CS03 ∷ []) ∷
   rw 59 q13 ∷
   rw 60 q13 ∷
   rw 61 q13 ∷
   rw 64 q1 ∷
   re 62 3 (CK30 ∷ []) ∷
   rw 63 q13 ∷
   rw 64 q13 ∷
   rw 65 q13 ∷
   rw 66 q13 ∷
   rw 69 q1 ∷
   re 67 3 (CK30 ∷ []) ∷
   rw 68 q13 ∷
   rw⁻ 69 q9 ∷
   rw⁻ 70 q9 ∷
   rw⁻ 71 q9 ∷
   rw⁻ 72 q9 ∷
   rw⁻ 73 q9 ∷
   rw⁻ 74 q9 ∷
   rw⁻ 75 q11 ∷
   rw⁻ 76 q10 ∷
   rw⁻ 77 q9 ∷
   rw⁻ 78 q9 ∷
   rw⁻ 79 q9 ∷
   rw⁻ 80 q9 ∷
   rw⁻ 81 q9 ∷
   rw⁻ 82 q9 ∷
   rw⁻ 83 q9 ∷
   rw⁻ 84 q9 ∷
   rw⁻ 85 q9 ∷
   rw 86 q5 ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   re 27 3 (CX31 ∷ []) ∷
   rw 27 q2 ∷
   rw⁻ 28 q3 ∷
   rw 29 q4 ∷
   re 30 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 32 q5 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   re 28 3 (CX31 ∷ []) ∷
   rw 28 q2 ∷
   rw⁻ 29 q3 ∷
   rw 30 q4 ∷
   re 31 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 33 q5 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   re 29 3 (CX31 ∷ []) ∷
   rw 29 q2 ∷
   rw⁻ 30 q3 ∷
   rw 31 q4 ∷
   re 32 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 34 q5 ∷
   re 28 5 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   re 30 3 (CX31 ∷ []) ∷
   rw 30 q2 ∷
   rw⁻ 31 q3 ∷
   rw 32 q4 ∷
   re 33 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 35 q5 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   re 31 3 (CX31 ∷ []) ∷
   rw 31 q2 ∷
   rw⁻ 32 q3 ∷
   rw 33 q4 ∷
   re 34 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 36 q5 ∷
   re 30 5 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   re 32 3 (CX31 ∷ []) ∷
   rw 32 q2 ∷
   rw⁻ 33 q3 ∷
   rw 34 q4 ∷
   re 35 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 37 q5 ∷
   re 31 5 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 33 3 (CX31 ∷ []) ∷
   rw 33 q2 ∷
   rw⁻ 34 q3 ∷
   rw 35 q4 ∷
   re 36 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 38 q5 ∷
   re 32 5 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 34 3 (CX31 ∷ []) ∷
   rw 34 q2 ∷
   rw⁻ 35 q3 ∷
   rw 36 q4 ∷
   re 37 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 39 q5 ∷
   re 33 5 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   re 35 3 (CX31 ∷ []) ∷
   rw 35 q2 ∷
   rw⁻ 36 q3 ∷
   rw 37 q4 ∷
   re 38 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 40 q5 ∷
   re 34 5 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   re 36 3 (CX31 ∷ []) ∷
   rw 36 q2 ∷
   rw⁻ 37 q3 ∷
   rw 38 q4 ∷
   re 39 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 41 q5 ∷
   re 35 5 (CS03 ∷ []) ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
   re 37 3 (CX31 ∷ []) ∷
   rw 37 q2 ∷
   rw⁻ 38 q3 ∷
   rw 39 q4 ∷
   re 40 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 42 q5 ∷
   re 36 5 (CS03 ∷ []) ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q1 ∷
   re 38 3 (CX31 ∷ []) ∷
   rw 38 q2 ∷
   rw⁻ 39 q3 ∷
   rw 40 q4 ∷
   re 41 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 43 q5 ∷
   re 37 5 (CS03 ∷ []) ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q1 ∷
   re 39 3 (CX31 ∷ []) ∷
   rw 39 q2 ∷
   rw⁻ 40 q3 ∷
   rw 41 q4 ∷
   re 42 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 44 q5 ∷
   re 38 5 (CS03 ∷ []) ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q1 ∷
   re 40 3 (CX31 ∷ []) ∷
   rw 40 q2 ∷
   rw⁻ 41 q3 ∷
   rw 42 q4 ∷
   re 43 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 45 q5 ∷
   re 39 5 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   re 41 3 (CX31 ∷ []) ∷
   rw 41 q2 ∷
   rw⁻ 42 q3 ∷
   rw 43 q4 ∷
   re 44 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 46 q5 ∷
   re 40 5 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   re 42 3 (CX31 ∷ []) ∷
   rw 42 q2 ∷
   rw⁻ 43 q3 ∷
   rw 44 q4 ∷
   re 45 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 47 q5 ∷
   re 41 5 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   re 43 3 (CX31 ∷ []) ∷
   rw 43 q2 ∷
   rw⁻ 44 q3 ∷
   rw 45 q4 ∷
   re 46 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 48 q5 ∷
   re 42 5 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   re 44 3 (CX31 ∷ []) ∷
   rw 44 q2 ∷
   rw⁻ 45 q3 ∷
   rw 46 q4 ∷
   re 47 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 49 q5 ∷
   re 43 5 (CS03 ∷ []) ∷
   rw 44 q6 ∷
   rw 45 q6 ∷
   rw 46 q6 ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   re 48 3 (CX31 ∷ []) ∷
   rw 48 q2 ∷
   rw⁻ 49 q7 ∷
   rw 50 q4 ∷
   re 51 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 53 q5 ∷
   re 47 5 (CK30 ∷ []) ∷
   rw 48 q6 ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   re 50 3 (CX31 ∷ []) ∷
   rw 50 q2 ∷
   rw⁻ 51 q3 ∷
   rw 52 q4 ∷
   re 53 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 55 q5 ∷
   re 49 5 (CS03 ∷ []) ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q1 ∷
   re 51 3 (CX31 ∷ []) ∷
   rw 51 q2 ∷
   rw⁻ 52 q3 ∷
   rw 53 q4 ∷
   re 54 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 56 q5 ∷
   re 50 5 (CS03 ∷ []) ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q1 ∷
   re 52 3 (CX31 ∷ []) ∷
   rw 52 q2 ∷
   rw⁻ 53 q3 ∷
   rw 54 q4 ∷
   re 55 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 57 q5 ∷
   re 51 5 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q1 ∷
   re 53 3 (CX31 ∷ []) ∷
   rw 53 q2 ∷
   rw⁻ 54 q3 ∷
   rw 55 q4 ∷
   re 56 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 58 q5 ∷
   re 52 5 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q1 ∷
   re 54 3 (CX31 ∷ []) ∷
   rw 54 q2 ∷
   rw⁻ 55 q3 ∷
   rw 56 q4 ∷
   re 57 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 59 q5 ∷
   re 53 5 (CS03 ∷ []) ∷
   re 55 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q1 ∷
   re 55 3 (CX31 ∷ []) ∷
   rw 55 q2 ∷
   rw⁻ 56 q3 ∷
   rw 57 q4 ∷
   re 58 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 60 q5 ∷
   re 54 5 (CS03 ∷ []) ∷
   re 56 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q1 ∷
   re 56 3 (CX31 ∷ []) ∷
   rw 56 q2 ∷
   rw⁻ 57 q3 ∷
   rw 58 q4 ∷
   re 59 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 61 q5 ∷
   re 55 5 (CS03 ∷ []) ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q1 ∷
   re 57 3 (CX31 ∷ []) ∷
   rw 57 q2 ∷
   rw⁻ 58 q3 ∷
   rw 59 q4 ∷
   re 60 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 62 q5 ∷
   re 56 5 (CS03 ∷ []) ∷
   re 58 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 57 q1 ∷
   re 58 3 (CX31 ∷ []) ∷
   rw 58 q2 ∷
   rw⁻ 59 q3 ∷
   rw 60 q4 ∷
   re 61 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 63 q5 ∷
   re 57 5 (CS03 ∷ []) ∷
   rw 58 q6 ∷
   rw 59 q6 ∷
   rw 60 q6 ∷
   re 62 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 61 q1 ∷
   re 62 3 (CX31 ∷ []) ∷
   rw 62 q2 ∷
   rw⁻ 63 q7 ∷
   rw 64 q4 ∷
   re 65 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 67 q5 ∷
   re 61 5 (CK30 ∷ []) ∷
   rw 62 q6 ∷
   rw 63 q6 ∷
   rw 64 q6 ∷
   rw 65 q6 ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 66 q1 ∷
   re 67 3 (CX31 ∷ []) ∷
   rw 67 q2 ∷
   rw⁻ 68 q7 ∷
   rw 69 q4 ∷
   re 70 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 72 q5 ∷
   re 66 5 (CK30 ∷ []) ∷
   rw 67 q6 ∷
   rw 68 q14 ∷
   rw⁻ 67 q15 ∷
   re 66 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷ []) Eq.refl

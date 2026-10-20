{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D346 (W : Ws) where

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
  q2 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q3 : Eqn
  q3 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q4 : Eqn
  q4 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ []) (CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (wn 616 W)
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q6 : Eqn
  q6 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q8 : Eqn
  q8 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q9 : Eqn
  q9 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q10 : Eqn
  q10 = eqn (CX13 ∷ Sw12 ∷ []) (Sw12 ∷ CX23 ∷ []) (wn 36 W)
  q11 : Eqn
  q11 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q12 : Eqn
  q12 = eqn (CX23 ∷ Sw12 ∷ []) (Sw12 ∷ CX13 ∷ []) (wn 37 W)
  q13 : Eqn
  q13 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q14 : Eqn
  q14 = eqn (CX12 ∷ S3 ∷ []) (S3 ∷ CX12 ∷ []) (low₃-comm ((CX₀₁ ↑)) (S))
  q15 : Eqn
  q15 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q16 : Eqn
  q16 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)

-- Bar(SSKSKK;1,2->0) passes groups of WBar(KiKiSSSKiSSSSSS;~1,3->0) part1: 500 steps
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part1 : ⟪ (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ Sw01 ∷ X1 ∷ CX13 ∷ X1 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ Sw01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CX13 ∷ X1 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part1 = derive (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ Sw01 ∷ X1 ∷ CX13 ∷ X1 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ Sw01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CX13 ∷ X1 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ [])
  (rw⁻ 51 q1 ∷
   rw 50 q2 ∷
   rw⁻ 49 q1 ∷
   re 50 3 (CS13 ∷ []) ∷
   rw 48 q3 ∷
   rw 47 q3 ∷
   rw 46 q2 ∷
   rw 45 q3 ∷
   rw 44 q2 ∷
   rw 43 q2 ∷
   rw 44 q4 ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   rw 44 q5 ∷
   rw 45 q1 ∷
   re 43 3 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   rw 45 q5 ∷
   rw 46 q1 ∷
   re 44 3 (CS03 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 45 q1 ∷
   rw 46 q5 ∷
   rw 47 q1 ∷
   re 45 3 (CS03 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 46 q1 ∷
   rw 47 q5 ∷
   rw 48 q1 ∷
   re 46 3 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   rw 48 q5 ∷
   rw 49 q1 ∷
   re 47 3 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 48 q1 ∷
   rw 49 q5 ∷
   rw 50 q1 ∷
   re 48 3 (CS03 ∷ []) ∷
   re 50 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   rw 50 q5 ∷
   rw 51 q1 ∷
   re 49 3 (CS03 ∷ []) ∷
   re 51 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 50 q1 ∷
   rw 51 q5 ∷
   rw 52 q1 ∷
   re 50 3 (CS03 ∷ []) ∷
   re 52 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 51 q1 ∷
   rw 52 q5 ∷
   rw 53 q1 ∷
   re 51 3 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 52 q1 ∷
   rw 53 q5 ∷
   rw 54 q1 ∷
   re 52 3 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 53 q1 ∷
   rw 54 q5 ∷
   rw 55 q1 ∷
   re 53 3 (CS03 ∷ []) ∷
   re 55 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 54 q1 ∷
   rw 55 q5 ∷
   rw 56 q1 ∷
   re 54 3 (CS03 ∷ []) ∷
   re 56 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 55 q1 ∷
   rw 56 q5 ∷
   rw 57 q1 ∷
   re 55 3 (CS03 ∷ []) ∷
   re 57 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 56 q1 ∷
   rw 57 q5 ∷
   rw 58 q1 ∷
   re 56 3 (CS03 ∷ []) ∷
   re 58 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 57 q1 ∷
   rw 58 q5 ∷
   rw 59 q1 ∷
   re 57 3 (CS03 ∷ []) ∷
   re 59 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 58 q1 ∷
   rw 59 q5 ∷
   rw 60 q1 ∷
   re 58 3 (CS03 ∷ []) ∷
   re 60 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 59 q1 ∷
   rw 60 q5 ∷
   rw 61 q1 ∷
   re 59 3 (CS03 ∷ []) ∷
   re 61 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 60 q1 ∷
   rw 61 q5 ∷
   rw 62 q1 ∷
   re 60 3 (CS03 ∷ []) ∷
   rw 61 q6 ∷
   rw 62 q6 ∷
   rw 63 q6 ∷
   re 65 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 64 q1 ∷
   rw 65 q7 ∷
   rw 66 q1 ∷
   re 64 3 (CK30 ∷ []) ∷
   rw 65 q6 ∷
   re 67 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 66 q1 ∷
   rw 67 q5 ∷
   rw 68 q1 ∷
   re 66 3 (CS03 ∷ []) ∷
   re 68 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 67 q1 ∷
   rw 68 q5 ∷
   rw 69 q1 ∷
   re 67 3 (CS03 ∷ []) ∷
   re 69 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 68 q1 ∷
   rw 69 q5 ∷
   rw 70 q1 ∷
   re 68 3 (CS03 ∷ []) ∷
   re 70 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 69 q1 ∷
   rw 70 q5 ∷
   rw 71 q1 ∷
   re 69 3 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 70 q1 ∷
   rw 71 q5 ∷
   rw 72 q1 ∷
   re 70 3 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 71 q1 ∷
   rw 72 q5 ∷
   rw 73 q1 ∷
   re 71 3 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 72 q1 ∷
   rw 73 q5 ∷
   rw 74 q1 ∷
   re 72 3 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 73 q1 ∷
   rw 74 q5 ∷
   rw 75 q1 ∷
   re 73 3 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 74 q1 ∷
   rw 75 q5 ∷
   rw 76 q1 ∷
   re 74 3 (CS03 ∷ []) ∷
   rw 75 q6 ∷
   rw 76 q6 ∷
   rw 77 q6 ∷
   re 79 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 78 q1 ∷
   rw 79 q7 ∷
   rw 80 q1 ∷
   re 78 3 (CK30 ∷ []) ∷
   rw 79 q6 ∷
   rw 80 q6 ∷
   rw 81 q6 ∷
   rw 82 q6 ∷
   re 84 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 83 q1 ∷
   rw 84 q7 ∷
   rw 85 q1 ∷
   re 83 3 (CK30 ∷ []) ∷
   rw 84 q6 ∷
   rw 85 q5 ∷
   rw 86 q5 ∷
   rw 87 q7 ∷
   rw 88 q5 ∷
   rw 89 q7 ∷
   rw 90 q7 ∷
   rw 91 q8 ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q9 ∷
   re 43 3 (CX13 ∷ []) ∷
   rw 43 q10 ∷
   rw⁻ 44 q11 ∷
   rw 45 q12 ∷
   re 46 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 48 q13 ∷
   re 42 5 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q9 ∷
   re 44 3 (CX13 ∷ []) ∷
   rw 44 q10 ∷
   rw⁻ 45 q11 ∷
   rw 46 q12 ∷
   re 47 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 49 q13 ∷
   re 43 5 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q9 ∷
   re 45 3 (CX13 ∷ []) ∷
   rw 45 q10 ∷
   rw⁻ 46 q11 ∷
   rw 47 q12 ∷
   re 48 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 50 q13 ∷
   re 44 5 (CS03 ∷ []) ∷
   re 46 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q9 ∷
   re 46 3 (CX13 ∷ []) ∷
   rw 46 q10 ∷
   rw⁻ 47 q11 ∷
   rw 48 q12 ∷
   re 49 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 51 q13 ∷
   re 45 5 (CS03 ∷ []) ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q9 ∷
   re 47 3 (CX13 ∷ []) ∷
   rw 47 q10 ∷
   rw⁻ 48 q11 ∷
   rw 49 q12 ∷
   re 50 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 52 q13 ∷
   re 46 5 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q9 ∷
   re 48 3 (CX13 ∷ []) ∷
   rw 48 q10 ∷
   rw⁻ 49 q11 ∷
   rw 50 q12 ∷
   re 51 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 53 q13 ∷
   re 47 5 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q9 ∷
   re 49 3 (CX13 ∷ []) ∷
   rw 49 q10 ∷
   rw⁻ 50 q11 ∷
   rw 51 q12 ∷
   re 52 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 54 q13 ∷
   re 48 5 (CS03 ∷ []) ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q9 ∷
   re 50 3 (CX13 ∷ []) ∷
   rw 50 q10 ∷
   rw⁻ 51 q11 ∷
   rw 52 q12 ∷
   re 53 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 55 q13 ∷
   re 49 5 (CS03 ∷ []) ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q9 ∷
   re 51 3 (CX13 ∷ []) ∷
   rw 51 q10 ∷
   rw⁻ 52 q11 ∷
   rw 53 q12 ∷
   re 54 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 56 q13 ∷
   re 50 5 (CS03 ∷ []) ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q9 ∷
   re 52 3 (CX13 ∷ []) ∷
   rw 52 q10 ∷
   rw⁻ 53 q11 ∷
   rw 54 q12 ∷
   re 55 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 57 q13 ∷
   re 51 5 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q9 ∷
   re 53 3 (CX13 ∷ []) ∷
   rw 53 q10 ∷
   rw⁻ 54 q11 ∷
   rw 55 q12 ∷
   re 56 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 58 q13 ∷
   re 52 5 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q9 ∷
   re 54 3 (CX13 ∷ []) ∷
   rw 54 q10 ∷
   rw⁻ 55 q11 ∷
   rw 56 q12 ∷
   re 57 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 59 q13 ∷
   re 53 5 (CS03 ∷ []) ∷
   re 55 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q9 ∷
   re 55 3 (CX13 ∷ []) ∷
   rw 55 q10 ∷
   rw⁻ 56 q11 ∷
   rw 57 q12 ∷
   re 58 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 60 q13 ∷
   re 54 5 (CS03 ∷ []) ∷
   re 56 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q9 ∷
   re 56 3 (CX13 ∷ []) ∷
   rw 56 q10 ∷
   rw⁻ 57 q11 ∷
   rw 58 q12 ∷
   re 59 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 61 q13 ∷
   re 55 5 (CS03 ∷ []) ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q9 ∷
   re 57 3 (CX13 ∷ []) ∷
   rw 57 q10 ∷
   rw⁻ 58 q11 ∷
   rw 59 q12 ∷
   re 60 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 62 q13 ∷
   re 56 5 (CS03 ∷ []) ∷
   re 58 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 57 q9 ∷
   re 58 3 (CX13 ∷ []) ∷
   rw 58 q10 ∷
   rw⁻ 59 q11 ∷
   rw 60 q12 ∷
   re 61 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 63 q13 ∷
   re 57 5 (CS03 ∷ []) ∷
   re 59 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q9 ∷
   re 59 3 (CX13 ∷ []) ∷
   rw 59 q10 ∷
   rw⁻ 60 q11 ∷
   rw 61 q12 ∷
   re 62 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 64 q13 ∷
   re 58 5 (CS03 ∷ []) ∷
   re 60 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q9 ∷
   re 60 3 (CX13 ∷ []) ∷
   rw 60 q10 ∷
   rw⁻ 61 q11 ∷
   rw 62 q12 ∷
   re 63 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 65 q13 ∷
   re 59 5 (CS03 ∷ []) ∷
   rw 60 q14 ∷
   rw 61 q14 ∷
   rw 62 q14 ∷
   re 64 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 63 q9 ∷
   re 64 3 (CX13 ∷ []) ∷
   rw 64 q10 ∷
   rw⁻ 65 q15 ∷
   rw 66 q12 ∷
   re 67 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 69 q13 ∷
   re 63 5 (CK30 ∷ []) ∷
   rw 64 q14 ∷
   re 66 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 65 q9 ∷
   re 66 3 (CX13 ∷ []) ∷
   rw 66 q10 ∷
   rw⁻ 67 q11 ∷
   rw 68 q12 ∷
   re 69 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 71 q13 ∷
   re 65 5 (CS03 ∷ []) ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 66 q9 ∷
   re 67 3 (CX13 ∷ []) ∷
   rw 67 q10 ∷
   rw⁻ 68 q11 ∷
   rw 69 q12 ∷
   re 70 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 72 q13 ∷
   re 66 5 (CS03 ∷ []) ∷
   re 68 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 67 q9 ∷
   re 68 3 (CX13 ∷ []) ∷
   rw 68 q10 ∷
   rw⁻ 69 q11 ∷
   rw 70 q12 ∷
   re 71 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 73 q13 ∷
   re 67 5 (CS03 ∷ []) ∷
   re 69 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 68 q9 ∷
   re 69 3 (CX13 ∷ []) ∷
   rw 69 q10 ∷
   rw⁻ 70 q11 ∷
   rw 71 q12 ∷
   re 72 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 74 q13 ∷
   re 68 5 (CS03 ∷ []) ∷
   re 70 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 69 q9 ∷
   re 70 3 (CX13 ∷ []) ∷
   rw 70 q10 ∷
   rw⁻ 71 q11 ∷
   rw 72 q12 ∷
   re 73 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 75 q13 ∷
   re 69 5 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 70 q9 ∷
   re 71 3 (CX13 ∷ []) ∷
   rw 71 q10 ∷
   rw⁻ 72 q11 ∷
   rw 73 q12 ∷
   re 74 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 76 q13 ∷
   re 70 5 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q9 ∷
   re 72 3 (CX13 ∷ []) ∷
   rw 72 q10 ∷
   rw⁻ 73 q11 ∷
   rw 74 q12 ∷
   re 75 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 77 q13 ∷
   re 71 5 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 72 q9 ∷
   re 73 3 (CX13 ∷ []) ∷
   rw 73 q10 ∷
   rw⁻ 74 q11 ∷
   rw 75 q12 ∷
   re 76 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 78 q13 ∷
   re 72 5 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q9 ∷
   re 74 3 (CX13 ∷ []) ∷
   rw 74 q10 ∷
   rw⁻ 75 q11 ∷
   rw 76 q12 ∷
   re 77 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 79 q13 ∷
   re 73 5 (CS03 ∷ []) ∷
   rw 74 q14 ∷
   rw 75 q14 ∷
   rw 76 q14 ∷
   re 78 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 77 q9 ∷
   re 78 3 (CX13 ∷ []) ∷
   rw 78 q10 ∷
   rw⁻ 79 q15 ∷
   rw 80 q12 ∷
   re 81 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 83 q13 ∷
   re 77 5 (CK30 ∷ []) ∷
   rw 78 q14 ∷
   rw 79 q14 ∷
   rw 80 q14 ∷
   rw 81 q14 ∷
   re 83 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 82 q9 ∷
   re 83 3 (CX13 ∷ []) ∷
   rw 83 q10 ∷
   rw⁻ 84 q15 ∷
   rw 85 q12 ∷
   re 86 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 88 q13 ∷
   re 82 5 (CK30 ∷ []) ∷
   rw 83 q14 ∷
   rw 84 q16 ∷
   rw⁻ 83 q6 ∷
   re 82 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 84 q1 ∷
   rw 83 q3 ∷
   rw⁻ 82 q1 ∷
   re 83 3 (CK31 ∷ []) ∷
   rw⁻ 81 q6 ∷
   rw⁻ 80 q6 ∷
   rw⁻ 79 q6 ∷
   rw⁻ 78 q6 ∷
   re 77 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 79 q1 ∷
   rw 78 q3 ∷
   rw⁻ 77 q1 ∷
   re 78 3 (CK31 ∷ []) ∷
   rw⁻ 76 q6 ∷
   rw⁻ 75 q6 ∷
   rw⁻ 74 q6 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 75 q1 ∷
   rw 74 q2 ∷
   rw⁻ 73 q1 ∷
   re 74 3 (CS13 ∷ []) ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 74 q1 ∷
   rw 73 q2 ∷
   rw⁻ 72 q1 ∷
   re 73 3 (CS13 ∷ []) ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 73 q1 ∷
   rw 72 q2 ∷
   rw⁻ 71 q1 ∷
   re 72 3 (CS13 ∷ []) ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 72 q1 ∷
   rw 71 q2 ∷
   rw⁻ 70 q1 ∷ []) Eq.refl

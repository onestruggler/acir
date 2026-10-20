{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D324 (W : Ws) where

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
  q1 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q2 : Eqn
  q2 = eqn (CX23 ∷ Sw12 ∷ []) (Sw12 ∷ CX13 ∷ []) (wn 37 W)
  q3 : Eqn
  q3 = eqn (CX13 ∷ Sw12 ∷ []) (Sw12 ∷ CX23 ∷ []) (wn 36 W)
  q4 : Eqn
  q4 = eqn (CX13 ∷ S2 ∷ []) (S2 ∷ CX13 ∷ []) (wn 883 W)
  q5 : Eqn
  q5 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q6 : Eqn
  q6 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q7 : Eqn
  q7 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q8 : Eqn
  q8 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q9 : Eqn
  q9 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q11 : Eqn
  q11 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q12 : Eqn
  q12 = eqn (CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ []) (CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ []) (wn 947 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q16 : Eqn
  q16 = eqn (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (wn 662 W)
  q17 : Eqn
  q17 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q18 : Eqn
  q18 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q19 : Eqn
  q19 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q20 : Eqn
  q20 = eqn (CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ []) (wn 880 W)
  q21 : Eqn
  q21 = eqn (Sw12 ∷ CX13 ∷ []) (CX23 ∷ Sw12 ∷ []) (wn 157 W)
  q22 : Eqn
  q22 = eqn (Sw12 ∷ CX23 ∷ []) (CX13 ∷ Sw12 ∷ []) (wn 158 W)

-- Bar(SSSKSS;1,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~1,2->0) part2: 500 steps
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part2 : ⟪ (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ Sw12 ∷ CX23 ∷ CS01 ∷ Sw12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ Sw23 ∷ X1 ∷ CS02 ∷ Sw23 ∷ CX12 ∷ X1 ∷ CS03 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part2 = derive (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ Sw12 ∷ CX23 ∷ CS01 ∷ Sw12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ Sw23 ∷ X1 ∷ CS02 ∷ Sw23 ∷ CX12 ∷ X1 ∷ CS03 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ [])
  (rw⁻ 69 q1 ∷
   rw 70 q2 ∷
   re 68 3 (CS02 ∷ []) ∷
   re 70 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 69 q3 ∷
   rw⁻ 70 q1 ∷
   rw 71 q2 ∷
   re 69 3 (CS02 ∷ []) ∷
   re 71 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 70 q3 ∷
   rw⁻ 71 q1 ∷
   rw 72 q2 ∷
   re 70 3 (CS02 ∷ []) ∷
   re 72 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 71 q3 ∷
   rw⁻ 72 q1 ∷
   rw 73 q2 ∷
   re 71 3 (CS02 ∷ []) ∷
   re 73 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 72 q3 ∷
   rw⁻ 73 q1 ∷
   rw 74 q2 ∷
   re 72 3 (CS02 ∷ []) ∷
   re 74 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 73 q3 ∷
   rw⁻ 74 q1 ∷
   rw 75 q2 ∷
   re 73 3 (CS02 ∷ []) ∷
   re 75 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 74 q3 ∷
   rw⁻ 75 q1 ∷
   rw 76 q2 ∷
   re 74 3 (CS02 ∷ []) ∷
   re 76 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 75 q3 ∷
   rw⁻ 76 q1 ∷
   rw 77 q2 ∷
   re 75 3 (CS02 ∷ []) ∷
   rw 76 q4 ∷
   rw 77 q4 ∷
   rw 78 q4 ∷
   re 80 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 79 q3 ∷
   rw⁻ 80 q5 ∷
   rw 81 q2 ∷
   re 79 3 (CK20 ∷ []) ∷
   rw 80 q4 ∷
   rw 81 q4 ∷
   rw 82 q4 ∷
   rw 83 q4 ∷
   re 85 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 84 q3 ∷
   rw⁻ 85 q5 ∷
   rw 86 q2 ∷
   re 84 3 (CK20 ∷ []) ∷
   rw 85 q4 ∷
   rw 86 q6 ∷
   rw⁻ 85 q7 ∷
   rw 84 q8 ∷
   rw⁻ 83 q7 ∷
   rw⁻ 82 q7 ∷
   rw⁻ 81 q7 ∷
   rw⁻ 80 q7 ∷
   rw 79 q8 ∷
   rw⁻ 78 q7 ∷
   rw⁻ 77 q7 ∷
   rw⁻ 76 q7 ∷
   rw 75 q9 ∷
   rw 74 q9 ∷
   rw 73 q9 ∷
   rw 72 q9 ∷
   rw 71 q9 ∷
   rw 70 q9 ∷
   rw 69 q9 ∷
   rw 68 q9 ∷
   rw 67 q9 ∷
   rw⁻ 66 q7 ∷
   rw 65 q8 ∷
   rw⁻ 64 q7 ∷
   rw⁻ 63 q7 ∷
   rw⁻ 62 q7 ∷
   rw 61 q9 ∷
   rw 60 q9 ∷
   rw 59 q9 ∷
   rw 58 q9 ∷
   rw 57 q9 ∷
   rw 56 q9 ∷
   rw 55 q9 ∷
   rw 54 q9 ∷
   rw 53 q9 ∷
   rw 52 q9 ∷
   rw 51 q9 ∷
   rw 50 q9 ∷
   rw 49 q9 ∷
   rw 48 q9 ∷
   rw 47 q9 ∷
   rw 46 q9 ∷
   rw 45 q9 ∷
   rw 44 q9 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q10 ∷
   rw 44 q9 ∷
   rw⁻ 43 q10 ∷
   re 44 3 (CS13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q10 ∷
   rw 43 q9 ∷
   rw⁻ 42 q10 ∷
   re 43 3 (CS13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q10 ∷
   rw 42 q9 ∷
   rw⁻ 41 q10 ∷
   re 42 3 (CS13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q10 ∷
   rw 41 q9 ∷
   rw⁻ 40 q10 ∷
   re 41 3 (CS13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q10 ∷
   rw 40 q9 ∷
   rw⁻ 39 q10 ∷
   re 40 3 (CS13 ∷ []) ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q10 ∷
   rw 39 q9 ∷
   rw⁻ 38 q10 ∷
   re 39 3 (CS13 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q10 ∷
   rw 38 q9 ∷
   rw⁻ 37 q10 ∷
   re 38 3 (CS13 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q10 ∷
   rw 37 q9 ∷
   rw⁻ 36 q10 ∷
   re 37 3 (CS13 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q10 ∷
   rw 36 q9 ∷
   rw⁻ 35 q10 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw⁻ 34 q11 ∷
   re 33 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q10 ∷
   rw 34 q8 ∷
   rw⁻ 33 q10 ∷
   re 34 3 (CK31 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q10 ∷
   rw 33 q9 ∷
   rw⁻ 32 q10 ∷
   re 33 3 (CS13 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q10 ∷
   rw 32 q9 ∷
   rw⁻ 31 q10 ∷
   re 32 3 (CS13 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q10 ∷
   rw 31 q9 ∷
   rw⁻ 30 q10 ∷
   re 31 3 (CS13 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q10 ∷
   rw 30 q9 ∷
   rw⁻ 29 q10 ∷
   re 30 3 (CS13 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q10 ∷
   rw 29 q9 ∷
   rw⁻ 28 q10 ∷
   re 29 3 (CS13 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q10 ∷
   rw 28 q9 ∷
   rw⁻ 27 q10 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 28 q12 ∷
   rw 27 q13 ∷
   rw 28 q13 ∷
   rw 29 q13 ∷
   rw 30 q13 ∷
   rw 31 q13 ∷
   rw 32 q13 ∷
   rw 33 q13 ∷
   rw 34 q13 ∷
   rw 35 q13 ∷
   rw 36 q13 ∷
   rw 37 q13 ∷
   rw 38 q13 ∷
   rw 39 q13 ∷
   rw 40 q13 ∷
   rw 41 q13 ∷
   rw 42 q13 ∷
   rw 43 q13 ∷
   rw 44 q13 ∷
   rw 45 q7 ∷
   rw 46 q7 ∷
   rw 47 q7 ∷
   rw 48 q14 ∷
   rw 49 q7 ∷
   rw 50 q13 ∷
   rw 51 q13 ∷
   rw 52 q13 ∷
   rw 53 q13 ∷
   rw 54 q13 ∷
   rw 55 q13 ∷
   rw 56 q13 ∷
   rw 57 q13 ∷
   rw 58 q13 ∷
   rw 59 q7 ∷
   rw 60 q7 ∷
   rw 61 q7 ∷
   rw 62 q14 ∷
   rw 63 q7 ∷
   rw 64 q7 ∷
   rw 65 q7 ∷
   rw 66 q7 ∷
   rw 67 q14 ∷
   rw 68 q7 ∷
   re 70 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 69 q10 ∷
   rw 70 q13 ∷
   rw 71 q10 ∷
   re 69 3 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 70 q10 ∷
   rw 71 q13 ∷
   rw 72 q10 ∷
   re 70 3 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 71 q10 ∷
   rw 72 q13 ∷
   rw 73 q10 ∷
   re 71 3 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 72 q10 ∷
   rw 73 q13 ∷
   rw 74 q10 ∷
   re 72 3 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 73 q10 ∷
   rw 74 q13 ∷
   rw 75 q10 ∷
   re 73 3 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 74 q10 ∷
   rw 75 q13 ∷
   rw 76 q10 ∷
   re 74 3 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 75 q10 ∷
   rw 76 q14 ∷
   rw 77 q10 ∷
   re 75 3 (CK30 ∷ []) ∷
   rw 76 q11 ∷
   re 78 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 77 q10 ∷
   rw 78 q13 ∷
   rw 79 q10 ∷
   re 77 3 (CS03 ∷ []) ∷
   re 79 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 78 q10 ∷
   rw 79 q13 ∷
   rw 80 q10 ∷
   re 78 3 (CS03 ∷ []) ∷
   re 80 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 79 q10 ∷
   rw 80 q13 ∷
   rw 81 q10 ∷
   re 79 3 (CS03 ∷ []) ∷
   re 81 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 80 q10 ∷
   rw 81 q13 ∷
   rw 82 q10 ∷
   re 80 3 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 81 q10 ∷
   rw 82 q13 ∷
   rw 83 q10 ∷
   re 81 3 (CS03 ∷ []) ∷
   re 83 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 82 q10 ∷
   rw 83 q13 ∷
   rw 84 q10 ∷
   re 82 3 (CS03 ∷ []) ∷
   re 84 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 83 q10 ∷
   rw 84 q13 ∷
   rw 85 q10 ∷
   re 83 3 (CS03 ∷ []) ∷
   re 85 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 84 q10 ∷
   rw 85 q13 ∷
   rw 86 q10 ∷
   re 84 3 (CS03 ∷ []) ∷
   re 86 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 85 q10 ∷
   rw 86 q13 ∷
   rw 87 q10 ∷
   re 85 3 (CS03 ∷ []) ∷
   rw 86 q15 ∷
   re 27 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 26 q3 ∷
   rw⁻ 27 q1 ∷
   rw 28 q2 ∷
   re 26 3 (CS02 ∷ []) ∷
   re 28 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 27 q3 ∷
   rw⁻ 28 q1 ∷
   rw 29 q2 ∷
   re 27 3 (CS02 ∷ []) ∷
   re 29 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 28 q3 ∷
   rw⁻ 29 q1 ∷
   rw 30 q2 ∷
   re 28 3 (CS02 ∷ []) ∷
   re 30 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 29 q3 ∷
   rw⁻ 30 q1 ∷
   rw 31 q2 ∷
   re 29 3 (CS02 ∷ []) ∷
   re 31 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 30 q3 ∷
   rw⁻ 31 q1 ∷
   rw 32 q2 ∷
   re 30 3 (CS02 ∷ []) ∷
   re 32 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 31 q3 ∷
   rw⁻ 32 q1 ∷
   rw 33 q2 ∷
   re 31 3 (CS02 ∷ []) ∷
   re 33 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 32 q3 ∷
   rw⁻ 33 q1 ∷
   rw 34 q2 ∷
   re 32 3 (CS02 ∷ []) ∷
   re 34 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 33 q3 ∷
   rw⁻ 34 q1 ∷
   rw 35 q2 ∷
   re 33 3 (CS02 ∷ []) ∷
   re 35 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 34 q3 ∷
   rw⁻ 35 q1 ∷
   rw 36 q2 ∷
   re 34 3 (CS02 ∷ []) ∷
   re 36 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 35 q3 ∷
   rw⁻ 36 q1 ∷
   rw 37 q2 ∷
   re 35 3 (CS02 ∷ []) ∷
   re 37 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 36 q3 ∷
   rw⁻ 37 q1 ∷
   rw 38 q2 ∷
   re 36 3 (CS02 ∷ []) ∷
   re 38 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 37 q3 ∷
   rw⁻ 38 q1 ∷
   rw 39 q2 ∷
   re 37 3 (CS02 ∷ []) ∷
   re 39 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 38 q3 ∷
   rw⁻ 39 q1 ∷
   rw 40 q2 ∷
   re 38 3 (CS02 ∷ []) ∷
   re 40 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 39 q3 ∷
   rw⁻ 40 q1 ∷
   rw 41 q2 ∷
   re 39 3 (CS02 ∷ []) ∷
   re 41 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 40 q3 ∷
   rw⁻ 41 q1 ∷
   rw 42 q2 ∷
   re 40 3 (CS02 ∷ []) ∷
   re 42 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 41 q3 ∷
   rw⁻ 42 q1 ∷
   rw 43 q2 ∷
   re 41 3 (CS02 ∷ []) ∷
   re 43 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 42 q3 ∷
   rw⁻ 43 q1 ∷
   rw 44 q2 ∷
   re 42 3 (CS02 ∷ []) ∷
   re 44 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 43 q3 ∷
   rw⁻ 44 q1 ∷
   rw 45 q2 ∷
   re 43 3 (CS02 ∷ []) ∷
   rw 44 q4 ∷
   rw 45 q4 ∷
   rw 46 q4 ∷
   re 48 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 47 q3 ∷
   rw⁻ 48 q5 ∷
   rw 49 q2 ∷
   re 47 3 (CK20 ∷ []) ∷
   rw 48 q4 ∷
   re 50 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 49 q3 ∷
   rw⁻ 50 q1 ∷
   rw 51 q2 ∷
   re 49 3 (CS02 ∷ []) ∷
   re 51 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 50 q3 ∷
   rw⁻ 51 q1 ∷
   rw 52 q2 ∷
   re 50 3 (CS02 ∷ []) ∷
   re 52 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 51 q3 ∷
   rw⁻ 52 q1 ∷
   rw 53 q2 ∷
   re 51 3 (CS02 ∷ []) ∷
   re 53 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 52 q3 ∷
   rw⁻ 53 q1 ∷
   rw 54 q2 ∷
   re 52 3 (CS02 ∷ []) ∷
   re 54 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 53 q3 ∷
   rw⁻ 54 q1 ∷
   rw 55 q2 ∷
   re 53 3 (CS02 ∷ []) ∷
   re 55 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 54 q3 ∷
   rw⁻ 55 q1 ∷
   rw 56 q2 ∷
   re 54 3 (CS02 ∷ []) ∷
   re 56 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 55 q3 ∷
   rw⁻ 56 q1 ∷
   rw 57 q2 ∷
   re 55 3 (CS02 ∷ []) ∷
   re 57 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 56 q3 ∷
   rw⁻ 57 q1 ∷
   rw 58 q2 ∷
   re 56 3 (CS02 ∷ []) ∷
   re 58 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 57 q3 ∷
   rw⁻ 58 q1 ∷
   rw 59 q2 ∷
   re 57 3 (CS02 ∷ []) ∷
   rw 58 q4 ∷
   rw 59 q4 ∷
   rw 60 q4 ∷
   re 62 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 61 q3 ∷
   rw⁻ 62 q5 ∷
   rw 63 q2 ∷
   re 61 3 (CK20 ∷ []) ∷
   rw 62 q4 ∷
   rw 63 q4 ∷
   rw 64 q4 ∷
   rw 65 q4 ∷
   re 67 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 66 q3 ∷
   rw⁻ 67 q5 ∷
   rw 68 q2 ∷
   re 66 3 (CK20 ∷ []) ∷
   rw 67 q4 ∷
   rw 20 q16 ∷
   rw 94 q17 ∷
   rw 93 q18 ∷
   re 92 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 94 q19 ∷
   rw 93 q20 ∷
   rw⁻ 92 q18 ∷
   rw 95 q17 ∷
   re 93 3 (CS03 ∷ []) ∷
   rw 94 q19 ∷
   re 93 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 99 q17 ∷
   re 97 3 (CX13 ∷ []) ∷
   rw 96 q21 ∷
   rw 95 q1 ∷
   rw 94 q22 ∷
   re 94 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 93 q19 ∷
   re 94 5 (CS03 ∷ []) ∷
   rw 96 q17 ∷
   rw 95 q18 ∷
   re 94 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 96 q19 ∷
   rw 95 q20 ∷
   rw⁻ 94 q18 ∷
   rw 97 q17 ∷
   re 95 3 (CS03 ∷ []) ∷
   rw 96 q19 ∷
   rw 93 q17 ∷
   rw 92 q18 ∷
   re 91 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 93 q19 ∷
   rw 92 q20 ∷ []) Eq.refl

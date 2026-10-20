{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D261 (W : Ws) where

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
  q2 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q3 : Eqn
  q3 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q4 : Eqn
  q4 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q5 : Eqn
  q5 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q6 : Eqn
  q6 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q7 : Eqn
  q7 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X2 ∷ []) (X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (wn 842 W)
  q8 : Eqn
  q8 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q9 : Eqn
  q9 = eqn (CK10 ∷ X3 ∷ []) (X3 ∷ CK10 ∷ []) (low-comm (CK₁₀) ((X ↑)))
  q10 : Eqn
  q10 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q11 : Eqn
  q11 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q12 : Eqn
  q12 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q13 : Eqn
  q13 = eqn (CX31 ∷ X3 ∷ CX32 ∷ X3 ∷ []) (X3 ∷ CX32 ∷ X3 ∷ CX31 ∷ []) (wn 537 W)
  q14 : Eqn
  q14 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q15 : Eqn
  q15 = eqn (S1 ∷ CX32 ∷ []) (CX32 ∷ S1 ∷ []) (low-comm ((S ↑)) (CX₁₀))
  q16 : Eqn
  q16 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q19 : Eqn
  q19 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q20 : Eqn
  q20 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q21 : Eqn
  q21 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q22 : Eqn
  q22 = eqn (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X3 ∷ CX32 ∷ X3 ∷ []) (X3 ∷ CX32 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) (wn 538 W)
  q23 : Eqn
  q23 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q24 : Eqn
  q24 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q25 : Eqn
  q25 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q26 : Eqn
  q26 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (wn 843 W)
  q27 : Eqn
  q27 = eqn (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) (wn 13 W)
  q28 : Eqn
  q28 = eqn (CX32 ∷ Sw12 ∷ []) (Sw12 ∷ CX31 ∷ []) (wn 78 W)
  q29 : Eqn
  q29 = eqn (CX31 ∷ S2 ∷ []) (S2 ∷ CX31 ∷ []) (wn 762 W)
  q30 : Eqn
  q30 = eqn (CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (wn 844 W)
  q31 : Eqn
  q31 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q32 : Eqn
  q32 = eqn (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ []) (CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) (wn 845 W)
  q33 : Eqn
  q33 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (wn 846 W)
  q34 : Eqn
  q34 = eqn (CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (wn 847 W)
  q35 : Eqn
  q35 = eqn (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) (CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) (wn 848 W)

-- Bar(SSKSKK;3,1->0) passes groups of WBar(SSSKSS;~3,2->0): 771 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-groups-of-WBar⟨SSSKSS~32-⟶0⟩ : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-groups-of-WBar⟨SSSKSS~32-⟶0⟩ = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 37 q1 ∷
   rw 36 q2 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q3 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q3 ∷
   re 33 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 35 q3 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q3 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q3 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q3 ∷
   rw 29 q2 ∷
   rw 28 q4 ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   rw 25 q4 ∷
   rw 24 q5 ∷
   rw 23 q5 ∷
   re 22 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 24 q3 ∷
   rw 21 q5 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   rw 16 q5 ∷
   rw 15 q6 ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   rw 9 q4 ∷
   rw 8 q6 ∷
   rw 7 q4 ∷
   re 6 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q3 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q3 ∷
   rw 1 q7 ∷
   rw 0 q8 ∷
   rw 3 q1 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 4 q1 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 5 q1 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CK30 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q8 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 12 q1 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 14 q1 ∷
   re 12 3 (CK30 ∷ []) ∷
   rw 15 q1 ∷
   re 13 3 (CK30 ∷ []) ∷
   rw 16 q1 ∷
   re 14 3 (CX31 ∷ []) ∷
   rw⁻ 15 q4 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 17 q4 ∷
   rw⁻ 18 q6 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 21 q5 ∷
   rw⁻ 22 q4 ∷
   rw⁻ 23 q6 ∷
   rw⁻ 24 q5 ∷
   rw⁻ 25 q5 ∷
   rw⁻ 26 q5 ∷
   rw⁻ 27 q5 ∷
   rw⁻ 28 q5 ∷
   rw⁻ 29 q5 ∷
   rw 32 q1 ∷
   re 30 3 (CX31 ∷ []) ∷
   rw⁻ 31 q5 ∷
   rw⁻ 32 q5 ∷
   rw⁻ 33 q4 ∷
   rw⁻ 34 q5 ∷
   rw⁻ 35 q4 ∷
   rw⁻ 36 q4 ∷
   rw 37 q3 ∷
   rw 36 q9 ∷
   rw 37 q10 ∷
   rw 38 q9 ∷
   rw 35 q9 ∷
   rw 36 q10 ∷
   rw 37 q9 ∷
   rw 34 q11 ∷
   rw 35 q12 ∷
   rw 36 q11 ∷
   rw 33 q9 ∷
   rw 34 q10 ∷
   rw 35 q9 ∷
   rw 32 q11 ∷
   rw 33 q12 ∷
   rw 34 q11 ∷
   rw 31 q11 ∷
   rw 32 q12 ∷
   rw 33 q11 ∷
   rw 30 q13 ∷
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
   rw 23 q14 ∷
   rw 24 q15 ∷
   rw 25 q14 ∷
   rw 22 q9 ∷
   rw 23 q10 ∷
   rw 24 q9 ∷
   rw 21 q11 ∷
   rw 22 q12 ∷
   rw 23 q11 ∷
   rw 20 q11 ∷
   rw 21 q12 ∷
   rw 22 q11 ∷
   rw 19 q11 ∷
   rw 20 q12 ∷
   rw 21 q11 ∷
   rw 18 q14 ∷
   rw 19 q15 ∷
   rw 20 q14 ∷
   rw 17 q9 ∷
   rw 18 q10 ∷
   rw 19 q9 ∷
   rw 16 q14 ∷
   rw 17 q15 ∷
   rw 18 q14 ∷
   rw 15 q9 ∷
   rw 16 q10 ∷
   rw 17 q9 ∷
   rw 14 q13 ∷
   rw 17 q16 ∷
   rw⁻ 16 q17 ∷
   rw⁻ 15 q18 ∷
   rw⁻ 14 q17 ∷
   re 13 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q19 ∷
   rw 14 q20 ∷
   rw⁻ 13 q19 ∷
   re 14 3 (CK31 ∷ []) ∷
   re 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q19 ∷
   rw 13 q20 ∷
   rw⁻ 12 q19 ∷
   re 13 3 (CK31 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q19 ∷
   rw 12 q21 ∷
   rw⁻ 11 q19 ∷
   re 12 3 (CS13 ∷ []) ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q19 ∷
   rw 11 q20 ∷
   rw⁻ 10 q19 ∷
   re 11 3 (CK31 ∷ []) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q19 ∷
   rw 10 q21 ∷
   rw⁻ 9 q19 ∷
   re 10 3 (CS13 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q19 ∷
   rw 9 q21 ∷
   rw⁻ 8 q19 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 9 q22 ∷
   rw 8 q17 ∷
   rw 9 q18 ∷
   rw 10 q17 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q19 ∷
   rw 12 q23 ∷
   rw 13 q19 ∷
   re 11 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q19 ∷
   rw 13 q23 ∷
   rw 14 q19 ∷
   re 12 3 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 13 q19 ∷
   rw 14 q24 ∷
   rw 15 q19 ∷
   re 13 3 (CK30 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q19 ∷
   rw 15 q23 ∷
   rw 16 q19 ∷
   re 14 3 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 15 q19 ∷
   rw 16 q24 ∷
   rw 17 q19 ∷
   re 15 3 (CK30 ∷ []) ∷
   re 17 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 16 q19 ∷
   rw 17 q24 ∷
   rw 18 q19 ∷
   re 16 3 (CK30 ∷ []) ∷
   rw 17 q25 ∷
   rw 34 q26 ∷
   re 34 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 33 q27 ∷
   rw⁻ 34 q12 ∷
   rw 35 q28 ∷
   re 33 3 (CS02 ∷ []) ∷
   re 35 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 34 q27 ∷
   rw⁻ 35 q12 ∷
   rw 36 q28 ∷
   re 34 3 (CS02 ∷ []) ∷
   re 36 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 35 q27 ∷
   rw⁻ 36 q12 ∷
   rw 37 q28 ∷
   re 35 3 (CS02 ∷ []) ∷
   re 37 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 36 q27 ∷
   rw⁻ 37 q12 ∷
   rw 38 q28 ∷
   re 36 3 (CS02 ∷ []) ∷
   re 38 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 37 q27 ∷
   rw⁻ 38 q12 ∷
   rw 39 q28 ∷
   re 37 3 (CS02 ∷ []) ∷
   re 39 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 38 q27 ∷
   rw⁻ 39 q12 ∷
   rw 40 q28 ∷
   re 38 3 (CS02 ∷ []) ∷
   re 40 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 39 q27 ∷
   rw⁻ 40 q10 ∷
   rw 41 q28 ∷
   re 39 3 (CK20 ∷ []) ∷
   rw 40 q29 ∷
   re 42 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 41 q27 ∷
   rw⁻ 42 q12 ∷
   rw 43 q28 ∷
   re 41 3 (CS02 ∷ []) ∷
   re 43 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 42 q27 ∷
   rw⁻ 43 q12 ∷
   rw 44 q28 ∷
   re 42 3 (CS02 ∷ []) ∷
   re 44 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 43 q27 ∷
   rw⁻ 44 q12 ∷
   rw 45 q28 ∷
   re 43 3 (CS02 ∷ []) ∷
   re 45 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 44 q27 ∷
   rw⁻ 45 q12 ∷
   rw 46 q28 ∷
   re 44 3 (CS02 ∷ []) ∷
   re 46 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 45 q27 ∷
   rw⁻ 46 q12 ∷
   rw 47 q28 ∷
   re 45 3 (CS02 ∷ []) ∷
   re 47 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 46 q27 ∷
   rw⁻ 47 q12 ∷
   rw 48 q28 ∷
   re 46 3 (CS02 ∷ []) ∷
   re 48 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 47 q27 ∷
   rw⁻ 48 q12 ∷
   rw 49 q28 ∷
   re 47 3 (CS02 ∷ []) ∷
   re 49 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 48 q27 ∷
   rw⁻ 49 q12 ∷
   rw 50 q28 ∷
   re 48 3 (CS02 ∷ []) ∷
   re 50 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 49 q27 ∷
   rw⁻ 50 q12 ∷
   rw 51 q28 ∷
   re 49 3 (CS02 ∷ []) ∷
   rw 18 q30 ∷
   re 18 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 17 q27 ∷
   rw⁻ 18 q12 ∷
   rw 19 q28 ∷
   re 17 3 (CS02 ∷ []) ∷
   re 19 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 18 q27 ∷
   rw⁻ 19 q12 ∷
   rw 20 q28 ∷
   re 18 3 (CS02 ∷ []) ∷
   re 20 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 19 q27 ∷
   rw⁻ 20 q12 ∷
   rw 21 q28 ∷
   re 19 3 (CS02 ∷ []) ∷
   re 21 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 20 q27 ∷
   rw⁻ 21 q12 ∷
   rw 22 q28 ∷
   re 20 3 (CS02 ∷ []) ∷
   re 22 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 21 q27 ∷
   rw⁻ 22 q12 ∷
   rw 23 q28 ∷
   re 21 3 (CS02 ∷ []) ∷
   re 23 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 22 q27 ∷
   rw⁻ 23 q12 ∷
   rw 24 q28 ∷
   re 22 3 (CS02 ∷ []) ∷
   re 24 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 23 q27 ∷
   rw⁻ 24 q10 ∷
   rw 25 q28 ∷
   re 23 3 (CK20 ∷ []) ∷
   rw 24 q29 ∷
   re 26 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 25 q27 ∷
   rw⁻ 26 q12 ∷
   rw 27 q28 ∷
   re 25 3 (CS02 ∷ []) ∷
   re 27 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 26 q27 ∷
   rw⁻ 27 q12 ∷
   rw 28 q28 ∷
   re 26 3 (CS02 ∷ []) ∷
   re 28 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 27 q27 ∷
   rw⁻ 28 q12 ∷
   rw 29 q28 ∷
   re 27 3 (CS02 ∷ []) ∷
   re 29 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 28 q27 ∷
   rw⁻ 29 q12 ∷
   rw 30 q28 ∷
   re 28 3 (CS02 ∷ []) ∷
   re 30 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 29 q27 ∷
   rw⁻ 30 q12 ∷
   rw 31 q28 ∷
   re 29 3 (CS02 ∷ []) ∷
   re 31 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 30 q27 ∷
   rw⁻ 31 q12 ∷
   rw 32 q28 ∷
   re 30 3 (CS02 ∷ []) ∷
   re 32 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 31 q27 ∷
   rw⁻ 32 q12 ∷
   rw 33 q28 ∷
   re 31 3 (CS02 ∷ []) ∷
   re 33 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 32 q27 ∷
   rw⁻ 33 q12 ∷
   rw 34 q28 ∷
   re 32 3 (CS02 ∷ []) ∷
   re 34 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 33 q27 ∷
   rw⁻ 34 q12 ∷
   rw 35 q28 ∷
   re 33 3 (CS02 ∷ []) ∷
   rw 34 q16 ∷
   rw 33 q21 ∷
   rw 32 q21 ∷
   rw 31 q21 ∷
   rw 30 q21 ∷
   rw 29 q21 ∷
   rw 28 q21 ∷
   rw 27 q21 ∷
   rw 26 q21 ∷
   rw 25 q21 ∷
   rw⁻ 24 q31 ∷
   rw 23 q20 ∷
   rw 22 q21 ∷
   rw 21 q21 ∷
   rw 20 q21 ∷
   rw 19 q21 ∷
   rw 18 q21 ∷
   rw 17 q21 ∷
   re 16 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q19 ∷
   rw 17 q20 ∷
   rw⁻ 16 q19 ∷
   re 17 3 (CK31 ∷ []) ∷
   re 15 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q19 ∷
   rw 16 q20 ∷
   rw⁻ 15 q19 ∷
   re 16 3 (CK31 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q19 ∷
   rw 15 q21 ∷
   rw⁻ 14 q19 ∷
   re 15 3 (CS13 ∷ []) ∷
   re 13 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q19 ∷
   rw 14 q20 ∷
   rw⁻ 13 q19 ∷
   re 14 3 (CK31 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q19 ∷
   rw 13 q21 ∷
   rw⁻ 12 q19 ∷
   re 13 3 (CS13 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q19 ∷
   rw 12 q21 ∷
   rw⁻ 11 q19 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 12 q32 ∷
   rw 11 q23 ∷
   rw 12 q23 ∷
   rw 13 q23 ∷
   rw 14 q23 ∷
   rw 15 q23 ∷
   rw 16 q23 ∷
   rw 17 q24 ∷
   rw 18 q31 ∷
   rw 19 q23 ∷
   rw 20 q23 ∷
   rw 21 q23 ∷
   rw 22 q23 ∷
   rw 23 q23 ∷
   rw 24 q23 ∷
   rw 25 q23 ∷
   rw 26 q23 ∷
   rw 27 q23 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q19 ∷
   rw 29 q23 ∷
   rw 30 q19 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q19 ∷
   rw 30 q23 ∷
   rw 31 q19 ∷
   re 29 3 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 30 q19 ∷
   rw 31 q24 ∷
   rw 32 q19 ∷
   re 30 3 (CK30 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q19 ∷
   rw 32 q23 ∷
   rw 33 q19 ∷
   re 31 3 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 32 q19 ∷
   rw 33 q24 ∷
   rw 34 q19 ∷
   re 32 3 (CK30 ∷ []) ∷
   re 34 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 33 q19 ∷
   rw 34 q24 ∷
   rw 35 q19 ∷
   re 33 3 (CK30 ∷ []) ∷
   rw 34 q25 ∷
   rw 56 q9 ∷
   rw 57 q10 ∷
   rw 58 q9 ∷
   rw 55 q9 ∷
   rw 56 q10 ∷
   rw 57 q9 ∷
   rw 54 q11 ∷
   rw 55 q12 ∷
   rw 56 q11 ∷
   rw 53 q9 ∷
   rw 54 q10 ∷
   rw 55 q9 ∷
   rw 52 q11 ∷
   rw 53 q12 ∷
   rw 54 q11 ∷
   rw 51 q11 ∷
   rw 52 q12 ∷
   rw 53 q11 ∷
   rw 50 q13 ∷
   rw 49 q11 ∷
   rw 50 q12 ∷
   rw 51 q11 ∷
   rw 48 q11 ∷
   rw 49 q12 ∷
   rw 50 q11 ∷
   rw 47 q11 ∷
   rw 48 q12 ∷
   rw 49 q11 ∷
   rw 46 q11 ∷
   rw 47 q12 ∷
   rw 48 q11 ∷
   rw 45 q11 ∷
   rw 46 q12 ∷
   rw 47 q11 ∷
   rw 44 q11 ∷
   rw 45 q12 ∷
   rw 46 q11 ∷
   rw 43 q14 ∷
   rw 44 q15 ∷
   rw 45 q14 ∷
   rw 42 q9 ∷
   rw 43 q10 ∷
   rw 44 q9 ∷
   rw 41 q11 ∷
   rw 42 q12 ∷
   rw 43 q11 ∷
   rw 40 q11 ∷
   rw 41 q12 ∷
   rw 42 q11 ∷
   rw 39 q11 ∷
   rw 40 q12 ∷
   rw 41 q11 ∷
   rw 38 q14 ∷
   rw 39 q15 ∷
   rw 40 q14 ∷
   rw 37 q9 ∷
   rw 38 q10 ∷
   rw 39 q9 ∷
   rw 36 q14 ∷
   rw 37 q15 ∷
   rw 38 q14 ∷
   rw 35 q9 ∷
   rw 36 q10 ∷
   rw 37 q9 ∷
   rw 34 q13 ∷
   rw 37 q16 ∷
   rw⁻ 36 q17 ∷
   rw⁻ 35 q18 ∷
   rw⁻ 34 q17 ∷
   re 33 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q19 ∷
   rw 34 q20 ∷
   rw⁻ 33 q19 ∷
   re 34 3 (CK31 ∷ []) ∷
   re 32 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q19 ∷
   rw 33 q20 ∷
   rw⁻ 32 q19 ∷
   re 33 3 (CK31 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q19 ∷
   rw 32 q21 ∷
   rw⁻ 31 q19 ∷
   re 32 3 (CS13 ∷ []) ∷
   re 30 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q19 ∷
   rw 31 q20 ∷
   rw⁻ 30 q19 ∷
   re 31 3 (CK31 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q19 ∷
   rw 30 q21 ∷
   rw⁻ 29 q19 ∷
   re 30 3 (CS13 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q19 ∷
   rw 29 q21 ∷
   rw⁻ 28 q19 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 29 q22 ∷
   rw 28 q17 ∷
   rw 29 q18 ∷
   rw 30 q17 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q19 ∷
   rw 32 q23 ∷
   rw 33 q19 ∷
   re 31 3 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q19 ∷
   rw 33 q23 ∷
   rw 34 q19 ∷
   re 32 3 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 33 q19 ∷
   rw 34 q24 ∷
   rw 35 q19 ∷
   re 33 3 (CK30 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q19 ∷
   rw 35 q23 ∷
   rw 36 q19 ∷
   re 34 3 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 35 q19 ∷
   rw 36 q24 ∷
   rw 37 q19 ∷
   re 35 3 (CK30 ∷ []) ∷
   re 37 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 36 q19 ∷
   rw 37 q24 ∷
   rw 38 q19 ∷
   re 36 3 (CK30 ∷ []) ∷
   rw 37 q25 ∷
   rw 54 q33 ∷
   re 54 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 53 q27 ∷
   rw⁻ 54 q12 ∷
   rw 55 q28 ∷
   re 53 3 (CS02 ∷ []) ∷
   re 55 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 54 q27 ∷
   rw⁻ 55 q12 ∷
   rw 56 q28 ∷
   re 54 3 (CS02 ∷ []) ∷
   re 56 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 55 q27 ∷
   rw⁻ 56 q12 ∷
   rw 57 q28 ∷
   re 55 3 (CS02 ∷ []) ∷
   re 57 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 56 q27 ∷
   rw⁻ 57 q10 ∷
   rw 58 q28 ∷
   re 56 3 (CK20 ∷ []) ∷
   re 58 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 57 q27 ∷
   rw⁻ 58 q12 ∷
   rw 59 q28 ∷
   re 57 3 (CS02 ∷ []) ∷
   re 59 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 58 q27 ∷
   rw⁻ 59 q12 ∷
   rw 60 q28 ∷
   re 58 3 (CS02 ∷ []) ∷
   rw 38 q34 ∷
   re 38 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 37 q27 ∷
   rw⁻ 38 q12 ∷
   rw 39 q28 ∷
   re 37 3 (CS02 ∷ []) ∷
   re 39 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 38 q27 ∷
   rw⁻ 39 q12 ∷
   rw 40 q28 ∷
   re 38 3 (CS02 ∷ []) ∷
   re 40 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 39 q27 ∷
   rw⁻ 40 q12 ∷
   rw 41 q28 ∷
   re 39 3 (CS02 ∷ []) ∷
   re 41 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 40 q27 ∷
   rw⁻ 41 q10 ∷
   rw 42 q28 ∷
   re 40 3 (CK20 ∷ []) ∷
   re 42 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 41 q27 ∷
   rw⁻ 42 q12 ∷
   rw 43 q28 ∷
   re 41 3 (CS02 ∷ []) ∷
   re 43 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 42 q27 ∷
   rw⁻ 43 q12 ∷
   rw 44 q28 ∷
   re 42 3 (CS02 ∷ []) ∷
   rw 43 q16 ∷
   rw 42 q21 ∷
   rw 41 q21 ∷
   rw 40 q20 ∷
   rw 39 q21 ∷
   rw 38 q21 ∷
   rw 37 q21 ∷
   re 36 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q19 ∷
   rw 37 q20 ∷
   rw⁻ 36 q19 ∷
   re 37 3 (CK31 ∷ []) ∷
   re 35 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q19 ∷
   rw 36 q20 ∷
   rw⁻ 35 q19 ∷
   re 36 3 (CK31 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q19 ∷
   rw 35 q21 ∷
   rw⁻ 34 q19 ∷
   re 35 3 (CS13 ∷ []) ∷
   re 33 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q19 ∷
   rw 34 q20 ∷
   rw⁻ 33 q19 ∷
   re 34 3 (CK31 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q19 ∷
   rw 33 q21 ∷
   rw⁻ 32 q19 ∷
   re 33 3 (CS13 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q19 ∷
   rw 32 q21 ∷
   rw⁻ 31 q19 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw 32 q35 ∷
   rw 31 q23 ∷
   rw 32 q23 ∷
   rw 33 q23 ∷
   rw 34 q24 ∷
   rw 35 q23 ∷
   rw 36 q23 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q19 ∷
   rw 38 q23 ∷
   rw 39 q19 ∷
   re 37 3 (CS03 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q19 ∷
   rw 39 q23 ∷
   rw 40 q19 ∷
   re 38 3 (CS03 ∷ []) ∷
   re 40 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 39 q19 ∷
   rw 40 q24 ∷
   rw 41 q19 ∷
   re 39 3 (CK30 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q19 ∷
   rw 41 q23 ∷
   rw 42 q19 ∷
   re 40 3 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 41 q19 ∷
   rw 42 q24 ∷
   rw 43 q19 ∷
   re 41 3 (CK30 ∷ []) ∷
   re 43 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 42 q19 ∷
   rw 43 q24 ∷
   rw 44 q19 ∷
   re 42 3 (CK30 ∷ []) ∷
   rw 43 q25 ∷ []) Eq.refl

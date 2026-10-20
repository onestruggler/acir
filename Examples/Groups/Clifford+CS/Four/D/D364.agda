{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D364 (W : Ws) where

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
  q1 = eqn (CS13 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ []) (wn 629 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q3 : Eqn
  q3 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q5 : Eqn
  q5 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q6 : Eqn
  q6 = eqn (CX23 ∷ X2 ∷ CX21 ∷ X2 ∷ []) (X2 ∷ CX21 ∷ X2 ∷ CX23 ∷ []) (wn 673 W)
  q7 : Eqn
  q7 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q8 : Eqn
  q8 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q9 : Eqn
  q9 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q10 : Eqn
  q10 = eqn (Sw12 ∷ CX31 ∷ []) (CX32 ∷ Sw12 ∷ []) (wn 113 W)
  q11 : Eqn
  q11 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q12 : Eqn
  q12 = eqn (Sw12 ∷ CX32 ∷ []) (CX31 ∷ Sw12 ∷ []) (wn 114 W)
  q13 : Eqn
  q13 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q14 : Eqn
  q14 = eqn (X2 ∷ S3 ∷ []) (S3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (S))
  q15 : Eqn
  q15 = eqn (CX21 ∷ S3 ∷ []) (S3 ∷ CX21 ∷ []) (low₃-comm ((CX₁₀ ↑)) (S))
  q16 : Eqn
  q16 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q17 : Eqn
  q17 = eqn (CK31 ∷ X2 ∷ []) (X2 ∷ CK31 ∷ []) (wn 630 W)
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q19 : Eqn
  q19 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))

-- Bar(SSSKSS;2,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,1->0) part1: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part1 : ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ X2 ∷ CX21 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ X2 ∷ Sw01 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CX32 ∷ Sw12 ∷ Sw23 ∷ X2 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part1 = derive (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ X2 ∷ CX21 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ X2 ∷ Sw01 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CX32 ∷ Sw12 ∷ Sw23 ∷ X2 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  (re 45 3 (CS13 ∷ []) ∷
   rw 45 q1 ∷
   rw 44 q2 ∷
   re 46 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 45 q3 ∷
   rw 46 q4 ∷
   rw 47 q3 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 46 q5 ∷
   rw 41 q6 ∷
   rw 42 q7 ∷
   rw⁻ 41 q2 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q3 ∷
   rw 41 q8 ∷
   rw⁻ 40 q3 ∷
   re 41 3 (CS13 ∷ []) ∷
   rw 41 q1 ∷
   rw 40 q2 ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 41 q3 ∷
   rw 42 q4 ∷
   rw 43 q3 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 42 q5 ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q9 ∷
   re 45 3 (CX31 ∷ []) ∷
   rw 44 q10 ∷
   rw 43 q11 ∷
   rw 42 q12 ∷
   re 42 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 41 q13 ∷
   re 42 5 (CS03 ∷ []) ∷
   rw 44 q7 ∷
   rw⁻ 43 q2 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q3 ∷
   rw 43 q8 ∷
   rw⁻ 42 q3 ∷
   re 43 3 (CS13 ∷ []) ∷
   rw 43 q1 ∷
   rw 42 q2 ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q3 ∷
   rw 44 q4 ∷
   rw 45 q3 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 44 q5 ∷
   rw 41 q7 ∷
   rw⁻ 40 q2 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q3 ∷
   rw 40 q8 ∷
   rw⁻ 39 q3 ∷
   re 40 3 (CS13 ∷ []) ∷
   rw 40 q1 ∷
   rw 39 q2 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q3 ∷
   rw 41 q4 ∷
   rw 42 q3 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q5 ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q9 ∷
   re 44 3 (CX31 ∷ []) ∷
   rw 43 q10 ∷
   rw 42 q11 ∷
   rw 41 q12 ∷
   re 41 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 40 q13 ∷
   re 41 5 (CS03 ∷ []) ∷
   rw 43 q7 ∷
   rw⁻ 42 q2 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q3 ∷
   rw 42 q8 ∷
   rw⁻ 41 q3 ∷
   re 42 3 (CS13 ∷ []) ∷
   rw 42 q1 ∷
   rw 41 q2 ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q3 ∷
   rw 43 q4 ∷
   rw 44 q3 ∷
   re 42 3 (CS03 ∷ []) ∷
   rw 43 q5 ∷
   rw 40 q7 ∷
   rw⁻ 39 q2 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q3 ∷
   rw 39 q8 ∷
   rw⁻ 38 q3 ∷
   re 39 3 (CS13 ∷ []) ∷
   rw 39 q1 ∷
   rw 38 q2 ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q3 ∷
   rw 40 q4 ∷
   rw 41 q3 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 40 q5 ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q9 ∷
   re 43 3 (CX31 ∷ []) ∷
   rw 42 q10 ∷
   rw 41 q11 ∷
   rw 40 q12 ∷
   re 40 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 39 q13 ∷
   re 40 5 (CS03 ∷ []) ∷
   rw 42 q7 ∷
   rw⁻ 41 q2 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q3 ∷
   rw 41 q8 ∷
   rw⁻ 40 q3 ∷
   re 41 3 (CS13 ∷ []) ∷
   rw 41 q1 ∷
   rw 40 q2 ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 41 q3 ∷
   rw 42 q4 ∷
   rw 43 q3 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 42 q5 ∷
   rw 39 q7 ∷
   rw⁻ 38 q2 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q3 ∷
   rw 38 q8 ∷
   rw⁻ 37 q3 ∷
   re 38 3 (CS13 ∷ []) ∷
   rw 38 q1 ∷
   rw 37 q2 ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q3 ∷
   rw 39 q4 ∷
   rw 40 q3 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 39 q5 ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q9 ∷
   re 42 3 (CX31 ∷ []) ∷
   rw 41 q10 ∷
   rw 40 q11 ∷
   rw 39 q12 ∷
   re 39 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 38 q13 ∷
   re 39 5 (CS03 ∷ []) ∷
   rw 41 q7 ∷
   rw⁻ 40 q2 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q3 ∷
   rw 40 q8 ∷
   rw⁻ 39 q3 ∷
   re 40 3 (CS13 ∷ []) ∷
   rw 40 q1 ∷
   rw 39 q2 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q3 ∷
   rw 41 q4 ∷
   rw 42 q3 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q5 ∷
   rw 38 q7 ∷
   rw⁻ 37 q2 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q3 ∷
   rw 37 q8 ∷
   rw⁻ 36 q3 ∷
   re 37 3 (CS13 ∷ []) ∷
   rw 37 q1 ∷
   rw 36 q2 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q3 ∷
   rw 38 q4 ∷
   rw 39 q3 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 38 q5 ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q9 ∷
   re 41 3 (CX31 ∷ []) ∷
   rw 40 q10 ∷
   rw 39 q11 ∷
   rw 38 q12 ∷
   re 38 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 37 q13 ∷
   re 38 5 (CS03 ∷ []) ∷
   rw 40 q7 ∷
   rw⁻ 39 q2 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q3 ∷
   rw 39 q8 ∷
   rw⁻ 38 q3 ∷
   re 39 3 (CS13 ∷ []) ∷
   rw 39 q1 ∷
   rw 38 q2 ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q3 ∷
   rw 40 q4 ∷
   rw 41 q3 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 40 q5 ∷
   rw 37 q7 ∷
   rw⁻ 36 q2 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q3 ∷
   rw 36 q8 ∷
   rw⁻ 35 q3 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 36 q1 ∷
   rw 35 q2 ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q3 ∷
   rw 37 q4 ∷
   rw 38 q3 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q5 ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q9 ∷
   re 40 3 (CX31 ∷ []) ∷
   rw 39 q10 ∷
   rw 38 q11 ∷
   rw 37 q12 ∷
   re 37 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 36 q13 ∷
   re 37 5 (CS03 ∷ []) ∷
   rw 39 q7 ∷
   rw⁻ 38 q2 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q3 ∷
   rw 38 q8 ∷
   rw⁻ 37 q3 ∷
   re 38 3 (CS13 ∷ []) ∷
   rw 38 q1 ∷
   rw 37 q2 ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q3 ∷
   rw 39 q4 ∷
   rw 40 q3 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 39 q5 ∷
   rw 36 q7 ∷
   rw⁻ 35 q2 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q3 ∷
   rw 35 q8 ∷
   rw⁻ 34 q3 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw 35 q1 ∷
   rw 34 q2 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q3 ∷
   rw 36 q4 ∷
   rw 37 q3 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q5 ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q9 ∷
   re 39 3 (CX31 ∷ []) ∷
   rw 38 q10 ∷
   rw 37 q11 ∷
   rw 36 q12 ∷
   re 36 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 35 q13 ∷
   re 36 5 (CS03 ∷ []) ∷
   rw 38 q7 ∷
   rw⁻ 37 q2 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q3 ∷
   rw 37 q8 ∷
   rw⁻ 36 q3 ∷
   re 37 3 (CS13 ∷ []) ∷
   rw 37 q1 ∷
   rw 36 q2 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q3 ∷
   rw 38 q4 ∷
   rw 39 q3 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 38 q5 ∷
   rw 35 q7 ∷
   rw⁻ 34 q2 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q3 ∷
   rw 34 q8 ∷
   rw⁻ 33 q3 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw 34 q1 ∷
   rw 33 q2 ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q3 ∷
   rw 35 q4 ∷
   rw 36 q3 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 35 q5 ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q9 ∷
   re 38 3 (CX31 ∷ []) ∷
   rw 37 q10 ∷
   rw 36 q11 ∷
   rw 35 q12 ∷
   re 35 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 34 q13 ∷
   re 35 5 (CS03 ∷ []) ∷
   rw 37 q7 ∷
   rw⁻ 36 q2 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q3 ∷
   rw 36 q8 ∷
   rw⁻ 35 q3 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 36 q1 ∷
   rw 35 q2 ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q3 ∷
   rw 37 q4 ∷
   rw 38 q3 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q5 ∷
   rw 34 q7 ∷
   rw⁻ 33 q2 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q3 ∷
   rw 33 q8 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw 33 q1 ∷
   rw 32 q2 ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q3 ∷
   rw 34 q4 ∷
   rw 35 q3 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 34 q5 ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q9 ∷
   re 37 3 (CX31 ∷ []) ∷
   rw 36 q10 ∷
   rw 35 q11 ∷
   rw 34 q12 ∷
   re 34 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 33 q13 ∷
   re 34 5 (CS03 ∷ []) ∷
   rw 36 q7 ∷
   rw⁻ 35 q2 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q3 ∷
   rw 35 q8 ∷
   rw⁻ 34 q3 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw 35 q1 ∷
   rw 34 q2 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q3 ∷
   rw 36 q4 ∷
   rw 37 q3 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q5 ∷
   rw⁻ 31 q14 ∷
   rw⁻ 32 q15 ∷
   rw⁻ 33 q14 ∷
   rw 32 q7 ∷
   rw⁻ 31 q2 ∷
   re 30 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q3 ∷
   rw 31 q16 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (CK31 ∷ []) ∷
   rw 31 q17 ∷
   rw 30 q2 ∷
   re 32 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 31 q3 ∷
   rw 32 q18 ∷
   rw 33 q3 ∷
   re 31 3 (CK30 ∷ []) ∷
   rw 32 q5 ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q9 ∷
   re 35 3 (CX31 ∷ []) ∷
   rw 34 q10 ∷
   rw 33 q19 ∷
   rw 32 q12 ∷
   re 32 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 31 q13 ∷
   re 32 5 (CK30 ∷ []) ∷
   rw 34 q7 ∷
   rw⁻ 33 q2 ∷
   re 32 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q3 ∷
   rw 33 q16 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (CK31 ∷ []) ∷
   rw 33 q17 ∷
   rw 32 q2 ∷
   re 34 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 33 q3 ∷
   rw 34 q18 ∷
   rw 35 q3 ∷
   re 33 3 (CK30 ∷ []) ∷
   rw 34 q5 ∷
   rw 31 q7 ∷
   rw⁻ 30 q2 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q3 ∷
   rw 30 q8 ∷
   rw⁻ 29 q3 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw 30 q1 ∷
   rw 29 q2 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q3 ∷
   rw 31 q4 ∷
   rw 32 q3 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 31 q5 ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q9 ∷
   re 34 3 (CX31 ∷ []) ∷
   rw 33 q10 ∷
   rw 32 q11 ∷
   rw 31 q12 ∷
   re 31 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 30 q13 ∷
   re 31 5 (CS03 ∷ []) ∷
   rw 33 q7 ∷
   rw⁻ 32 q2 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q3 ∷
   rw 32 q8 ∷
   rw⁻ 31 q3 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw 32 q1 ∷
   rw 31 q2 ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q3 ∷
   rw 33 q4 ∷
   rw 34 q3 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 33 q5 ∷
   rw 30 q7 ∷
   rw⁻ 29 q2 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q3 ∷
   rw 29 q8 ∷
   rw⁻ 28 q3 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 29 q1 ∷
   rw 28 q2 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q3 ∷
   rw 30 q4 ∷
   rw 31 q3 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 30 q5 ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q9 ∷
   re 33 3 (CX31 ∷ []) ∷
   rw 32 q10 ∷
   rw 31 q11 ∷
   rw 30 q12 ∷
   re 30 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 29 q13 ∷
   re 30 5 (CS03 ∷ []) ∷
   rw 32 q7 ∷
   rw⁻ 31 q2 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q3 ∷
   rw 31 q8 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 31 q1 ∷
   rw 30 q2 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q3 ∷
   rw 32 q4 ∷
   rw 33 q3 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 32 q5 ∷
   rw 29 q7 ∷
   rw⁻ 28 q2 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q3 ∷
   rw 28 q8 ∷
   rw⁻ 27 q3 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 28 q1 ∷
   rw 27 q2 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q3 ∷
   rw 29 q4 ∷
   rw 30 q3 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 29 q5 ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q9 ∷
   re 32 3 (CX31 ∷ []) ∷
   rw 31 q10 ∷ []) Eq.refl

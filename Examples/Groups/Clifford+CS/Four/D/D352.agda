{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D352 (W : Ws) where

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
  q3 = wE 629 W
  q4 : Eqn
  q4 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q5 : Eqn
  q5 = wE 27 W
  q6 : Eqn
  q6 = wE 31 W
  q7 : Eqn
  q7 = wE 5 W
  q8 : Eqn
  q8 = wE 1 W
  q9 : Eqn
  q9 = wE 113 W
  q10 : Eqn
  q10 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q11 : Eqn
  q11 = wE 114 W
  q12 : Eqn
  q12 = wE 3 W
  q13 : Eqn
  q13 = eqn (X2 ∷ S3 ∷ []) (S3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (S))
  q14 : Eqn
  q14 = eqn (CX21 ∷ S3 ∷ []) (S3 ∷ CX21 ∷ []) (low₃-comm ((CX₁₀ ↑)) (S))
  q15 : Eqn
  q15 = wE 140 W
  q16 : Eqn
  q16 = wE 630 W
  q17 : Eqn
  q17 = wE 142 W
  q18 : Eqn
  q18 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q19 : Eqn
  q19 = wE 673 W
  q20 : Eqn
  q20 = wE 488 W
  q21 : Eqn
  q21 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q22 : Eqn
  q22 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q23 : Eqn
  q23 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))

-- Bar(SSKSKK;2,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,1->0) part1: 500 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part1 : ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ CS03 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ Sw23 ∷ CK20 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ Sw23 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part1 = derive (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ CS03 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ Sw23 ∷ CK20 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ Sw23 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  (re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q1 ∷
   rw 41 q2 ∷
   rw⁻ 40 q1 ∷
   re 41 3 (CS13 ∷ []) ∷
   rw 41 q3 ∷
   rw 40 q4 ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   rw 42 q5 ∷
   rw 43 q1 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 42 q6 ∷
   rw 39 q7 ∷
   rw⁻ 38 q4 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q1 ∷
   rw 38 q2 ∷
   rw⁻ 37 q1 ∷
   re 38 3 (CS13 ∷ []) ∷
   rw 38 q3 ∷
   rw 37 q4 ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q1 ∷
   rw 39 q5 ∷
   rw 40 q1 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 39 q6 ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q8 ∷
   re 42 3 (CX31 ∷ []) ∷
   rw 41 q9 ∷
   rw 40 q10 ∷
   rw 39 q11 ∷
   re 39 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 38 q12 ∷
   re 39 5 (CS03 ∷ []) ∷
   rw 41 q7 ∷
   rw⁻ 40 q4 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q1 ∷
   rw 40 q2 ∷
   rw⁻ 39 q1 ∷
   re 40 3 (CS13 ∷ []) ∷
   rw 40 q3 ∷
   rw 39 q4 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   rw 41 q5 ∷
   rw 42 q1 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q6 ∷
   rw 38 q7 ∷
   rw⁻ 37 q4 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q1 ∷
   rw 37 q2 ∷
   rw⁻ 36 q1 ∷
   re 37 3 (CS13 ∷ []) ∷
   rw 37 q3 ∷
   rw 36 q4 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q1 ∷
   rw 38 q5 ∷
   rw 39 q1 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 38 q6 ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q8 ∷
   re 41 3 (CX31 ∷ []) ∷
   rw 40 q9 ∷
   rw 39 q10 ∷
   rw 38 q11 ∷
   re 38 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 37 q12 ∷
   re 38 5 (CS03 ∷ []) ∷
   rw 40 q7 ∷
   rw⁻ 39 q4 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q1 ∷
   rw 39 q2 ∷
   rw⁻ 38 q1 ∷
   re 39 3 (CS13 ∷ []) ∷
   rw 39 q3 ∷
   rw 38 q4 ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q1 ∷
   rw 40 q5 ∷
   rw 41 q1 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 40 q6 ∷
   rw 37 q7 ∷
   rw⁻ 36 q4 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q1 ∷
   rw 36 q2 ∷
   rw⁻ 35 q1 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 36 q3 ∷
   rw 35 q4 ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
   rw 37 q5 ∷
   rw 38 q1 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q6 ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q8 ∷
   re 40 3 (CX31 ∷ []) ∷
   rw 39 q9 ∷
   rw 38 q10 ∷
   rw 37 q11 ∷
   re 37 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 36 q12 ∷
   re 37 5 (CS03 ∷ []) ∷
   rw 39 q7 ∷
   rw⁻ 38 q4 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q1 ∷
   rw 38 q2 ∷
   rw⁻ 37 q1 ∷
   re 38 3 (CS13 ∷ []) ∷
   rw 38 q3 ∷
   rw 37 q4 ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q1 ∷
   rw 39 q5 ∷
   rw 40 q1 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 39 q6 ∷
   rw 36 q7 ∷
   rw⁻ 35 q4 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q1 ∷
   rw 35 q2 ∷
   rw⁻ 34 q1 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw 35 q3 ∷
   rw 34 q4 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   rw 36 q5 ∷
   rw 37 q1 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q6 ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q8 ∷
   re 39 3 (CX31 ∷ []) ∷
   rw 38 q9 ∷
   rw 37 q10 ∷
   rw 36 q11 ∷
   re 36 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 35 q12 ∷
   re 36 5 (CS03 ∷ []) ∷
   rw 38 q7 ∷
   rw⁻ 37 q4 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q1 ∷
   rw 37 q2 ∷
   rw⁻ 36 q1 ∷
   re 37 3 (CS13 ∷ []) ∷
   rw 37 q3 ∷
   rw 36 q4 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q1 ∷
   rw 38 q5 ∷
   rw 39 q1 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 38 q6 ∷
   rw 35 q7 ∷
   rw⁻ 34 q4 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q1 ∷
   rw 34 q2 ∷
   rw⁻ 33 q1 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw 34 q3 ∷
   rw 33 q4 ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   rw 35 q5 ∷
   rw 36 q1 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 35 q6 ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q8 ∷
   re 38 3 (CX31 ∷ []) ∷
   rw 37 q9 ∷
   rw 36 q10 ∷
   rw 35 q11 ∷
   re 35 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 34 q12 ∷
   re 35 5 (CS03 ∷ []) ∷
   rw 37 q7 ∷
   rw⁻ 36 q4 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q1 ∷
   rw 36 q2 ∷
   rw⁻ 35 q1 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 36 q3 ∷
   rw 35 q4 ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
   rw 37 q5 ∷
   rw 38 q1 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q6 ∷
   rw⁻ 32 q13 ∷
   rw⁻ 33 q14 ∷
   rw⁻ 34 q13 ∷
   rw 33 q7 ∷
   rw⁻ 32 q4 ∷
   re 31 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q1 ∷
   rw 32 q15 ∷
   rw⁻ 31 q1 ∷
   re 32 3 (CK31 ∷ []) ∷
   rw 32 q16 ∷
   rw 31 q4 ∷
   re 33 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   rw 33 q17 ∷
   rw 34 q1 ∷
   re 32 3 (CK30 ∷ []) ∷
   rw 33 q6 ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q8 ∷
   re 36 3 (CX31 ∷ []) ∷
   rw 35 q9 ∷
   rw 34 q18 ∷
   rw 33 q11 ∷
   re 33 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 32 q12 ∷
   re 33 5 (CK30 ∷ []) ∷
   rw 35 q7 ∷
   rw⁻ 34 q4 ∷
   re 33 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q1 ∷
   rw 34 q15 ∷
   rw⁻ 33 q1 ∷
   re 34 3 (CK31 ∷ []) ∷
   rw 34 q16 ∷
   rw 33 q4 ∷
   re 35 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   rw 35 q17 ∷
   rw 36 q1 ∷
   re 34 3 (CK30 ∷ []) ∷
   rw 35 q6 ∷
   rw 32 q7 ∷
   rw⁻ 31 q4 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q1 ∷
   rw 31 q2 ∷
   rw⁻ 30 q1 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 31 q3 ∷
   rw 30 q4 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   rw 32 q5 ∷
   rw 33 q1 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 32 q6 ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q8 ∷
   re 35 3 (CX31 ∷ []) ∷
   rw 34 q9 ∷
   rw 33 q10 ∷
   rw 32 q11 ∷
   re 32 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 31 q12 ∷
   re 32 5 (CS03 ∷ []) ∷
   rw 34 q7 ∷
   rw⁻ 33 q4 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q1 ∷
   rw 33 q2 ∷
   rw⁻ 32 q1 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   rw 34 q5 ∷
   rw 35 q1 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 34 q6 ∷
   rw 31 q7 ∷
   rw⁻ 30 q4 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q1 ∷
   rw 30 q2 ∷
   rw⁻ 29 q1 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   rw 31 q5 ∷
   rw 32 q1 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 31 q6 ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q8 ∷
   re 34 3 (CX31 ∷ []) ∷
   rw 33 q9 ∷
   rw 32 q10 ∷
   rw 31 q11 ∷
   re 31 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 30 q12 ∷
   re 31 5 (CS03 ∷ []) ∷
   rw 33 q7 ∷
   rw⁻ 32 q4 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q1 ∷
   rw 32 q2 ∷
   rw⁻ 31 q1 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   rw 33 q5 ∷
   rw 34 q1 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 33 q6 ∷
   rw 30 q7 ∷
   rw⁻ 29 q4 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q1 ∷
   rw 29 q2 ∷
   rw⁻ 28 q1 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 29 q3 ∷
   rw 28 q4 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   rw 30 q5 ∷
   rw 31 q1 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 30 q6 ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q8 ∷
   re 33 3 (CX31 ∷ []) ∷
   rw 32 q9 ∷
   rw 31 q10 ∷
   rw 30 q11 ∷
   re 30 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 29 q12 ∷
   re 30 5 (CS03 ∷ []) ∷
   rw 32 q7 ∷
   rw⁻ 31 q4 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q1 ∷
   rw 31 q2 ∷
   rw⁻ 30 q1 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 31 q3 ∷
   rw 30 q4 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   rw 32 q5 ∷
   rw 33 q1 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 32 q6 ∷
   rw⁻ 27 q13 ∷
   rw⁻ 28 q14 ∷
   rw⁻ 29 q13 ∷
   rw 28 q7 ∷
   rw⁻ 27 q4 ∷
   re 26 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q1 ∷
   rw 27 q15 ∷
   rw⁻ 26 q1 ∷
   re 27 3 (CK31 ∷ []) ∷
   rw 27 q16 ∷
   rw 26 q4 ∷
   re 28 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   rw 28 q17 ∷
   rw 29 q1 ∷
   re 27 3 (CK30 ∷ []) ∷
   rw 28 q6 ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q8 ∷
   re 31 3 (CX31 ∷ []) ∷
   rw 30 q9 ∷
   rw 29 q18 ∷
   rw 28 q11 ∷
   re 28 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 27 q12 ∷
   re 28 5 (CK30 ∷ []) ∷
   rw 30 q7 ∷
   rw⁻ 29 q4 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q1 ∷
   rw 29 q15 ∷
   rw⁻ 28 q1 ∷
   re 29 3 (CK31 ∷ []) ∷
   rw 29 q16 ∷
   rw 28 q4 ∷
   re 30 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   rw 30 q17 ∷
   rw 31 q1 ∷
   re 29 3 (CK30 ∷ []) ∷
   rw 30 q6 ∷
   rw⁻ 25 q13 ∷
   rw⁻ 26 q14 ∷
   rw⁻ 27 q13 ∷
   rw 26 q7 ∷
   rw⁻ 25 q4 ∷
   re 24 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q1 ∷
   rw 25 q15 ∷
   rw⁻ 24 q1 ∷
   re 25 3 (CK31 ∷ []) ∷
   rw 25 q16 ∷
   rw 24 q4 ∷
   re 26 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   rw 26 q17 ∷
   rw 27 q1 ∷
   re 25 3 (CK30 ∷ []) ∷
   rw 26 q6 ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q8 ∷
   re 29 3 (CX31 ∷ []) ∷
   rw 28 q9 ∷
   rw 27 q18 ∷
   rw 26 q11 ∷
   re 26 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 25 q12 ∷
   re 26 5 (CK30 ∷ []) ∷
   rw 28 q7 ∷
   rw⁻ 27 q4 ∷
   re 26 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q1 ∷
   rw 27 q15 ∷
   rw⁻ 26 q1 ∷
   re 27 3 (CK31 ∷ []) ∷
   rw 27 q16 ∷
   rw 26 q4 ∷
   re 28 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   rw 28 q17 ∷
   rw 29 q1 ∷
   re 27 3 (CK30 ∷ []) ∷
   rw 28 q6 ∷
   rw 23 q19 ∷
   rw 17 q20 ∷
   rw 91 q8 ∷
   rw 90 q21 ∷
   rw 89 q22 ∷
   rw 88 q21 ∷
   rw 87 q21 ∷
   rw 86 q21 ∷
   rw 85 q21 ∷
   rw 84 q22 ∷
   rw 83 q21 ∷
   rw 82 q21 ∷
   rw 81 q21 ∷
   rw 80 q23 ∷
   rw 79 q23 ∷
   rw 78 q23 ∷
   rw 77 q23 ∷
   rw 76 q23 ∷
   rw 75 q23 ∷
   rw 74 q23 ∷
   rw 73 q23 ∷
   rw 72 q23 ∷
   rw 71 q21 ∷
   rw 70 q22 ∷
   rw 69 q21 ∷
   rw 68 q21 ∷
   rw 67 q21 ∷
   rw 66 q23 ∷
   rw 65 q23 ∷
   rw 64 q23 ∷
   rw 63 q23 ∷
   rw 62 q23 ∷
   rw 61 q23 ∷
   rw 60 q23 ∷
   rw 59 q23 ∷
   rw 58 q23 ∷
   rw 57 q23 ∷
   rw 56 q23 ∷
   rw 55 q23 ∷
   rw 54 q23 ∷
   rw 53 q23 ∷
   rw 52 q23 ∷
   rw 51 q23 ∷
   rw 50 q23 ∷
   rw 49 q23 ∷
   re 48 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 50 q12 ∷
   re 47 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 49 q12 ∷ []) Eq.refl

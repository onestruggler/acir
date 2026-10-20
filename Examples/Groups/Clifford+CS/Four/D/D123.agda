{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D123 (W : Ws) where

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
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q3 : Eqn
  q3 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q4 : Eqn
  q4 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q5 : Eqn
  q5 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q8 : Eqn
  q8 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) (wn 677 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q12 : Eqn
  q12 = eqn (CK31 ∷ X2 ∷ []) (X2 ∷ CK31 ∷ []) (wn 630 W)
  q13 : Eqn
  q13 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q14 : Eqn
  q14 = eqn (Sw12 ∷ CX31 ∷ []) (CX32 ∷ Sw12 ∷ []) (wn 113 W)
  q15 : Eqn
  q15 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q16 : Eqn
  q16 = eqn (Sw12 ∷ CX32 ∷ []) (CX31 ∷ Sw12 ∷ []) (wn 114 W)
  q17 : Eqn
  q17 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q18 : Eqn
  q18 = eqn (CS13 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ []) (wn 629 W)
  q19 : Eqn
  q19 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q20 : Eqn
  q20 = eqn (CX23 ∷ X2 ∷ CX21 ∷ X2 ∷ []) (X2 ∷ CX21 ∷ X2 ∷ CX23 ∷ []) (wn 673 W)

-- Bar(SSKSKK;2,3->0) passes groups of WBar(SSSKSS;~2,1->0) part0: 500 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨SSSKSS~21-⟶0⟩-part0 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ X2 ∷ Sw01 ∷ CX21 ∷ X2 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨SSSKSS~21-⟶0⟩-part0 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ X2 ∷ Sw01 ∷ CX21 ∷ X2 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 37 q1 ∷
   rw⁻ 36 q2 ∷
   rw 35 q3 ∷
   rw 34 q3 ∷
   rw 33 q4 ∷
   rw 32 q3 ∷
   rw 31 q3 ∷
   rw 30 q3 ∷
   rw⁻ 29 q2 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q5 ∷
   rw 29 q4 ∷
   rw⁻ 28 q5 ∷
   re 29 3 (CK31 ∷ []) ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q5 ∷
   rw 28 q4 ∷
   rw⁻ 27 q5 ∷
   re 28 3 (CK31 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q5 ∷
   rw 27 q3 ∷
   rw⁻ 26 q5 ∷
   re 27 3 (CS13 ∷ []) ∷
   re 25 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q5 ∷
   rw 26 q4 ∷
   rw⁻ 25 q5 ∷
   re 26 3 (CK31 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q5 ∷
   rw 25 q3 ∷
   rw⁻ 24 q5 ∷
   re 25 3 (CS13 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q5 ∷
   rw 24 q3 ∷
   rw⁻ 23 q5 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw⁻ 22 q6 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q5 ∷
   rw 22 q3 ∷
   rw⁻ 21 q5 ∷
   re 22 3 (CS13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q5 ∷
   rw 21 q3 ∷
   rw⁻ 20 q5 ∷
   re 21 3 (CS13 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q5 ∷
   rw 20 q3 ∷
   rw⁻ 19 q5 ∷
   re 20 3 (CS13 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q5 ∷
   rw 19 q3 ∷
   rw⁻ 18 q5 ∷
   re 19 3 (CS13 ∷ []) ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q5 ∷
   rw 18 q3 ∷
   rw⁻ 17 q5 ∷
   re 18 3 (CS13 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q5 ∷
   rw 17 q3 ∷
   rw⁻ 16 q5 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw⁻ 15 q7 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q5 ∷
   rw 15 q4 ∷
   rw⁻ 14 q5 ∷
   re 15 3 (CK31 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q5 ∷
   rw 14 q3 ∷
   rw⁻ 13 q5 ∷
   re 14 3 (CS13 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q5 ∷
   rw 13 q3 ∷
   rw⁻ 12 q5 ∷
   re 13 3 (CS13 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q5 ∷
   rw 12 q3 ∷
   rw⁻ 11 q5 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw⁻ 10 q7 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q5 ∷
   rw 10 q4 ∷
   rw⁻ 9 q5 ∷
   re 10 3 (CK31 ∷ []) ∷
   rw⁻ 8 q7 ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q5 ∷
   rw 8 q4 ∷
   rw⁻ 7 q5 ∷
   re 8 3 (CK31 ∷ []) ∷
   rw⁻ 6 q6 ∷
   rw 5 q4 ∷
   rw 4 q4 ∷
   rw 3 q3 ∷
   rw 2 q4 ∷
   rw 1 q3 ∷
   rw 0 q3 ∷
   rw 1 q8 ∷
   rw 0 q2 ∷
   rw 1 q9 ∷
   rw 2 q9 ∷
   rw 3 q9 ∷
   rw 4 q10 ∷
   rw 5 q9 ∷
   rw 6 q9 ∷
   rw 7 q2 ∷
   rw 8 q9 ∷
   rw 9 q9 ∷
   rw 10 q10 ∷
   rw 11 q9 ∷
   rw 12 q10 ∷
   rw 13 q10 ∷
   rw 14 q6 ∷
   re 16 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   rw 16 q10 ∷
   rw 17 q5 ∷
   re 15 3 (CK30 ∷ []) ∷
   rw 16 q7 ∷
   re 18 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   rw 18 q10 ∷
   rw 19 q5 ∷
   re 17 3 (CK30 ∷ []) ∷
   rw 18 q7 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q5 ∷
   rw 20 q9 ∷
   rw 21 q5 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q5 ∷
   rw 21 q9 ∷
   rw 22 q5 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q5 ∷
   rw 22 q9 ∷
   rw 23 q5 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 22 q5 ∷
   rw 23 q10 ∷
   rw 24 q5 ∷
   re 22 3 (CK30 ∷ []) ∷
   rw 23 q7 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q5 ∷
   rw 25 q9 ∷
   rw 26 q5 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q5 ∷
   rw 26 q9 ∷
   rw 27 q5 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q5 ∷
   rw 27 q9 ∷
   rw 28 q5 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q5 ∷
   rw 28 q9 ∷
   rw 29 q5 ∷
   re 27 3 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q5 ∷
   rw 29 q9 ∷
   rw 30 q5 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q5 ∷
   rw 30 q9 ∷
   rw 31 q5 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 30 q6 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q5 ∷
   rw 32 q9 ∷
   rw 33 q5 ∷
   re 31 3 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q5 ∷
   rw 33 q9 ∷
   rw 34 q5 ∷
   re 32 3 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 33 q5 ∷
   rw 34 q10 ∷
   rw 35 q5 ∷
   re 33 3 (CK30 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q5 ∷
   rw 35 q9 ∷
   rw 36 q5 ∷
   re 34 3 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 35 q5 ∷
   rw 36 q10 ∷
   rw 37 q5 ∷
   re 35 3 (CK30 ∷ []) ∷
   re 37 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 36 q5 ∷
   rw 37 q10 ∷
   rw 38 q5 ∷
   re 36 3 (CK30 ∷ []) ∷
   rw 37 q11 ∷
   rw 38 q1 ∷
   rw⁻ 37 q2 ∷
   re 36 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q5 ∷
   rw 37 q4 ∷
   rw⁻ 36 q5 ∷
   re 37 3 (CK31 ∷ []) ∷
   rw 37 q12 ∷
   rw 36 q2 ∷
   re 38 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 37 q5 ∷
   rw 38 q10 ∷
   rw 39 q5 ∷
   re 37 3 (CK30 ∷ []) ∷
   rw 38 q11 ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q13 ∷
   re 41 3 (CX31 ∷ []) ∷
   rw 40 q14 ∷
   rw 39 q15 ∷
   rw 38 q16 ∷
   re 38 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 37 q17 ∷
   re 38 5 (CK30 ∷ []) ∷
   rw 40 q1 ∷
   rw⁻ 39 q2 ∷
   re 38 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q5 ∷
   rw 39 q4 ∷
   rw⁻ 38 q5 ∷
   re 39 3 (CK31 ∷ []) ∷
   rw 39 q12 ∷
   rw 38 q2 ∷
   re 40 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 39 q5 ∷
   rw 40 q10 ∷
   rw 41 q5 ∷
   re 39 3 (CK30 ∷ []) ∷
   rw 40 q11 ∷
   rw 37 q1 ∷
   rw⁻ 36 q2 ∷
   re 35 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q5 ∷
   rw 36 q4 ∷
   rw⁻ 35 q5 ∷
   re 36 3 (CK31 ∷ []) ∷
   rw 36 q12 ∷
   rw 35 q2 ∷
   re 37 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 36 q5 ∷
   rw 37 q10 ∷
   rw 38 q5 ∷
   re 36 3 (CK30 ∷ []) ∷
   rw 37 q11 ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q13 ∷
   re 40 3 (CX31 ∷ []) ∷
   rw 39 q14 ∷
   rw 38 q15 ∷
   rw 37 q16 ∷
   re 37 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 36 q17 ∷
   re 37 5 (CK30 ∷ []) ∷
   rw 39 q1 ∷
   rw⁻ 38 q2 ∷
   re 37 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q5 ∷
   rw 38 q4 ∷
   rw⁻ 37 q5 ∷
   re 38 3 (CK31 ∷ []) ∷
   rw 38 q12 ∷
   rw 37 q2 ∷
   re 39 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 38 q5 ∷
   rw 39 q10 ∷
   rw 40 q5 ∷
   re 38 3 (CK30 ∷ []) ∷
   rw 39 q11 ∷
   rw 36 q1 ∷
   rw⁻ 35 q2 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q5 ∷
   rw 35 q3 ∷
   rw⁻ 34 q5 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw 35 q18 ∷
   rw 34 q2 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q5 ∷
   rw 36 q9 ∷
   rw 37 q5 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q11 ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q13 ∷
   re 39 3 (CX31 ∷ []) ∷
   rw 38 q14 ∷
   rw 37 q19 ∷
   rw 36 q16 ∷
   re 36 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 35 q17 ∷
   re 36 5 (CS03 ∷ []) ∷
   rw 38 q1 ∷
   rw⁻ 37 q2 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q5 ∷
   rw 37 q3 ∷
   rw⁻ 36 q5 ∷
   re 37 3 (CS13 ∷ []) ∷
   rw 37 q18 ∷
   rw 36 q2 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q5 ∷
   rw 38 q9 ∷
   rw 39 q5 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 38 q11 ∷
   rw 35 q1 ∷
   rw⁻ 34 q2 ∷
   re 33 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q5 ∷
   rw 34 q4 ∷
   rw⁻ 33 q5 ∷
   re 34 3 (CK31 ∷ []) ∷
   rw 34 q12 ∷
   rw 33 q2 ∷
   re 35 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 34 q5 ∷
   rw 35 q10 ∷
   rw 36 q5 ∷
   re 34 3 (CK30 ∷ []) ∷
   rw 35 q11 ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q13 ∷
   re 38 3 (CX31 ∷ []) ∷
   rw 37 q14 ∷
   rw 36 q15 ∷
   rw 35 q16 ∷
   re 35 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 34 q17 ∷
   re 35 5 (CK30 ∷ []) ∷
   rw 37 q1 ∷
   rw⁻ 36 q2 ∷
   re 35 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q5 ∷
   rw 36 q4 ∷
   rw⁻ 35 q5 ∷
   re 36 3 (CK31 ∷ []) ∷
   rw 36 q12 ∷
   rw 35 q2 ∷
   re 37 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 36 q5 ∷
   rw 37 q10 ∷
   rw 38 q5 ∷
   re 36 3 (CK30 ∷ []) ∷
   rw 37 q11 ∷
   rw 34 q1 ∷
   rw⁻ 33 q2 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q5 ∷
   rw 33 q3 ∷
   rw⁻ 32 q5 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw 33 q18 ∷
   rw 32 q2 ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q5 ∷
   rw 34 q9 ∷
   rw 35 q5 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 34 q11 ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q13 ∷
   re 37 3 (CX31 ∷ []) ∷
   rw 36 q14 ∷
   rw 35 q19 ∷
   rw 34 q16 ∷
   re 34 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 33 q17 ∷
   re 34 5 (CS03 ∷ []) ∷
   rw 36 q1 ∷
   rw⁻ 35 q2 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q5 ∷
   rw 35 q3 ∷
   rw⁻ 34 q5 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw 35 q18 ∷
   rw 34 q2 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q5 ∷
   rw 36 q9 ∷
   rw 37 q5 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q11 ∷
   rw 33 q1 ∷
   rw⁻ 32 q2 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q5 ∷
   rw 32 q3 ∷
   rw⁻ 31 q5 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw 32 q18 ∷
   rw 31 q2 ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q5 ∷
   rw 33 q9 ∷
   rw 34 q5 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 33 q11 ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q13 ∷
   re 36 3 (CX31 ∷ []) ∷
   rw 35 q14 ∷
   rw 34 q19 ∷
   rw 33 q16 ∷
   re 33 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 32 q17 ∷
   re 33 5 (CS03 ∷ []) ∷
   rw 35 q1 ∷
   rw⁻ 34 q2 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q5 ∷
   rw 34 q3 ∷
   rw⁻ 33 q5 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw 34 q18 ∷
   rw 33 q2 ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q5 ∷
   rw 35 q9 ∷
   rw 36 q5 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 35 q11 ∷
   rw 30 q20 ∷
   rw 31 q1 ∷
   rw⁻ 30 q2 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q5 ∷
   rw 30 q3 ∷
   rw⁻ 29 q5 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw 30 q18 ∷
   rw 29 q2 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q5 ∷
   rw 31 q9 ∷
   rw 32 q5 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 31 q11 ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q13 ∷
   re 34 3 (CX31 ∷ []) ∷
   rw 33 q14 ∷
   rw 32 q19 ∷
   rw 31 q16 ∷
   re 31 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 30 q17 ∷
   re 31 5 (CS03 ∷ []) ∷
   rw 33 q1 ∷
   rw⁻ 32 q2 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q5 ∷
   rw 32 q3 ∷
   rw⁻ 31 q5 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw 32 q18 ∷
   rw 31 q2 ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q5 ∷
   rw 33 q9 ∷
   rw 34 q5 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 33 q11 ∷
   rw 30 q1 ∷
   rw⁻ 29 q2 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q5 ∷
   rw 29 q3 ∷ []) Eq.refl

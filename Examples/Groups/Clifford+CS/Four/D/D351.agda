{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D351 (W : Ws) where

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
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q3 : Eqn
  q3 = wE 7 W
  q4 : Eqn
  q4 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q5 : Eqn
  q5 = wE 140 W
  q6 : Eqn
  q6 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q8 : Eqn
  q8 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q9 : Eqn
  q9 = wE 967 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = wE 27 W
  q12 : Eqn
  q12 = wE 31 W
  q13 : Eqn
  q13 = wE 630 W
  q14 : Eqn
  q14 = wE 1 W
  q15 : Eqn
  q15 = wE 113 W
  q16 : Eqn
  q16 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q17 : Eqn
  q17 = wE 114 W
  q18 : Eqn
  q18 = wE 3 W
  q19 : Eqn
  q19 = wE 629 W
  q20 : Eqn
  q20 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q21 : Eqn
  q21 = wE 673 W

-- Bar(SSKSKK;2,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,1->0) part0: 500 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part0 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ CS03 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part0 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ CS03 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  (rw 46 q1 ∷
   rw⁻ 45 q2 ∷
   rw 44 q3 ∷
   rw 43 q3 ∷
   rw 42 q3 ∷
   rw 41 q3 ∷
   rw 40 q3 ∷
   rw 39 q3 ∷
   rw⁻ 38 q4 ∷
   rw 37 q5 ∷
   rw 36 q3 ∷
   rw 35 q3 ∷
   rw 34 q3 ∷
   rw⁻ 33 q4 ∷
   rw 32 q5 ∷
   rw⁻ 31 q4 ∷
   rw 30 q5 ∷
   rw⁻ 29 q2 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q6 ∷
   rw 29 q5 ∷
   rw⁻ 28 q6 ∷
   re 29 3 (CK31 ∷ []) ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q6 ∷
   rw 28 q5 ∷
   rw⁻ 27 q6 ∷
   re 28 3 (CK31 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q6 ∷
   rw 27 q3 ∷
   rw⁻ 26 q6 ∷
   re 27 3 (CS13 ∷ []) ∷
   re 25 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q6 ∷
   rw 26 q5 ∷
   rw⁻ 25 q6 ∷
   re 26 3 (CK31 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q6 ∷
   rw 25 q3 ∷
   rw⁻ 24 q6 ∷
   re 25 3 (CS13 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q6 ∷
   rw 24 q3 ∷
   rw⁻ 23 q6 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw⁻ 22 q7 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q6 ∷
   rw 22 q3 ∷
   rw⁻ 21 q6 ∷
   re 22 3 (CS13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q6 ∷
   rw 21 q3 ∷
   rw⁻ 20 q6 ∷
   re 21 3 (CS13 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q6 ∷
   rw 20 q3 ∷
   rw⁻ 19 q6 ∷
   re 20 3 (CS13 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q6 ∷
   rw 19 q3 ∷
   rw⁻ 18 q6 ∷
   re 19 3 (CS13 ∷ []) ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q6 ∷
   rw 18 q3 ∷
   rw⁻ 17 q6 ∷
   re 18 3 (CS13 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q6 ∷
   rw 17 q3 ∷
   rw⁻ 16 q6 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw⁻ 15 q8 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q6 ∷
   rw 15 q5 ∷
   rw⁻ 14 q6 ∷
   re 15 3 (CK31 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q6 ∷
   rw 14 q3 ∷
   rw⁻ 13 q6 ∷
   re 14 3 (CS13 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q6 ∷
   rw 13 q3 ∷
   rw⁻ 12 q6 ∷
   re 13 3 (CS13 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q6 ∷
   rw 12 q3 ∷
   rw⁻ 11 q6 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw⁻ 10 q8 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q6 ∷
   rw 10 q5 ∷
   rw⁻ 9 q6 ∷
   re 10 3 (CK31 ∷ []) ∷
   rw⁻ 8 q8 ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q6 ∷
   rw 8 q5 ∷
   rw⁻ 7 q6 ∷
   re 8 3 (CK31 ∷ []) ∷
   rw⁻ 6 q7 ∷
   rw 5 q5 ∷
   rw 4 q5 ∷
   rw 3 q3 ∷
   rw 2 q5 ∷
   rw 1 q3 ∷
   rw 0 q3 ∷
   rw 1 q9 ∷
   rw 0 q2 ∷
   rw 1 q10 ∷
   rw 2 q4 ∷
   rw 3 q10 ∷
   rw 4 q4 ∷
   rw 5 q11 ∷
   rw 6 q11 ∷
   rw 7 q11 ∷
   rw 8 q10 ∷
   rw 9 q4 ∷
   rw 10 q11 ∷
   rw 11 q11 ∷
   rw 12 q11 ∷
   rw 13 q11 ∷
   rw 14 q11 ∷
   rw 15 q11 ∷
   rw 16 q2 ∷
   rw 17 q11 ∷
   rw 18 q11 ∷
   rw 19 q10 ∷
   rw 20 q11 ∷
   rw 21 q10 ∷
   rw 22 q10 ∷
   rw 23 q7 ∷
   re 25 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   rw 25 q10 ∷
   rw 26 q6 ∷
   re 24 3 (CK30 ∷ []) ∷
   rw 25 q8 ∷
   re 27 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   rw 27 q10 ∷
   rw 28 q6 ∷
   re 26 3 (CK30 ∷ []) ∷
   rw 27 q8 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q6 ∷
   rw 29 q11 ∷
   rw 30 q6 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q6 ∷
   rw 30 q11 ∷
   rw 31 q6 ∷
   re 29 3 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q6 ∷
   rw 31 q11 ∷
   rw 32 q6 ∷
   re 30 3 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 31 q6 ∷
   rw 32 q10 ∷
   rw 33 q6 ∷
   re 31 3 (CK30 ∷ []) ∷
   rw 32 q8 ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q6 ∷
   rw 34 q11 ∷
   rw 35 q6 ∷
   re 33 3 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q6 ∷
   rw 35 q11 ∷
   rw 36 q6 ∷
   re 34 3 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q6 ∷
   rw 36 q11 ∷
   rw 37 q6 ∷
   re 35 3 (CS03 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q6 ∷
   rw 37 q11 ∷
   rw 38 q6 ∷
   re 36 3 (CS03 ∷ []) ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q6 ∷
   rw 38 q11 ∷
   rw 39 q6 ∷
   re 37 3 (CS03 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q6 ∷
   rw 39 q11 ∷
   rw 40 q6 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 39 q7 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q6 ∷
   rw 41 q11 ∷
   rw 42 q6 ∷
   re 40 3 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 41 q6 ∷
   rw 42 q11 ∷
   rw 43 q6 ∷
   re 41 3 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 42 q6 ∷
   rw 43 q10 ∷
   rw 44 q6 ∷
   re 42 3 (CK30 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q6 ∷
   rw 44 q11 ∷
   rw 45 q6 ∷
   re 43 3 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 44 q6 ∷
   rw 45 q10 ∷
   rw 46 q6 ∷
   re 44 3 (CK30 ∷ []) ∷
   re 46 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 45 q6 ∷
   rw 46 q10 ∷
   rw 47 q6 ∷
   re 45 3 (CK30 ∷ []) ∷
   rw 46 q12 ∷
   rw 47 q1 ∷
   rw⁻ 46 q2 ∷
   re 45 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q6 ∷
   rw 46 q5 ∷
   rw⁻ 45 q6 ∷
   re 46 3 (CK31 ∷ []) ∷
   rw 46 q13 ∷
   rw 45 q2 ∷
   re 47 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 46 q6 ∷
   rw 47 q10 ∷
   rw 48 q6 ∷
   re 46 3 (CK30 ∷ []) ∷
   rw 47 q12 ∷
   re 46 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q14 ∷
   re 50 3 (CX31 ∷ []) ∷
   rw 49 q15 ∷
   rw 48 q16 ∷
   rw 47 q17 ∷
   re 47 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 46 q18 ∷
   re 47 5 (CK30 ∷ []) ∷
   rw 49 q1 ∷
   rw⁻ 48 q2 ∷
   re 47 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q6 ∷
   rw 48 q5 ∷
   rw⁻ 47 q6 ∷
   re 48 3 (CK31 ∷ []) ∷
   rw 48 q13 ∷
   rw 47 q2 ∷
   re 49 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 48 q6 ∷
   rw 49 q10 ∷
   rw 50 q6 ∷
   re 48 3 (CK30 ∷ []) ∷
   rw 49 q12 ∷
   rw 46 q1 ∷
   rw⁻ 45 q2 ∷
   re 44 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q6 ∷
   rw 45 q5 ∷
   rw⁻ 44 q6 ∷
   re 45 3 (CK31 ∷ []) ∷
   rw 45 q13 ∷
   rw 44 q2 ∷
   re 46 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 45 q6 ∷
   rw 46 q10 ∷
   rw 47 q6 ∷
   re 45 3 (CK30 ∷ []) ∷
   rw 46 q12 ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q14 ∷
   re 49 3 (CX31 ∷ []) ∷
   rw 48 q15 ∷
   rw 47 q16 ∷
   rw 46 q17 ∷
   re 46 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 45 q18 ∷
   re 46 5 (CK30 ∷ []) ∷
   rw 48 q1 ∷
   rw⁻ 47 q2 ∷
   re 46 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q6 ∷
   rw 47 q5 ∷
   rw⁻ 46 q6 ∷
   re 47 3 (CK31 ∷ []) ∷
   rw 47 q13 ∷
   rw 46 q2 ∷
   re 48 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 47 q6 ∷
   rw 48 q10 ∷
   rw 49 q6 ∷
   re 47 3 (CK30 ∷ []) ∷
   rw 48 q12 ∷
   rw 45 q1 ∷
   rw⁻ 44 q2 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q6 ∷
   rw 44 q3 ∷
   rw⁻ 43 q6 ∷
   re 44 3 (CS13 ∷ []) ∷
   rw 44 q19 ∷
   rw 43 q2 ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q6 ∷
   rw 45 q11 ∷
   rw 46 q6 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 45 q12 ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q14 ∷
   re 48 3 (CX31 ∷ []) ∷
   rw 47 q15 ∷
   rw 46 q20 ∷
   rw 45 q17 ∷
   re 45 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 44 q18 ∷
   re 45 5 (CS03 ∷ []) ∷
   rw 47 q1 ∷
   rw⁻ 46 q2 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q6 ∷
   rw 46 q3 ∷
   rw⁻ 45 q6 ∷
   re 46 3 (CS13 ∷ []) ∷
   rw 46 q19 ∷
   rw 45 q2 ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 46 q6 ∷
   rw 47 q11 ∷
   rw 48 q6 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 47 q12 ∷
   rw 44 q1 ∷
   rw⁻ 43 q2 ∷
   re 42 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q6 ∷
   rw 43 q5 ∷
   rw⁻ 42 q6 ∷
   re 43 3 (CK31 ∷ []) ∷
   rw 43 q13 ∷
   rw 42 q2 ∷
   re 44 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 43 q6 ∷
   rw 44 q10 ∷
   rw 45 q6 ∷
   re 43 3 (CK30 ∷ []) ∷
   rw 44 q12 ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q14 ∷
   re 47 3 (CX31 ∷ []) ∷
   rw 46 q15 ∷
   rw 45 q16 ∷
   rw 44 q17 ∷
   re 44 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 43 q18 ∷
   re 44 5 (CK30 ∷ []) ∷
   rw 46 q1 ∷
   rw⁻ 45 q2 ∷
   re 44 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q6 ∷
   rw 45 q5 ∷
   rw⁻ 44 q6 ∷
   re 45 3 (CK31 ∷ []) ∷
   rw 45 q13 ∷
   rw 44 q2 ∷
   re 46 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 45 q6 ∷
   rw 46 q10 ∷
   rw 47 q6 ∷
   re 45 3 (CK30 ∷ []) ∷
   rw 46 q12 ∷
   rw 43 q1 ∷
   rw⁻ 42 q2 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q6 ∷
   rw 42 q3 ∷
   rw⁻ 41 q6 ∷
   re 42 3 (CS13 ∷ []) ∷
   rw 42 q19 ∷
   rw 41 q2 ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q6 ∷
   rw 43 q11 ∷
   rw 44 q6 ∷
   re 42 3 (CS03 ∷ []) ∷
   rw 43 q12 ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q14 ∷
   re 46 3 (CX31 ∷ []) ∷
   rw 45 q15 ∷
   rw 44 q20 ∷
   rw 43 q17 ∷
   re 43 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 42 q18 ∷
   re 43 5 (CS03 ∷ []) ∷
   rw 45 q1 ∷
   rw⁻ 44 q2 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q6 ∷
   rw 44 q3 ∷
   rw⁻ 43 q6 ∷
   re 44 3 (CS13 ∷ []) ∷
   rw 44 q19 ∷
   rw 43 q2 ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q6 ∷
   rw 45 q11 ∷
   rw 46 q6 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 45 q12 ∷
   rw 42 q1 ∷
   rw⁻ 41 q2 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q6 ∷
   rw 41 q3 ∷
   rw⁻ 40 q6 ∷
   re 41 3 (CS13 ∷ []) ∷
   rw 41 q19 ∷
   rw 40 q2 ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 41 q6 ∷
   rw 42 q11 ∷
   rw 43 q6 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 42 q12 ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q14 ∷
   re 45 3 (CX31 ∷ []) ∷
   rw 44 q15 ∷
   rw 43 q20 ∷
   rw 42 q17 ∷
   re 42 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 41 q18 ∷
   re 42 5 (CS03 ∷ []) ∷
   rw 44 q1 ∷
   rw⁻ 43 q2 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q6 ∷
   rw 43 q3 ∷
   rw⁻ 42 q6 ∷
   re 43 3 (CS13 ∷ []) ∷
   rw 43 q19 ∷
   rw 42 q2 ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q6 ∷
   rw 44 q11 ∷
   rw 45 q6 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 44 q12 ∷
   rw 39 q21 ∷
   rw 40 q1 ∷
   rw⁻ 39 q2 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q6 ∷
   rw 39 q3 ∷
   rw⁻ 38 q6 ∷
   re 39 3 (CS13 ∷ []) ∷
   rw 39 q19 ∷
   rw 38 q2 ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q6 ∷
   rw 40 q11 ∷
   rw 41 q6 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 40 q12 ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q14 ∷
   re 43 3 (CX31 ∷ []) ∷
   rw 42 q15 ∷
   rw 41 q20 ∷
   rw 40 q17 ∷
   re 40 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 39 q18 ∷
   re 40 5 (CS03 ∷ []) ∷
   rw 42 q1 ∷
   rw⁻ 41 q2 ∷ []) Eq.refl

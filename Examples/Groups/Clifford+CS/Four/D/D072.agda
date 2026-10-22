{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D072 (W : Ws) where

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
  q2 = wE 140 W
  q3 : Eqn
  q3 = wE 7 W
  q4 : Eqn
  q4 = wE 542 W
  q5 : Eqn
  q5 = wE 29 W
  q6 : Eqn
  q6 = eqn (Sw01 ∷ S2⁻ ∷ []) (S2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • S • S)))
  q7 : Eqn
  q7 = wE 139 W
  q8 : Eqn
  q8 = wE 27 W
  q9 : Eqn
  q9 = wE 142 W
  q10 : Eqn
  q10 = wE 31 W
  q11 : Eqn
  q11 = eqn (CK10 ∷ X3 ∷ []) (X3 ∷ CK10 ∷ []) (low-comm (CK₁₀) ((X ↑)))
  q12 : Eqn
  q12 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q13 : Eqn
  q13 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q14 : Eqn
  q14 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q15 : Eqn
  q15 = wE 537 W
  q16 : Eqn
  q16 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q17 : Eqn
  q17 = eqn (S1 ∷ CX32 ∷ []) (CX32 ∷ S1 ∷ []) (low-comm ((S ↑)) (CX₁₀))
  q18 : Eqn
  q18 = wE 5 W
  q19 : Eqn
  q19 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q20 : Eqn
  q20 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q21 : Eqn
  q21 = wE 538 W
  q22 : Eqn
  q22 = wE 1 W
  q23 : Eqn
  q23 = wE 173 W
  q24 : Eqn
  q24 = wE 3 W
  q25 : Eqn
  q25 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q26 : Eqn
  q26 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q27 : Eqn
  q27 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q28 : Eqn
  q28 = wE 578 W
  q29 : Eqn
  q29 = wE 175 W
  q30 : Eqn
  q30 = wE 579 W
  q31 : Eqn
  q31 = wE 574 W
  q32 : Eqn
  q32 = wE 13 W
  q33 : Eqn
  q33 = eqn (CS01⁻ ∷ CX32 ∷ []) (CX32 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₁₀))
  q34 : Eqn
  q34 = wE 78 W
  q35 : Eqn
  q35 = eqn (CK10⁻ ∷ CX32 ∷ []) (CX32 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q36 : Eqn
  q36 = wE 575 W
  q37 : Eqn
  q37 = wE 76 W
  q38 : Eqn
  q38 = wE 137 W
  q39 : Eqn
  q39 = wE 536 W

-- Bar(SSKSKK;3,1->0) passes white iX via V2 conjugates 2 part1: 500 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part1 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ Sw23 ∷ Sw01 ∷ CK21 ∷ Sw23 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ Sw01 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ CK31 ∷ Sw01 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part1 = derive (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ Sw23 ∷ Sw01 ∷ CK21 ∷ Sw23 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ Sw01 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ CK31 ∷ Sw01 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ [])
  (rw⁻ 15 q1 ∷
   re 16 3 (CK31 ∷ []) ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q1 ∷
   rw 15 q2 ∷
   rw⁻ 14 q1 ∷
   re 15 3 (CK31 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q1 ∷
   rw 14 q3 ∷
   rw⁻ 13 q1 ∷
   re 14 3 (CS13 ∷ []) ∷
   re 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q1 ∷
   rw 13 q2 ∷
   rw⁻ 12 q1 ∷
   re 13 3 (CK31 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q1 ∷
   rw 12 q3 ∷
   rw⁻ 11 q1 ∷
   re 12 3 (CS13 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q1 ∷
   rw 11 q3 ∷
   rw⁻ 10 q1 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 11 q4 ∷
   rw 10 q5 ∷
   rw 11 q5 ∷
   rw 12 q5 ∷
   rw 13 q5 ∷
   rw 14 q5 ∷
   rw 15 q5 ∷
   rw 16 q6 ∷
   rw 17 q7 ∷
   rw 18 q5 ∷
   rw 19 q5 ∷
   rw 20 q5 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q1 ∷
   rw 22 q8 ∷
   rw 23 q1 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q1 ∷
   rw 23 q8 ∷
   rw 24 q1 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   rw 24 q9 ∷
   rw 25 q1 ∷
   re 23 3 (CK30 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   rw 25 q8 ∷
   rw 26 q1 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   rw 26 q9 ∷
   rw 27 q1 ∷
   re 25 3 (CK30 ∷ []) ∷
   re 27 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   rw 27 q9 ∷
   rw 28 q1 ∷
   re 26 3 (CK30 ∷ []) ∷
   rw 27 q10 ∷
   rw 49 q11 ∷
   rw 50 q12 ∷
   rw 51 q11 ∷
   rw 48 q11 ∷
   rw 49 q12 ∷
   rw 50 q11 ∷
   rw 47 q13 ∷
   rw 48 q14 ∷
   rw 49 q13 ∷
   rw 46 q11 ∷
   rw 47 q12 ∷
   rw 48 q11 ∷
   rw 45 q13 ∷
   rw 46 q14 ∷
   rw 47 q13 ∷
   rw 44 q13 ∷
   rw 45 q14 ∷
   rw 46 q13 ∷
   rw 43 q15 ∷
   rw 42 q13 ∷
   rw 43 q14 ∷
   rw 44 q13 ∷
   rw 41 q13 ∷
   rw 42 q14 ∷
   rw 43 q13 ∷
   rw 40 q13 ∷
   rw 41 q14 ∷
   rw 42 q13 ∷
   rw 39 q13 ∷
   rw 40 q14 ∷
   rw 41 q13 ∷
   rw 38 q13 ∷
   rw 39 q14 ∷
   rw 40 q13 ∷
   rw 37 q13 ∷
   rw 38 q14 ∷
   rw 39 q13 ∷
   rw 36 q16 ∷
   rw 37 q17 ∷
   rw 38 q16 ∷
   rw 35 q11 ∷
   rw 36 q12 ∷
   rw 37 q11 ∷
   rw 34 q13 ∷
   rw 35 q14 ∷
   rw 36 q13 ∷
   rw 33 q13 ∷
   rw 34 q14 ∷
   rw 35 q13 ∷
   rw 32 q13 ∷
   rw 33 q14 ∷
   rw 34 q13 ∷
   rw 31 q16 ∷
   rw 32 q17 ∷
   rw 33 q16 ∷
   rw 30 q11 ∷
   rw 31 q12 ∷
   rw 32 q11 ∷
   rw 29 q16 ∷
   rw 30 q17 ∷
   rw 31 q16 ∷
   rw 28 q11 ∷
   rw 29 q12 ∷
   rw 30 q11 ∷
   rw 27 q15 ∷
   rw 30 q18 ∷
   rw⁻ 29 q19 ∷
   rw⁻ 28 q20 ∷
   rw⁻ 27 q19 ∷
   re 26 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q1 ∷
   rw 27 q2 ∷
   rw⁻ 26 q1 ∷
   re 27 3 (CK31 ∷ []) ∷
   re 25 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q1 ∷
   rw 26 q2 ∷
   rw⁻ 25 q1 ∷
   re 26 3 (CK31 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q1 ∷
   rw 25 q3 ∷
   rw⁻ 24 q1 ∷
   re 25 3 (CS13 ∷ []) ∷
   re 23 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q1 ∷
   rw 24 q2 ∷
   rw⁻ 23 q1 ∷
   re 24 3 (CK31 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q1 ∷
   rw 23 q3 ∷
   rw⁻ 22 q1 ∷
   re 23 3 (CS13 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q1 ∷
   rw 22 q3 ∷
   rw⁻ 21 q1 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 22 q21 ∷
   rw 21 q19 ∷
   rw 22 q20 ∷
   rw 23 q19 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   rw 25 q8 ∷
   rw 26 q1 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   rw 26 q8 ∷
   rw 27 q1 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   rw 27 q9 ∷
   rw 28 q1 ∷
   re 26 3 (CK30 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   rw 28 q8 ∷
   rw 29 q1 ∷
   re 27 3 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   rw 29 q9 ∷
   rw 30 q1 ∷
   re 28 3 (CK30 ∷ []) ∷
   re 30 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   rw 30 q9 ∷
   rw 31 q1 ∷
   re 29 3 (CK30 ∷ []) ∷
   rw 30 q10 ∷
   rw 59 q22 ∷
   rw 58 q23 ∷
   re 57 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 59 q24 ∷
   re 56 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 58 q24 ∷
   re 55 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 57 q24 ∷
   re 54 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 56 q24 ∷
   rw 53 q23 ∷
   rw 52 q25 ∷
   rw 51 q25 ∷
   rw 50 q26 ∷
   rw 49 q25 ∷
   rw 48 q26 ∷
   rw 47 q26 ∷
   re 46 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 48 q24 ∷
   rw 45 q26 ∷
   rw 44 q26 ∷
   rw 43 q26 ∷
   rw 42 q26 ∷
   rw 41 q26 ∷
   rw 40 q26 ∷
   rw 39 q27 ∷
   rw 38 q25 ∷
   rw 37 q26 ∷
   rw 36 q26 ∷
   rw 35 q26 ∷
   rw 34 q27 ∷
   rw 33 q25 ∷
   rw 32 q27 ∷
   rw 31 q25 ∷
   re 30 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 32 q24 ∷
   re 29 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 31 q24 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q24 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q24 ∷
   re 26 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 28 q24 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q24 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q24 ∷
   rw 25 q28 ∷
   rw 24 q29 ∷
   rw 27 q22 ∷
   re 25 3 (CS03⁻ ∷ []) ∷
   rw 28 q22 ∷
   re 26 3 (CK30⁻ ∷ []) ∷
   rw 29 q22 ∷
   re 27 3 (CS03⁻ ∷ []) ∷
   rw 30 q22 ∷
   re 28 3 (CS03⁻ ∷ []) ∷
   rw 29 q29 ∷
   rw 32 q22 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 33 q22 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 34 q22 ∷
   re 32 3 (CK30 ∷ []) ∷
   rw 35 q22 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 36 q22 ∷
   re 34 3 (CK30 ∷ []) ∷
   rw 37 q22 ∷
   re 35 3 (CK30 ∷ []) ∷
   rw 38 q22 ∷
   re 36 3 (CX31 ∷ []) ∷
   rw⁻ 37 q25 ∷
   rw⁻ 38 q27 ∷
   rw⁻ 39 q25 ∷
   rw⁻ 40 q27 ∷
   rw⁻ 41 q26 ∷
   rw⁻ 42 q26 ∷
   rw⁻ 43 q26 ∷
   rw⁻ 44 q25 ∷
   rw⁻ 45 q27 ∷
   rw⁻ 46 q26 ∷
   rw⁻ 47 q26 ∷
   rw⁻ 48 q26 ∷
   rw⁻ 49 q26 ∷
   rw⁻ 50 q26 ∷
   rw⁻ 51 q26 ∷
   rw 54 q22 ∷
   re 52 3 (CX31 ∷ []) ∷
   rw⁻ 53 q26 ∷
   rw⁻ 54 q26 ∷
   rw⁻ 55 q25 ∷
   rw⁻ 56 q26 ∷
   rw⁻ 57 q25 ∷
   rw⁻ 58 q25 ∷
   rw 59 q24 ∷
   rw 64 q22 ∷
   rw 63 q23 ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 64 q24 ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 63 q24 ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 62 q24 ∷
   rw 59 q23 ∷
   rw 58 q25 ∷
   rw 57 q25 ∷
   rw 56 q26 ∷
   rw 55 q25 ∷
   rw 54 q26 ∷
   rw 53 q26 ∷
   re 52 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 54 q24 ∷
   rw 51 q26 ∷
   rw 50 q26 ∷
   rw 49 q26 ∷
   rw 48 q26 ∷
   rw 47 q26 ∷
   rw 46 q26 ∷
   rw 45 q27 ∷
   rw 44 q25 ∷
   rw 43 q26 ∷
   rw 42 q26 ∷
   rw 41 q26 ∷
   rw 40 q27 ∷
   rw 39 q25 ∷
   rw 38 q27 ∷
   rw 37 q25 ∷
   re 36 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 38 q24 ∷
   re 35 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 37 q24 ∷
   re 34 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 36 q24 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q24 ∷
   re 32 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 34 q24 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q24 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q24 ∷
   rw 31 q30 ∷
   rw 30 q29 ∷
   rw 33 q22 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 34 q22 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 35 q22 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 34 q29 ∷
   rw 37 q22 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 38 q22 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 39 q22 ∷
   re 37 3 (CK30 ∷ []) ∷
   rw 40 q22 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 41 q22 ∷
   re 39 3 (CK30 ∷ []) ∷
   rw 42 q22 ∷
   re 40 3 (CK30 ∷ []) ∷
   rw 43 q22 ∷
   re 41 3 (CX31 ∷ []) ∷
   rw⁻ 42 q25 ∷
   rw⁻ 43 q27 ∷
   rw⁻ 44 q25 ∷
   rw⁻ 45 q27 ∷
   rw⁻ 46 q26 ∷
   rw⁻ 47 q26 ∷
   rw⁻ 48 q26 ∷
   rw⁻ 49 q25 ∷
   rw⁻ 50 q27 ∷
   rw⁻ 51 q26 ∷
   rw⁻ 52 q26 ∷
   rw⁻ 53 q26 ∷
   rw⁻ 54 q26 ∷
   rw⁻ 55 q26 ∷
   rw⁻ 56 q26 ∷
   rw 59 q22 ∷
   re 57 3 (CX31 ∷ []) ∷
   rw⁻ 58 q26 ∷
   rw⁻ 59 q26 ∷
   rw⁻ 60 q25 ∷
   rw⁻ 61 q26 ∷
   rw⁻ 62 q25 ∷
   rw⁻ 63 q25 ∷
   rw 64 q24 ∷
   rw 58 q31 ∷
   re 58 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 57 q32 ∷
   rw⁻ 58 q33 ∷
   rw 59 q34 ∷
   re 57 3 (CS02⁻ ∷ []) ∷
   re 59 1 (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) ∷
   rw 58 q32 ∷
   rw⁻ 59 q35 ∷
   rw 60 q34 ∷
   re 58 3 (CK20⁻ ∷ []) ∷
   re 60 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 59 q32 ∷
   rw⁻ 60 q33 ∷
   rw 61 q34 ∷
   re 59 3 (CS02⁻ ∷ []) ∷
   re 61 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 60 q32 ∷
   rw⁻ 61 q33 ∷
   rw 62 q34 ∷
   re 60 3 (CS02⁻ ∷ []) ∷
   rw 42 q36 ∷
   re 42 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 41 q32 ∷
   rw⁻ 42 q33 ∷
   rw 43 q34 ∷
   re 41 3 (CS02⁻ ∷ []) ∷
   re 43 1 (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) ∷
   rw 42 q32 ∷
   rw⁻ 43 q35 ∷
   rw 44 q34 ∷
   re 42 3 (CK20⁻ ∷ []) ∷
   re 44 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 43 q32 ∷
   rw⁻ 44 q33 ∷
   rw 45 q34 ∷
   re 43 3 (CS02⁻ ∷ []) ∷
   re 45 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 44 q32 ∷
   rw⁻ 45 q33 ∷
   rw 46 q34 ∷
   re 44 3 (CS02⁻ ∷ []) ∷
   rw 45 q18 ∷
   rw 44 q37 ∷
   rw 43 q37 ∷
   rw 42 q38 ∷
   rw 41 q37 ∷
   re 40 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q1 ∷
   rw 41 q2 ∷
   rw⁻ 40 q1 ∷
   re 41 3 (CK31 ∷ []) ∷
   re 39 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q1 ∷
   rw 40 q2 ∷
   rw⁻ 39 q1 ∷
   re 40 3 (CK31 ∷ []) ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q1 ∷
   rw 39 q3 ∷
   rw⁻ 38 q1 ∷
   re 39 3 (CS13 ∷ []) ∷
   re 37 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q1 ∷
   rw 38 q2 ∷
   rw⁻ 37 q1 ∷
   re 38 3 (CK31 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q1 ∷
   rw 37 q3 ∷
   rw⁻ 36 q1 ∷
   re 37 3 (CS13 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q1 ∷
   rw 36 q3 ∷
   rw⁻ 35 q1 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 36 q39 ∷
   rw 35 q5 ∷
   rw 36 q7 ∷
   rw 37 q5 ∷
   rw 38 q5 ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q1 ∷
   rw 40 q8 ∷
   rw 41 q1 ∷
   re 39 3 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   rw 41 q8 ∷
   rw 42 q1 ∷
   re 40 3 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   rw 42 q9 ∷
   rw 43 q1 ∷
   re 41 3 (CK30 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   rw 43 q8 ∷
   rw 44 q1 ∷
   re 42 3 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   rw 44 q9 ∷
   rw 45 q1 ∷ []) Eq.refl

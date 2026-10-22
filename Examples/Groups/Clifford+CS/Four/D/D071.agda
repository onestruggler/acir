{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D071 (W : Ws) where

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
  q1 = eqn (CK10 ∷ X3 ∷ []) (X3 ∷ CK10 ∷ []) (low-comm (CK₁₀) ((X ↑)))
  q2 : Eqn
  q2 = eqn (CK10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((CS • CS • CS)))
  q3 : Eqn
  q3 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q4 : Eqn
  q4 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q5 : Eqn
  q5 = wE 532 W
  q6 : Eqn
  q6 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q7 : Eqn
  q7 = eqn (S1 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S1 ∷ []) (low-comm ((S ↑)) ((CS • CS • CS)))
  q8 : Eqn
  q8 = wE 5 W
  q9 : Eqn
  q9 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q11 : Eqn
  q11 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q12 : Eqn
  q12 = wE 140 W
  q13 : Eqn
  q13 = wE 7 W
  q14 : Eqn
  q14 = wE 533 W
  q15 : Eqn
  q15 = wE 27 W
  q16 : Eqn
  q16 = wE 142 W
  q17 : Eqn
  q17 = wE 31 W
  q18 : Eqn
  q18 = wE 574 W
  q19 : Eqn
  q19 = wE 13 W
  q20 : Eqn
  q20 = eqn (CS01⁻ ∷ CX32 ∷ []) (CX32 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₁₀))
  q21 : Eqn
  q21 = wE 78 W
  q22 : Eqn
  q22 = eqn (CK10⁻ ∷ CX32 ∷ []) (CX32 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q23 : Eqn
  q23 = wE 575 W
  q24 : Eqn
  q24 = wE 76 W
  q25 : Eqn
  q25 = wE 137 W
  q26 : Eqn
  q26 = wE 536 W
  q27 : Eqn
  q27 = wE 29 W
  q28 : Eqn
  q28 = wE 139 W
  q29 : Eqn
  q29 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q30 : Eqn
  q30 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q31 : Eqn
  q31 = wE 537 W
  q32 : Eqn
  q32 = eqn (S1 ∷ CX32 ∷ []) (CX32 ∷ S1 ∷ []) (low-comm ((S ↑)) (CX₁₀))
  q33 : Eqn
  q33 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q34 : Eqn
  q34 = wE 538 W
  q35 : Eqn
  q35 = wE 576 W
  q36 : Eqn
  q36 = wE 540 W
  q37 : Eqn
  q37 = wE 577 W
  q38 : Eqn
  q38 = eqn (Sw01 ∷ S2⁻ ∷ []) (S2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • S • S)))

-- Bar(SSKSKK;3,1->0) passes white iX via V2 conjugates 2 part0: 500 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part0 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ Sw23 ∷ Sw01 ∷ CK21 ∷ Sw23 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ Sw01 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part0 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ Sw23 ∷ Sw01 ∷ CK21 ∷ Sw23 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ Sw01 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 28 q1 ∷
   rw 29 q2 ∷
   rw 30 q1 ∷
   rw 27 q1 ∷
   rw 28 q2 ∷
   rw 29 q1 ∷
   rw 26 q3 ∷
   rw 27 q4 ∷
   rw 28 q3 ∷
   rw 25 q1 ∷
   rw 26 q2 ∷
   rw 27 q1 ∷
   rw 24 q3 ∷
   rw 25 q4 ∷
   rw 26 q3 ∷
   rw 23 q3 ∷
   rw 24 q4 ∷
   rw 25 q3 ∷
   rw 22 q5 ∷
   rw 21 q3 ∷
   rw 22 q4 ∷
   rw 23 q3 ∷
   rw 20 q3 ∷
   rw 21 q4 ∷
   rw 22 q3 ∷
   rw 19 q3 ∷
   rw 20 q4 ∷
   rw 21 q3 ∷
   rw 18 q3 ∷
   rw 19 q4 ∷
   rw 20 q3 ∷
   rw 17 q3 ∷
   rw 18 q4 ∷
   rw 19 q3 ∷
   rw 16 q3 ∷
   rw 17 q4 ∷
   rw 18 q3 ∷
   rw 15 q6 ∷
   rw 16 q7 ∷
   rw 17 q6 ∷
   rw 14 q1 ∷
   rw 15 q2 ∷
   rw 16 q1 ∷
   rw 13 q3 ∷
   rw 14 q4 ∷
   rw 15 q3 ∷
   rw 12 q3 ∷
   rw 13 q4 ∷
   rw 14 q3 ∷
   rw 11 q3 ∷
   rw 12 q4 ∷
   rw 13 q3 ∷
   rw 10 q6 ∷
   rw 11 q7 ∷
   rw 12 q6 ∷
   rw 9 q1 ∷
   rw 10 q2 ∷
   rw 11 q1 ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   rw 7 q1 ∷
   rw 8 q2 ∷
   rw 9 q1 ∷
   rw 6 q5 ∷
   rw 9 q8 ∷
   rw⁻ 8 q9 ∷
   rw⁻ 7 q10 ∷
   rw⁻ 6 q9 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q11 ∷
   rw 6 q12 ∷
   rw⁻ 5 q11 ∷
   re 6 3 (CK31 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q11 ∷
   rw 5 q12 ∷
   rw⁻ 4 q11 ∷
   re 5 3 (CK31 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q11 ∷
   rw 4 q13 ∷
   rw⁻ 3 q11 ∷
   re 4 3 (CS13 ∷ []) ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q11 ∷
   rw 3 q12 ∷
   rw⁻ 2 q11 ∷
   re 3 3 (CK31 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q11 ∷
   rw 2 q13 ∷
   rw⁻ 1 q11 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q11 ∷
   rw 1 q13 ∷
   rw⁻ 0 q11 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q14 ∷
   rw 0 q9 ∷
   rw 1 q10 ∷
   rw 2 q9 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q11 ∷
   rw 4 q15 ∷
   rw 5 q11 ∷
   re 3 3 (CS03 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q11 ∷
   rw 5 q15 ∷
   rw 6 q11 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 5 q11 ∷
   rw 6 q16 ∷
   rw 7 q11 ∷
   re 5 3 (CK30 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q11 ∷
   rw 7 q15 ∷
   rw 8 q11 ∷
   re 6 3 (CS03 ∷ []) ∷
   re 8 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q11 ∷
   rw 8 q16 ∷
   rw 9 q11 ∷
   re 7 3 (CK30 ∷ []) ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q11 ∷
   rw 9 q16 ∷
   rw 10 q11 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q17 ∷
   rw 26 q18 ∷
   re 26 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 25 q19 ∷
   rw⁻ 26 q20 ∷
   rw 27 q21 ∷
   re 25 3 (CS02⁻ ∷ []) ∷
   re 27 1 (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) ∷
   rw 26 q19 ∷
   rw⁻ 27 q22 ∷
   rw 28 q21 ∷
   re 26 3 (CK20⁻ ∷ []) ∷
   re 28 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 27 q19 ∷
   rw⁻ 28 q20 ∷
   rw 29 q21 ∷
   re 27 3 (CS02⁻ ∷ []) ∷
   re 29 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 28 q19 ∷
   rw⁻ 29 q20 ∷
   rw 30 q21 ∷
   re 28 3 (CS02⁻ ∷ []) ∷
   rw 10 q23 ∷
   re 10 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 9 q19 ∷
   rw⁻ 10 q20 ∷
   rw 11 q21 ∷
   re 9 3 (CS02⁻ ∷ []) ∷
   re 11 1 (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) ∷
   rw 10 q19 ∷
   rw⁻ 11 q22 ∷
   rw 12 q21 ∷
   re 10 3 (CK20⁻ ∷ []) ∷
   re 12 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 11 q19 ∷
   rw⁻ 12 q20 ∷
   rw 13 q21 ∷
   re 11 3 (CS02⁻ ∷ []) ∷
   re 13 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 12 q19 ∷
   rw⁻ 13 q20 ∷
   rw 14 q21 ∷
   re 12 3 (CS02⁻ ∷ []) ∷
   rw 13 q8 ∷
   rw 12 q24 ∷
   rw 11 q24 ∷
   rw 10 q25 ∷
   rw 9 q24 ∷
   re 8 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q11 ∷
   rw 9 q12 ∷
   rw⁻ 8 q11 ∷
   re 9 3 (CK31 ∷ []) ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q11 ∷
   rw 8 q12 ∷
   rw⁻ 7 q11 ∷
   re 8 3 (CK31 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q11 ∷
   rw 7 q13 ∷
   rw⁻ 6 q11 ∷
   re 7 3 (CS13 ∷ []) ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q11 ∷
   rw 6 q12 ∷
   rw⁻ 5 q11 ∷
   re 6 3 (CK31 ∷ []) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q11 ∷
   rw 5 q13 ∷
   rw⁻ 4 q11 ∷
   re 5 3 (CS13 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q11 ∷
   rw 4 q13 ∷
   rw⁻ 3 q11 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 4 q26 ∷
   rw 3 q27 ∷
   rw 4 q28 ∷
   rw 5 q27 ∷
   rw 6 q27 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q11 ∷
   rw 8 q15 ∷
   rw 9 q11 ∷
   re 7 3 (CS03 ∷ []) ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q11 ∷
   rw 9 q15 ∷
   rw 10 q11 ∷
   re 8 3 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 9 q11 ∷
   rw 10 q16 ∷
   rw 11 q11 ∷
   re 9 3 (CK30 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q11 ∷
   rw 11 q15 ∷
   rw 12 q11 ∷
   re 10 3 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 11 q11 ∷
   rw 12 q16 ∷
   rw 13 q11 ∷
   re 11 3 (CK30 ∷ []) ∷
   re 13 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 12 q11 ∷
   rw 13 q16 ∷
   rw 14 q11 ∷
   re 12 3 (CK30 ∷ []) ∷
   rw 13 q17 ∷
   rw 35 q1 ∷
   rw 36 q29 ∷
   rw 37 q1 ∷
   rw 34 q1 ∷
   rw 35 q29 ∷
   rw 36 q1 ∷
   rw 33 q3 ∷
   rw 34 q30 ∷
   rw 35 q3 ∷
   rw 32 q1 ∷
   rw 33 q29 ∷
   rw 34 q1 ∷
   rw 31 q3 ∷
   rw 32 q30 ∷
   rw 33 q3 ∷
   rw 30 q3 ∷
   rw 31 q30 ∷
   rw 32 q3 ∷
   rw 29 q31 ∷
   rw 28 q3 ∷
   rw 29 q30 ∷
   rw 30 q3 ∷
   rw 27 q3 ∷
   rw 28 q30 ∷
   rw 29 q3 ∷
   rw 26 q3 ∷
   rw 27 q30 ∷
   rw 28 q3 ∷
   rw 25 q3 ∷
   rw 26 q30 ∷
   rw 27 q3 ∷
   rw 24 q3 ∷
   rw 25 q30 ∷
   rw 26 q3 ∷
   rw 23 q3 ∷
   rw 24 q30 ∷
   rw 25 q3 ∷
   rw 22 q6 ∷
   rw 23 q32 ∷
   rw 24 q6 ∷
   rw 21 q1 ∷
   rw 22 q29 ∷
   rw 23 q1 ∷
   rw 20 q3 ∷
   rw 21 q30 ∷
   rw 22 q3 ∷
   rw 19 q3 ∷
   rw 20 q30 ∷
   rw 21 q3 ∷
   rw 18 q3 ∷
   rw 19 q30 ∷
   rw 20 q3 ∷
   rw 17 q6 ∷
   rw 18 q32 ∷
   rw 19 q6 ∷
   rw 16 q1 ∷
   rw 17 q29 ∷
   rw 18 q1 ∷
   rw 15 q6 ∷
   rw 16 q32 ∷
   rw 17 q6 ∷
   rw 14 q1 ∷
   rw 15 q29 ∷
   rw 16 q1 ∷
   rw 13 q31 ∷
   rw 16 q8 ∷
   rw⁻ 15 q9 ∷
   rw⁻ 14 q33 ∷
   rw⁻ 13 q9 ∷
   re 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q11 ∷
   rw 13 q12 ∷
   rw⁻ 12 q11 ∷
   re 13 3 (CK31 ∷ []) ∷
   re 11 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q11 ∷
   rw 12 q12 ∷
   rw⁻ 11 q11 ∷
   re 12 3 (CK31 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q11 ∷
   rw 11 q13 ∷
   rw⁻ 10 q11 ∷
   re 11 3 (CS13 ∷ []) ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q11 ∷
   rw 10 q12 ∷
   rw⁻ 9 q11 ∷
   re 10 3 (CK31 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q11 ∷
   rw 9 q13 ∷
   rw⁻ 8 q11 ∷
   re 9 3 (CS13 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q11 ∷
   rw 8 q13 ∷
   rw⁻ 7 q11 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 8 q34 ∷
   rw 7 q9 ∷
   rw 8 q33 ∷
   rw 9 q9 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q11 ∷
   rw 11 q15 ∷
   rw 12 q11 ∷
   re 10 3 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q11 ∷
   rw 12 q15 ∷
   rw 13 q11 ∷
   re 11 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 12 q11 ∷
   rw 13 q16 ∷
   rw 14 q11 ∷
   re 12 3 (CK30 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q11 ∷
   rw 14 q15 ∷
   rw 15 q11 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 14 q11 ∷
   rw 15 q16 ∷
   rw 16 q11 ∷
   re 14 3 (CK30 ∷ []) ∷
   re 16 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 15 q11 ∷
   rw 16 q16 ∷
   rw 17 q11 ∷
   re 15 3 (CK30 ∷ []) ∷
   rw 16 q17 ∷
   rw 33 q35 ∷
   re 33 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 32 q19 ∷
   rw⁻ 33 q20 ∷
   rw 34 q21 ∷
   re 32 3 (CS02⁻ ∷ []) ∷
   re 34 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 33 q19 ∷
   rw⁻ 34 q20 ∷
   rw 35 q21 ∷
   re 33 3 (CS02⁻ ∷ []) ∷
   re 35 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 34 q19 ∷
   rw⁻ 35 q20 ∷
   rw 36 q21 ∷
   re 34 3 (CS02⁻ ∷ []) ∷
   re 36 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 35 q19 ∷
   rw⁻ 36 q20 ∷
   rw 37 q21 ∷
   re 35 3 (CS02⁻ ∷ []) ∷
   re 37 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 36 q19 ∷
   rw⁻ 37 q20 ∷
   rw 38 q21 ∷
   re 36 3 (CS02⁻ ∷ []) ∷
   re 38 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 37 q19 ∷
   rw⁻ 38 q20 ∷
   rw 39 q21 ∷
   re 37 3 (CS02⁻ ∷ []) ∷
   rw 38 q36 ∷
   re 40 1 (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) ∷
   rw 39 q19 ∷
   rw⁻ 40 q22 ∷
   rw 41 q21 ∷
   re 39 3 (CK20⁻ ∷ []) ∷
   re 41 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 40 q19 ∷
   rw⁻ 41 q20 ∷
   rw 42 q21 ∷
   re 40 3 (CS02⁻ ∷ []) ∷
   re 42 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 41 q19 ∷
   rw⁻ 42 q20 ∷
   rw 43 q21 ∷
   re 41 3 (CS02⁻ ∷ []) ∷
   re 43 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 42 q19 ∷
   rw⁻ 43 q20 ∷
   rw 44 q21 ∷
   re 42 3 (CS02⁻ ∷ []) ∷
   rw 17 q37 ∷
   re 17 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 16 q19 ∷
   rw⁻ 17 q20 ∷
   rw 18 q21 ∷
   re 16 3 (CS02⁻ ∷ []) ∷
   re 18 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 17 q19 ∷
   rw⁻ 18 q20 ∷
   rw 19 q21 ∷
   re 17 3 (CS02⁻ ∷ []) ∷
   re 19 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 18 q19 ∷
   rw⁻ 19 q20 ∷
   rw 20 q21 ∷
   re 18 3 (CS02⁻ ∷ []) ∷
   re 20 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 19 q19 ∷
   rw⁻ 20 q20 ∷
   rw 21 q21 ∷
   re 19 3 (CS02⁻ ∷ []) ∷
   re 21 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 20 q19 ∷
   rw⁻ 21 q20 ∷
   rw 22 q21 ∷
   re 20 3 (CS02⁻ ∷ []) ∷
   re 22 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 21 q19 ∷
   rw⁻ 22 q20 ∷
   rw 23 q21 ∷
   re 21 3 (CS02⁻ ∷ []) ∷
   rw 22 q36 ∷
   re 24 1 (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) ∷
   rw 23 q19 ∷
   rw⁻ 24 q22 ∷
   rw 25 q21 ∷
   re 23 3 (CK20⁻ ∷ []) ∷
   re 25 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 24 q19 ∷
   rw⁻ 25 q20 ∷
   rw 26 q21 ∷
   re 24 3 (CS02⁻ ∷ []) ∷
   re 26 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 25 q19 ∷
   rw⁻ 26 q20 ∷
   rw 27 q21 ∷
   re 25 3 (CS02⁻ ∷ []) ∷
   re 27 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 26 q19 ∷
   rw⁻ 27 q20 ∷
   rw 28 q21 ∷
   re 26 3 (CS02⁻ ∷ []) ∷
   rw 27 q8 ∷
   rw 26 q24 ∷
   rw 25 q24 ∷
   rw 24 q24 ∷
   rw 23 q25 ∷
   rw⁻ 22 q38 ∷
   rw 21 q24 ∷
   rw 20 q24 ∷
   rw 19 q24 ∷
   rw 18 q24 ∷
   rw 17 q24 ∷
   rw 16 q24 ∷
   re 15 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q11 ∷
   rw 16 q12 ∷ []) Eq.refl

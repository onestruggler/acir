{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D073 (W : Ws) where

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
  q2 = wE 142 W
  q3 : Eqn
  q3 = wE 31 W
  q4 : Eqn
  q4 = eqn (CK10 ∷ X3 ∷ []) (X3 ∷ CK10 ∷ []) (low-comm (CK₁₀) ((X ↑)))
  q5 : Eqn
  q5 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q6 : Eqn
  q6 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q7 : Eqn
  q7 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q8 : Eqn
  q8 = wE 537 W
  q9 : Eqn
  q9 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q10 : Eqn
  q10 = eqn (S1 ∷ CX32 ∷ []) (CX32 ∷ S1 ∷ []) (low-comm ((S ↑)) (CX₁₀))
  q11 : Eqn
  q11 = wE 5 W
  q12 : Eqn
  q12 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q14 : Eqn
  q14 = wE 140 W
  q15 : Eqn
  q15 = wE 7 W
  q16 : Eqn
  q16 = wE 538 W
  q17 : Eqn
  q17 = wE 27 W
  q18 : Eqn
  q18 = wE 576 W
  q19 : Eqn
  q19 = wE 13 W
  q20 : Eqn
  q20 = eqn (CS01⁻ ∷ CX32 ∷ []) (CX32 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₁₀))
  q21 : Eqn
  q21 = wE 78 W
  q22 : Eqn
  q22 = wE 540 W
  q23 : Eqn
  q23 = eqn (CK10⁻ ∷ CX32 ∷ []) (CX32 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q24 : Eqn
  q24 = wE 577 W
  q25 : Eqn
  q25 = wE 76 W
  q26 : Eqn
  q26 = wE 137 W
  q27 : Eqn
  q27 = eqn (Sw01 ∷ S2⁻ ∷ []) (S2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • S • S)))
  q28 : Eqn
  q28 = wE 542 W
  q29 : Eqn
  q29 = wE 29 W
  q30 : Eqn
  q30 = wE 139 W
  q31 : Eqn
  q31 = wE 1 W
  q32 : Eqn
  q32 = wE 173 W
  q33 : Eqn
  q33 = wE 3 W
  q34 : Eqn
  q34 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q35 : Eqn
  q35 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q36 : Eqn
  q36 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))

-- Bar(SSKSKK;3,1->0) passes white iX via V2 conjugates 2 part2: 500 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part2 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ CK31 ∷ Sw01 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ Sw23 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part2 = derive (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ CK31 ∷ Sw01 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ Sw23 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ [])
  (re 43 3 (CK30 ∷ []) ∷
   re 45 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   rw 45 q2 ∷
   rw 46 q1 ∷
   re 44 3 (CK30 ∷ []) ∷
   rw 45 q3 ∷
   rw 67 q4 ∷
   rw 68 q5 ∷
   rw 69 q4 ∷
   rw 66 q4 ∷
   rw 67 q5 ∷
   rw 68 q4 ∷
   rw 65 q6 ∷
   rw 66 q7 ∷
   rw 67 q6 ∷
   rw 64 q4 ∷
   rw 65 q5 ∷
   rw 66 q4 ∷
   rw 63 q6 ∷
   rw 64 q7 ∷
   rw 65 q6 ∷
   rw 62 q6 ∷
   rw 63 q7 ∷
   rw 64 q6 ∷
   rw 61 q8 ∷
   rw 60 q6 ∷
   rw 61 q7 ∷
   rw 62 q6 ∷
   rw 59 q6 ∷
   rw 60 q7 ∷
   rw 61 q6 ∷
   rw 58 q6 ∷
   rw 59 q7 ∷
   rw 60 q6 ∷
   rw 57 q6 ∷
   rw 58 q7 ∷
   rw 59 q6 ∷
   rw 56 q6 ∷
   rw 57 q7 ∷
   rw 58 q6 ∷
   rw 55 q6 ∷
   rw 56 q7 ∷
   rw 57 q6 ∷
   rw 54 q9 ∷
   rw 55 q10 ∷
   rw 56 q9 ∷
   rw 53 q4 ∷
   rw 54 q5 ∷
   rw 55 q4 ∷
   rw 52 q6 ∷
   rw 53 q7 ∷
   rw 54 q6 ∷
   rw 51 q6 ∷
   rw 52 q7 ∷
   rw 53 q6 ∷
   rw 50 q6 ∷
   rw 51 q7 ∷
   rw 52 q6 ∷
   rw 49 q9 ∷
   rw 50 q10 ∷
   rw 51 q9 ∷
   rw 48 q4 ∷
   rw 49 q5 ∷
   rw 50 q4 ∷
   rw 47 q9 ∷
   rw 48 q10 ∷
   rw 49 q9 ∷
   rw 46 q4 ∷
   rw 47 q5 ∷
   rw 48 q4 ∷
   rw 45 q8 ∷
   rw 48 q11 ∷
   rw⁻ 47 q12 ∷
   rw⁻ 46 q13 ∷
   rw⁻ 45 q12 ∷
   re 44 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q1 ∷
   rw 45 q14 ∷
   rw⁻ 44 q1 ∷
   re 45 3 (CK31 ∷ []) ∷
   re 43 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q1 ∷
   rw 44 q14 ∷
   rw⁻ 43 q1 ∷
   re 44 3 (CK31 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q1 ∷
   rw 43 q15 ∷
   rw⁻ 42 q1 ∷
   re 43 3 (CS13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q1 ∷
   rw 42 q14 ∷
   rw⁻ 41 q1 ∷
   re 42 3 (CK31 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q1 ∷
   rw 41 q15 ∷
   rw⁻ 40 q1 ∷
   re 41 3 (CS13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q1 ∷
   rw 40 q15 ∷
   rw⁻ 39 q1 ∷
   re 40 3 (CS13 ∷ []) ∷
   rw 40 q16 ∷
   rw 39 q12 ∷
   rw 40 q13 ∷
   rw 41 q12 ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   rw 43 q17 ∷
   rw 44 q1 ∷
   re 42 3 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   rw 44 q17 ∷
   rw 45 q1 ∷
   re 43 3 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   rw 45 q2 ∷
   rw 46 q1 ∷
   re 44 3 (CK30 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 45 q1 ∷
   rw 46 q17 ∷
   rw 47 q1 ∷
   re 45 3 (CS03 ∷ []) ∷
   re 47 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 46 q1 ∷
   rw 47 q2 ∷
   rw 48 q1 ∷
   re 46 3 (CK30 ∷ []) ∷
   re 48 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   rw 48 q2 ∷
   rw 49 q1 ∷
   re 47 3 (CK30 ∷ []) ∷
   rw 48 q3 ∷
   rw 65 q18 ∷
   re 65 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 64 q19 ∷
   rw⁻ 65 q20 ∷
   rw 66 q21 ∷
   re 64 3 (CS02⁻ ∷ []) ∷
   re 66 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 65 q19 ∷
   rw⁻ 66 q20 ∷
   rw 67 q21 ∷
   re 65 3 (CS02⁻ ∷ []) ∷
   re 67 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 66 q19 ∷
   rw⁻ 67 q20 ∷
   rw 68 q21 ∷
   re 66 3 (CS02⁻ ∷ []) ∷
   re 68 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 67 q19 ∷
   rw⁻ 68 q20 ∷
   rw 69 q21 ∷
   re 67 3 (CS02⁻ ∷ []) ∷
   re 69 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 68 q19 ∷
   rw⁻ 69 q20 ∷
   rw 70 q21 ∷
   re 68 3 (CS02⁻ ∷ []) ∷
   re 70 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 69 q19 ∷
   rw⁻ 70 q20 ∷
   rw 71 q21 ∷
   re 69 3 (CS02⁻ ∷ []) ∷
   rw 70 q22 ∷
   re 72 1 (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) ∷
   rw 71 q19 ∷
   rw⁻ 72 q23 ∷
   rw 73 q21 ∷
   re 71 3 (CK20⁻ ∷ []) ∷
   re 73 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 72 q19 ∷
   rw⁻ 73 q20 ∷
   rw 74 q21 ∷
   re 72 3 (CS02⁻ ∷ []) ∷
   re 74 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 73 q19 ∷
   rw⁻ 74 q20 ∷
   rw 75 q21 ∷
   re 73 3 (CS02⁻ ∷ []) ∷
   re 75 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 74 q19 ∷
   rw⁻ 75 q20 ∷
   rw 76 q21 ∷
   re 74 3 (CS02⁻ ∷ []) ∷
   rw 49 q24 ∷
   re 49 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 48 q19 ∷
   rw⁻ 49 q20 ∷
   rw 50 q21 ∷
   re 48 3 (CS02⁻ ∷ []) ∷
   re 50 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 49 q19 ∷
   rw⁻ 50 q20 ∷
   rw 51 q21 ∷
   re 49 3 (CS02⁻ ∷ []) ∷
   re 51 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 50 q19 ∷
   rw⁻ 51 q20 ∷
   rw 52 q21 ∷
   re 50 3 (CS02⁻ ∷ []) ∷
   re 52 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 51 q19 ∷
   rw⁻ 52 q20 ∷
   rw 53 q21 ∷
   re 51 3 (CS02⁻ ∷ []) ∷
   re 53 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 52 q19 ∷
   rw⁻ 53 q20 ∷
   rw 54 q21 ∷
   re 52 3 (CS02⁻ ∷ []) ∷
   re 54 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 53 q19 ∷
   rw⁻ 54 q20 ∷
   rw 55 q21 ∷
   re 53 3 (CS02⁻ ∷ []) ∷
   rw 54 q22 ∷
   re 56 1 (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) ∷
   rw 55 q19 ∷
   rw⁻ 56 q23 ∷
   rw 57 q21 ∷
   re 55 3 (CK20⁻ ∷ []) ∷
   re 57 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 56 q19 ∷
   rw⁻ 57 q20 ∷
   rw 58 q21 ∷
   re 56 3 (CS02⁻ ∷ []) ∷
   re 58 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 57 q19 ∷
   rw⁻ 58 q20 ∷
   rw 59 q21 ∷
   re 57 3 (CS02⁻ ∷ []) ∷
   re 59 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 58 q19 ∷
   rw⁻ 59 q20 ∷
   rw 60 q21 ∷
   re 58 3 (CS02⁻ ∷ []) ∷
   rw 59 q11 ∷
   rw 58 q25 ∷
   rw 57 q25 ∷
   rw 56 q25 ∷
   rw 55 q26 ∷
   rw⁻ 54 q27 ∷
   rw 53 q25 ∷
   rw 52 q25 ∷
   rw 51 q25 ∷
   rw 50 q25 ∷
   rw 49 q25 ∷
   rw 48 q25 ∷
   re 47 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q1 ∷
   rw 48 q14 ∷
   rw⁻ 47 q1 ∷
   re 48 3 (CK31 ∷ []) ∷
   re 46 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q1 ∷
   rw 47 q14 ∷
   rw⁻ 46 q1 ∷
   re 47 3 (CK31 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q1 ∷
   rw 46 q15 ∷
   rw⁻ 45 q1 ∷
   re 46 3 (CS13 ∷ []) ∷
   re 44 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q1 ∷
   rw 45 q14 ∷
   rw⁻ 44 q1 ∷
   re 45 3 (CK31 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q1 ∷
   rw 44 q15 ∷
   rw⁻ 43 q1 ∷
   re 44 3 (CS13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q1 ∷
   rw 43 q15 ∷
   rw⁻ 42 q1 ∷
   re 43 3 (CS13 ∷ []) ∷
   rw 43 q28 ∷
   rw 42 q29 ∷
   rw 43 q29 ∷
   rw 44 q29 ∷
   rw 45 q29 ∷
   rw 46 q29 ∷
   rw 47 q29 ∷
   rw 48 q27 ∷
   rw 49 q30 ∷
   rw 50 q29 ∷
   rw 51 q29 ∷
   rw 52 q29 ∷
   re 54 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 53 q1 ∷
   rw 54 q17 ∷
   rw 55 q1 ∷
   re 53 3 (CS03 ∷ []) ∷
   re 55 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 54 q1 ∷
   rw 55 q17 ∷
   rw 56 q1 ∷
   re 54 3 (CS03 ∷ []) ∷
   re 56 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 55 q1 ∷
   rw 56 q2 ∷
   rw 57 q1 ∷
   re 55 3 (CK30 ∷ []) ∷
   re 57 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 56 q1 ∷
   rw 57 q17 ∷
   rw 58 q1 ∷
   re 56 3 (CS03 ∷ []) ∷
   re 58 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 57 q1 ∷
   rw 58 q2 ∷
   rw 59 q1 ∷
   re 57 3 (CK30 ∷ []) ∷
   re 59 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 58 q1 ∷
   rw 59 q2 ∷
   rw 60 q1 ∷
   re 58 3 (CK30 ∷ []) ∷
   rw 59 q3 ∷
   rw 81 q4 ∷
   rw 82 q5 ∷
   rw 83 q4 ∷
   rw 80 q4 ∷
   rw 81 q5 ∷
   rw 82 q4 ∷
   rw 79 q6 ∷
   rw 80 q7 ∷
   rw 81 q6 ∷
   rw 78 q4 ∷
   rw 79 q5 ∷
   rw 80 q4 ∷
   rw 77 q6 ∷
   rw 78 q7 ∷
   rw 79 q6 ∷
   rw 76 q6 ∷
   rw 77 q7 ∷
   rw 78 q6 ∷
   rw 75 q8 ∷
   rw 74 q6 ∷
   rw 75 q7 ∷
   rw 76 q6 ∷
   rw 73 q6 ∷
   rw 74 q7 ∷
   rw 75 q6 ∷
   rw 72 q6 ∷
   rw 73 q7 ∷
   rw 74 q6 ∷
   rw 71 q6 ∷
   rw 72 q7 ∷
   rw 73 q6 ∷
   rw 70 q6 ∷
   rw 71 q7 ∷
   rw 72 q6 ∷
   rw 69 q6 ∷
   rw 70 q7 ∷
   rw 71 q6 ∷
   rw 68 q9 ∷
   rw 69 q10 ∷
   rw 70 q9 ∷
   rw 67 q4 ∷
   rw 68 q5 ∷
   rw 69 q4 ∷
   rw 66 q6 ∷
   rw 67 q7 ∷
   rw 68 q6 ∷
   rw 65 q6 ∷
   rw 66 q7 ∷
   rw 67 q6 ∷
   rw 64 q6 ∷
   rw 65 q7 ∷
   rw 66 q6 ∷
   rw 63 q9 ∷
   rw 64 q10 ∷
   rw 65 q9 ∷
   rw 62 q4 ∷
   rw 63 q5 ∷
   rw 64 q4 ∷
   rw 61 q9 ∷
   rw 62 q10 ∷
   rw 63 q9 ∷
   rw 60 q4 ∷
   rw 61 q5 ∷
   rw 62 q4 ∷
   rw 59 q8 ∷
   rw 62 q11 ∷
   rw⁻ 61 q12 ∷
   rw⁻ 60 q13 ∷
   rw⁻ 59 q12 ∷
   re 58 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 60 q1 ∷
   rw 59 q14 ∷
   rw⁻ 58 q1 ∷
   re 59 3 (CK31 ∷ []) ∷
   re 57 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 59 q1 ∷
   rw 58 q14 ∷
   rw⁻ 57 q1 ∷
   re 58 3 (CK31 ∷ []) ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 58 q1 ∷
   rw 57 q15 ∷
   rw⁻ 56 q1 ∷
   re 57 3 (CS13 ∷ []) ∷
   re 55 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 57 q1 ∷
   rw 56 q14 ∷
   rw⁻ 55 q1 ∷
   re 56 3 (CK31 ∷ []) ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 56 q1 ∷
   rw 55 q15 ∷
   rw⁻ 54 q1 ∷
   re 55 3 (CS13 ∷ []) ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 55 q1 ∷
   rw 54 q15 ∷
   rw⁻ 53 q1 ∷
   re 54 3 (CS13 ∷ []) ∷
   rw 54 q16 ∷
   rw 53 q12 ∷
   rw 54 q13 ∷
   rw 55 q12 ∷
   re 57 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 56 q1 ∷
   rw 57 q17 ∷
   rw 58 q1 ∷
   re 56 3 (CS03 ∷ []) ∷
   re 58 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 57 q1 ∷
   rw 58 q17 ∷
   rw 59 q1 ∷
   re 57 3 (CS03 ∷ []) ∷
   re 59 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 58 q1 ∷
   rw 59 q2 ∷
   rw 60 q1 ∷
   re 58 3 (CK30 ∷ []) ∷
   re 60 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 59 q1 ∷
   rw 60 q17 ∷
   rw 61 q1 ∷
   re 59 3 (CS03 ∷ []) ∷
   re 61 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 60 q1 ∷
   rw 61 q2 ∷
   rw 62 q1 ∷
   re 60 3 (CK30 ∷ []) ∷
   re 62 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 61 q1 ∷
   rw 62 q2 ∷
   rw 63 q1 ∷
   re 61 3 (CK30 ∷ []) ∷
   rw 62 q3 ∷
   rw 91 q31 ∷
   rw 90 q32 ∷
   re 89 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 91 q33 ∷
   re 88 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 90 q33 ∷
   re 87 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 89 q33 ∷
   re 86 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 88 q33 ∷
   rw 85 q32 ∷
   rw 84 q34 ∷
   rw 83 q34 ∷
   rw 82 q35 ∷
   rw 81 q34 ∷
   rw 80 q35 ∷
   rw 79 q35 ∷
   re 78 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 80 q33 ∷
   rw 77 q35 ∷
   rw 76 q35 ∷
   rw 75 q35 ∷
   rw 74 q35 ∷
   rw 73 q35 ∷
   rw 72 q35 ∷
   rw 71 q36 ∷
   rw 70 q34 ∷
   rw 69 q35 ∷
   rw 68 q35 ∷
   rw 67 q35 ∷
   rw 66 q36 ∷
   rw 65 q34 ∷
   rw 64 q36 ∷
   rw 63 q34 ∷
   re 62 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 64 q33 ∷ []) Eq.refl

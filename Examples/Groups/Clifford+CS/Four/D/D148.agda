{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D148 (W : Ws) where

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
  q1 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q2 : Eqn
  q2 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q3 : Eqn
  q3 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q4 : Eqn
  q4 = wE 728 W
  q5 : Eqn
  q5 = wE 1 W
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 13 W
  q8 : Eqn
  q8 = eqn (CS01⁻ ∷ CX32 ∷ []) (CX32 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₁₀))
  q9 : Eqn
  q9 = wE 78 W
  q10 : Eqn
  q10 = eqn (CK10⁻ ∷ CX32 ∷ []) (CX32 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q11 : Eqn
  q11 = wE 5 W
  q12 : Eqn
  q12 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q13 : Eqn
  q13 = wE 76 W
  q14 : Eqn
  q14 = wE 137 W
  q15 : Eqn
  q15 = wE 7 W
  q16 : Eqn
  q16 = wE 140 W
  q17 : Eqn
  q17 = wE 729 W
  q18 : Eqn
  q18 = wE 29 W
  q19 : Eqn
  q19 = wE 139 W
  q20 : Eqn
  q20 = wE 27 W
  q21 : Eqn
  q21 = wE 142 W
  q22 : Eqn
  q22 = wE 31 W
  q23 : Eqn
  q23 = eqn (CS01 ∷ X2 ∷ []) (X2 ∷ CS01 ∷ []) (low-comm (CS) (X))
  q24 : Eqn
  q24 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q25 : Eqn
  q25 = eqn (CK10 ∷ X2 ∷ []) (X2 ∷ CK10 ∷ []) (low-comm (CK₁₀) (X))
  q26 : Eqn
  q26 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q27 : Eqn
  q27 = wE 612 W
  q28 : Eqn
  q28 = eqn (S1 ∷ X2 ∷ []) (X2 ∷ S1 ∷ []) (low-comm ((S ↑)) (X))
  q29 : Eqn
  q29 = eqn (S1 ∷ CX23 ∷ []) (CX23 ∷ S1 ∷ []) (low-comm ((S ↑)) (CX₀₁))
  q30 : Eqn
  q30 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q31 : Eqn
  q31 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q32 : Eqn
  q32 = wE 661 W
  q33 : Eqn
  q33 = wE 689 W
  q34 : Eqn
  q34 = wE 730 W
  q35 : Eqn
  q35 = wE 153 W
  q36 : Eqn
  q36 = eqn (CX21 ∷ S3⁻ ∷ []) (S3⁻ ∷ CX21 ∷ []) (low₃-comm ((CX₁₀ ↑)) ((S • S • S)))
  q37 : Eqn
  q37 = wE 731 W

-- Bar(SSSKSS;2,1->0) passes white iX via V2 conjugates 3 part2: 500 steps
lem-Bar⟨SSSKSS21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part2 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sw23 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ Sw23 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part2 = derive (X2 ∷ CS23⁻ ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sw23 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ Sw23 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS23⁻ ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ [])
  (rw 58 q1 ∷
   rw 57 q1 ∷
   rw 56 q1 ∷
   rw 55 q1 ∷
   rw 54 q1 ∷
   rw 53 q1 ∷
   rw 52 q1 ∷
   rw 51 q1 ∷
   rw 50 q1 ∷
   rw 49 q2 ∷
   rw 48 q3 ∷
   rw 47 q1 ∷
   rw 46 q1 ∷
   rw 45 q1 ∷
   rw 44 q1 ∷
   rw 43 q1 ∷
   rw 42 q1 ∷
   rw 43 q4 ∷
   rw 44 q5 ∷
   re 42 3 (CS03⁻ ∷ []) ∷
   rw 45 q5 ∷
   re 43 3 (CK30⁻ ∷ []) ∷
   rw 46 q5 ∷
   re 44 3 (CS03⁻ ∷ []) ∷
   rw 47 q5 ∷
   re 45 3 (CS03⁻ ∷ []) ∷
   rw⁻ 46 q1 ∷
   rw⁻ 47 q1 ∷
   rw⁻ 48 q1 ∷
   rw⁻ 49 q1 ∷
   rw⁻ 50 q1 ∷
   rw⁻ 51 q1 ∷
   rw⁻ 52 q3 ∷
   rw⁻ 53 q2 ∷
   rw⁻ 54 q1 ∷
   rw⁻ 55 q1 ∷
   rw⁻ 56 q1 ∷
   rw⁻ 57 q1 ∷
   rw⁻ 58 q1 ∷
   rw⁻ 59 q1 ∷
   rw⁻ 60 q1 ∷
   rw⁻ 61 q1 ∷
   rw⁻ 62 q1 ∷
   rw 63 q6 ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q5 ∷
   re 42 3 (CX31 ∷ []) ∷
   rw 42 q7 ∷
   rw⁻ 43 q8 ∷
   rw 44 q9 ∷
   re 45 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 47 q6 ∷
   re 41 5 (CS03⁻ ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q5 ∷
   re 43 3 (CX31 ∷ []) ∷
   rw 43 q7 ∷
   rw⁻ 44 q10 ∷
   rw 45 q9 ∷
   re 46 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 48 q6 ∷
   re 42 5 (CK30⁻ ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q5 ∷
   re 44 3 (CX31 ∷ []) ∷
   rw 44 q7 ∷
   rw⁻ 45 q8 ∷
   rw 46 q9 ∷
   re 47 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 49 q6 ∷
   re 43 5 (CS03⁻ ∷ []) ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q5 ∷
   re 45 3 (CX31 ∷ []) ∷
   rw 45 q7 ∷
   rw⁻ 46 q8 ∷
   rw 47 q9 ∷
   re 48 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 50 q6 ∷
   re 44 5 (CS03⁻ ∷ []) ∷
   rw 45 q11 ∷
   re 44 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q12 ∷
   rw 45 q13 ∷
   rw⁻ 44 q12 ∷
   re 45 3 (CS13⁻ ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q12 ∷
   rw 44 q13 ∷
   rw⁻ 43 q12 ∷
   re 44 3 (CS13⁻ ∷ []) ∷
   re 42 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q12 ∷
   rw 43 q14 ∷
   rw⁻ 42 q12 ∷
   re 43 3 (CK31⁻ ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q12 ∷
   rw 42 q13 ∷
   rw⁻ 41 q12 ∷
   re 42 3 (CS13⁻ ∷ []) ∷
   rw 40 q15 ∷
   rw 39 q15 ∷
   rw 38 q16 ∷
   rw 37 q15 ∷
   rw 36 q15 ∷
   rw 35 q15 ∷
   rw 36 q17 ∷
   re 36 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 35 q12 ∷
   rw 36 q18 ∷
   rw 37 q12 ∷
   re 35 3 (CS03⁻ ∷ []) ∷
   re 37 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 36 q12 ∷
   rw 37 q19 ∷
   rw 38 q12 ∷
   re 36 3 (CK30⁻ ∷ []) ∷
   re 38 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 37 q12 ∷
   rw 38 q18 ∷
   rw 39 q12 ∷
   re 37 3 (CS03⁻ ∷ []) ∷
   re 39 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 38 q12 ∷
   rw 39 q18 ∷
   rw 40 q12 ∷
   re 38 3 (CS03⁻ ∷ []) ∷
   rw 39 q20 ∷
   rw 40 q20 ∷
   rw 41 q20 ∷
   rw 42 q21 ∷
   rw 43 q20 ∷
   rw 44 q20 ∷
   rw 45 q22 ∷
   rw 69 q23 ∷
   rw 70 q24 ∷
   rw 71 q23 ∷
   rw 68 q23 ∷
   rw 69 q24 ∷
   rw 70 q23 ∷
   rw 67 q25 ∷
   rw 68 q26 ∷
   rw 69 q25 ∷
   rw 66 q23 ∷
   rw 67 q24 ∷
   rw 68 q23 ∷
   rw 65 q23 ∷
   rw 66 q24 ∷
   rw 67 q23 ∷
   rw 64 q23 ∷
   rw 65 q24 ∷
   rw 66 q23 ∷
   rw 63 q27 ∷
   rw 62 q23 ∷
   rw 63 q24 ∷
   rw 64 q23 ∷
   rw 61 q23 ∷
   rw 62 q24 ∷
   rw 63 q23 ∷
   rw 60 q23 ∷
   rw 61 q24 ∷
   rw 62 q23 ∷
   rw 59 q23 ∷
   rw 60 q24 ∷
   rw 61 q23 ∷
   rw 58 q23 ∷
   rw 59 q24 ∷
   rw 60 q23 ∷
   rw 57 q23 ∷
   rw 58 q24 ∷
   rw 59 q23 ∷
   rw 56 q23 ∷
   rw 57 q24 ∷
   rw 58 q23 ∷
   rw 55 q23 ∷
   rw 56 q24 ∷
   rw 57 q23 ∷
   rw 54 q23 ∷
   rw 55 q24 ∷
   rw 56 q23 ∷
   rw 53 q28 ∷
   rw 54 q29 ∷
   rw 55 q28 ∷
   rw 52 q25 ∷
   rw 53 q26 ∷
   rw 54 q25 ∷
   rw 51 q23 ∷
   rw 52 q24 ∷
   rw 53 q23 ∷
   rw 50 q23 ∷
   rw 51 q24 ∷
   rw 52 q23 ∷
   rw 49 q23 ∷
   rw 50 q24 ∷
   rw 51 q23 ∷
   rw 48 q23 ∷
   rw 49 q24 ∷
   rw 50 q23 ∷
   rw 47 q23 ∷
   rw 48 q24 ∷
   rw 49 q23 ∷
   rw 46 q23 ∷
   rw 47 q24 ∷
   rw 48 q23 ∷
   rw 45 q27 ∷
   rw 48 q11 ∷
   rw⁻ 47 q30 ∷
   rw⁻ 46 q31 ∷
   rw⁻ 45 q30 ∷
   rw 44 q15 ∷
   rw 43 q15 ∷
   rw 42 q16 ∷
   rw 41 q15 ∷
   rw 40 q15 ∷
   rw 39 q15 ∷
   rw 40 q32 ∷
   rw 39 q30 ∷
   rw 40 q31 ∷
   rw 41 q30 ∷
   rw 42 q20 ∷
   rw 43 q20 ∷
   rw 44 q20 ∷
   rw 45 q21 ∷
   rw 46 q20 ∷
   rw 47 q20 ∷
   rw 48 q22 ∷
   rw 84 q5 ∷
   re 83 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 85 q6 ∷
   re 82 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 84 q6 ∷
   re 81 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 83 q6 ∷
   re 80 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 82 q6 ∷
   rw 79 q33 ∷
   re 78 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 80 q6 ∷
   re 77 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 79 q6 ∷
   re 76 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 78 q6 ∷
   re 75 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 77 q6 ∷
   re 74 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 76 q6 ∷
   re 73 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 75 q6 ∷
   rw 72 q1 ∷
   rw 71 q1 ∷
   rw 70 q3 ∷
   rw 69 q1 ∷
   rw 68 q1 ∷
   rw 67 q1 ∷
   rw 68 q34 ∷
   rw 69 q5 ∷
   re 67 3 (CS03⁻ ∷ []) ∷
   rw 70 q5 ∷
   re 68 3 (CS03⁻ ∷ []) ∷
   rw 71 q5 ∷
   re 69 3 (CS03⁻ ∷ []) ∷
   rw 72 q5 ∷
   re 70 3 (CS03⁻ ∷ []) ∷
   rw 73 q5 ∷
   re 71 3 (CS03⁻ ∷ []) ∷
   rw 74 q5 ∷
   re 72 3 (CS03⁻ ∷ []) ∷
   rw 73 q35 ∷
   rw 76 q5 ∷
   re 74 3 (CK30⁻ ∷ []) ∷
   rw 77 q5 ∷
   re 75 3 (CS03⁻ ∷ []) ∷
   rw 78 q5 ∷
   re 76 3 (CS03⁻ ∷ []) ∷
   rw 79 q5 ∷
   re 77 3 (CS03⁻ ∷ []) ∷
   rw⁻ 78 q1 ∷
   rw⁻ 79 q1 ∷
   rw⁻ 80 q1 ∷
   rw⁻ 81 q3 ∷
   rw⁻ 82 q1 ∷
   rw⁻ 83 q1 ∷
   rw 84 q6 ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 66 q5 ∷
   re 67 3 (CX31 ∷ []) ∷
   rw 67 q7 ∷
   rw⁻ 68 q8 ∷
   rw 69 q9 ∷
   re 70 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 72 q6 ∷
   re 66 5 (CS03⁻ ∷ []) ∷
   re 68 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 67 q5 ∷
   re 68 3 (CX31 ∷ []) ∷
   rw 68 q7 ∷
   rw⁻ 69 q8 ∷
   rw 70 q9 ∷
   re 71 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 73 q6 ∷
   re 67 5 (CS03⁻ ∷ []) ∷
   re 69 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 68 q5 ∷
   re 69 3 (CX31 ∷ []) ∷
   rw 69 q7 ∷
   rw⁻ 70 q8 ∷
   rw 71 q9 ∷
   re 72 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 74 q6 ∷
   re 68 5 (CS03⁻ ∷ []) ∷
   re 70 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 69 q5 ∷
   re 70 3 (CX31 ∷ []) ∷
   rw 70 q7 ∷
   rw⁻ 71 q8 ∷
   rw 72 q9 ∷
   re 73 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 75 q6 ∷
   re 69 5 (CS03⁻ ∷ []) ∷
   re 71 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 70 q5 ∷
   re 71 3 (CX31 ∷ []) ∷
   rw 71 q7 ∷
   rw⁻ 72 q8 ∷
   rw 73 q9 ∷
   re 74 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 76 q6 ∷
   re 70 5 (CS03⁻ ∷ []) ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q5 ∷
   re 72 3 (CX31 ∷ []) ∷
   rw 72 q7 ∷
   rw⁻ 73 q8 ∷
   rw 74 q9 ∷
   re 75 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 77 q6 ∷
   re 71 5 (CS03⁻ ∷ []) ∷
   rw 72 q36 ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q5 ∷
   re 74 3 (CX31 ∷ []) ∷
   rw 74 q7 ∷
   rw⁻ 75 q10 ∷
   rw 76 q9 ∷
   re 77 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 79 q6 ∷
   re 73 5 (CK30⁻ ∷ []) ∷
   re 75 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 74 q5 ∷
   re 75 3 (CX31 ∷ []) ∷
   rw 75 q7 ∷
   rw⁻ 76 q8 ∷
   rw 77 q9 ∷
   re 78 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 80 q6 ∷
   re 74 5 (CS03⁻ ∷ []) ∷
   re 76 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 75 q5 ∷
   re 76 3 (CX31 ∷ []) ∷
   rw 76 q7 ∷
   rw⁻ 77 q8 ∷
   rw 78 q9 ∷
   re 79 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 81 q6 ∷
   re 75 5 (CS03⁻ ∷ []) ∷
   re 77 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 76 q5 ∷
   re 77 3 (CX31 ∷ []) ∷
   rw 77 q7 ∷
   rw⁻ 78 q8 ∷
   rw 79 q9 ∷
   re 80 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 82 q6 ∷
   re 76 5 (CS03⁻ ∷ []) ∷
   rw 77 q5 ∷
   re 76 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 78 q6 ∷
   re 75 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 77 q6 ∷
   re 74 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 76 q6 ∷
   re 73 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 75 q6 ∷
   rw 72 q33 ∷
   re 71 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 73 q6 ∷
   re 70 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 72 q6 ∷
   re 69 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 71 q6 ∷
   re 68 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 70 q6 ∷
   re 67 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 69 q6 ∷
   re 66 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 68 q6 ∷
   rw 65 q1 ∷
   rw 64 q1 ∷
   rw 63 q1 ∷
   rw 62 q1 ∷
   rw 61 q1 ∷
   rw 60 q1 ∷
   rw 59 q1 ∷
   rw 58 q1 ∷
   rw 57 q1 ∷
   rw 56 q2 ∷
   rw 55 q3 ∷
   rw 54 q1 ∷
   rw 53 q1 ∷
   rw 52 q1 ∷
   rw 51 q1 ∷
   rw 50 q1 ∷
   rw 49 q1 ∷
   rw 50 q37 ∷
   rw 51 q5 ∷
   re 49 3 (CS03⁻ ∷ []) ∷
   rw 52 q5 ∷
   re 50 3 (CS03⁻ ∷ []) ∷
   rw 53 q5 ∷
   re 51 3 (CS03⁻ ∷ []) ∷
   rw 54 q5 ∷
   re 52 3 (CS03⁻ ∷ []) ∷
   rw 55 q5 ∷
   re 53 3 (CS03⁻ ∷ []) ∷
   rw 56 q5 ∷
   re 54 3 (CS03⁻ ∷ []) ∷
   rw 55 q35 ∷
   rw 58 q5 ∷
   re 56 3 (CK30⁻ ∷ []) ∷
   rw 59 q5 ∷
   re 57 3 (CS03⁻ ∷ []) ∷
   rw 60 q5 ∷
   re 58 3 (CS03⁻ ∷ []) ∷
   rw 61 q5 ∷
   re 59 3 (CS03⁻ ∷ []) ∷
   rw⁻ 60 q1 ∷
   rw⁻ 61 q1 ∷
   rw⁻ 62 q1 ∷
   rw⁻ 63 q1 ∷
   rw⁻ 64 q1 ∷
   rw⁻ 65 q1 ∷
   rw⁻ 66 q3 ∷
   rw⁻ 67 q2 ∷
   rw⁻ 68 q1 ∷
   rw⁻ 69 q1 ∷
   rw⁻ 70 q1 ∷
   rw⁻ 71 q1 ∷
   rw⁻ 72 q1 ∷
   rw⁻ 73 q1 ∷
   rw⁻ 74 q1 ∷
   rw⁻ 75 q1 ∷
   rw⁻ 76 q1 ∷
   rw 77 q6 ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q5 ∷
   re 49 3 (CX31 ∷ []) ∷
   rw 49 q7 ∷
   rw⁻ 50 q8 ∷
   rw 51 q9 ∷
   re 52 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 54 q6 ∷
   re 48 5 (CS03⁻ ∷ []) ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q5 ∷
   re 50 3 (CX31 ∷ []) ∷
   rw 50 q7 ∷
   rw⁻ 51 q8 ∷
   rw 52 q9 ∷
   re 53 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 55 q6 ∷
   re 49 5 (CS03⁻ ∷ []) ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q5 ∷
   re 51 3 (CX31 ∷ []) ∷
   rw 51 q7 ∷
   rw⁻ 52 q8 ∷
   rw 53 q9 ∷
   re 54 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 56 q6 ∷
   re 50 5 (CS03⁻ ∷ []) ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q5 ∷
   re 52 3 (CX31 ∷ []) ∷
   rw 52 q7 ∷
   rw⁻ 53 q8 ∷
   rw 54 q9 ∷
   re 55 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 57 q6 ∷
   re 51 5 (CS03⁻ ∷ []) ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q5 ∷
   re 53 3 (CX31 ∷ []) ∷
   rw 53 q7 ∷
   rw⁻ 54 q8 ∷
   rw 55 q9 ∷
   re 56 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 58 q6 ∷
   re 52 5 (CS03⁻ ∷ []) ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷ []) Eq.refl

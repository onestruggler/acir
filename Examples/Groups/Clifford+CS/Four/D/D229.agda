{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D229 (W : Ws) where

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
  q3 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q4 : Eqn
  q4 = wE 140 W
  q5 : Eqn
  q5 = wE 818 W
  q6 : Eqn
  q6 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q7 : Eqn
  q7 = wE 29 W
  q8 : Eqn
  q8 = wE 139 W
  q9 : Eqn
  q9 = wE 27 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q12 : Eqn
  q12 = wE 31 W
  q13 : Eqn
  q13 = wE 5 W
  q14 : Eqn
  q14 = wE 76 W
  q15 : Eqn
  q15 = wE 820 W

-- Bar(SSSKSS;2,3->0) passes white iX via V2 conjugates 1 part11: 396 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part11 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ Sw01 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part11 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ Sw01 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (re 66 3 (CS13 ∷ []) ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 66 q1 ∷
   rw 65 q2 ∷
   rw⁻ 64 q1 ∷
   re 65 3 (CS13 ∷ []) ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 65 q1 ∷
   rw 64 q2 ∷
   rw⁻ 63 q1 ∷
   re 64 3 (CS13 ∷ []) ∷
   rw⁻ 62 q3 ∷
   rw 61 q2 ∷
   rw 60 q2 ∷
   rw 59 q4 ∷
   rw 58 q2 ∷
   rw 57 q2 ∷
   rw 56 q2 ∷
   rw 57 q5 ∷
   rw 56 q6 ∷
   rw 57 q7 ∷
   rw 58 q8 ∷
   rw 59 q7 ∷
   rw 60 q7 ∷
   rw 61 q6 ∷
   rw 62 q9 ∷
   rw 63 q9 ∷
   rw 64 q9 ∷
   rw 65 q10 ∷
   rw 66 q9 ∷
   rw 67 q9 ∷
   rw 68 q3 ∷
   re 70 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 69 q1 ∷
   rw 70 q9 ∷
   rw 71 q1 ∷
   re 69 3 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 70 q1 ∷
   rw 71 q9 ∷
   rw 72 q1 ∷
   re 70 3 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 71 q1 ∷
   rw 72 q9 ∷
   rw 73 q1 ∷
   re 71 3 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 72 q1 ∷
   rw 73 q9 ∷
   rw 74 q1 ∷
   re 72 3 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 73 q1 ∷
   rw 74 q9 ∷
   rw 75 q1 ∷
   re 73 3 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 74 q1 ∷
   rw 75 q9 ∷
   rw 76 q1 ∷
   re 74 3 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 75 q1 ∷
   rw 76 q10 ∷
   rw 77 q1 ∷
   re 75 3 (CK30 ∷ []) ∷
   rw 76 q11 ∷
   re 78 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 77 q1 ∷
   rw 78 q9 ∷
   rw 79 q1 ∷
   re 77 3 (CS03 ∷ []) ∷
   re 79 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 78 q1 ∷
   rw 79 q9 ∷
   rw 80 q1 ∷
   re 78 3 (CS03 ∷ []) ∷
   re 80 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 79 q1 ∷
   rw 80 q9 ∷
   rw 81 q1 ∷
   re 79 3 (CS03 ∷ []) ∷
   re 81 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 80 q1 ∷
   rw 81 q9 ∷
   rw 82 q1 ∷
   re 80 3 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 81 q1 ∷
   rw 82 q9 ∷
   rw 83 q1 ∷
   re 81 3 (CS03 ∷ []) ∷
   re 83 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 82 q1 ∷
   rw 83 q9 ∷
   rw 84 q1 ∷
   re 82 3 (CS03 ∷ []) ∷
   re 84 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 83 q1 ∷
   rw 84 q9 ∷
   rw 85 q1 ∷
   re 83 3 (CS03 ∷ []) ∷
   re 85 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 84 q1 ∷
   rw 85 q9 ∷
   rw 86 q1 ∷
   re 84 3 (CS03 ∷ []) ∷
   re 86 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 85 q1 ∷
   rw 86 q9 ∷
   rw 87 q1 ∷
   re 85 3 (CS03 ∷ []) ∷
   rw 86 q3 ∷
   re 88 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 87 q1 ∷
   rw 88 q9 ∷
   rw 89 q1 ∷
   re 87 3 (CS03 ∷ []) ∷
   re 89 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 88 q1 ∷
   rw 89 q9 ∷
   rw 90 q1 ∷
   re 88 3 (CS03 ∷ []) ∷
   re 90 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 89 q1 ∷
   rw 90 q9 ∷
   rw 91 q1 ∷
   re 89 3 (CS03 ∷ []) ∷
   re 91 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 90 q1 ∷
   rw 91 q10 ∷
   rw 92 q1 ∷
   re 90 3 (CK30 ∷ []) ∷
   re 92 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 91 q1 ∷
   rw 92 q9 ∷
   rw 93 q1 ∷
   re 91 3 (CS03 ∷ []) ∷
   re 93 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 92 q1 ∷
   rw 93 q9 ∷
   rw 94 q1 ∷
   re 92 3 (CS03 ∷ []) ∷
   rw 93 q12 ∷
   rw 98 q13 ∷
   rw⁻ 97 q6 ∷
   rw 96 q14 ∷
   rw 95 q14 ∷
   rw 94 q14 ∷
   rw⁻ 93 q6 ∷
   re 92 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 94 q1 ∷
   rw 93 q2 ∷
   rw⁻ 92 q1 ∷
   re 93 3 (CS13 ∷ []) ∷
   re 91 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 93 q1 ∷
   rw 92 q2 ∷
   rw⁻ 91 q1 ∷
   re 92 3 (CS13 ∷ []) ∷
   re 90 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 92 q1 ∷
   rw 91 q4 ∷
   rw⁻ 90 q1 ∷
   re 91 3 (CK31 ∷ []) ∷
   re 89 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 91 q1 ∷
   rw 90 q2 ∷
   rw⁻ 89 q1 ∷
   re 90 3 (CS13 ∷ []) ∷
   re 88 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 90 q1 ∷
   rw 89 q2 ∷
   rw⁻ 88 q1 ∷
   re 89 3 (CS13 ∷ []) ∷
   re 87 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 89 q1 ∷
   rw 88 q2 ∷
   rw⁻ 87 q1 ∷
   re 88 3 (CS13 ∷ []) ∷
   rw⁻ 86 q3 ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 87 q1 ∷
   rw 86 q2 ∷
   rw⁻ 85 q1 ∷
   re 86 3 (CS13 ∷ []) ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 86 q1 ∷
   rw 85 q2 ∷
   rw⁻ 84 q1 ∷
   re 85 3 (CS13 ∷ []) ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 85 q1 ∷
   rw 84 q2 ∷
   rw⁻ 83 q1 ∷
   re 84 3 (CS13 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 84 q1 ∷
   rw 83 q2 ∷
   rw⁻ 82 q1 ∷
   re 83 3 (CS13 ∷ []) ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 83 q1 ∷
   rw 82 q2 ∷
   rw⁻ 81 q1 ∷
   re 82 3 (CS13 ∷ []) ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 82 q1 ∷
   rw 81 q2 ∷
   rw⁻ 80 q1 ∷
   re 81 3 (CS13 ∷ []) ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 81 q1 ∷
   rw 80 q2 ∷
   rw⁻ 79 q1 ∷
   re 80 3 (CS13 ∷ []) ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 80 q1 ∷
   rw 79 q2 ∷
   rw⁻ 78 q1 ∷
   re 79 3 (CS13 ∷ []) ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 79 q1 ∷
   rw 78 q2 ∷
   rw⁻ 77 q1 ∷
   re 78 3 (CS13 ∷ []) ∷
   rw⁻ 76 q11 ∷
   re 75 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 77 q1 ∷
   rw 76 q4 ∷
   rw⁻ 75 q1 ∷
   re 76 3 (CK31 ∷ []) ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 76 q1 ∷
   rw 75 q2 ∷
   rw⁻ 74 q1 ∷
   re 75 3 (CS13 ∷ []) ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 75 q1 ∷
   rw 74 q2 ∷
   rw⁻ 73 q1 ∷
   re 74 3 (CS13 ∷ []) ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 74 q1 ∷
   rw 73 q2 ∷
   rw⁻ 72 q1 ∷
   re 73 3 (CS13 ∷ []) ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 73 q1 ∷
   rw 72 q2 ∷
   rw⁻ 71 q1 ∷
   re 72 3 (CS13 ∷ []) ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 72 q1 ∷
   rw 71 q2 ∷
   rw⁻ 70 q1 ∷
   re 71 3 (CS13 ∷ []) ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 71 q1 ∷
   rw 70 q2 ∷
   rw⁻ 69 q1 ∷
   re 70 3 (CS13 ∷ []) ∷
   rw⁻ 68 q3 ∷
   rw 67 q2 ∷
   rw 66 q2 ∷
   rw 65 q4 ∷
   rw 64 q2 ∷
   rw 63 q2 ∷
   rw 62 q2 ∷
   rw 63 q15 ∷
   rw 62 q6 ∷
   rw 63 q7 ∷
   rw 64 q7 ∷
   rw 65 q7 ∷
   rw 66 q6 ∷
   rw 67 q9 ∷
   rw 68 q9 ∷
   rw 69 q9 ∷
   rw 70 q10 ∷
   rw 71 q9 ∷
   rw 72 q9 ∷
   rw 73 q3 ∷
   re 75 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 74 q1 ∷
   rw 75 q9 ∷
   rw 76 q1 ∷
   re 74 3 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 75 q1 ∷
   rw 76 q9 ∷
   rw 77 q1 ∷
   re 75 3 (CS03 ∷ []) ∷
   re 77 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 76 q1 ∷
   rw 77 q9 ∷
   rw 78 q1 ∷
   re 76 3 (CS03 ∷ []) ∷
   re 78 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 77 q1 ∷
   rw 78 q9 ∷
   rw 79 q1 ∷
   re 77 3 (CS03 ∷ []) ∷
   re 79 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 78 q1 ∷
   rw 79 q9 ∷
   rw 80 q1 ∷
   re 78 3 (CS03 ∷ []) ∷
   re 80 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 79 q1 ∷
   rw 80 q9 ∷
   rw 81 q1 ∷
   re 79 3 (CS03 ∷ []) ∷
   re 81 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 80 q1 ∷
   rw 81 q10 ∷
   rw 82 q1 ∷
   re 80 3 (CK30 ∷ []) ∷
   rw 81 q11 ∷
   re 83 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 82 q1 ∷
   rw 83 q9 ∷
   rw 84 q1 ∷
   re 82 3 (CS03 ∷ []) ∷
   re 84 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 83 q1 ∷
   rw 84 q9 ∷
   rw 85 q1 ∷
   re 83 3 (CS03 ∷ []) ∷
   re 85 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 84 q1 ∷
   rw 85 q9 ∷
   rw 86 q1 ∷
   re 84 3 (CS03 ∷ []) ∷
   re 86 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 85 q1 ∷
   rw 86 q9 ∷
   rw 87 q1 ∷
   re 85 3 (CS03 ∷ []) ∷
   re 87 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 86 q1 ∷
   rw 87 q9 ∷
   rw 88 q1 ∷
   re 86 3 (CS03 ∷ []) ∷
   re 88 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 87 q1 ∷
   rw 88 q9 ∷
   rw 89 q1 ∷
   re 87 3 (CS03 ∷ []) ∷
   re 89 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 88 q1 ∷
   rw 89 q9 ∷
   rw 90 q1 ∷
   re 88 3 (CS03 ∷ []) ∷
   re 90 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 89 q1 ∷
   rw 90 q9 ∷
   rw 91 q1 ∷
   re 89 3 (CS03 ∷ []) ∷
   re 91 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 90 q1 ∷
   rw 91 q9 ∷
   rw 92 q1 ∷
   re 90 3 (CS03 ∷ []) ∷
   rw 91 q3 ∷
   re 93 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 92 q1 ∷
   rw 93 q9 ∷
   rw 94 q1 ∷
   re 92 3 (CS03 ∷ []) ∷
   re 94 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 93 q1 ∷
   rw 94 q9 ∷
   rw 95 q1 ∷
   re 93 3 (CS03 ∷ []) ∷
   re 95 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 94 q1 ∷
   rw 95 q9 ∷
   rw 96 q1 ∷
   re 94 3 (CS03 ∷ []) ∷
   re 96 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 95 q1 ∷
   rw 96 q10 ∷
   rw 97 q1 ∷
   re 95 3 (CK30 ∷ []) ∷
   re 97 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 96 q1 ∷
   rw 97 q9 ∷
   rw 98 q1 ∷
   re 96 3 (CS03 ∷ []) ∷
   re 98 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 97 q1 ∷
   rw 98 q9 ∷
   rw 99 q1 ∷
   re 97 3 (CS03 ∷ []) ∷
   rw 98 q12 ∷ []) Eq.refl

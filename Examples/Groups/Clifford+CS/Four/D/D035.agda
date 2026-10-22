{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D035 (W : Ws) where

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
  q4 = wE 493 W
  q5 : Eqn
  q5 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q6 : Eqn
  q6 = wE 29 W
  q7 : Eqn
  q7 = wE 27 W
  q8 : Eqn
  q8 = wE 142 W
  q9 : Eqn
  q9 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q10 : Eqn
  q10 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q11 : Eqn
  q11 = wE 31 W

-- Bar(SSKSKK;3,2->0) passes white iX via V2 conjugates 1 part5: 88 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part5 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part5 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ Sw01 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (re 66 3 (CS13 ∷ []) ∷
   re 64 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 66 q1 ∷
   rw 65 q2 ∷
   rw⁻ 64 q1 ∷
   re 65 3 (CK31 ∷ []) ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 65 q1 ∷
   rw 64 q3 ∷
   rw⁻ 63 q1 ∷
   re 64 3 (CS13 ∷ []) ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 64 q1 ∷
   rw 63 q3 ∷
   rw⁻ 62 q1 ∷
   re 63 3 (CS13 ∷ []) ∷
   rw 63 q4 ∷
   rw 62 q5 ∷
   re 64 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 63 q1 ∷
   rw 64 q6 ∷
   rw 65 q1 ∷
   re 63 3 (CS03⁻ ∷ []) ∷
   re 65 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 64 q1 ∷
   rw 65 q6 ∷
   rw 66 q1 ∷
   re 64 3 (CS03⁻ ∷ []) ∷
   re 66 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 65 q1 ∷
   rw 66 q6 ∷
   rw 67 q1 ∷
   re 65 3 (CS03⁻ ∷ []) ∷
   rw 66 q5 ∷
   re 68 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 67 q1 ∷
   rw 68 q7 ∷
   rw 69 q1 ∷
   re 67 3 (CS03 ∷ []) ∷
   re 69 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 68 q1 ∷
   rw 69 q7 ∷
   rw 70 q1 ∷
   re 68 3 (CS03 ∷ []) ∷
   re 70 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 69 q1 ∷
   rw 70 q8 ∷
   rw 71 q1 ∷
   re 69 3 (CK30 ∷ []) ∷
   re 71 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 70 q1 ∷
   rw 71 q7 ∷
   rw 72 q1 ∷
   re 70 3 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 71 q1 ∷
   rw 72 q8 ∷
   rw 73 q1 ∷
   re 71 3 (CK30 ∷ []) ∷
   re 73 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 72 q1 ∷
   rw 73 q8 ∷
   rw 74 q1 ∷
   re 72 3 (CK30 ∷ []) ∷
   rw 73 q9 ∷
   rw 74 q8 ∷
   rw 75 q10 ∷
   rw 76 q8 ∷
   rw 77 q10 ∷
   rw 78 q7 ∷
   rw 79 q7 ∷
   rw 80 q7 ∷
   rw 81 q8 ∷
   rw 82 q10 ∷
   rw 83 q7 ∷
   rw 84 q7 ∷
   rw 85 q7 ∷
   rw 86 q7 ∷
   rw 87 q7 ∷
   rw 88 q7 ∷
   rw 89 q9 ∷
   rw 90 q7 ∷
   rw 91 q7 ∷
   rw 92 q8 ∷
   rw 93 q7 ∷
   rw 94 q8 ∷
   rw 95 q8 ∷
   rw 96 q11 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = eqn (CK20 ∷ X3 ∷ []) (X3 ∷ CK20 ∷ []) (low₃-comm ((Swap ↑ • CK₁₀ • Swap ↑)) (X))
  q13 : Eqn
  q13 = wE 1 W
  q14 : Eqn
  q14 = wE 359 W
  q15 : Eqn
  q15 = eqn (CK10 ∷ CK32 ∷ []) (CK32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CK₁₀))
  q16 : Eqn
  q16 = wE 361 W
  q17 : Eqn
  q17 = wE 3 W
  q18 : Eqn
  q18 = eqn (CS02 ∷ X3 ∷ []) (X3 ∷ CS02 ∷ []) (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q19 : Eqn
  q19 = eqn (CS01 ∷ CK32 ∷ []) (CK32 ∷ CS01 ∷ []) (low-comm (CS) (CK₁₀))
  q20 : Eqn
  q20 = wE 494 W
  q21 : Eqn
  q21 = eqn (S2 ∷ X3 ∷ []) (X3 ∷ S2 ∷ []) (low₃-comm ((S ↑ ↑)) (X))
  q22 : Eqn
  q22 = wE 495 W
  q23 : Eqn
  q23 = wE 173 W
  q24 : Eqn
  q24 = wE 496 W
  q25 : Eqn
  q25 = wE 175 W
  q26 : Eqn
  q26 = wE 497 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 CK31 X3]: 407 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK31-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK31-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (X3 ∷ CK31 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 28 q12 ∷
   re 30 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 29 q13 ∷
   re 30 3 (CK30 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q13 ∷
   re 34 3 (CK31 ∷ []) ∷
   rw 33 q14 ∷
   rw 32 q15 ∷
   rw 31 q16 ∷
   re 31 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 30 q17 ∷
   re 31 5 (CK30 ∷ []) ∷
   re 31 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 33 q17 ∷
   re 29 3 (CK31 ∷ []) ∷
   rw 30 q12 ∷
   rw 27 q12 ∷
   re 29 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 28 q13 ∷
   re 29 3 (CK30 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q13 ∷
   re 33 3 (CK31 ∷ []) ∷
   rw 32 q14 ∷
   rw 31 q15 ∷
   rw 30 q16 ∷
   re 30 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 29 q17 ∷
   re 30 5 (CK30 ∷ []) ∷
   re 30 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 32 q17 ∷
   re 28 3 (CK31 ∷ []) ∷
   rw 29 q12 ∷
   rw 26 q18 ∷
   re 28 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 27 q13 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q13 ∷
   re 32 3 (CK31 ∷ []) ∷
   rw 31 q14 ∷
   rw 30 q19 ∷
   rw 29 q16 ∷
   re 29 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 28 q17 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q17 ∷
   re 27 3 (CK31 ∷ []) ∷
   rw 28 q18 ∷
   rw 25 q12 ∷
   re 27 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 26 q13 ∷
   re 27 3 (CK30 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q13 ∷
   re 31 3 (CK31 ∷ []) ∷
   rw 30 q14 ∷
   rw 29 q15 ∷
   rw 28 q16 ∷
   re 28 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 27 q17 ∷
   re 28 5 (CK30 ∷ []) ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q17 ∷
   re 26 3 (CK31 ∷ []) ∷
   rw 27 q12 ∷
   rw 24 q18 ∷
   re 26 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 25 q13 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q13 ∷
   re 30 3 (CK31 ∷ []) ∷
   rw 29 q14 ∷
   rw 28 q19 ∷
   rw 27 q16 ∷
   re 27 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 26 q17 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q17 ∷
   re 25 3 (CK31 ∷ []) ∷
   rw 26 q18 ∷
   rw 23 q18 ∷
   re 25 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 24 q13 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q13 ∷
   re 29 3 (CK31 ∷ []) ∷
   rw 28 q14 ∷
   rw 27 q19 ∷
   rw 26 q16 ∷
   re 26 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 25 q17 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q17 ∷
   re 24 3 (CK31 ∷ []) ∷
   rw 25 q18 ∷
   rw 22 q20 ∷
   rw 21 q18 ∷
   re 23 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 22 q13 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q13 ∷
   re 27 3 (CK31 ∷ []) ∷
   rw 26 q14 ∷
   rw 25 q19 ∷
   rw 24 q16 ∷
   re 24 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 23 q17 ∷
   re 24 5 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q17 ∷
   re 22 3 (CK31 ∷ []) ∷
   rw 23 q18 ∷
   rw 20 q18 ∷
   re 22 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 21 q13 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q13 ∷
   re 26 3 (CK31 ∷ []) ∷
   rw 25 q14 ∷
   rw 24 q19 ∷
   rw 23 q16 ∷
   re 23 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 22 q17 ∷
   re 23 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q17 ∷
   re 21 3 (CK31 ∷ []) ∷
   rw 22 q18 ∷
   rw 19 q18 ∷
   re 21 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 20 q13 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q13 ∷
   re 25 3 (CK31 ∷ []) ∷
   rw 24 q14 ∷
   rw 23 q19 ∷
   rw 22 q16 ∷
   re 22 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 21 q17 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q17 ∷
   re 20 3 (CK31 ∷ []) ∷
   rw 21 q18 ∷
   rw 18 q18 ∷
   re 20 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 19 q13 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q13 ∷
   re 24 3 (CK31 ∷ []) ∷
   rw 23 q14 ∷
   rw 22 q19 ∷
   rw 21 q16 ∷
   re 21 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 20 q17 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q17 ∷
   re 19 3 (CK31 ∷ []) ∷
   rw 20 q18 ∷
   rw 17 q18 ∷
   re 19 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 18 q13 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q13 ∷
   re 23 3 (CK31 ∷ []) ∷
   rw 22 q14 ∷
   rw 21 q19 ∷
   rw 20 q16 ∷
   re 20 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 19 q17 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q17 ∷
   re 18 3 (CK31 ∷ []) ∷
   rw 19 q18 ∷
   rw 16 q18 ∷
   re 18 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 17 q13 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q13 ∷
   re 22 3 (CK31 ∷ []) ∷
   rw 21 q14 ∷
   rw 20 q19 ∷
   rw 19 q16 ∷
   re 19 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 18 q17 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q17 ∷
   re 17 3 (CK31 ∷ []) ∷
   rw 18 q18 ∷
   rw 15 q21 ∷
   rw 16 q22 ∷
   rw 17 q21 ∷
   rw 14 q12 ∷
   re 16 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 15 q13 ∷
   re 16 3 (CK30 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q13 ∷
   re 20 3 (CK31 ∷ []) ∷
   rw 19 q14 ∷
   rw 18 q15 ∷
   rw 17 q16 ∷
   re 17 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 16 q17 ∷
   re 17 5 (CK30 ∷ []) ∷
   re 17 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 19 q17 ∷
   re 15 3 (CK31 ∷ []) ∷
   rw 16 q12 ∷
   rw 13 q18 ∷
   re 15 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 14 q13 ∷
   re 15 3 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q13 ∷
   re 19 3 (CK31 ∷ []) ∷
   rw 18 q14 ∷
   rw 17 q19 ∷
   rw 16 q16 ∷
   re 16 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 15 q17 ∷
   re 16 5 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q17 ∷
   re 14 3 (CK31 ∷ []) ∷
   rw 15 q18 ∷
   rw 12 q18 ∷
   re 14 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 13 q13 ∷
   re 14 3 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q13 ∷
   re 18 3 (CK31 ∷ []) ∷
   rw 17 q14 ∷
   rw 16 q19 ∷
   rw 15 q16 ∷
   re 15 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 14 q17 ∷
   re 15 5 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q17 ∷
   re 13 3 (CK31 ∷ []) ∷
   rw 14 q18 ∷
   rw 11 q18 ∷
   re 13 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 12 q13 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q13 ∷
   re 17 3 (CK31 ∷ []) ∷
   rw 16 q14 ∷
   rw 15 q19 ∷
   rw 14 q16 ∷
   re 14 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 13 q17 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q17 ∷
   re 12 3 (CK31 ∷ []) ∷
   rw 13 q18 ∷
   rw 10 q21 ∷
   rw 11 q22 ∷
   rw 12 q21 ∷
   rw 9 q12 ∷
   re 11 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 10 q13 ∷
   re 11 3 (CK30 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q13 ∷
   re 15 3 (CK31 ∷ []) ∷
   rw 14 q14 ∷
   rw 13 q15 ∷
   rw 12 q16 ∷
   re 12 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 11 q17 ∷
   re 12 5 (CK30 ∷ []) ∷
   re 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 14 q17 ∷
   re 10 3 (CK31 ∷ []) ∷
   rw 11 q12 ∷
   rw 8 q21 ∷
   rw 9 q22 ∷
   rw 10 q21 ∷
   rw 7 q12 ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q13 ∷
   re 9 3 (CK30 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q13 ∷
   re 13 3 (CK31 ∷ []) ∷
   rw 12 q14 ∷
   rw 11 q15 ∷
   rw 10 q16 ∷
   re 10 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 9 q17 ∷
   re 10 5 (CK30 ∷ []) ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 12 q17 ∷
   re 8 3 (CK31 ∷ []) ∷
   rw 9 q12 ∷
   rw 6 q20 ∷
   rw 9 q13 ∷
   rw 8 q23 ∷
   re 7 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 9 q17 ∷
   rw 6 q23 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 7 q17 ∷
   rw 6 q24 ∷
   rw 5 q25 ∷
   rw 8 q13 ∷
   re 6 3 (CK31 ∷ []) ∷
   rw 7 q25 ∷
   rw 10 q13 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q17 ∷
   rw 8 q13 ∷
   rw 7 q23 ∷
   re 6 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q17 ∷
   rw 5 q23 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 6 q17 ∷
   rw 5 q24 ∷
   rw 4 q25 ∷
   rw 7 q13 ∷
   re 5 3 (CK31 ∷ []) ∷
   rw 6 q25 ∷
   rw 9 q13 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 8 q17 ∷
   rw 7 q13 ∷
   rw 6 q23 ∷
   re 5 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q17 ∷
   rw 4 q23 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q17 ∷
   rw 4 q26 ∷
   rw 3 q25 ∷
   rw 6 q13 ∷
   re 4 3 (CK31 ∷ []) ∷
   rw 5 q25 ∷
   rw 8 q13 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q17 ∷
   rw 6 q13 ∷
   rw 5 q23 ∷
   re 4 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 6 q17 ∷
   rw 3 q23 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 4 q17 ∷
   rw 3 q24 ∷
   rw 2 q25 ∷
   rw 5 q13 ∷
   re 3 3 (CK31 ∷ []) ∷
   rw 4 q25 ∷
   rw 7 q13 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 6 q17 ∷
   rw 5 q13 ∷
   rw 4 q23 ∷
   re 3 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 5 q17 ∷
   rw 2 q23 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q17 ∷
   rw 2 q26 ∷
   rw 1 q25 ∷
   rw 4 q13 ∷
   re 2 3 (CK31 ∷ []) ∷
   rw 3 q25 ∷
   rw 6 q13 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q17 ∷
   rw 4 q13 ∷
   rw 3 q23 ∷
   re 2 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 4 q17 ∷
   rw 1 q23 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q17 ∷
   rw 1 q26 ∷
   rw 0 q25 ∷
   rw 3 q13 ∷
   re 1 3 (CK31 ∷ []) ∷
   rw 2 q25 ∷
   rw 5 q13 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q17 ∷ []) Eq.refl

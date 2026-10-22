{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D033 (W : Ws) where

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
  q1 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = eqn (CK20 ∷ X3 ∷ []) (X3 ∷ CK20 ∷ []) (low₃-comm ((Swap ↑ • CK₁₀ • Swap ↑)) (X))
  q5 : Eqn
  q5 = wE 113 W
  q6 : Eqn
  q6 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q7 : Eqn
  q7 = wE 114 W
  q8 : Eqn
  q8 = eqn (CS02 ∷ X3 ∷ []) (X3 ∷ CS02 ∷ []) (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q9 : Eqn
  q9 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q10 : Eqn
  q10 = wE 486 W
  q11 : Eqn
  q11 = eqn (S2 ∷ X3 ∷ []) (X3 ∷ S2 ∷ []) (low₃-comm ((S ↑ ↑)) (X))
  q12 : Eqn
  q12 = wE 487 W
  q13 : Eqn
  q13 = wE 173 W
  q14 : Eqn
  q14 = wE 488 W
  q15 : Eqn
  q15 = wE 175 W
  q16 : Eqn
  q16 = wE 489 W
  q17 : Eqn
  q17 = eqn (CS01⁻ ∷ CX32 ∷ []) (CX32 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₁₀))
  q18 : Eqn
  q18 = eqn (S1⁻ ∷ CX32 ∷ []) (CX32 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (CX₁₀))
  q19 : Eqn
  q19 = eqn (CK10⁻ ∷ CX32 ∷ []) (CX32 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q20 : Eqn
  q20 = wE 490 W
  q21 : Eqn
  q21 = eqn (CK10⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap))
  q22 : Eqn
  q22 = eqn (S1⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (Swap))

-- Bar(SSKSKK;3,2->0) passes white iX via V2 conjugates 1 part3: 500 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part3 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ Sw23 ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Sw23 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CX32 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X3 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part3 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ Sw23 ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Sw23 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CX32 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X3 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ [])
  (rw⁻ 37 q1 ∷
   rw⁻ 38 q1 ∷
   rw 41 q2 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 42 q2 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 43 q2 ∷
   re 41 3 (CK30 ∷ []) ∷
   rw 44 q2 ∷
   re 42 3 (CS03 ∷ []) ∷
   rw 45 q2 ∷
   re 43 3 (CK30 ∷ []) ∷
   rw 46 q2 ∷
   re 44 3 (CK30 ∷ []) ∷
   rw 45 q3 ∷
   rw 67 q4 ∷
   re 69 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 68 q2 ∷
   re 69 3 (CK30 ∷ []) ∷
   re 69 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 75 q2 ∷
   re 73 3 (CX31 ∷ []) ∷
   rw 72 q5 ∷
   rw 71 q6 ∷
   rw 70 q7 ∷
   re 70 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 69 q3 ∷
   re 70 5 (CK30 ∷ []) ∷
   re 70 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 72 q3 ∷
   re 68 3 (CX31 ∷ []) ∷
   rw 69 q4 ∷
   rw 66 q4 ∷
   re 68 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 67 q2 ∷
   re 68 3 (CK30 ∷ []) ∷
   re 68 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 74 q2 ∷
   re 72 3 (CX31 ∷ []) ∷
   rw 71 q5 ∷
   rw 70 q6 ∷
   rw 69 q7 ∷
   re 69 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 68 q3 ∷
   re 69 5 (CK30 ∷ []) ∷
   re 69 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 71 q3 ∷
   re 67 3 (CX31 ∷ []) ∷
   rw 68 q4 ∷
   rw 65 q8 ∷
   re 67 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 66 q2 ∷
   re 67 3 (CS03 ∷ []) ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q2 ∷
   re 71 3 (CX31 ∷ []) ∷
   rw 70 q5 ∷
   rw 69 q9 ∷
   rw 68 q7 ∷
   re 68 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 67 q3 ∷
   re 68 5 (CS03 ∷ []) ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 70 q3 ∷
   re 66 3 (CX31 ∷ []) ∷
   rw 67 q8 ∷
   rw 64 q4 ∷
   re 66 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 65 q2 ∷
   re 66 3 (CK30 ∷ []) ∷
   re 66 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 72 q2 ∷
   re 70 3 (CX31 ∷ []) ∷
   rw 69 q5 ∷
   rw 68 q6 ∷
   rw 67 q7 ∷
   re 67 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 66 q3 ∷
   re 67 5 (CK30 ∷ []) ∷
   re 67 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 69 q3 ∷
   re 65 3 (CX31 ∷ []) ∷
   rw 66 q4 ∷
   rw 63 q8 ∷
   re 65 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 64 q2 ∷
   re 65 3 (CS03 ∷ []) ∷
   re 65 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q2 ∷
   re 69 3 (CX31 ∷ []) ∷
   rw 68 q5 ∷
   rw 67 q9 ∷
   rw 66 q7 ∷
   re 66 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 65 q3 ∷
   re 66 5 (CS03 ∷ []) ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 68 q3 ∷
   re 64 3 (CX31 ∷ []) ∷
   rw 65 q8 ∷
   rw 62 q8 ∷
   re 64 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 63 q2 ∷
   re 64 3 (CS03 ∷ []) ∷
   re 64 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 70 q2 ∷
   re 68 3 (CX31 ∷ []) ∷
   rw 67 q5 ∷
   rw 66 q9 ∷
   rw 65 q7 ∷
   re 65 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 64 q3 ∷
   re 65 5 (CS03 ∷ []) ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q3 ∷
   re 63 3 (CX31 ∷ []) ∷
   rw 64 q8 ∷
   rw 61 q10 ∷
   rw 60 q8 ∷
   re 62 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 61 q2 ∷
   re 62 3 (CS03 ∷ []) ∷
   re 62 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 68 q2 ∷
   re 66 3 (CX31 ∷ []) ∷
   rw 65 q5 ∷
   rw 64 q9 ∷
   rw 63 q7 ∷
   re 63 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 62 q3 ∷
   re 63 5 (CS03 ∷ []) ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 65 q3 ∷
   re 61 3 (CX31 ∷ []) ∷
   rw 62 q8 ∷
   rw 59 q8 ∷
   re 61 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 60 q2 ∷
   re 61 3 (CS03 ∷ []) ∷
   re 61 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 67 q2 ∷
   re 65 3 (CX31 ∷ []) ∷
   rw 64 q5 ∷
   rw 63 q9 ∷
   rw 62 q7 ∷
   re 62 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 61 q3 ∷
   re 62 5 (CS03 ∷ []) ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 64 q3 ∷
   re 60 3 (CX31 ∷ []) ∷
   rw 61 q8 ∷
   rw 58 q8 ∷
   re 60 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 59 q2 ∷
   re 60 3 (CS03 ∷ []) ∷
   re 60 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 66 q2 ∷
   re 64 3 (CX31 ∷ []) ∷
   rw 63 q5 ∷
   rw 62 q9 ∷
   rw 61 q7 ∷
   re 61 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 60 q3 ∷
   re 61 5 (CS03 ∷ []) ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 63 q3 ∷
   re 59 3 (CX31 ∷ []) ∷
   rw 60 q8 ∷
   rw 57 q8 ∷
   re 59 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 58 q2 ∷
   re 59 3 (CS03 ∷ []) ∷
   re 59 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 65 q2 ∷
   re 63 3 (CX31 ∷ []) ∷
   rw 62 q5 ∷
   rw 61 q9 ∷
   rw 60 q7 ∷
   re 60 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 59 q3 ∷
   re 60 5 (CS03 ∷ []) ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 62 q3 ∷
   re 58 3 (CX31 ∷ []) ∷
   rw 59 q8 ∷
   rw 56 q8 ∷
   re 58 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 57 q2 ∷
   re 58 3 (CS03 ∷ []) ∷
   re 58 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 64 q2 ∷
   re 62 3 (CX31 ∷ []) ∷
   rw 61 q5 ∷
   rw 60 q9 ∷
   rw 59 q7 ∷
   re 59 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 58 q3 ∷
   re 59 5 (CS03 ∷ []) ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 61 q3 ∷
   re 57 3 (CX31 ∷ []) ∷
   rw 58 q8 ∷
   rw 55 q8 ∷
   re 57 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 56 q2 ∷
   re 57 3 (CS03 ∷ []) ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 63 q2 ∷
   re 61 3 (CX31 ∷ []) ∷
   rw 60 q5 ∷
   rw 59 q9 ∷
   rw 58 q7 ∷
   re 58 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 57 q3 ∷
   re 58 5 (CS03 ∷ []) ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q3 ∷
   re 56 3 (CX31 ∷ []) ∷
   rw 57 q8 ∷
   rw 54 q11 ∷
   rw 55 q12 ∷
   rw 56 q11 ∷
   rw 53 q4 ∷
   re 55 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 54 q2 ∷
   re 55 3 (CK30 ∷ []) ∷
   re 55 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 61 q2 ∷
   re 59 3 (CX31 ∷ []) ∷
   rw 58 q5 ∷
   rw 57 q6 ∷
   rw 56 q7 ∷
   re 56 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 55 q3 ∷
   re 56 5 (CK30 ∷ []) ∷
   re 56 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 58 q3 ∷
   re 54 3 (CX31 ∷ []) ∷
   rw 55 q4 ∷
   rw 52 q8 ∷
   re 54 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 53 q2 ∷
   re 54 3 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 60 q2 ∷
   re 58 3 (CX31 ∷ []) ∷
   rw 57 q5 ∷
   rw 56 q9 ∷
   rw 55 q7 ∷
   re 55 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 54 q3 ∷
   re 55 5 (CS03 ∷ []) ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q3 ∷
   re 53 3 (CX31 ∷ []) ∷
   rw 54 q8 ∷
   rw 51 q8 ∷
   re 53 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 52 q2 ∷
   re 53 3 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q2 ∷
   re 57 3 (CX31 ∷ []) ∷
   rw 56 q5 ∷
   rw 55 q9 ∷
   rw 54 q7 ∷
   re 54 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 53 q3 ∷
   re 54 5 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q3 ∷
   re 52 3 (CX31 ∷ []) ∷
   rw 53 q8 ∷
   rw 50 q8 ∷
   re 52 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 51 q2 ∷
   re 52 3 (CS03 ∷ []) ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q2 ∷
   re 56 3 (CX31 ∷ []) ∷
   rw 55 q5 ∷
   rw 54 q9 ∷
   rw 53 q7 ∷
   re 53 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 52 q3 ∷
   re 53 5 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 55 q3 ∷
   re 51 3 (CX31 ∷ []) ∷
   rw 52 q8 ∷
   rw 49 q11 ∷
   rw 50 q12 ∷
   rw 51 q11 ∷
   rw 48 q4 ∷
   re 50 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 49 q2 ∷
   re 50 3 (CK30 ∷ []) ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q2 ∷
   re 54 3 (CX31 ∷ []) ∷
   rw 53 q5 ∷
   rw 52 q6 ∷
   rw 51 q7 ∷
   re 51 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 50 q3 ∷
   re 51 5 (CK30 ∷ []) ∷
   re 51 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 53 q3 ∷
   re 49 3 (CX31 ∷ []) ∷
   rw 50 q4 ∷
   rw 47 q11 ∷
   rw 48 q12 ∷
   rw 49 q11 ∷
   rw 46 q4 ∷
   re 48 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 47 q2 ∷
   re 48 3 (CK30 ∷ []) ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q2 ∷
   re 52 3 (CX31 ∷ []) ∷
   rw 51 q5 ∷
   rw 50 q6 ∷
   rw 49 q7 ∷
   re 49 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 48 q3 ∷
   re 49 5 (CK30 ∷ []) ∷
   re 49 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 51 q3 ∷
   re 47 3 (CX31 ∷ []) ∷
   rw 48 q4 ∷
   rw 45 q10 ∷
   rw 48 q2 ∷
   rw 47 q13 ∷
   re 46 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 48 q3 ∷
   rw 45 q13 ∷
   re 44 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 46 q3 ∷
   re 43 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 45 q3 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q3 ∷
   re 41 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 43 q3 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q3 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q3 ∷
   rw 40 q14 ∷
   rw 39 q15 ∷
   rw 42 q2 ∷
   re 40 3 (CX31 ∷ []) ∷
   rw 41 q15 ∷
   rw 44 q2 ∷
   re 42 3 (CS03 ∷ []) ∷
   rw 45 q2 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 46 q2 ∷
   re 44 3 (CK30 ∷ []) ∷
   rw 47 q2 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 48 q2 ∷
   re 46 3 (CK30 ∷ []) ∷
   rw 49 q2 ∷
   re 47 3 (CK30 ∷ []) ∷
   rw 48 q3 ∷
   rw 65 q16 ∷
   rw⁻ 64 q17 ∷
   rw⁻ 65 q17 ∷
   rw⁻ 66 q17 ∷
   rw⁻ 67 q17 ∷
   rw⁻ 68 q17 ∷
   rw⁻ 69 q17 ∷
   rw⁻ 70 q18 ∷
   rw⁻ 71 q19 ∷
   rw⁻ 72 q17 ∷
   rw⁻ 73 q17 ∷
   rw⁻ 74 q17 ∷
   rw 49 q20 ∷
   rw⁻ 48 q17 ∷
   rw⁻ 49 q17 ∷
   rw⁻ 50 q17 ∷
   rw⁻ 51 q17 ∷
   rw⁻ 52 q17 ∷
   rw⁻ 53 q17 ∷
   rw⁻ 54 q18 ∷
   rw⁻ 55 q19 ∷
   rw⁻ 56 q17 ∷
   rw⁻ 57 q17 ∷
   rw⁻ 58 q17 ∷
   rw 59 q2 ∷
   rw 58 q1 ∷
   rw 57 q1 ∷
   rw 56 q1 ∷
   rw 55 q21 ∷
   rw 54 q22 ∷
   rw 53 q1 ∷
   rw 52 q1 ∷
   rw 51 q1 ∷
   rw 50 q1 ∷
   rw 49 q1 ∷
   rw 48 q1 ∷
   re 47 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 49 q3 ∷
   re 46 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 48 q3 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q3 ∷
   re 44 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 46 q3 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q3 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q3 ∷
   rw 43 q16 ∷
   rw⁻ 42 q1 ∷
   rw⁻ 43 q1 ∷
   rw⁻ 44 q1 ∷
   rw⁻ 45 q1 ∷
   rw⁻ 46 q1 ∷
   rw⁻ 47 q1 ∷
   rw⁻ 48 q22 ∷
   rw⁻ 49 q21 ∷
   rw⁻ 50 q1 ∷
   rw⁻ 51 q1 ∷
   rw⁻ 52 q1 ∷
   rw 55 q2 ∷
   re 53 3 (CS03 ∷ []) ∷
   rw 56 q2 ∷
   re 54 3 (CS03 ∷ []) ∷
   rw 57 q2 ∷
   re 55 3 (CK30 ∷ []) ∷
   rw 58 q2 ∷
   re 56 3 (CS03 ∷ []) ∷
   rw 59 q2 ∷
   re 57 3 (CK30 ∷ []) ∷
   rw 60 q2 ∷
   re 58 3 (CK30 ∷ []) ∷
   rw 59 q3 ∷
   rw 81 q4 ∷
   re 83 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 82 q2 ∷
   re 83 3 (CK30 ∷ []) ∷
   re 83 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 89 q2 ∷
   re 87 3 (CX31 ∷ []) ∷
   rw 86 q5 ∷
   rw 85 q6 ∷
   rw 84 q7 ∷
   re 84 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 83 q3 ∷
   re 84 5 (CK30 ∷ []) ∷
   re 84 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 86 q3 ∷
   re 82 3 (CX31 ∷ []) ∷
   rw 83 q4 ∷
   rw 80 q4 ∷
   re 82 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 81 q2 ∷
   re 82 3 (CK30 ∷ []) ∷
   re 82 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 88 q2 ∷
   re 86 3 (CX31 ∷ []) ∷
   rw 85 q5 ∷
   rw 84 q6 ∷
   rw 83 q7 ∷
   re 83 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 82 q3 ∷
   re 83 5 (CK30 ∷ []) ∷
   re 83 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 85 q3 ∷
   re 81 3 (CX31 ∷ []) ∷
   rw 82 q4 ∷
   rw 79 q8 ∷
   re 81 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 80 q2 ∷
   re 81 3 (CS03 ∷ []) ∷
   re 81 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 87 q2 ∷
   re 85 3 (CX31 ∷ []) ∷
   rw 84 q5 ∷
   rw 83 q9 ∷
   rw 82 q7 ∷
   re 82 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 81 q3 ∷
   re 82 5 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 84 q3 ∷
   re 80 3 (CX31 ∷ []) ∷
   rw 81 q8 ∷
   rw 78 q4 ∷
   re 80 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 79 q2 ∷
   re 80 3 (CK30 ∷ []) ∷
   re 80 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 86 q2 ∷
   re 84 3 (CX31 ∷ []) ∷
   rw 83 q5 ∷
   rw 82 q6 ∷ []) Eq.refl

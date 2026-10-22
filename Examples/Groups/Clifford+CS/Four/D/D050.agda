{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D050 (W : Ws) where

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
  q1 = wE 21 W
  q2 : Eqn
  q2 = eqn (CX10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((CS • CS • CS)))
  q3 : Eqn
  q3 = wE 51 W
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = wE 1 W
  q6 : Eqn
  q6 = wE 5 W
  q7 : Eqn
  q7 = eqn (Sw01 ∷ S2⁻ ∷ []) (S2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • S • S)))
  q8 : Eqn
  q8 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q9 : Eqn
  q9 = wE 6 W
  q10 : Eqn
  q10 = wE 540 W
  q11 : Eqn
  q11 = wE 39 W
  q12 : Eqn
  q12 = wE 31 W
  q13 : Eqn
  q13 = wE 360 W
  q14 : Eqn
  q14 = eqn (CX10 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((S ↑ • CK₁₀)))
  q15 : Eqn
  q15 = wE 362 W
  q16 : Eqn
  q16 = wE 541 W
  q17 : Eqn
  q17 = wE 542 W
  q18 : Eqn
  q18 = eqn (CK01 ∷ X3 ∷ []) (X3 ∷ CK01 ∷ []) (low-comm (CK₀₁) ((X ↑)))
  q19 : Eqn
  q19 = eqn (CK01 ∷ CX32 ∷ []) (CX32 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₁₀))
  q20 : Eqn
  q20 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q21 : Eqn
  q21 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q22 : Eqn
  q22 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q23 : Eqn
  q23 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q24 : Eqn
  q24 = wE 537 W
  q25 : Eqn
  q25 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q26 : Eqn
  q26 = eqn (S0 ∷ CX32 ∷ []) (CX32 ∷ S0 ∷ []) (low₁-comm (S) ((CX₁₀ ↑)))
  q27 : Eqn
  q27 = wE 538 W
  q28 : Eqn
  q28 = wE 173 W
  q29 : Eqn
  q29 = eqn (CK01 ∷ Sw23 ∷ []) (Sw23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (Swap))
  q30 : Eqn
  q30 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q31 : Eqn
  q31 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q32 : Eqn
  q32 = wE 543 W
  q33 : Eqn
  q33 = wE 175 W
  q34 : Eqn
  q34 = wE 545 W

-- Bar(['S', 'S', 'K', 'S', 'K', 'K'];3,0->1) passes white iX via V2 conjugates 2 part2: 466 steps
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-white-iX-via-V2-conjugates-2-part2 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) ⟫ʷ
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-white-iX-via-V2-conjugates-2-part2 = derive (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ [])
  (re 72 3 (CS13⁻ ∷ []) ∷
   rw 71 q1 ∷
   rw 70 q2 ∷
   rw 69 q3 ∷
   re 69 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 68 q4 ∷
   re 69 5 (CX30 ∷ []) ∷
   re 69 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 75 q5 ∷
   re 73 3 (CS13⁻ ∷ []) ∷
   rw 72 q1 ∷
   rw 71 q2 ∷
   rw 70 q3 ∷
   re 70 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 69 q4 ∷
   re 70 5 (CX30 ∷ []) ∷
   rw 72 q6 ∷
   rw⁻ 71 q7 ∷
   re 70 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 72 q8 ∷
   rw 71 q9 ∷
   rw⁻ 70 q8 ∷
   re 71 3 (CX31 ∷ []) ∷
   rw 71 q10 ∷
   rw 70 q7 ∷
   re 72 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 71 q8 ∷
   rw 72 q11 ∷
   rw 73 q8 ∷
   re 71 3 (CX30 ∷ []) ∷
   rw 72 q12 ∷
   re 71 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 77 q5 ∷
   re 75 3 (CK31⁻ ∷ []) ∷
   rw 74 q13 ∷
   rw 73 q14 ∷
   rw 72 q15 ∷
   re 72 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 71 q4 ∷
   re 72 5 (CX30 ∷ []) ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 78 q5 ∷
   re 76 3 (CS13⁻ ∷ []) ∷
   rw 75 q1 ∷
   rw 74 q2 ∷
   rw 73 q3 ∷
   re 73 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 72 q4 ∷
   re 73 5 (CX30 ∷ []) ∷
   re 73 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 79 q5 ∷
   re 77 3 (CS13⁻ ∷ []) ∷
   rw 76 q1 ∷
   rw 75 q2 ∷
   rw 74 q3 ∷
   re 74 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 73 q4 ∷
   re 74 5 (CX30 ∷ []) ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 80 q5 ∷
   re 78 3 (CS13⁻ ∷ []) ∷
   rw 77 q1 ∷
   rw 76 q2 ∷
   rw 75 q3 ∷
   re 75 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 74 q4 ∷
   re 75 5 (CX30 ∷ []) ∷
   rw 49 q16 ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q5 ∷
   re 52 3 (CS13⁻ ∷ []) ∷
   rw 51 q1 ∷
   rw 50 q2 ∷
   rw 49 q3 ∷
   re 49 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 48 q4 ∷
   re 49 5 (CX30 ∷ []) ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q5 ∷
   re 53 3 (CS13⁻ ∷ []) ∷
   rw 52 q1 ∷
   rw 51 q2 ∷
   rw 50 q3 ∷
   re 50 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 49 q4 ∷
   re 50 5 (CX30 ∷ []) ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q5 ∷
   re 54 3 (CS13⁻ ∷ []) ∷
   rw 53 q1 ∷
   rw 52 q2 ∷
   rw 51 q3 ∷
   re 51 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 50 q4 ∷
   re 51 5 (CX30 ∷ []) ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 57 q5 ∷
   re 55 3 (CS13⁻ ∷ []) ∷
   rw 54 q1 ∷
   rw 53 q2 ∷
   rw 52 q3 ∷
   re 52 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 51 q4 ∷
   re 52 5 (CX30 ∷ []) ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q5 ∷
   re 56 3 (CS13⁻ ∷ []) ∷
   rw 55 q1 ∷
   rw 54 q2 ∷
   rw 53 q3 ∷
   re 53 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 52 q4 ∷
   re 53 5 (CX30 ∷ []) ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q5 ∷
   re 57 3 (CS13⁻ ∷ []) ∷
   rw 56 q1 ∷
   rw 55 q2 ∷
   rw 54 q3 ∷
   re 54 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 53 q4 ∷
   re 54 5 (CX30 ∷ []) ∷
   rw 56 q6 ∷
   rw⁻ 55 q7 ∷
   re 54 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 56 q8 ∷
   rw 55 q9 ∷
   rw⁻ 54 q8 ∷
   re 55 3 (CX31 ∷ []) ∷
   rw 55 q10 ∷
   rw 54 q7 ∷
   re 56 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 55 q8 ∷
   rw 56 q11 ∷
   rw 57 q8 ∷
   re 55 3 (CX30 ∷ []) ∷
   rw 56 q12 ∷
   re 55 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 61 q5 ∷
   re 59 3 (CK31⁻ ∷ []) ∷
   rw 58 q13 ∷
   rw 57 q14 ∷
   rw 56 q15 ∷
   re 56 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 55 q4 ∷
   re 56 5 (CX30 ∷ []) ∷
   re 56 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 62 q5 ∷
   re 60 3 (CS13⁻ ∷ []) ∷
   rw 59 q1 ∷
   rw 58 q2 ∷
   rw 57 q3 ∷
   re 57 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 56 q4 ∷
   re 57 5 (CX30 ∷ []) ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 63 q5 ∷
   re 61 3 (CS13⁻ ∷ []) ∷
   rw 60 q1 ∷
   rw 59 q2 ∷
   rw 58 q3 ∷
   re 58 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 57 q4 ∷
   re 58 5 (CX30 ∷ []) ∷
   re 58 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 64 q5 ∷
   re 62 3 (CS13⁻ ∷ []) ∷
   rw 61 q1 ∷
   rw 60 q2 ∷
   rw 59 q3 ∷
   re 59 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 58 q4 ∷
   re 59 5 (CX30 ∷ []) ∷
   rw 42 q17 ∷
   rw 81 q18 ∷
   rw 82 q19 ∷
   rw 83 q18 ∷
   rw 80 q18 ∷
   rw 81 q19 ∷
   rw 82 q18 ∷
   rw 79 q20 ∷
   rw 80 q21 ∷
   rw 81 q20 ∷
   rw 78 q18 ∷
   rw 79 q19 ∷
   rw 80 q18 ∷
   rw 77 q20 ∷
   rw 78 q21 ∷
   rw 79 q20 ∷
   rw 76 q20 ∷
   rw 77 q21 ∷
   rw 78 q20 ∷
   rw 79 q6 ∷
   rw⁻ 78 q22 ∷
   rw⁻ 77 q23 ∷
   rw⁻ 76 q22 ∷
   re 75 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 77 q8 ∷
   rw 76 q9 ∷
   rw⁻ 75 q8 ∷
   re 76 3 (CX31 ∷ []) ∷
   rw 76 q24 ∷
   rw 75 q22 ∷
   rw 76 q23 ∷
   rw 77 q22 ∷
   re 79 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 78 q8 ∷
   rw 79 q11 ∷
   rw 80 q8 ∷
   re 78 3 (CX30 ∷ []) ∷
   rw 79 q12 ∷
   rw 74 q20 ∷
   rw 75 q21 ∷
   rw 76 q20 ∷
   rw 73 q20 ∷
   rw 74 q21 ∷
   rw 75 q20 ∷
   rw 72 q20 ∷
   rw 73 q21 ∷
   rw 74 q20 ∷
   rw 71 q20 ∷
   rw 72 q21 ∷
   rw 73 q20 ∷
   rw 70 q20 ∷
   rw 71 q21 ∷
   rw 72 q20 ∷
   rw 69 q20 ∷
   rw 70 q21 ∷
   rw 71 q20 ∷
   rw 68 q25 ∷
   rw 69 q26 ∷
   rw 70 q25 ∷
   rw 67 q18 ∷
   rw 68 q19 ∷
   rw 69 q18 ∷
   rw 66 q20 ∷
   rw 67 q21 ∷
   rw 68 q20 ∷
   rw 65 q20 ∷
   rw 66 q21 ∷
   rw 67 q20 ∷
   rw 64 q20 ∷
   rw 65 q21 ∷
   rw 66 q20 ∷
   rw 63 q25 ∷
   rw 64 q26 ∷
   rw 65 q25 ∷
   rw 62 q18 ∷
   rw 63 q19 ∷
   rw 64 q18 ∷
   rw 61 q25 ∷
   rw 62 q26 ∷
   rw 63 q25 ∷
   rw 60 q18 ∷
   rw 61 q19 ∷
   rw 62 q18 ∷
   rw 63 q6 ∷
   rw⁻ 62 q22 ∷
   rw⁻ 61 q23 ∷
   rw⁻ 60 q22 ∷
   re 59 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 61 q8 ∷
   rw 60 q9 ∷
   rw⁻ 59 q8 ∷
   re 60 3 (CX31 ∷ []) ∷
   rw 60 q24 ∷
   rw 59 q22 ∷
   rw 60 q23 ∷
   rw 61 q22 ∷
   re 63 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 62 q8 ∷
   rw 63 q11 ∷
   rw 64 q8 ∷
   re 62 3 (CX30 ∷ []) ∷
   rw 63 q12 ∷
   rw 53 q27 ∷
   rw 91 q5 ∷
   rw 90 q28 ∷
   re 89 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 91 q4 ∷
   re 88 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 90 q4 ∷
   re 87 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 89 q4 ∷
   re 86 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 88 q4 ∷
   rw 85 q28 ∷
   rw 84 q29 ∷
   rw 83 q29 ∷
   rw 82 q30 ∷
   rw 81 q29 ∷
   rw 80 q30 ∷
   rw 79 q30 ∷
   re 78 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 80 q4 ∷
   rw 77 q30 ∷
   rw 76 q30 ∷
   rw 75 q30 ∷
   rw 74 q30 ∷
   rw 73 q30 ∷
   rw 72 q30 ∷
   rw 71 q31 ∷
   rw 70 q29 ∷
   rw 69 q30 ∷
   rw 68 q30 ∷
   rw 67 q30 ∷
   rw 66 q31 ∷
   rw 65 q29 ∷
   rw 64 q31 ∷
   rw 63 q29 ∷
   re 62 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 64 q4 ∷
   re 61 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 63 q4 ∷
   re 60 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 62 q4 ∷
   re 59 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 61 q4 ∷
   re 58 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 60 q4 ∷
   re 57 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 59 q4 ∷
   re 56 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 58 q4 ∷
   rw 57 q32 ∷
   rw 56 q33 ∷
   rw 59 q5 ∷
   re 57 3 (CS13⁻ ∷ []) ∷
   rw 60 q5 ∷
   re 58 3 (CK31⁻ ∷ []) ∷
   rw 61 q5 ∷
   re 59 3 (CS13⁻ ∷ []) ∷
   rw 62 q5 ∷
   re 60 3 (CS13⁻ ∷ []) ∷
   rw 61 q33 ∷
   rw 64 q5 ∷
   re 62 3 (CS13 ∷ []) ∷
   rw 65 q5 ∷
   re 63 3 (CS13 ∷ []) ∷
   rw 66 q5 ∷
   re 64 3 (CK31 ∷ []) ∷
   rw 67 q5 ∷
   re 65 3 (CS13 ∷ []) ∷
   rw 68 q5 ∷
   re 66 3 (CK31 ∷ []) ∷
   rw 69 q5 ∷
   re 67 3 (CK31 ∷ []) ∷
   rw 70 q5 ∷
   re 68 3 (CX30 ∷ []) ∷
   rw⁻ 69 q29 ∷
   rw⁻ 70 q31 ∷
   rw⁻ 71 q29 ∷
   rw⁻ 72 q31 ∷
   rw⁻ 73 q30 ∷
   rw⁻ 74 q30 ∷
   rw⁻ 75 q30 ∷
   rw⁻ 76 q29 ∷
   rw⁻ 77 q31 ∷
   rw⁻ 78 q30 ∷
   rw⁻ 79 q30 ∷
   rw⁻ 80 q30 ∷
   rw⁻ 81 q30 ∷
   rw⁻ 82 q30 ∷
   rw⁻ 83 q30 ∷
   rw 86 q5 ∷
   re 84 3 (CX30 ∷ []) ∷
   rw⁻ 85 q30 ∷
   rw⁻ 86 q30 ∷
   rw⁻ 87 q29 ∷
   rw⁻ 88 q30 ∷
   rw⁻ 89 q29 ∷
   rw⁻ 90 q29 ∷
   rw 91 q4 ∷
   rw 96 q5 ∷
   rw 95 q28 ∷
   re 94 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 96 q4 ∷
   re 93 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 95 q4 ∷
   re 92 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 94 q4 ∷
   rw 91 q28 ∷
   rw 90 q29 ∷
   rw 89 q29 ∷
   rw 88 q30 ∷
   rw 87 q29 ∷
   rw 86 q30 ∷
   rw 85 q30 ∷
   re 84 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 86 q4 ∷
   rw 83 q30 ∷
   rw 82 q30 ∷
   rw 81 q30 ∷
   rw 80 q30 ∷
   rw 79 q30 ∷
   rw 78 q30 ∷
   rw 77 q31 ∷
   rw 76 q29 ∷
   rw 75 q30 ∷
   rw 74 q30 ∷
   rw 73 q30 ∷
   rw 72 q31 ∷
   rw 71 q29 ∷
   rw 70 q31 ∷
   rw 69 q29 ∷
   re 68 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 70 q4 ∷
   re 67 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 69 q4 ∷
   re 66 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 68 q4 ∷
   re 65 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 67 q4 ∷
   re 64 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 66 q4 ∷
   re 63 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 65 q4 ∷
   re 62 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 64 q4 ∷
   rw 63 q34 ∷
   rw 62 q33 ∷
   rw 65 q5 ∷
   re 63 3 (CS13⁻ ∷ []) ∷
   rw 66 q5 ∷
   re 64 3 (CS13⁻ ∷ []) ∷
   rw 67 q5 ∷
   re 65 3 (CS13⁻ ∷ []) ∷
   rw 66 q33 ∷
   rw 69 q5 ∷
   re 67 3 (CS13 ∷ []) ∷
   rw 70 q5 ∷
   re 68 3 (CS13 ∷ []) ∷
   rw 71 q5 ∷
   re 69 3 (CK31 ∷ []) ∷
   rw 72 q5 ∷
   re 70 3 (CS13 ∷ []) ∷
   rw 73 q5 ∷
   re 71 3 (CK31 ∷ []) ∷
   rw 74 q5 ∷
   re 72 3 (CK31 ∷ []) ∷
   rw 75 q5 ∷
   re 73 3 (CX30 ∷ []) ∷
   rw⁻ 74 q29 ∷
   rw⁻ 75 q31 ∷
   rw⁻ 76 q29 ∷
   rw⁻ 77 q31 ∷
   rw⁻ 78 q30 ∷
   rw⁻ 79 q30 ∷
   rw⁻ 80 q30 ∷
   rw⁻ 81 q29 ∷
   rw⁻ 82 q31 ∷
   rw⁻ 83 q30 ∷
   rw⁻ 84 q30 ∷
   rw⁻ 85 q30 ∷
   rw⁻ 86 q30 ∷
   rw⁻ 87 q30 ∷
   rw⁻ 88 q30 ∷
   rw 91 q5 ∷
   re 89 3 (CX30 ∷ []) ∷
   rw⁻ 90 q30 ∷
   rw⁻ 91 q30 ∷
   rw⁻ 92 q29 ∷
   rw⁻ 93 q30 ∷
   rw⁻ 94 q29 ∷
   rw⁻ 95 q29 ∷
   rw 96 q4 ∷ []) Eq.refl

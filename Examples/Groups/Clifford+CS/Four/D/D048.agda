{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D048 (W : Ws) where

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
  q1 = eqn (CK01 ∷ X3 ∷ []) (X3 ∷ CK01 ∷ []) (low-comm (CK₀₁) ((X ↑)))
  q2 : Eqn
  q2 = eqn (CK01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CK01 ∷ []) (low-comm (CK₀₁) ((CS • CS • CS)))
  q3 : Eqn
  q3 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q4 : Eqn
  q4 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q5 : Eqn
  q5 = wE 5 W
  q6 : Eqn
  q6 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q8 : Eqn
  q8 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q9 : Eqn
  q9 = wE 6 W
  q10 : Eqn
  q10 = wE 532 W
  q11 : Eqn
  q11 = wE 39 W
  q12 : Eqn
  q12 = wE 31 W
  q13 : Eqn
  q13 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q14 : Eqn
  q14 = eqn (S0 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S0 ∷ []) (low₁-comm (S) (((CS • CS • CS) ↑)))
  q15 : Eqn
  q15 = wE 533 W
  q16 : Eqn
  q16 = wE 534 W
  q17 : Eqn
  q17 = wE 1 W
  q18 : Eqn
  q18 = wE 21 W
  q19 : Eqn
  q19 = eqn (CX10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((CS • CS • CS)))
  q20 : Eqn
  q20 = wE 51 W
  q21 : Eqn
  q21 = wE 3 W
  q22 : Eqn
  q22 = wE 360 W
  q23 : Eqn
  q23 = eqn (CX10 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((S ↑ • CK₁₀)))
  q24 : Eqn
  q24 = wE 362 W
  q25 : Eqn
  q25 = wE 535 W
  q26 : Eqn
  q26 = wE 536 W
  q27 : Eqn
  q27 = eqn (CK01 ∷ CX32 ∷ []) (CX32 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₁₀))
  q28 : Eqn
  q28 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q29 : Eqn
  q29 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q30 : Eqn
  q30 = wE 537 W
  q31 : Eqn
  q31 = eqn (S0 ∷ CX32 ∷ []) (CX32 ∷ S0 ∷ []) (low₁-comm (S) ((CX₁₀ ↑)))
  q32 : Eqn
  q32 = wE 538 W
  q33 : Eqn
  q33 = wE 539 W
  q34 : Eqn
  q34 = eqn (Sw01 ∷ S2⁻ ∷ []) (S2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • S • S)))
  q35 : Eqn
  q35 = wE 540 W
  q36 : Eqn
  q36 = wE 541 W
  q37 : Eqn
  q37 = wE 542 W

-- Bar(['S', 'S', 'K', 'S', 'K', 'K'];3,0->1) passes white iX via V2 conjugates 2 part0: 500 steps
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-white-iX-via-V2-conjugates-2-part0 : ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ X3 ∷ CX32 ∷ CS01 ∷ X3 ∷ CK01 ∷ CK01 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-white-iX-via-V2-conjugates-2-part0 = derive (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ X3 ∷ CX32 ∷ CS01 ∷ X3 ∷ CK01 ∷ CK01 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ [])
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
   rw 26 q5 ∷
   rw⁻ 25 q6 ∷
   rw⁻ 24 q7 ∷
   rw⁻ 23 q6 ∷
   re 22 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q8 ∷
   rw 23 q9 ∷
   rw⁻ 22 q8 ∷
   re 23 3 (CX31 ∷ []) ∷
   rw 23 q10 ∷
   rw 22 q6 ∷
   rw 23 q7 ∷
   rw 24 q6 ∷
   re 26 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 25 q8 ∷
   rw 26 q11 ∷
   rw 27 q8 ∷
   re 25 3 (CX30 ∷ []) ∷
   rw 26 q12 ∷
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
   rw 15 q13 ∷
   rw 16 q14 ∷
   rw 17 q13 ∷
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
   rw 10 q13 ∷
   rw 11 q14 ∷
   rw 12 q13 ∷
   rw 9 q1 ∷
   rw 10 q2 ∷
   rw 11 q1 ∷
   rw 8 q13 ∷
   rw 9 q14 ∷
   rw 10 q13 ∷
   rw 7 q1 ∷
   rw 8 q2 ∷
   rw 9 q1 ∷
   rw 10 q5 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 8 q7 ∷
   rw⁻ 7 q6 ∷
   re 6 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q8 ∷
   rw 7 q9 ∷
   rw⁻ 6 q8 ∷
   re 7 3 (CX31 ∷ []) ∷
   rw 7 q10 ∷
   rw 6 q6 ∷
   rw 7 q7 ∷
   rw 8 q6 ∷
   re 10 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 9 q8 ∷
   rw 10 q11 ∷
   rw 11 q8 ∷
   re 9 3 (CX30 ∷ []) ∷
   rw 10 q12 ∷
   rw 0 q15 ∷
   rw 26 q16 ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q17 ∷
   re 29 3 (CS13⁻ ∷ []) ∷
   rw 28 q18 ∷
   rw 27 q19 ∷
   rw 26 q20 ∷
   re 26 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q21 ∷
   re 26 5 (CX30 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q17 ∷
   re 30 3 (CK31⁻ ∷ []) ∷
   rw 29 q22 ∷
   rw 28 q23 ∷
   rw 27 q24 ∷
   re 27 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q21 ∷
   re 27 5 (CX30 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q17 ∷
   re 31 3 (CS13⁻ ∷ []) ∷
   rw 30 q18 ∷
   rw 29 q19 ∷
   rw 28 q20 ∷
   re 28 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q21 ∷
   re 28 5 (CX30 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q17 ∷
   re 32 3 (CS13⁻ ∷ []) ∷
   rw 31 q18 ∷
   rw 30 q19 ∷
   rw 29 q20 ∷
   re 29 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 28 q21 ∷
   re 29 5 (CX30 ∷ []) ∷
   rw 10 q25 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q17 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw 12 q18 ∷
   rw 11 q19 ∷
   rw 10 q20 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q21 ∷
   re 10 5 (CX30 ∷ []) ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q17 ∷
   re 14 3 (CK31⁻ ∷ []) ∷
   rw 13 q22 ∷
   rw 12 q23 ∷
   rw 11 q24 ∷
   re 11 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q21 ∷
   re 11 5 (CX30 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q17 ∷
   re 15 3 (CS13⁻ ∷ []) ∷
   rw 14 q18 ∷
   rw 13 q19 ∷
   rw 12 q20 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q21 ∷
   re 12 5 (CX30 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q17 ∷
   re 16 3 (CS13⁻ ∷ []) ∷
   rw 15 q18 ∷
   rw 14 q19 ∷
   rw 13 q20 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q21 ∷
   re 13 5 (CX30 ∷ []) ∷
   rw 3 q26 ∷
   rw 35 q1 ∷
   rw 36 q27 ∷
   rw 37 q1 ∷
   rw 34 q1 ∷
   rw 35 q27 ∷
   rw 36 q1 ∷
   rw 33 q3 ∷
   rw 34 q28 ∷
   rw 35 q3 ∷
   rw 32 q1 ∷
   rw 33 q27 ∷
   rw 34 q1 ∷
   rw 31 q3 ∷
   rw 32 q28 ∷
   rw 33 q3 ∷
   rw 30 q3 ∷
   rw 31 q28 ∷
   rw 32 q3 ∷
   rw 33 q5 ∷
   rw⁻ 32 q6 ∷
   rw⁻ 31 q29 ∷
   rw⁻ 30 q6 ∷
   re 29 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q8 ∷
   rw 30 q9 ∷
   rw⁻ 29 q8 ∷
   re 30 3 (CX31 ∷ []) ∷
   rw 30 q30 ∷
   rw 29 q6 ∷
   rw 30 q29 ∷
   rw 31 q6 ∷
   re 33 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 32 q8 ∷
   rw 33 q11 ∷
   rw 34 q8 ∷
   re 32 3 (CX30 ∷ []) ∷
   rw 33 q12 ∷
   rw 28 q3 ∷
   rw 29 q28 ∷
   rw 30 q3 ∷
   rw 27 q3 ∷
   rw 28 q28 ∷
   rw 29 q3 ∷
   rw 26 q3 ∷
   rw 27 q28 ∷
   rw 28 q3 ∷
   rw 25 q3 ∷
   rw 26 q28 ∷
   rw 27 q3 ∷
   rw 24 q3 ∷
   rw 25 q28 ∷
   rw 26 q3 ∷
   rw 23 q3 ∷
   rw 24 q28 ∷
   rw 25 q3 ∷
   rw 22 q13 ∷
   rw 23 q31 ∷
   rw 24 q13 ∷
   rw 21 q1 ∷
   rw 22 q27 ∷
   rw 23 q1 ∷
   rw 20 q3 ∷
   rw 21 q28 ∷
   rw 22 q3 ∷
   rw 19 q3 ∷
   rw 20 q28 ∷
   rw 21 q3 ∷
   rw 18 q3 ∷
   rw 19 q28 ∷
   rw 20 q3 ∷
   rw 17 q13 ∷
   rw 18 q31 ∷
   rw 19 q13 ∷
   rw 16 q1 ∷
   rw 17 q27 ∷
   rw 18 q1 ∷
   rw 15 q13 ∷
   rw 16 q31 ∷
   rw 17 q13 ∷
   rw 14 q1 ∷
   rw 15 q27 ∷
   rw 16 q1 ∷
   rw 17 q5 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 15 q29 ∷
   rw⁻ 14 q6 ∷
   re 13 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q8 ∷
   rw 14 q9 ∷
   rw⁻ 13 q8 ∷
   re 14 3 (CX31 ∷ []) ∷
   rw 14 q30 ∷
   rw 13 q6 ∷
   rw 14 q29 ∷
   rw 15 q6 ∷
   re 17 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 16 q8 ∷
   rw 17 q11 ∷
   rw 18 q8 ∷
   re 16 3 (CX30 ∷ []) ∷
   rw 17 q12 ∷
   rw 7 q32 ∷
   rw 33 q33 ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q17 ∷
   re 36 3 (CS13⁻ ∷ []) ∷
   rw 35 q18 ∷
   rw 34 q19 ∷
   rw 33 q20 ∷
   re 33 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 32 q21 ∷
   re 33 5 (CX30 ∷ []) ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q17 ∷
   re 37 3 (CS13⁻ ∷ []) ∷
   rw 36 q18 ∷
   rw 35 q19 ∷
   rw 34 q20 ∷
   re 34 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 33 q21 ∷
   re 34 5 (CX30 ∷ []) ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q17 ∷
   re 38 3 (CS13⁻ ∷ []) ∷
   rw 37 q18 ∷
   rw 36 q19 ∷
   rw 35 q20 ∷
   re 35 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 34 q21 ∷
   re 35 5 (CX30 ∷ []) ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q17 ∷
   re 39 3 (CS13⁻ ∷ []) ∷
   rw 38 q18 ∷
   rw 37 q19 ∷
   rw 36 q20 ∷
   re 36 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 35 q21 ∷
   re 36 5 (CX30 ∷ []) ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q17 ∷
   re 40 3 (CS13⁻ ∷ []) ∷
   rw 39 q18 ∷
   rw 38 q19 ∷
   rw 37 q20 ∷
   re 37 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 36 q21 ∷
   re 37 5 (CX30 ∷ []) ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q17 ∷
   re 41 3 (CS13⁻ ∷ []) ∷
   rw 40 q18 ∷
   rw 39 q19 ∷
   rw 38 q20 ∷
   re 38 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 37 q21 ∷
   re 38 5 (CX30 ∷ []) ∷
   rw 40 q5 ∷
   rw⁻ 39 q34 ∷
   re 38 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q8 ∷
   rw 39 q9 ∷
   rw⁻ 38 q8 ∷
   re 39 3 (CX31 ∷ []) ∷
   rw 39 q35 ∷
   rw 38 q34 ∷
   re 40 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 39 q8 ∷
   rw 40 q11 ∷
   rw 41 q8 ∷
   re 39 3 (CX30 ∷ []) ∷
   rw 40 q12 ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q17 ∷
   re 43 3 (CK31⁻ ∷ []) ∷
   rw 42 q22 ∷
   rw 41 q23 ∷
   rw 40 q24 ∷
   re 40 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 39 q21 ∷
   re 40 5 (CX30 ∷ []) ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q17 ∷
   re 44 3 (CS13⁻ ∷ []) ∷
   rw 43 q18 ∷
   rw 42 q19 ∷
   rw 41 q20 ∷
   re 41 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 40 q21 ∷
   re 41 5 (CX30 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q17 ∷
   re 45 3 (CS13⁻ ∷ []) ∷
   rw 44 q18 ∷
   rw 43 q19 ∷
   rw 42 q20 ∷
   re 42 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 41 q21 ∷
   re 42 5 (CX30 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q17 ∷
   re 46 3 (CS13⁻ ∷ []) ∷
   rw 45 q18 ∷
   rw 44 q19 ∷
   rw 43 q20 ∷
   re 43 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 42 q21 ∷
   re 43 5 (CX30 ∷ []) ∷
   rw 17 q36 ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q17 ∷
   re 20 3 (CS13⁻ ∷ []) ∷
   rw 19 q18 ∷
   rw 18 q19 ∷
   rw 17 q20 ∷
   re 17 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q21 ∷
   re 17 5 (CX30 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q17 ∷
   re 21 3 (CS13⁻ ∷ []) ∷
   rw 20 q18 ∷
   rw 19 q19 ∷
   rw 18 q20 ∷
   re 18 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q21 ∷
   re 18 5 (CX30 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q17 ∷
   re 22 3 (CS13⁻ ∷ []) ∷
   rw 21 q18 ∷
   rw 20 q19 ∷
   rw 19 q20 ∷
   re 19 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q21 ∷
   re 19 5 (CX30 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q17 ∷
   re 23 3 (CS13⁻ ∷ []) ∷
   rw 22 q18 ∷
   rw 21 q19 ∷
   rw 20 q20 ∷
   re 20 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q21 ∷
   re 20 5 (CX30 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q17 ∷
   re 24 3 (CS13⁻ ∷ []) ∷
   rw 23 q18 ∷
   rw 22 q19 ∷
   rw 21 q20 ∷
   re 21 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q21 ∷
   re 21 5 (CX30 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q17 ∷
   re 25 3 (CS13⁻ ∷ []) ∷
   rw 24 q18 ∷
   rw 23 q19 ∷
   rw 22 q20 ∷
   re 22 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q21 ∷
   re 22 5 (CX30 ∷ []) ∷
   rw 24 q5 ∷
   rw⁻ 23 q34 ∷
   re 22 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q8 ∷
   rw 23 q9 ∷
   rw⁻ 22 q8 ∷
   re 23 3 (CX31 ∷ []) ∷
   rw 23 q35 ∷
   rw 22 q34 ∷
   re 24 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 23 q8 ∷
   rw 24 q11 ∷
   rw 25 q8 ∷
   re 23 3 (CX30 ∷ []) ∷
   rw 24 q12 ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q17 ∷
   re 27 3 (CK31⁻ ∷ []) ∷
   rw 26 q22 ∷
   rw 25 q23 ∷
   rw 24 q24 ∷
   re 24 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 23 q21 ∷
   re 24 5 (CX30 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q17 ∷
   re 28 3 (CS13⁻ ∷ []) ∷
   rw 27 q18 ∷
   rw 26 q19 ∷
   rw 25 q20 ∷
   re 25 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 24 q21 ∷
   re 25 5 (CX30 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q17 ∷
   re 29 3 (CS13⁻ ∷ []) ∷
   rw 28 q18 ∷
   rw 27 q19 ∷
   rw 26 q20 ∷
   re 26 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q21 ∷
   re 26 5 (CX30 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q17 ∷
   re 30 3 (CS13⁻ ∷ []) ∷
   rw 29 q18 ∷
   rw 28 q19 ∷
   rw 27 q20 ∷
   re 27 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q21 ∷
   re 27 5 (CX30 ∷ []) ∷
   rw 10 q37 ∷
   rw 49 q1 ∷
   rw 50 q27 ∷
   rw 51 q1 ∷
   rw 48 q1 ∷
   rw 49 q27 ∷
   rw 50 q1 ∷
   rw 47 q3 ∷
   rw 48 q28 ∷ []) Eq.refl

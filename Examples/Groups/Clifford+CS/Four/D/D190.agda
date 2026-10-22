{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D190 (W : Ws) where

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
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 353 W
  q3 : Eqn
  q3 = eqn (CX10 ∷ CK23⁻ ∷ []) (CK23⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((S • CK₀₁)))
  q4 : Eqn
  q4 = wE 358 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 21 W
  q7 : Eqn
  q7 = eqn (CX10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((CS • CS • CS)))
  q8 : Eqn
  q8 = wE 51 W
  q9 : Eqn
  q9 = wE 777 W
  q10 : Eqn
  q10 = wE 778 W
  q11 : Eqn
  q11 = eqn (CK02 ∷ X3 ∷ []) (X3 ∷ CK02 ∷ []) (low₃-comm ((Swap ↑ • CK₀₁ • Swap ↑)) (X))
  q12 : Eqn
  q12 = wE 113 W
  q13 : Eqn
  q13 = eqn (CK01 ∷ CX32 ∷ []) (CX32 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₁₀))
  q14 : Eqn
  q14 = wE 114 W
  q15 : Eqn
  q15 = eqn (CS02 ∷ X3 ∷ []) (X3 ∷ CS02 ∷ []) (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q16 : Eqn
  q16 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q17 : Eqn
  q17 = wE 173 W
  q18 : Eqn
  q18 = wE 779 W
  q19 : Eqn
  q19 = wE 175 W
  q20 : Eqn
  q20 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q21 : Eqn
  q21 = eqn (S0 ∷ CX31 ∷ []) (CX31 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑ • CX₁₀ • Swap ↑)))
  q22 : Eqn
  q22 = wE 780 W
  q23 : Eqn
  q23 = wE 781 W
  q24 : Eqn
  q24 = eqn (S1⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (Swap))
  q25 : Eqn
  q25 = wE 782 W

-- Bar(['S', 'S', 'K', 'S', 'K', 'K'];3,0->2) passes white iX via V2 conjugates 1 part3: 500 steps
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part3 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS12⁻ ∷ CX30 ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part3 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS12⁻ ∷ CX30 ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ [])
  (re 58 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 64 q1 ∷
   re 62 3 (CK13⁻ ∷ []) ∷
   rw 61 q2 ∷
   rw 60 q3 ∷
   rw 59 q4 ∷
   re 59 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 58 q5 ∷
   re 59 5 (CX30 ∷ []) ∷
   re 59 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 65 q1 ∷
   re 63 3 (CS13⁻ ∷ []) ∷
   rw 62 q6 ∷
   rw 61 q7 ∷
   rw 60 q8 ∷
   re 60 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 59 q5 ∷
   re 60 5 (CX30 ∷ []) ∷
   re 60 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 66 q1 ∷
   re 64 3 (CS13⁻ ∷ []) ∷
   rw 63 q6 ∷
   rw 62 q7 ∷
   rw 61 q8 ∷
   re 61 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 60 q5 ∷
   re 61 5 (CX30 ∷ []) ∷
   rw 42 q9 ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   re 45 3 (CS13⁻ ∷ []) ∷
   rw 44 q6 ∷
   rw 43 q7 ∷
   rw 42 q8 ∷
   re 42 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 41 q5 ∷
   re 42 5 (CX30 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q1 ∷
   re 46 3 (CK13⁻ ∷ []) ∷
   rw 45 q2 ∷
   rw 44 q3 ∷
   rw 43 q4 ∷
   re 43 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 42 q5 ∷
   re 43 5 (CX30 ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   re 47 3 (CS13⁻ ∷ []) ∷
   rw 46 q6 ∷
   rw 45 q7 ∷
   rw 44 q8 ∷
   re 44 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 43 q5 ∷
   re 44 5 (CX30 ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q1 ∷
   re 48 3 (CS13⁻ ∷ []) ∷
   rw 47 q6 ∷
   rw 46 q7 ∷
   rw 45 q8 ∷
   re 45 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 44 q5 ∷
   re 45 5 (CX30 ∷ []) ∷
   rw 35 q10 ∷
   rw 67 q11 ∷
   re 69 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 68 q1 ∷
   re 69 3 (CK03 ∷ []) ∷
   re 69 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 75 q1 ∷
   re 73 3 (CX31 ∷ []) ∷
   rw 72 q12 ∷
   rw 71 q13 ∷
   rw 70 q14 ∷
   re 70 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 69 q5 ∷
   re 70 5 (CK03 ∷ []) ∷
   re 70 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 72 q5 ∷
   re 68 3 (CX31 ∷ []) ∷
   rw 69 q11 ∷
   rw 66 q11 ∷
   re 68 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 67 q1 ∷
   re 68 3 (CK03 ∷ []) ∷
   re 68 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 74 q1 ∷
   re 72 3 (CX31 ∷ []) ∷
   rw 71 q12 ∷
   rw 70 q13 ∷
   rw 69 q14 ∷
   re 69 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 68 q5 ∷
   re 69 5 (CK03 ∷ []) ∷
   re 69 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 71 q5 ∷
   re 67 3 (CX31 ∷ []) ∷
   rw 68 q11 ∷
   rw 65 q15 ∷
   re 67 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 66 q1 ∷
   re 67 3 (CS03 ∷ []) ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q1 ∷
   re 71 3 (CX31 ∷ []) ∷
   rw 70 q12 ∷
   rw 69 q16 ∷
   rw 68 q14 ∷
   re 68 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 67 q5 ∷
   re 68 5 (CS03 ∷ []) ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 70 q5 ∷
   re 66 3 (CX31 ∷ []) ∷
   rw 67 q15 ∷
   rw 64 q11 ∷
   re 66 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 65 q1 ∷
   re 66 3 (CK03 ∷ []) ∷
   re 66 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 72 q1 ∷
   re 70 3 (CX31 ∷ []) ∷
   rw 69 q12 ∷
   rw 68 q13 ∷
   rw 67 q14 ∷
   re 67 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 66 q5 ∷
   re 67 5 (CK03 ∷ []) ∷
   re 67 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 69 q5 ∷
   re 65 3 (CX31 ∷ []) ∷
   rw 66 q11 ∷
   rw 63 q15 ∷
   re 65 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 64 q1 ∷
   re 65 3 (CS03 ∷ []) ∷
   re 65 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q1 ∷
   re 69 3 (CX31 ∷ []) ∷
   rw 68 q12 ∷
   rw 67 q16 ∷
   rw 66 q14 ∷
   re 66 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 65 q5 ∷
   re 66 5 (CS03 ∷ []) ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 68 q5 ∷
   re 64 3 (CX31 ∷ []) ∷
   rw 65 q15 ∷
   rw 62 q15 ∷
   re 64 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 63 q1 ∷
   re 64 3 (CS03 ∷ []) ∷
   re 64 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 70 q1 ∷
   re 68 3 (CX31 ∷ []) ∷
   rw 67 q12 ∷
   rw 66 q16 ∷
   rw 65 q14 ∷
   re 65 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 64 q5 ∷
   re 65 5 (CS03 ∷ []) ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q5 ∷
   re 63 3 (CX31 ∷ []) ∷
   rw 64 q15 ∷
   rw 65 q1 ∷
   rw 64 q17 ∷
   re 63 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 65 q5 ∷
   rw 62 q17 ∷
   re 61 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 63 q5 ∷
   rw 62 q18 ∷
   rw 61 q19 ∷
   rw 64 q1 ∷
   re 62 3 (CX31 ∷ []) ∷
   rw 63 q19 ∷
   rw 66 q1 ∷
   re 64 3 (CX30 ∷ []) ∷
   rw 65 q5 ∷
   rw 60 q15 ∷
   re 62 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 61 q1 ∷
   re 62 3 (CS03 ∷ []) ∷
   re 62 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 68 q1 ∷
   re 66 3 (CX31 ∷ []) ∷
   rw 65 q12 ∷
   rw 64 q16 ∷
   rw 63 q14 ∷
   re 63 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 62 q5 ∷
   re 63 5 (CS03 ∷ []) ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 65 q5 ∷
   re 61 3 (CX31 ∷ []) ∷
   rw 62 q15 ∷
   rw 59 q15 ∷
   re 61 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 60 q1 ∷
   re 61 3 (CS03 ∷ []) ∷
   re 61 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 67 q1 ∷
   re 65 3 (CX31 ∷ []) ∷
   rw 64 q12 ∷
   rw 63 q16 ∷
   rw 62 q14 ∷
   re 62 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 61 q5 ∷
   re 62 5 (CS03 ∷ []) ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 64 q5 ∷
   re 60 3 (CX31 ∷ []) ∷
   rw 61 q15 ∷
   rw 58 q15 ∷
   re 60 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 59 q1 ∷
   re 60 3 (CS03 ∷ []) ∷
   re 60 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 66 q1 ∷
   re 64 3 (CX31 ∷ []) ∷
   rw 63 q12 ∷
   rw 62 q16 ∷
   rw 61 q14 ∷
   re 61 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 60 q5 ∷
   re 61 5 (CS03 ∷ []) ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 63 q5 ∷
   re 59 3 (CX31 ∷ []) ∷
   rw 60 q15 ∷
   rw 57 q15 ∷
   re 59 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 58 q1 ∷
   re 59 3 (CS03 ∷ []) ∷
   re 59 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 65 q1 ∷
   re 63 3 (CX31 ∷ []) ∷
   rw 62 q12 ∷
   rw 61 q16 ∷
   rw 60 q14 ∷
   re 60 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 59 q5 ∷
   re 60 5 (CS03 ∷ []) ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 62 q5 ∷
   re 58 3 (CX31 ∷ []) ∷
   rw 59 q15 ∷
   rw 56 q15 ∷
   re 58 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 57 q1 ∷
   re 58 3 (CS03 ∷ []) ∷
   re 58 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 64 q1 ∷
   re 62 3 (CX31 ∷ []) ∷
   rw 61 q12 ∷
   rw 60 q16 ∷
   rw 59 q14 ∷
   re 59 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 58 q5 ∷
   re 59 5 (CS03 ∷ []) ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 61 q5 ∷
   re 57 3 (CX31 ∷ []) ∷
   rw 58 q15 ∷
   rw 55 q15 ∷
   re 57 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 56 q1 ∷
   re 57 3 (CS03 ∷ []) ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 63 q1 ∷
   re 61 3 (CX31 ∷ []) ∷
   rw 60 q12 ∷
   rw 59 q16 ∷
   rw 58 q14 ∷
   re 58 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 57 q5 ∷
   re 58 5 (CS03 ∷ []) ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q5 ∷
   re 56 3 (CX31 ∷ []) ∷
   rw 57 q15 ∷
   rw 54 q20 ∷
   rw 55 q21 ∷
   rw 56 q20 ∷
   rw 53 q11 ∷
   re 55 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 54 q1 ∷
   re 55 3 (CK03 ∷ []) ∷
   re 55 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 61 q1 ∷
   re 59 3 (CX31 ∷ []) ∷
   rw 58 q12 ∷
   rw 57 q13 ∷
   rw 56 q14 ∷
   re 56 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 55 q5 ∷
   re 56 5 (CK03 ∷ []) ∷
   re 56 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 58 q5 ∷
   re 54 3 (CX31 ∷ []) ∷
   rw 55 q11 ∷
   rw 52 q15 ∷
   re 54 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 53 q1 ∷
   re 54 3 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 60 q1 ∷
   re 58 3 (CX31 ∷ []) ∷
   rw 57 q12 ∷
   rw 56 q16 ∷
   rw 55 q14 ∷
   re 55 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 54 q5 ∷
   re 55 5 (CS03 ∷ []) ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q5 ∷
   re 53 3 (CX31 ∷ []) ∷
   rw 54 q15 ∷
   rw 51 q15 ∷
   re 53 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 52 q1 ∷
   re 53 3 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q1 ∷
   re 57 3 (CX31 ∷ []) ∷
   rw 56 q12 ∷
   rw 55 q16 ∷
   rw 54 q14 ∷
   re 54 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 53 q5 ∷
   re 54 5 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q5 ∷
   re 52 3 (CX31 ∷ []) ∷
   rw 53 q15 ∷
   rw 50 q15 ∷
   re 52 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 51 q1 ∷
   re 52 3 (CS03 ∷ []) ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q1 ∷
   re 56 3 (CX31 ∷ []) ∷
   rw 55 q12 ∷
   rw 54 q16 ∷
   rw 53 q14 ∷
   re 53 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 52 q5 ∷
   re 53 5 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 55 q5 ∷
   re 51 3 (CX31 ∷ []) ∷
   rw 52 q15 ∷
   rw 49 q20 ∷
   rw 50 q21 ∷
   rw 51 q20 ∷
   rw 48 q11 ∷
   re 50 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   re 50 3 (CK03 ∷ []) ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q1 ∷
   re 54 3 (CX31 ∷ []) ∷
   rw 53 q12 ∷
   rw 52 q13 ∷
   rw 51 q14 ∷
   re 51 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 50 q5 ∷
   re 51 5 (CK03 ∷ []) ∷
   re 51 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 53 q5 ∷
   re 49 3 (CX31 ∷ []) ∷
   rw 50 q11 ∷
   rw 47 q20 ∷
   rw 48 q21 ∷
   rw 49 q20 ∷
   rw 46 q11 ∷
   re 48 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   re 48 3 (CK03 ∷ []) ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q1 ∷
   re 52 3 (CX31 ∷ []) ∷
   rw 51 q12 ∷
   rw 50 q13 ∷
   rw 49 q14 ∷
   re 49 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 48 q5 ∷
   re 49 5 (CK03 ∷ []) ∷
   re 49 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 51 q5 ∷
   re 47 3 (CX31 ∷ []) ∷
   rw 48 q11 ∷
   rw 49 q1 ∷
   rw 48 q17 ∷
   re 47 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 49 q5 ∷
   rw 46 q17 ∷
   re 45 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 47 q5 ∷
   rw 46 q18 ∷
   rw 45 q19 ∷
   rw 48 q1 ∷
   re 46 3 (CX31 ∷ []) ∷
   rw 47 q19 ∷
   rw 50 q1 ∷
   re 48 3 (CX30 ∷ []) ∷
   rw 49 q5 ∷
   rw 39 q22 ∷
   rw 65 q23 ∷
   re 64 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 70 q1 ∷
   re 68 3 (CS13⁻ ∷ []) ∷
   rw 67 q6 ∷
   rw 66 q7 ∷
   rw 65 q8 ∷
   re 65 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 64 q5 ∷
   re 65 5 (CX30 ∷ []) ∷
   re 65 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q1 ∷
   re 69 3 (CS13⁻ ∷ []) ∷
   rw 68 q6 ∷
   rw 67 q7 ∷
   rw 66 q8 ∷
   re 66 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 65 q5 ∷
   re 66 5 (CX30 ∷ []) ∷
   re 66 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 72 q1 ∷
   re 70 3 (CS13⁻ ∷ []) ∷
   rw 69 q6 ∷
   rw 68 q7 ∷
   rw 67 q8 ∷
   re 67 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 66 q5 ∷
   re 67 5 (CX30 ∷ []) ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q1 ∷
   re 71 3 (CS13⁻ ∷ []) ∷
   rw 70 q6 ∷
   rw 69 q7 ∷
   rw 68 q8 ∷
   re 68 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 67 q5 ∷
   re 68 5 (CX30 ∷ []) ∷
   re 68 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 74 q1 ∷
   re 72 3 (CS13⁻ ∷ []) ∷
   rw 71 q6 ∷
   rw 70 q7 ∷
   rw 69 q8 ∷
   re 69 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 68 q5 ∷
   re 69 5 (CX30 ∷ []) ∷
   re 69 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 75 q1 ∷
   re 73 3 (CS13⁻ ∷ []) ∷
   rw 72 q6 ∷
   rw 71 q7 ∷
   rw 70 q8 ∷
   re 70 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 69 q5 ∷
   re 70 5 (CX30 ∷ []) ∷
   rw 72 q1 ∷
   rw 71 q24 ∷
   re 70 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 72 q5 ∷
   rw 71 q25 ∷
   rw⁻ 70 q24 ∷
   rw 73 q1 ∷
   re 71 3 (CX30 ∷ []) ∷
   rw 72 q5 ∷
   re 71 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 77 q1 ∷
   re 75 3 (CK13⁻ ∷ []) ∷
   rw 74 q2 ∷
   rw 73 q3 ∷
   rw 72 q4 ∷
   re 72 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 71 q5 ∷
   re 72 5 (CX30 ∷ []) ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 78 q1 ∷
   re 76 3 (CS13⁻ ∷ []) ∷
   rw 75 q6 ∷
   rw 74 q7 ∷
   rw 73 q8 ∷
   re 73 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 72 q5 ∷
   re 73 5 (CX30 ∷ []) ∷
   re 73 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 79 q1 ∷
   re 77 3 (CS13⁻ ∷ []) ∷
   rw 76 q6 ∷
   rw 75 q7 ∷
   rw 74 q8 ∷
   re 74 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷ []) Eq.refl

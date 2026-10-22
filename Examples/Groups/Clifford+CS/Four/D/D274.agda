{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D274 (W : Ws) where

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
  q1 = wE 27 W
  q2 : Eqn
  q2 = wE 31 W
  q3 : Eqn
  q3 = wE 777 W
  q4 : Eqn
  q4 = wE 1 W
  q5 : Eqn
  q5 = wE 21 W
  q6 : Eqn
  q6 = eqn (CX10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((CS • CS • CS)))
  q7 : Eqn
  q7 = wE 51 W
  q8 : Eqn
  q8 = wE 3 W
  q9 : Eqn
  q9 = wE 353 W
  q10 : Eqn
  q10 = eqn (CX10 ∷ CK23⁻ ∷ []) (CK23⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((S • CK₀₁)))
  q11 : Eqn
  q11 = wE 358 W
  q12 : Eqn
  q12 = wE 856 W
  q13 : Eqn
  q13 = wE 857 W
  q14 : Eqn
  q14 = eqn (CS02 ∷ X3 ∷ []) (X3 ∷ CS02 ∷ []) (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q15 : Eqn
  q15 = wE 113 W
  q16 : Eqn
  q16 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q17 : Eqn
  q17 = wE 114 W
  q18 : Eqn
  q18 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q19 : Eqn
  q19 = eqn (S0 ∷ CX31 ∷ []) (CX31 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑ • CX₁₀ • Swap ↑)))
  q20 : Eqn
  q20 = eqn (CK02 ∷ X3 ∷ []) (X3 ∷ CK02 ∷ []) (low₃-comm ((Swap ↑ • CK₀₁ • Swap ↑)) (X))
  q21 : Eqn
  q21 = eqn (CK01 ∷ CX32 ∷ []) (CX32 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₁₀))
  q22 : Eqn
  q22 = wE 173 W
  q23 : Eqn
  q23 = wE 779 W
  q24 : Eqn
  q24 = wE 175 W

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];3,0->2) passes white iX via V2 conjugates 1 part6: 500 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part6 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw01 ∷ CS12 ∷ Sw01 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ X3 ∷ CS02 ∷ CX31 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part6 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw01 ∷ CS12 ∷ Sw01 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ X3 ∷ CS02 ∷ CX31 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ [])
  (rw 108 q1 ∷
   rw 109 q2 ∷
   rw 94 q3 ∷
   re 93 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 99 q4 ∷
   re 97 3 (CS13⁻ ∷ []) ∷
   rw 96 q5 ∷
   rw 95 q6 ∷
   rw 94 q7 ∷
   re 94 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 93 q8 ∷
   re 94 5 (CX30 ∷ []) ∷
   re 94 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 100 q4 ∷
   re 98 3 (CK13⁻ ∷ []) ∷
   rw 97 q9 ∷
   rw 96 q10 ∷
   rw 95 q11 ∷
   re 95 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 94 q8 ∷
   re 95 5 (CX30 ∷ []) ∷
   re 95 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 101 q4 ∷
   re 99 3 (CS13⁻ ∷ []) ∷
   rw 98 q5 ∷
   rw 97 q6 ∷
   rw 96 q7 ∷
   re 96 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 95 q8 ∷
   re 96 5 (CX30 ∷ []) ∷
   re 96 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 102 q4 ∷
   re 100 3 (CS13⁻ ∷ []) ∷
   rw 99 q5 ∷
   rw 98 q6 ∷
   rw 97 q7 ∷
   re 97 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 96 q8 ∷
   re 97 5 (CX30 ∷ []) ∷
   rw 51 q12 ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q4 ∷
   re 54 3 (CS13⁻ ∷ []) ∷
   rw 53 q5 ∷
   rw 52 q6 ∷
   rw 51 q7 ∷
   re 51 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 50 q8 ∷
   re 51 5 (CX30 ∷ []) ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 57 q4 ∷
   re 55 3 (CK13⁻ ∷ []) ∷
   rw 54 q9 ∷
   rw 53 q10 ∷
   rw 52 q11 ∷
   re 52 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 51 q8 ∷
   re 52 5 (CX30 ∷ []) ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q4 ∷
   re 56 3 (CS13⁻ ∷ []) ∷
   rw 55 q5 ∷
   rw 54 q6 ∷
   rw 53 q7 ∷
   re 53 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 52 q8 ∷
   re 53 5 (CX30 ∷ []) ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q4 ∷
   re 57 3 (CS13⁻ ∷ []) ∷
   rw 56 q5 ∷
   rw 55 q6 ∷
   rw 54 q7 ∷
   re 54 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 53 q8 ∷
   re 54 5 (CX30 ∷ []) ∷
   rw 35 q13 ∷
   rw 112 q14 ∷
   re 114 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 113 q4 ∷
   re 114 3 (CS03 ∷ []) ∷
   re 114 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 120 q4 ∷
   re 118 3 (CX31 ∷ []) ∷
   rw 117 q15 ∷
   rw 116 q16 ∷
   rw 115 q17 ∷
   re 115 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 114 q8 ∷
   re 115 5 (CS03 ∷ []) ∷
   re 115 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 117 q8 ∷
   re 113 3 (CX31 ∷ []) ∷
   rw 114 q14 ∷
   rw 111 q14 ∷
   re 113 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 112 q4 ∷
   re 113 3 (CS03 ∷ []) ∷
   re 113 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 119 q4 ∷
   re 117 3 (CX31 ∷ []) ∷
   rw 116 q15 ∷
   rw 115 q16 ∷
   rw 114 q17 ∷
   re 114 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 113 q8 ∷
   re 114 5 (CS03 ∷ []) ∷
   re 114 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 116 q8 ∷
   re 112 3 (CX31 ∷ []) ∷
   rw 113 q14 ∷
   rw 110 q14 ∷
   re 112 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 111 q4 ∷
   re 112 3 (CS03 ∷ []) ∷
   re 112 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 118 q4 ∷
   re 116 3 (CX31 ∷ []) ∷
   rw 115 q15 ∷
   rw 114 q16 ∷
   rw 113 q17 ∷
   re 113 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 112 q8 ∷
   re 113 5 (CS03 ∷ []) ∷
   re 113 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 115 q8 ∷
   re 111 3 (CX31 ∷ []) ∷
   rw 112 q14 ∷
   rw 109 q14 ∷
   re 111 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 110 q4 ∷
   re 111 3 (CS03 ∷ []) ∷
   re 111 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 117 q4 ∷
   re 115 3 (CX31 ∷ []) ∷
   rw 114 q15 ∷
   rw 113 q16 ∷
   rw 112 q17 ∷
   re 112 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 111 q8 ∷
   re 112 5 (CS03 ∷ []) ∷
   re 112 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 114 q8 ∷
   re 110 3 (CX31 ∷ []) ∷
   rw 111 q14 ∷
   rw 108 q14 ∷
   re 110 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 109 q4 ∷
   re 110 3 (CS03 ∷ []) ∷
   re 110 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 116 q4 ∷
   re 114 3 (CX31 ∷ []) ∷
   rw 113 q15 ∷
   rw 112 q16 ∷
   rw 111 q17 ∷
   re 111 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 110 q8 ∷
   re 111 5 (CS03 ∷ []) ∷
   re 111 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 113 q8 ∷
   re 109 3 (CX31 ∷ []) ∷
   rw 110 q14 ∷
   rw 107 q14 ∷
   re 109 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 108 q4 ∷
   re 109 3 (CS03 ∷ []) ∷
   re 109 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 115 q4 ∷
   re 113 3 (CX31 ∷ []) ∷
   rw 112 q15 ∷
   rw 111 q16 ∷
   rw 110 q17 ∷
   re 110 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 109 q8 ∷
   re 110 5 (CS03 ∷ []) ∷
   re 110 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 112 q8 ∷
   re 108 3 (CX31 ∷ []) ∷
   rw 109 q14 ∷
   rw 106 q18 ∷
   rw 107 q19 ∷
   rw 108 q18 ∷
   rw 105 q20 ∷
   re 107 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 106 q4 ∷
   re 107 3 (CK03 ∷ []) ∷
   re 107 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 113 q4 ∷
   re 111 3 (CX31 ∷ []) ∷
   rw 110 q15 ∷
   rw 109 q21 ∷
   rw 108 q17 ∷
   re 108 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 107 q8 ∷
   re 108 5 (CK03 ∷ []) ∷
   re 108 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 110 q8 ∷
   re 106 3 (CX31 ∷ []) ∷
   rw 107 q20 ∷
   rw 104 q14 ∷
   re 106 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 105 q4 ∷
   re 106 3 (CS03 ∷ []) ∷
   re 106 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 112 q4 ∷
   re 110 3 (CX31 ∷ []) ∷
   rw 109 q15 ∷
   rw 108 q16 ∷
   rw 107 q17 ∷
   re 107 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 106 q8 ∷
   re 107 5 (CS03 ∷ []) ∷
   re 107 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 109 q8 ∷
   re 105 3 (CX31 ∷ []) ∷
   rw 106 q14 ∷
   rw 103 q14 ∷
   re 105 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 104 q4 ∷
   re 105 3 (CS03 ∷ []) ∷
   re 105 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 111 q4 ∷
   re 109 3 (CX31 ∷ []) ∷
   rw 108 q15 ∷
   rw 107 q16 ∷
   rw 106 q17 ∷
   re 106 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 105 q8 ∷
   re 106 5 (CS03 ∷ []) ∷
   re 106 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 108 q8 ∷
   re 104 3 (CX31 ∷ []) ∷
   rw 105 q14 ∷
   rw 102 q14 ∷
   re 104 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 103 q4 ∷
   re 104 3 (CS03 ∷ []) ∷
   re 104 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 110 q4 ∷
   re 108 3 (CX31 ∷ []) ∷
   rw 107 q15 ∷
   rw 106 q16 ∷
   rw 105 q17 ∷
   re 105 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 104 q8 ∷
   re 105 5 (CS03 ∷ []) ∷
   re 105 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 107 q8 ∷
   re 103 3 (CX31 ∷ []) ∷
   rw 104 q14 ∷
   rw 101 q18 ∷
   rw 102 q19 ∷
   rw 103 q18 ∷
   rw 100 q20 ∷
   re 102 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 101 q4 ∷
   re 102 3 (CK03 ∷ []) ∷
   re 102 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 108 q4 ∷
   re 106 3 (CX31 ∷ []) ∷
   rw 105 q15 ∷
   rw 104 q21 ∷
   rw 103 q17 ∷
   re 103 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 102 q8 ∷
   re 103 5 (CK03 ∷ []) ∷
   re 103 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 105 q8 ∷
   re 101 3 (CX31 ∷ []) ∷
   rw 102 q20 ∷
   rw 99 q18 ∷
   rw 100 q19 ∷
   rw 101 q18 ∷
   rw 98 q20 ∷
   re 100 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 99 q4 ∷
   re 100 3 (CK03 ∷ []) ∷
   re 100 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 106 q4 ∷
   re 104 3 (CX31 ∷ []) ∷
   rw 103 q15 ∷
   rw 102 q21 ∷
   rw 101 q17 ∷
   re 101 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 100 q8 ∷
   re 101 5 (CK03 ∷ []) ∷
   re 101 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 103 q8 ∷
   re 99 3 (CX31 ∷ []) ∷
   rw 100 q20 ∷
   rw 101 q4 ∷
   rw 100 q22 ∷
   re 99 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 101 q8 ∷
   rw 98 q22 ∷
   re 97 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 99 q8 ∷
   rw 98 q23 ∷
   rw 97 q24 ∷
   rw 100 q4 ∷
   re 98 3 (CX31 ∷ []) ∷
   rw 99 q24 ∷
   rw 102 q4 ∷
   re 100 3 (CX30 ∷ []) ∷
   rw 101 q8 ∷
   rw 96 q18 ∷
   rw 97 q19 ∷
   rw 98 q18 ∷
   rw 95 q20 ∷
   re 97 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 96 q4 ∷
   re 97 3 (CK03 ∷ []) ∷
   re 97 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 103 q4 ∷
   re 101 3 (CX31 ∷ []) ∷
   rw 100 q15 ∷
   rw 99 q21 ∷
   rw 98 q17 ∷
   re 98 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 97 q8 ∷
   re 98 5 (CK03 ∷ []) ∷
   re 98 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 100 q8 ∷
   re 96 3 (CX31 ∷ []) ∷
   rw 97 q20 ∷
   rw 94 q18 ∷
   rw 95 q19 ∷
   rw 96 q18 ∷
   rw 93 q18 ∷
   rw 94 q19 ∷
   rw 95 q18 ∷
   rw 92 q18 ∷
   rw 93 q19 ∷
   rw 94 q18 ∷
   rw 91 q18 ∷
   rw 92 q19 ∷
   rw 93 q18 ∷
   rw 90 q20 ∷
   re 92 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 91 q4 ∷
   re 92 3 (CK03 ∷ []) ∷
   re 92 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 98 q4 ∷
   re 96 3 (CX31 ∷ []) ∷
   rw 95 q15 ∷
   rw 94 q21 ∷
   rw 93 q17 ∷
   re 93 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 92 q8 ∷
   re 93 5 (CK03 ∷ []) ∷
   re 93 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 95 q8 ∷
   re 91 3 (CX31 ∷ []) ∷
   rw 92 q20 ∷
   rw 89 q18 ∷
   rw 90 q19 ∷
   rw 91 q18 ∷
   rw 88 q18 ∷
   rw 89 q19 ∷
   rw 90 q18 ∷
   rw 87 q18 ∷
   rw 88 q19 ∷
   rw 89 q18 ∷
   rw 86 q14 ∷
   re 88 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 87 q4 ∷
   re 88 3 (CS03 ∷ []) ∷
   re 88 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 94 q4 ∷
   re 92 3 (CX31 ∷ []) ∷
   rw 91 q15 ∷
   rw 90 q16 ∷
   rw 89 q17 ∷
   re 89 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 88 q8 ∷
   re 89 5 (CS03 ∷ []) ∷
   re 89 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 91 q8 ∷
   re 87 3 (CX31 ∷ []) ∷
   rw 88 q14 ∷
   rw 85 q14 ∷
   re 87 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 86 q4 ∷
   re 87 3 (CS03 ∷ []) ∷
   re 87 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 93 q4 ∷
   re 91 3 (CX31 ∷ []) ∷
   rw 90 q15 ∷
   rw 89 q16 ∷
   rw 88 q17 ∷
   re 88 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 87 q8 ∷
   re 88 5 (CS03 ∷ []) ∷
   re 88 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 90 q8 ∷
   re 86 3 (CX31 ∷ []) ∷
   rw 87 q14 ∷
   rw 84 q14 ∷
   re 86 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 85 q4 ∷
   re 86 3 (CS03 ∷ []) ∷
   re 86 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 92 q4 ∷
   re 90 3 (CX31 ∷ []) ∷
   rw 89 q15 ∷
   rw 88 q16 ∷
   rw 87 q17 ∷
   re 87 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 86 q8 ∷
   re 87 5 (CS03 ∷ []) ∷
   re 87 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 89 q8 ∷
   re 85 3 (CX31 ∷ []) ∷
   rw 86 q14 ∷
   rw 83 q14 ∷
   re 85 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 84 q4 ∷
   re 85 3 (CS03 ∷ []) ∷
   re 85 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 91 q4 ∷
   re 89 3 (CX31 ∷ []) ∷
   rw 88 q15 ∷
   rw 87 q16 ∷
   rw 86 q17 ∷
   re 86 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 85 q8 ∷
   re 86 5 (CS03 ∷ []) ∷
   re 86 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 88 q8 ∷
   re 84 3 (CX31 ∷ []) ∷
   rw 85 q14 ∷
   rw 82 q14 ∷
   re 84 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 83 q4 ∷
   re 84 3 (CS03 ∷ []) ∷
   re 84 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 90 q4 ∷
   re 88 3 (CX31 ∷ []) ∷
   rw 87 q15 ∷
   rw 86 q16 ∷
   rw 85 q17 ∷
   re 85 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 84 q8 ∷
   re 85 5 (CS03 ∷ []) ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 87 q8 ∷
   re 83 3 (CX31 ∷ []) ∷
   rw 84 q14 ∷
   rw 81 q14 ∷
   re 83 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 82 q4 ∷
   re 83 3 (CS03 ∷ []) ∷
   re 83 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 89 q4 ∷
   re 87 3 (CX31 ∷ []) ∷
   rw 86 q15 ∷
   rw 85 q16 ∷
   rw 84 q17 ∷
   re 84 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 83 q8 ∷
   re 84 5 (CS03 ∷ []) ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 86 q8 ∷
   re 82 3 (CX31 ∷ []) ∷
   rw 83 q14 ∷
   rw 80 q14 ∷
   re 82 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 81 q4 ∷
   re 82 3 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 88 q4 ∷
   re 86 3 (CX31 ∷ []) ∷
   rw 85 q15 ∷
   rw 84 q16 ∷
   rw 83 q17 ∷
   re 83 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 82 q8 ∷
   re 83 5 (CS03 ∷ []) ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 85 q8 ∷
   re 81 3 (CX31 ∷ []) ∷
   rw 82 q14 ∷
   rw 79 q14 ∷
   re 81 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 80 q4 ∷
   re 81 3 (CS03 ∷ []) ∷
   re 81 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 87 q4 ∷
   re 85 3 (CX31 ∷ []) ∷
   rw 84 q15 ∷
   rw 83 q16 ∷
   rw 82 q17 ∷
   re 82 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 81 q8 ∷
   re 82 5 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 84 q8 ∷
   re 80 3 (CX31 ∷ []) ∷
   rw 81 q14 ∷
   rw 78 q14 ∷ []) Eq.refl

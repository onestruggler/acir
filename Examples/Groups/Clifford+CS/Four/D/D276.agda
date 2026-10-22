{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D276 (W : Ws) where

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
  q1 = wE 51 W
  q2 : Eqn
  q2 = wE 3 W
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 21 W
  q5 : Eqn
  q5 = eqn (CX10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((CS • CS • CS)))
  q6 : Eqn
  q6 = eqn (S1⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (Swap))
  q7 : Eqn
  q7 = wE 782 W
  q8 : Eqn
  q8 = wE 353 W
  q9 : Eqn
  q9 = eqn (CX10 ∷ CK23⁻ ∷ []) (CK23⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((S • CK₀₁)))
  q10 : Eqn
  q10 = wE 358 W
  q11 : Eqn
  q11 = wE 860 W
  q12 : Eqn
  q12 = eqn (CS02 ∷ X3 ∷ []) (X3 ∷ CS02 ∷ []) (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q13 : Eqn
  q13 = wE 113 W
  q14 : Eqn
  q14 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q15 : Eqn
  q15 = wE 114 W
  q16 : Eqn
  q16 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q17 : Eqn
  q17 = eqn (S0 ∷ CX31 ∷ []) (CX31 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑ • CX₁₀ • Swap ↑)))
  q18 : Eqn
  q18 = eqn (CK02 ∷ X3 ∷ []) (X3 ∷ CK02 ∷ []) (low₃-comm ((Swap ↑ • CK₀₁ • Swap ↑)) (X))
  q19 : Eqn
  q19 = eqn (CK01 ∷ CX32 ∷ []) (CX32 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₁₀))
  q20 : Eqn
  q20 = wE 173 W
  q21 : Eqn
  q21 = wE 779 W
  q22 : Eqn
  q22 = wE 175 W

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];3,0->2) passes white iX via V2 conjugates 1 part8: 500 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part8 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ CX31 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part8 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ CX31 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ [])
  (rw 61 q1 ∷
   re 61 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 60 q2 ∷
   re 61 5 (CX30 ∷ []) ∷
   re 61 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 67 q3 ∷
   re 65 3 (CS13⁻ ∷ []) ∷
   rw 64 q4 ∷
   rw 63 q5 ∷
   rw 62 q1 ∷
   re 62 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 61 q2 ∷
   re 62 5 (CX30 ∷ []) ∷
   re 62 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 68 q3 ∷
   re 66 3 (CS13⁻ ∷ []) ∷
   rw 65 q4 ∷
   rw 64 q5 ∷
   rw 63 q1 ∷
   re 63 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 62 q2 ∷
   re 63 5 (CX30 ∷ []) ∷
   rw 65 q3 ∷
   rw 64 q6 ∷
   re 63 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 65 q2 ∷
   rw 64 q7 ∷
   rw⁻ 63 q6 ∷
   rw 66 q3 ∷
   re 64 3 (CX30 ∷ []) ∷
   rw 65 q2 ∷
   re 64 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 70 q3 ∷
   re 68 3 (CK13⁻ ∷ []) ∷
   rw 67 q8 ∷
   rw 66 q9 ∷
   rw 65 q10 ∷
   re 65 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 64 q2 ∷
   re 65 5 (CX30 ∷ []) ∷
   re 65 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q3 ∷
   re 69 3 (CS13⁻ ∷ []) ∷
   rw 68 q4 ∷
   rw 67 q5 ∷
   rw 66 q1 ∷
   re 66 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 65 q2 ∷
   re 66 5 (CX30 ∷ []) ∷
   re 66 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 72 q3 ∷
   re 70 3 (CS13⁻ ∷ []) ∷
   rw 69 q4 ∷
   rw 68 q5 ∷
   rw 67 q1 ∷
   re 67 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 66 q2 ∷
   re 67 5 (CX30 ∷ []) ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q3 ∷
   re 71 3 (CS13⁻ ∷ []) ∷
   rw 70 q4 ∷
   rw 69 q5 ∷
   rw 68 q1 ∷
   re 68 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 67 q2 ∷
   re 68 5 (CX30 ∷ []) ∷
   rw 42 q11 ∷
   rw 126 q12 ∷
   re 128 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 127 q3 ∷
   re 128 3 (CS03 ∷ []) ∷
   re 128 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 134 q3 ∷
   re 132 3 (CX31 ∷ []) ∷
   rw 131 q13 ∷
   rw 130 q14 ∷
   rw 129 q15 ∷
   re 129 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 128 q2 ∷
   re 129 5 (CS03 ∷ []) ∷
   re 129 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 131 q2 ∷
   re 127 3 (CX31 ∷ []) ∷
   rw 128 q12 ∷
   rw 125 q12 ∷
   re 127 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 126 q3 ∷
   re 127 3 (CS03 ∷ []) ∷
   re 127 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 133 q3 ∷
   re 131 3 (CX31 ∷ []) ∷
   rw 130 q13 ∷
   rw 129 q14 ∷
   rw 128 q15 ∷
   re 128 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 127 q2 ∷
   re 128 5 (CS03 ∷ []) ∷
   re 128 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 130 q2 ∷
   re 126 3 (CX31 ∷ []) ∷
   rw 127 q12 ∷
   rw 124 q12 ∷
   re 126 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 125 q3 ∷
   re 126 3 (CS03 ∷ []) ∷
   re 126 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 132 q3 ∷
   re 130 3 (CX31 ∷ []) ∷
   rw 129 q13 ∷
   rw 128 q14 ∷
   rw 127 q15 ∷
   re 127 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 126 q2 ∷
   re 127 5 (CS03 ∷ []) ∷
   re 127 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 129 q2 ∷
   re 125 3 (CX31 ∷ []) ∷
   rw 126 q12 ∷
   rw 123 q12 ∷
   re 125 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 124 q3 ∷
   re 125 3 (CS03 ∷ []) ∷
   re 125 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 131 q3 ∷
   re 129 3 (CX31 ∷ []) ∷
   rw 128 q13 ∷
   rw 127 q14 ∷
   rw 126 q15 ∷
   re 126 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 125 q2 ∷
   re 126 5 (CS03 ∷ []) ∷
   re 126 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 128 q2 ∷
   re 124 3 (CX31 ∷ []) ∷
   rw 125 q12 ∷
   rw 122 q12 ∷
   re 124 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 123 q3 ∷
   re 124 3 (CS03 ∷ []) ∷
   re 124 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 130 q3 ∷
   re 128 3 (CX31 ∷ []) ∷
   rw 127 q13 ∷
   rw 126 q14 ∷
   rw 125 q15 ∷
   re 125 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 124 q2 ∷
   re 125 5 (CS03 ∷ []) ∷
   re 125 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 127 q2 ∷
   re 123 3 (CX31 ∷ []) ∷
   rw 124 q12 ∷
   rw 121 q12 ∷
   re 123 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 122 q3 ∷
   re 123 3 (CS03 ∷ []) ∷
   re 123 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 129 q3 ∷
   re 127 3 (CX31 ∷ []) ∷
   rw 126 q13 ∷
   rw 125 q14 ∷
   rw 124 q15 ∷
   re 124 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 123 q2 ∷
   re 124 5 (CS03 ∷ []) ∷
   re 124 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 126 q2 ∷
   re 122 3 (CX31 ∷ []) ∷
   rw 123 q12 ∷
   rw 120 q16 ∷
   rw 121 q17 ∷
   rw 122 q16 ∷
   rw 119 q18 ∷
   re 121 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 120 q3 ∷
   re 121 3 (CK03 ∷ []) ∷
   re 121 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 127 q3 ∷
   re 125 3 (CX31 ∷ []) ∷
   rw 124 q13 ∷
   rw 123 q19 ∷
   rw 122 q15 ∷
   re 122 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 121 q2 ∷
   re 122 5 (CK03 ∷ []) ∷
   re 122 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 124 q2 ∷
   re 120 3 (CX31 ∷ []) ∷
   rw 121 q18 ∷
   rw 118 q12 ∷
   re 120 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 119 q3 ∷
   re 120 3 (CS03 ∷ []) ∷
   re 120 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 126 q3 ∷
   re 124 3 (CX31 ∷ []) ∷
   rw 123 q13 ∷
   rw 122 q14 ∷
   rw 121 q15 ∷
   re 121 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 120 q2 ∷
   re 121 5 (CS03 ∷ []) ∷
   re 121 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 123 q2 ∷
   re 119 3 (CX31 ∷ []) ∷
   rw 120 q12 ∷
   rw 117 q12 ∷
   re 119 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 118 q3 ∷
   re 119 3 (CS03 ∷ []) ∷
   re 119 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 125 q3 ∷
   re 123 3 (CX31 ∷ []) ∷
   rw 122 q13 ∷
   rw 121 q14 ∷
   rw 120 q15 ∷
   re 120 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 119 q2 ∷
   re 120 5 (CS03 ∷ []) ∷
   re 120 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 122 q2 ∷
   re 118 3 (CX31 ∷ []) ∷
   rw 119 q12 ∷
   rw 116 q12 ∷
   re 118 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 117 q3 ∷
   re 118 3 (CS03 ∷ []) ∷
   re 118 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 124 q3 ∷
   re 122 3 (CX31 ∷ []) ∷
   rw 121 q13 ∷
   rw 120 q14 ∷
   rw 119 q15 ∷
   re 119 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 118 q2 ∷
   re 119 5 (CS03 ∷ []) ∷
   re 119 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 121 q2 ∷
   re 117 3 (CX31 ∷ []) ∷
   rw 118 q12 ∷
   rw 115 q16 ∷
   rw 116 q17 ∷
   rw 117 q16 ∷
   rw 114 q18 ∷
   re 116 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 115 q3 ∷
   re 116 3 (CK03 ∷ []) ∷
   re 116 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 122 q3 ∷
   re 120 3 (CX31 ∷ []) ∷
   rw 119 q13 ∷
   rw 118 q19 ∷
   rw 117 q15 ∷
   re 117 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 116 q2 ∷
   re 117 5 (CK03 ∷ []) ∷
   re 117 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 119 q2 ∷
   re 115 3 (CX31 ∷ []) ∷
   rw 116 q18 ∷
   rw 113 q16 ∷
   rw 114 q17 ∷
   rw 115 q16 ∷
   rw 112 q18 ∷
   re 114 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 113 q3 ∷
   re 114 3 (CK03 ∷ []) ∷
   re 114 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 120 q3 ∷
   re 118 3 (CX31 ∷ []) ∷
   rw 117 q13 ∷
   rw 116 q19 ∷
   rw 115 q15 ∷
   re 115 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 114 q2 ∷
   re 115 5 (CK03 ∷ []) ∷
   re 115 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 117 q2 ∷
   re 113 3 (CX31 ∷ []) ∷
   rw 114 q18 ∷
   rw 115 q3 ∷
   rw 114 q20 ∷
   re 113 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 115 q2 ∷
   rw 112 q20 ∷
   re 111 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 113 q2 ∷
   rw 112 q21 ∷
   rw 111 q22 ∷
   rw 114 q3 ∷
   re 112 3 (CX31 ∷ []) ∷
   rw 113 q22 ∷
   rw 116 q3 ∷
   re 114 3 (CX30 ∷ []) ∷
   rw 115 q2 ∷
   rw 110 q16 ∷
   rw 111 q17 ∷
   rw 112 q16 ∷
   rw 109 q18 ∷
   re 111 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 110 q3 ∷
   re 111 3 (CK03 ∷ []) ∷
   re 111 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 117 q3 ∷
   re 115 3 (CX31 ∷ []) ∷
   rw 114 q13 ∷
   rw 113 q19 ∷
   rw 112 q15 ∷
   re 112 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 111 q2 ∷
   re 112 5 (CK03 ∷ []) ∷
   re 112 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 114 q2 ∷
   re 110 3 (CX31 ∷ []) ∷
   rw 111 q18 ∷
   rw 108 q16 ∷
   rw 109 q17 ∷
   rw 110 q16 ∷
   rw 107 q16 ∷
   rw 108 q17 ∷
   rw 109 q16 ∷
   rw 106 q16 ∷
   rw 107 q17 ∷
   rw 108 q16 ∷
   rw 105 q16 ∷
   rw 106 q17 ∷
   rw 107 q16 ∷
   rw 104 q18 ∷
   re 106 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 105 q3 ∷
   re 106 3 (CK03 ∷ []) ∷
   re 106 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 112 q3 ∷
   re 110 3 (CX31 ∷ []) ∷
   rw 109 q13 ∷
   rw 108 q19 ∷
   rw 107 q15 ∷
   re 107 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 106 q2 ∷
   re 107 5 (CK03 ∷ []) ∷
   re 107 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 109 q2 ∷
   re 105 3 (CX31 ∷ []) ∷
   rw 106 q18 ∷
   rw 103 q16 ∷
   rw 104 q17 ∷
   rw 105 q16 ∷
   rw 102 q16 ∷
   rw 103 q17 ∷
   rw 104 q16 ∷
   rw 101 q16 ∷
   rw 102 q17 ∷
   rw 103 q16 ∷
   rw 100 q12 ∷
   re 102 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 101 q3 ∷
   re 102 3 (CS03 ∷ []) ∷
   re 102 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 108 q3 ∷
   re 106 3 (CX31 ∷ []) ∷
   rw 105 q13 ∷
   rw 104 q14 ∷
   rw 103 q15 ∷
   re 103 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 102 q2 ∷
   re 103 5 (CS03 ∷ []) ∷
   re 103 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 105 q2 ∷
   re 101 3 (CX31 ∷ []) ∷
   rw 102 q12 ∷
   rw 99 q12 ∷
   re 101 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 100 q3 ∷
   re 101 3 (CS03 ∷ []) ∷
   re 101 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 107 q3 ∷
   re 105 3 (CX31 ∷ []) ∷
   rw 104 q13 ∷
   rw 103 q14 ∷
   rw 102 q15 ∷
   re 102 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 101 q2 ∷
   re 102 5 (CS03 ∷ []) ∷
   re 102 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 104 q2 ∷
   re 100 3 (CX31 ∷ []) ∷
   rw 101 q12 ∷
   rw 98 q12 ∷
   re 100 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 99 q3 ∷
   re 100 3 (CS03 ∷ []) ∷
   re 100 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 106 q3 ∷
   re 104 3 (CX31 ∷ []) ∷
   rw 103 q13 ∷
   rw 102 q14 ∷
   rw 101 q15 ∷
   re 101 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 100 q2 ∷
   re 101 5 (CS03 ∷ []) ∷
   re 101 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 103 q2 ∷
   re 99 3 (CX31 ∷ []) ∷
   rw 100 q12 ∷
   rw 97 q12 ∷
   re 99 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 98 q3 ∷
   re 99 3 (CS03 ∷ []) ∷
   re 99 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 105 q3 ∷
   re 103 3 (CX31 ∷ []) ∷
   rw 102 q13 ∷
   rw 101 q14 ∷
   rw 100 q15 ∷
   re 100 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 99 q2 ∷
   re 100 5 (CS03 ∷ []) ∷
   re 100 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 102 q2 ∷
   re 98 3 (CX31 ∷ []) ∷
   rw 99 q12 ∷
   rw 96 q12 ∷
   re 98 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 97 q3 ∷
   re 98 3 (CS03 ∷ []) ∷
   re 98 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 104 q3 ∷
   re 102 3 (CX31 ∷ []) ∷
   rw 101 q13 ∷
   rw 100 q14 ∷
   rw 99 q15 ∷
   re 99 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 98 q2 ∷
   re 99 5 (CS03 ∷ []) ∷
   re 99 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 101 q2 ∷
   re 97 3 (CX31 ∷ []) ∷
   rw 98 q12 ∷
   rw 95 q12 ∷
   re 97 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 96 q3 ∷
   re 97 3 (CS03 ∷ []) ∷
   re 97 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 103 q3 ∷
   re 101 3 (CX31 ∷ []) ∷
   rw 100 q13 ∷
   rw 99 q14 ∷
   rw 98 q15 ∷
   re 98 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 97 q2 ∷
   re 98 5 (CS03 ∷ []) ∷
   re 98 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 100 q2 ∷
   re 96 3 (CX31 ∷ []) ∷
   rw 97 q12 ∷
   rw 94 q12 ∷
   re 96 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 95 q3 ∷
   re 96 3 (CS03 ∷ []) ∷
   re 96 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 102 q3 ∷
   re 100 3 (CX31 ∷ []) ∷
   rw 99 q13 ∷
   rw 98 q14 ∷
   rw 97 q15 ∷
   re 97 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 96 q2 ∷
   re 97 5 (CS03 ∷ []) ∷
   re 97 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 99 q2 ∷
   re 95 3 (CX31 ∷ []) ∷
   rw 96 q12 ∷
   rw 93 q12 ∷
   re 95 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 94 q3 ∷
   re 95 3 (CS03 ∷ []) ∷
   re 95 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 101 q3 ∷
   re 99 3 (CX31 ∷ []) ∷
   rw 98 q13 ∷
   rw 97 q14 ∷
   rw 96 q15 ∷
   re 96 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 95 q2 ∷
   re 96 5 (CS03 ∷ []) ∷
   re 96 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 98 q2 ∷
   re 94 3 (CX31 ∷ []) ∷
   rw 95 q12 ∷
   rw 92 q12 ∷
   re 94 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 93 q3 ∷
   re 94 3 (CS03 ∷ []) ∷
   re 94 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 100 q3 ∷
   re 98 3 (CX31 ∷ []) ∷
   rw 97 q13 ∷
   rw 96 q14 ∷
   rw 95 q15 ∷ []) Eq.refl

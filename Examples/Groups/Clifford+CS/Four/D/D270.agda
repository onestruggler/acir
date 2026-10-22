{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D270 (W : Ws) where

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
  q1 = wE 3 W
  q2 : Eqn
  q2 = eqn (CS02 ∷ X3 ∷ []) (X3 ∷ CS02 ∷ []) (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 113 W
  q5 : Eqn
  q5 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q6 : Eqn
  q6 = wE 114 W
  q7 : Eqn
  q7 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q8 : Eqn
  q8 = eqn (S0 ∷ CX31 ∷ []) (CX31 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑ • CX₁₀ • Swap ↑)))
  q9 : Eqn
  q9 = eqn (CK02 ∷ X3 ∷ []) (X3 ∷ CK02 ∷ []) (low₃-comm ((Swap ↑ • CK₀₁ • Swap ↑)) (X))
  q10 : Eqn
  q10 = eqn (CK01 ∷ CX32 ∷ []) (CX32 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₁₀))
  q11 : Eqn
  q11 = wE 173 W
  q12 : Eqn
  q12 = wE 779 W
  q13 : Eqn
  q13 = wE 175 W

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];3,0->2) passes white iX via V2 conjugates 1 part2: 500 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part2 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ X3 ∷ Sw23 ∷ CX21 ∷ CS03 ∷ Sw23 ∷ X3 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part2 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ X3 ∷ Sw23 ∷ CX21 ∷ CS03 ∷ Sw23 ∷ X3 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ [])
  (re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q1 ∷
   re 73 3 (CX31 ∷ []) ∷
   rw 74 q2 ∷
   rw 71 q2 ∷
   re 73 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 72 q3 ∷
   re 73 3 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 79 q3 ∷
   re 77 3 (CX31 ∷ []) ∷
   rw 76 q4 ∷
   rw 75 q5 ∷
   rw 74 q6 ∷
   re 74 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 73 q1 ∷
   re 74 5 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q1 ∷
   re 72 3 (CX31 ∷ []) ∷
   rw 73 q2 ∷
   rw 70 q2 ∷
   re 72 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 71 q3 ∷
   re 72 3 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 78 q3 ∷
   re 76 3 (CX31 ∷ []) ∷
   rw 75 q4 ∷
   rw 74 q5 ∷
   rw 73 q6 ∷
   re 73 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 72 q1 ∷
   re 73 5 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q1 ∷
   re 71 3 (CX31 ∷ []) ∷
   rw 72 q2 ∷
   rw 69 q7 ∷
   rw 70 q8 ∷
   rw 71 q7 ∷
   rw 68 q9 ∷
   re 70 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 69 q3 ∷
   re 70 3 (CK03 ∷ []) ∷
   re 70 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 76 q3 ∷
   re 74 3 (CX31 ∷ []) ∷
   rw 73 q4 ∷
   rw 72 q10 ∷
   rw 71 q6 ∷
   re 71 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 70 q1 ∷
   re 71 5 (CK03 ∷ []) ∷
   re 71 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 73 q1 ∷
   re 69 3 (CX31 ∷ []) ∷
   rw 70 q9 ∷
   rw 67 q7 ∷
   rw 68 q8 ∷
   rw 69 q7 ∷
   rw 66 q9 ∷
   re 68 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 67 q3 ∷
   re 68 3 (CK03 ∷ []) ∷
   re 68 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 74 q3 ∷
   re 72 3 (CX31 ∷ []) ∷
   rw 71 q4 ∷
   rw 70 q10 ∷
   rw 69 q6 ∷
   re 69 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 68 q1 ∷
   re 69 5 (CK03 ∷ []) ∷
   re 69 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 71 q1 ∷
   re 67 3 (CX31 ∷ []) ∷
   rw 68 q9 ∷
   rw 69 q3 ∷
   rw 68 q11 ∷
   re 67 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 69 q1 ∷
   rw 66 q11 ∷
   re 65 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 67 q1 ∷
   rw 66 q12 ∷
   rw 65 q13 ∷
   rw 68 q3 ∷
   re 66 3 (CX31 ∷ []) ∷
   rw 67 q13 ∷
   rw 70 q3 ∷
   re 68 3 (CX30 ∷ []) ∷
   rw 69 q1 ∷
   rw 64 q7 ∷
   rw 65 q8 ∷
   rw 66 q7 ∷
   rw 63 q9 ∷
   re 65 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 64 q3 ∷
   re 65 3 (CK03 ∷ []) ∷
   re 65 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q3 ∷
   re 69 3 (CX31 ∷ []) ∷
   rw 68 q4 ∷
   rw 67 q10 ∷
   rw 66 q6 ∷
   re 66 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 65 q1 ∷
   re 66 5 (CK03 ∷ []) ∷
   re 66 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 68 q1 ∷
   re 64 3 (CX31 ∷ []) ∷
   rw 65 q9 ∷
   rw 62 q7 ∷
   rw 63 q8 ∷
   rw 64 q7 ∷
   rw 61 q7 ∷
   rw 62 q8 ∷
   rw 63 q7 ∷
   rw 60 q7 ∷
   rw 61 q8 ∷
   rw 62 q7 ∷
   rw 59 q7 ∷
   rw 60 q8 ∷
   rw 61 q7 ∷
   rw 58 q9 ∷
   re 60 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 59 q3 ∷
   re 60 3 (CK03 ∷ []) ∷
   re 60 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 66 q3 ∷
   re 64 3 (CX31 ∷ []) ∷
   rw 63 q4 ∷
   rw 62 q10 ∷
   rw 61 q6 ∷
   re 61 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 60 q1 ∷
   re 61 5 (CK03 ∷ []) ∷
   re 61 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 63 q1 ∷
   re 59 3 (CX31 ∷ []) ∷
   rw 60 q9 ∷
   rw 57 q7 ∷
   rw 58 q8 ∷
   rw 59 q7 ∷
   rw 56 q7 ∷
   rw 57 q8 ∷
   rw 58 q7 ∷
   rw 55 q7 ∷
   rw 56 q8 ∷
   rw 57 q7 ∷
   rw 54 q2 ∷
   re 56 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 55 q3 ∷
   re 56 3 (CS03 ∷ []) ∷
   re 56 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 62 q3 ∷
   re 60 3 (CX31 ∷ []) ∷
   rw 59 q4 ∷
   rw 58 q5 ∷
   rw 57 q6 ∷
   re 57 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 56 q1 ∷
   re 57 5 (CS03 ∷ []) ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q1 ∷
   re 55 3 (CX31 ∷ []) ∷
   rw 56 q2 ∷
   rw 53 q2 ∷
   re 55 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 54 q3 ∷
   re 55 3 (CS03 ∷ []) ∷
   re 55 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 61 q3 ∷
   re 59 3 (CX31 ∷ []) ∷
   rw 58 q4 ∷
   rw 57 q5 ∷
   rw 56 q6 ∷
   re 56 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 55 q1 ∷
   re 56 5 (CS03 ∷ []) ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 58 q1 ∷
   re 54 3 (CX31 ∷ []) ∷
   rw 55 q2 ∷
   rw 52 q2 ∷
   re 54 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 53 q3 ∷
   re 54 3 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 60 q3 ∷
   re 58 3 (CX31 ∷ []) ∷
   rw 57 q4 ∷
   rw 56 q5 ∷
   rw 55 q6 ∷
   re 55 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 54 q1 ∷
   re 55 5 (CS03 ∷ []) ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q1 ∷
   re 53 3 (CX31 ∷ []) ∷
   rw 54 q2 ∷
   rw 51 q2 ∷
   re 53 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 52 q3 ∷
   re 53 3 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q3 ∷
   re 57 3 (CX31 ∷ []) ∷
   rw 56 q4 ∷
   rw 55 q5 ∷
   rw 54 q6 ∷
   re 54 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 53 q1 ∷
   re 54 5 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q1 ∷
   re 52 3 (CX31 ∷ []) ∷
   rw 53 q2 ∷
   rw 50 q2 ∷
   re 52 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 51 q3 ∷
   re 52 3 (CS03 ∷ []) ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q3 ∷
   re 56 3 (CX31 ∷ []) ∷
   rw 55 q4 ∷
   rw 54 q5 ∷
   rw 53 q6 ∷
   re 53 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 52 q1 ∷
   re 53 5 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 55 q1 ∷
   re 51 3 (CX31 ∷ []) ∷
   rw 52 q2 ∷
   rw 49 q2 ∷
   re 51 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 50 q3 ∷
   re 51 3 (CS03 ∷ []) ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 57 q3 ∷
   re 55 3 (CX31 ∷ []) ∷
   rw 54 q4 ∷
   rw 53 q5 ∷
   rw 52 q6 ∷
   re 52 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 51 q1 ∷
   re 52 5 (CS03 ∷ []) ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 54 q1 ∷
   re 50 3 (CX31 ∷ []) ∷
   rw 51 q2 ∷
   rw 48 q2 ∷
   re 50 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 49 q3 ∷
   re 50 3 (CS03 ∷ []) ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q3 ∷
   re 54 3 (CX31 ∷ []) ∷
   rw 53 q4 ∷
   rw 52 q5 ∷
   rw 51 q6 ∷
   re 51 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 50 q1 ∷
   re 51 5 (CS03 ∷ []) ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q1 ∷
   re 49 3 (CX31 ∷ []) ∷
   rw 50 q2 ∷
   rw 47 q2 ∷
   re 49 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 48 q3 ∷
   re 49 3 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q3 ∷
   re 53 3 (CX31 ∷ []) ∷
   rw 52 q4 ∷
   rw 51 q5 ∷
   rw 50 q6 ∷
   re 50 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   re 50 5 (CS03 ∷ []) ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q1 ∷
   re 48 3 (CX31 ∷ []) ∷
   rw 49 q2 ∷
   rw 46 q2 ∷
   re 48 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 47 q3 ∷
   re 48 3 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q3 ∷
   re 52 3 (CX31 ∷ []) ∷
   rw 51 q4 ∷
   rw 50 q5 ∷
   rw 49 q6 ∷
   re 49 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 48 q1 ∷
   re 49 5 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q1 ∷
   re 47 3 (CX31 ∷ []) ∷
   rw 48 q2 ∷
   rw 45 q7 ∷
   rw 46 q8 ∷
   rw 47 q7 ∷
   rw 44 q9 ∷
   re 46 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 45 q3 ∷
   re 46 3 (CK03 ∷ []) ∷
   re 46 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q3 ∷
   re 50 3 (CX31 ∷ []) ∷
   rw 49 q4 ∷
   rw 48 q10 ∷
   rw 47 q6 ∷
   re 47 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 46 q1 ∷
   re 47 5 (CK03 ∷ []) ∷
   re 47 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   re 45 3 (CX31 ∷ []) ∷
   rw 46 q9 ∷
   rw 43 q7 ∷
   rw 44 q8 ∷
   rw 45 q7 ∷
   rw 42 q7 ∷
   rw 43 q8 ∷
   rw 44 q7 ∷
   rw 41 q7 ∷
   rw 42 q8 ∷
   rw 43 q7 ∷
   rw 40 q2 ∷
   re 42 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 41 q3 ∷
   re 42 3 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q3 ∷
   re 46 3 (CX31 ∷ []) ∷
   rw 45 q4 ∷
   rw 44 q5 ∷
   rw 43 q6 ∷
   re 43 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   re 43 5 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q1 ∷
   re 41 3 (CX31 ∷ []) ∷
   rw 42 q2 ∷
   rw 39 q2 ∷
   re 41 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 40 q3 ∷
   re 41 3 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q3 ∷
   re 45 3 (CX31 ∷ []) ∷
   rw 44 q4 ∷
   rw 43 q5 ∷
   rw 42 q6 ∷
   re 42 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   re 42 5 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   re 40 3 (CX31 ∷ []) ∷
   rw 41 q2 ∷
   rw 38 q2 ∷
   re 40 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 39 q3 ∷
   re 40 3 (CS03 ∷ []) ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q3 ∷
   re 44 3 (CX31 ∷ []) ∷
   rw 43 q4 ∷
   rw 42 q5 ∷
   rw 41 q6 ∷
   re 41 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   re 41 5 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   re 39 3 (CX31 ∷ []) ∷
   rw 40 q2 ∷
   rw 37 q2 ∷
   re 39 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 38 q3 ∷
   re 39 3 (CS03 ∷ []) ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q3 ∷
   re 43 3 (CX31 ∷ []) ∷
   rw 42 q4 ∷
   rw 41 q5 ∷
   rw 40 q6 ∷
   re 40 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 39 q1 ∷
   re 40 5 (CS03 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   re 38 3 (CX31 ∷ []) ∷
   rw 39 q2 ∷
   rw 36 q2 ∷
   re 38 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 37 q3 ∷
   re 38 3 (CS03 ∷ []) ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q3 ∷
   re 42 3 (CX31 ∷ []) ∷
   rw 41 q4 ∷
   rw 40 q5 ∷
   rw 39 q6 ∷
   re 39 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 38 q1 ∷
   re 39 5 (CS03 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   re 37 3 (CX31 ∷ []) ∷
   rw 38 q2 ∷
   rw 35 q2 ∷
   re 37 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 36 q3 ∷
   re 37 3 (CS03 ∷ []) ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q3 ∷
   re 41 3 (CX31 ∷ []) ∷
   rw 40 q4 ∷
   rw 39 q5 ∷
   rw 38 q6 ∷
   re 38 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 37 q1 ∷
   re 38 5 (CS03 ∷ []) ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   re 36 3 (CX31 ∷ []) ∷
   rw 37 q2 ∷
   rw 34 q2 ∷
   re 36 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 35 q3 ∷
   re 36 3 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q3 ∷
   re 40 3 (CX31 ∷ []) ∷
   rw 39 q4 ∷
   rw 38 q5 ∷
   rw 37 q6 ∷
   re 37 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
   re 37 5 (CS03 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q1 ∷
   re 35 3 (CX31 ∷ []) ∷
   rw 36 q2 ∷
   rw 33 q2 ∷
   re 35 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 34 q3 ∷
   re 35 3 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q3 ∷
   re 39 3 (CX31 ∷ []) ∷
   rw 38 q4 ∷
   rw 37 q5 ∷
   rw 36 q6 ∷
   re 36 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   re 36 5 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q1 ∷
   re 34 3 (CX31 ∷ []) ∷
   rw 35 q2 ∷
   rw 32 q2 ∷
   re 34 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 33 q3 ∷
   re 34 3 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q3 ∷
   re 38 3 (CX31 ∷ []) ∷
   rw 37 q4 ∷
   rw 36 q5 ∷
   rw 35 q6 ∷
   re 35 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   re 35 5 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q1 ∷
   re 33 3 (CX31 ∷ []) ∷
   rw 34 q2 ∷
   rw 31 q2 ∷
   re 33 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 32 q3 ∷
   re 33 3 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q3 ∷
   re 37 3 (CX31 ∷ []) ∷
   rw 36 q4 ∷
   rw 35 q5 ∷
   rw 34 q6 ∷
   re 34 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 34 5 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷ []) Eq.refl

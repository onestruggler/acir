{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D271 (W : Ws) where

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
  q7 = wE 173 W
  q8 : Eqn
  q8 = wE 779 W
  q9 : Eqn
  q9 = wE 175 W
  q10 : Eqn
  q10 = wE 858 W
  q11 : Eqn
  q11 = wE 783 W
  q12 : Eqn
  q12 = wE 21 W
  q13 : Eqn
  q13 = eqn (CX10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((CS • CS • CS)))
  q14 : Eqn
  q14 = wE 51 W
  q15 : Eqn
  q15 = eqn (S1⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (Swap))
  q16 : Eqn
  q16 = wE 782 W
  q17 : Eqn
  q17 = wE 353 W
  q18 : Eqn
  q18 = eqn (CX10 ∷ CK23⁻ ∷ []) (CK23⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((S • CK₀₁)))
  q19 : Eqn
  q19 = wE 358 W
  q20 : Eqn
  q20 = wE 859 W
  q21 : Eqn
  q21 = wE 860 W
  q22 : Eqn
  q22 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q23 : Eqn
  q23 = eqn (S0 ∷ CX31 ∷ []) (CX31 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑ • CX₁₀ • Swap ↑)))
  q24 : Eqn
  q24 = eqn (CK02 ∷ X3 ∷ []) (X3 ∷ CK02 ∷ []) (low₃-comm ((Swap ↑ • CK₀₁ • Swap ↑)) (X))
  q25 : Eqn
  q25 = eqn (CK01 ∷ CX32 ∷ []) (CX32 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₁₀))

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];3,0->2) passes white iX via V2 conjugates 1 part3: 500 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part3 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ X3 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part3 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ X3 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ [])
  (rw 36 q1 ∷
   re 32 3 (CX31 ∷ []) ∷
   rw 33 q2 ∷
   rw 30 q2 ∷
   re 32 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 31 q3 ∷
   re 32 3 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q3 ∷
   re 36 3 (CX31 ∷ []) ∷
   rw 35 q4 ∷
   rw 34 q5 ∷
   rw 33 q6 ∷
   re 33 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 33 5 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   re 31 3 (CX31 ∷ []) ∷
   rw 32 q2 ∷
   rw 29 q2 ∷
   re 31 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 30 q3 ∷
   re 31 3 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q3 ∷
   re 35 3 (CX31 ∷ []) ∷
   rw 34 q4 ∷
   rw 33 q5 ∷
   rw 32 q6 ∷
   re 32 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   re 32 5 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   re 30 3 (CX31 ∷ []) ∷
   rw 31 q2 ∷
   rw 28 q2 ∷
   re 30 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 29 q3 ∷
   re 30 3 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q3 ∷
   re 34 3 (CX31 ∷ []) ∷
   rw 33 q4 ∷
   rw 32 q5 ∷
   rw 31 q6 ∷
   re 31 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   re 31 5 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 29 3 (CX31 ∷ []) ∷
   rw 30 q2 ∷
   rw 27 q2 ∷
   re 29 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 28 q3 ∷
   re 29 3 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q3 ∷
   re 33 3 (CX31 ∷ []) ∷
   rw 32 q4 ∷
   rw 31 q5 ∷
   rw 30 q6 ∷
   re 30 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   re 30 5 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 28 3 (CX31 ∷ []) ∷
   rw 29 q2 ∷
   rw 26 q2 ∷
   re 28 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 27 q3 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q3 ∷
   re 32 3 (CX31 ∷ []) ∷
   rw 31 q4 ∷
   rw 30 q5 ∷
   rw 29 q6 ∷
   re 29 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   re 27 3 (CX31 ∷ []) ∷
   rw 28 q2 ∷
   rw 25 q2 ∷
   re 27 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 26 q3 ∷
   re 27 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q3 ∷
   re 31 3 (CX31 ∷ []) ∷
   rw 30 q4 ∷
   rw 29 q5 ∷
   rw 28 q6 ∷
   re 28 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   re 28 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   re 26 3 (CX31 ∷ []) ∷
   rw 27 q2 ∷
   rw 24 q2 ∷
   re 26 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 25 q3 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q3 ∷
   re 30 3 (CX31 ∷ []) ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   rw 27 q6 ∷
   re 27 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   re 25 3 (CX31 ∷ []) ∷
   rw 26 q2 ∷
   rw 23 q2 ∷
   re 25 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 24 q3 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q3 ∷
   re 29 3 (CX31 ∷ []) ∷
   rw 28 q4 ∷
   rw 27 q5 ∷
   rw 26 q6 ∷
   re 26 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   re 24 3 (CX31 ∷ []) ∷
   rw 25 q2 ∷
   rw 26 q3 ∷
   rw 25 q7 ∷
   re 24 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   rw 23 q7 ∷
   re 22 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   rw 23 q8 ∷
   rw 22 q9 ∷
   rw 25 q3 ∷
   re 23 3 (CX31 ∷ []) ∷
   rw 24 q9 ∷
   rw 27 q3 ∷
   re 25 3 (CX30 ∷ []) ∷
   rw 26 q1 ∷
   rw 7 q10 ∷
   rw 69 q11 ∷
   re 68 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 74 q3 ∷
   re 72 3 (CS13⁻ ∷ []) ∷
   rw 71 q12 ∷
   rw 70 q13 ∷
   rw 69 q14 ∷
   re 69 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 68 q1 ∷
   re 69 5 (CX30 ∷ []) ∷
   re 69 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 75 q3 ∷
   re 73 3 (CS13⁻ ∷ []) ∷
   rw 72 q12 ∷
   rw 71 q13 ∷
   rw 70 q14 ∷
   re 70 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 69 q1 ∷
   re 70 5 (CX30 ∷ []) ∷
   re 70 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 76 q3 ∷
   re 74 3 (CS13⁻ ∷ []) ∷
   rw 73 q12 ∷
   rw 72 q13 ∷
   rw 71 q14 ∷
   re 71 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 70 q1 ∷
   re 71 5 (CX30 ∷ []) ∷
   re 71 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 77 q3 ∷
   re 75 3 (CS13⁻ ∷ []) ∷
   rw 74 q12 ∷
   rw 73 q13 ∷
   rw 72 q14 ∷
   re 72 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 71 q1 ∷
   re 72 5 (CX30 ∷ []) ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 78 q3 ∷
   re 76 3 (CS13⁻ ∷ []) ∷
   rw 75 q12 ∷
   rw 74 q13 ∷
   rw 73 q14 ∷
   re 73 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 72 q1 ∷
   re 73 5 (CX30 ∷ []) ∷
   re 73 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 79 q3 ∷
   re 77 3 (CS13⁻ ∷ []) ∷
   rw 76 q12 ∷
   rw 75 q13 ∷
   rw 74 q14 ∷
   re 74 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 73 q1 ∷
   re 74 5 (CX30 ∷ []) ∷
   rw 76 q3 ∷
   rw 75 q15 ∷
   re 74 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 76 q1 ∷
   rw 75 q16 ∷
   rw⁻ 74 q15 ∷
   rw 77 q3 ∷
   re 75 3 (CX30 ∷ []) ∷
   rw 76 q1 ∷
   re 75 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 81 q3 ∷
   re 79 3 (CK13⁻ ∷ []) ∷
   rw 78 q17 ∷
   rw 77 q18 ∷
   rw 76 q19 ∷
   re 76 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 75 q1 ∷
   re 76 5 (CX30 ∷ []) ∷
   re 76 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 82 q3 ∷
   re 80 3 (CS13⁻ ∷ []) ∷
   rw 79 q12 ∷
   rw 78 q13 ∷
   rw 77 q14 ∷
   re 77 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 76 q1 ∷
   re 77 5 (CX30 ∷ []) ∷
   re 77 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 83 q3 ∷
   re 81 3 (CS13⁻ ∷ []) ∷
   rw 80 q12 ∷
   rw 79 q13 ∷
   rw 78 q14 ∷
   re 78 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 77 q1 ∷
   re 78 5 (CX30 ∷ []) ∷
   re 78 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 84 q3 ∷
   re 82 3 (CS13⁻ ∷ []) ∷
   rw 81 q12 ∷
   rw 80 q13 ∷
   rw 79 q14 ∷
   re 79 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 78 q1 ∷
   re 79 5 (CX30 ∷ []) ∷
   rw 26 q20 ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q3 ∷
   re 29 3 (CS13⁻ ∷ []) ∷
   rw 28 q12 ∷
   rw 27 q13 ∷
   rw 26 q14 ∷
   re 26 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 26 5 (CX30 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q3 ∷
   re 30 3 (CS13⁻ ∷ []) ∷
   rw 29 q12 ∷
   rw 28 q13 ∷
   rw 27 q14 ∷
   re 27 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   re 27 5 (CX30 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q3 ∷
   re 31 3 (CS13⁻ ∷ []) ∷
   rw 30 q12 ∷
   rw 29 q13 ∷
   rw 28 q14 ∷
   re 28 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   re 28 5 (CX30 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q3 ∷
   re 32 3 (CS13⁻ ∷ []) ∷
   rw 31 q12 ∷
   rw 30 q13 ∷
   rw 29 q14 ∷
   re 29 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   re 29 5 (CX30 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q3 ∷
   re 33 3 (CS13⁻ ∷ []) ∷
   rw 32 q12 ∷
   rw 31 q13 ∷
   rw 30 q14 ∷
   re 30 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   re 30 5 (CX30 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q3 ∷
   re 34 3 (CS13⁻ ∷ []) ∷
   rw 33 q12 ∷
   rw 32 q13 ∷
   rw 31 q14 ∷
   re 31 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   re 31 5 (CX30 ∷ []) ∷
   rw 33 q3 ∷
   rw 32 q15 ∷
   re 31 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   rw 32 q16 ∷
   rw⁻ 31 q15 ∷
   rw 34 q3 ∷
   re 32 3 (CX30 ∷ []) ∷
   rw 33 q1 ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q3 ∷
   re 36 3 (CK13⁻ ∷ []) ∷
   rw 35 q17 ∷
   rw 34 q18 ∷
   rw 33 q19 ∷
   re 33 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 33 5 (CX30 ∷ []) ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q3 ∷
   re 37 3 (CS13⁻ ∷ []) ∷
   rw 36 q12 ∷
   rw 35 q13 ∷
   rw 34 q14 ∷
   re 34 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 34 5 (CX30 ∷ []) ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q3 ∷
   re 38 3 (CS13⁻ ∷ []) ∷
   rw 37 q12 ∷
   rw 36 q13 ∷
   rw 35 q14 ∷
   re 35 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   re 35 5 (CX30 ∷ []) ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q3 ∷
   re 39 3 (CS13⁻ ∷ []) ∷
   rw 38 q12 ∷
   rw 37 q13 ∷
   rw 36 q14 ∷
   re 36 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   re 36 5 (CX30 ∷ []) ∷
   rw 10 q21 ∷
   rw 94 q2 ∷
   re 96 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 95 q3 ∷
   re 96 3 (CS03 ∷ []) ∷
   re 96 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 102 q3 ∷
   re 100 3 (CX31 ∷ []) ∷
   rw 99 q4 ∷
   rw 98 q5 ∷
   rw 97 q6 ∷
   re 97 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 96 q1 ∷
   re 97 5 (CS03 ∷ []) ∷
   re 97 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 99 q1 ∷
   re 95 3 (CX31 ∷ []) ∷
   rw 96 q2 ∷
   rw 93 q2 ∷
   re 95 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 94 q3 ∷
   re 95 3 (CS03 ∷ []) ∷
   re 95 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 101 q3 ∷
   re 99 3 (CX31 ∷ []) ∷
   rw 98 q4 ∷
   rw 97 q5 ∷
   rw 96 q6 ∷
   re 96 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 95 q1 ∷
   re 96 5 (CS03 ∷ []) ∷
   re 96 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 98 q1 ∷
   re 94 3 (CX31 ∷ []) ∷
   rw 95 q2 ∷
   rw 92 q2 ∷
   re 94 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 93 q3 ∷
   re 94 3 (CS03 ∷ []) ∷
   re 94 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 100 q3 ∷
   re 98 3 (CX31 ∷ []) ∷
   rw 97 q4 ∷
   rw 96 q5 ∷
   rw 95 q6 ∷
   re 95 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 94 q1 ∷
   re 95 5 (CS03 ∷ []) ∷
   re 95 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 97 q1 ∷
   re 93 3 (CX31 ∷ []) ∷
   rw 94 q2 ∷
   rw 91 q2 ∷
   re 93 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 92 q3 ∷
   re 93 3 (CS03 ∷ []) ∷
   re 93 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 99 q3 ∷
   re 97 3 (CX31 ∷ []) ∷
   rw 96 q4 ∷
   rw 95 q5 ∷
   rw 94 q6 ∷
   re 94 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 93 q1 ∷
   re 94 5 (CS03 ∷ []) ∷
   re 94 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 96 q1 ∷
   re 92 3 (CX31 ∷ []) ∷
   rw 93 q2 ∷
   rw 90 q2 ∷
   re 92 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 91 q3 ∷
   re 92 3 (CS03 ∷ []) ∷
   re 92 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 98 q3 ∷
   re 96 3 (CX31 ∷ []) ∷
   rw 95 q4 ∷
   rw 94 q5 ∷
   rw 93 q6 ∷
   re 93 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 92 q1 ∷
   re 93 5 (CS03 ∷ []) ∷
   re 93 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 95 q1 ∷
   re 91 3 (CX31 ∷ []) ∷
   rw 92 q2 ∷
   rw 89 q2 ∷
   re 91 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 90 q3 ∷
   re 91 3 (CS03 ∷ []) ∷
   re 91 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 97 q3 ∷
   re 95 3 (CX31 ∷ []) ∷
   rw 94 q4 ∷
   rw 93 q5 ∷
   rw 92 q6 ∷
   re 92 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 91 q1 ∷
   re 92 5 (CS03 ∷ []) ∷
   re 92 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 94 q1 ∷
   re 90 3 (CX31 ∷ []) ∷
   rw 91 q2 ∷
   rw 88 q22 ∷
   rw 89 q23 ∷
   rw 90 q22 ∷
   rw 87 q24 ∷
   re 89 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 88 q3 ∷
   re 89 3 (CK03 ∷ []) ∷
   re 89 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 95 q3 ∷
   re 93 3 (CX31 ∷ []) ∷
   rw 92 q4 ∷
   rw 91 q25 ∷
   rw 90 q6 ∷
   re 90 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 89 q1 ∷
   re 90 5 (CK03 ∷ []) ∷
   re 90 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 92 q1 ∷
   re 88 3 (CX31 ∷ []) ∷
   rw 89 q24 ∷
   rw 86 q2 ∷
   re 88 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 87 q3 ∷
   re 88 3 (CS03 ∷ []) ∷
   re 88 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 94 q3 ∷
   re 92 3 (CX31 ∷ []) ∷
   rw 91 q4 ∷
   rw 90 q5 ∷
   rw 89 q6 ∷
   re 89 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 88 q1 ∷
   re 89 5 (CS03 ∷ []) ∷
   re 89 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 91 q1 ∷
   re 87 3 (CX31 ∷ []) ∷
   rw 88 q2 ∷
   rw 85 q2 ∷
   re 87 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 86 q3 ∷
   re 87 3 (CS03 ∷ []) ∷
   re 87 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷ []) Eq.refl

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D269 (W : Ws) where

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
  q1 = eqn (CS02 ∷ X3 ∷ []) (X3 ∷ CS02 ∷ []) (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 21 W
  q4 : Eqn
  q4 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q5 : Eqn
  q5 = wE 51 W
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 173 W
  q8 : Eqn
  q8 = wE 774 W
  q9 : Eqn
  q9 = wE 175 W
  q10 : Eqn
  q10 = wE 855 W
  q11 : Eqn
  q11 = wE 777 W
  q12 : Eqn
  q12 = eqn (CX10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((CS • CS • CS)))
  q13 : Eqn
  q13 = wE 353 W
  q14 : Eqn
  q14 = eqn (CX10 ∷ CK23⁻ ∷ []) (CK23⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((S • CK₀₁)))
  q15 : Eqn
  q15 = wE 358 W
  q16 : Eqn
  q16 = wE 856 W
  q17 : Eqn
  q17 = wE 857 W
  q18 : Eqn
  q18 = wE 113 W
  q19 : Eqn
  q19 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q20 : Eqn
  q20 = wE 114 W
  q21 : Eqn
  q21 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q22 : Eqn
  q22 = eqn (S0 ∷ CX31 ∷ []) (CX31 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑ • CX₁₀ • Swap ↑)))
  q23 : Eqn
  q23 = eqn (CK02 ∷ X3 ∷ []) (X3 ∷ CK02 ∷ []) (low₃-comm ((Swap ↑ • CK₀₁ • Swap ↑)) (X))
  q24 : Eqn
  q24 = eqn (CK01 ∷ CX32 ∷ []) (CX32 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₁₀))

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];3,0->2) passes white iX via V2 conjugates 1 part1: 500 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part1 : ⟪ (CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CS02 ∷ X3 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ X3 ∷ Sw23 ∷ CX21 ∷ CS03 ∷ Sw23 ∷ X3 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part1 = derive (CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CS02 ∷ X3 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ X3 ∷ Sw23 ∷ CX21 ∷ CS03 ∷ Sw23 ∷ X3 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ [])
  (re 33 3 (CS13⁻ ∷ []) ∷
   rw 34 q1 ∷
   rw 31 q1 ∷
   re 33 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 32 q2 ∷
   re 33 3 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q2 ∷
   re 37 3 (CS13⁻ ∷ []) ∷
   rw 36 q3 ∷
   rw 35 q4 ∷
   rw 34 q5 ∷
   re 34 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 33 q6 ∷
   re 34 5 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q6 ∷
   re 32 3 (CS13⁻ ∷ []) ∷
   rw 33 q1 ∷
   rw 30 q1 ∷
   re 32 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 31 q2 ∷
   re 32 3 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q2 ∷
   re 36 3 (CS13⁻ ∷ []) ∷
   rw 35 q3 ∷
   rw 34 q4 ∷
   rw 33 q5 ∷
   re 33 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 32 q6 ∷
   re 33 5 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q6 ∷
   re 31 3 (CS13⁻ ∷ []) ∷
   rw 32 q1 ∷
   rw 29 q1 ∷
   re 31 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 30 q2 ∷
   re 31 3 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q2 ∷
   re 35 3 (CS13⁻ ∷ []) ∷
   rw 34 q3 ∷
   rw 33 q4 ∷
   rw 32 q5 ∷
   re 32 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 31 q6 ∷
   re 32 5 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q6 ∷
   re 30 3 (CS13⁻ ∷ []) ∷
   rw 31 q1 ∷
   rw 28 q1 ∷
   re 30 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   re 30 3 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   re 34 3 (CS13⁻ ∷ []) ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   rw 31 q5 ∷
   re 31 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 30 q6 ∷
   re 31 5 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q6 ∷
   re 29 3 (CS13⁻ ∷ []) ∷
   rw 30 q1 ∷
   rw 27 q1 ∷
   re 29 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   re 29 3 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   re 33 3 (CS13⁻ ∷ []) ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   rw 30 q5 ∷
   re 30 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 29 q6 ∷
   re 30 5 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q6 ∷
   re 28 3 (CS13⁻ ∷ []) ∷
   rw 29 q1 ∷
   rw 26 q1 ∷
   re 28 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   re 32 3 (CS13⁻ ∷ []) ∷
   rw 31 q3 ∷
   rw 30 q4 ∷
   rw 29 q5 ∷
   re 29 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 28 q6 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q6 ∷
   re 27 3 (CS13⁻ ∷ []) ∷
   rw 28 q1 ∷
   rw 25 q1 ∷
   re 27 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   re 27 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q2 ∷
   re 31 3 (CS13⁻ ∷ []) ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   re 28 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q6 ∷
   re 28 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q6 ∷
   re 26 3 (CS13⁻ ∷ []) ∷
   rw 27 q1 ∷
   rw 24 q1 ∷
   re 26 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q2 ∷
   re 30 3 (CS13⁻ ∷ []) ∷
   rw 29 q3 ∷
   rw 28 q4 ∷
   rw 27 q5 ∷
   re 27 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q6 ∷
   re 25 3 (CS13⁻ ∷ []) ∷
   rw 26 q1 ∷
   rw 23 q1 ∷
   re 25 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q2 ∷
   re 29 3 (CS13⁻ ∷ []) ∷
   rw 28 q3 ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   re 26 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q6 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q6 ∷
   re 24 3 (CS13⁻ ∷ []) ∷
   rw 25 q1 ∷
   rw 22 q1 ∷
   re 24 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 23 q2 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q2 ∷
   re 28 3 (CS13⁻ ∷ []) ∷
   rw 27 q3 ∷
   rw 26 q4 ∷
   rw 25 q5 ∷
   re 25 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q6 ∷
   re 23 3 (CS13⁻ ∷ []) ∷
   rw 24 q1 ∷
   rw 21 q1 ∷
   re 23 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   re 27 3 (CS13⁻ ∷ []) ∷
   rw 26 q3 ∷
   rw 25 q4 ∷
   rw 24 q5 ∷
   re 24 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 23 q6 ∷
   re 24 5 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   re 22 3 (CS13⁻ ∷ []) ∷
   rw 23 q1 ∷
   rw 20 q1 ∷
   re 22 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q2 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   re 26 3 (CS13⁻ ∷ []) ∷
   rw 25 q3 ∷
   rw 24 q4 ∷
   rw 23 q5 ∷
   re 23 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 22 q6 ∷
   re 23 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q6 ∷
   re 21 3 (CS13⁻ ∷ []) ∷
   rw 22 q1 ∷
   rw 19 q1 ∷
   re 21 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   re 25 3 (CS13⁻ ∷ []) ∷
   rw 24 q3 ∷
   rw 23 q4 ∷
   rw 22 q5 ∷
   re 22 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   re 20 3 (CS13⁻ ∷ []) ∷
   rw 21 q1 ∷
   rw 18 q1 ∷
   re 20 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   re 24 3 (CS13⁻ ∷ []) ∷
   rw 23 q3 ∷
   rw 22 q4 ∷
   rw 21 q5 ∷
   re 21 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q6 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q6 ∷
   re 19 3 (CS13⁻ ∷ []) ∷
   rw 20 q1 ∷
   rw 17 q1 ∷
   re 19 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q2 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   re 23 3 (CS13⁻ ∷ []) ∷
   rw 22 q3 ∷
   rw 21 q4 ∷
   rw 20 q5 ∷
   re 20 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q6 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q6 ∷
   re 18 3 (CS13⁻ ∷ []) ∷
   rw 19 q1 ∷
   rw 16 q1 ∷
   re 18 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   re 22 3 (CS13⁻ ∷ []) ∷
   rw 21 q3 ∷
   rw 20 q4 ∷
   rw 19 q5 ∷
   re 19 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q6 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw 18 q1 ∷
   rw 19 q2 ∷
   rw 18 q7 ∷
   re 17 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q6 ∷
   rw 16 q7 ∷
   re 15 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 17 q6 ∷
   rw 16 q8 ∷
   rw 15 q9 ∷
   rw 18 q2 ∷
   re 16 3 (CS13⁻ ∷ []) ∷
   rw 17 q9 ∷
   rw 20 q2 ∷
   re 18 3 (CX30 ∷ []) ∷
   rw 19 q6 ∷
   rw 0 q10 ∷
   rw 62 q11 ∷
   re 61 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 67 q2 ∷
   re 65 3 (CS13⁻ ∷ []) ∷
   rw 64 q3 ∷
   rw 63 q12 ∷
   rw 62 q5 ∷
   re 62 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 61 q6 ∷
   re 62 5 (CX30 ∷ []) ∷
   re 62 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 68 q2 ∷
   re 66 3 (CK13⁻ ∷ []) ∷
   rw 65 q13 ∷
   rw 64 q14 ∷
   rw 63 q15 ∷
   re 63 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 62 q6 ∷
   re 63 5 (CX30 ∷ []) ∷
   re 63 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 69 q2 ∷
   re 67 3 (CS13⁻ ∷ []) ∷
   rw 66 q3 ∷
   rw 65 q12 ∷
   rw 64 q5 ∷
   re 64 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 63 q6 ∷
   re 64 5 (CX30 ∷ []) ∷
   re 64 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 70 q2 ∷
   re 68 3 (CS13⁻ ∷ []) ∷
   rw 67 q3 ∷
   rw 66 q12 ∷
   rw 65 q5 ∷
   re 65 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 64 q6 ∷
   re 65 5 (CX30 ∷ []) ∷
   rw 19 q16 ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   re 22 3 (CS13⁻ ∷ []) ∷
   rw 21 q3 ∷
   rw 20 q12 ∷
   rw 19 q5 ∷
   re 19 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q6 ∷
   re 19 5 (CX30 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   re 23 3 (CK13⁻ ∷ []) ∷
   rw 22 q13 ∷
   rw 21 q14 ∷
   rw 20 q15 ∷
   re 20 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q6 ∷
   re 20 5 (CX30 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   re 24 3 (CS13⁻ ∷ []) ∷
   rw 23 q3 ∷
   rw 22 q12 ∷
   rw 21 q5 ∷
   re 21 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q6 ∷
   re 21 5 (CX30 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   re 25 3 (CS13⁻ ∷ []) ∷
   rw 24 q3 ∷
   rw 23 q12 ∷
   rw 22 q5 ∷
   re 22 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   re 22 5 (CX30 ∷ []) ∷
   rw 3 q17 ∷
   rw 80 q1 ∷
   re 82 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 81 q2 ∷
   re 82 3 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 88 q2 ∷
   re 86 3 (CX31 ∷ []) ∷
   rw 85 q18 ∷
   rw 84 q19 ∷
   rw 83 q20 ∷
   re 83 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 82 q6 ∷
   re 83 5 (CS03 ∷ []) ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 85 q6 ∷
   re 81 3 (CX31 ∷ []) ∷
   rw 82 q1 ∷
   rw 79 q1 ∷
   re 81 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 80 q2 ∷
   re 81 3 (CS03 ∷ []) ∷
   re 81 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 87 q2 ∷
   re 85 3 (CX31 ∷ []) ∷
   rw 84 q18 ∷
   rw 83 q19 ∷
   rw 82 q20 ∷
   re 82 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 81 q6 ∷
   re 82 5 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 84 q6 ∷
   re 80 3 (CX31 ∷ []) ∷
   rw 81 q1 ∷
   rw 78 q1 ∷
   re 80 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 79 q2 ∷
   re 80 3 (CS03 ∷ []) ∷
   re 80 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 86 q2 ∷
   re 84 3 (CX31 ∷ []) ∷
   rw 83 q18 ∷
   rw 82 q19 ∷
   rw 81 q20 ∷
   re 81 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 80 q6 ∷
   re 81 5 (CS03 ∷ []) ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 83 q6 ∷
   re 79 3 (CX31 ∷ []) ∷
   rw 80 q1 ∷
   rw 77 q1 ∷
   re 79 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 78 q2 ∷
   re 79 3 (CS03 ∷ []) ∷
   re 79 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 85 q2 ∷
   re 83 3 (CX31 ∷ []) ∷
   rw 82 q18 ∷
   rw 81 q19 ∷
   rw 80 q20 ∷
   re 80 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 79 q6 ∷
   re 80 5 (CS03 ∷ []) ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 82 q6 ∷
   re 78 3 (CX31 ∷ []) ∷
   rw 79 q1 ∷
   rw 76 q1 ∷
   re 78 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 77 q2 ∷
   re 78 3 (CS03 ∷ []) ∷
   re 78 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 84 q2 ∷
   re 82 3 (CX31 ∷ []) ∷
   rw 81 q18 ∷
   rw 80 q19 ∷
   rw 79 q20 ∷
   re 79 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 78 q6 ∷
   re 79 5 (CS03 ∷ []) ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 81 q6 ∷
   re 77 3 (CX31 ∷ []) ∷
   rw 78 q1 ∷
   rw 75 q1 ∷
   re 77 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 76 q2 ∷
   re 77 3 (CS03 ∷ []) ∷
   re 77 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 83 q2 ∷
   re 81 3 (CX31 ∷ []) ∷
   rw 80 q18 ∷
   rw 79 q19 ∷
   rw 78 q20 ∷
   re 78 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 77 q6 ∷
   re 78 5 (CS03 ∷ []) ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 80 q6 ∷
   re 76 3 (CX31 ∷ []) ∷
   rw 77 q1 ∷
   rw 74 q21 ∷
   rw 75 q22 ∷
   rw 76 q21 ∷
   rw 73 q23 ∷
   re 75 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 74 q2 ∷
   re 75 3 (CK03 ∷ []) ∷
   re 75 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 81 q2 ∷
   re 79 3 (CX31 ∷ []) ∷
   rw 78 q18 ∷
   rw 77 q24 ∷
   rw 76 q20 ∷
   re 76 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 75 q6 ∷
   re 76 5 (CK03 ∷ []) ∷
   re 76 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 78 q6 ∷
   re 74 3 (CX31 ∷ []) ∷
   rw 75 q23 ∷
   rw 72 q1 ∷
   re 74 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 73 q2 ∷
   re 74 3 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 80 q2 ∷
   re 78 3 (CX31 ∷ []) ∷
   rw 77 q18 ∷
   rw 76 q19 ∷
   rw 75 q20 ∷
   re 75 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 74 q6 ∷
   re 75 5 (CS03 ∷ []) ∷ []) Eq.refl

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D188 (W : Ws) where

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
  q10 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q11 : Eqn
  q11 = eqn (S0 ∷ CX31 ∷ []) (CX31 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑ • CX₁₀ • Swap ↑)))
  q12 : Eqn
  q12 = eqn (CK02 ∷ X3 ∷ []) (X3 ∷ CK02 ∷ []) (low₃-comm ((Swap ↑ • CK₀₁ • Swap ↑)) (X))
  q13 : Eqn
  q13 = eqn (CK01 ∷ CX32 ∷ []) (CX32 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₁₀))
  q14 : Eqn
  q14 = wE 780 W
  q15 : Eqn
  q15 = wE 781 W
  q16 : Eqn
  q16 = wE 21 W
  q17 : Eqn
  q17 = eqn (CX10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((CS • CS • CS)))
  q18 : Eqn
  q18 = wE 51 W
  q19 : Eqn
  q19 = eqn (S1⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (Swap))
  q20 : Eqn
  q20 = wE 782 W
  q21 : Eqn
  q21 = wE 353 W
  q22 : Eqn
  q22 = eqn (CX10 ∷ CK23⁻ ∷ []) (CK23⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((S • CK₀₁)))
  q23 : Eqn
  q23 = wE 358 W
  q24 : Eqn
  q24 = wE 783 W
  q25 : Eqn
  q25 = wE 784 W

-- Bar(['S', 'S', 'K', 'S', 'K', 'K'];3,0->2) passes white iX via V2 conjugates 1 part1: 500 steps
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part1 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X3 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ X3 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CK02 ∷ X3 ∷ CK02 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part1 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X3 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ X3 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CK02 ∷ X3 ∷ CK02 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ [])
  (rw 33 q1 ∷
   re 34 5 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
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
   rw 33 q3 ∷
   rw 32 q7 ∷
   re 31 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   rw 30 q7 ∷
   re 29 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   rw 30 q8 ∷
   rw 29 q9 ∷
   rw 32 q3 ∷
   re 30 3 (CX31 ∷ []) ∷
   rw 31 q9 ∷
   rw 34 q3 ∷
   re 32 3 (CX30 ∷ []) ∷
   rw 33 q1 ∷
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
   rw 22 q10 ∷
   rw 23 q11 ∷
   rw 24 q10 ∷
   rw 21 q12 ∷
   re 23 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 22 q3 ∷
   re 23 3 (CK03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q3 ∷
   re 27 3 (CX31 ∷ []) ∷
   rw 26 q4 ∷
   rw 25 q13 ∷
   rw 24 q6 ∷
   re 24 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   re 24 5 (CK03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   re 22 3 (CX31 ∷ []) ∷
   rw 23 q12 ∷
   rw 20 q2 ∷
   re 22 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 21 q3 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q3 ∷
   re 26 3 (CX31 ∷ []) ∷
   rw 25 q4 ∷
   rw 24 q5 ∷
   rw 23 q6 ∷
   re 23 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 22 q1 ∷
   re 23 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 21 3 (CX31 ∷ []) ∷
   rw 22 q2 ∷
   rw 19 q2 ∷
   re 21 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q3 ∷
   re 25 3 (CX31 ∷ []) ∷
   rw 24 q4 ∷
   rw 23 q5 ∷
   rw 22 q6 ∷
   re 22 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 21 q1 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   re 20 3 (CX31 ∷ []) ∷
   rw 21 q2 ∷
   rw 18 q2 ∷
   re 20 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q3 ∷
   re 24 3 (CX31 ∷ []) ∷
   rw 23 q4 ∷
   rw 22 q5 ∷
   rw 21 q6 ∷
   re 21 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 20 q1 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   re 19 3 (CX31 ∷ []) ∷
   rw 20 q2 ∷
   rw 17 q10 ∷
   rw 18 q11 ∷
   rw 19 q10 ∷
   rw 16 q12 ∷
   re 18 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   re 18 3 (CK03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q3 ∷
   re 22 3 (CX31 ∷ []) ∷
   rw 21 q4 ∷
   rw 20 q13 ∷
   rw 19 q6 ∷
   re 19 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 18 q1 ∷
   re 19 5 (CK03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 21 q1 ∷
   re 17 3 (CX31 ∷ []) ∷
   rw 18 q12 ∷
   rw 15 q10 ∷
   rw 16 q11 ∷
   rw 17 q10 ∷
   rw 14 q12 ∷
   re 16 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   re 16 3 (CK03 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q3 ∷
   re 20 3 (CX31 ∷ []) ∷
   rw 19 q4 ∷
   rw 18 q13 ∷
   rw 17 q6 ∷
   re 17 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 16 q1 ∷
   re 17 5 (CK03 ∷ []) ∷
   re 17 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 19 q1 ∷
   re 15 3 (CX31 ∷ []) ∷
   rw 16 q12 ∷
   rw 17 q3 ∷
   rw 16 q7 ∷
   re 15 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 17 q1 ∷
   rw 14 q7 ∷
   re 13 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 15 q1 ∷
   rw 14 q8 ∷
   rw 13 q9 ∷
   rw 16 q3 ∷
   re 14 3 (CX31 ∷ []) ∷
   rw 15 q9 ∷
   rw 18 q3 ∷
   re 16 3 (CX30 ∷ []) ∷
   rw 17 q1 ∷
   rw 7 q14 ∷
   rw 33 q15 ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q3 ∷
   re 36 3 (CS13⁻ ∷ []) ∷
   rw 35 q16 ∷
   rw 34 q17 ∷
   rw 33 q18 ∷
   re 33 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 33 5 (CX30 ∷ []) ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q3 ∷
   re 37 3 (CS13⁻ ∷ []) ∷
   rw 36 q16 ∷
   rw 35 q17 ∷
   rw 34 q18 ∷
   re 34 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 34 5 (CX30 ∷ []) ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q3 ∷
   re 38 3 (CS13⁻ ∷ []) ∷
   rw 37 q16 ∷
   rw 36 q17 ∷
   rw 35 q18 ∷
   re 35 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   re 35 5 (CX30 ∷ []) ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q3 ∷
   re 39 3 (CS13⁻ ∷ []) ∷
   rw 38 q16 ∷
   rw 37 q17 ∷
   rw 36 q18 ∷
   re 36 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   re 36 5 (CX30 ∷ []) ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q3 ∷
   re 40 3 (CS13⁻ ∷ []) ∷
   rw 39 q16 ∷
   rw 38 q17 ∷
   rw 37 q18 ∷
   re 37 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
   re 37 5 (CX30 ∷ []) ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q3 ∷
   re 41 3 (CS13⁻ ∷ []) ∷
   rw 40 q16 ∷
   rw 39 q17 ∷
   rw 38 q18 ∷
   re 38 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 37 q1 ∷
   re 38 5 (CX30 ∷ []) ∷
   rw 40 q3 ∷
   rw 39 q19 ∷
   re 38 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   rw 39 q20 ∷
   rw⁻ 38 q19 ∷
   rw 41 q3 ∷
   re 39 3 (CX30 ∷ []) ∷
   rw 40 q1 ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q3 ∷
   re 43 3 (CK13⁻ ∷ []) ∷
   rw 42 q21 ∷
   rw 41 q22 ∷
   rw 40 q23 ∷
   re 40 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 39 q1 ∷
   re 40 5 (CX30 ∷ []) ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q3 ∷
   re 44 3 (CS13⁻ ∷ []) ∷
   rw 43 q16 ∷
   rw 42 q17 ∷
   rw 41 q18 ∷
   re 41 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   re 41 5 (CX30 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q3 ∷
   re 45 3 (CS13⁻ ∷ []) ∷
   rw 44 q16 ∷
   rw 43 q17 ∷
   rw 42 q18 ∷
   re 42 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   re 42 5 (CX30 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q3 ∷
   re 46 3 (CS13⁻ ∷ []) ∷
   rw 45 q16 ∷
   rw 44 q17 ∷
   rw 43 q18 ∷
   re 43 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   re 43 5 (CX30 ∷ []) ∷
   rw 17 q24 ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q3 ∷
   re 20 3 (CS13⁻ ∷ []) ∷
   rw 19 q16 ∷
   rw 18 q17 ∷
   rw 17 q18 ∷
   re 17 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q1 ∷
   re 17 5 (CX30 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q3 ∷
   re 21 3 (CS13⁻ ∷ []) ∷
   rw 20 q16 ∷
   rw 19 q17 ∷
   rw 18 q18 ∷
   re 18 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q1 ∷
   re 18 5 (CX30 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q3 ∷
   re 22 3 (CS13⁻ ∷ []) ∷
   rw 21 q16 ∷
   rw 20 q17 ∷
   rw 19 q18 ∷
   re 19 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q1 ∷
   re 19 5 (CX30 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q3 ∷
   re 23 3 (CS13⁻ ∷ []) ∷
   rw 22 q16 ∷
   rw 21 q17 ∷
   rw 20 q18 ∷
   re 20 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q1 ∷
   re 20 5 (CX30 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q3 ∷
   re 24 3 (CS13⁻ ∷ []) ∷
   rw 23 q16 ∷
   rw 22 q17 ∷
   rw 21 q18 ∷
   re 21 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q1 ∷
   re 21 5 (CX30 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q3 ∷
   re 25 3 (CS13⁻ ∷ []) ∷
   rw 24 q16 ∷
   rw 23 q17 ∷
   rw 22 q18 ∷
   re 22 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q1 ∷
   re 22 5 (CX30 ∷ []) ∷
   rw 24 q3 ∷
   rw 23 q19 ∷
   re 22 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   rw 23 q20 ∷
   rw⁻ 22 q19 ∷
   rw 25 q3 ∷
   re 23 3 (CX30 ∷ []) ∷
   rw 24 q1 ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q3 ∷
   re 27 3 (CK13⁻ ∷ []) ∷
   rw 26 q21 ∷
   rw 25 q22 ∷
   rw 24 q23 ∷
   re 24 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   re 24 5 (CX30 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q3 ∷
   re 28 3 (CS13⁻ ∷ []) ∷
   rw 27 q16 ∷
   rw 26 q17 ∷
   rw 25 q18 ∷
   re 25 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   re 25 5 (CX30 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q3 ∷
   re 29 3 (CS13⁻ ∷ []) ∷
   rw 28 q16 ∷
   rw 27 q17 ∷
   rw 26 q18 ∷
   re 26 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 26 5 (CX30 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q3 ∷
   re 30 3 (CS13⁻ ∷ []) ∷
   rw 29 q16 ∷
   rw 28 q17 ∷
   rw 27 q18 ∷
   re 27 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   re 27 5 (CX30 ∷ []) ∷
   rw 10 q25 ∷
   rw 49 q12 ∷
   re 51 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 50 q3 ∷
   re 51 3 (CK03 ∷ []) ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 57 q3 ∷
   re 55 3 (CX31 ∷ []) ∷
   rw 54 q4 ∷
   rw 53 q13 ∷
   rw 52 q6 ∷
   re 52 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 51 q1 ∷
   re 52 5 (CK03 ∷ []) ∷
   re 52 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 54 q1 ∷
   re 50 3 (CX31 ∷ []) ∷
   rw 51 q12 ∷
   rw 48 q12 ∷
   re 50 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 49 q3 ∷
   re 50 3 (CK03 ∷ []) ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q3 ∷
   re 54 3 (CX31 ∷ []) ∷
   rw 53 q4 ∷
   rw 52 q13 ∷
   rw 51 q6 ∷
   re 51 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 50 q1 ∷
   re 51 5 (CK03 ∷ []) ∷
   re 51 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 53 q1 ∷ []) Eq.refl

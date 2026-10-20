{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D191 (W : Ws) where

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
  q1 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q2 : Eqn
  q2 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q3 : Eqn
  q3 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q4 : Eqn
  q4 = eqn (CX10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((CS • CS • CS)))
  q5 : Eqn
  q5 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q6 : Eqn
  q6 = eqn (CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (wn 783 W)
  q7 : Eqn
  q7 = eqn (S1⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (Swap))
  q8 : Eqn
  q8 = eqn (CX20 ∷ S1⁻ ∷ []) (S1⁻ ∷ CX20 ∷ []) (wn 782 W)
  q9 : Eqn
  q9 = eqn (Sw12 ∷ CK13⁻ ∷ []) (CK23⁻ ∷ Sw12 ∷ []) (wn 353 W)
  q10 : Eqn
  q10 = eqn (CX10 ∷ CK23⁻ ∷ []) (CK23⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((S • CK₀₁)))
  q11 : Eqn
  q11 = eqn (Sw12 ∷ CK23⁻ ∷ []) (CK13⁻ ∷ Sw12 ∷ []) (wn 358 W)
  q12 : Eqn
  q12 = eqn (CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) (wn 784 W)
  q13 : Eqn
  q13 = eqn (CK02 ∷ X3 ∷ []) (X3 ∷ CK02 ∷ []) (low₃-comm ((Swap ↑ • CK₀₁ • Swap ↑)) (X))
  q14 : Eqn
  q14 = eqn (Sw12 ∷ CX31 ∷ []) (CX32 ∷ Sw12 ∷ []) (wn 113 W)
  q15 : Eqn
  q15 = eqn (CK01 ∷ CX32 ∷ []) (CX32 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₁₀))
  q16 : Eqn
  q16 = eqn (Sw12 ∷ CX32 ∷ []) (CX31 ∷ Sw12 ∷ []) (wn 114 W)
  q17 : Eqn
  q17 = eqn (CS02 ∷ X3 ∷ []) (X3 ∷ CS02 ∷ []) (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q18 : Eqn
  q18 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q19 : Eqn
  q19 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q20 : Eqn
  q20 = eqn (CX20 ∷ X2 ∷ CX21 ∷ X2 ∷ []) (X2 ∷ CX21 ∷ X2 ∷ CX20 ∷ []) (wn 779 W)
  q21 : Eqn
  q21 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q22 : Eqn
  q22 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q23 : Eqn
  q23 = eqn (S0 ∷ CX31 ∷ []) (CX31 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑ • CX₁₀ • Swap ↑)))
  q24 : Eqn
  q24 = eqn (CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X3 ∷ CX31 ∷ X3 ∷ []) (X3 ∷ CX31 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) (wn 780 W)
  q25 : Eqn
  q25 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q26 : Eqn
  q26 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q27 : Eqn
  q27 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q28 : Eqn
  q28 = eqn (Sw01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑ • CK₁₀)))
  q29 : Eqn
  q29 = eqn (CK02 ∷ Sw01 ∷ []) (Sw01 ∷ CK12 ∷ []) (wn 772 W)
  q30 : Eqn
  q30 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q31 : Eqn
  q31 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q32 : Eqn
  q32 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q33 : Eqn
  q33 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wn 481 W)
  q34 : Eqn
  q34 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q35 : Eqn
  q35 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))

-- Bar(['S', 'S', 'K', 'S', 'K', 'K'];3,0->2) passes white iX via V2 conjugates 1 part4: 500 steps
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part4 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ Sw01 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part4 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ Sw01 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ [])
  (rw 73 q1 ∷
   re 74 5 (CX30 ∷ []) ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 80 q2 ∷
   re 78 3 (CS13⁻ ∷ []) ∷
   rw 77 q3 ∷
   rw 76 q4 ∷
   rw 75 q5 ∷
   re 75 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 74 q1 ∷
   re 75 5 (CX30 ∷ []) ∷
   rw 49 q6 ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q2 ∷
   re 52 3 (CS13⁻ ∷ []) ∷
   rw 51 q3 ∷
   rw 50 q4 ∷
   rw 49 q5 ∷
   re 49 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 48 q1 ∷
   re 49 5 (CX30 ∷ []) ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q2 ∷
   re 53 3 (CS13⁻ ∷ []) ∷
   rw 52 q3 ∷
   rw 51 q4 ∷
   rw 50 q5 ∷
   re 50 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   re 50 5 (CX30 ∷ []) ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q2 ∷
   re 54 3 (CS13⁻ ∷ []) ∷
   rw 53 q3 ∷
   rw 52 q4 ∷
   rw 51 q5 ∷
   re 51 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 50 q1 ∷
   re 51 5 (CX30 ∷ []) ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 57 q2 ∷
   re 55 3 (CS13⁻ ∷ []) ∷
   rw 54 q3 ∷
   rw 53 q4 ∷
   rw 52 q5 ∷
   re 52 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 51 q1 ∷
   re 52 5 (CX30 ∷ []) ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q2 ∷
   re 56 3 (CS13⁻ ∷ []) ∷
   rw 55 q3 ∷
   rw 54 q4 ∷
   rw 53 q5 ∷
   re 53 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 52 q1 ∷
   re 53 5 (CX30 ∷ []) ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q2 ∷
   re 57 3 (CS13⁻ ∷ []) ∷
   rw 56 q3 ∷
   rw 55 q4 ∷
   rw 54 q5 ∷
   re 54 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 53 q1 ∷
   re 54 5 (CX30 ∷ []) ∷
   rw 56 q2 ∷
   rw 55 q7 ∷
   re 54 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 56 q1 ∷
   rw 55 q8 ∷
   rw⁻ 54 q7 ∷
   rw 57 q2 ∷
   re 55 3 (CX30 ∷ []) ∷
   rw 56 q1 ∷
   re 55 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 61 q2 ∷
   re 59 3 (CK13⁻ ∷ []) ∷
   rw 58 q9 ∷
   rw 57 q10 ∷
   rw 56 q11 ∷
   re 56 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 55 q1 ∷
   re 56 5 (CX30 ∷ []) ∷
   re 56 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 62 q2 ∷
   re 60 3 (CS13⁻ ∷ []) ∷
   rw 59 q3 ∷
   rw 58 q4 ∷
   rw 57 q5 ∷
   re 57 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 56 q1 ∷
   re 57 5 (CX30 ∷ []) ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 63 q2 ∷
   re 61 3 (CS13⁻ ∷ []) ∷
   rw 60 q3 ∷
   rw 59 q4 ∷
   rw 58 q5 ∷
   re 58 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 57 q1 ∷
   re 58 5 (CX30 ∷ []) ∷
   re 58 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 64 q2 ∷
   re 62 3 (CS13⁻ ∷ []) ∷
   rw 61 q3 ∷
   rw 60 q4 ∷
   rw 59 q5 ∷
   re 59 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 58 q1 ∷
   re 59 5 (CX30 ∷ []) ∷
   rw 42 q12 ∷
   rw 81 q13 ∷
   re 83 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 82 q2 ∷
   re 83 3 (CK03 ∷ []) ∷
   re 83 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 89 q2 ∷
   re 87 3 (CX31 ∷ []) ∷
   rw 86 q14 ∷
   rw 85 q15 ∷
   rw 84 q16 ∷
   re 84 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 83 q1 ∷
   re 84 5 (CK03 ∷ []) ∷
   re 84 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 86 q1 ∷
   re 82 3 (CX31 ∷ []) ∷
   rw 83 q13 ∷
   rw 80 q13 ∷
   re 82 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 81 q2 ∷
   re 82 3 (CK03 ∷ []) ∷
   re 82 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 88 q2 ∷
   re 86 3 (CX31 ∷ []) ∷
   rw 85 q14 ∷
   rw 84 q15 ∷
   rw 83 q16 ∷
   re 83 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 82 q1 ∷
   re 83 5 (CK03 ∷ []) ∷
   re 83 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 85 q1 ∷
   re 81 3 (CX31 ∷ []) ∷
   rw 82 q13 ∷
   rw 79 q17 ∷
   re 81 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 80 q2 ∷
   re 81 3 (CS03 ∷ []) ∷
   re 81 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 87 q2 ∷
   re 85 3 (CX31 ∷ []) ∷
   rw 84 q14 ∷
   rw 83 q18 ∷
   rw 82 q16 ∷
   re 82 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 81 q1 ∷
   re 82 5 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 84 q1 ∷
   re 80 3 (CX31 ∷ []) ∷
   rw 81 q17 ∷
   rw 78 q13 ∷
   re 80 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 79 q2 ∷
   re 80 3 (CK03 ∷ []) ∷
   re 80 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 86 q2 ∷
   re 84 3 (CX31 ∷ []) ∷
   rw 83 q14 ∷
   rw 82 q15 ∷
   rw 81 q16 ∷
   re 81 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 80 q1 ∷
   re 81 5 (CK03 ∷ []) ∷
   re 81 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 83 q1 ∷
   re 79 3 (CX31 ∷ []) ∷
   rw 80 q13 ∷
   rw 77 q17 ∷
   re 79 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 78 q2 ∷
   re 79 3 (CS03 ∷ []) ∷
   re 79 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 85 q2 ∷
   re 83 3 (CX31 ∷ []) ∷
   rw 82 q14 ∷
   rw 81 q18 ∷
   rw 80 q16 ∷
   re 80 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 79 q1 ∷
   re 80 5 (CS03 ∷ []) ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 82 q1 ∷
   re 78 3 (CX31 ∷ []) ∷
   rw 79 q17 ∷
   rw 76 q17 ∷
   re 78 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 77 q2 ∷
   re 78 3 (CS03 ∷ []) ∷
   re 78 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 84 q2 ∷
   re 82 3 (CX31 ∷ []) ∷
   rw 81 q14 ∷
   rw 80 q18 ∷
   rw 79 q16 ∷
   re 79 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 78 q1 ∷
   re 79 5 (CS03 ∷ []) ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 81 q1 ∷
   re 77 3 (CX31 ∷ []) ∷
   rw 78 q17 ∷
   rw 79 q2 ∷
   rw 78 q19 ∷
   re 77 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 79 q1 ∷
   rw 76 q19 ∷
   re 75 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 77 q1 ∷
   rw 76 q20 ∷
   rw 75 q21 ∷
   rw 78 q2 ∷
   re 76 3 (CX31 ∷ []) ∷
   rw 77 q21 ∷
   rw 80 q2 ∷
   re 78 3 (CX30 ∷ []) ∷
   rw 79 q1 ∷
   rw 74 q17 ∷
   re 76 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 75 q2 ∷
   re 76 3 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 82 q2 ∷
   re 80 3 (CX31 ∷ []) ∷
   rw 79 q14 ∷
   rw 78 q18 ∷
   rw 77 q16 ∷
   re 77 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 76 q1 ∷
   re 77 5 (CS03 ∷ []) ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q1 ∷
   re 75 3 (CX31 ∷ []) ∷
   rw 76 q17 ∷
   rw 73 q17 ∷
   re 75 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 74 q2 ∷
   re 75 3 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 81 q2 ∷
   re 79 3 (CX31 ∷ []) ∷
   rw 78 q14 ∷
   rw 77 q18 ∷
   rw 76 q16 ∷
   re 76 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 75 q1 ∷
   re 76 5 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q1 ∷
   re 74 3 (CX31 ∷ []) ∷
   rw 75 q17 ∷
   rw 72 q17 ∷
   re 74 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 73 q2 ∷
   re 74 3 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 80 q2 ∷
   re 78 3 (CX31 ∷ []) ∷
   rw 77 q14 ∷
   rw 76 q18 ∷
   rw 75 q16 ∷
   re 75 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 74 q1 ∷
   re 75 5 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q1 ∷
   re 73 3 (CX31 ∷ []) ∷
   rw 74 q17 ∷
   rw 71 q17 ∷
   re 73 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 72 q2 ∷
   re 73 3 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 79 q2 ∷
   re 77 3 (CX31 ∷ []) ∷
   rw 76 q14 ∷
   rw 75 q18 ∷
   rw 74 q16 ∷
   re 74 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 73 q1 ∷
   re 74 5 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q1 ∷
   re 72 3 (CX31 ∷ []) ∷
   rw 73 q17 ∷
   rw 70 q17 ∷
   re 72 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 71 q2 ∷
   re 72 3 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 78 q2 ∷
   re 76 3 (CX31 ∷ []) ∷
   rw 75 q14 ∷
   rw 74 q18 ∷
   rw 73 q16 ∷
   re 73 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 72 q1 ∷
   re 73 5 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q1 ∷
   re 71 3 (CX31 ∷ []) ∷
   rw 72 q17 ∷
   rw 69 q17 ∷
   re 71 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 70 q2 ∷
   re 71 3 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 77 q2 ∷
   re 75 3 (CX31 ∷ []) ∷
   rw 74 q14 ∷
   rw 73 q18 ∷
   rw 72 q16 ∷
   re 72 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 71 q1 ∷
   re 72 5 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q1 ∷
   re 70 3 (CX31 ∷ []) ∷
   rw 71 q17 ∷
   rw 68 q22 ∷
   rw 69 q23 ∷
   rw 70 q22 ∷
   rw 67 q13 ∷
   re 69 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 68 q2 ∷
   re 69 3 (CK03 ∷ []) ∷
   re 69 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 75 q2 ∷
   re 73 3 (CX31 ∷ []) ∷
   rw 72 q14 ∷
   rw 71 q15 ∷
   rw 70 q16 ∷
   re 70 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 69 q1 ∷
   re 70 5 (CK03 ∷ []) ∷
   re 70 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 72 q1 ∷
   re 68 3 (CX31 ∷ []) ∷
   rw 69 q13 ∷
   rw 66 q17 ∷
   re 68 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 67 q2 ∷
   re 68 3 (CS03 ∷ []) ∷
   re 68 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 74 q2 ∷
   re 72 3 (CX31 ∷ []) ∷
   rw 71 q14 ∷
   rw 70 q18 ∷
   rw 69 q16 ∷
   re 69 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 68 q1 ∷
   re 69 5 (CS03 ∷ []) ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 71 q1 ∷
   re 67 3 (CX31 ∷ []) ∷
   rw 68 q17 ∷
   rw 65 q17 ∷
   re 67 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 66 q2 ∷
   re 67 3 (CS03 ∷ []) ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q2 ∷
   re 71 3 (CX31 ∷ []) ∷
   rw 70 q14 ∷
   rw 69 q18 ∷
   rw 68 q16 ∷
   re 68 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 67 q1 ∷
   re 68 5 (CS03 ∷ []) ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 70 q1 ∷
   re 66 3 (CX31 ∷ []) ∷
   rw 67 q17 ∷
   rw 64 q17 ∷
   re 66 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 65 q2 ∷
   re 66 3 (CS03 ∷ []) ∷
   re 66 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 72 q2 ∷
   re 70 3 (CX31 ∷ []) ∷
   rw 69 q14 ∷
   rw 68 q18 ∷
   rw 67 q16 ∷
   re 67 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 66 q1 ∷
   re 67 5 (CS03 ∷ []) ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 69 q1 ∷
   re 65 3 (CX31 ∷ []) ∷
   rw 66 q17 ∷
   rw 63 q22 ∷
   rw 64 q23 ∷
   rw 65 q22 ∷
   rw 62 q13 ∷
   re 64 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 63 q2 ∷
   re 64 3 (CK03 ∷ []) ∷
   re 64 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 70 q2 ∷
   re 68 3 (CX31 ∷ []) ∷
   rw 67 q14 ∷
   rw 66 q15 ∷
   rw 65 q16 ∷
   re 65 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 64 q1 ∷
   re 65 5 (CK03 ∷ []) ∷
   re 65 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 67 q1 ∷
   re 63 3 (CX31 ∷ []) ∷
   rw 64 q13 ∷
   rw 61 q22 ∷
   rw 62 q23 ∷
   rw 63 q22 ∷
   rw 60 q13 ∷
   re 62 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 61 q2 ∷
   re 62 3 (CK03 ∷ []) ∷
   re 62 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 68 q2 ∷
   re 66 3 (CX31 ∷ []) ∷
   rw 65 q14 ∷
   rw 64 q15 ∷
   rw 63 q16 ∷
   re 63 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 62 q1 ∷
   re 63 5 (CK03 ∷ []) ∷
   re 63 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 65 q1 ∷
   re 61 3 (CX31 ∷ []) ∷
   rw 62 q13 ∷
   rw 63 q2 ∷
   rw 62 q19 ∷
   re 61 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 63 q1 ∷
   rw 60 q19 ∷
   re 59 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 61 q1 ∷
   rw 60 q20 ∷
   rw 59 q21 ∷
   rw 62 q2 ∷
   re 60 3 (CX31 ∷ []) ∷
   rw 61 q21 ∷
   rw 64 q2 ∷
   re 62 3 (CX30 ∷ []) ∷
   rw 63 q1 ∷
   rw 53 q24 ∷
   rw 91 q25 ∷
   rw⁻ 90 q26 ∷
   rw⁻ 89 q27 ∷
   rw⁻ 88 q27 ∷
   rw⁻ 87 q28 ∷
   rw⁻ 86 q27 ∷
   rw⁻ 85 q26 ∷
   rw 84 q29 ∷
   rw 83 q29 ∷
   rw 82 q30 ∷
   rw 81 q29 ∷
   rw 80 q30 ∷
   rw 79 q30 ∷
   re 78 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 80 q31 ∷
   rw 79 q32 ∷
   rw⁻ 78 q31 ∷
   re 79 3 (CX31 ∷ []) ∷
   rw 77 q30 ∷
   rw 76 q30 ∷
   rw 75 q30 ∷
   rw 74 q30 ∷
   rw 73 q30 ∷
   rw 72 q30 ∷
   rw 71 q33 ∷
   rw 70 q29 ∷
   rw 69 q30 ∷
   rw 68 q30 ∷
   rw 67 q30 ∷
   rw 66 q33 ∷
   rw 65 q29 ∷
   rw 64 q33 ∷
   rw 63 q29 ∷
   re 62 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 64 q31 ∷
   rw 63 q32 ∷
   rw⁻ 62 q31 ∷
   re 63 3 (CX31 ∷ []) ∷
   rw⁻ 61 q34 ∷
   rw⁻ 60 q34 ∷
   rw⁻ 59 q35 ∷
   rw⁻ 58 q34 ∷ []) Eq.refl

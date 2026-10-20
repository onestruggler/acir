{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D277 (W : Ws) where

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
  q2 = eqn (CS02 ∷ X3 ∷ []) (X3 ∷ CS02 ∷ []) (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q3 : Eqn
  q3 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q4 : Eqn
  q4 = eqn (S0 ∷ CX31 ∷ []) (CX31 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑ • CX₁₀ • Swap ↑)))
  q5 : Eqn
  q5 = eqn (CK02 ∷ X3 ∷ []) (X3 ∷ CK02 ∷ []) (low₃-comm ((Swap ↑ • CK₀₁ • Swap ↑)) (X))
  q6 : Eqn
  q6 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q7 : Eqn
  q7 = eqn (Sw12 ∷ CX31 ∷ []) (CX32 ∷ Sw12 ∷ []) (wn 113 W)
  q8 : Eqn
  q8 = eqn (CK01 ∷ CX32 ∷ []) (CX32 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₁₀))
  q9 : Eqn
  q9 = eqn (Sw12 ∷ CX32 ∷ []) (CX31 ∷ Sw12 ∷ []) (wn 114 W)
  q10 : Eqn
  q10 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q11 : Eqn
  q11 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q12 : Eqn
  q12 = eqn (CX20 ∷ X2 ∷ CX21 ∷ X2 ∷ []) (X2 ∷ CX21 ∷ X2 ∷ CX20 ∷ []) (wn 779 W)
  q13 : Eqn
  q13 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q14 : Eqn
  q14 = eqn (CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CX31 ∷ X3 ∷ []) (X3 ∷ CX31 ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ []) (wn 858 W)
  q15 : Eqn
  q15 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q16 : Eqn
  q16 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑ • CK₁₀)))
  q19 : Eqn
  q19 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q20 : Eqn
  q20 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wn 481 W)
  q21 : Eqn
  q21 = eqn (CK02 ∷ Sw01 ∷ []) (Sw01 ∷ CK12 ∷ []) (wn 772 W)
  q22 : Eqn
  q22 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q23 : Eqn
  q23 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q24 : Eqn
  q24 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q25 : Eqn
  q25 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q26 : Eqn
  q26 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q27 : Eqn
  q27 = eqn (CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ []) (wn 861 W)
  q28 : Eqn
  q28 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q29 : Eqn
  q29 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q30 : Eqn
  q30 = eqn (Sw01 ∷ S1 ∷ []) (S0 ∷ Sw01 ∷ []) (wn 315 W)
  q31 : Eqn
  q31 = eqn (Sw01 ∷ CK12 ∷ []) (CK02 ∷ Sw01 ∷ []) (wn 329 W)

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];3,0->2) passes white iX via V2 conjugates 1 part9: 500 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part9 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ CX31 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw01 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw01 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part9 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ CX31 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw01 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw01 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ [])
  (re 95 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 94 q1 ∷
   re 95 5 (CS03 ∷ []) ∷
   re 95 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 97 q1 ∷
   re 93 3 (CX31 ∷ []) ∷
   rw 94 q2 ∷
   rw 91 q3 ∷
   rw 92 q4 ∷
   rw 93 q3 ∷
   rw 90 q5 ∷
   re 92 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 91 q6 ∷
   re 92 3 (CK03 ∷ []) ∷
   re 92 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 98 q6 ∷
   re 96 3 (CX31 ∷ []) ∷
   rw 95 q7 ∷
   rw 94 q8 ∷
   rw 93 q9 ∷
   re 93 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 92 q1 ∷
   re 93 5 (CK03 ∷ []) ∷
   re 93 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 95 q1 ∷
   re 91 3 (CX31 ∷ []) ∷
   rw 92 q5 ∷
   rw 89 q3 ∷
   rw 90 q4 ∷
   rw 91 q3 ∷
   rw 88 q3 ∷
   rw 89 q4 ∷
   rw 90 q3 ∷
   rw 87 q3 ∷
   rw 88 q4 ∷
   rw 89 q3 ∷
   rw 86 q2 ∷
   re 88 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 87 q6 ∷
   re 88 3 (CS03 ∷ []) ∷
   re 88 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 94 q6 ∷
   re 92 3 (CX31 ∷ []) ∷
   rw 91 q7 ∷
   rw 90 q10 ∷
   rw 89 q9 ∷
   re 89 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 88 q1 ∷
   re 89 5 (CS03 ∷ []) ∷
   re 89 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 91 q1 ∷
   re 87 3 (CX31 ∷ []) ∷
   rw 88 q2 ∷
   rw 85 q2 ∷
   re 87 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 86 q6 ∷
   re 87 3 (CS03 ∷ []) ∷
   re 87 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 93 q6 ∷
   re 91 3 (CX31 ∷ []) ∷
   rw 90 q7 ∷
   rw 89 q10 ∷
   rw 88 q9 ∷
   re 88 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 87 q1 ∷
   re 88 5 (CS03 ∷ []) ∷
   re 88 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 90 q1 ∷
   re 86 3 (CX31 ∷ []) ∷
   rw 87 q2 ∷
   rw 84 q2 ∷
   re 86 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 85 q6 ∷
   re 86 3 (CS03 ∷ []) ∷
   re 86 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 92 q6 ∷
   re 90 3 (CX31 ∷ []) ∷
   rw 89 q7 ∷
   rw 88 q10 ∷
   rw 87 q9 ∷
   re 87 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 86 q1 ∷
   re 87 5 (CS03 ∷ []) ∷
   re 87 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 89 q1 ∷
   re 85 3 (CX31 ∷ []) ∷
   rw 86 q2 ∷
   rw 83 q2 ∷
   re 85 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 84 q6 ∷
   re 85 3 (CS03 ∷ []) ∷
   re 85 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 91 q6 ∷
   re 89 3 (CX31 ∷ []) ∷
   rw 88 q7 ∷
   rw 87 q10 ∷
   rw 86 q9 ∷
   re 86 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 85 q1 ∷
   re 86 5 (CS03 ∷ []) ∷
   re 86 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 88 q1 ∷
   re 84 3 (CX31 ∷ []) ∷
   rw 85 q2 ∷
   rw 82 q2 ∷
   re 84 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 83 q6 ∷
   re 84 3 (CS03 ∷ []) ∷
   re 84 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 90 q6 ∷
   re 88 3 (CX31 ∷ []) ∷
   rw 87 q7 ∷
   rw 86 q10 ∷
   rw 85 q9 ∷
   re 85 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 84 q1 ∷
   re 85 5 (CS03 ∷ []) ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 87 q1 ∷
   re 83 3 (CX31 ∷ []) ∷
   rw 84 q2 ∷
   rw 81 q2 ∷
   re 83 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 82 q6 ∷
   re 83 3 (CS03 ∷ []) ∷
   re 83 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 89 q6 ∷
   re 87 3 (CX31 ∷ []) ∷
   rw 86 q7 ∷
   rw 85 q10 ∷
   rw 84 q9 ∷
   re 84 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 83 q1 ∷
   re 84 5 (CS03 ∷ []) ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 86 q1 ∷
   re 82 3 (CX31 ∷ []) ∷
   rw 83 q2 ∷
   rw 80 q2 ∷
   re 82 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 81 q6 ∷
   re 82 3 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 88 q6 ∷
   re 86 3 (CX31 ∷ []) ∷
   rw 85 q7 ∷
   rw 84 q10 ∷
   rw 83 q9 ∷
   re 83 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 82 q1 ∷
   re 83 5 (CS03 ∷ []) ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 85 q1 ∷
   re 81 3 (CX31 ∷ []) ∷
   rw 82 q2 ∷
   rw 79 q2 ∷
   re 81 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 80 q6 ∷
   re 81 3 (CS03 ∷ []) ∷
   re 81 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 87 q6 ∷
   re 85 3 (CX31 ∷ []) ∷
   rw 84 q7 ∷
   rw 83 q10 ∷
   rw 82 q9 ∷
   re 82 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 81 q1 ∷
   re 82 5 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 84 q1 ∷
   re 80 3 (CX31 ∷ []) ∷
   rw 81 q2 ∷
   rw 78 q2 ∷
   re 80 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 79 q6 ∷
   re 80 3 (CS03 ∷ []) ∷
   re 80 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 86 q6 ∷
   re 84 3 (CX31 ∷ []) ∷
   rw 83 q7 ∷
   rw 82 q10 ∷
   rw 81 q9 ∷
   re 81 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 80 q1 ∷
   re 81 5 (CS03 ∷ []) ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 83 q1 ∷
   re 79 3 (CX31 ∷ []) ∷
   rw 80 q2 ∷
   rw 77 q2 ∷
   re 79 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 78 q6 ∷
   re 79 3 (CS03 ∷ []) ∷
   re 79 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 85 q6 ∷
   re 83 3 (CX31 ∷ []) ∷
   rw 82 q7 ∷
   rw 81 q10 ∷
   rw 80 q9 ∷
   re 80 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 79 q1 ∷
   re 80 5 (CS03 ∷ []) ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 82 q1 ∷
   re 78 3 (CX31 ∷ []) ∷
   rw 79 q2 ∷
   rw 76 q2 ∷
   re 78 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 77 q6 ∷
   re 78 3 (CS03 ∷ []) ∷
   re 78 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 84 q6 ∷
   re 82 3 (CX31 ∷ []) ∷
   rw 81 q7 ∷
   rw 80 q10 ∷
   rw 79 q9 ∷
   re 79 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 78 q1 ∷
   re 79 5 (CS03 ∷ []) ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 81 q1 ∷
   re 77 3 (CX31 ∷ []) ∷
   rw 78 q2 ∷
   rw 75 q2 ∷
   re 77 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 76 q6 ∷
   re 77 3 (CS03 ∷ []) ∷
   re 77 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 83 q6 ∷
   re 81 3 (CX31 ∷ []) ∷
   rw 80 q7 ∷
   rw 79 q10 ∷
   rw 78 q9 ∷
   re 78 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 77 q1 ∷
   re 78 5 (CS03 ∷ []) ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 80 q1 ∷
   re 76 3 (CX31 ∷ []) ∷
   rw 77 q2 ∷
   rw 74 q2 ∷
   re 76 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 75 q6 ∷
   re 76 3 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 82 q6 ∷
   re 80 3 (CX31 ∷ []) ∷
   rw 79 q7 ∷
   rw 78 q10 ∷
   rw 77 q9 ∷
   re 77 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 76 q1 ∷
   re 77 5 (CS03 ∷ []) ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q1 ∷
   re 75 3 (CX31 ∷ []) ∷
   rw 76 q2 ∷
   rw 73 q2 ∷
   re 75 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 74 q6 ∷
   re 75 3 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 81 q6 ∷
   re 79 3 (CX31 ∷ []) ∷
   rw 78 q7 ∷
   rw 77 q10 ∷
   rw 76 q9 ∷
   re 76 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 75 q1 ∷
   re 76 5 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q1 ∷
   re 74 3 (CX31 ∷ []) ∷
   rw 75 q2 ∷
   rw 72 q2 ∷
   re 74 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 73 q6 ∷
   re 74 3 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 80 q6 ∷
   re 78 3 (CX31 ∷ []) ∷
   rw 77 q7 ∷
   rw 76 q10 ∷
   rw 75 q9 ∷
   re 75 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 74 q1 ∷
   re 75 5 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q1 ∷
   re 73 3 (CX31 ∷ []) ∷
   rw 74 q2 ∷
   rw 71 q2 ∷
   re 73 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 72 q6 ∷
   re 73 3 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 79 q6 ∷
   re 77 3 (CX31 ∷ []) ∷
   rw 76 q7 ∷
   rw 75 q10 ∷
   rw 74 q9 ∷
   re 74 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 73 q1 ∷
   re 74 5 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q1 ∷
   re 72 3 (CX31 ∷ []) ∷
   rw 73 q2 ∷
   rw 70 q2 ∷
   re 72 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 71 q6 ∷
   re 72 3 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 78 q6 ∷
   re 76 3 (CX31 ∷ []) ∷
   rw 75 q7 ∷
   rw 74 q10 ∷
   rw 73 q9 ∷
   re 73 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 72 q1 ∷
   re 73 5 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q1 ∷
   re 71 3 (CX31 ∷ []) ∷
   rw 72 q2 ∷
   rw 69 q2 ∷
   re 71 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 70 q6 ∷
   re 71 3 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 77 q6 ∷
   re 75 3 (CX31 ∷ []) ∷
   rw 74 q7 ∷
   rw 73 q10 ∷
   rw 72 q9 ∷
   re 72 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 71 q1 ∷
   re 72 5 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q1 ∷
   re 70 3 (CX31 ∷ []) ∷
   rw 71 q2 ∷
   rw 72 q6 ∷
   rw 71 q11 ∷
   re 70 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 72 q1 ∷
   rw 69 q11 ∷
   re 68 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 70 q1 ∷
   rw 69 q12 ∷
   rw 68 q13 ∷
   rw 71 q6 ∷
   re 69 3 (CX31 ∷ []) ∷
   rw 70 q13 ∷
   rw 73 q6 ∷
   re 71 3 (CX30 ∷ []) ∷
   rw 72 q1 ∷
   rw 53 q14 ∷
   rw 136 q15 ∷
   rw⁻ 135 q16 ∷
   rw⁻ 134 q17 ∷
   rw⁻ 133 q17 ∷
   rw⁻ 132 q18 ∷
   rw⁻ 131 q17 ∷
   rw⁻ 130 q16 ∷
   rw 129 q19 ∷
   rw 128 q19 ∷
   rw 127 q19 ∷
   rw 126 q19 ∷
   rw 125 q19 ∷
   rw 124 q19 ∷
   rw 123 q20 ∷
   rw 122 q21 ∷
   rw 121 q19 ∷
   rw 120 q19 ∷
   rw 119 q19 ∷
   rw 118 q20 ∷
   rw 117 q21 ∷
   rw 116 q20 ∷
   rw 115 q21 ∷
   re 114 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 116 q22 ∷
   rw 115 q23 ∷
   rw⁻ 114 q22 ∷
   re 115 3 (CX31 ∷ []) ∷
   rw 113 q20 ∷
   rw 112 q21 ∷
   rw 111 q20 ∷
   rw 110 q20 ∷
   rw 109 q20 ∷
   rw 108 q20 ∷
   rw 107 q21 ∷
   rw 106 q20 ∷
   rw 105 q20 ∷
   rw 104 q20 ∷
   rw 103 q19 ∷
   rw 102 q19 ∷
   rw 101 q19 ∷
   rw 100 q19 ∷
   rw 99 q19 ∷
   rw 98 q19 ∷
   rw 97 q19 ∷
   rw 96 q19 ∷
   rw 95 q19 ∷
   rw 94 q20 ∷
   rw 93 q21 ∷
   rw 92 q20 ∷
   rw 91 q20 ∷
   rw 90 q20 ∷
   rw 89 q19 ∷
   rw 88 q19 ∷
   rw 87 q19 ∷
   rw 86 q19 ∷
   rw 85 q19 ∷
   rw 84 q19 ∷
   rw 83 q19 ∷
   rw 82 q19 ∷
   rw 81 q19 ∷
   rw 80 q19 ∷
   rw 79 q19 ∷
   rw 78 q19 ∷
   rw 77 q19 ∷
   rw 76 q19 ∷
   rw 75 q19 ∷
   rw 74 q19 ∷
   rw 73 q19 ∷
   rw 72 q19 ∷
   re 71 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 73 q22 ∷
   rw 72 q23 ∷
   rw⁻ 71 q22 ∷
   re 72 3 (CX31 ∷ []) ∷
   rw⁻ 70 q24 ∷
   rw⁻ 69 q24 ∷
   rw⁻ 68 q24 ∷
   rw⁻ 67 q24 ∷
   rw⁻ 66 q24 ∷
   rw⁻ 65 q24 ∷
   rw⁻ 64 q25 ∷
   rw⁻ 63 q26 ∷
   rw⁻ 62 q24 ∷
   rw⁻ 61 q24 ∷
   rw⁻ 60 q24 ∷
   rw⁻ 59 q25 ∷
   rw⁻ 58 q26 ∷
   rw⁻ 57 q25 ∷
   rw⁻ 56 q26 ∷
   rw 57 q27 ∷
   rw 56 q16 ∷
   rw 57 q17 ∷
   rw 58 q18 ∷
   rw 59 q17 ∷
   rw 60 q17 ∷
   rw 61 q16 ∷
   rw 62 q26 ∷
   rw 63 q25 ∷
   rw 64 q26 ∷
   rw 65 q25 ∷
   rw 66 q24 ∷
   rw 67 q24 ∷
   rw 68 q24 ∷
   rw 69 q26 ∷
   rw 70 q25 ∷
   rw 71 q24 ∷
   rw 72 q24 ∷
   rw 73 q24 ∷
   rw 74 q24 ∷
   rw 75 q24 ∷
   rw 76 q24 ∷
   re 78 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 77 q22 ∷
   rw 78 q28 ∷
   rw 79 q22 ∷
   re 77 3 (CX30 ∷ []) ∷
   rw 78 q29 ∷
   rw 79 q29 ∷
   rw 80 q29 ∷
   rw 81 q29 ∷
   rw 82 q29 ∷
   rw 83 q29 ∷
   rw 84 q29 ∷
   rw 85 q29 ∷
   rw 86 q29 ∷
   rw 87 q29 ∷
   rw 88 q29 ∷
   rw 89 q29 ∷
   rw 90 q29 ∷
   rw 91 q29 ∷
   rw 92 q29 ∷
   rw 93 q29 ∷
   rw 94 q29 ∷
   rw 95 q29 ∷
   rw 96 q30 ∷
   rw 97 q30 ∷
   rw 98 q30 ∷
   rw 99 q31 ∷
   rw 100 q30 ∷
   rw 101 q29 ∷
   rw 102 q29 ∷
   rw 103 q29 ∷ []) Eq.refl

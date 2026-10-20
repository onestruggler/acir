{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D142 (W : Ws) where

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
  q6 = eqn (CX20 ∷ S3⁻ ∷ []) (S3⁻ ∷ CX20 ∷ []) (low₃-comm ((Swap ↑ • CX₁₀ • Swap ↑)) ((S • S • S)))
  q7 : Eqn
  q7 = eqn (Sw12 ∷ CK31⁻ ∷ []) (CK32⁻ ∷ Sw12 ∷ []) (wn 360 W)
  q8 : Eqn
  q8 = eqn (CX10 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((S ↑ • CK₁₀)))
  q9 : Eqn
  q9 = eqn (Sw12 ∷ CK32⁻ ∷ []) (CK31⁻ ∷ Sw12 ∷ []) (wn 362 W)
  q10 : Eqn
  q10 = eqn (S3⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S2⁻ ∷ []) (wn 689 W)
  q11 : Eqn
  q11 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q12 : Eqn
  q12 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q13 : Eqn
  q13 = eqn (CK01 ∷ Sw23 ∷ []) (Sw23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (Swap))
  q14 : Eqn
  q14 = eqn (CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (wn 541 W)
  q15 : Eqn
  q15 = eqn (Sw23 ∷ S2⁻ ∷ []) (S3⁻ ∷ Sw23 ∷ []) (wn 153 W)
  q16 : Eqn
  q16 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (wn 690 W)
  q17 : Eqn
  q17 = eqn (CK01 ∷ X2 ∷ []) (X2 ∷ CK01 ∷ []) (low-comm (CK₀₁) (X))
  q18 : Eqn
  q18 = eqn (CK01 ∷ CX23 ∷ []) (CX23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₀₁))
  q19 : Eqn
  q19 = eqn (CS01 ∷ X2 ∷ []) (X2 ∷ CS01 ∷ []) (low-comm (CS) (X))
  q20 : Eqn
  q20 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q21 : Eqn
  q21 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q22 : Eqn
  q22 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q23 : Eqn
  q23 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q24 : Eqn
  q24 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q25 : Eqn
  q25 = eqn (CX21 ∷ X2 ∷ CX23 ∷ X2 ∷ []) (X2 ∷ CX23 ∷ X2 ∷ CX21 ∷ []) (wn 612 W)
  q26 : Eqn
  q26 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q27 : Eqn
  q27 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q28 : Eqn
  q28 = eqn (S0 ∷ X2 ∷ []) (X2 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑)))
  q29 : Eqn
  q29 = eqn (S0 ∷ CX23 ∷ []) (CX23 ∷ S0 ∷ []) (low₁-comm (S) ((CX₀₁ ↑)))
  q30 : Eqn
  q30 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X2 ∷ CX23 ∷ X2 ∷ []) (X2 ∷ CX23 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (wn 613 W)
  q31 : Eqn
  q31 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) (wn 543 W)
  q32 : Eqn
  q32 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) (wn 544 W)
  q33 : Eqn
  q33 = eqn (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) (wn 534 W)

-- Bar(['S', 'S', 'K', 'S', 'K', 'K'];2,0->1) passes white iX via V2 conjugates 3 part1: 500 steps
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part1 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ Sw23 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ Sw23 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part1 = derive (X2 ∷ CS23⁻ ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS23⁻ ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ Sw23 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ Sw23 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ [])
  (rw 37 q1 ∷
   re 38 5 (CX30 ∷ []) ∷
   re 38 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   re 36 3 (CS13⁻ ∷ []) ∷
   re 38 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 37 q2 ∷
   re 38 3 (CX30 ∷ []) ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q2 ∷
   re 42 3 (CS13⁻ ∷ []) ∷
   rw 41 q3 ∷
   rw 40 q4 ∷
   rw 39 q5 ∷
   re 39 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 38 q1 ∷
   re 39 5 (CX30 ∷ []) ∷
   re 39 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   re 37 3 (CS13⁻ ∷ []) ∷
   rw 38 q6 ∷
   re 40 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 39 q2 ∷
   re 40 3 (CX30 ∷ []) ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q2 ∷
   re 44 3 (CK31⁻ ∷ []) ∷
   rw 43 q7 ∷
   rw 42 q8 ∷
   rw 41 q9 ∷
   re 41 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   re 41 5 (CX30 ∷ []) ∷
   re 41 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   re 39 3 (CK31⁻ ∷ []) ∷
   re 41 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 40 q2 ∷
   re 41 3 (CX30 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q2 ∷
   re 45 3 (CS13⁻ ∷ []) ∷
   rw 44 q3 ∷
   rw 43 q4 ∷
   rw 42 q5 ∷
   re 42 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   re 42 5 (CX30 ∷ []) ∷
   re 42 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   re 40 3 (CS13⁻ ∷ []) ∷
   re 42 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 41 q2 ∷
   re 42 3 (CX30 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q2 ∷
   re 46 3 (CS13⁻ ∷ []) ∷
   rw 45 q3 ∷
   rw 44 q4 ∷
   rw 43 q5 ∷
   re 43 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   re 43 5 (CX30 ∷ []) ∷
   re 43 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 45 q1 ∷
   re 41 3 (CS13⁻ ∷ []) ∷
   re 43 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 42 q2 ∷
   re 43 3 (CX30 ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q2 ∷
   re 47 3 (CS13⁻ ∷ []) ∷
   rw 46 q3 ∷
   rw 45 q4 ∷
   rw 44 q5 ∷
   re 44 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   re 44 5 (CX30 ∷ []) ∷
   re 44 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 46 q1 ∷
   re 42 3 (CS13⁻ ∷ []) ∷
   rw 43 q2 ∷
   re 42 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   re 41 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   re 40 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   re 39 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   rw 38 q10 ∷
   re 37 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 39 q1 ∷
   re 36 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 38 q1 ∷
   re 35 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 37 q1 ∷
   re 34 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
   re 33 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   re 32 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   rw 31 q11 ∷
   rw 30 q11 ∷
   rw 29 q11 ∷
   rw 28 q11 ∷
   rw 27 q11 ∷
   rw 26 q11 ∷
   rw 25 q12 ∷
   rw 24 q13 ∷
   rw 23 q11 ∷
   rw 22 q11 ∷
   rw 21 q11 ∷
   rw 20 q12 ∷
   rw 19 q13 ∷
   rw 18 q12 ∷
   rw 17 q13 ∷
   rw 18 q14 ∷
   rw 19 q2 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw 20 q2 ∷
   re 18 3 (CS13⁻ ∷ []) ∷
   rw 21 q2 ∷
   re 19 3 (CS13⁻ ∷ []) ∷
   rw 22 q2 ∷
   re 20 3 (CS13⁻ ∷ []) ∷
   rw 23 q2 ∷
   re 21 3 (CS13⁻ ∷ []) ∷
   rw 24 q2 ∷
   re 22 3 (CS13⁻ ∷ []) ∷
   rw 23 q15 ∷
   rw 26 q2 ∷
   re 24 3 (CK31⁻ ∷ []) ∷
   rw 27 q2 ∷
   re 25 3 (CS13⁻ ∷ []) ∷
   rw 28 q2 ∷
   re 26 3 (CS13⁻ ∷ []) ∷
   rw 29 q2 ∷
   re 27 3 (CS13⁻ ∷ []) ∷
   rw⁻ 28 q13 ∷
   rw⁻ 29 q12 ∷
   rw⁻ 30 q13 ∷
   rw⁻ 31 q12 ∷
   rw⁻ 32 q11 ∷
   rw⁻ 33 q11 ∷
   rw⁻ 34 q11 ∷
   rw⁻ 35 q13 ∷
   rw⁻ 36 q12 ∷
   rw⁻ 37 q11 ∷
   rw⁻ 38 q11 ∷
   rw⁻ 39 q11 ∷
   rw⁻ 40 q11 ∷
   rw⁻ 41 q11 ∷
   rw⁻ 42 q11 ∷
   rw 43 q1 ∷
   re 17 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q2 ∷
   re 17 3 (CX30 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q2 ∷
   re 21 3 (CS13⁻ ∷ []) ∷
   rw 20 q3 ∷
   rw 19 q4 ∷
   rw 18 q5 ∷
   re 18 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q1 ∷
   re 18 5 (CX30 ∷ []) ∷
   re 18 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 20 q1 ∷
   re 16 3 (CS13⁻ ∷ []) ∷
   re 18 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   re 18 3 (CX30 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   re 22 3 (CS13⁻ ∷ []) ∷
   rw 21 q3 ∷
   rw 20 q4 ∷
   rw 19 q5 ∷
   re 19 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q1 ∷
   re 19 5 (CX30 ∷ []) ∷
   re 19 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 21 q1 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   re 19 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q2 ∷
   re 19 3 (CX30 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   re 23 3 (CS13⁻ ∷ []) ∷
   rw 22 q3 ∷
   rw 21 q4 ∷
   rw 20 q5 ∷
   re 20 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q1 ∷
   re 20 5 (CX30 ∷ []) ∷
   re 20 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 22 q1 ∷
   re 18 3 (CS13⁻ ∷ []) ∷
   re 20 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   re 20 3 (CX30 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   re 24 3 (CS13⁻ ∷ []) ∷
   rw 23 q3 ∷
   rw 22 q4 ∷
   rw 21 q5 ∷
   re 21 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q1 ∷
   re 21 5 (CX30 ∷ []) ∷
   re 21 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   re 19 3 (CS13⁻ ∷ []) ∷
   re 21 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   re 21 3 (CX30 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   re 25 3 (CS13⁻ ∷ []) ∷
   rw 24 q3 ∷
   rw 23 q4 ∷
   rw 22 q5 ∷
   re 22 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q1 ∷
   re 22 5 (CX30 ∷ []) ∷
   re 22 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   re 20 3 (CS13⁻ ∷ []) ∷
   re 22 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q2 ∷
   re 22 3 (CX30 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   re 26 3 (CS13⁻ ∷ []) ∷
   rw 25 q3 ∷
   rw 24 q4 ∷
   rw 23 q5 ∷
   re 23 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 22 q1 ∷
   re 23 5 (CX30 ∷ []) ∷
   re 23 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 21 3 (CS13⁻ ∷ []) ∷
   rw 22 q6 ∷
   re 24 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 23 q2 ∷
   re 24 3 (CX30 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q2 ∷
   re 28 3 (CK31⁻ ∷ []) ∷
   rw 27 q7 ∷
   rw 26 q8 ∷
   rw 25 q9 ∷
   re 25 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   re 25 5 (CX30 ∷ []) ∷
   re 25 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   re 23 3 (CK31⁻ ∷ []) ∷
   re 25 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   re 25 3 (CX30 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q2 ∷
   re 29 3 (CS13⁻ ∷ []) ∷
   rw 28 q3 ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   re 26 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 26 5 (CX30 ∷ []) ∷
   re 26 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   re 24 3 (CS13⁻ ∷ []) ∷
   re 26 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   re 26 3 (CX30 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q2 ∷
   re 30 3 (CS13⁻ ∷ []) ∷
   rw 29 q3 ∷
   rw 28 q4 ∷
   rw 27 q5 ∷
   re 27 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   re 27 5 (CX30 ∷ []) ∷
   re 27 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   re 25 3 (CS13⁻ ∷ []) ∷
   re 27 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   re 27 3 (CX30 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q2 ∷
   re 31 3 (CS13⁻ ∷ []) ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   re 28 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   re 28 5 (CX30 ∷ []) ∷
   re 28 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   re 26 3 (CS13⁻ ∷ []) ∷
   rw 10 q16 ∷
   rw 49 q17 ∷
   rw 50 q18 ∷
   rw 51 q17 ∷
   rw 48 q17 ∷
   rw 49 q18 ∷
   rw 50 q17 ∷
   rw 47 q19 ∷
   rw 48 q20 ∷
   rw 49 q19 ∷
   rw 46 q17 ∷
   rw 47 q18 ∷
   rw 48 q17 ∷
   rw 45 q19 ∷
   rw 46 q20 ∷
   rw 47 q19 ∷
   rw 44 q19 ∷
   rw 45 q20 ∷
   rw 46 q19 ∷
   rw 47 q21 ∷
   rw⁻ 46 q22 ∷
   rw⁻ 45 q23 ∷
   rw⁻ 44 q22 ∷
   rw 43 q24 ∷
   rw 44 q25 ∷
   rw 43 q22 ∷
   rw 44 q23 ∷
   rw 45 q22 ∷
   rw 46 q26 ∷
   rw 47 q27 ∷
   rw 42 q19 ∷
   rw 43 q20 ∷
   rw 44 q19 ∷
   rw 41 q19 ∷
   rw 42 q20 ∷
   rw 43 q19 ∷
   rw 40 q19 ∷
   rw 41 q20 ∷
   rw 42 q19 ∷
   rw 39 q19 ∷
   rw 40 q20 ∷
   rw 41 q19 ∷
   rw 38 q19 ∷
   rw 39 q20 ∷
   rw 40 q19 ∷
   rw 37 q19 ∷
   rw 38 q20 ∷
   rw 39 q19 ∷
   rw 36 q28 ∷
   rw 37 q29 ∷
   rw 38 q28 ∷
   rw 35 q17 ∷
   rw 36 q18 ∷
   rw 37 q17 ∷
   rw 34 q19 ∷
   rw 35 q20 ∷
   rw 36 q19 ∷
   rw 33 q19 ∷
   rw 34 q20 ∷
   rw 35 q19 ∷
   rw 32 q19 ∷
   rw 33 q20 ∷
   rw 34 q19 ∷
   rw 31 q28 ∷
   rw 32 q29 ∷
   rw 33 q28 ∷
   rw 30 q17 ∷
   rw 31 q18 ∷
   rw 32 q17 ∷
   rw 29 q28 ∷
   rw 30 q29 ∷
   rw 31 q28 ∷
   rw 28 q17 ∷
   rw 29 q18 ∷
   rw 30 q17 ∷
   rw 31 q21 ∷
   rw⁻ 30 q22 ∷
   rw⁻ 29 q23 ∷
   rw⁻ 28 q22 ∷
   rw 27 q24 ∷
   rw 28 q25 ∷
   rw 27 q22 ∷
   rw 28 q23 ∷
   rw 29 q22 ∷
   rw 30 q26 ∷
   rw 31 q27 ∷
   rw 21 q30 ∷
   rw 24 q31 ∷
   rw 30 q32 ∷
   rw 68 q2 ∷
   re 67 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 69 q1 ∷
   re 66 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 68 q1 ∷
   re 65 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 67 q1 ∷
   re 64 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 66 q1 ∷
   rw 63 q13 ∷
   rw 62 q13 ∷
   rw 61 q11 ∷
   rw 60 q13 ∷
   rw 59 q11 ∷
   rw 58 q11 ∷
   rw 59 q33 ∷
   rw 60 q2 ∷
   re 58 3 (CS13⁻ ∷ []) ∷
   rw 61 q2 ∷
   re 59 3 (CK31⁻ ∷ []) ∷
   rw 62 q2 ∷
   re 60 3 (CS13⁻ ∷ []) ∷
   rw 63 q2 ∷
   re 61 3 (CS13⁻ ∷ []) ∷
   rw⁻ 62 q11 ∷
   rw⁻ 63 q11 ∷
   rw⁻ 64 q13 ∷
   rw⁻ 65 q11 ∷
   rw⁻ 66 q13 ∷
   rw⁻ 67 q13 ∷
   rw 68 q1 ∷
   re 58 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 57 q2 ∷
   re 58 3 (CX30 ∷ []) ∷
   re 58 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 64 q2 ∷
   re 62 3 (CS13⁻ ∷ []) ∷
   rw 61 q3 ∷
   rw 60 q4 ∷
   rw 59 q5 ∷
   re 59 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 58 q1 ∷
   re 59 5 (CX30 ∷ []) ∷
   re 59 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 61 q1 ∷
   re 57 3 (CS13⁻ ∷ []) ∷
   re 59 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 58 q2 ∷
   re 59 3 (CX30 ∷ []) ∷
   re 59 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 65 q2 ∷
   re 63 3 (CK31⁻ ∷ []) ∷
   rw 62 q7 ∷
   rw 61 q8 ∷
   rw 60 q9 ∷
   re 60 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 59 q1 ∷
   re 60 5 (CX30 ∷ []) ∷
   re 60 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 62 q1 ∷
   re 58 3 (CK31⁻ ∷ []) ∷
   re 60 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 59 q2 ∷
   re 60 3 (CX30 ∷ []) ∷
   re 60 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 66 q2 ∷
   re 64 3 (CS13⁻ ∷ []) ∷
   rw 63 q3 ∷
   rw 62 q4 ∷
   rw 61 q5 ∷
   re 61 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 60 q1 ∷
   re 61 5 (CX30 ∷ []) ∷
   re 61 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 63 q1 ∷
   re 59 3 (CS13⁻ ∷ []) ∷
   re 61 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 60 q2 ∷
   re 61 3 (CX30 ∷ []) ∷
   re 61 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 67 q2 ∷
   re 65 3 (CS13⁻ ∷ []) ∷
   rw 64 q3 ∷
   rw 63 q4 ∷
   rw 62 q5 ∷
   re 62 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 61 q1 ∷
   re 62 5 (CX30 ∷ []) ∷
   re 62 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 64 q1 ∷
   re 60 3 (CS13⁻ ∷ []) ∷
   rw 61 q2 ∷
   re 60 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 62 q1 ∷
   re 59 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 61 q1 ∷
   re 58 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 60 q1 ∷
   re 57 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 59 q1 ∷
   rw 56 q11 ∷
   rw 55 q11 ∷
   rw 54 q11 ∷
   rw 53 q11 ∷ []) Eq.refl

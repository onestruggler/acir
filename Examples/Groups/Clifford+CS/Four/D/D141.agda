{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D141 (W : Ws) where

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
  q1 = eqn (CK01 ∷ X2 ∷ []) (X2 ∷ CK01 ∷ []) (low-comm (CK₀₁) (X))
  q2 : Eqn
  q2 = eqn (CK01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CK01 ∷ []) (low-comm (CK₀₁) ((CS • CS • CS)))
  q3 : Eqn
  q3 = eqn (CS01 ∷ X2 ∷ []) (X2 ∷ CS01 ∷ []) (low-comm (CS) (X))
  q4 : Eqn
  q4 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q5 : Eqn
  q5 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q6 : Eqn
  q6 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q8 : Eqn
  q8 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q9 : Eqn
  q9 = eqn (CX21 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (X2 ∷ CS23⁻ ∷ X2 ∷ CX21 ∷ []) (wn 686 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q12 : Eqn
  q12 = eqn (S0 ∷ X2 ∷ []) (X2 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑)))
  q13 : Eqn
  q13 = eqn (S0 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S0 ∷ []) (low₁-comm (S) (((CS • CS • CS) ↑)))
  q14 : Eqn
  q14 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (X2 ∷ CS23⁻ ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (wn 687 W)
  q15 : Eqn
  q15 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q16 : Eqn
  q16 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q17 : Eqn
  q17 = eqn (CK01 ∷ Sw23 ∷ []) (Sw23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (Swap))
  q18 : Eqn
  q18 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q19 : Eqn
  q19 = eqn (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) (wn 534 W)
  q20 : Eqn
  q20 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q21 : Eqn
  q21 = eqn (CX10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((CS • CS • CS)))
  q22 : Eqn
  q22 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q23 : Eqn
  q23 = eqn (Sw12 ∷ CK31⁻ ∷ []) (CK32⁻ ∷ Sw12 ∷ []) (wn 360 W)
  q24 : Eqn
  q24 = eqn (CX10 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((S ↑ • CK₁₀)))
  q25 : Eqn
  q25 = eqn (Sw12 ∷ CK32⁻ ∷ []) (CK31⁻ ∷ Sw12 ∷ []) (wn 362 W)
  q26 : Eqn
  q26 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q27 : Eqn
  q27 = eqn (CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (wn 535 W)
  q28 : Eqn
  q28 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (wn 688 W)
  q29 : Eqn
  q29 = eqn (CK01 ∷ CX23 ∷ []) (CX23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₀₁))
  q30 : Eqn
  q30 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q31 : Eqn
  q31 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q32 : Eqn
  q32 = eqn (CX21 ∷ X2 ∷ CX23 ∷ X2 ∷ []) (X2 ∷ CX23 ∷ X2 ∷ CX21 ∷ []) (wn 612 W)
  q33 : Eqn
  q33 = eqn (S0 ∷ CX23 ∷ []) (CX23 ∷ S0 ∷ []) (low₁-comm (S) ((CX₀₁ ↑)))
  q34 : Eqn
  q34 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X2 ∷ CX23 ∷ X2 ∷ []) (X2 ∷ CX23 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (wn 613 W)
  q35 : Eqn
  q35 = eqn (S3⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S2⁻ ∷ []) (wn 689 W)
  q36 : Eqn
  q36 = eqn (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) (wn 539 W)
  q37 : Eqn
  q37 = eqn (Sw23 ∷ S2⁻ ∷ []) (S3⁻ ∷ Sw23 ∷ []) (wn 153 W)

-- Bar(['S', 'S', 'K', 'S', 'K', 'K'];2,0->1) passes white iX via V2 conjugates 3 part0: 500 steps
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part0 : ⟪ (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part0 = derive (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS23⁻ ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ [])
  (rw 28 q1 ∷
   rw 29 q2 ∷
   rw 30 q1 ∷
   rw 27 q1 ∷
   rw 28 q2 ∷
   rw 29 q1 ∷
   rw 26 q3 ∷
   rw 27 q4 ∷
   rw 28 q3 ∷
   rw 25 q1 ∷
   rw 26 q2 ∷
   rw 27 q1 ∷
   rw 24 q3 ∷
   rw 25 q4 ∷
   rw 26 q3 ∷
   rw 23 q3 ∷
   rw 24 q4 ∷
   rw 25 q3 ∷
   rw 26 q5 ∷
   rw⁻ 25 q6 ∷
   rw⁻ 24 q7 ∷
   rw⁻ 23 q6 ∷
   rw 22 q8 ∷
   rw 23 q9 ∷
   rw 22 q6 ∷
   rw 23 q7 ∷
   rw 24 q6 ∷
   rw 25 q10 ∷
   rw 26 q11 ∷
   rw 21 q3 ∷
   rw 22 q4 ∷
   rw 23 q3 ∷
   rw 20 q3 ∷
   rw 21 q4 ∷
   rw 22 q3 ∷
   rw 19 q3 ∷
   rw 20 q4 ∷
   rw 21 q3 ∷
   rw 18 q3 ∷
   rw 19 q4 ∷
   rw 20 q3 ∷
   rw 17 q3 ∷
   rw 18 q4 ∷
   rw 19 q3 ∷
   rw 16 q3 ∷
   rw 17 q4 ∷
   rw 18 q3 ∷
   rw 15 q12 ∷
   rw 16 q13 ∷
   rw 17 q12 ∷
   rw 14 q1 ∷
   rw 15 q2 ∷
   rw 16 q1 ∷
   rw 13 q3 ∷
   rw 14 q4 ∷
   rw 15 q3 ∷
   rw 12 q3 ∷
   rw 13 q4 ∷
   rw 14 q3 ∷
   rw 11 q3 ∷
   rw 12 q4 ∷
   rw 13 q3 ∷
   rw 10 q12 ∷
   rw 11 q13 ∷
   rw 12 q12 ∷
   rw 9 q1 ∷
   rw 10 q2 ∷
   rw 11 q1 ∷
   rw 8 q12 ∷
   rw 9 q13 ∷
   rw 10 q12 ∷
   rw 7 q1 ∷
   rw 8 q2 ∷
   rw 9 q1 ∷
   rw 10 q5 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 8 q7 ∷
   rw⁻ 7 q6 ∷
   rw 6 q8 ∷
   rw 7 q9 ∷
   rw 6 q6 ∷
   rw 7 q7 ∷
   rw 8 q6 ∷
   rw 9 q10 ∷
   rw 10 q11 ∷
   rw 0 q14 ∷
   rw 36 q15 ∷
   re 35 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 37 q16 ∷
   re 34 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 36 q16 ∷
   re 33 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 35 q16 ∷
   re 32 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 34 q16 ∷
   rw 31 q17 ∷
   rw 30 q17 ∷
   rw 29 q18 ∷
   rw 28 q17 ∷
   rw 27 q18 ∷
   rw 26 q18 ∷
   rw 27 q19 ∷
   rw 28 q15 ∷
   re 26 3 (CS13⁻ ∷ []) ∷
   rw 29 q15 ∷
   re 27 3 (CK31⁻ ∷ []) ∷
   rw 30 q15 ∷
   re 28 3 (CS13⁻ ∷ []) ∷
   rw 31 q15 ∷
   re 29 3 (CS13⁻ ∷ []) ∷
   rw⁻ 30 q18 ∷
   rw⁻ 31 q18 ∷
   rw⁻ 32 q17 ∷
   rw⁻ 33 q18 ∷
   rw⁻ 34 q17 ∷
   rw⁻ 35 q17 ∷
   rw 36 q16 ∷
   re 26 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q15 ∷
   re 26 3 (CX30 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q15 ∷
   re 30 3 (CS13⁻ ∷ []) ∷
   rw 29 q20 ∷
   rw 28 q21 ∷
   rw 27 q22 ∷
   re 27 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q16 ∷
   re 27 5 (CX30 ∷ []) ∷
   re 27 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 29 q16 ∷
   re 25 3 (CS13⁻ ∷ []) ∷
   re 27 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q15 ∷
   re 27 3 (CX30 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q15 ∷
   re 31 3 (CK31⁻ ∷ []) ∷
   rw 30 q23 ∷
   rw 29 q24 ∷
   rw 28 q25 ∷
   re 28 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q16 ∷
   re 28 5 (CX30 ∷ []) ∷
   re 28 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 30 q16 ∷
   re 26 3 (CK31⁻ ∷ []) ∷
   re 28 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q15 ∷
   re 28 3 (CX30 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q15 ∷
   re 32 3 (CS13⁻ ∷ []) ∷
   rw 31 q20 ∷
   rw 30 q21 ∷
   rw 29 q22 ∷
   re 29 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 28 q16 ∷
   re 29 5 (CX30 ∷ []) ∷
   re 29 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 31 q16 ∷
   re 27 3 (CS13⁻ ∷ []) ∷
   re 29 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 28 q15 ∷
   re 29 3 (CX30 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q15 ∷
   re 33 3 (CS13⁻ ∷ []) ∷
   rw 32 q20 ∷
   rw 31 q21 ∷
   rw 30 q22 ∷
   re 30 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 29 q16 ∷
   re 30 5 (CX30 ∷ []) ∷
   re 30 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 32 q16 ∷
   re 28 3 (CS13⁻ ∷ []) ∷
   rw 29 q15 ∷
   re 28 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 30 q16 ∷
   re 27 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 29 q16 ∷
   re 26 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 28 q16 ∷
   re 25 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q16 ∷
   rw 24 q18 ∷
   rw 23 q18 ∷
   rw 22 q18 ∷
   rw 21 q18 ∷
   rw 20 q18 ∷
   rw 19 q18 ∷
   rw 18 q26 ∷
   rw 17 q17 ∷
   rw 16 q18 ∷
   rw 15 q18 ∷
   rw 14 q18 ∷
   rw 13 q26 ∷
   rw 12 q17 ∷
   rw 11 q26 ∷
   rw 10 q17 ∷
   rw 11 q27 ∷
   rw 12 q15 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw 13 q15 ∷
   re 11 3 (CK31⁻ ∷ []) ∷
   rw 14 q15 ∷
   re 12 3 (CS13⁻ ∷ []) ∷
   rw 15 q15 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw⁻ 14 q17 ∷
   rw⁻ 15 q26 ∷
   rw⁻ 16 q17 ∷
   rw⁻ 17 q26 ∷
   rw⁻ 18 q18 ∷
   rw⁻ 19 q18 ∷
   rw⁻ 20 q18 ∷
   rw⁻ 21 q17 ∷
   rw⁻ 22 q26 ∷
   rw⁻ 23 q18 ∷
   rw⁻ 24 q18 ∷
   rw⁻ 25 q18 ∷
   rw⁻ 26 q18 ∷
   rw⁻ 27 q18 ∷
   rw⁻ 28 q18 ∷
   rw 29 q16 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q15 ∷
   re 10 3 (CX30 ∷ []) ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q15 ∷
   re 14 3 (CS13⁻ ∷ []) ∷
   rw 13 q20 ∷
   rw 12 q21 ∷
   rw 11 q22 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q16 ∷
   re 11 5 (CX30 ∷ []) ∷
   re 11 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 13 q16 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   re 11 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q15 ∷
   re 11 3 (CX30 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q15 ∷
   re 15 3 (CK31⁻ ∷ []) ∷
   rw 14 q23 ∷
   rw 13 q24 ∷
   rw 12 q25 ∷
   re 12 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q16 ∷
   re 12 5 (CX30 ∷ []) ∷
   re 12 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 14 q16 ∷
   re 10 3 (CK31⁻ ∷ []) ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q15 ∷
   re 12 3 (CX30 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q15 ∷
   re 16 3 (CS13⁻ ∷ []) ∷
   rw 15 q20 ∷
   rw 14 q21 ∷
   rw 13 q22 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q16 ∷
   re 13 5 (CX30 ∷ []) ∷
   re 13 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 15 q16 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q15 ∷
   re 13 3 (CX30 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q15 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw 16 q20 ∷
   rw 15 q21 ∷
   rw 14 q22 ∷
   re 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q16 ∷
   re 14 5 (CX30 ∷ []) ∷
   re 14 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 16 q16 ∷
   re 12 3 (CS13⁻ ∷ []) ∷
   rw 3 q28 ∷
   rw 35 q1 ∷
   rw 36 q29 ∷
   rw 37 q1 ∷
   rw 34 q1 ∷
   rw 35 q29 ∷
   rw 36 q1 ∷
   rw 33 q3 ∷
   rw 34 q30 ∷
   rw 35 q3 ∷
   rw 32 q1 ∷
   rw 33 q29 ∷
   rw 34 q1 ∷
   rw 31 q3 ∷
   rw 32 q30 ∷
   rw 33 q3 ∷
   rw 30 q3 ∷
   rw 31 q30 ∷
   rw 32 q3 ∷
   rw 33 q5 ∷
   rw⁻ 32 q6 ∷
   rw⁻ 31 q31 ∷
   rw⁻ 30 q6 ∷
   rw 29 q8 ∷
   rw 30 q32 ∷
   rw 29 q6 ∷
   rw 30 q31 ∷
   rw 31 q6 ∷
   rw 32 q10 ∷
   rw 33 q11 ∷
   rw 28 q3 ∷
   rw 29 q30 ∷
   rw 30 q3 ∷
   rw 27 q3 ∷
   rw 28 q30 ∷
   rw 29 q3 ∷
   rw 26 q3 ∷
   rw 27 q30 ∷
   rw 28 q3 ∷
   rw 25 q3 ∷
   rw 26 q30 ∷
   rw 27 q3 ∷
   rw 24 q3 ∷
   rw 25 q30 ∷
   rw 26 q3 ∷
   rw 23 q3 ∷
   rw 24 q30 ∷
   rw 25 q3 ∷
   rw 22 q12 ∷
   rw 23 q33 ∷
   rw 24 q12 ∷
   rw 21 q1 ∷
   rw 22 q29 ∷
   rw 23 q1 ∷
   rw 20 q3 ∷
   rw 21 q30 ∷
   rw 22 q3 ∷
   rw 19 q3 ∷
   rw 20 q30 ∷
   rw 21 q3 ∷
   rw 18 q3 ∷
   rw 19 q30 ∷
   rw 20 q3 ∷
   rw 17 q12 ∷
   rw 18 q33 ∷
   rw 19 q12 ∷
   rw 16 q1 ∷
   rw 17 q29 ∷
   rw 18 q1 ∷
   rw 15 q12 ∷
   rw 16 q33 ∷
   rw 17 q12 ∷
   rw 14 q1 ∷
   rw 15 q29 ∷
   rw 16 q1 ∷
   rw 17 q5 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 15 q31 ∷
   rw⁻ 14 q6 ∷
   rw 13 q8 ∷
   rw 14 q32 ∷
   rw 13 q6 ∷
   rw 14 q31 ∷
   rw 15 q6 ∷
   rw 16 q10 ∷
   rw 17 q11 ∷
   rw 7 q34 ∷
   rw 50 q15 ∷
   re 49 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 51 q16 ∷
   re 48 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 50 q16 ∷
   re 47 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 49 q16 ∷
   re 46 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 48 q16 ∷
   rw 45 q35 ∷
   re 44 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 46 q16 ∷
   re 43 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 45 q16 ∷
   re 42 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 44 q16 ∷
   re 41 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 43 q16 ∷
   re 40 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 42 q16 ∷
   re 39 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 41 q16 ∷
   rw 38 q17 ∷
   rw 37 q17 ∷
   rw 36 q18 ∷
   rw 35 q17 ∷
   rw 34 q18 ∷
   rw 33 q18 ∷
   rw 34 q36 ∷
   rw 35 q15 ∷
   re 33 3 (CS13⁻ ∷ []) ∷
   rw 36 q15 ∷
   re 34 3 (CS13⁻ ∷ []) ∷
   rw 37 q15 ∷
   re 35 3 (CS13⁻ ∷ []) ∷
   rw 38 q15 ∷
   re 36 3 (CS13⁻ ∷ []) ∷
   rw 39 q15 ∷
   re 37 3 (CS13⁻ ∷ []) ∷
   rw 40 q15 ∷
   re 38 3 (CS13⁻ ∷ []) ∷
   rw 39 q37 ∷
   rw 42 q15 ∷
   re 40 3 (CK31⁻ ∷ []) ∷
   rw 43 q15 ∷
   re 41 3 (CS13⁻ ∷ []) ∷
   rw 44 q15 ∷
   re 42 3 (CS13⁻ ∷ []) ∷
   rw 45 q15 ∷
   re 43 3 (CS13⁻ ∷ []) ∷
   rw⁻ 44 q18 ∷
   rw⁻ 45 q18 ∷
   rw⁻ 46 q17 ∷
   rw⁻ 47 q18 ∷
   rw⁻ 48 q17 ∷
   rw⁻ 49 q17 ∷
   rw 50 q16 ∷
   re 33 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 32 q15 ∷
   re 33 3 (CX30 ∷ []) ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q15 ∷
   re 37 3 (CS13⁻ ∷ []) ∷
   rw 36 q20 ∷
   rw 35 q21 ∷
   rw 34 q22 ∷
   re 34 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 33 q16 ∷
   re 34 5 (CX30 ∷ []) ∷
   re 34 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 36 q16 ∷
   re 32 3 (CS13⁻ ∷ []) ∷
   re 34 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 33 q15 ∷
   re 34 3 (CX30 ∷ []) ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q15 ∷
   re 38 3 (CS13⁻ ∷ []) ∷
   rw 37 q20 ∷
   rw 36 q21 ∷
   rw 35 q22 ∷
   re 35 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 34 q16 ∷
   re 35 5 (CX30 ∷ []) ∷
   re 35 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 37 q16 ∷
   re 33 3 (CS13⁻ ∷ []) ∷
   re 35 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 34 q15 ∷
   re 35 3 (CX30 ∷ []) ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q15 ∷
   re 39 3 (CS13⁻ ∷ []) ∷
   rw 38 q20 ∷
   rw 37 q21 ∷
   rw 36 q22 ∷
   re 36 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 35 q16 ∷
   re 36 5 (CX30 ∷ []) ∷
   re 36 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 38 q16 ∷
   re 34 3 (CS13⁻ ∷ []) ∷
   re 36 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 35 q15 ∷
   re 36 3 (CX30 ∷ []) ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q15 ∷
   re 40 3 (CS13⁻ ∷ []) ∷
   rw 39 q20 ∷
   rw 38 q21 ∷
   rw 37 q22 ∷
   re 37 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 36 q16 ∷
   re 37 5 (CX30 ∷ []) ∷
   re 37 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 39 q16 ∷
   re 35 3 (CS13⁻ ∷ []) ∷
   re 37 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 36 q15 ∷
   re 37 3 (CX30 ∷ []) ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q15 ∷
   re 41 3 (CS13⁻ ∷ []) ∷
   rw 40 q20 ∷
   rw 39 q21 ∷
   rw 38 q22 ∷
   re 38 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷ []) Eq.refl

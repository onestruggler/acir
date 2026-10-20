{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D049 (W : Ws) where

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
  q1 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q2 : Eqn
  q2 = eqn (CK01 ∷ X3 ∷ []) (X3 ∷ CK01 ∷ []) (low-comm (CK₀₁) ((X ↑)))
  q3 : Eqn
  q3 = eqn (CK01 ∷ CX32 ∷ []) (CX32 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₁₀))
  q4 : Eqn
  q4 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q5 : Eqn
  q5 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q6 : Eqn
  q6 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q8 : Eqn
  q8 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q9 : Eqn
  q9 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q10 : Eqn
  q10 = eqn (CX31 ∷ X3 ∷ CX32 ∷ X3 ∷ []) (X3 ∷ CX32 ∷ X3 ∷ CX31 ∷ []) (wn 537 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q13 : Eqn
  q13 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q14 : Eqn
  q14 = eqn (S0 ∷ CX32 ∷ []) (CX32 ∷ S0 ∷ []) (low₁-comm (S) ((CX₁₀ ↑)))
  q15 : Eqn
  q15 = eqn (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X3 ∷ CX32 ∷ X3 ∷ []) (X3 ∷ CX32 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) (wn 538 W)
  q16 : Eqn
  q16 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q17 : Eqn
  q17 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q18 : Eqn
  q18 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q19 : Eqn
  q19 = eqn (CK01 ∷ Sw23 ∷ []) (Sw23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (Swap))
  q20 : Eqn
  q20 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q21 : Eqn
  q21 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q22 : Eqn
  q22 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) (wn 543 W)
  q23 : Eqn
  q23 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q24 : Eqn
  q24 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) (wn 544 W)
  q25 : Eqn
  q25 = eqn (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) (wn 534 W)
  q26 : Eqn
  q26 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q27 : Eqn
  q27 = eqn (CX10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((CS • CS • CS)))
  q28 : Eqn
  q28 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q29 : Eqn
  q29 = eqn (Sw12 ∷ CK31⁻ ∷ []) (CK32⁻ ∷ Sw12 ∷ []) (wn 360 W)
  q30 : Eqn
  q30 = eqn (CX10 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((S ↑ • CK₁₀)))
  q31 : Eqn
  q31 = eqn (Sw12 ∷ CK32⁻ ∷ []) (CK31⁻ ∷ Sw12 ∷ []) (wn 362 W)
  q32 : Eqn
  q32 = eqn (CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (wn 535 W)
  q33 : Eqn
  q33 = eqn (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) (wn 536 W)
  q34 : Eqn
  q34 = eqn (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) (wn 539 W)

-- Bar(['S', 'S', 'K', 'S', 'K', 'K'];3,0->1) passes white iX via V2 conjugates 2 part1: 500 steps
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-white-iX-via-V2-conjugates-2-part1 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ X3 ∷ CX32 ∷ CS01 ∷ X3 ∷ CK01 ∷ CK01 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-white-iX-via-V2-conjugates-2-part1 = derive (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ X3 ∷ CX32 ∷ CS01 ∷ X3 ∷ CK01 ∷ CK01 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ [])
  (rw 49 q1 ∷
   rw 46 q2 ∷
   rw 47 q3 ∷
   rw 48 q2 ∷
   rw 45 q1 ∷
   rw 46 q4 ∷
   rw 47 q1 ∷
   rw 44 q1 ∷
   rw 45 q4 ∷
   rw 46 q1 ∷
   rw 47 q5 ∷
   rw⁻ 46 q6 ∷
   rw⁻ 45 q7 ∷
   rw⁻ 44 q6 ∷
   re 43 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q8 ∷
   rw 44 q9 ∷
   rw⁻ 43 q8 ∷
   re 44 3 (CX31 ∷ []) ∷
   rw 44 q10 ∷
   rw 43 q6 ∷
   rw 44 q7 ∷
   rw 45 q6 ∷
   re 47 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 46 q8 ∷
   rw 47 q11 ∷
   rw 48 q8 ∷
   re 46 3 (CX30 ∷ []) ∷
   rw 47 q12 ∷
   rw 42 q1 ∷
   rw 43 q4 ∷
   rw 44 q1 ∷
   rw 41 q1 ∷
   rw 42 q4 ∷
   rw 43 q1 ∷
   rw 40 q1 ∷
   rw 41 q4 ∷
   rw 42 q1 ∷
   rw 39 q1 ∷
   rw 40 q4 ∷
   rw 41 q1 ∷
   rw 38 q1 ∷
   rw 39 q4 ∷
   rw 40 q1 ∷
   rw 37 q1 ∷
   rw 38 q4 ∷
   rw 39 q1 ∷
   rw 36 q13 ∷
   rw 37 q14 ∷
   rw 38 q13 ∷
   rw 35 q2 ∷
   rw 36 q3 ∷
   rw 37 q2 ∷
   rw 34 q1 ∷
   rw 35 q4 ∷
   rw 36 q1 ∷
   rw 33 q1 ∷
   rw 34 q4 ∷
   rw 35 q1 ∷
   rw 32 q1 ∷
   rw 33 q4 ∷
   rw 34 q1 ∷
   rw 31 q13 ∷
   rw 32 q14 ∷
   rw 33 q13 ∷
   rw 30 q2 ∷
   rw 31 q3 ∷
   rw 32 q2 ∷
   rw 29 q13 ∷
   rw 30 q14 ∷
   rw 31 q13 ∷
   rw 28 q2 ∷
   rw 29 q3 ∷
   rw 30 q2 ∷
   rw 31 q5 ∷
   rw⁻ 30 q6 ∷
   rw⁻ 29 q7 ∷
   rw⁻ 28 q6 ∷
   re 27 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q8 ∷
   rw 28 q9 ∷
   rw⁻ 27 q8 ∷
   re 28 3 (CX31 ∷ []) ∷
   rw 28 q10 ∷
   rw 27 q6 ∷
   rw 28 q7 ∷
   rw 29 q6 ∷
   re 31 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 30 q8 ∷
   rw 31 q11 ∷
   rw 32 q8 ∷
   re 30 3 (CX30 ∷ []) ∷
   rw 31 q12 ∷
   rw 21 q15 ∷
   rw 59 q16 ∷
   rw 58 q17 ∷
   re 57 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 59 q18 ∷
   re 56 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 58 q18 ∷
   re 55 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 57 q18 ∷
   re 54 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 56 q18 ∷
   rw 53 q17 ∷
   rw 52 q19 ∷
   rw 51 q19 ∷
   rw 50 q20 ∷
   rw 49 q19 ∷
   rw 48 q20 ∷
   rw 47 q20 ∷
   re 46 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 48 q18 ∷
   rw 45 q20 ∷
   rw 44 q20 ∷
   rw 43 q20 ∷
   rw 42 q20 ∷
   rw 41 q20 ∷
   rw 40 q20 ∷
   rw 39 q21 ∷
   rw 38 q19 ∷
   rw 37 q20 ∷
   rw 36 q20 ∷
   rw 35 q20 ∷
   rw 34 q21 ∷
   rw 33 q19 ∷
   rw 32 q21 ∷
   rw 31 q19 ∷
   re 30 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 32 q18 ∷
   re 29 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 31 q18 ∷
   re 28 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 30 q18 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q18 ∷
   re 26 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 28 q18 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q18 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q18 ∷
   rw 25 q22 ∷
   rw 24 q23 ∷
   rw 27 q16 ∷
   re 25 3 (CS13⁻ ∷ []) ∷
   rw 28 q16 ∷
   re 26 3 (CK31⁻ ∷ []) ∷
   rw 29 q16 ∷
   re 27 3 (CS13⁻ ∷ []) ∷
   rw 30 q16 ∷
   re 28 3 (CS13⁻ ∷ []) ∷
   rw 29 q23 ∷
   rw 32 q16 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw 33 q16 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 34 q16 ∷
   re 32 3 (CK31 ∷ []) ∷
   rw 35 q16 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw 36 q16 ∷
   re 34 3 (CK31 ∷ []) ∷
   rw 37 q16 ∷
   re 35 3 (CK31 ∷ []) ∷
   rw 38 q16 ∷
   re 36 3 (CX30 ∷ []) ∷
   rw⁻ 37 q19 ∷
   rw⁻ 38 q21 ∷
   rw⁻ 39 q19 ∷
   rw⁻ 40 q21 ∷
   rw⁻ 41 q20 ∷
   rw⁻ 42 q20 ∷
   rw⁻ 43 q20 ∷
   rw⁻ 44 q19 ∷
   rw⁻ 45 q21 ∷
   rw⁻ 46 q20 ∷
   rw⁻ 47 q20 ∷
   rw⁻ 48 q20 ∷
   rw⁻ 49 q20 ∷
   rw⁻ 50 q20 ∷
   rw⁻ 51 q20 ∷
   rw 54 q16 ∷
   re 52 3 (CX30 ∷ []) ∷
   rw⁻ 53 q20 ∷
   rw⁻ 54 q20 ∷
   rw⁻ 55 q19 ∷
   rw⁻ 56 q20 ∷
   rw⁻ 57 q19 ∷
   rw⁻ 58 q19 ∷
   rw 59 q18 ∷
   rw 64 q16 ∷
   rw 63 q17 ∷
   re 62 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 64 q18 ∷
   re 61 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 63 q18 ∷
   re 60 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 62 q18 ∷
   rw 59 q17 ∷
   rw 58 q19 ∷
   rw 57 q19 ∷
   rw 56 q20 ∷
   rw 55 q19 ∷
   rw 54 q20 ∷
   rw 53 q20 ∷
   re 52 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 54 q18 ∷
   rw 51 q20 ∷
   rw 50 q20 ∷
   rw 49 q20 ∷
   rw 48 q20 ∷
   rw 47 q20 ∷
   rw 46 q20 ∷
   rw 45 q21 ∷
   rw 44 q19 ∷
   rw 43 q20 ∷
   rw 42 q20 ∷
   rw 41 q20 ∷
   rw 40 q21 ∷
   rw 39 q19 ∷
   rw 38 q21 ∷
   rw 37 q19 ∷
   re 36 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 38 q18 ∷
   re 35 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 37 q18 ∷
   re 34 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 36 q18 ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q18 ∷
   re 32 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 34 q18 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q18 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q18 ∷
   rw 31 q24 ∷
   rw 30 q23 ∷
   rw 33 q16 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 34 q16 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw 35 q16 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw 34 q23 ∷
   rw 37 q16 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw 38 q16 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 39 q16 ∷
   re 37 3 (CK31 ∷ []) ∷
   rw 40 q16 ∷
   re 38 3 (CS13 ∷ []) ∷
   rw 41 q16 ∷
   re 39 3 (CK31 ∷ []) ∷
   rw 42 q16 ∷
   re 40 3 (CK31 ∷ []) ∷
   rw 43 q16 ∷
   re 41 3 (CX30 ∷ []) ∷
   rw⁻ 42 q19 ∷
   rw⁻ 43 q21 ∷
   rw⁻ 44 q19 ∷
   rw⁻ 45 q21 ∷
   rw⁻ 46 q20 ∷
   rw⁻ 47 q20 ∷
   rw⁻ 48 q20 ∷
   rw⁻ 49 q19 ∷
   rw⁻ 50 q21 ∷
   rw⁻ 51 q20 ∷
   rw⁻ 52 q20 ∷
   rw⁻ 53 q20 ∷
   rw⁻ 54 q20 ∷
   rw⁻ 55 q20 ∷
   rw⁻ 56 q20 ∷
   rw 59 q16 ∷
   re 57 3 (CX30 ∷ []) ∷
   rw⁻ 58 q20 ∷
   rw⁻ 59 q20 ∷
   rw⁻ 60 q19 ∷
   rw⁻ 61 q20 ∷
   rw⁻ 62 q19 ∷
   rw⁻ 63 q19 ∷
   rw 64 q18 ∷
   rw 58 q25 ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 63 q16 ∷
   re 61 3 (CS13⁻ ∷ []) ∷
   rw 60 q26 ∷
   rw 59 q27 ∷
   rw 58 q28 ∷
   re 58 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 57 q18 ∷
   re 58 5 (CX30 ∷ []) ∷
   re 58 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 64 q16 ∷
   re 62 3 (CK31⁻ ∷ []) ∷
   rw 61 q29 ∷
   rw 60 q30 ∷
   rw 59 q31 ∷
   re 59 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 58 q18 ∷
   re 59 5 (CX30 ∷ []) ∷
   re 59 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 65 q16 ∷
   re 63 3 (CS13⁻ ∷ []) ∷
   rw 62 q26 ∷
   rw 61 q27 ∷
   rw 60 q28 ∷
   re 60 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 59 q18 ∷
   re 60 5 (CX30 ∷ []) ∷
   re 60 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 66 q16 ∷
   re 64 3 (CS13⁻ ∷ []) ∷
   rw 63 q26 ∷
   rw 62 q27 ∷
   rw 61 q28 ∷
   re 61 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 60 q18 ∷
   re 61 5 (CX30 ∷ []) ∷
   rw 42 q32 ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q16 ∷
   re 45 3 (CS13⁻ ∷ []) ∷
   rw 44 q26 ∷
   rw 43 q27 ∷
   rw 42 q28 ∷
   re 42 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 41 q18 ∷
   re 42 5 (CX30 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q16 ∷
   re 46 3 (CK31⁻ ∷ []) ∷
   rw 45 q29 ∷
   rw 44 q30 ∷
   rw 43 q31 ∷
   re 43 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 42 q18 ∷
   re 43 5 (CX30 ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q16 ∷
   re 47 3 (CS13⁻ ∷ []) ∷
   rw 46 q26 ∷
   rw 45 q27 ∷
   rw 44 q28 ∷
   re 44 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 43 q18 ∷
   re 44 5 (CX30 ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q16 ∷
   re 48 3 (CS13⁻ ∷ []) ∷
   rw 47 q26 ∷
   rw 46 q27 ∷
   rw 45 q28 ∷
   re 45 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 44 q18 ∷
   re 45 5 (CX30 ∷ []) ∷
   rw 35 q33 ∷
   rw 67 q2 ∷
   rw 68 q3 ∷
   rw 69 q2 ∷
   rw 66 q2 ∷
   rw 67 q3 ∷
   rw 68 q2 ∷
   rw 65 q1 ∷
   rw 66 q4 ∷
   rw 67 q1 ∷
   rw 64 q2 ∷
   rw 65 q3 ∷
   rw 66 q2 ∷
   rw 63 q1 ∷
   rw 64 q4 ∷
   rw 65 q1 ∷
   rw 62 q1 ∷
   rw 63 q4 ∷
   rw 64 q1 ∷
   rw 65 q5 ∷
   rw⁻ 64 q6 ∷
   rw⁻ 63 q7 ∷
   rw⁻ 62 q6 ∷
   re 61 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 63 q8 ∷
   rw 62 q9 ∷
   rw⁻ 61 q8 ∷
   re 62 3 (CX31 ∷ []) ∷
   rw 62 q10 ∷
   rw 61 q6 ∷
   rw 62 q7 ∷
   rw 63 q6 ∷
   re 65 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 64 q8 ∷
   rw 65 q11 ∷
   rw 66 q8 ∷
   re 64 3 (CX30 ∷ []) ∷
   rw 65 q12 ∷
   rw 60 q1 ∷
   rw 61 q4 ∷
   rw 62 q1 ∷
   rw 59 q1 ∷
   rw 60 q4 ∷
   rw 61 q1 ∷
   rw 58 q1 ∷
   rw 59 q4 ∷
   rw 60 q1 ∷
   rw 57 q1 ∷
   rw 58 q4 ∷
   rw 59 q1 ∷
   rw 56 q1 ∷
   rw 57 q4 ∷
   rw 58 q1 ∷
   rw 55 q1 ∷
   rw 56 q4 ∷
   rw 57 q1 ∷
   rw 54 q13 ∷
   rw 55 q14 ∷
   rw 56 q13 ∷
   rw 53 q2 ∷
   rw 54 q3 ∷
   rw 55 q2 ∷
   rw 52 q1 ∷
   rw 53 q4 ∷
   rw 54 q1 ∷
   rw 51 q1 ∷
   rw 52 q4 ∷
   rw 53 q1 ∷
   rw 50 q1 ∷
   rw 51 q4 ∷
   rw 52 q1 ∷
   rw 49 q13 ∷
   rw 50 q14 ∷
   rw 51 q13 ∷
   rw 48 q2 ∷
   rw 49 q3 ∷
   rw 50 q2 ∷
   rw 47 q13 ∷
   rw 48 q14 ∷
   rw 49 q13 ∷
   rw 46 q2 ∷
   rw 47 q3 ∷
   rw 48 q2 ∷
   rw 49 q5 ∷
   rw⁻ 48 q6 ∷
   rw⁻ 47 q7 ∷
   rw⁻ 46 q6 ∷
   re 45 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q8 ∷
   rw 46 q9 ∷
   rw⁻ 45 q8 ∷
   re 46 3 (CX31 ∷ []) ∷
   rw 46 q10 ∷
   rw 45 q6 ∷
   rw 46 q7 ∷
   rw 47 q6 ∷
   re 49 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 48 q8 ∷
   rw 49 q11 ∷
   rw 50 q8 ∷
   re 48 3 (CX30 ∷ []) ∷
   rw 49 q12 ∷
   rw 39 q15 ∷
   rw 65 q34 ∷
   re 64 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 70 q16 ∷
   re 68 3 (CS13⁻ ∷ []) ∷
   rw 67 q26 ∷
   rw 66 q27 ∷
   rw 65 q28 ∷
   re 65 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 64 q18 ∷
   re 65 5 (CX30 ∷ []) ∷
   re 65 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q16 ∷
   re 69 3 (CS13⁻ ∷ []) ∷
   rw 68 q26 ∷
   rw 67 q27 ∷
   rw 66 q28 ∷
   re 66 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 65 q18 ∷
   re 66 5 (CX30 ∷ []) ∷
   re 66 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 72 q16 ∷
   re 70 3 (CS13⁻ ∷ []) ∷
   rw 69 q26 ∷
   rw 68 q27 ∷
   rw 67 q28 ∷
   re 67 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 66 q18 ∷
   re 67 5 (CX30 ∷ []) ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q16 ∷
   re 71 3 (CS13⁻ ∷ []) ∷
   rw 70 q26 ∷
   rw 69 q27 ∷
   rw 68 q28 ∷
   re 68 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 67 q18 ∷
   re 68 5 (CX30 ∷ []) ∷
   re 68 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 74 q16 ∷ []) Eq.refl

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D361 (W : Ws) where

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
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn (Sw12 ∷ CK31⁻ ∷ []) (CK32⁻ ∷ Sw12 ∷ []) (wn 360 W)
  q3 : Eqn
  q3 = eqn (CX10 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((S ↑ • CK₁₀)))
  q4 : Eqn
  q4 = eqn (Sw12 ∷ CK32⁻ ∷ []) (CK31⁻ ∷ Sw12 ∷ []) (wn 362 W)
  q5 : Eqn
  q5 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q6 : Eqn
  q6 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q7 : Eqn
  q7 = eqn (CX10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((CS • CS • CS)))
  q8 : Eqn
  q8 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q9 : Eqn
  q9 = eqn (S3⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S2⁻ ∷ []) (wn 689 W)
  q10 : Eqn
  q10 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q11 : Eqn
  q11 = eqn (CK01 ∷ Sw23 ∷ []) (Sw23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (Swap))
  q12 : Eqn
  q12 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q13 : Eqn
  q13 = eqn (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ []) (wn 977 W)
  q14 : Eqn
  q14 = eqn (Sw23 ∷ S2⁻ ∷ []) (S3⁻ ∷ Sw23 ∷ []) (wn 153 W)
  q15 : Eqn
  q15 = eqn (CX20 ∷ S3⁻ ∷ []) (S3⁻ ∷ CX20 ∷ []) (low₃-comm ((Swap ↑ • CX₁₀ • Swap ↑)) ((S • S • S)))
  q16 : Eqn
  q16 = eqn (CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ []) (wn 978 W)
  q17 : Eqn
  q17 = eqn (CS01 ∷ X2 ∷ []) (X2 ∷ CS01 ∷ []) (low-comm (CS) (X))
  q18 : Eqn
  q18 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q19 : Eqn
  q19 = eqn (S0 ∷ X2 ∷ []) (X2 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑)))
  q20 : Eqn
  q20 = eqn (S0 ∷ CX23 ∷ []) (CX23 ∷ S0 ∷ []) (low₁-comm (S) ((CX₀₁ ↑)))
  q21 : Eqn
  q21 = eqn (CK01 ∷ X2 ∷ []) (X2 ∷ CK01 ∷ []) (low-comm (CK₀₁) (X))
  q22 : Eqn
  q22 = eqn (CK01 ∷ CX23 ∷ []) (CX23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₀₁))
  q23 : Eqn
  q23 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q24 : Eqn
  q24 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q25 : Eqn
  q25 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q26 : Eqn
  q26 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q27 : Eqn
  q27 = eqn (CX21 ∷ X2 ∷ CX23 ∷ X2 ∷ []) (X2 ∷ CX23 ∷ X2 ∷ CX21 ∷ []) (wn 612 W)
  q28 : Eqn
  q28 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q29 : Eqn
  q29 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];2,0->1) passes white iX via V2 conjugates 3 part4: 500 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part4 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ Sw23 ∷ CX30 ∷ CK21⁻ ∷ Sw23 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS01 ∷ CX23 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part4 = derive (X2 ∷ CS23⁻ ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ Sw23 ∷ CX30 ∷ CK21⁻ ∷ Sw23 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS23⁻ ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS01 ∷ CX23 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ [])
  (re 108 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 114 q1 ∷
   re 112 3 (CK31⁻ ∷ []) ∷
   rw 111 q2 ∷
   rw 110 q3 ∷
   rw 109 q4 ∷
   re 109 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 108 q5 ∷
   re 109 5 (CX30 ∷ []) ∷
   re 109 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 111 q5 ∷
   re 107 3 (CK31⁻ ∷ []) ∷
   re 109 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 108 q1 ∷
   re 109 3 (CX30 ∷ []) ∷
   re 109 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 115 q1 ∷
   re 113 3 (CS13⁻ ∷ []) ∷
   rw 112 q6 ∷
   rw 111 q7 ∷
   rw 110 q8 ∷
   re 110 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 109 q5 ∷
   re 110 5 (CX30 ∷ []) ∷
   re 110 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 112 q5 ∷
   re 108 3 (CS13⁻ ∷ []) ∷
   re 110 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 109 q1 ∷
   re 110 3 (CX30 ∷ []) ∷
   re 110 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 116 q1 ∷
   re 114 3 (CS13⁻ ∷ []) ∷
   rw 113 q6 ∷
   rw 112 q7 ∷
   rw 111 q8 ∷
   re 111 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 110 q5 ∷
   re 111 5 (CX30 ∷ []) ∷
   re 111 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 113 q5 ∷
   re 109 3 (CS13⁻ ∷ []) ∷
   re 111 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 110 q1 ∷
   re 111 3 (CX30 ∷ []) ∷
   re 111 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 117 q1 ∷
   re 115 3 (CS13⁻ ∷ []) ∷
   rw 114 q6 ∷
   rw 113 q7 ∷
   rw 112 q8 ∷
   re 112 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 111 q5 ∷
   re 112 5 (CX30 ∷ []) ∷
   re 112 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 114 q5 ∷
   re 110 3 (CS13⁻ ∷ []) ∷
   rw 111 q1 ∷
   re 110 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 112 q5 ∷
   re 109 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 111 q5 ∷
   re 108 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 110 q5 ∷
   re 107 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 109 q5 ∷
   rw 106 q9 ∷
   re 105 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 107 q5 ∷
   re 104 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 106 q5 ∷
   re 103 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 105 q5 ∷
   re 102 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 104 q5 ∷
   re 101 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 103 q5 ∷
   re 100 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 102 q5 ∷
   rw 99 q10 ∷
   rw 98 q11 ∷
   rw 97 q10 ∷
   rw 96 q10 ∷
   rw 95 q10 ∷
   rw 94 q10 ∷
   rw 93 q11 ∷
   rw 92 q10 ∷
   rw 91 q10 ∷
   rw 90 q10 ∷
   rw 89 q12 ∷
   rw 88 q12 ∷
   rw 87 q12 ∷
   rw 86 q12 ∷
   rw 85 q12 ∷
   rw 84 q12 ∷
   rw 83 q12 ∷
   rw 82 q12 ∷
   rw 81 q12 ∷
   rw 80 q10 ∷
   rw 79 q11 ∷
   rw 78 q10 ∷
   rw 77 q10 ∷
   rw 76 q10 ∷
   rw 75 q12 ∷
   rw 74 q12 ∷
   rw 73 q12 ∷
   rw 72 q12 ∷
   rw 71 q12 ∷
   rw 70 q12 ∷
   rw 69 q12 ∷
   rw 68 q12 ∷
   rw 67 q12 ∷
   rw 66 q12 ∷
   rw 65 q12 ∷
   rw 64 q12 ∷
   rw 63 q12 ∷
   rw 62 q12 ∷
   rw 61 q12 ∷
   rw 60 q12 ∷
   rw 59 q12 ∷
   rw 58 q12 ∷
   rw 59 q13 ∷
   rw 60 q1 ∷
   re 58 3 (CS13⁻ ∷ []) ∷
   rw 61 q1 ∷
   re 59 3 (CS13⁻ ∷ []) ∷
   rw 62 q1 ∷
   re 60 3 (CS13⁻ ∷ []) ∷
   rw 63 q1 ∷
   re 61 3 (CS13⁻ ∷ []) ∷
   rw 64 q1 ∷
   re 62 3 (CS13⁻ ∷ []) ∷
   rw 65 q1 ∷
   re 63 3 (CS13⁻ ∷ []) ∷
   rw 64 q14 ∷
   rw 67 q1 ∷
   re 65 3 (CK31⁻ ∷ []) ∷
   rw 68 q1 ∷
   re 66 3 (CS13⁻ ∷ []) ∷
   rw 69 q1 ∷
   re 67 3 (CS13⁻ ∷ []) ∷
   rw 70 q1 ∷
   re 68 3 (CS13⁻ ∷ []) ∷
   rw⁻ 69 q12 ∷
   rw⁻ 70 q12 ∷
   rw⁻ 71 q12 ∷
   rw⁻ 72 q12 ∷
   rw⁻ 73 q12 ∷
   rw⁻ 74 q12 ∷
   rw⁻ 75 q12 ∷
   rw⁻ 76 q12 ∷
   rw⁻ 77 q12 ∷
   rw⁻ 78 q12 ∷
   rw⁻ 79 q12 ∷
   rw⁻ 80 q12 ∷
   rw⁻ 81 q12 ∷
   rw⁻ 82 q12 ∷
   rw⁻ 83 q12 ∷
   rw⁻ 84 q12 ∷
   rw⁻ 85 q12 ∷
   rw⁻ 86 q12 ∷
   rw⁻ 87 q10 ∷
   rw⁻ 88 q10 ∷
   rw⁻ 89 q10 ∷
   rw⁻ 90 q11 ∷
   rw⁻ 91 q10 ∷
   rw⁻ 92 q12 ∷
   rw⁻ 93 q12 ∷
   rw⁻ 94 q12 ∷
   rw⁻ 95 q12 ∷
   rw⁻ 96 q12 ∷
   rw⁻ 97 q12 ∷
   rw⁻ 98 q12 ∷
   rw⁻ 99 q12 ∷
   rw⁻ 100 q12 ∷
   rw⁻ 101 q10 ∷
   rw⁻ 102 q10 ∷
   rw⁻ 103 q10 ∷
   rw⁻ 104 q11 ∷
   rw⁻ 105 q10 ∷
   rw⁻ 106 q10 ∷
   rw⁻ 107 q10 ∷
   rw⁻ 108 q10 ∷
   rw⁻ 109 q11 ∷
   rw⁻ 110 q10 ∷
   rw 111 q5 ∷
   re 58 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 57 q1 ∷
   re 58 3 (CX30 ∷ []) ∷
   re 58 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 64 q1 ∷
   re 62 3 (CS13⁻ ∷ []) ∷
   rw 61 q6 ∷
   rw 60 q7 ∷
   rw 59 q8 ∷
   re 59 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 58 q5 ∷
   re 59 5 (CX30 ∷ []) ∷
   re 59 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 61 q5 ∷
   re 57 3 (CS13⁻ ∷ []) ∷
   re 59 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 58 q1 ∷
   re 59 3 (CX30 ∷ []) ∷
   re 59 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 65 q1 ∷
   re 63 3 (CS13⁻ ∷ []) ∷
   rw 62 q6 ∷
   rw 61 q7 ∷
   rw 60 q8 ∷
   re 60 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 59 q5 ∷
   re 60 5 (CX30 ∷ []) ∷
   re 60 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 62 q5 ∷
   re 58 3 (CS13⁻ ∷ []) ∷
   re 60 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 59 q1 ∷
   re 60 3 (CX30 ∷ []) ∷
   re 60 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 66 q1 ∷
   re 64 3 (CS13⁻ ∷ []) ∷
   rw 63 q6 ∷
   rw 62 q7 ∷
   rw 61 q8 ∷
   re 61 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 60 q5 ∷
   re 61 5 (CX30 ∷ []) ∷
   re 61 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 63 q5 ∷
   re 59 3 (CS13⁻ ∷ []) ∷
   re 61 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 60 q1 ∷
   re 61 3 (CX30 ∷ []) ∷
   re 61 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 67 q1 ∷
   re 65 3 (CS13⁻ ∷ []) ∷
   rw 64 q6 ∷
   rw 63 q7 ∷
   rw 62 q8 ∷
   re 62 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 61 q5 ∷
   re 62 5 (CX30 ∷ []) ∷
   re 62 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 64 q5 ∷
   re 60 3 (CS13⁻ ∷ []) ∷
   re 62 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 61 q1 ∷
   re 62 3 (CX30 ∷ []) ∷
   re 62 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 68 q1 ∷
   re 66 3 (CS13⁻ ∷ []) ∷
   rw 65 q6 ∷
   rw 64 q7 ∷
   rw 63 q8 ∷
   re 63 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 62 q5 ∷
   re 63 5 (CX30 ∷ []) ∷
   re 63 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 65 q5 ∷
   re 61 3 (CS13⁻ ∷ []) ∷
   re 63 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 62 q1 ∷
   re 63 3 (CX30 ∷ []) ∷
   re 63 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 69 q1 ∷
   re 67 3 (CS13⁻ ∷ []) ∷
   rw 66 q6 ∷
   rw 65 q7 ∷
   rw 64 q8 ∷
   re 64 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 63 q5 ∷
   re 64 5 (CX30 ∷ []) ∷
   re 64 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 66 q5 ∷
   re 62 3 (CS13⁻ ∷ []) ∷
   rw 63 q15 ∷
   re 65 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 64 q1 ∷
   re 65 3 (CX30 ∷ []) ∷
   re 65 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q1 ∷
   re 69 3 (CK31⁻ ∷ []) ∷
   rw 68 q2 ∷
   rw 67 q3 ∷
   rw 66 q4 ∷
   re 66 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 65 q5 ∷
   re 66 5 (CX30 ∷ []) ∷
   re 66 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 68 q5 ∷
   re 64 3 (CK31⁻ ∷ []) ∷
   re 66 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 65 q1 ∷
   re 66 3 (CX30 ∷ []) ∷
   re 66 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 72 q1 ∷
   re 70 3 (CS13⁻ ∷ []) ∷
   rw 69 q6 ∷
   rw 68 q7 ∷
   rw 67 q8 ∷
   re 67 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 66 q5 ∷
   re 67 5 (CX30 ∷ []) ∷
   re 67 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 69 q5 ∷
   re 65 3 (CS13⁻ ∷ []) ∷
   re 67 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 66 q1 ∷
   re 67 3 (CX30 ∷ []) ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q1 ∷
   re 71 3 (CS13⁻ ∷ []) ∷
   rw 70 q6 ∷
   rw 69 q7 ∷
   rw 68 q8 ∷
   re 68 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 67 q5 ∷
   re 68 5 (CX30 ∷ []) ∷
   re 68 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 70 q5 ∷
   re 66 3 (CS13⁻ ∷ []) ∷
   re 68 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 67 q1 ∷
   re 68 3 (CX30 ∷ []) ∷
   re 68 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 74 q1 ∷
   re 72 3 (CS13⁻ ∷ []) ∷
   rw 71 q6 ∷
   rw 70 q7 ∷
   rw 69 q8 ∷
   re 69 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 68 q5 ∷
   re 69 5 (CX30 ∷ []) ∷
   re 69 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 71 q5 ∷
   re 67 3 (CS13⁻ ∷ []) ∷
   rw 42 q16 ∷
   rw 126 q17 ∷
   rw 127 q18 ∷
   rw 128 q17 ∷
   rw 125 q17 ∷
   rw 126 q18 ∷
   rw 127 q17 ∷
   rw 124 q17 ∷
   rw 125 q18 ∷
   rw 126 q17 ∷
   rw 123 q17 ∷
   rw 124 q18 ∷
   rw 125 q17 ∷
   rw 122 q17 ∷
   rw 123 q18 ∷
   rw 124 q17 ∷
   rw 121 q17 ∷
   rw 122 q18 ∷
   rw 123 q17 ∷
   rw 120 q19 ∷
   rw 121 q20 ∷
   rw 122 q19 ∷
   rw 119 q21 ∷
   rw 120 q22 ∷
   rw 121 q21 ∷
   rw 118 q17 ∷
   rw 119 q18 ∷
   rw 120 q17 ∷
   rw 117 q17 ∷
   rw 118 q18 ∷
   rw 119 q17 ∷
   rw 116 q17 ∷
   rw 117 q18 ∷
   rw 118 q17 ∷
   rw 115 q19 ∷
   rw 116 q20 ∷
   rw 117 q19 ∷
   rw 114 q21 ∷
   rw 115 q22 ∷
   rw 116 q21 ∷
   rw 113 q19 ∷
   rw 114 q20 ∷
   rw 115 q19 ∷
   rw 112 q21 ∷
   rw 113 q22 ∷
   rw 114 q21 ∷
   rw 115 q23 ∷
   rw⁻ 114 q24 ∷
   rw⁻ 113 q25 ∷
   rw⁻ 112 q24 ∷
   rw 111 q26 ∷
   rw 112 q27 ∷
   rw 111 q24 ∷
   rw 112 q25 ∷
   rw 113 q24 ∷
   rw 114 q28 ∷
   rw 115 q29 ∷
   rw 110 q19 ∷
   rw 111 q20 ∷
   rw 112 q19 ∷
   rw 109 q21 ∷
   rw 110 q22 ∷
   rw 111 q21 ∷
   rw 108 q19 ∷
   rw 109 q20 ∷
   rw 110 q19 ∷
   rw 107 q19 ∷
   rw 108 q20 ∷
   rw 109 q19 ∷
   rw 106 q19 ∷
   rw 107 q20 ∷
   rw 108 q19 ∷
   rw 105 q19 ∷
   rw 106 q20 ∷
   rw 107 q19 ∷
   rw 104 q21 ∷
   rw 105 q22 ∷
   rw 106 q21 ∷
   rw 103 q19 ∷
   rw 104 q20 ∷
   rw 105 q19 ∷
   rw 102 q19 ∷
   rw 103 q20 ∷
   rw 104 q19 ∷
   rw 101 q19 ∷
   rw 102 q20 ∷
   rw 103 q19 ∷
   rw 100 q17 ∷
   rw 101 q18 ∷
   rw 102 q17 ∷
   rw 99 q17 ∷
   rw 100 q18 ∷
   rw 101 q17 ∷
   rw 98 q17 ∷
   rw 99 q18 ∷
   rw 100 q17 ∷
   rw 97 q17 ∷
   rw 98 q18 ∷
   rw 99 q17 ∷
   rw 96 q17 ∷
   rw 97 q18 ∷
   rw 98 q17 ∷
   rw 95 q17 ∷
   rw 96 q18 ∷
   rw 97 q17 ∷
   rw 94 q17 ∷
   rw 95 q18 ∷
   rw 96 q17 ∷
   rw 93 q17 ∷
   rw 94 q18 ∷
   rw 95 q17 ∷
   rw 92 q17 ∷
   rw 93 q18 ∷
   rw 94 q17 ∷
   rw 91 q19 ∷
   rw 92 q20 ∷
   rw 93 q19 ∷
   rw 90 q21 ∷
   rw 91 q22 ∷
   rw 92 q21 ∷
   rw 89 q19 ∷
   rw 90 q20 ∷
   rw 91 q19 ∷
   rw 88 q19 ∷
   rw 89 q20 ∷
   rw 90 q19 ∷
   rw 87 q19 ∷
   rw 88 q20 ∷
   rw 89 q19 ∷
   rw 86 q17 ∷
   rw 87 q18 ∷
   rw 88 q17 ∷
   rw 85 q17 ∷
   rw 86 q18 ∷
   rw 87 q17 ∷
   rw 84 q17 ∷
   rw 85 q18 ∷
   rw 86 q17 ∷
   rw 83 q17 ∷
   rw 84 q18 ∷
   rw 85 q17 ∷
   rw 82 q17 ∷
   rw 83 q18 ∷
   rw 84 q17 ∷
   rw 81 q17 ∷
   rw 82 q18 ∷
   rw 83 q17 ∷
   rw 80 q17 ∷
   rw 81 q18 ∷
   rw 82 q17 ∷
   rw 79 q17 ∷
   rw 80 q18 ∷
   rw 81 q17 ∷
   rw 78 q17 ∷
   rw 79 q18 ∷
   rw 80 q17 ∷
   rw 77 q17 ∷
   rw 78 q18 ∷
   rw 79 q17 ∷
   rw 76 q17 ∷
   rw 77 q18 ∷
   rw 78 q17 ∷
   rw 75 q17 ∷ []) Eq.refl

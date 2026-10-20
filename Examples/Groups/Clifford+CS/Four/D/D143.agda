{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D143 (W : Ws) where

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
  q1 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q2 : Eqn
  q2 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q3 : Eqn
  q3 = eqn (CK01 ∷ Sw23 ∷ []) (Sw23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (Swap))
  q4 : Eqn
  q4 = eqn (CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (wn 535 W)
  q5 : Eqn
  q5 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q6 : Eqn
  q6 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q7 : Eqn
  q7 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q8 : Eqn
  q8 = eqn (CX10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((CS • CS • CS)))
  q9 : Eqn
  q9 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q10 : Eqn
  q10 = eqn (Sw12 ∷ CK31⁻ ∷ []) (CK32⁻ ∷ Sw12 ∷ []) (wn 360 W)
  q11 : Eqn
  q11 = eqn (CX10 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((S ↑ • CK₁₀)))
  q12 : Eqn
  q12 = eqn (Sw12 ∷ CK32⁻ ∷ []) (CK31⁻ ∷ Sw12 ∷ []) (wn 362 W)
  q13 : Eqn
  q13 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (wn 688 W)
  q14 : Eqn
  q14 = eqn (CK01 ∷ X2 ∷ []) (X2 ∷ CK01 ∷ []) (low-comm (CK₀₁) (X))
  q15 : Eqn
  q15 = eqn (CK01 ∷ CX23 ∷ []) (CX23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₀₁))
  q16 : Eqn
  q16 = eqn (CS01 ∷ X2 ∷ []) (X2 ∷ CS01 ∷ []) (low-comm (CS) (X))
  q17 : Eqn
  q17 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q18 : Eqn
  q18 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q20 : Eqn
  q20 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q21 : Eqn
  q21 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q22 : Eqn
  q22 = eqn (CX21 ∷ X2 ∷ CX23 ∷ X2 ∷ []) (X2 ∷ CX23 ∷ X2 ∷ CX21 ∷ []) (wn 612 W)
  q23 : Eqn
  q23 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q24 : Eqn
  q24 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q25 : Eqn
  q25 = eqn (S0 ∷ X2 ∷ []) (X2 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑)))
  q26 : Eqn
  q26 = eqn (S0 ∷ CX23 ∷ []) (CX23 ∷ S0 ∷ []) (low₁-comm (S) ((CX₀₁ ↑)))
  q27 : Eqn
  q27 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X2 ∷ CX23 ∷ X2 ∷ []) (X2 ∷ CX23 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (wn 613 W)
  q28 : Eqn
  q28 = eqn (S3⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S2⁻ ∷ []) (wn 689 W)
  q29 : Eqn
  q29 = eqn (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) (wn 539 W)
  q30 : Eqn
  q30 = eqn (Sw23 ∷ S2⁻ ∷ []) (S3⁻ ∷ Sw23 ∷ []) (wn 153 W)
  q31 : Eqn
  q31 = eqn (CX20 ∷ S3⁻ ∷ []) (S3⁻ ∷ CX20 ∷ []) (low₃-comm ((Swap ↑ • CX₁₀ • Swap ↑)) ((S • S • S)))
  q32 : Eqn
  q32 = eqn (CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (wn 541 W)

-- Bar(['S', 'S', 'K', 'S', 'K', 'K'];2,0->1) passes white iX via V2 conjugates 3 part2: 500 steps
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part2 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ Sw23 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ Sw23 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CS13⁻ ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part2 = derive (X2 ∷ CS23⁻ ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ Sw23 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ Sw23 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS23⁻ ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CS13⁻ ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ [])
  (rw 52 q1 ∷
   rw 51 q1 ∷
   rw 50 q2 ∷
   rw 49 q3 ∷
   rw 48 q1 ∷
   rw 47 q1 ∷
   rw 46 q1 ∷
   rw 45 q2 ∷
   rw 44 q3 ∷
   rw 43 q2 ∷
   rw 42 q3 ∷
   rw 43 q4 ∷
   rw 44 q5 ∷
   re 42 3 (CS13⁻ ∷ []) ∷
   rw 45 q5 ∷
   re 43 3 (CK31⁻ ∷ []) ∷
   rw 46 q5 ∷
   re 44 3 (CS13⁻ ∷ []) ∷
   rw 47 q5 ∷
   re 45 3 (CS13⁻ ∷ []) ∷
   rw⁻ 46 q3 ∷
   rw⁻ 47 q2 ∷
   rw⁻ 48 q3 ∷
   rw⁻ 49 q2 ∷
   rw⁻ 50 q1 ∷
   rw⁻ 51 q1 ∷
   rw⁻ 52 q1 ∷
   rw⁻ 53 q3 ∷
   rw⁻ 54 q2 ∷
   rw⁻ 55 q1 ∷
   rw⁻ 56 q1 ∷
   rw⁻ 57 q1 ∷
   rw⁻ 58 q1 ∷
   rw⁻ 59 q1 ∷
   rw⁻ 60 q1 ∷
   rw 61 q6 ∷
   re 42 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 41 q5 ∷
   re 42 3 (CX30 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q5 ∷
   re 46 3 (CS13⁻ ∷ []) ∷
   rw 45 q7 ∷
   rw 44 q8 ∷
   rw 43 q9 ∷
   re 43 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 42 q6 ∷
   re 43 5 (CX30 ∷ []) ∷
   re 43 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 45 q6 ∷
   re 41 3 (CS13⁻ ∷ []) ∷
   re 43 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 42 q5 ∷
   re 43 3 (CX30 ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q5 ∷
   re 47 3 (CK31⁻ ∷ []) ∷
   rw 46 q10 ∷
   rw 45 q11 ∷
   rw 44 q12 ∷
   re 44 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 43 q6 ∷
   re 44 5 (CX30 ∷ []) ∷
   re 44 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 46 q6 ∷
   re 42 3 (CK31⁻ ∷ []) ∷
   re 44 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 43 q5 ∷
   re 44 3 (CX30 ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q5 ∷
   re 48 3 (CS13⁻ ∷ []) ∷
   rw 47 q7 ∷
   rw 46 q8 ∷
   rw 45 q9 ∷
   re 45 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 44 q6 ∷
   re 45 5 (CX30 ∷ []) ∷
   re 45 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 47 q6 ∷
   re 43 3 (CS13⁻ ∷ []) ∷
   re 45 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 44 q5 ∷
   re 45 3 (CX30 ∷ []) ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q5 ∷
   re 49 3 (CS13⁻ ∷ []) ∷
   rw 48 q7 ∷
   rw 47 q8 ∷
   rw 46 q9 ∷
   re 46 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 45 q6 ∷
   re 46 5 (CX30 ∷ []) ∷
   re 46 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 48 q6 ∷
   re 44 3 (CS13⁻ ∷ []) ∷
   rw 35 q13 ∷
   rw 67 q14 ∷
   rw 68 q15 ∷
   rw 69 q14 ∷
   rw 66 q14 ∷
   rw 67 q15 ∷
   rw 68 q14 ∷
   rw 65 q16 ∷
   rw 66 q17 ∷
   rw 67 q16 ∷
   rw 64 q14 ∷
   rw 65 q15 ∷
   rw 66 q14 ∷
   rw 63 q16 ∷
   rw 64 q17 ∷
   rw 65 q16 ∷
   rw 62 q16 ∷
   rw 63 q17 ∷
   rw 64 q16 ∷
   rw 65 q18 ∷
   rw⁻ 64 q19 ∷
   rw⁻ 63 q20 ∷
   rw⁻ 62 q19 ∷
   rw 61 q21 ∷
   rw 62 q22 ∷
   rw 61 q19 ∷
   rw 62 q20 ∷
   rw 63 q19 ∷
   rw 64 q23 ∷
   rw 65 q24 ∷
   rw 60 q16 ∷
   rw 61 q17 ∷
   rw 62 q16 ∷
   rw 59 q16 ∷
   rw 60 q17 ∷
   rw 61 q16 ∷
   rw 58 q16 ∷
   rw 59 q17 ∷
   rw 60 q16 ∷
   rw 57 q16 ∷
   rw 58 q17 ∷
   rw 59 q16 ∷
   rw 56 q16 ∷
   rw 57 q17 ∷
   rw 58 q16 ∷
   rw 55 q16 ∷
   rw 56 q17 ∷
   rw 57 q16 ∷
   rw 54 q25 ∷
   rw 55 q26 ∷
   rw 56 q25 ∷
   rw 53 q14 ∷
   rw 54 q15 ∷
   rw 55 q14 ∷
   rw 52 q16 ∷
   rw 53 q17 ∷
   rw 54 q16 ∷
   rw 51 q16 ∷
   rw 52 q17 ∷
   rw 53 q16 ∷
   rw 50 q16 ∷
   rw 51 q17 ∷
   rw 52 q16 ∷
   rw 49 q25 ∷
   rw 50 q26 ∷
   rw 51 q25 ∷
   rw 48 q14 ∷
   rw 49 q15 ∷
   rw 50 q14 ∷
   rw 47 q25 ∷
   rw 48 q26 ∷
   rw 49 q25 ∷
   rw 46 q14 ∷
   rw 47 q15 ∷
   rw 48 q14 ∷
   rw 49 q18 ∷
   rw⁻ 48 q19 ∷
   rw⁻ 47 q20 ∷
   rw⁻ 46 q19 ∷
   rw 45 q21 ∷
   rw 46 q22 ∷
   rw 45 q19 ∷
   rw 46 q20 ∷
   rw 47 q19 ∷
   rw 48 q23 ∷
   rw 49 q24 ∷
   rw 39 q27 ∷
   rw 82 q5 ∷
   re 81 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 83 q6 ∷
   re 80 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 82 q6 ∷
   re 79 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 81 q6 ∷
   re 78 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 80 q6 ∷
   rw 77 q28 ∷
   re 76 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 78 q6 ∷
   re 75 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 77 q6 ∷
   re 74 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 76 q6 ∷
   re 73 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 75 q6 ∷
   re 72 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 74 q6 ∷
   re 71 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 73 q6 ∷
   rw 70 q3 ∷
   rw 69 q3 ∷
   rw 68 q1 ∷
   rw 67 q3 ∷
   rw 66 q1 ∷
   rw 65 q1 ∷
   rw 66 q29 ∷
   rw 67 q5 ∷
   re 65 3 (CS13⁻ ∷ []) ∷
   rw 68 q5 ∷
   re 66 3 (CS13⁻ ∷ []) ∷
   rw 69 q5 ∷
   re 67 3 (CS13⁻ ∷ []) ∷
   rw 70 q5 ∷
   re 68 3 (CS13⁻ ∷ []) ∷
   rw 71 q5 ∷
   re 69 3 (CS13⁻ ∷ []) ∷
   rw 72 q5 ∷
   re 70 3 (CS13⁻ ∷ []) ∷
   rw 71 q30 ∷
   rw 74 q5 ∷
   re 72 3 (CK31⁻ ∷ []) ∷
   rw 75 q5 ∷
   re 73 3 (CS13⁻ ∷ []) ∷
   rw 76 q5 ∷
   re 74 3 (CS13⁻ ∷ []) ∷
   rw 77 q5 ∷
   re 75 3 (CS13⁻ ∷ []) ∷
   rw⁻ 76 q1 ∷
   rw⁻ 77 q1 ∷
   rw⁻ 78 q3 ∷
   rw⁻ 79 q1 ∷
   rw⁻ 80 q3 ∷
   rw⁻ 81 q3 ∷
   rw 82 q6 ∷
   re 65 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 64 q5 ∷
   re 65 3 (CX30 ∷ []) ∷
   re 65 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q5 ∷
   re 69 3 (CS13⁻ ∷ []) ∷
   rw 68 q7 ∷
   rw 67 q8 ∷
   rw 66 q9 ∷
   re 66 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 65 q6 ∷
   re 66 5 (CX30 ∷ []) ∷
   re 66 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 68 q6 ∷
   re 64 3 (CS13⁻ ∷ []) ∷
   re 66 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 65 q5 ∷
   re 66 3 (CX30 ∷ []) ∷
   re 66 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 72 q5 ∷
   re 70 3 (CS13⁻ ∷ []) ∷
   rw 69 q7 ∷
   rw 68 q8 ∷
   rw 67 q9 ∷
   re 67 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 66 q6 ∷
   re 67 5 (CX30 ∷ []) ∷
   re 67 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 69 q6 ∷
   re 65 3 (CS13⁻ ∷ []) ∷
   re 67 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 66 q5 ∷
   re 67 3 (CX30 ∷ []) ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q5 ∷
   re 71 3 (CS13⁻ ∷ []) ∷
   rw 70 q7 ∷
   rw 69 q8 ∷
   rw 68 q9 ∷
   re 68 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 67 q6 ∷
   re 68 5 (CX30 ∷ []) ∷
   re 68 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 70 q6 ∷
   re 66 3 (CS13⁻ ∷ []) ∷
   re 68 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 67 q5 ∷
   re 68 3 (CX30 ∷ []) ∷
   re 68 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 74 q5 ∷
   re 72 3 (CS13⁻ ∷ []) ∷
   rw 71 q7 ∷
   rw 70 q8 ∷
   rw 69 q9 ∷
   re 69 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 68 q6 ∷
   re 69 5 (CX30 ∷ []) ∷
   re 69 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 71 q6 ∷
   re 67 3 (CS13⁻ ∷ []) ∷
   re 69 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 68 q5 ∷
   re 69 3 (CX30 ∷ []) ∷
   re 69 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 75 q5 ∷
   re 73 3 (CS13⁻ ∷ []) ∷
   rw 72 q7 ∷
   rw 71 q8 ∷
   rw 70 q9 ∷
   re 70 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 69 q6 ∷
   re 70 5 (CX30 ∷ []) ∷
   re 70 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 72 q6 ∷
   re 68 3 (CS13⁻ ∷ []) ∷
   re 70 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 69 q5 ∷
   re 70 3 (CX30 ∷ []) ∷
   re 70 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 76 q5 ∷
   re 74 3 (CS13⁻ ∷ []) ∷
   rw 73 q7 ∷
   rw 72 q8 ∷
   rw 71 q9 ∷
   re 71 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 70 q6 ∷
   re 71 5 (CX30 ∷ []) ∷
   re 71 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 73 q6 ∷
   re 69 3 (CS13⁻ ∷ []) ∷
   rw 70 q31 ∷
   re 72 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 71 q5 ∷
   re 72 3 (CX30 ∷ []) ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 78 q5 ∷
   re 76 3 (CK31⁻ ∷ []) ∷
   rw 75 q10 ∷
   rw 74 q11 ∷
   rw 73 q12 ∷
   re 73 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 72 q6 ∷
   re 73 5 (CX30 ∷ []) ∷
   re 73 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 75 q6 ∷
   re 71 3 (CK31⁻ ∷ []) ∷
   re 73 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 72 q5 ∷
   re 73 3 (CX30 ∷ []) ∷
   re 73 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 79 q5 ∷
   re 77 3 (CS13⁻ ∷ []) ∷
   rw 76 q7 ∷
   rw 75 q8 ∷
   rw 74 q9 ∷
   re 74 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 73 q6 ∷
   re 74 5 (CX30 ∷ []) ∷
   re 74 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 76 q6 ∷
   re 72 3 (CS13⁻ ∷ []) ∷
   re 74 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 73 q5 ∷
   re 74 3 (CX30 ∷ []) ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 80 q5 ∷
   re 78 3 (CS13⁻ ∷ []) ∷
   rw 77 q7 ∷
   rw 76 q8 ∷
   rw 75 q9 ∷
   re 75 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 74 q6 ∷
   re 75 5 (CX30 ∷ []) ∷
   re 75 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 77 q6 ∷
   re 73 3 (CS13⁻ ∷ []) ∷
   re 75 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 74 q5 ∷
   re 75 3 (CX30 ∷ []) ∷
   re 75 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 81 q5 ∷
   re 79 3 (CS13⁻ ∷ []) ∷
   rw 78 q7 ∷
   rw 77 q8 ∷
   rw 76 q9 ∷
   re 76 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 75 q6 ∷
   re 76 5 (CX30 ∷ []) ∷
   re 76 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 78 q6 ∷
   re 74 3 (CS13⁻ ∷ []) ∷
   rw 75 q5 ∷
   re 74 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 76 q6 ∷
   re 73 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 75 q6 ∷
   re 72 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 74 q6 ∷
   re 71 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 73 q6 ∷
   rw 70 q28 ∷
   re 69 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 71 q6 ∷
   re 68 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 70 q6 ∷
   re 67 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 69 q6 ∷
   re 66 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 68 q6 ∷
   re 65 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 67 q6 ∷
   re 64 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 66 q6 ∷
   rw 63 q1 ∷
   rw 62 q1 ∷
   rw 61 q1 ∷
   rw 60 q1 ∷
   rw 59 q1 ∷
   rw 58 q1 ∷
   rw 57 q2 ∷
   rw 56 q3 ∷
   rw 55 q1 ∷
   rw 54 q1 ∷
   rw 53 q1 ∷
   rw 52 q2 ∷
   rw 51 q3 ∷
   rw 50 q2 ∷
   rw 49 q3 ∷
   rw 50 q32 ∷
   rw 51 q5 ∷
   re 49 3 (CS13⁻ ∷ []) ∷
   rw 52 q5 ∷
   re 50 3 (CS13⁻ ∷ []) ∷
   rw 53 q5 ∷
   re 51 3 (CS13⁻ ∷ []) ∷
   rw 54 q5 ∷
   re 52 3 (CS13⁻ ∷ []) ∷
   rw 55 q5 ∷
   re 53 3 (CS13⁻ ∷ []) ∷
   rw 56 q5 ∷
   re 54 3 (CS13⁻ ∷ []) ∷
   rw 55 q30 ∷
   rw 58 q5 ∷
   re 56 3 (CK31⁻ ∷ []) ∷
   rw 59 q5 ∷
   re 57 3 (CS13⁻ ∷ []) ∷
   rw 60 q5 ∷
   re 58 3 (CS13⁻ ∷ []) ∷
   rw 61 q5 ∷
   re 59 3 (CS13⁻ ∷ []) ∷
   rw⁻ 60 q3 ∷
   rw⁻ 61 q2 ∷
   rw⁻ 62 q3 ∷
   rw⁻ 63 q2 ∷
   rw⁻ 64 q1 ∷
   rw⁻ 65 q1 ∷
   rw⁻ 66 q1 ∷
   rw⁻ 67 q3 ∷
   rw⁻ 68 q2 ∷
   rw⁻ 69 q1 ∷
   rw⁻ 70 q1 ∷
   rw⁻ 71 q1 ∷
   rw⁻ 72 q1 ∷
   rw⁻ 73 q1 ∷
   rw⁻ 74 q1 ∷
   rw 75 q6 ∷
   re 49 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 48 q5 ∷
   re 49 3 (CX30 ∷ []) ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q5 ∷
   re 53 3 (CS13⁻ ∷ []) ∷
   rw 52 q7 ∷
   rw 51 q8 ∷
   rw 50 q9 ∷
   re 50 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 49 q6 ∷
   re 50 5 (CX30 ∷ []) ∷
   re 50 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 52 q6 ∷
   re 48 3 (CS13⁻ ∷ []) ∷
   re 50 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 49 q5 ∷
   re 50 3 (CX30 ∷ []) ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q5 ∷
   re 54 3 (CS13⁻ ∷ []) ∷
   rw 53 q7 ∷
   rw 52 q8 ∷
   rw 51 q9 ∷
   re 51 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 50 q6 ∷
   re 51 5 (CX30 ∷ []) ∷
   re 51 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 53 q6 ∷
   re 49 3 (CS13⁻ ∷ []) ∷
   re 51 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 50 q5 ∷
   re 51 3 (CX30 ∷ []) ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷ []) Eq.refl

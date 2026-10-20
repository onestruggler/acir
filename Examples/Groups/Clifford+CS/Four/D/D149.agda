{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D149 (W : Ws) where

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
  q2 = eqn (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) (wn 13 W)
  q3 : Eqn
  q3 = eqn (CS01⁻ ∷ CX32 ∷ []) (CX32 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₁₀))
  q4 : Eqn
  q4 = eqn (CX32 ∷ Sw12 ∷ []) (Sw12 ∷ CX31 ∷ []) (wn 78 W)
  q5 : Eqn
  q5 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q6 : Eqn
  q6 = eqn (CX21 ∷ S3⁻ ∷ []) (S3⁻ ∷ CX21 ∷ []) (low₃-comm ((CX₁₀ ↑)) ((S • S • S)))
  q7 : Eqn
  q7 = eqn (CK10⁻ ∷ CX32 ∷ []) (CX32 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q8 : Eqn
  q8 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q10 : Eqn
  q10 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q11 : Eqn
  q11 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ S3⁻ ∷ []) (S3⁻ ∷ Sw01 ∷ []) (low-comm (Swap) (((S • S • S) ↑)))
  q13 : Eqn
  q13 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q14 : Eqn
  q14 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q15 : Eqn
  q15 = eqn (CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) (wn 732 W)
  q16 : Eqn
  q16 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CK21⁻ ∷ []) (CK20⁻ ∷ Sw01 ∷ []) (wn 139 W)
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q20 : Eqn
  q20 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q21 : Eqn
  q21 = eqn (CS01 ∷ X2 ∷ []) (X2 ∷ CS01 ∷ []) (low-comm (CS) (X))
  q22 : Eqn
  q22 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q23 : Eqn
  q23 = eqn (CK10 ∷ X2 ∷ []) (X2 ∷ CK10 ∷ []) (low-comm (CK₁₀) (X))
  q24 : Eqn
  q24 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q25 : Eqn
  q25 = eqn (CX21 ∷ X2 ∷ CX23 ∷ X2 ∷ []) (X2 ∷ CX23 ∷ X2 ∷ CX21 ∷ []) (wn 612 W)
  q26 : Eqn
  q26 = eqn (S1 ∷ X2 ∷ []) (X2 ∷ S1 ∷ []) (low-comm ((S ↑)) (X))
  q27 : Eqn
  q27 = eqn (S1 ∷ CX23 ∷ []) (CX23 ∷ S1 ∷ []) (low-comm ((S ↑)) (CX₀₁))
  q28 : Eqn
  q28 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q29 : Eqn
  q29 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q30 : Eqn
  q30 = eqn (CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X2 ∷ CX23 ∷ X2 ∷ []) (X2 ∷ CX23 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) (wn 661 W)
  q31 : Eqn
  q31 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (wn 733 W)
  q32 : Eqn
  q32 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (wn 735 W)

-- Bar(SSSKSS;2,1->0) passes white iX via V2 conjugates 3 part3: 256 steps
lem-Bar⟨SSSKSS21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part3 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part3 = derive (X2 ∷ CS23⁻ ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS23⁻ ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 53 q1 ∷
   re 54 3 (CX31 ∷ []) ∷
   rw 54 q2 ∷
   rw⁻ 55 q3 ∷
   rw 56 q4 ∷
   re 57 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 59 q5 ∷
   re 53 5 (CS03⁻ ∷ []) ∷
   rw 54 q6 ∷
   re 56 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q1 ∷
   re 56 3 (CX31 ∷ []) ∷
   rw 56 q2 ∷
   rw⁻ 57 q7 ∷
   rw 58 q4 ∷
   re 59 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 61 q5 ∷
   re 55 5 (CK30⁻ ∷ []) ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q1 ∷
   re 57 3 (CX31 ∷ []) ∷
   rw 57 q2 ∷
   rw⁻ 58 q3 ∷
   rw 59 q4 ∷
   re 60 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 62 q5 ∷
   re 56 5 (CS03⁻ ∷ []) ∷
   re 58 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 57 q1 ∷
   re 58 3 (CX31 ∷ []) ∷
   rw 58 q2 ∷
   rw⁻ 59 q3 ∷
   rw 60 q4 ∷
   re 61 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 63 q5 ∷
   re 57 5 (CS03⁻ ∷ []) ∷
   re 59 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q1 ∷
   re 59 3 (CX31 ∷ []) ∷
   rw 59 q2 ∷
   rw⁻ 60 q3 ∷
   rw 61 q4 ∷
   re 62 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 64 q5 ∷
   re 58 5 (CS03⁻ ∷ []) ∷
   rw 59 q8 ∷
   re 58 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 60 q9 ∷
   rw 59 q10 ∷
   rw⁻ 58 q9 ∷
   re 59 3 (CS13⁻ ∷ []) ∷
   re 57 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 59 q9 ∷
   rw 58 q10 ∷
   rw⁻ 57 q9 ∷
   re 58 3 (CS13⁻ ∷ []) ∷
   re 56 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 58 q9 ∷
   rw 57 q10 ∷
   rw⁻ 56 q9 ∷
   re 57 3 (CS13⁻ ∷ []) ∷
   re 55 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 57 q9 ∷
   rw 56 q11 ∷
   rw⁻ 55 q9 ∷
   re 56 3 (CK31⁻ ∷ []) ∷
   rw⁻ 54 q12 ∷
   re 53 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 55 q9 ∷
   rw 54 q10 ∷
   rw⁻ 53 q9 ∷
   re 54 3 (CS13⁻ ∷ []) ∷
   re 52 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 54 q9 ∷
   rw 53 q10 ∷
   rw⁻ 52 q9 ∷
   re 53 3 (CS13⁻ ∷ []) ∷
   re 51 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q9 ∷
   rw 52 q10 ∷
   rw⁻ 51 q9 ∷
   re 52 3 (CS13⁻ ∷ []) ∷
   re 50 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q9 ∷
   rw 51 q10 ∷
   rw⁻ 50 q9 ∷
   re 51 3 (CS13⁻ ∷ []) ∷
   re 49 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q9 ∷
   rw 50 q10 ∷
   rw⁻ 49 q9 ∷
   re 50 3 (CS13⁻ ∷ []) ∷
   re 48 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q9 ∷
   rw 49 q10 ∷
   rw⁻ 48 q9 ∷
   re 49 3 (CS13⁻ ∷ []) ∷
   rw 47 q13 ∷
   rw 46 q13 ∷
   rw 45 q14 ∷
   rw 44 q13 ∷
   rw 43 q13 ∷
   rw 42 q13 ∷
   rw 43 q15 ∷
   re 43 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 42 q9 ∷
   rw 43 q16 ∷
   rw 44 q9 ∷
   re 42 3 (CS03⁻ ∷ []) ∷
   re 44 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 43 q9 ∷
   rw 44 q16 ∷
   rw 45 q9 ∷
   re 43 3 (CS03⁻ ∷ []) ∷
   re 45 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 44 q9 ∷
   rw 45 q16 ∷
   rw 46 q9 ∷
   re 44 3 (CS03⁻ ∷ []) ∷
   re 46 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 45 q9 ∷
   rw 46 q16 ∷
   rw 47 q9 ∷
   re 45 3 (CS03⁻ ∷ []) ∷
   re 47 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 46 q9 ∷
   rw 47 q16 ∷
   rw 48 q9 ∷
   re 46 3 (CS03⁻ ∷ []) ∷
   re 48 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 47 q9 ∷
   rw 48 q16 ∷
   rw 49 q9 ∷
   re 47 3 (CS03⁻ ∷ []) ∷
   rw 48 q12 ∷
   re 50 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 49 q9 ∷
   rw 50 q17 ∷
   rw 51 q9 ∷
   re 49 3 (CK30⁻ ∷ []) ∷
   re 51 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 50 q9 ∷
   rw 51 q16 ∷
   rw 52 q9 ∷
   re 50 3 (CS03⁻ ∷ []) ∷
   re 52 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 51 q9 ∷
   rw 52 q16 ∷
   rw 53 q9 ∷
   re 51 3 (CS03⁻ ∷ []) ∷
   re 53 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 52 q9 ∷
   rw 53 q16 ∷
   rw 54 q9 ∷
   re 52 3 (CS03⁻ ∷ []) ∷
   rw 53 q18 ∷
   rw 54 q18 ∷
   rw 55 q18 ∷
   rw 56 q19 ∷
   rw 57 q18 ∷
   rw 58 q18 ∷
   rw 59 q20 ∷
   rw 83 q21 ∷
   rw 84 q22 ∷
   rw 85 q21 ∷
   rw 82 q21 ∷
   rw 83 q22 ∷
   rw 84 q21 ∷
   rw 81 q23 ∷
   rw 82 q24 ∷
   rw 83 q23 ∷
   rw 80 q21 ∷
   rw 81 q22 ∷
   rw 82 q21 ∷
   rw 79 q21 ∷
   rw 80 q22 ∷
   rw 81 q21 ∷
   rw 78 q21 ∷
   rw 79 q22 ∷
   rw 80 q21 ∷
   rw 77 q25 ∷
   rw 76 q21 ∷
   rw 77 q22 ∷
   rw 78 q21 ∷
   rw 75 q21 ∷
   rw 76 q22 ∷
   rw 77 q21 ∷
   rw 74 q21 ∷
   rw 75 q22 ∷
   rw 76 q21 ∷
   rw 73 q21 ∷
   rw 74 q22 ∷
   rw 75 q21 ∷
   rw 72 q21 ∷
   rw 73 q22 ∷
   rw 74 q21 ∷
   rw 71 q21 ∷
   rw 72 q22 ∷
   rw 73 q21 ∷
   rw 70 q21 ∷
   rw 71 q22 ∷
   rw 72 q21 ∷
   rw 69 q21 ∷
   rw 70 q22 ∷
   rw 71 q21 ∷
   rw 68 q21 ∷
   rw 69 q22 ∷
   rw 70 q21 ∷
   rw 67 q26 ∷
   rw 68 q27 ∷
   rw 69 q26 ∷
   rw 66 q23 ∷
   rw 67 q24 ∷
   rw 68 q23 ∷
   rw 65 q21 ∷
   rw 66 q22 ∷
   rw 67 q21 ∷
   rw 64 q21 ∷
   rw 65 q22 ∷
   rw 66 q21 ∷
   rw 63 q21 ∷
   rw 64 q22 ∷
   rw 65 q21 ∷
   rw 62 q21 ∷
   rw 63 q22 ∷
   rw 64 q21 ∷
   rw 61 q21 ∷
   rw 62 q22 ∷
   rw 63 q21 ∷
   rw 60 q21 ∷
   rw 61 q22 ∷
   rw 62 q21 ∷
   rw 59 q25 ∷
   rw 62 q8 ∷
   rw⁻ 61 q28 ∷
   rw⁻ 60 q29 ∷
   rw⁻ 59 q28 ∷
   rw 58 q13 ∷
   rw 57 q13 ∷
   rw 56 q14 ∷
   rw 55 q13 ∷
   rw 54 q13 ∷
   rw 53 q13 ∷
   rw 54 q30 ∷
   rw 53 q28 ∷
   rw 54 q29 ∷
   rw 55 q28 ∷
   rw 56 q18 ∷
   rw 57 q18 ∷
   rw 58 q18 ∷
   rw 59 q19 ∷
   rw 60 q18 ∷
   rw 61 q18 ∷
   rw 62 q20 ∷
   rw 56 q31 ∷
   rw 62 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (X2 ∷ CK20⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (wn 736 W)

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 CKd20 X2]: 1 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd20-X2 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd20-X2 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (X2 ∷ CK20⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 0 q33 ∷ []) Eq.refl

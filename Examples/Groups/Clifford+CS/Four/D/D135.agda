{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D135 (W : Ws) where

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
  q1 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q2 : Eqn
  q2 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q3 : Eqn
  q3 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q4 : Eqn
  q4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q5 : Eqn
  q5 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q6 : Eqn
  q6 = eqn (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) (wn 13 W)
  q7 : Eqn
  q7 = eqn (CS01⁻ ∷ CX32 ∷ []) (CX32 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₁₀))
  q8 : Eqn
  q8 = eqn (CX32 ∷ Sw12 ∷ []) (Sw12 ∷ CX31 ∷ []) (wn 78 W)
  q9 : Eqn
  q9 = eqn (CK10⁻ ∷ CX32 ∷ []) (CX32 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q10 : Eqn
  q10 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q12 : Eqn
  q12 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q13 : Eqn
  q13 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q14 : Eqn
  q14 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q15 : Eqn
  q15 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q16 : Eqn
  q16 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (wn 688 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CK21⁻ ∷ []) (CK20⁻ ∷ Sw01 ∷ []) (wn 139 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q20 : Eqn
  q20 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q21 : Eqn
  q21 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q22 : Eqn
  q22 = eqn (CK10 ∷ X2 ∷ []) (X2 ∷ CK10 ∷ []) (low-comm (CK₁₀) (X))
  q23 : Eqn
  q23 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q24 : Eqn
  q24 = eqn (CS01 ∷ X2 ∷ []) (X2 ∷ CS01 ∷ []) (low-comm (CS) (X))
  q25 : Eqn
  q25 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q26 : Eqn
  q26 = eqn (CX21 ∷ X2 ∷ CX23 ∷ X2 ∷ []) (X2 ∷ CX23 ∷ X2 ∷ CX21 ∷ []) (wn 612 W)
  q27 : Eqn
  q27 = eqn (S1 ∷ X2 ∷ []) (X2 ∷ S1 ∷ []) (low-comm ((S ↑)) (X))
  q28 : Eqn
  q28 = eqn (S1 ∷ CX23 ∷ []) (CX23 ∷ S1 ∷ []) (low-comm ((S ↑)) (CX₀₁))
  q29 : Eqn
  q29 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q30 : Eqn
  q30 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q31 : Eqn
  q31 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X2 ∷ CX23 ∷ X2 ∷ []) (X2 ∷ CX23 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (wn 613 W)
  q32 : Eqn
  q32 = eqn (S3⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S2⁻ ∷ []) (wn 689 W)
  q33 : Eqn
  q33 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (wn 576 W)
  q34 : Eqn
  q34 = eqn (Sw23 ∷ S2⁻ ∷ []) (S3⁻ ∷ Sw23 ∷ []) (wn 153 W)
  q35 : Eqn
  q35 = eqn (CX21 ∷ S3⁻ ∷ []) (S3⁻ ∷ CX21 ∷ []) (low₃-comm ((CX₁₀ ↑)) ((S • S • S)))
  q36 : Eqn
  q36 = eqn (CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (wn 577 W)

-- Bar(SSKSKK;2,1->0) passes white iX via V2 conjugates 3 part2: 500 steps
lem-Bar⟨SSKSKK21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part2 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CK10 ∷ S1 ∷ Sw23 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sw23 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ Sw23 ∷ Sw12 ∷ CX32 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part2 = derive (X2 ∷ CS23⁻ ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CK10 ∷ S1 ∷ Sw23 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sw23 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS23⁻ ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ Sw23 ∷ Sw12 ∷ CX32 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ [])
  (rw⁻ 48 q1 ∷
   rw⁻ 49 q2 ∷
   rw⁻ 50 q3 ∷
   rw⁻ 51 q3 ∷
   rw⁻ 52 q3 ∷
   rw⁻ 53 q1 ∷
   rw⁻ 54 q2 ∷
   rw⁻ 55 q3 ∷
   rw⁻ 56 q3 ∷
   rw⁻ 57 q3 ∷
   rw⁻ 58 q3 ∷
   rw⁻ 59 q3 ∷
   rw⁻ 60 q3 ∷
   rw 61 q4 ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q5 ∷
   re 42 3 (CX31 ∷ []) ∷
   rw 42 q6 ∷
   rw⁻ 43 q7 ∷
   rw 44 q8 ∷
   re 45 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 47 q4 ∷
   re 41 5 (CS03⁻ ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q5 ∷
   re 43 3 (CX31 ∷ []) ∷
   rw 43 q6 ∷
   rw⁻ 44 q9 ∷
   rw 45 q8 ∷
   re 46 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 48 q4 ∷
   re 42 5 (CK30⁻ ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q5 ∷
   re 44 3 (CX31 ∷ []) ∷
   rw 44 q6 ∷
   rw⁻ 45 q7 ∷
   rw 46 q8 ∷
   re 47 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 49 q4 ∷
   re 43 5 (CS03⁻ ∷ []) ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q5 ∷
   re 45 3 (CX31 ∷ []) ∷
   rw 45 q6 ∷
   rw⁻ 46 q7 ∷
   rw 47 q8 ∷
   re 48 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 50 q4 ∷
   re 44 5 (CS03⁻ ∷ []) ∷
   rw 45 q10 ∷
   re 44 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q11 ∷
   rw 45 q12 ∷
   rw⁻ 44 q11 ∷
   re 45 3 (CS13⁻ ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q11 ∷
   rw 44 q12 ∷
   rw⁻ 43 q11 ∷
   re 44 3 (CS13⁻ ∷ []) ∷
   re 42 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q11 ∷
   rw 43 q13 ∷
   rw⁻ 42 q11 ∷
   re 43 3 (CK31⁻ ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q11 ∷
   rw 42 q12 ∷
   rw⁻ 41 q11 ∷
   re 42 3 (CS13⁻ ∷ []) ∷
   rw 40 q14 ∷
   rw 39 q14 ∷
   rw 38 q15 ∷
   rw 37 q14 ∷
   rw 36 q15 ∷
   rw 35 q15 ∷
   rw 36 q16 ∷
   re 36 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 35 q11 ∷
   rw 36 q17 ∷
   rw 37 q11 ∷
   re 35 3 (CS03⁻ ∷ []) ∷
   re 37 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 36 q11 ∷
   rw 37 q18 ∷
   rw 38 q11 ∷
   re 36 3 (CK30⁻ ∷ []) ∷
   re 38 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 37 q11 ∷
   rw 38 q17 ∷
   rw 39 q11 ∷
   re 37 3 (CS03⁻ ∷ []) ∷
   re 39 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 38 q11 ∷
   rw 39 q17 ∷
   rw 40 q11 ∷
   re 38 3 (CS03⁻ ∷ []) ∷
   rw 39 q19 ∷
   rw 40 q19 ∷
   rw 41 q20 ∷
   rw 42 q19 ∷
   rw 43 q20 ∷
   rw 44 q20 ∷
   rw 45 q21 ∷
   rw 67 q22 ∷
   rw 68 q23 ∷
   rw 69 q22 ∷
   rw 66 q22 ∷
   rw 67 q23 ∷
   rw 68 q22 ∷
   rw 65 q24 ∷
   rw 66 q25 ∷
   rw 67 q24 ∷
   rw 64 q22 ∷
   rw 65 q23 ∷
   rw 66 q22 ∷
   rw 63 q24 ∷
   rw 64 q25 ∷
   rw 65 q24 ∷
   rw 62 q24 ∷
   rw 63 q25 ∷
   rw 64 q24 ∷
   rw 61 q26 ∷
   rw 60 q24 ∷
   rw 61 q25 ∷
   rw 62 q24 ∷
   rw 59 q24 ∷
   rw 60 q25 ∷
   rw 61 q24 ∷
   rw 58 q24 ∷
   rw 59 q25 ∷
   rw 60 q24 ∷
   rw 57 q24 ∷
   rw 58 q25 ∷
   rw 59 q24 ∷
   rw 56 q24 ∷
   rw 57 q25 ∷
   rw 58 q24 ∷
   rw 55 q24 ∷
   rw 56 q25 ∷
   rw 57 q24 ∷
   rw 54 q27 ∷
   rw 55 q28 ∷
   rw 56 q27 ∷
   rw 53 q22 ∷
   rw 54 q23 ∷
   rw 55 q22 ∷
   rw 52 q24 ∷
   rw 53 q25 ∷
   rw 54 q24 ∷
   rw 51 q24 ∷
   rw 52 q25 ∷
   rw 53 q24 ∷
   rw 50 q24 ∷
   rw 51 q25 ∷
   rw 52 q24 ∷
   rw 49 q27 ∷
   rw 50 q28 ∷
   rw 51 q27 ∷
   rw 48 q22 ∷
   rw 49 q23 ∷
   rw 50 q22 ∷
   rw 47 q27 ∷
   rw 48 q28 ∷
   rw 49 q27 ∷
   rw 46 q22 ∷
   rw 47 q23 ∷
   rw 48 q22 ∷
   rw 45 q26 ∷
   rw 48 q10 ∷
   rw⁻ 47 q29 ∷
   rw⁻ 46 q30 ∷
   rw⁻ 45 q29 ∷
   rw 44 q14 ∷
   rw 43 q14 ∷
   rw 42 q15 ∷
   rw 41 q14 ∷
   rw 40 q15 ∷
   rw 39 q15 ∷
   rw 40 q31 ∷
   rw 39 q29 ∷
   rw 40 q30 ∷
   rw 41 q29 ∷
   rw 42 q19 ∷
   rw 43 q19 ∷
   rw 44 q20 ∷
   rw 45 q19 ∷
   rw 46 q20 ∷
   rw 47 q20 ∷
   rw 48 q21 ∷
   rw 82 q5 ∷
   re 81 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 83 q4 ∷
   re 80 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 82 q4 ∷
   re 79 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 81 q4 ∷
   re 78 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 80 q4 ∷
   rw 77 q32 ∷
   re 76 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 78 q4 ∷
   re 75 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 77 q4 ∷
   re 74 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 76 q4 ∷
   re 73 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 75 q4 ∷
   re 72 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 74 q4 ∷
   re 71 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 73 q4 ∷
   rw 70 q1 ∷
   rw 69 q1 ∷
   rw 68 q3 ∷
   rw 67 q1 ∷
   rw 66 q3 ∷
   rw 65 q3 ∷
   rw 66 q33 ∷
   rw 67 q5 ∷
   re 65 3 (CS03⁻ ∷ []) ∷
   rw 68 q5 ∷
   re 66 3 (CS03⁻ ∷ []) ∷
   rw 69 q5 ∷
   re 67 3 (CS03⁻ ∷ []) ∷
   rw 70 q5 ∷
   re 68 3 (CS03⁻ ∷ []) ∷
   rw 71 q5 ∷
   re 69 3 (CS03⁻ ∷ []) ∷
   rw 72 q5 ∷
   re 70 3 (CS03⁻ ∷ []) ∷
   rw 71 q34 ∷
   rw 74 q5 ∷
   re 72 3 (CK30⁻ ∷ []) ∷
   rw 75 q5 ∷
   re 73 3 (CS03⁻ ∷ []) ∷
   rw 76 q5 ∷
   re 74 3 (CS03⁻ ∷ []) ∷
   rw 77 q5 ∷
   re 75 3 (CS03⁻ ∷ []) ∷
   rw⁻ 76 q3 ∷
   rw⁻ 77 q3 ∷
   rw⁻ 78 q1 ∷
   rw⁻ 79 q3 ∷
   rw⁻ 80 q1 ∷
   rw⁻ 81 q1 ∷
   rw 82 q4 ∷
   re 65 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 64 q5 ∷
   re 65 3 (CX31 ∷ []) ∷
   rw 65 q6 ∷
   rw⁻ 66 q7 ∷
   rw 67 q8 ∷
   re 68 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 70 q4 ∷
   re 64 5 (CS03⁻ ∷ []) ∷
   re 66 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 65 q5 ∷
   re 66 3 (CX31 ∷ []) ∷
   rw 66 q6 ∷
   rw⁻ 67 q7 ∷
   rw 68 q8 ∷
   re 69 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 71 q4 ∷
   re 65 5 (CS03⁻ ∷ []) ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 66 q5 ∷
   re 67 3 (CX31 ∷ []) ∷
   rw 67 q6 ∷
   rw⁻ 68 q7 ∷
   rw 69 q8 ∷
   re 70 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 72 q4 ∷
   re 66 5 (CS03⁻ ∷ []) ∷
   re 68 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 67 q5 ∷
   re 68 3 (CX31 ∷ []) ∷
   rw 68 q6 ∷
   rw⁻ 69 q7 ∷
   rw 70 q8 ∷
   re 71 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 73 q4 ∷
   re 67 5 (CS03⁻ ∷ []) ∷
   re 69 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 68 q5 ∷
   re 69 3 (CX31 ∷ []) ∷
   rw 69 q6 ∷
   rw⁻ 70 q7 ∷
   rw 71 q8 ∷
   re 72 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 74 q4 ∷
   re 68 5 (CS03⁻ ∷ []) ∷
   re 70 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 69 q5 ∷
   re 70 3 (CX31 ∷ []) ∷
   rw 70 q6 ∷
   rw⁻ 71 q7 ∷
   rw 72 q8 ∷
   re 73 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 75 q4 ∷
   re 69 5 (CS03⁻ ∷ []) ∷
   rw 70 q35 ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q5 ∷
   re 72 3 (CX31 ∷ []) ∷
   rw 72 q6 ∷
   rw⁻ 73 q9 ∷
   rw 74 q8 ∷
   re 75 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 77 q4 ∷
   re 71 5 (CK30⁻ ∷ []) ∷
   re 73 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 72 q5 ∷
   re 73 3 (CX31 ∷ []) ∷
   rw 73 q6 ∷
   rw⁻ 74 q7 ∷
   rw 75 q8 ∷
   re 76 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 78 q4 ∷
   re 72 5 (CS03⁻ ∷ []) ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q5 ∷
   re 74 3 (CX31 ∷ []) ∷
   rw 74 q6 ∷
   rw⁻ 75 q7 ∷
   rw 76 q8 ∷
   re 77 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 79 q4 ∷
   re 73 5 (CS03⁻ ∷ []) ∷
   re 75 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 74 q5 ∷
   re 75 3 (CX31 ∷ []) ∷
   rw 75 q6 ∷
   rw⁻ 76 q7 ∷
   rw 77 q8 ∷
   re 78 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 80 q4 ∷
   re 74 5 (CS03⁻ ∷ []) ∷
   rw 75 q5 ∷
   re 74 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 76 q4 ∷
   re 73 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 75 q4 ∷
   re 72 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 74 q4 ∷
   re 71 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 73 q4 ∷
   rw 70 q32 ∷
   re 69 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 71 q4 ∷
   re 68 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 70 q4 ∷
   re 67 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 69 q4 ∷
   re 66 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 68 q4 ∷
   re 65 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 67 q4 ∷
   re 64 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 66 q4 ∷
   rw 63 q3 ∷
   rw 62 q3 ∷
   rw 61 q3 ∷
   rw 60 q3 ∷
   rw 59 q3 ∷
   rw 58 q3 ∷
   rw 57 q2 ∷
   rw 56 q1 ∷
   rw 55 q3 ∷
   rw 54 q3 ∷
   rw 53 q3 ∷
   rw 52 q2 ∷
   rw 51 q1 ∷
   rw 50 q2 ∷
   rw 49 q1 ∷
   rw 50 q36 ∷
   rw 51 q5 ∷
   re 49 3 (CS03⁻ ∷ []) ∷
   rw 52 q5 ∷
   re 50 3 (CS03⁻ ∷ []) ∷
   rw 53 q5 ∷
   re 51 3 (CS03⁻ ∷ []) ∷
   rw 54 q5 ∷
   re 52 3 (CS03⁻ ∷ []) ∷
   rw 55 q5 ∷
   re 53 3 (CS03⁻ ∷ []) ∷
   rw 56 q5 ∷
   re 54 3 (CS03⁻ ∷ []) ∷
   rw 55 q34 ∷
   rw 58 q5 ∷
   re 56 3 (CK30⁻ ∷ []) ∷
   rw 59 q5 ∷
   re 57 3 (CS03⁻ ∷ []) ∷
   rw 60 q5 ∷
   re 58 3 (CS03⁻ ∷ []) ∷
   rw 61 q5 ∷
   re 59 3 (CS03⁻ ∷ []) ∷
   rw⁻ 60 q1 ∷
   rw⁻ 61 q2 ∷
   rw⁻ 62 q1 ∷
   rw⁻ 63 q2 ∷
   rw⁻ 64 q3 ∷
   rw⁻ 65 q3 ∷
   rw⁻ 66 q3 ∷
   rw⁻ 67 q1 ∷
   rw⁻ 68 q2 ∷
   rw⁻ 69 q3 ∷
   rw⁻ 70 q3 ∷
   rw⁻ 71 q3 ∷
   rw⁻ 72 q3 ∷
   rw⁻ 73 q3 ∷
   rw⁻ 74 q3 ∷
   rw 75 q4 ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q5 ∷
   re 49 3 (CX31 ∷ []) ∷
   rw 49 q6 ∷
   rw⁻ 50 q7 ∷
   rw 51 q8 ∷
   re 52 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 54 q4 ∷
   re 48 5 (CS03⁻ ∷ []) ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q5 ∷
   re 50 3 (CX31 ∷ []) ∷
   rw 50 q6 ∷
   rw⁻ 51 q7 ∷
   rw 52 q8 ∷
   re 53 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 55 q4 ∷
   re 49 5 (CS03⁻ ∷ []) ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q5 ∷
   re 51 3 (CX31 ∷ []) ∷
   rw 51 q6 ∷
   rw⁻ 52 q7 ∷
   rw 53 q8 ∷
   re 54 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 56 q4 ∷
   re 50 5 (CS03⁻ ∷ []) ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q5 ∷
   re 52 3 (CX31 ∷ []) ∷
   rw 52 q6 ∷
   rw⁻ 53 q7 ∷
   rw 54 q8 ∷
   re 55 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 57 q4 ∷
   re 51 5 (CS03⁻ ∷ []) ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q5 ∷
   re 53 3 (CX31 ∷ []) ∷
   rw 53 q6 ∷
   rw⁻ 54 q7 ∷
   rw 55 q8 ∷
   re 56 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 58 q4 ∷
   re 52 5 (CS03⁻ ∷ []) ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q5 ∷
   re 54 3 (CX31 ∷ []) ∷
   rw 54 q6 ∷
   rw⁻ 55 q7 ∷
   rw 56 q8 ∷
   re 57 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 59 q4 ∷
   re 53 5 (CS03⁻ ∷ []) ∷
   rw 54 q35 ∷
   re 56 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q5 ∷
   re 56 3 (CX31 ∷ []) ∷
   rw 56 q6 ∷
   rw⁻ 57 q9 ∷
   rw 58 q8 ∷
   re 59 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 61 q4 ∷
   re 55 5 (CK30⁻ ∷ []) ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q5 ∷
   re 57 3 (CX31 ∷ []) ∷
   rw 57 q6 ∷
   rw⁻ 58 q7 ∷
   rw 59 q8 ∷
   re 60 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 62 q4 ∷
   re 56 5 (CS03⁻ ∷ []) ∷
   re 58 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 57 q5 ∷
   re 58 3 (CX31 ∷ []) ∷
   rw 58 q6 ∷
   rw⁻ 59 q7 ∷
   rw 60 q8 ∷
   re 61 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 63 q4 ∷
   re 57 5 (CS03⁻ ∷ []) ∷
   re 59 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q5 ∷
   re 59 3 (CX31 ∷ []) ∷
   rw 59 q6 ∷ []) Eq.refl

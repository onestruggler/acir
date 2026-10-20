{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D147 (W : Ws) where

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
  q1 = eqn (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) (wn 13 W)
  q2 : Eqn
  q2 = eqn (CS01⁻ ∷ CX32 ∷ []) (CX32 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₁₀))
  q3 : Eqn
  q3 = eqn (CX32 ∷ Sw12 ∷ []) (Sw12 ∷ CX31 ∷ []) (wn 78 W)
  q4 : Eqn
  q4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q5 : Eqn
  q5 = eqn (CX21 ∷ S3⁻ ∷ []) (S3⁻ ∷ CX21 ∷ []) (low₃-comm ((CX₁₀ ↑)) ((S • S • S)))
  q6 : Eqn
  q6 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q7 : Eqn
  q7 = eqn (CK10⁻ ∷ CX32 ∷ []) (CX32 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q8 : Eqn
  q8 = eqn (S3⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S2⁻ ∷ []) (wn 689 W)
  q9 : Eqn
  q9 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q10 : Eqn
  q10 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q11 : Eqn
  q11 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q12 : Eqn
  q12 = eqn (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (wn 731 W)
  q13 : Eqn
  q13 = eqn (Sw23 ∷ S2⁻ ∷ []) (S3⁻ ∷ Sw23 ∷ []) (wn 153 W)
  q14 : Eqn
  q14 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q16 : Eqn
  q16 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q17 : Eqn
  q17 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q18 : Eqn
  q18 = eqn (Sw01 ∷ S3⁻ ∷ []) (S3⁻ ∷ Sw01 ∷ []) (low-comm (Swap) (((S • S • S) ↑)))
  q19 : Eqn
  q19 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q20 : Eqn
  q20 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q21 : Eqn
  q21 = eqn (CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) (wn 732 W)
  q22 : Eqn
  q22 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q23 : Eqn
  q23 = eqn (Sw01 ∷ CK21⁻ ∷ []) (CK20⁻ ∷ Sw01 ∷ []) (wn 139 W)
  q24 : Eqn
  q24 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q25 : Eqn
  q25 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q26 : Eqn
  q26 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q27 : Eqn
  q27 = eqn (CS01 ∷ X2 ∷ []) (X2 ∷ CS01 ∷ []) (low-comm (CS) (X))
  q28 : Eqn
  q28 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q29 : Eqn
  q29 = eqn (CK10 ∷ X2 ∷ []) (X2 ∷ CK10 ∷ []) (low-comm (CK₁₀) (X))
  q30 : Eqn
  q30 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q31 : Eqn
  q31 = eqn (CX21 ∷ X2 ∷ CX23 ∷ X2 ∷ []) (X2 ∷ CX23 ∷ X2 ∷ CX21 ∷ []) (wn 612 W)
  q32 : Eqn
  q32 = eqn (S1 ∷ X2 ∷ []) (X2 ∷ S1 ∷ []) (low-comm ((S ↑)) (X))
  q33 : Eqn
  q33 = eqn (S1 ∷ CX23 ∷ []) (CX23 ∷ S1 ∷ []) (low-comm ((S ↑)) (CX₀₁))
  q34 : Eqn
  q34 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q35 : Eqn
  q35 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q36 : Eqn
  q36 = eqn (CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X2 ∷ CX23 ∷ X2 ∷ []) (X2 ∷ CX23 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) (wn 661 W)
  q37 : Eqn
  q37 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (wn 733 W)
  q38 : Eqn
  q38 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ []) (X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (wn 734 W)
  q39 : Eqn
  q39 = eqn (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (wn 727 W)

-- Bar(SSSKSS;2,1->0) passes white iX via V2 conjugates 3 part1: 500 steps
lem-Bar⟨SSSKSS21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part1 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ Sw23 ∷ CX31 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sw23 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ Sw23 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part1 = derive (X2 ∷ CS23⁻ ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ Sw23 ∷ CX31 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS23⁻ ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sw23 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ Sw23 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ [])
  (rw 40 q1 ∷
   rw⁻ 41 q2 ∷
   rw 42 q3 ∷
   re 43 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 45 q4 ∷
   re 39 5 (CS03⁻ ∷ []) ∷
   rw 40 q5 ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q6 ∷
   re 42 3 (CX31 ∷ []) ∷
   rw 42 q1 ∷
   rw⁻ 43 q7 ∷
   rw 44 q3 ∷
   re 45 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 47 q4 ∷
   re 41 5 (CK30⁻ ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q6 ∷
   re 43 3 (CX31 ∷ []) ∷
   rw 43 q1 ∷
   rw⁻ 44 q2 ∷
   rw 45 q3 ∷
   re 46 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 48 q4 ∷
   re 42 5 (CS03⁻ ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q6 ∷
   re 44 3 (CX31 ∷ []) ∷
   rw 44 q1 ∷
   rw⁻ 45 q2 ∷
   rw 46 q3 ∷
   re 47 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 49 q4 ∷
   re 43 5 (CS03⁻ ∷ []) ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q6 ∷
   re 45 3 (CX31 ∷ []) ∷
   rw 45 q1 ∷
   rw⁻ 46 q2 ∷
   rw 47 q3 ∷
   re 48 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 50 q4 ∷
   re 44 5 (CS03⁻ ∷ []) ∷
   rw 45 q6 ∷
   re 44 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 46 q4 ∷
   re 43 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 45 q4 ∷
   re 42 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 44 q4 ∷
   re 41 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 43 q4 ∷
   rw 40 q8 ∷
   re 39 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 41 q4 ∷
   re 38 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 40 q4 ∷
   re 37 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 39 q4 ∷
   re 36 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 38 q4 ∷
   re 35 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 37 q4 ∷
   re 34 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 36 q4 ∷
   rw 33 q9 ∷
   rw 32 q9 ∷
   rw 31 q9 ∷
   rw 30 q9 ∷
   rw 29 q9 ∷
   rw 28 q9 ∷
   rw 27 q9 ∷
   rw 26 q9 ∷
   rw 25 q9 ∷
   rw 24 q10 ∷
   rw 23 q11 ∷
   rw 22 q9 ∷
   rw 21 q9 ∷
   rw 20 q9 ∷
   rw 19 q9 ∷
   rw 18 q9 ∷
   rw 17 q9 ∷
   rw 18 q12 ∷
   rw 19 q6 ∷
   re 17 3 (CS03⁻ ∷ []) ∷
   rw 20 q6 ∷
   re 18 3 (CS03⁻ ∷ []) ∷
   rw 21 q6 ∷
   re 19 3 (CS03⁻ ∷ []) ∷
   rw 22 q6 ∷
   re 20 3 (CS03⁻ ∷ []) ∷
   rw 23 q6 ∷
   re 21 3 (CS03⁻ ∷ []) ∷
   rw 24 q6 ∷
   re 22 3 (CS03⁻ ∷ []) ∷
   rw 23 q13 ∷
   rw 26 q6 ∷
   re 24 3 (CK30⁻ ∷ []) ∷
   rw 27 q6 ∷
   re 25 3 (CS03⁻ ∷ []) ∷
   rw 28 q6 ∷
   re 26 3 (CS03⁻ ∷ []) ∷
   rw 29 q6 ∷
   re 27 3 (CS03⁻ ∷ []) ∷
   rw⁻ 28 q9 ∷
   rw⁻ 29 q9 ∷
   rw⁻ 30 q9 ∷
   rw⁻ 31 q9 ∷
   rw⁻ 32 q9 ∷
   rw⁻ 33 q9 ∷
   rw⁻ 34 q11 ∷
   rw⁻ 35 q10 ∷
   rw⁻ 36 q9 ∷
   rw⁻ 37 q9 ∷
   rw⁻ 38 q9 ∷
   rw⁻ 39 q9 ∷
   rw⁻ 40 q9 ∷
   rw⁻ 41 q9 ∷
   rw⁻ 42 q9 ∷
   rw⁻ 43 q9 ∷
   rw⁻ 44 q9 ∷
   rw 45 q4 ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q6 ∷
   re 17 3 (CX31 ∷ []) ∷
   rw 17 q1 ∷
   rw⁻ 18 q2 ∷
   rw 19 q3 ∷
   re 20 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   re 16 5 (CS03⁻ ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q6 ∷
   re 18 3 (CX31 ∷ []) ∷
   rw 18 q1 ∷
   rw⁻ 19 q2 ∷
   rw 20 q3 ∷
   re 21 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 23 q4 ∷
   re 17 5 (CS03⁻ ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q6 ∷
   re 19 3 (CX31 ∷ []) ∷
   rw 19 q1 ∷
   rw⁻ 20 q2 ∷
   rw 21 q3 ∷
   re 22 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   re 18 5 (CS03⁻ ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q6 ∷
   re 20 3 (CX31 ∷ []) ∷
   rw 20 q1 ∷
   rw⁻ 21 q2 ∷
   rw 22 q3 ∷
   re 23 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   re 19 5 (CS03⁻ ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q6 ∷
   re 21 3 (CX31 ∷ []) ∷
   rw 21 q1 ∷
   rw⁻ 22 q2 ∷
   rw 23 q3 ∷
   re 24 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   re 20 5 (CS03⁻ ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   re 22 3 (CX31 ∷ []) ∷
   rw 22 q1 ∷
   rw⁻ 23 q2 ∷
   rw 24 q3 ∷
   re 25 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 27 q4 ∷
   re 21 5 (CS03⁻ ∷ []) ∷
   rw 22 q5 ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q6 ∷
   re 24 3 (CX31 ∷ []) ∷
   rw 24 q1 ∷
   rw⁻ 25 q7 ∷
   rw 26 q3 ∷
   re 27 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 29 q4 ∷
   re 23 5 (CK30⁻ ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   re 25 3 (CX31 ∷ []) ∷
   rw 25 q1 ∷
   rw⁻ 26 q2 ∷
   rw 27 q3 ∷
   re 28 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 30 q4 ∷
   re 24 5 (CS03⁻ ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q6 ∷
   re 26 3 (CX31 ∷ []) ∷
   rw 26 q1 ∷
   rw⁻ 27 q2 ∷
   rw 28 q3 ∷
   re 29 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 31 q4 ∷
   re 25 5 (CS03⁻ ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   re 27 3 (CX31 ∷ []) ∷
   rw 27 q1 ∷
   rw⁻ 28 q2 ∷
   rw 29 q3 ∷
   re 30 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 32 q4 ∷
   re 26 5 (CS03⁻ ∷ []) ∷
   rw 27 q14 ∷
   re 26 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q15 ∷
   rw 27 q16 ∷
   rw⁻ 26 q15 ∷
   re 27 3 (CS13⁻ ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q15 ∷
   rw 26 q16 ∷
   rw⁻ 25 q15 ∷
   re 26 3 (CS13⁻ ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q15 ∷
   rw 25 q16 ∷
   rw⁻ 24 q15 ∷
   re 25 3 (CS13⁻ ∷ []) ∷
   re 23 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q15 ∷
   rw 24 q17 ∷
   rw⁻ 23 q15 ∷
   re 24 3 (CK31⁻ ∷ []) ∷
   rw⁻ 22 q18 ∷
   re 21 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q15 ∷
   rw 22 q16 ∷
   rw⁻ 21 q15 ∷
   re 22 3 (CS13⁻ ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q15 ∷
   rw 21 q16 ∷
   rw⁻ 20 q15 ∷
   re 21 3 (CS13⁻ ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q15 ∷
   rw 20 q16 ∷
   rw⁻ 19 q15 ∷
   re 20 3 (CS13⁻ ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q15 ∷
   rw 19 q16 ∷
   rw⁻ 18 q15 ∷
   re 19 3 (CS13⁻ ∷ []) ∷
   re 17 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q15 ∷
   rw 18 q16 ∷
   rw⁻ 17 q15 ∷
   re 18 3 (CS13⁻ ∷ []) ∷
   re 16 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q15 ∷
   rw 17 q16 ∷
   rw⁻ 16 q15 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw 15 q19 ∷
   rw 14 q19 ∷
   rw 13 q20 ∷
   rw 12 q19 ∷
   rw 11 q19 ∷
   rw 10 q19 ∷
   rw 11 q21 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q15 ∷
   rw 11 q22 ∷
   rw 12 q15 ∷
   re 10 3 (CS03⁻ ∷ []) ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q15 ∷
   rw 12 q22 ∷
   rw 13 q15 ∷
   re 11 3 (CS03⁻ ∷ []) ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q15 ∷
   rw 13 q22 ∷
   rw 14 q15 ∷
   re 12 3 (CS03⁻ ∷ []) ∷
   re 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q15 ∷
   rw 14 q22 ∷
   rw 15 q15 ∷
   re 13 3 (CS03⁻ ∷ []) ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q15 ∷
   rw 15 q22 ∷
   rw 16 q15 ∷
   re 14 3 (CS03⁻ ∷ []) ∷
   re 16 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q15 ∷
   rw 16 q22 ∷
   rw 17 q15 ∷
   re 15 3 (CS03⁻ ∷ []) ∷
   rw 16 q18 ∷
   re 18 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q15 ∷
   rw 18 q23 ∷
   rw 19 q15 ∷
   re 17 3 (CK30⁻ ∷ []) ∷
   re 19 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q15 ∷
   rw 19 q22 ∷
   rw 20 q15 ∷
   re 18 3 (CS03⁻ ∷ []) ∷
   re 20 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q15 ∷
   rw 20 q22 ∷
   rw 21 q15 ∷
   re 19 3 (CS03⁻ ∷ []) ∷
   re 21 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q15 ∷
   rw 21 q22 ∷
   rw 22 q15 ∷
   re 20 3 (CS03⁻ ∷ []) ∷
   rw 21 q24 ∷
   rw 22 q24 ∷
   rw 23 q24 ∷
   rw 24 q25 ∷
   rw 25 q24 ∷
   rw 26 q24 ∷
   rw 27 q26 ∷
   rw 51 q27 ∷
   rw 52 q28 ∷
   rw 53 q27 ∷
   rw 50 q27 ∷
   rw 51 q28 ∷
   rw 52 q27 ∷
   rw 49 q29 ∷
   rw 50 q30 ∷
   rw 51 q29 ∷
   rw 48 q27 ∷
   rw 49 q28 ∷
   rw 50 q27 ∷
   rw 47 q27 ∷
   rw 48 q28 ∷
   rw 49 q27 ∷
   rw 46 q27 ∷
   rw 47 q28 ∷
   rw 48 q27 ∷
   rw 45 q31 ∷
   rw 44 q27 ∷
   rw 45 q28 ∷
   rw 46 q27 ∷
   rw 43 q27 ∷
   rw 44 q28 ∷
   rw 45 q27 ∷
   rw 42 q27 ∷
   rw 43 q28 ∷
   rw 44 q27 ∷
   rw 41 q27 ∷
   rw 42 q28 ∷
   rw 43 q27 ∷
   rw 40 q27 ∷
   rw 41 q28 ∷
   rw 42 q27 ∷
   rw 39 q27 ∷
   rw 40 q28 ∷
   rw 41 q27 ∷
   rw 38 q27 ∷
   rw 39 q28 ∷
   rw 40 q27 ∷
   rw 37 q27 ∷
   rw 38 q28 ∷
   rw 39 q27 ∷
   rw 36 q27 ∷
   rw 37 q28 ∷
   rw 38 q27 ∷
   rw 35 q32 ∷
   rw 36 q33 ∷
   rw 37 q32 ∷
   rw 34 q29 ∷
   rw 35 q30 ∷
   rw 36 q29 ∷
   rw 33 q27 ∷
   rw 34 q28 ∷
   rw 35 q27 ∷
   rw 32 q27 ∷
   rw 33 q28 ∷
   rw 34 q27 ∷
   rw 31 q27 ∷
   rw 32 q28 ∷
   rw 33 q27 ∷
   rw 30 q27 ∷
   rw 31 q28 ∷
   rw 32 q27 ∷
   rw 29 q27 ∷
   rw 30 q28 ∷
   rw 31 q27 ∷
   rw 28 q27 ∷
   rw 29 q28 ∷
   rw 30 q27 ∷
   rw 27 q31 ∷
   rw 30 q14 ∷
   rw⁻ 29 q34 ∷
   rw⁻ 28 q35 ∷
   rw⁻ 27 q34 ∷
   rw 26 q19 ∷
   rw 25 q19 ∷
   rw 24 q20 ∷
   rw 23 q19 ∷
   rw 22 q19 ∷
   rw 21 q19 ∷
   rw 22 q36 ∷
   rw 21 q34 ∷
   rw 22 q35 ∷
   rw 23 q34 ∷
   rw 24 q24 ∷
   rw 25 q24 ∷
   rw 26 q24 ∷
   rw 27 q25 ∷
   rw 28 q24 ∷
   rw 29 q24 ∷
   rw 30 q26 ∷
   rw 24 q37 ∷
   rw 30 q38 ∷
   rw 70 q6 ∷
   re 69 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 71 q4 ∷
   re 68 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 70 q4 ∷
   re 67 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 69 q4 ∷
   re 66 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 68 q4 ∷
   rw 65 q9 ∷
   rw 64 q9 ∷
   rw 63 q11 ∷
   rw 62 q9 ∷
   rw 61 q9 ∷
   rw 60 q9 ∷
   rw 61 q39 ∷
   rw 62 q6 ∷
   re 60 3 (CS03⁻ ∷ []) ∷
   rw 63 q6 ∷
   re 61 3 (CK30⁻ ∷ []) ∷
   rw 64 q6 ∷
   re 62 3 (CS03⁻ ∷ []) ∷
   rw 65 q6 ∷
   re 63 3 (CS03⁻ ∷ []) ∷
   rw⁻ 64 q9 ∷
   rw⁻ 65 q9 ∷
   rw⁻ 66 q9 ∷
   rw⁻ 67 q11 ∷
   rw⁻ 68 q9 ∷
   rw⁻ 69 q9 ∷
   rw 70 q4 ∷
   re 60 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q6 ∷
   re 60 3 (CX31 ∷ []) ∷
   rw 60 q1 ∷
   rw⁻ 61 q2 ∷
   rw 62 q3 ∷
   re 63 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 65 q4 ∷
   re 59 5 (CS03⁻ ∷ []) ∷
   re 61 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 60 q6 ∷
   re 61 3 (CX31 ∷ []) ∷
   rw 61 q1 ∷
   rw⁻ 62 q7 ∷
   rw 63 q3 ∷
   re 64 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 66 q4 ∷
   re 60 5 (CK30⁻ ∷ []) ∷
   re 62 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 61 q6 ∷
   re 62 3 (CX31 ∷ []) ∷
   rw 62 q1 ∷
   rw⁻ 63 q2 ∷
   rw 64 q3 ∷
   re 65 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 67 q4 ∷
   re 61 5 (CS03⁻ ∷ []) ∷
   re 63 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 62 q6 ∷
   re 63 3 (CX31 ∷ []) ∷
   rw 63 q1 ∷
   rw⁻ 64 q2 ∷
   rw 65 q3 ∷
   re 66 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 68 q4 ∷
   re 62 5 (CS03⁻ ∷ []) ∷
   rw 63 q6 ∷
   re 62 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 64 q4 ∷
   re 61 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 63 q4 ∷
   re 60 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 62 q4 ∷
   re 59 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 61 q4 ∷ []) Eq.refl

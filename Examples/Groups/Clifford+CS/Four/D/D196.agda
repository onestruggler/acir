{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D196 (W : Ws) where

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
  q1 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q2 : Eqn
  q2 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q3 : Eqn
  q3 = eqn (Sw01 ∷ S2⁻ ∷ []) (S2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • S • S)))
  q4 : Eqn
  q4 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q6 : Eqn
  q6 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q7 : Eqn
  q7 = eqn (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (wn 797 W)
  q8 : Eqn
  q8 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ CK21⁻ ∷ []) (CK20⁻ ∷ Sw01 ∷ []) (wn 139 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q13 : Eqn
  q13 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q14 : Eqn
  q14 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q15 : Eqn
  q15 = eqn (CK10 ∷ X3 ∷ []) (X3 ∷ CK10 ∷ []) (low-comm (CK₁₀) ((X ↑)))
  q16 : Eqn
  q16 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q17 : Eqn
  q17 = eqn (CX31 ∷ X3 ∷ CX32 ∷ X3 ∷ []) (X3 ∷ CX32 ∷ X3 ∷ CX31 ∷ []) (wn 537 W)
  q18 : Eqn
  q18 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q19 : Eqn
  q19 = eqn (S1 ∷ CX32 ∷ []) (CX32 ∷ S1 ∷ []) (low-comm ((S ↑)) (CX₁₀))
  q20 : Eqn
  q20 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q21 : Eqn
  q21 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q22 : Eqn
  q22 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q23 : Eqn
  q23 = eqn (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X3 ∷ CX32 ∷ X3 ∷ []) (X3 ∷ CX32 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (wn 796 W)
  q24 : Eqn
  q24 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q25 : Eqn
  q25 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q26 : Eqn
  q26 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q27 : Eqn
  q27 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q28 : Eqn
  q28 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q29 : Eqn
  q29 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q30 : Eqn
  q30 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (wn 733 W)
  q31 : Eqn
  q31 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q32 : Eqn
  q32 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ []) (X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (wn 734 W)
  q33 : Eqn
  q33 = eqn (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (wn 727 W)
  q34 : Eqn
  q34 = eqn (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) (wn 13 W)
  q35 : Eqn
  q35 = eqn (CS01⁻ ∷ CX32 ∷ []) (CX32 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₁₀))
  q36 : Eqn
  q36 = eqn (CX32 ∷ Sw12 ∷ []) (Sw12 ∷ CX31 ∷ []) (wn 78 W)
  q37 : Eqn
  q37 = eqn (CK10⁻ ∷ CX32 ∷ []) (CX32 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q38 : Eqn
  q38 = eqn (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (wn 728 W)
  q39 : Eqn
  q39 = eqn (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (wn 795 W)

-- Bar(SSSKSS;3,1->0) passes white iX via V2 conjugates 2 part1: 500 steps
lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part1 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ Sw01 ∷ CS12⁻ ∷ CS12⁻ ∷ Sw01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ Sw01 ∷ CS12⁻ ∷ CS12⁻ ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ Sw01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part1 = derive (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ Sw01 ∷ CS12⁻ ∷ CS12⁻ ∷ Sw01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ Sw01 ∷ CS12⁻ ∷ CS12⁻ ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ Sw01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 24 q1 ∷
   rw 23 q2 ∷
   rw⁻ 22 q3 ∷
   rw 21 q1 ∷
   rw 20 q1 ∷
   rw 19 q1 ∷
   rw 18 q1 ∷
   rw 17 q1 ∷
   rw 16 q1 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q4 ∷
   rw 16 q5 ∷
   rw⁻ 15 q4 ∷
   re 16 3 (CS13 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q4 ∷
   rw 15 q5 ∷
   rw⁻ 14 q4 ∷
   re 15 3 (CS13 ∷ []) ∷
   re 13 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q4 ∷
   rw 14 q6 ∷
   rw⁻ 13 q4 ∷
   re 14 3 (CK31 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q4 ∷
   rw 13 q5 ∷
   rw⁻ 12 q4 ∷
   re 13 3 (CS13 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q4 ∷
   rw 12 q5 ∷
   rw⁻ 11 q4 ∷
   re 12 3 (CS13 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q4 ∷
   rw 11 q5 ∷
   rw⁻ 10 q4 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 11 q7 ∷
   rw 10 q8 ∷
   rw 11 q8 ∷
   rw 12 q8 ∷
   rw 13 q8 ∷
   rw 14 q8 ∷
   rw 15 q8 ∷
   rw 16 q3 ∷
   rw 17 q9 ∷
   rw 18 q8 ∷
   rw 19 q8 ∷
   rw 20 q8 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q4 ∷
   rw 22 q10 ∷
   rw 23 q4 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   rw 23 q10 ∷
   rw 24 q4 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q4 ∷
   rw 24 q10 ∷
   rw 25 q4 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   rw 25 q11 ∷
   rw 26 q4 ∷
   re 24 3 (CK30 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   rw 26 q10 ∷
   rw 27 q4 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   rw 27 q10 ∷
   rw 28 q4 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 27 q12 ∷
   rw 51 q13 ∷
   rw 52 q14 ∷
   rw 53 q13 ∷
   rw 50 q13 ∷
   rw 51 q14 ∷
   rw 52 q13 ∷
   rw 49 q15 ∷
   rw 50 q16 ∷
   rw 51 q15 ∷
   rw 48 q13 ∷
   rw 49 q14 ∷
   rw 50 q13 ∷
   rw 47 q13 ∷
   rw 48 q14 ∷
   rw 49 q13 ∷
   rw 46 q13 ∷
   rw 47 q14 ∷
   rw 48 q13 ∷
   rw 45 q17 ∷
   rw 44 q13 ∷
   rw 45 q14 ∷
   rw 46 q13 ∷
   rw 43 q13 ∷
   rw 44 q14 ∷
   rw 45 q13 ∷
   rw 42 q13 ∷
   rw 43 q14 ∷
   rw 44 q13 ∷
   rw 41 q13 ∷
   rw 42 q14 ∷
   rw 43 q13 ∷
   rw 40 q13 ∷
   rw 41 q14 ∷
   rw 42 q13 ∷
   rw 39 q13 ∷
   rw 40 q14 ∷
   rw 41 q13 ∷
   rw 38 q13 ∷
   rw 39 q14 ∷
   rw 40 q13 ∷
   rw 37 q13 ∷
   rw 38 q14 ∷
   rw 39 q13 ∷
   rw 36 q13 ∷
   rw 37 q14 ∷
   rw 38 q13 ∷
   rw 35 q18 ∷
   rw 36 q19 ∷
   rw 37 q18 ∷
   rw 34 q15 ∷
   rw 35 q16 ∷
   rw 36 q15 ∷
   rw 33 q13 ∷
   rw 34 q14 ∷
   rw 35 q13 ∷
   rw 32 q13 ∷
   rw 33 q14 ∷
   rw 34 q13 ∷
   rw 31 q13 ∷
   rw 32 q14 ∷
   rw 33 q13 ∷
   rw 30 q13 ∷
   rw 31 q14 ∷
   rw 32 q13 ∷
   rw 29 q13 ∷
   rw 30 q14 ∷
   rw 31 q13 ∷
   rw 28 q13 ∷
   rw 29 q14 ∷
   rw 30 q13 ∷
   rw 27 q17 ∷
   rw 30 q20 ∷
   rw⁻ 29 q21 ∷
   rw⁻ 28 q22 ∷
   rw⁻ 27 q21 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q4 ∷
   rw 27 q5 ∷
   rw⁻ 26 q4 ∷
   re 27 3 (CS13 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q4 ∷
   rw 26 q5 ∷
   rw⁻ 25 q4 ∷
   re 26 3 (CS13 ∷ []) ∷
   re 24 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q4 ∷
   rw 25 q6 ∷
   rw⁻ 24 q4 ∷
   re 25 3 (CK31 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q4 ∷
   rw 24 q5 ∷
   rw⁻ 23 q4 ∷
   re 24 3 (CS13 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q4 ∷
   rw 23 q5 ∷
   rw⁻ 22 q4 ∷
   re 23 3 (CS13 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q4 ∷
   rw 22 q5 ∷
   rw⁻ 21 q4 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 22 q23 ∷
   rw 21 q21 ∷
   rw 22 q22 ∷
   rw 23 q21 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   rw 25 q10 ∷
   rw 26 q4 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   rw 26 q10 ∷
   rw 27 q4 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   rw 27 q10 ∷
   rw 28 q4 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 27 q4 ∷
   rw 28 q11 ∷
   rw 29 q4 ∷
   re 27 3 (CK30 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q4 ∷
   rw 29 q10 ∷
   rw 30 q4 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q4 ∷
   rw 30 q10 ∷
   rw 31 q4 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 30 q12 ∷
   rw 61 q24 ∷
   rw 60 q25 ∷
   re 59 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 61 q26 ∷
   re 58 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 60 q26 ∷
   re 57 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 59 q26 ∷
   re 56 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 58 q26 ∷
   rw 55 q25 ∷
   rw 54 q27 ∷
   rw 53 q27 ∷
   rw 52 q28 ∷
   rw 51 q27 ∷
   rw 50 q27 ∷
   rw 49 q27 ∷
   re 48 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 50 q26 ∷
   rw 47 q27 ∷
   rw 46 q27 ∷
   rw 45 q27 ∷
   rw 44 q27 ∷
   rw 43 q27 ∷
   rw 42 q27 ∷
   rw 41 q27 ∷
   rw 40 q27 ∷
   rw 39 q27 ∷
   rw 38 q29 ∷
   rw 37 q28 ∷
   rw 36 q27 ∷
   rw 35 q27 ∷
   rw 34 q27 ∷
   rw 33 q27 ∷
   rw 32 q27 ∷
   rw 31 q27 ∷
   re 30 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 32 q26 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q26 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q26 ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 29 q26 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q26 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q26 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q26 ∷
   rw 25 q30 ∷
   rw 24 q31 ∷
   rw 27 q24 ∷
   re 25 3 (CS03⁻ ∷ []) ∷
   rw 28 q24 ∷
   re 26 3 (CK30⁻ ∷ []) ∷
   rw 29 q24 ∷
   re 27 3 (CS03⁻ ∷ []) ∷
   rw 30 q24 ∷
   re 28 3 (CS03⁻ ∷ []) ∷
   rw 29 q31 ∷
   rw 32 q24 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 33 q24 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 34 q24 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 35 q24 ∷
   re 33 3 (CK30 ∷ []) ∷
   rw 36 q24 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 37 q24 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 38 q24 ∷
   re 36 3 (CX31 ∷ []) ∷
   rw⁻ 37 q27 ∷
   rw⁻ 38 q27 ∷
   rw⁻ 39 q27 ∷
   rw⁻ 40 q27 ∷
   rw⁻ 41 q27 ∷
   rw⁻ 42 q27 ∷
   rw⁻ 43 q28 ∷
   rw⁻ 44 q29 ∷
   rw⁻ 45 q27 ∷
   rw⁻ 46 q27 ∷
   rw⁻ 47 q27 ∷
   rw⁻ 48 q27 ∷
   rw⁻ 49 q27 ∷
   rw⁻ 50 q27 ∷
   rw⁻ 51 q27 ∷
   rw⁻ 52 q27 ∷
   rw⁻ 53 q27 ∷
   rw 56 q24 ∷
   re 54 3 (CX31 ∷ []) ∷
   rw⁻ 55 q27 ∷
   rw⁻ 56 q27 ∷
   rw⁻ 57 q27 ∷
   rw⁻ 58 q28 ∷
   rw⁻ 59 q27 ∷
   rw⁻ 60 q27 ∷
   rw 61 q26 ∷
   rw 66 q24 ∷
   rw 65 q25 ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 66 q26 ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 65 q26 ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 64 q26 ∷
   rw 61 q25 ∷
   rw 60 q27 ∷
   rw 59 q27 ∷
   rw 58 q28 ∷
   rw 57 q27 ∷
   rw 56 q27 ∷
   rw 55 q27 ∷
   re 54 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 56 q26 ∷
   rw 53 q27 ∷
   rw 52 q27 ∷
   rw 51 q27 ∷
   rw 50 q27 ∷
   rw 49 q27 ∷
   rw 48 q27 ∷
   rw 47 q27 ∷
   rw 46 q27 ∷
   rw 45 q27 ∷
   rw 44 q29 ∷
   rw 43 q28 ∷
   rw 42 q27 ∷
   rw 41 q27 ∷
   rw 40 q27 ∷
   rw 39 q27 ∷
   rw 38 q27 ∷
   rw 37 q27 ∷
   re 36 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 38 q26 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q26 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q26 ∷
   re 33 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 35 q26 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q26 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q26 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q26 ∷
   rw 31 q32 ∷
   rw 30 q31 ∷
   rw 33 q24 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 34 q24 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 35 q24 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 34 q31 ∷
   rw 37 q24 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 38 q24 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 39 q24 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 40 q24 ∷
   re 38 3 (CK30 ∷ []) ∷
   rw 41 q24 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 42 q24 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 43 q24 ∷
   re 41 3 (CX31 ∷ []) ∷
   rw⁻ 42 q27 ∷
   rw⁻ 43 q27 ∷
   rw⁻ 44 q27 ∷
   rw⁻ 45 q27 ∷
   rw⁻ 46 q27 ∷
   rw⁻ 47 q27 ∷
   rw⁻ 48 q28 ∷
   rw⁻ 49 q29 ∷
   rw⁻ 50 q27 ∷
   rw⁻ 51 q27 ∷
   rw⁻ 52 q27 ∷
   rw⁻ 53 q27 ∷
   rw⁻ 54 q27 ∷
   rw⁻ 55 q27 ∷
   rw⁻ 56 q27 ∷
   rw⁻ 57 q27 ∷
   rw⁻ 58 q27 ∷
   rw 61 q24 ∷
   re 59 3 (CX31 ∷ []) ∷
   rw⁻ 60 q27 ∷
   rw⁻ 61 q27 ∷
   rw⁻ 62 q27 ∷
   rw⁻ 63 q28 ∷
   rw⁻ 64 q27 ∷
   rw⁻ 65 q27 ∷
   rw 66 q26 ∷
   rw 60 q33 ∷
   re 60 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 59 q34 ∷
   rw⁻ 60 q35 ∷
   rw 61 q36 ∷
   re 59 3 (CS02⁻ ∷ []) ∷
   re 61 1 (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) ∷
   rw 60 q34 ∷
   rw⁻ 61 q37 ∷
   rw 62 q36 ∷
   re 60 3 (CK20⁻ ∷ []) ∷
   re 62 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 61 q34 ∷
   rw⁻ 62 q35 ∷
   rw 63 q36 ∷
   re 61 3 (CS02⁻ ∷ []) ∷
   re 63 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 62 q34 ∷
   rw⁻ 63 q35 ∷
   rw 64 q36 ∷
   re 62 3 (CS02⁻ ∷ []) ∷
   rw 42 q38 ∷
   re 42 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 41 q34 ∷
   rw⁻ 42 q35 ∷
   rw 43 q36 ∷
   re 41 3 (CS02⁻ ∷ []) ∷
   re 43 1 (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) ∷
   rw 42 q34 ∷
   rw⁻ 43 q37 ∷
   rw 44 q36 ∷
   re 42 3 (CK20⁻ ∷ []) ∷
   re 44 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 43 q34 ∷
   rw⁻ 44 q35 ∷
   rw 45 q36 ∷
   re 43 3 (CS02⁻ ∷ []) ∷
   re 45 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 44 q34 ∷
   rw⁻ 45 q35 ∷
   rw 46 q36 ∷
   re 44 3 (CS02⁻ ∷ []) ∷
   rw 45 q20 ∷
   rw 44 q1 ∷
   rw 43 q1 ∷
   rw 42 q2 ∷
   rw 41 q1 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q4 ∷
   rw 41 q5 ∷
   rw⁻ 40 q4 ∷
   re 41 3 (CS13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q4 ∷
   rw 40 q5 ∷
   rw⁻ 39 q4 ∷
   re 40 3 (CS13 ∷ []) ∷
   re 38 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q4 ∷
   rw 39 q6 ∷
   rw⁻ 38 q4 ∷
   re 39 3 (CK31 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q4 ∷
   rw 38 q5 ∷
   rw⁻ 37 q4 ∷
   re 38 3 (CS13 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q4 ∷
   rw 37 q5 ∷
   rw⁻ 36 q4 ∷
   re 37 3 (CS13 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q4 ∷
   rw 36 q5 ∷
   rw⁻ 35 q4 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 36 q39 ∷
   rw 35 q8 ∷
   rw 36 q9 ∷ []) Eq.refl

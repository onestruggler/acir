{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D197 (W : Ws) where

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
  q1 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q4 : Eqn
  q4 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q5 : Eqn
  q5 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q6 : Eqn
  q6 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q7 : Eqn
  q7 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q8 : Eqn
  q8 = eqn (CK10 ∷ X3 ∷ []) (X3 ∷ CK10 ∷ []) (low-comm (CK₁₀) ((X ↑)))
  q9 : Eqn
  q9 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q10 : Eqn
  q10 = eqn (CX31 ∷ X3 ∷ CX32 ∷ X3 ∷ []) (X3 ∷ CX32 ∷ X3 ∷ CX31 ∷ []) (wn 537 W)
  q11 : Eqn
  q11 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q12 : Eqn
  q12 = eqn (S1 ∷ CX32 ∷ []) (CX32 ∷ S1 ∷ []) (low-comm ((S ↑)) (CX₁₀))
  q13 : Eqn
  q13 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q15 : Eqn
  q15 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q16 : Eqn
  q16 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q17 : Eqn
  q17 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q18 : Eqn
  q18 = eqn (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X3 ∷ CX32 ∷ X3 ∷ []) (X3 ∷ CX32 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (wn 796 W)
  q19 : Eqn
  q19 = eqn (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (wn 730 W)
  q20 : Eqn
  q20 = eqn (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) (wn 13 W)
  q21 : Eqn
  q21 = eqn (CS01⁻ ∷ CX32 ∷ []) (CX32 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₁₀))
  q22 : Eqn
  q22 = eqn (CX32 ∷ Sw12 ∷ []) (Sw12 ∷ CX31 ∷ []) (wn 78 W)
  q23 : Eqn
  q23 = eqn (CX31 ∷ S2⁻ ∷ []) (S2⁻ ∷ CX31 ∷ []) (wn 540 W)
  q24 : Eqn
  q24 = eqn (CK10⁻ ∷ CX32 ∷ []) (CX32 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q25 : Eqn
  q25 = eqn (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (wn 731 W)
  q26 : Eqn
  q26 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q27 : Eqn
  q27 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q28 : Eqn
  q28 = eqn (Sw01 ∷ S2⁻ ∷ []) (S2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • S • S)))
  q29 : Eqn
  q29 = eqn (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (wn 797 W)
  q30 : Eqn
  q30 = eqn (Sw01 ∷ CK21⁻ ∷ []) (CK20⁻ ∷ Sw01 ∷ []) (wn 139 W)

-- Bar(SSSKSS;3,1->0) passes white iX via V2 conjugates 2 part2: 500 steps
lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part2 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ Sw01 ∷ CS12⁻ ∷ CS12⁻ ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ Sw01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part2 = derive (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ Sw01 ∷ CS12⁻ ∷ CS12⁻ ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ Sw01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 37 q1 ∷
   rw 38 q1 ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q2 ∷
   rw 40 q3 ∷
   rw 41 q2 ∷
   re 39 3 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q2 ∷
   rw 41 q3 ∷
   rw 42 q2 ∷
   re 40 3 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 41 q2 ∷
   rw 42 q3 ∷
   rw 43 q2 ∷
   re 41 3 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 42 q2 ∷
   rw 43 q4 ∷
   rw 44 q2 ∷
   re 42 3 (CK30 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q2 ∷
   rw 44 q3 ∷
   rw 45 q2 ∷
   re 43 3 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q2 ∷
   rw 45 q3 ∷
   rw 46 q2 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 45 q5 ∷
   rw 69 q6 ∷
   rw 70 q7 ∷
   rw 71 q6 ∷
   rw 68 q6 ∷
   rw 69 q7 ∷
   rw 70 q6 ∷
   rw 67 q8 ∷
   rw 68 q9 ∷
   rw 69 q8 ∷
   rw 66 q6 ∷
   rw 67 q7 ∷
   rw 68 q6 ∷
   rw 65 q6 ∷
   rw 66 q7 ∷
   rw 67 q6 ∷
   rw 64 q6 ∷
   rw 65 q7 ∷
   rw 66 q6 ∷
   rw 63 q10 ∷
   rw 62 q6 ∷
   rw 63 q7 ∷
   rw 64 q6 ∷
   rw 61 q6 ∷
   rw 62 q7 ∷
   rw 63 q6 ∷
   rw 60 q6 ∷
   rw 61 q7 ∷
   rw 62 q6 ∷
   rw 59 q6 ∷
   rw 60 q7 ∷
   rw 61 q6 ∷
   rw 58 q6 ∷
   rw 59 q7 ∷
   rw 60 q6 ∷
   rw 57 q6 ∷
   rw 58 q7 ∷
   rw 59 q6 ∷
   rw 56 q6 ∷
   rw 57 q7 ∷
   rw 58 q6 ∷
   rw 55 q6 ∷
   rw 56 q7 ∷
   rw 57 q6 ∷
   rw 54 q6 ∷
   rw 55 q7 ∷
   rw 56 q6 ∷
   rw 53 q11 ∷
   rw 54 q12 ∷
   rw 55 q11 ∷
   rw 52 q8 ∷
   rw 53 q9 ∷
   rw 54 q8 ∷
   rw 51 q6 ∷
   rw 52 q7 ∷
   rw 53 q6 ∷
   rw 50 q6 ∷
   rw 51 q7 ∷
   rw 52 q6 ∷
   rw 49 q6 ∷
   rw 50 q7 ∷
   rw 51 q6 ∷
   rw 48 q6 ∷
   rw 49 q7 ∷
   rw 50 q6 ∷
   rw 47 q6 ∷
   rw 48 q7 ∷
   rw 49 q6 ∷
   rw 46 q6 ∷
   rw 47 q7 ∷
   rw 48 q6 ∷
   rw 45 q10 ∷
   rw 48 q13 ∷
   rw⁻ 47 q14 ∷
   rw⁻ 46 q15 ∷
   rw⁻ 45 q14 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q2 ∷
   rw 45 q16 ∷
   rw⁻ 44 q2 ∷
   re 45 3 (CS13 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q2 ∷
   rw 44 q16 ∷
   rw⁻ 43 q2 ∷
   re 44 3 (CS13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q2 ∷
   rw 43 q17 ∷
   rw⁻ 42 q2 ∷
   re 43 3 (CK31 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q2 ∷
   rw 42 q16 ∷
   rw⁻ 41 q2 ∷
   re 42 3 (CS13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q2 ∷
   rw 41 q16 ∷
   rw⁻ 40 q2 ∷
   re 41 3 (CS13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q2 ∷
   rw 40 q16 ∷
   rw⁻ 39 q2 ∷
   re 40 3 (CS13 ∷ []) ∷
   rw 40 q18 ∷
   rw 39 q14 ∷
   rw 40 q15 ∷
   rw 41 q14 ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q2 ∷
   rw 43 q3 ∷
   rw 44 q2 ∷
   re 42 3 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q2 ∷
   rw 44 q3 ∷
   rw 45 q2 ∷
   re 43 3 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q2 ∷
   rw 45 q3 ∷
   rw 46 q2 ∷
   re 44 3 (CS03 ∷ []) ∷
   re 46 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 45 q2 ∷
   rw 46 q4 ∷
   rw 47 q2 ∷
   re 45 3 (CK30 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 46 q2 ∷
   rw 47 q3 ∷
   rw 48 q2 ∷
   re 46 3 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q2 ∷
   rw 48 q3 ∷
   rw 49 q2 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 48 q5 ∷
   rw 67 q19 ∷
   re 67 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 66 q20 ∷
   rw⁻ 67 q21 ∷
   rw 68 q22 ∷
   re 66 3 (CS02⁻ ∷ []) ∷
   re 68 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 67 q20 ∷
   rw⁻ 68 q21 ∷
   rw 69 q22 ∷
   re 67 3 (CS02⁻ ∷ []) ∷
   re 69 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 68 q20 ∷
   rw⁻ 69 q21 ∷
   rw 70 q22 ∷
   re 68 3 (CS02⁻ ∷ []) ∷
   re 70 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 69 q20 ∷
   rw⁻ 70 q21 ∷
   rw 71 q22 ∷
   re 69 3 (CS02⁻ ∷ []) ∷
   re 71 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 70 q20 ∷
   rw⁻ 71 q21 ∷
   rw 72 q22 ∷
   re 70 3 (CS02⁻ ∷ []) ∷
   re 72 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 71 q20 ∷
   rw⁻ 72 q21 ∷
   rw 73 q22 ∷
   re 71 3 (CS02⁻ ∷ []) ∷
   rw 72 q23 ∷
   re 74 1 (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) ∷
   rw 73 q20 ∷
   rw⁻ 74 q24 ∷
   rw 75 q22 ∷
   re 73 3 (CK20⁻ ∷ []) ∷
   re 75 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 74 q20 ∷
   rw⁻ 75 q21 ∷
   rw 76 q22 ∷
   re 74 3 (CS02⁻ ∷ []) ∷
   re 76 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 75 q20 ∷
   rw⁻ 76 q21 ∷
   rw 77 q22 ∷
   re 75 3 (CS02⁻ ∷ []) ∷
   re 77 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 76 q20 ∷
   rw⁻ 77 q21 ∷
   rw 78 q22 ∷
   re 76 3 (CS02⁻ ∷ []) ∷
   rw 49 q25 ∷
   re 49 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 48 q20 ∷
   rw⁻ 49 q21 ∷
   rw 50 q22 ∷
   re 48 3 (CS02⁻ ∷ []) ∷
   re 50 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 49 q20 ∷
   rw⁻ 50 q21 ∷
   rw 51 q22 ∷
   re 49 3 (CS02⁻ ∷ []) ∷
   re 51 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 50 q20 ∷
   rw⁻ 51 q21 ∷
   rw 52 q22 ∷
   re 50 3 (CS02⁻ ∷ []) ∷
   re 52 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 51 q20 ∷
   rw⁻ 52 q21 ∷
   rw 53 q22 ∷
   re 51 3 (CS02⁻ ∷ []) ∷
   re 53 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 52 q20 ∷
   rw⁻ 53 q21 ∷
   rw 54 q22 ∷
   re 52 3 (CS02⁻ ∷ []) ∷
   re 54 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 53 q20 ∷
   rw⁻ 54 q21 ∷
   rw 55 q22 ∷
   re 53 3 (CS02⁻ ∷ []) ∷
   rw 54 q23 ∷
   re 56 1 (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) ∷
   rw 55 q20 ∷
   rw⁻ 56 q24 ∷
   rw 57 q22 ∷
   re 55 3 (CK20⁻ ∷ []) ∷
   re 57 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 56 q20 ∷
   rw⁻ 57 q21 ∷
   rw 58 q22 ∷
   re 56 3 (CS02⁻ ∷ []) ∷
   re 58 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 57 q20 ∷
   rw⁻ 58 q21 ∷
   rw 59 q22 ∷
   re 57 3 (CS02⁻ ∷ []) ∷
   re 59 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 58 q20 ∷
   rw⁻ 59 q21 ∷
   rw 60 q22 ∷
   re 58 3 (CS02⁻ ∷ []) ∷
   rw 59 q13 ∷
   rw 58 q26 ∷
   rw 57 q26 ∷
   rw 56 q26 ∷
   rw 55 q27 ∷
   rw⁻ 54 q28 ∷
   rw 53 q26 ∷
   rw 52 q26 ∷
   rw 51 q26 ∷
   rw 50 q26 ∷
   rw 49 q26 ∷
   rw 48 q26 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q2 ∷
   rw 48 q16 ∷
   rw⁻ 47 q2 ∷
   re 48 3 (CS13 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q2 ∷
   rw 47 q16 ∷
   rw⁻ 46 q2 ∷
   re 47 3 (CS13 ∷ []) ∷
   re 45 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q2 ∷
   rw 46 q17 ∷
   rw⁻ 45 q2 ∷
   re 46 3 (CK31 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q2 ∷
   rw 45 q16 ∷
   rw⁻ 44 q2 ∷
   re 45 3 (CS13 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q2 ∷
   rw 44 q16 ∷
   rw⁻ 43 q2 ∷
   re 44 3 (CS13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q2 ∷
   rw 43 q16 ∷
   rw⁻ 42 q2 ∷
   re 43 3 (CS13 ∷ []) ∷
   rw 43 q29 ∷
   rw 42 q1 ∷
   rw 43 q1 ∷
   rw 44 q1 ∷
   rw 45 q1 ∷
   rw 46 q1 ∷
   rw 47 q1 ∷
   rw 48 q28 ∷
   rw 49 q30 ∷
   rw 50 q1 ∷
   rw 51 q1 ∷
   rw 52 q1 ∷
   re 54 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 53 q2 ∷
   rw 54 q3 ∷
   rw 55 q2 ∷
   re 53 3 (CS03 ∷ []) ∷
   re 55 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 54 q2 ∷
   rw 55 q3 ∷
   rw 56 q2 ∷
   re 54 3 (CS03 ∷ []) ∷
   re 56 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 55 q2 ∷
   rw 56 q3 ∷
   rw 57 q2 ∷
   re 55 3 (CS03 ∷ []) ∷
   re 57 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 56 q2 ∷
   rw 57 q4 ∷
   rw 58 q2 ∷
   re 56 3 (CK30 ∷ []) ∷
   re 58 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 57 q2 ∷
   rw 58 q3 ∷
   rw 59 q2 ∷
   re 57 3 (CS03 ∷ []) ∷
   re 59 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 58 q2 ∷
   rw 59 q3 ∷
   rw 60 q2 ∷
   re 58 3 (CS03 ∷ []) ∷
   rw 59 q5 ∷
   rw 83 q6 ∷
   rw 84 q7 ∷
   rw 85 q6 ∷
   rw 82 q6 ∷
   rw 83 q7 ∷
   rw 84 q6 ∷
   rw 81 q8 ∷
   rw 82 q9 ∷
   rw 83 q8 ∷
   rw 80 q6 ∷
   rw 81 q7 ∷
   rw 82 q6 ∷
   rw 79 q6 ∷
   rw 80 q7 ∷
   rw 81 q6 ∷
   rw 78 q6 ∷
   rw 79 q7 ∷
   rw 80 q6 ∷
   rw 77 q10 ∷
   rw 76 q6 ∷
   rw 77 q7 ∷
   rw 78 q6 ∷
   rw 75 q6 ∷
   rw 76 q7 ∷
   rw 77 q6 ∷
   rw 74 q6 ∷
   rw 75 q7 ∷
   rw 76 q6 ∷
   rw 73 q6 ∷
   rw 74 q7 ∷
   rw 75 q6 ∷
   rw 72 q6 ∷
   rw 73 q7 ∷
   rw 74 q6 ∷
   rw 71 q6 ∷
   rw 72 q7 ∷
   rw 73 q6 ∷
   rw 70 q6 ∷
   rw 71 q7 ∷
   rw 72 q6 ∷
   rw 69 q6 ∷
   rw 70 q7 ∷
   rw 71 q6 ∷
   rw 68 q6 ∷
   rw 69 q7 ∷
   rw 70 q6 ∷
   rw 67 q11 ∷
   rw 68 q12 ∷
   rw 69 q11 ∷
   rw 66 q8 ∷
   rw 67 q9 ∷
   rw 68 q8 ∷
   rw 65 q6 ∷
   rw 66 q7 ∷
   rw 67 q6 ∷
   rw 64 q6 ∷
   rw 65 q7 ∷
   rw 66 q6 ∷
   rw 63 q6 ∷
   rw 64 q7 ∷
   rw 65 q6 ∷
   rw 62 q6 ∷
   rw 63 q7 ∷
   rw 64 q6 ∷
   rw 61 q6 ∷
   rw 62 q7 ∷
   rw 63 q6 ∷
   rw 60 q6 ∷
   rw 61 q7 ∷
   rw 62 q6 ∷
   rw 59 q10 ∷
   rw 62 q13 ∷
   rw⁻ 61 q14 ∷
   rw⁻ 60 q15 ∷
   rw⁻ 59 q14 ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 60 q2 ∷
   rw 59 q16 ∷
   rw⁻ 58 q2 ∷
   re 59 3 (CS13 ∷ []) ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 59 q2 ∷
   rw 58 q16 ∷
   rw⁻ 57 q2 ∷
   re 58 3 (CS13 ∷ []) ∷
   re 56 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 58 q2 ∷
   rw 57 q17 ∷
   rw⁻ 56 q2 ∷
   re 57 3 (CK31 ∷ []) ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 57 q2 ∷
   rw 56 q16 ∷
   rw⁻ 55 q2 ∷
   re 56 3 (CS13 ∷ []) ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 56 q2 ∷
   rw 55 q16 ∷
   rw⁻ 54 q2 ∷
   re 55 3 (CS13 ∷ []) ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 55 q2 ∷
   rw 54 q16 ∷
   rw⁻ 53 q2 ∷
   re 54 3 (CS13 ∷ []) ∷
   rw 54 q18 ∷
   rw 53 q14 ∷
   rw 54 q15 ∷
   rw 55 q14 ∷
   re 57 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 56 q2 ∷
   rw 57 q3 ∷
   rw 58 q2 ∷
   re 56 3 (CS03 ∷ []) ∷
   re 58 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 57 q2 ∷
   rw 58 q3 ∷
   rw 59 q2 ∷
   re 57 3 (CS03 ∷ []) ∷
   re 59 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 58 q2 ∷
   rw 59 q3 ∷
   rw 60 q2 ∷
   re 58 3 (CS03 ∷ []) ∷
   re 60 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 59 q2 ∷
   rw 60 q4 ∷
   rw 61 q2 ∷
   re 59 3 (CK30 ∷ []) ∷
   re 61 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 60 q2 ∷
   rw 61 q3 ∷
   rw 62 q2 ∷
   re 60 3 (CS03 ∷ []) ∷
   re 62 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 61 q2 ∷
   rw 62 q3 ∷
   rw 63 q2 ∷ []) Eq.refl

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D163 (W : Ws) where

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
  q1 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q2 : Eqn
  q2 = eqn (Sw12 ∷ CX32 ∷ []) (CX31 ∷ Sw12 ∷ []) (wn 114 W)
  q3 : Eqn
  q3 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q4 : Eqn
  q4 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q5 : Eqn
  q5 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q8 : Eqn
  q8 = eqn (CK31 ∷ X2 ∷ []) (X2 ∷ CK31 ∷ []) (wn 630 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q11 : Eqn
  q11 = eqn (CX23 ∷ X2 ∷ CX21 ∷ X2 ∷ []) (X2 ∷ CX21 ∷ X2 ∷ CX23 ∷ []) (wn 673 W)
  q12 : Eqn
  q12 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ CX21 ∷ X2 ∷ []) (X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (wn 488 W)
  q13 : Eqn
  q13 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q14 : Eqn
  q14 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q15 : Eqn
  q15 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q16 : Eqn
  q16 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q17 : Eqn
  q17 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q18 : Eqn
  q18 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) (wn 740 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q20 : Eqn
  q20 = eqn (Sw01 ∷ CK21⁻ ∷ []) (CK20⁻ ∷ Sw01 ∷ []) (wn 139 W)
  q21 : Eqn
  q21 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q22 : Eqn
  q22 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) (wn 742 W)

-- Bar(SSKSKK;2,3->0) passes white iX via V2 conjugates 1 part9: 454 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part9 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ CX32 ∷ Sw12 ∷ Sw23 ∷ X2 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part9 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ CX32 ∷ Sw12 ∷ Sw23 ∷ X2 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 63 q1 ∷
   rw 62 q2 ∷
   re 62 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 61 q3 ∷
   re 62 5 (CK30 ∷ []) ∷
   rw 64 q4 ∷
   rw⁻ 63 q5 ∷
   re 62 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 64 q6 ∷
   rw 63 q7 ∷
   rw⁻ 62 q6 ∷
   re 63 3 (CK31 ∷ []) ∷
   rw 63 q8 ∷
   rw 62 q5 ∷
   re 64 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 63 q6 ∷
   rw 64 q9 ∷
   rw 65 q6 ∷
   re 63 3 (CK30 ∷ []) ∷
   rw 64 q10 ∷
   rw 59 q11 ∷
   rw 53 q12 ∷
   rw 91 q4 ∷
   rw⁻ 90 q5 ∷
   rw 89 q13 ∷
   rw 88 q13 ∷
   rw 87 q14 ∷
   rw 86 q13 ∷
   rw⁻ 85 q5 ∷
   re 84 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 86 q6 ∷
   rw 85 q7 ∷
   rw⁻ 84 q6 ∷
   re 85 3 (CK31 ∷ []) ∷
   re 83 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 85 q6 ∷
   rw 84 q7 ∷
   rw⁻ 83 q6 ∷
   re 84 3 (CK31 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 84 q6 ∷
   rw 83 q15 ∷
   rw⁻ 82 q6 ∷
   re 83 3 (CS13 ∷ []) ∷
   re 81 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 83 q6 ∷
   rw 82 q7 ∷
   rw⁻ 81 q6 ∷
   re 82 3 (CK31 ∷ []) ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 82 q6 ∷
   rw 81 q15 ∷
   rw⁻ 80 q6 ∷
   re 81 3 (CS13 ∷ []) ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 81 q6 ∷
   rw 80 q15 ∷
   rw⁻ 79 q6 ∷
   re 80 3 (CS13 ∷ []) ∷
   rw⁻ 78 q16 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 79 q6 ∷
   rw 78 q15 ∷
   rw⁻ 77 q6 ∷
   re 78 3 (CS13 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 78 q6 ∷
   rw 77 q15 ∷
   rw⁻ 76 q6 ∷
   re 77 3 (CS13 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 77 q6 ∷
   rw 76 q15 ∷
   rw⁻ 75 q6 ∷
   re 76 3 (CS13 ∷ []) ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 76 q6 ∷
   rw 75 q15 ∷
   rw⁻ 74 q6 ∷
   re 75 3 (CS13 ∷ []) ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 75 q6 ∷
   rw 74 q15 ∷
   rw⁻ 73 q6 ∷
   re 74 3 (CS13 ∷ []) ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 74 q6 ∷
   rw 73 q15 ∷
   rw⁻ 72 q6 ∷
   re 73 3 (CS13 ∷ []) ∷
   rw⁻ 71 q17 ∷
   re 70 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 72 q6 ∷
   rw 71 q7 ∷
   rw⁻ 70 q6 ∷
   re 71 3 (CK31 ∷ []) ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 71 q6 ∷
   rw 70 q15 ∷
   rw⁻ 69 q6 ∷
   re 70 3 (CS13 ∷ []) ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 70 q6 ∷
   rw 69 q15 ∷
   rw⁻ 68 q6 ∷
   re 69 3 (CS13 ∷ []) ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 69 q6 ∷
   rw 68 q15 ∷
   rw⁻ 67 q6 ∷
   re 68 3 (CS13 ∷ []) ∷
   rw⁻ 66 q17 ∷
   re 65 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 67 q6 ∷
   rw 66 q7 ∷
   rw⁻ 65 q6 ∷
   re 66 3 (CK31 ∷ []) ∷
   rw⁻ 64 q17 ∷
   re 63 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 65 q6 ∷
   rw 64 q7 ∷
   rw⁻ 63 q6 ∷
   re 64 3 (CK31 ∷ []) ∷
   rw⁻ 62 q16 ∷
   rw 61 q7 ∷
   rw 60 q7 ∷
   rw 59 q15 ∷
   rw 58 q7 ∷
   rw 57 q15 ∷
   rw 56 q15 ∷
   rw 57 q18 ∷
   rw 56 q5 ∷
   rw 57 q19 ∷
   rw 58 q20 ∷
   rw 59 q19 ∷
   rw 60 q19 ∷
   rw 61 q5 ∷
   rw 62 q21 ∷
   rw 63 q21 ∷
   rw 64 q9 ∷
   rw 65 q21 ∷
   rw 66 q9 ∷
   rw 67 q9 ∷
   rw 68 q16 ∷
   re 70 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 69 q6 ∷
   rw 70 q9 ∷
   rw 71 q6 ∷
   re 69 3 (CK30 ∷ []) ∷
   rw 70 q17 ∷
   re 72 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 71 q6 ∷
   rw 72 q9 ∷
   rw 73 q6 ∷
   re 71 3 (CK30 ∷ []) ∷
   rw 72 q17 ∷
   re 74 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 73 q6 ∷
   rw 74 q21 ∷
   rw 75 q6 ∷
   re 73 3 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 74 q6 ∷
   rw 75 q21 ∷
   rw 76 q6 ∷
   re 74 3 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 75 q6 ∷
   rw 76 q21 ∷
   rw 77 q6 ∷
   re 75 3 (CS03 ∷ []) ∷
   re 77 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 76 q6 ∷
   rw 77 q9 ∷
   rw 78 q6 ∷
   re 76 3 (CK30 ∷ []) ∷
   rw 77 q17 ∷
   re 79 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 78 q6 ∷
   rw 79 q21 ∷
   rw 80 q6 ∷
   re 78 3 (CS03 ∷ []) ∷
   re 80 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 79 q6 ∷
   rw 80 q21 ∷
   rw 81 q6 ∷
   re 79 3 (CS03 ∷ []) ∷
   re 81 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 80 q6 ∷
   rw 81 q21 ∷
   rw 82 q6 ∷
   re 80 3 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 81 q6 ∷
   rw 82 q21 ∷
   rw 83 q6 ∷
   re 81 3 (CS03 ∷ []) ∷
   re 83 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 82 q6 ∷
   rw 83 q21 ∷
   rw 84 q6 ∷
   re 82 3 (CS03 ∷ []) ∷
   re 84 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 83 q6 ∷
   rw 84 q21 ∷
   rw 85 q6 ∷
   re 83 3 (CS03 ∷ []) ∷
   rw 84 q16 ∷
   re 86 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 85 q6 ∷
   rw 86 q21 ∷
   rw 87 q6 ∷
   re 85 3 (CS03 ∷ []) ∷
   re 87 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 86 q6 ∷
   rw 87 q21 ∷
   rw 88 q6 ∷
   re 86 3 (CS03 ∷ []) ∷
   re 88 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 87 q6 ∷
   rw 88 q9 ∷
   rw 89 q6 ∷
   re 87 3 (CK30 ∷ []) ∷
   re 89 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 88 q6 ∷
   rw 89 q21 ∷
   rw 90 q6 ∷
   re 88 3 (CS03 ∷ []) ∷
   re 90 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 89 q6 ∷
   rw 90 q9 ∷
   rw 91 q6 ∷
   re 89 3 (CK30 ∷ []) ∷
   re 91 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 90 q6 ∷
   rw 91 q9 ∷
   rw 92 q6 ∷
   re 90 3 (CK30 ∷ []) ∷
   rw 91 q10 ∷
   rw 96 q4 ∷
   rw⁻ 95 q5 ∷
   rw 94 q13 ∷
   rw 93 q13 ∷
   rw 92 q13 ∷
   rw⁻ 91 q5 ∷
   re 90 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 92 q6 ∷
   rw 91 q7 ∷
   rw⁻ 90 q6 ∷
   re 91 3 (CK31 ∷ []) ∷
   re 89 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 91 q6 ∷
   rw 90 q7 ∷
   rw⁻ 89 q6 ∷
   re 90 3 (CK31 ∷ []) ∷
   re 88 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 90 q6 ∷
   rw 89 q15 ∷
   rw⁻ 88 q6 ∷
   re 89 3 (CS13 ∷ []) ∷
   re 87 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 89 q6 ∷
   rw 88 q7 ∷
   rw⁻ 87 q6 ∷
   re 88 3 (CK31 ∷ []) ∷
   re 86 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 88 q6 ∷
   rw 87 q15 ∷
   rw⁻ 86 q6 ∷
   re 87 3 (CS13 ∷ []) ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 87 q6 ∷
   rw 86 q15 ∷
   rw⁻ 85 q6 ∷
   re 86 3 (CS13 ∷ []) ∷
   rw⁻ 84 q16 ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 85 q6 ∷
   rw 84 q15 ∷
   rw⁻ 83 q6 ∷
   re 84 3 (CS13 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 84 q6 ∷
   rw 83 q15 ∷
   rw⁻ 82 q6 ∷
   re 83 3 (CS13 ∷ []) ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 83 q6 ∷
   rw 82 q15 ∷
   rw⁻ 81 q6 ∷
   re 82 3 (CS13 ∷ []) ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 82 q6 ∷
   rw 81 q15 ∷
   rw⁻ 80 q6 ∷
   re 81 3 (CS13 ∷ []) ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 81 q6 ∷
   rw 80 q15 ∷
   rw⁻ 79 q6 ∷
   re 80 3 (CS13 ∷ []) ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 80 q6 ∷
   rw 79 q15 ∷
   rw⁻ 78 q6 ∷
   re 79 3 (CS13 ∷ []) ∷
   rw⁻ 77 q17 ∷
   re 76 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 78 q6 ∷
   rw 77 q7 ∷
   rw⁻ 76 q6 ∷
   re 77 3 (CK31 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 77 q6 ∷
   rw 76 q15 ∷
   rw⁻ 75 q6 ∷
   re 76 3 (CS13 ∷ []) ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 76 q6 ∷
   rw 75 q15 ∷
   rw⁻ 74 q6 ∷
   re 75 3 (CS13 ∷ []) ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 75 q6 ∷
   rw 74 q15 ∷
   rw⁻ 73 q6 ∷
   re 74 3 (CS13 ∷ []) ∷
   rw⁻ 72 q17 ∷
   re 71 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 73 q6 ∷
   rw 72 q7 ∷
   rw⁻ 71 q6 ∷
   re 72 3 (CK31 ∷ []) ∷
   rw⁻ 70 q17 ∷
   re 69 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 71 q6 ∷
   rw 70 q7 ∷
   rw⁻ 69 q6 ∷
   re 70 3 (CK31 ∷ []) ∷
   rw⁻ 68 q16 ∷
   rw 67 q7 ∷
   rw 66 q7 ∷
   rw 65 q15 ∷
   rw 64 q7 ∷
   rw 63 q15 ∷
   rw 62 q15 ∷
   rw 63 q22 ∷
   rw 62 q5 ∷
   rw 63 q19 ∷
   rw 64 q19 ∷
   rw 65 q19 ∷
   rw 66 q5 ∷
   rw 67 q21 ∷
   rw 68 q21 ∷
   rw 69 q9 ∷
   rw 70 q21 ∷
   rw 71 q9 ∷
   rw 72 q9 ∷
   rw 73 q16 ∷
   re 75 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 74 q6 ∷
   rw 75 q9 ∷
   rw 76 q6 ∷
   re 74 3 (CK30 ∷ []) ∷
   rw 75 q17 ∷
   re 77 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 76 q6 ∷
   rw 77 q9 ∷
   rw 78 q6 ∷
   re 76 3 (CK30 ∷ []) ∷
   rw 77 q17 ∷
   re 79 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 78 q6 ∷
   rw 79 q21 ∷
   rw 80 q6 ∷
   re 78 3 (CS03 ∷ []) ∷
   re 80 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 79 q6 ∷
   rw 80 q21 ∷
   rw 81 q6 ∷
   re 79 3 (CS03 ∷ []) ∷
   re 81 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 80 q6 ∷
   rw 81 q21 ∷
   rw 82 q6 ∷
   re 80 3 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 81 q6 ∷
   rw 82 q9 ∷
   rw 83 q6 ∷
   re 81 3 (CK30 ∷ []) ∷
   rw 82 q17 ∷
   re 84 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 83 q6 ∷
   rw 84 q21 ∷
   rw 85 q6 ∷
   re 83 3 (CS03 ∷ []) ∷
   re 85 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 84 q6 ∷
   rw 85 q21 ∷
   rw 86 q6 ∷
   re 84 3 (CS03 ∷ []) ∷
   re 86 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 85 q6 ∷
   rw 86 q21 ∷
   rw 87 q6 ∷
   re 85 3 (CS03 ∷ []) ∷
   re 87 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 86 q6 ∷
   rw 87 q21 ∷
   rw 88 q6 ∷
   re 86 3 (CS03 ∷ []) ∷
   re 88 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 87 q6 ∷
   rw 88 q21 ∷
   rw 89 q6 ∷
   re 87 3 (CS03 ∷ []) ∷
   re 89 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 88 q6 ∷
   rw 89 q21 ∷
   rw 90 q6 ∷
   re 88 3 (CS03 ∷ []) ∷
   rw 89 q16 ∷
   re 91 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 90 q6 ∷
   rw 91 q21 ∷
   rw 92 q6 ∷
   re 90 3 (CS03 ∷ []) ∷
   re 92 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 91 q6 ∷
   rw 92 q21 ∷
   rw 93 q6 ∷
   re 91 3 (CS03 ∷ []) ∷
   re 93 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 92 q6 ∷
   rw 93 q9 ∷
   rw 94 q6 ∷
   re 92 3 (CK30 ∷ []) ∷
   re 94 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 93 q6 ∷
   rw 94 q21 ∷
   rw 95 q6 ∷
   re 93 3 (CS03 ∷ []) ∷
   re 95 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 94 q6 ∷
   rw 95 q9 ∷
   rw 96 q6 ∷
   re 94 3 (CK30 ∷ []) ∷
   re 96 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 95 q6 ∷
   rw 96 q9 ∷
   rw 97 q6 ∷
   re 95 3 (CK30 ∷ []) ∷
   rw 96 q10 ∷ []) Eq.refl

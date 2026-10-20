{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D158 (W : Ws) where

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
  q1 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q2 : Eqn
  q2 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q3 : Eqn
  q3 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q4 : Eqn
  q4 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q6 : Eqn
  q6 = eqn (CS13 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ []) (wn 629 W)
  q7 : Eqn
  q7 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q8 : Eqn
  q8 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q9 : Eqn
  q9 = eqn (Sw12 ∷ CX31 ∷ []) (CX32 ∷ Sw12 ∷ []) (wn 113 W)
  q10 : Eqn
  q10 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q11 : Eqn
  q11 = eqn (Sw12 ∷ CX32 ∷ []) (CX31 ∷ Sw12 ∷ []) (wn 114 W)
  q12 : Eqn
  q12 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q13 : Eqn
  q13 = eqn (X2 ∷ S3 ∷ []) (S3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (S))
  q14 : Eqn
  q14 = eqn (CX21 ∷ S3 ∷ []) (S3 ∷ CX21 ∷ []) (low₃-comm ((CX₁₀ ↑)) (S))
  q15 : Eqn
  q15 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q16 : Eqn
  q16 = eqn (CK31 ∷ X2 ∷ []) (X2 ∷ CK31 ∷ []) (wn 630 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q18 : Eqn
  q18 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q19 : Eqn
  q19 = eqn (CX23 ∷ X2 ∷ CX21 ∷ X2 ∷ []) (X2 ∷ CX21 ∷ X2 ∷ CX23 ∷ []) (wn 673 W)
  q20 : Eqn
  q20 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ CX21 ∷ X2 ∷ []) (X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (wn 488 W)
  q21 : Eqn
  q21 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q22 : Eqn
  q22 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q23 : Eqn
  q23 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q24 : Eqn
  q24 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))

-- Bar(SSKSKK;2,3->0) passes white iX via V2 conjugates 1 part4: 500 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part4 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ X2 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ Sw23 ∷ CK20 ∷ Sw01 ∷ Sw23 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ Sw01 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part4 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ X2 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ Sw23 ∷ CK20 ∷ Sw01 ∷ Sw23 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ Sw01 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ [])
  (rw 45 q1 ∷
   rw 42 q2 ∷
   rw⁻ 41 q3 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q4 ∷
   rw 41 q5 ∷
   rw⁻ 40 q4 ∷
   re 41 3 (CS13 ∷ []) ∷
   rw 41 q6 ∷
   rw 40 q3 ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 41 q4 ∷
   rw 42 q7 ∷
   rw 43 q4 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 42 q1 ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q8 ∷
   re 45 3 (CX31 ∷ []) ∷
   rw 44 q9 ∷
   rw 43 q10 ∷
   rw 42 q11 ∷
   re 42 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 41 q12 ∷
   re 42 5 (CS03 ∷ []) ∷
   rw 44 q2 ∷
   rw⁻ 43 q3 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q4 ∷
   rw 43 q5 ∷
   rw⁻ 42 q4 ∷
   re 43 3 (CS13 ∷ []) ∷
   rw 43 q6 ∷
   rw 42 q3 ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q4 ∷
   rw 44 q7 ∷
   rw 45 q4 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 44 q1 ∷
   rw 41 q2 ∷
   rw⁻ 40 q3 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q4 ∷
   rw 40 q5 ∷
   rw⁻ 39 q4 ∷
   re 40 3 (CS13 ∷ []) ∷
   rw 40 q6 ∷
   rw 39 q3 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q4 ∷
   rw 41 q7 ∷
   rw 42 q4 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q1 ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q8 ∷
   re 44 3 (CX31 ∷ []) ∷
   rw 43 q9 ∷
   rw 42 q10 ∷
   rw 41 q11 ∷
   re 41 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 40 q12 ∷
   re 41 5 (CS03 ∷ []) ∷
   rw 43 q2 ∷
   rw⁻ 42 q3 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q4 ∷
   rw 42 q5 ∷
   rw⁻ 41 q4 ∷
   re 42 3 (CS13 ∷ []) ∷
   rw 42 q6 ∷
   rw 41 q3 ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q4 ∷
   rw 43 q7 ∷
   rw 44 q4 ∷
   re 42 3 (CS03 ∷ []) ∷
   rw 43 q1 ∷
   rw 40 q2 ∷
   rw⁻ 39 q3 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q4 ∷
   rw 39 q5 ∷
   rw⁻ 38 q4 ∷
   re 39 3 (CS13 ∷ []) ∷
   rw 39 q6 ∷
   rw 38 q3 ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q4 ∷
   rw 40 q7 ∷
   rw 41 q4 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 40 q1 ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q8 ∷
   re 43 3 (CX31 ∷ []) ∷
   rw 42 q9 ∷
   rw 41 q10 ∷
   rw 40 q11 ∷
   re 40 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 39 q12 ∷
   re 40 5 (CS03 ∷ []) ∷
   rw 42 q2 ∷
   rw⁻ 41 q3 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q4 ∷
   rw 41 q5 ∷
   rw⁻ 40 q4 ∷
   re 41 3 (CS13 ∷ []) ∷
   rw 41 q6 ∷
   rw 40 q3 ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 41 q4 ∷
   rw 42 q7 ∷
   rw 43 q4 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 42 q1 ∷
   rw 39 q2 ∷
   rw⁻ 38 q3 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q4 ∷
   rw 38 q5 ∷
   rw⁻ 37 q4 ∷
   re 38 3 (CS13 ∷ []) ∷
   rw 38 q6 ∷
   rw 37 q3 ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q4 ∷
   rw 39 q7 ∷
   rw 40 q4 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 39 q1 ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q8 ∷
   re 42 3 (CX31 ∷ []) ∷
   rw 41 q9 ∷
   rw 40 q10 ∷
   rw 39 q11 ∷
   re 39 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 38 q12 ∷
   re 39 5 (CS03 ∷ []) ∷
   rw 41 q2 ∷
   rw⁻ 40 q3 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q4 ∷
   rw 40 q5 ∷
   rw⁻ 39 q4 ∷
   re 40 3 (CS13 ∷ []) ∷
   rw 40 q6 ∷
   rw 39 q3 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q4 ∷
   rw 41 q7 ∷
   rw 42 q4 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q1 ∷
   rw⁻ 36 q13 ∷
   rw⁻ 37 q14 ∷
   rw⁻ 38 q13 ∷
   rw 37 q2 ∷
   rw⁻ 36 q3 ∷
   re 35 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q4 ∷
   rw 36 q15 ∷
   rw⁻ 35 q4 ∷
   re 36 3 (CK31 ∷ []) ∷
   rw 36 q16 ∷
   rw 35 q3 ∷
   re 37 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 36 q4 ∷
   rw 37 q17 ∷
   rw 38 q4 ∷
   re 36 3 (CK30 ∷ []) ∷
   rw 37 q1 ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q8 ∷
   re 40 3 (CX31 ∷ []) ∷
   rw 39 q9 ∷
   rw 38 q18 ∷
   rw 37 q11 ∷
   re 37 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 36 q12 ∷
   re 37 5 (CK30 ∷ []) ∷
   rw 39 q2 ∷
   rw⁻ 38 q3 ∷
   re 37 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q4 ∷
   rw 38 q15 ∷
   rw⁻ 37 q4 ∷
   re 38 3 (CK31 ∷ []) ∷
   rw 38 q16 ∷
   rw 37 q3 ∷
   re 39 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 38 q4 ∷
   rw 39 q17 ∷
   rw 40 q4 ∷
   re 38 3 (CK30 ∷ []) ∷
   rw 39 q1 ∷
   rw 36 q2 ∷
   rw⁻ 35 q3 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q4 ∷
   rw 35 q5 ∷
   rw⁻ 34 q4 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw 35 q6 ∷
   rw 34 q3 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q4 ∷
   rw 36 q7 ∷
   rw 37 q4 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q1 ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q8 ∷
   re 39 3 (CX31 ∷ []) ∷
   rw 38 q9 ∷
   rw 37 q10 ∷
   rw 36 q11 ∷
   re 36 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 35 q12 ∷
   re 36 5 (CS03 ∷ []) ∷
   rw 38 q2 ∷
   rw⁻ 37 q3 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q4 ∷
   rw 37 q5 ∷
   rw⁻ 36 q4 ∷
   re 37 3 (CS13 ∷ []) ∷
   rw 37 q6 ∷
   rw 36 q3 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q4 ∷
   rw 38 q7 ∷
   rw 39 q4 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 38 q1 ∷
   rw 35 q2 ∷
   rw⁻ 34 q3 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q4 ∷
   rw 34 q5 ∷
   rw⁻ 33 q4 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw 34 q6 ∷
   rw 33 q3 ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q4 ∷
   rw 35 q7 ∷
   rw 36 q4 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 35 q1 ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q8 ∷
   re 38 3 (CX31 ∷ []) ∷
   rw 37 q9 ∷
   rw 36 q10 ∷
   rw 35 q11 ∷
   re 35 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 34 q12 ∷
   re 35 5 (CS03 ∷ []) ∷
   rw 37 q2 ∷
   rw⁻ 36 q3 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q4 ∷
   rw 36 q5 ∷
   rw⁻ 35 q4 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 36 q6 ∷
   rw 35 q3 ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q4 ∷
   rw 37 q7 ∷
   rw 38 q4 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q1 ∷
   rw 34 q2 ∷
   rw⁻ 33 q3 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q4 ∷
   rw 33 q5 ∷
   rw⁻ 32 q4 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw 33 q6 ∷
   rw 32 q3 ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q4 ∷
   rw 34 q7 ∷
   rw 35 q4 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 34 q1 ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q8 ∷
   re 37 3 (CX31 ∷ []) ∷
   rw 36 q9 ∷
   rw 35 q10 ∷
   rw 34 q11 ∷
   re 34 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 33 q12 ∷
   re 34 5 (CS03 ∷ []) ∷
   rw 36 q2 ∷
   rw⁻ 35 q3 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q4 ∷
   rw 35 q5 ∷
   rw⁻ 34 q4 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw 35 q6 ∷
   rw 34 q3 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q4 ∷
   rw 36 q7 ∷
   rw 37 q4 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q1 ∷
   rw⁻ 31 q13 ∷
   rw⁻ 32 q14 ∷
   rw⁻ 33 q13 ∷
   rw 32 q2 ∷
   rw⁻ 31 q3 ∷
   re 30 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q4 ∷
   rw 31 q15 ∷
   rw⁻ 30 q4 ∷
   re 31 3 (CK31 ∷ []) ∷
   rw 31 q16 ∷
   rw 30 q3 ∷
   re 32 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 31 q4 ∷
   rw 32 q17 ∷
   rw 33 q4 ∷
   re 31 3 (CK30 ∷ []) ∷
   rw 32 q1 ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q8 ∷
   re 35 3 (CX31 ∷ []) ∷
   rw 34 q9 ∷
   rw 33 q18 ∷
   rw 32 q11 ∷
   re 32 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 31 q12 ∷
   re 32 5 (CK30 ∷ []) ∷
   rw 34 q2 ∷
   rw⁻ 33 q3 ∷
   re 32 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q4 ∷
   rw 33 q15 ∷
   rw⁻ 32 q4 ∷
   re 33 3 (CK31 ∷ []) ∷
   rw 33 q16 ∷
   rw 32 q3 ∷
   re 34 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 33 q4 ∷
   rw 34 q17 ∷
   rw 35 q4 ∷
   re 33 3 (CK30 ∷ []) ∷
   rw 34 q1 ∷
   rw⁻ 29 q13 ∷
   rw⁻ 30 q14 ∷
   rw⁻ 31 q13 ∷
   rw 30 q2 ∷
   rw⁻ 29 q3 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q4 ∷
   rw 29 q15 ∷
   rw⁻ 28 q4 ∷
   re 29 3 (CK31 ∷ []) ∷
   rw 29 q16 ∷
   rw 28 q3 ∷
   re 30 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 29 q4 ∷
   rw 30 q17 ∷
   rw 31 q4 ∷
   re 29 3 (CK30 ∷ []) ∷
   rw 30 q1 ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q8 ∷
   re 33 3 (CX31 ∷ []) ∷
   rw 32 q9 ∷
   rw 31 q18 ∷
   rw 30 q11 ∷
   re 30 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 29 q12 ∷
   re 30 5 (CK30 ∷ []) ∷
   rw 32 q2 ∷
   rw⁻ 31 q3 ∷
   re 30 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q4 ∷
   rw 31 q15 ∷
   rw⁻ 30 q4 ∷
   re 31 3 (CK31 ∷ []) ∷
   rw 31 q16 ∷
   rw 30 q3 ∷
   re 32 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 31 q4 ∷
   rw 32 q17 ∷
   rw 33 q4 ∷
   re 31 3 (CK30 ∷ []) ∷
   rw 32 q1 ∷
   rw 27 q19 ∷
   rw 21 q20 ∷
   rw 59 q2 ∷
   rw⁻ 58 q3 ∷
   rw 57 q21 ∷
   rw 56 q21 ∷
   rw 55 q22 ∷
   rw 54 q21 ∷
   rw⁻ 53 q3 ∷
   re 52 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 54 q4 ∷
   rw 53 q15 ∷
   rw⁻ 52 q4 ∷
   re 53 3 (CK31 ∷ []) ∷
   re 51 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q4 ∷
   rw 52 q15 ∷
   rw⁻ 51 q4 ∷
   re 52 3 (CK31 ∷ []) ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q4 ∷
   rw 51 q5 ∷
   rw⁻ 50 q4 ∷
   re 51 3 (CS13 ∷ []) ∷
   re 49 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q4 ∷
   rw 50 q15 ∷
   rw⁻ 49 q4 ∷
   re 50 3 (CK31 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q4 ∷
   rw 49 q5 ∷
   rw⁻ 48 q4 ∷
   re 49 3 (CS13 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q4 ∷
   rw 48 q5 ∷
   rw⁻ 47 q4 ∷
   re 48 3 (CS13 ∷ []) ∷
   rw⁻ 46 q23 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q4 ∷
   rw 46 q5 ∷
   rw⁻ 45 q4 ∷
   re 46 3 (CS13 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q4 ∷
   rw 45 q5 ∷
   rw⁻ 44 q4 ∷
   re 45 3 (CS13 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q4 ∷
   rw 44 q5 ∷
   rw⁻ 43 q4 ∷
   re 44 3 (CS13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q4 ∷
   rw 43 q5 ∷
   rw⁻ 42 q4 ∷
   re 43 3 (CS13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q4 ∷
   rw 42 q5 ∷
   rw⁻ 41 q4 ∷
   re 42 3 (CS13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q4 ∷
   rw 41 q5 ∷
   rw⁻ 40 q4 ∷
   re 41 3 (CS13 ∷ []) ∷
   rw⁻ 39 q24 ∷
   re 38 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q4 ∷
   rw 39 q15 ∷
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
   rw⁻ 34 q24 ∷
   re 33 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q4 ∷
   rw 34 q15 ∷
   rw⁻ 33 q4 ∷
   re 34 3 (CK31 ∷ []) ∷
   rw⁻ 32 q24 ∷
   re 31 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q4 ∷ []) Eq.refl

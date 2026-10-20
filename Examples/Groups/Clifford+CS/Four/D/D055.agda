{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D055 (W : Ws) where

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
  q1 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q3 : Eqn
  q3 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q4 : Eqn
  q4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q5 : Eqn
  q5 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q6 : Eqn
  q6 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q9 : Eqn
  q9 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q11 : Eqn
  q11 = eqn (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) (wn 561 W)
  q12 : Eqn
  q12 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (wn 555 W)
  q13 : Eqn
  q13 = eqn (CS01⁻ ∷ CX32 ∷ []) (CX32 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₁₀))
  q14 : Eqn
  q14 = eqn (CK10⁻ ∷ CX32 ∷ []) (CX32 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q15 : Eqn
  q15 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (wn 556 W)
  q16 : Eqn
  q16 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q17 : Eqn
  q17 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q18 : Eqn
  q18 = eqn (CK10⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap))
  q19 : Eqn
  q19 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q20 : Eqn
  q20 = eqn (CS02 ∷ X3 ∷ []) (X3 ∷ CS02 ∷ []) (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q21 : Eqn
  q21 = eqn (Sw12 ∷ CX31 ∷ []) (CX32 ∷ Sw12 ∷ []) (wn 113 W)
  q22 : Eqn
  q22 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q23 : Eqn
  q23 = eqn (Sw12 ∷ CX32 ∷ []) (CX31 ∷ Sw12 ∷ []) (wn 114 W)
  q24 : Eqn
  q24 = eqn (CK20 ∷ X3 ∷ []) (X3 ∷ CK20 ∷ []) (low₃-comm ((Swap ↑ • CK₁₀ • Swap ↑)) (X))
  q25 : Eqn
  q25 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q26 : Eqn
  q26 = eqn (CX32 ∷ X3 ∷ CX31 ∷ X3 ∷ []) (X3 ∷ CX31 ∷ X3 ∷ CX32 ∷ []) (wn 486 W)
  q27 : Eqn
  q27 = eqn (S2 ∷ X3 ∷ []) (X3 ∷ S2 ∷ []) (low₃-comm ((S ↑ ↑)) (X))
  q28 : Eqn
  q28 = eqn (S2 ∷ CX31 ∷ []) (CX31 ∷ S2 ∷ []) (wn 487 W)

-- Bar(SSSKSS;3,2->0) passes white iX via V2 conjugates 1 part3: 500 steps
lem-Bar⟨SSSKSS32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part3 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ Sw01 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ Sw01 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CS02 ∷ X3 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part3 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ Sw01 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ Sw01 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CS02 ∷ X3 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 45 q1 ∷
   rw 46 q1 ∷
   rw 47 q1 ∷
   rw 48 q1 ∷
   rw 49 q1 ∷
   rw 50 q1 ∷
   rw 51 q1 ∷
   rw 52 q1 ∷
   rw 53 q1 ∷
   rw 54 q2 ∷
   rw 55 q1 ∷
   rw 56 q1 ∷
   rw 57 q1 ∷
   rw 58 q3 ∷
   rw 59 q1 ∷
   rw 60 q1 ∷
   rw 61 q4 ∷
   rw 66 q5 ∷
   rw⁻ 65 q6 ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 66 q7 ∷
   rw 65 q8 ∷
   rw⁻ 64 q7 ∷
   re 65 3 (CS13 ∷ []) ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 65 q7 ∷
   rw 64 q8 ∷
   rw⁻ 63 q7 ∷
   re 64 3 (CS13 ∷ []) ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 64 q7 ∷
   rw 63 q8 ∷
   rw⁻ 62 q7 ∷
   re 63 3 (CS13 ∷ []) ∷
   rw⁻ 61 q6 ∷
   rw 60 q8 ∷
   rw 59 q8 ∷
   rw 58 q9 ∷
   rw 57 q8 ∷
   rw 56 q8 ∷
   rw 55 q8 ∷
   rw⁻ 54 q2 ∷
   rw 53 q8 ∷
   rw 52 q8 ∷
   rw 51 q8 ∷
   rw 50 q8 ∷
   rw 49 q8 ∷
   rw 48 q8 ∷
   rw 47 q8 ∷
   rw 46 q8 ∷
   rw 45 q8 ∷
   rw⁻ 44 q10 ∷
   rw 43 q9 ∷
   rw 42 q8 ∷
   rw 41 q8 ∷
   rw 40 q8 ∷
   rw 39 q8 ∷
   rw 38 q8 ∷
   rw 37 q8 ∷
   rw⁻ 36 q2 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q7 ∷
   rw 36 q8 ∷
   rw⁻ 35 q7 ∷
   re 36 3 (CS13 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q7 ∷
   rw 35 q8 ∷
   rw⁻ 34 q7 ∷
   re 35 3 (CS13 ∷ []) ∷
   re 33 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q7 ∷
   rw 34 q9 ∷
   rw⁻ 33 q7 ∷
   re 34 3 (CK31 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q7 ∷
   rw 33 q8 ∷
   rw⁻ 32 q7 ∷
   re 33 3 (CS13 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q7 ∷
   rw 32 q8 ∷
   rw⁻ 31 q7 ∷
   re 32 3 (CS13 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q7 ∷
   rw 31 q8 ∷
   rw⁻ 30 q7 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 31 q11 ∷
   rw 30 q6 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q7 ∷
   rw 32 q1 ∷
   rw 33 q7 ∷
   re 31 3 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q7 ∷
   rw 33 q1 ∷
   rw 34 q7 ∷
   re 32 3 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q7 ∷
   rw 34 q1 ∷
   rw 35 q7 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 34 q6 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q7 ∷
   rw 36 q1 ∷
   rw 37 q7 ∷
   re 35 3 (CS03 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q7 ∷
   rw 37 q1 ∷
   rw 38 q7 ∷
   re 36 3 (CS03 ∷ []) ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q7 ∷
   rw 38 q1 ∷
   rw 39 q7 ∷
   re 37 3 (CS03 ∷ []) ∷
   re 39 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 38 q7 ∷
   rw 39 q3 ∷
   rw 40 q7 ∷
   re 38 3 (CK30 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q7 ∷
   rw 40 q1 ∷
   rw 41 q7 ∷
   re 39 3 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q7 ∷
   rw 41 q1 ∷
   rw 42 q7 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q2 ∷
   rw 42 q1 ∷
   rw 43 q1 ∷
   rw 44 q1 ∷
   rw 45 q1 ∷
   rw 46 q1 ∷
   rw 47 q1 ∷
   rw 48 q3 ∷
   rw 49 q10 ∷
   rw 50 q1 ∷
   rw 51 q1 ∷
   rw 52 q1 ∷
   rw 53 q1 ∷
   rw 54 q1 ∷
   rw 55 q1 ∷
   rw 56 q1 ∷
   rw 57 q1 ∷
   rw 58 q1 ∷
   rw 59 q2 ∷
   rw 60 q1 ∷
   rw 61 q1 ∷
   rw 62 q1 ∷
   rw 63 q3 ∷
   rw 64 q1 ∷
   rw 65 q1 ∷
   rw 66 q4 ∷
   rw 60 q12 ∷
   rw⁻ 59 q13 ∷
   rw⁻ 60 q14 ∷
   rw⁻ 61 q13 ∷
   rw⁻ 62 q13 ∷
   rw 42 q15 ∷
   rw⁻ 41 q13 ∷
   rw⁻ 42 q14 ∷
   rw⁻ 43 q13 ∷
   rw⁻ 44 q13 ∷
   rw 45 q16 ∷
   rw 44 q17 ∷
   rw 43 q17 ∷
   rw 42 q18 ∷
   rw 41 q17 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q19 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q19 ∷
   re 38 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 40 q19 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q19 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q19 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q19 ∷
   rw 36 q12 ∷
   rw⁻ 35 q17 ∷
   rw⁻ 36 q18 ∷
   rw⁻ 37 q17 ∷
   rw⁻ 38 q17 ∷
   rw 41 q16 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 42 q16 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 43 q16 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 44 q16 ∷
   re 42 3 (CK30 ∷ []) ∷
   rw 45 q16 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 46 q16 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 45 q19 ∷
   rw 69 q20 ∷
   re 71 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 70 q16 ∷
   re 71 3 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 77 q16 ∷
   re 75 3 (CX31 ∷ []) ∷
   rw 74 q21 ∷
   rw 73 q22 ∷
   rw 72 q23 ∷
   re 72 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 71 q19 ∷
   re 72 5 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q19 ∷
   re 70 3 (CX31 ∷ []) ∷
   rw 71 q20 ∷
   rw 68 q20 ∷
   re 70 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 69 q16 ∷
   re 70 3 (CS03 ∷ []) ∷
   re 70 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 76 q16 ∷
   re 74 3 (CX31 ∷ []) ∷
   rw 73 q21 ∷
   rw 72 q22 ∷
   rw 71 q23 ∷
   re 71 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 70 q19 ∷
   re 71 5 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 73 q19 ∷
   re 69 3 (CX31 ∷ []) ∷
   rw 70 q20 ∷
   rw 67 q24 ∷
   re 69 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 68 q16 ∷
   re 69 3 (CK30 ∷ []) ∷
   re 69 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 75 q16 ∷
   re 73 3 (CX31 ∷ []) ∷
   rw 72 q21 ∷
   rw 71 q25 ∷
   rw 70 q23 ∷
   re 70 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 69 q19 ∷
   re 70 5 (CK30 ∷ []) ∷
   re 70 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 72 q19 ∷
   re 68 3 (CX31 ∷ []) ∷
   rw 69 q24 ∷
   rw 66 q20 ∷
   re 68 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 67 q16 ∷
   re 68 3 (CS03 ∷ []) ∷
   re 68 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 74 q16 ∷
   re 72 3 (CX31 ∷ []) ∷
   rw 71 q21 ∷
   rw 70 q22 ∷
   rw 69 q23 ∷
   re 69 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 68 q19 ∷
   re 69 5 (CS03 ∷ []) ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 71 q19 ∷
   re 67 3 (CX31 ∷ []) ∷
   rw 68 q20 ∷
   rw 65 q20 ∷
   re 67 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 66 q16 ∷
   re 67 3 (CS03 ∷ []) ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q16 ∷
   re 71 3 (CX31 ∷ []) ∷
   rw 70 q21 ∷
   rw 69 q22 ∷
   rw 68 q23 ∷
   re 68 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 67 q19 ∷
   re 68 5 (CS03 ∷ []) ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 70 q19 ∷
   re 66 3 (CX31 ∷ []) ∷
   rw 67 q20 ∷
   rw 64 q20 ∷
   re 66 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 65 q16 ∷
   re 66 3 (CS03 ∷ []) ∷
   re 66 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 72 q16 ∷
   re 70 3 (CX31 ∷ []) ∷
   rw 69 q21 ∷
   rw 68 q22 ∷
   rw 67 q23 ∷
   re 67 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 66 q19 ∷
   re 67 5 (CS03 ∷ []) ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 69 q19 ∷
   re 65 3 (CX31 ∷ []) ∷
   rw 66 q20 ∷
   rw 63 q26 ∷
   rw 62 q20 ∷
   re 64 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 63 q16 ∷
   re 64 3 (CS03 ∷ []) ∷
   re 64 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 70 q16 ∷
   re 68 3 (CX31 ∷ []) ∷
   rw 67 q21 ∷
   rw 66 q22 ∷
   rw 65 q23 ∷
   re 65 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 64 q19 ∷
   re 65 5 (CS03 ∷ []) ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q19 ∷
   re 63 3 (CX31 ∷ []) ∷
   rw 64 q20 ∷
   rw 61 q20 ∷
   re 63 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 62 q16 ∷
   re 63 3 (CS03 ∷ []) ∷
   re 63 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 69 q16 ∷
   re 67 3 (CX31 ∷ []) ∷
   rw 66 q21 ∷
   rw 65 q22 ∷
   rw 64 q23 ∷
   re 64 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 63 q19 ∷
   re 64 5 (CS03 ∷ []) ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 66 q19 ∷
   re 62 3 (CX31 ∷ []) ∷
   rw 63 q20 ∷
   rw 60 q20 ∷
   re 62 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 61 q16 ∷
   re 62 3 (CS03 ∷ []) ∷
   re 62 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 68 q16 ∷
   re 66 3 (CX31 ∷ []) ∷
   rw 65 q21 ∷
   rw 64 q22 ∷
   rw 63 q23 ∷
   re 63 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 62 q19 ∷
   re 63 5 (CS03 ∷ []) ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 65 q19 ∷
   re 61 3 (CX31 ∷ []) ∷
   rw 62 q20 ∷
   rw 59 q20 ∷
   re 61 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 60 q16 ∷
   re 61 3 (CS03 ∷ []) ∷
   re 61 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 67 q16 ∷
   re 65 3 (CX31 ∷ []) ∷
   rw 64 q21 ∷
   rw 63 q22 ∷
   rw 62 q23 ∷
   re 62 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 61 q19 ∷
   re 62 5 (CS03 ∷ []) ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 64 q19 ∷
   re 60 3 (CX31 ∷ []) ∷
   rw 61 q20 ∷
   rw 58 q20 ∷
   re 60 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 59 q16 ∷
   re 60 3 (CS03 ∷ []) ∷
   re 60 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 66 q16 ∷
   re 64 3 (CX31 ∷ []) ∷
   rw 63 q21 ∷
   rw 62 q22 ∷
   rw 61 q23 ∷
   re 61 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 60 q19 ∷
   re 61 5 (CS03 ∷ []) ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 63 q19 ∷
   re 59 3 (CX31 ∷ []) ∷
   rw 60 q20 ∷
   rw 57 q20 ∷
   re 59 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 58 q16 ∷
   re 59 3 (CS03 ∷ []) ∷
   re 59 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 65 q16 ∷
   re 63 3 (CX31 ∷ []) ∷
   rw 62 q21 ∷
   rw 61 q22 ∷
   rw 60 q23 ∷
   re 60 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 59 q19 ∷
   re 60 5 (CS03 ∷ []) ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 62 q19 ∷
   re 58 3 (CX31 ∷ []) ∷
   rw 59 q20 ∷
   rw 56 q20 ∷
   re 58 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 57 q16 ∷
   re 58 3 (CS03 ∷ []) ∷
   re 58 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 64 q16 ∷
   re 62 3 (CX31 ∷ []) ∷
   rw 61 q21 ∷
   rw 60 q22 ∷
   rw 59 q23 ∷
   re 59 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 58 q19 ∷
   re 59 5 (CS03 ∷ []) ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 61 q19 ∷
   re 57 3 (CX31 ∷ []) ∷
   rw 58 q20 ∷
   rw 55 q20 ∷
   re 57 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 56 q16 ∷
   re 57 3 (CS03 ∷ []) ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 63 q16 ∷
   re 61 3 (CX31 ∷ []) ∷
   rw 60 q21 ∷
   rw 59 q22 ∷
   rw 58 q23 ∷
   re 58 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 57 q19 ∷
   re 58 5 (CS03 ∷ []) ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q19 ∷
   re 56 3 (CX31 ∷ []) ∷
   rw 57 q20 ∷
   rw 54 q20 ∷
   re 56 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 55 q16 ∷
   re 56 3 (CS03 ∷ []) ∷
   re 56 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 62 q16 ∷
   re 60 3 (CX31 ∷ []) ∷
   rw 59 q21 ∷
   rw 58 q22 ∷
   rw 57 q23 ∷
   re 57 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 56 q19 ∷
   re 57 5 (CS03 ∷ []) ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q19 ∷
   re 55 3 (CX31 ∷ []) ∷
   rw 56 q20 ∷
   rw 53 q27 ∷
   rw 54 q28 ∷
   rw 55 q27 ∷
   rw 52 q24 ∷
   re 54 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 53 q16 ∷
   re 54 3 (CK30 ∷ []) ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 60 q16 ∷
   re 58 3 (CX31 ∷ []) ∷
   rw 57 q21 ∷
   rw 56 q25 ∷
   rw 55 q23 ∷
   re 55 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 54 q19 ∷
   re 55 5 (CK30 ∷ []) ∷
   re 55 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 57 q19 ∷
   re 53 3 (CX31 ∷ []) ∷
   rw 54 q24 ∷
   rw 51 q20 ∷
   re 53 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 52 q16 ∷
   re 53 3 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q16 ∷
   re 57 3 (CX31 ∷ []) ∷
   rw 56 q21 ∷
   rw 55 q22 ∷
   rw 54 q23 ∷
   re 54 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 53 q19 ∷
   re 54 5 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q19 ∷ []) Eq.refl

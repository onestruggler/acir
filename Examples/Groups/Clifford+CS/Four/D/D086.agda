{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D086 (W : Ws) where

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
  q1 = eqn (CX21 ∷ S3 ∷ []) (S3 ∷ CX21 ∷ []) (low₃-comm ((CX₁₀ ↑)) (S))
  q2 : Eqn
  q2 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q3 : Eqn
  q3 = eqn (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) (wn 13 W)
  q4 : Eqn
  q4 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q5 : Eqn
  q5 = eqn (CX32 ∷ Sw12 ∷ []) (Sw12 ∷ CX31 ∷ []) (wn 78 W)
  q6 : Eqn
  q6 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q7 : Eqn
  q7 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q8 : Eqn
  q8 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q9 : Eqn
  q9 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q10 : Eqn
  q10 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q11 : Eqn
  q11 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q12 : Eqn
  q12 = eqn (CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (wn 618 W)
  q13 : Eqn
  q13 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)
  q14 : Eqn
  q14 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q16 : Eqn
  q16 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q18 : Eqn
  q18 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q19 : Eqn
  q19 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ []) (CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (wn 619 W)
  q20 : Eqn
  q20 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q21 : Eqn
  q21 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q22 : Eqn
  q22 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)

-- Bar(SSKSKK;2,1->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,3->0) part3: 431 steps
lem-Bar⟨SSKSKK21-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~23-⟶0⟩-part3 : ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK30 ∷ S3 ∷ CK30 ∷ CX21 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ X2 ∷ CX23 ∷ X2 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK21-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~23-⟶0⟩-part3 = derive (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK30 ∷ S3 ∷ CK30 ∷ CX21 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ X2 ∷ CX23 ∷ X2 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 90 q1 ∷
   re 92 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 91 q2 ∷
   re 92 3 (CX31 ∷ []) ∷
   rw 92 q3 ∷
   rw⁻ 93 q4 ∷
   rw 94 q5 ∷
   re 95 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 97 q6 ∷
   re 91 5 (CS03 ∷ []) ∷
   re 93 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 92 q2 ∷
   re 93 3 (CX31 ∷ []) ∷
   rw 93 q3 ∷
   rw⁻ 94 q4 ∷
   rw 95 q5 ∷
   re 96 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 98 q6 ∷
   re 92 5 (CS03 ∷ []) ∷
   re 94 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 93 q2 ∷
   re 94 3 (CX31 ∷ []) ∷
   rw 94 q3 ∷
   rw⁻ 95 q4 ∷
   rw 96 q5 ∷
   re 97 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 99 q6 ∷
   re 93 5 (CS03 ∷ []) ∷
   re 95 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 94 q2 ∷
   re 95 3 (CX31 ∷ []) ∷
   rw 95 q3 ∷
   rw⁻ 96 q7 ∷
   rw 97 q5 ∷
   re 98 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 100 q6 ∷
   re 94 5 (CK30 ∷ []) ∷
   rw 95 q1 ∷
   re 97 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 96 q2 ∷
   re 97 3 (CX31 ∷ []) ∷
   rw 97 q3 ∷
   rw⁻ 98 q4 ∷
   rw 99 q5 ∷
   re 100 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 102 q6 ∷
   re 96 5 (CS03 ∷ []) ∷
   re 98 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 97 q2 ∷
   re 98 3 (CX31 ∷ []) ∷
   rw 98 q3 ∷
   rw⁻ 99 q4 ∷
   rw 100 q5 ∷
   re 101 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 103 q6 ∷
   re 97 5 (CS03 ∷ []) ∷
   re 99 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 98 q2 ∷
   re 99 3 (CX31 ∷ []) ∷
   rw 99 q3 ∷
   rw⁻ 100 q4 ∷
   rw 101 q5 ∷
   re 102 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 104 q6 ∷
   re 98 5 (CS03 ∷ []) ∷
   re 100 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 99 q2 ∷
   re 100 3 (CX31 ∷ []) ∷
   rw 100 q3 ∷
   rw⁻ 101 q4 ∷
   rw 102 q5 ∷
   re 103 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 105 q6 ∷
   re 99 5 (CS03 ∷ []) ∷
   re 101 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 100 q2 ∷
   re 101 3 (CX31 ∷ []) ∷
   rw 101 q3 ∷
   rw⁻ 102 q4 ∷
   rw 103 q5 ∷
   re 104 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 106 q6 ∷
   re 100 5 (CS03 ∷ []) ∷
   re 102 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 101 q2 ∷
   re 102 3 (CX31 ∷ []) ∷
   rw 102 q3 ∷
   rw⁻ 103 q4 ∷
   rw 104 q5 ∷
   re 105 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 107 q6 ∷
   re 101 5 (CS03 ∷ []) ∷
   rw 102 q2 ∷
   re 101 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 103 q6 ∷
   re 100 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 102 q6 ∷
   re 99 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 101 q6 ∷
   re 98 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 100 q6 ∷
   re 97 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 99 q6 ∷
   re 96 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 98 q6 ∷
   rw 95 q8 ∷
   re 94 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 96 q6 ∷
   re 93 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 95 q6 ∷
   re 92 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 94 q6 ∷
   re 91 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 93 q6 ∷
   rw 90 q8 ∷
   re 89 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 91 q6 ∷
   rw 88 q8 ∷
   re 87 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 89 q6 ∷
   rw 86 q9 ∷
   rw 85 q9 ∷
   rw 84 q9 ∷
   rw 83 q9 ∷
   rw 82 q9 ∷
   rw 81 q9 ∷
   rw 80 q10 ∷
   rw 79 q11 ∷
   rw 78 q9 ∷
   rw 77 q9 ∷
   rw 76 q9 ∷
   rw 75 q10 ∷
   rw 74 q11 ∷
   rw 73 q10 ∷
   rw 72 q11 ∷
   rw 73 q12 ∷
   rw 74 q2 ∷
   re 72 3 (CK30 ∷ []) ∷
   rw 73 q13 ∷
   rw 76 q2 ∷
   re 74 3 (CK30 ∷ []) ∷
   rw 75 q13 ∷
   rw 78 q2 ∷
   re 76 3 (CS03 ∷ []) ∷
   rw 79 q2 ∷
   re 77 3 (CS03 ∷ []) ∷
   rw 80 q2 ∷
   re 78 3 (CS03 ∷ []) ∷
   rw 81 q2 ∷
   re 79 3 (CK30 ∷ []) ∷
   rw 80 q13 ∷
   rw 83 q2 ∷
   re 81 3 (CS03 ∷ []) ∷
   rw 84 q2 ∷
   re 82 3 (CS03 ∷ []) ∷
   rw 85 q2 ∷
   re 83 3 (CS03 ∷ []) ∷
   rw 86 q2 ∷
   re 84 3 (CS03 ∷ []) ∷
   rw 87 q2 ∷
   re 85 3 (CS03 ∷ []) ∷
   rw 88 q2 ∷
   re 86 3 (CS03 ∷ []) ∷
   rw⁻ 87 q11 ∷
   rw⁻ 88 q10 ∷
   rw⁻ 89 q11 ∷
   rw⁻ 90 q10 ∷
   rw⁻ 91 q9 ∷
   rw⁻ 92 q9 ∷
   rw⁻ 93 q9 ∷
   rw⁻ 94 q11 ∷
   rw⁻ 95 q10 ∷
   rw⁻ 96 q9 ∷
   rw⁻ 97 q9 ∷
   rw⁻ 98 q9 ∷
   rw⁻ 99 q9 ∷
   rw⁻ 100 q9 ∷
   rw⁻ 101 q9 ∷
   rw 102 q6 ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q2 ∷
   re 72 3 (CX31 ∷ []) ∷
   rw 72 q3 ∷
   rw⁻ 73 q7 ∷
   rw 74 q5 ∷
   re 75 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 77 q6 ∷
   re 71 5 (CK30 ∷ []) ∷
   rw 72 q1 ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q2 ∷
   re 74 3 (CX31 ∷ []) ∷
   rw 74 q3 ∷
   rw⁻ 75 q7 ∷
   rw 76 q5 ∷
   re 77 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 79 q6 ∷
   re 73 5 (CK30 ∷ []) ∷
   rw 74 q1 ∷
   re 76 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 75 q2 ∷
   re 76 3 (CX31 ∷ []) ∷
   rw 76 q3 ∷
   rw⁻ 77 q4 ∷
   rw 78 q5 ∷
   re 79 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 81 q6 ∷
   re 75 5 (CS03 ∷ []) ∷
   re 77 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 76 q2 ∷
   re 77 3 (CX31 ∷ []) ∷
   rw 77 q3 ∷
   rw⁻ 78 q4 ∷
   rw 79 q5 ∷
   re 80 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 82 q6 ∷
   re 76 5 (CS03 ∷ []) ∷
   re 78 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 77 q2 ∷
   re 78 3 (CX31 ∷ []) ∷
   rw 78 q3 ∷
   rw⁻ 79 q4 ∷
   rw 80 q5 ∷
   re 81 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 83 q6 ∷
   re 77 5 (CS03 ∷ []) ∷
   re 79 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 78 q2 ∷
   re 79 3 (CX31 ∷ []) ∷
   rw 79 q3 ∷
   rw⁻ 80 q7 ∷
   rw 81 q5 ∷
   re 82 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 84 q6 ∷
   re 78 5 (CK30 ∷ []) ∷
   rw 79 q1 ∷
   re 81 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 80 q2 ∷
   re 81 3 (CX31 ∷ []) ∷
   rw 81 q3 ∷
   rw⁻ 82 q4 ∷
   rw 83 q5 ∷
   re 84 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 86 q6 ∷
   re 80 5 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 81 q2 ∷
   re 82 3 (CX31 ∷ []) ∷
   rw 82 q3 ∷
   rw⁻ 83 q4 ∷
   rw 84 q5 ∷
   re 85 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 87 q6 ∷
   re 81 5 (CS03 ∷ []) ∷
   re 83 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 82 q2 ∷
   re 83 3 (CX31 ∷ []) ∷
   rw 83 q3 ∷
   rw⁻ 84 q4 ∷
   rw 85 q5 ∷
   re 86 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 88 q6 ∷
   re 82 5 (CS03 ∷ []) ∷
   re 84 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 83 q2 ∷
   re 84 3 (CX31 ∷ []) ∷
   rw 84 q3 ∷
   rw⁻ 85 q4 ∷
   rw 86 q5 ∷
   re 87 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 89 q6 ∷
   re 83 5 (CS03 ∷ []) ∷
   re 85 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 84 q2 ∷
   re 85 3 (CX31 ∷ []) ∷
   rw 85 q3 ∷
   rw⁻ 86 q4 ∷
   rw 87 q5 ∷
   re 88 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 90 q6 ∷
   re 84 5 (CS03 ∷ []) ∷
   re 86 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 85 q2 ∷
   re 86 3 (CX31 ∷ []) ∷
   rw 86 q3 ∷
   rw⁻ 87 q4 ∷
   rw 88 q5 ∷
   re 89 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 91 q6 ∷
   re 85 5 (CS03 ∷ []) ∷
   rw 86 q14 ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 87 q15 ∷
   rw 86 q16 ∷
   rw⁻ 85 q15 ∷
   re 86 3 (CS13 ∷ []) ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 86 q15 ∷
   rw 85 q16 ∷
   rw⁻ 84 q15 ∷
   re 85 3 (CS13 ∷ []) ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 85 q15 ∷
   rw 84 q16 ∷
   rw⁻ 83 q15 ∷
   re 84 3 (CS13 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 84 q15 ∷
   rw 83 q16 ∷
   rw⁻ 82 q15 ∷
   re 83 3 (CS13 ∷ []) ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 83 q15 ∷
   rw 82 q16 ∷
   rw⁻ 81 q15 ∷
   re 82 3 (CS13 ∷ []) ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 82 q15 ∷
   rw 81 q16 ∷
   rw⁻ 80 q15 ∷
   re 81 3 (CS13 ∷ []) ∷
   rw⁻ 79 q17 ∷
   re 78 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 80 q15 ∷
   rw 79 q18 ∷
   rw⁻ 78 q15 ∷
   re 79 3 (CK31 ∷ []) ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 79 q15 ∷
   rw 78 q16 ∷
   rw⁻ 77 q15 ∷
   re 78 3 (CS13 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 78 q15 ∷
   rw 77 q16 ∷
   rw⁻ 76 q15 ∷
   re 77 3 (CS13 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 77 q15 ∷
   rw 76 q16 ∷
   rw⁻ 75 q15 ∷
   re 76 3 (CS13 ∷ []) ∷
   rw⁻ 74 q17 ∷
   re 73 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 75 q15 ∷
   rw 74 q18 ∷
   rw⁻ 73 q15 ∷
   re 74 3 (CK31 ∷ []) ∷
   rw⁻ 72 q17 ∷
   re 71 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 73 q15 ∷
   rw 72 q18 ∷
   rw⁻ 71 q15 ∷
   re 72 3 (CK31 ∷ []) ∷
   rw 70 q18 ∷
   rw 69 q18 ∷
   rw 68 q16 ∷
   rw 67 q18 ∷
   rw 66 q16 ∷
   rw 65 q16 ∷
   rw 66 q19 ∷
   re 66 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 65 q15 ∷
   rw 66 q20 ∷
   rw 67 q15 ∷
   re 65 3 (CK30 ∷ []) ∷
   rw 66 q17 ∷
   re 68 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 67 q15 ∷
   rw 68 q20 ∷
   rw 69 q15 ∷
   re 67 3 (CK30 ∷ []) ∷
   rw 68 q17 ∷
   re 70 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 69 q15 ∷
   rw 70 q21 ∷
   rw 71 q15 ∷
   re 69 3 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 70 q15 ∷
   rw 71 q21 ∷
   rw 72 q15 ∷
   re 70 3 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 71 q15 ∷
   rw 72 q21 ∷
   rw 73 q15 ∷
   re 71 3 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 72 q15 ∷
   rw 73 q20 ∷
   rw 74 q15 ∷
   re 72 3 (CK30 ∷ []) ∷
   rw 73 q17 ∷
   re 75 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 74 q15 ∷
   rw 75 q21 ∷
   rw 76 q15 ∷
   re 74 3 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 75 q15 ∷
   rw 76 q21 ∷
   rw 77 q15 ∷
   re 75 3 (CS03 ∷ []) ∷
   re 77 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 76 q15 ∷
   rw 77 q21 ∷
   rw 78 q15 ∷
   re 76 3 (CS03 ∷ []) ∷
   re 78 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 77 q15 ∷
   rw 78 q21 ∷
   rw 79 q15 ∷
   re 77 3 (CS03 ∷ []) ∷
   re 79 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 78 q15 ∷
   rw 79 q21 ∷
   rw 80 q15 ∷
   re 78 3 (CS03 ∷ []) ∷
   re 80 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 79 q15 ∷
   rw 80 q21 ∷
   rw 81 q15 ∷
   re 79 3 (CS03 ∷ []) ∷
   rw 80 q21 ∷
   rw 81 q21 ∷
   rw 82 q20 ∷
   rw 83 q21 ∷
   rw 84 q20 ∷
   rw 85 q20 ∷
   rw 86 q22 ∷ []) Eq.refl

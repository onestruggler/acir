{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D344 (W : Ws) where

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
  q1 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q2 : Eqn
  q2 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q3 : Eqn
  q3 = eqn (CX13 ∷ Sw12 ∷ []) (Sw12 ∷ CX23 ∷ []) (wn 36 W)
  q4 : Eqn
  q4 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q5 : Eqn
  q5 = eqn (CX23 ∷ Sw12 ∷ []) (Sw12 ∷ CX13 ∷ []) (wn 37 W)
  q6 : Eqn
  q6 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q7 : Eqn
  q7 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q10 : Eqn
  q10 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q12 : Eqn
  q12 = eqn (CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ []) (CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ []) (wn 964 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q16 : Eqn
  q16 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q17 : Eqn
  q17 = eqn (CX12 ∷ S3 ∷ []) (S3 ∷ CX12 ∷ []) (low₃-comm ((CX₀₁ ↑)) (S))
  q18 : Eqn
  q18 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q19 : Eqn
  q19 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q20 : Eqn
  q20 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q21 : Eqn
  q21 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (wn 843 W)
  q22 : Eqn
  q22 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)

-- Bar(SSKSKK;1,2->0) passes groups of WBar(SSSSSSKiSSSSSSSSS;~1,3->0) part6: 451 steps
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part6 : ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X1 ∷ CX13 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ CX13 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part6 = derive (X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X1 ∷ CX13 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ CX13 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (re 114 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 116 q1 ∷
   re 110 5 (CS03 ∷ []) ∷
   re 112 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 111 q2 ∷
   re 112 3 (CX13 ∷ []) ∷
   rw 112 q3 ∷
   rw⁻ 113 q4 ∷
   rw 114 q5 ∷
   re 115 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 117 q1 ∷
   re 111 5 (CS03 ∷ []) ∷
   re 113 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 112 q2 ∷
   re 113 3 (CX13 ∷ []) ∷
   rw 113 q3 ∷
   rw⁻ 114 q4 ∷
   rw 115 q5 ∷
   re 116 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 118 q1 ∷
   re 112 5 (CS03 ∷ []) ∷
   re 114 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 113 q2 ∷
   re 114 3 (CX13 ∷ []) ∷
   rw 114 q3 ∷
   rw⁻ 115 q4 ∷
   rw 116 q5 ∷
   re 117 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 119 q1 ∷
   re 113 5 (CS03 ∷ []) ∷
   rw 114 q6 ∷
   re 113 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 115 q7 ∷
   rw 114 q8 ∷
   rw⁻ 113 q7 ∷
   re 114 3 (CS13 ∷ []) ∷
   re 112 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 114 q7 ∷
   rw 113 q8 ∷
   rw⁻ 112 q7 ∷
   re 113 3 (CS13 ∷ []) ∷
   re 111 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 113 q7 ∷
   rw 112 q8 ∷
   rw⁻ 111 q7 ∷
   re 112 3 (CS13 ∷ []) ∷
   re 110 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 112 q7 ∷
   rw 111 q8 ∷
   rw⁻ 110 q7 ∷
   re 111 3 (CS13 ∷ []) ∷
   re 109 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 111 q7 ∷
   rw 110 q8 ∷
   rw⁻ 109 q7 ∷
   re 110 3 (CS13 ∷ []) ∷
   re 108 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 110 q7 ∷
   rw 109 q8 ∷
   rw⁻ 108 q7 ∷
   re 109 3 (CS13 ∷ []) ∷
   re 107 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 109 q7 ∷
   rw 108 q8 ∷
   rw⁻ 107 q7 ∷
   re 108 3 (CS13 ∷ []) ∷
   re 106 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 108 q7 ∷
   rw 107 q8 ∷
   rw⁻ 106 q7 ∷
   re 107 3 (CS13 ∷ []) ∷
   re 105 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 107 q7 ∷
   rw 106 q8 ∷
   rw⁻ 105 q7 ∷
   re 106 3 (CS13 ∷ []) ∷
   rw⁻ 104 q9 ∷
   re 103 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 105 q7 ∷
   rw 104 q10 ∷
   rw⁻ 103 q7 ∷
   re 104 3 (CK31 ∷ []) ∷
   re 102 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 104 q7 ∷
   rw 103 q8 ∷
   rw⁻ 102 q7 ∷
   re 103 3 (CS13 ∷ []) ∷
   re 101 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 103 q7 ∷
   rw 102 q8 ∷
   rw⁻ 101 q7 ∷
   re 102 3 (CS13 ∷ []) ∷
   re 100 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 102 q7 ∷
   rw 101 q8 ∷
   rw⁻ 100 q7 ∷
   re 101 3 (CS13 ∷ []) ∷
   re 99 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 101 q7 ∷
   rw 100 q8 ∷
   rw⁻ 99 q7 ∷
   re 100 3 (CS13 ∷ []) ∷
   re 98 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 100 q7 ∷
   rw 99 q8 ∷
   rw⁻ 98 q7 ∷
   re 99 3 (CS13 ∷ []) ∷
   re 97 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 99 q7 ∷
   rw 98 q8 ∷
   rw⁻ 97 q7 ∷
   re 98 3 (CS13 ∷ []) ∷
   rw 96 q8 ∷
   rw 95 q8 ∷
   rw 94 q8 ∷
   rw 93 q8 ∷
   rw 92 q8 ∷
   rw 91 q8 ∷
   rw⁻ 90 q11 ∷
   rw 89 q10 ∷
   rw 88 q8 ∷
   rw 87 q8 ∷
   rw 86 q8 ∷
   rw⁻ 85 q11 ∷
   rw 84 q10 ∷
   rw⁻ 83 q11 ∷
   rw 82 q10 ∷
   rw 83 q12 ∷
   re 83 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 82 q7 ∷
   rw 83 q13 ∷
   rw 84 q7 ∷
   re 82 3 (CS03 ∷ []) ∷
   re 84 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 83 q7 ∷
   rw 84 q13 ∷
   rw 85 q7 ∷
   re 83 3 (CS03 ∷ []) ∷
   re 85 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 84 q7 ∷
   rw 85 q13 ∷
   rw 86 q7 ∷
   re 84 3 (CS03 ∷ []) ∷
   re 86 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 85 q7 ∷
   rw 86 q13 ∷
   rw 87 q7 ∷
   re 85 3 (CS03 ∷ []) ∷
   re 87 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 86 q7 ∷
   rw 87 q13 ∷
   rw 88 q7 ∷
   re 86 3 (CS03 ∷ []) ∷
   re 88 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 87 q7 ∷
   rw 88 q13 ∷
   rw 89 q7 ∷
   re 87 3 (CS03 ∷ []) ∷
   re 89 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 88 q7 ∷
   rw 89 q14 ∷
   rw 90 q7 ∷
   re 88 3 (CK30 ∷ []) ∷
   rw 89 q9 ∷
   re 91 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 90 q7 ∷
   rw 91 q13 ∷
   rw 92 q7 ∷
   re 90 3 (CS03 ∷ []) ∷
   re 92 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 91 q7 ∷
   rw 92 q13 ∷
   rw 93 q7 ∷
   re 91 3 (CS03 ∷ []) ∷
   re 93 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 92 q7 ∷
   rw 93 q13 ∷
   rw 94 q7 ∷
   re 92 3 (CS03 ∷ []) ∷
   re 94 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 93 q7 ∷
   rw 94 q13 ∷
   rw 95 q7 ∷
   re 93 3 (CS03 ∷ []) ∷
   re 95 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 94 q7 ∷
   rw 95 q13 ∷
   rw 96 q7 ∷
   re 94 3 (CS03 ∷ []) ∷
   re 96 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 95 q7 ∷
   rw 96 q13 ∷
   rw 97 q7 ∷
   re 95 3 (CS03 ∷ []) ∷
   re 97 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 96 q7 ∷
   rw 97 q13 ∷
   rw 98 q7 ∷
   re 96 3 (CS03 ∷ []) ∷
   re 98 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 97 q7 ∷
   rw 98 q13 ∷
   rw 99 q7 ∷
   re 97 3 (CS03 ∷ []) ∷
   re 99 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 98 q7 ∷
   rw 99 q13 ∷
   rw 100 q7 ∷
   re 98 3 (CS03 ∷ []) ∷
   rw 99 q14 ∷
   rw 100 q11 ∷
   rw 101 q14 ∷
   rw 102 q11 ∷
   rw 103 q13 ∷
   rw 104 q13 ∷
   rw 105 q13 ∷
   rw 106 q14 ∷
   rw 107 q11 ∷
   rw 108 q13 ∷
   rw 109 q13 ∷
   rw 110 q13 ∷
   rw 111 q13 ∷
   rw 112 q13 ∷
   rw 113 q13 ∷
   rw 114 q15 ∷
   re 82 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 81 q2 ∷
   re 82 3 (CX13 ∷ []) ∷
   rw 82 q3 ∷
   rw⁻ 83 q4 ∷
   rw 84 q5 ∷
   re 85 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 87 q1 ∷
   re 81 5 (CS03 ∷ []) ∷
   re 83 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 82 q2 ∷
   re 83 3 (CX13 ∷ []) ∷
   rw 83 q3 ∷
   rw⁻ 84 q4 ∷
   rw 85 q5 ∷
   re 86 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 88 q1 ∷
   re 82 5 (CS03 ∷ []) ∷
   re 84 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 83 q2 ∷
   re 84 3 (CX13 ∷ []) ∷
   rw 84 q3 ∷
   rw⁻ 85 q4 ∷
   rw 86 q5 ∷
   re 87 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 89 q1 ∷
   re 83 5 (CS03 ∷ []) ∷
   re 85 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 84 q2 ∷
   re 85 3 (CX13 ∷ []) ∷
   rw 85 q3 ∷
   rw⁻ 86 q4 ∷
   rw 87 q5 ∷
   re 88 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 90 q1 ∷
   re 84 5 (CS03 ∷ []) ∷
   re 86 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 85 q2 ∷
   re 86 3 (CX13 ∷ []) ∷
   rw 86 q3 ∷
   rw⁻ 87 q4 ∷
   rw 88 q5 ∷
   re 89 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 91 q1 ∷
   re 85 5 (CS03 ∷ []) ∷
   re 87 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 86 q2 ∷
   re 87 3 (CX13 ∷ []) ∷
   rw 87 q3 ∷
   rw⁻ 88 q4 ∷
   rw 89 q5 ∷
   re 90 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 92 q1 ∷
   re 86 5 (CS03 ∷ []) ∷
   re 88 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 87 q2 ∷
   re 88 3 (CX13 ∷ []) ∷
   rw 88 q3 ∷
   rw⁻ 89 q16 ∷
   rw 90 q5 ∷
   re 91 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 93 q1 ∷
   re 87 5 (CK30 ∷ []) ∷
   rw 88 q17 ∷
   re 90 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 89 q2 ∷
   re 90 3 (CX13 ∷ []) ∷
   rw 90 q3 ∷
   rw⁻ 91 q4 ∷
   rw 92 q5 ∷
   re 93 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 95 q1 ∷
   re 89 5 (CS03 ∷ []) ∷
   re 91 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 90 q2 ∷
   re 91 3 (CX13 ∷ []) ∷
   rw 91 q3 ∷
   rw⁻ 92 q4 ∷
   rw 93 q5 ∷
   re 94 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 96 q1 ∷
   re 90 5 (CS03 ∷ []) ∷
   re 92 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 91 q2 ∷
   re 92 3 (CX13 ∷ []) ∷
   rw 92 q3 ∷
   rw⁻ 93 q4 ∷
   rw 94 q5 ∷
   re 95 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 97 q1 ∷
   re 91 5 (CS03 ∷ []) ∷
   re 93 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 92 q2 ∷
   re 93 3 (CX13 ∷ []) ∷
   rw 93 q3 ∷
   rw⁻ 94 q4 ∷
   rw 95 q5 ∷
   re 96 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 98 q1 ∷
   re 92 5 (CS03 ∷ []) ∷
   re 94 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 93 q2 ∷
   re 94 3 (CX13 ∷ []) ∷
   rw 94 q3 ∷
   rw⁻ 95 q4 ∷
   rw 96 q5 ∷
   re 97 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 99 q1 ∷
   re 93 5 (CS03 ∷ []) ∷
   re 95 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 94 q2 ∷
   re 95 3 (CX13 ∷ []) ∷
   rw 95 q3 ∷
   rw⁻ 96 q4 ∷
   rw 97 q5 ∷
   re 98 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 100 q1 ∷
   re 94 5 (CS03 ∷ []) ∷
   re 96 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 95 q2 ∷
   re 96 3 (CX13 ∷ []) ∷
   rw 96 q3 ∷
   rw⁻ 97 q4 ∷
   rw 98 q5 ∷
   re 99 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 101 q1 ∷
   re 95 5 (CS03 ∷ []) ∷
   re 97 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 96 q2 ∷
   re 97 3 (CX13 ∷ []) ∷
   rw 97 q3 ∷
   rw⁻ 98 q4 ∷
   rw 99 q5 ∷
   re 100 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 102 q1 ∷
   re 96 5 (CS03 ∷ []) ∷
   re 98 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 97 q2 ∷
   re 98 3 (CX13 ∷ []) ∷
   rw 98 q3 ∷
   rw⁻ 99 q4 ∷
   rw 100 q5 ∷
   re 101 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 103 q1 ∷
   re 97 5 (CS03 ∷ []) ∷
   rw 98 q2 ∷
   re 97 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 99 q1 ∷
   re 96 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 98 q1 ∷
   re 95 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 97 q1 ∷
   re 94 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 96 q1 ∷
   re 93 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 95 q1 ∷
   re 92 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 94 q1 ∷
   re 91 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 93 q1 ∷
   re 90 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 92 q1 ∷
   re 89 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 91 q1 ∷
   rw 88 q18 ∷
   re 87 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 89 q1 ∷
   re 86 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 88 q1 ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 87 q1 ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 86 q1 ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 85 q1 ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 84 q1 ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 83 q1 ∷
   rw 80 q19 ∷
   rw 79 q19 ∷
   rw 78 q20 ∷
   rw 77 q19 ∷
   rw 76 q20 ∷
   rw 75 q20 ∷
   rw 76 q21 ∷
   rw 77 q2 ∷
   re 75 3 (CS03 ∷ []) ∷
   rw 78 q2 ∷
   re 76 3 (CS03 ∷ []) ∷
   rw 79 q2 ∷
   re 77 3 (CS03 ∷ []) ∷
   rw 80 q2 ∷
   re 78 3 (CS03 ∷ []) ∷
   rw 81 q2 ∷
   re 79 3 (CS03 ∷ []) ∷
   rw 82 q2 ∷
   re 80 3 (CS03 ∷ []) ∷
   rw 83 q2 ∷
   re 81 3 (CK30 ∷ []) ∷
   rw 82 q22 ∷
   rw 85 q2 ∷
   re 83 3 (CS03 ∷ []) ∷
   rw 86 q2 ∷
   re 84 3 (CS03 ∷ []) ∷
   rw 87 q2 ∷
   re 85 3 (CS03 ∷ []) ∷
   rw 88 q2 ∷
   re 86 3 (CS03 ∷ []) ∷
   rw 89 q2 ∷
   re 87 3 (CS03 ∷ []) ∷
   rw 90 q2 ∷
   re 88 3 (CS03 ∷ []) ∷
   rw 91 q2 ∷
   re 89 3 (CS03 ∷ []) ∷
   rw 92 q2 ∷
   re 90 3 (CS03 ∷ []) ∷
   rw 93 q2 ∷
   re 91 3 (CS03 ∷ []) ∷
   rw⁻ 92 q20 ∷
   rw⁻ 93 q20 ∷
   rw⁻ 94 q19 ∷
   rw⁻ 95 q20 ∷
   rw⁻ 96 q19 ∷
   rw⁻ 97 q19 ∷
   rw 98 q1 ∷ []) Eq.refl

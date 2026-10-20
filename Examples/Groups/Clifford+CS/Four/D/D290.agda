{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D290 (W : Ws) where

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
  q2 = eqn (Sw12 ∷ CX13 ∷ []) (CX23 ∷ Sw12 ∷ []) (wn 157 W)
  q3 : Eqn
  q3 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q4 : Eqn
  q4 = eqn (Sw12 ∷ CX23 ∷ []) (CX13 ∷ Sw12 ∷ []) (wn 158 W)
  q5 : Eqn
  q5 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q6 : Eqn
  q6 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q7 : Eqn
  q7 = eqn (CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ []) (wn 880 W)
  q8 : Eqn
  q8 = eqn (X1 ∷ S3 ∷ []) (S3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((S ↑)))
  q9 : Eqn
  q9 = eqn (CX12 ∷ S3 ∷ []) (S3 ∷ CX12 ∷ []) (low₃-comm ((CX₀₁ ↑)) (S))
  q10 : Eqn
  q10 = eqn (CK20 ∷ X1 ∷ []) (X1 ∷ CK20 ∷ []) (wn 879 W)
  q11 : Eqn
  q11 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q12 : Eqn
  q12 = eqn (CX13 ∷ X1 ∷ CX12 ∷ X1 ∷ []) (X1 ∷ CX12 ∷ X1 ∷ CX13 ∷ []) (wn 881 W)
  q13 : Eqn
  q13 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ CX12 ∷ X1 ∷ []) (X1 ∷ CX12 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (wn 882 W)
  q14 : Eqn
  q14 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q16 : Eqn
  q16 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q17 : Eqn
  q17 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q18 : Eqn
  q18 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q19 : Eqn
  q19 = eqn (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ []) (CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) (wn 852 W)
  q20 : Eqn
  q20 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q21 : Eqn
  q21 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q22 : Eqn
  q22 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q23 : Eqn
  q23 = eqn (CX13 ∷ Sw12 ∷ []) (Sw12 ∷ CX23 ∷ []) (wn 36 W)
  q24 : Eqn
  q24 = eqn (CX23 ∷ Sw12 ∷ []) (Sw12 ∷ CX13 ∷ []) (wn 37 W)
  q25 : Eqn
  q25 = eqn (CX13 ∷ S2 ∷ []) (S2 ∷ CX13 ∷ []) (wn 883 W)

-- Bar(SSKSKK;1,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~1,2->0) part1: 500 steps
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part1 : ⟪ (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ X1 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CX12 ∷ X1 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ Sw01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part1 = derive (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ X1 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CX12 ∷ X1 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ Sw01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ [])
  (rw 37 q1 ∷
   re 35 3 (CX13 ∷ []) ∷
   rw 34 q2 ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   re 32 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 31 q5 ∷
   re 32 5 (CS03 ∷ []) ∷
   rw 34 q1 ∷
   rw 33 q6 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q5 ∷
   rw 33 q7 ∷
   rw⁻ 32 q6 ∷
   rw 35 q1 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 34 q5 ∷
   rw 31 q1 ∷
   rw 30 q6 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q5 ∷
   rw 30 q7 ∷
   rw⁻ 29 q6 ∷
   rw 32 q1 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 31 q5 ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
   re 34 3 (CX13 ∷ []) ∷
   rw 33 q2 ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   re 31 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 30 q5 ∷
   re 31 5 (CS03 ∷ []) ∷
   rw 33 q1 ∷
   rw 32 q6 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q5 ∷
   rw 32 q7 ∷
   rw⁻ 31 q6 ∷
   rw 34 q1 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 33 q5 ∷
   rw 30 q1 ∷
   rw 29 q6 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q5 ∷
   rw 29 q7 ∷
   rw⁻ 28 q6 ∷
   rw 31 q1 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 30 q5 ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   re 33 3 (CX13 ∷ []) ∷
   rw 32 q2 ∷
   rw 31 q3 ∷
   rw 30 q4 ∷
   re 30 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 29 q5 ∷
   re 30 5 (CS03 ∷ []) ∷
   rw 32 q1 ∷
   rw 31 q6 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q5 ∷
   rw 31 q7 ∷
   rw⁻ 30 q6 ∷
   rw 33 q1 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 32 q5 ∷
   rw⁻ 27 q8 ∷
   rw⁻ 28 q9 ∷
   rw⁻ 29 q8 ∷
   rw 28 q1 ∷
   rw 27 q6 ∷
   re 26 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 28 q5 ∷
   rw 27 q10 ∷
   rw⁻ 26 q6 ∷
   rw 29 q1 ∷
   re 27 3 (CK30 ∷ []) ∷
   rw 28 q5 ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CX13 ∷ []) ∷
   rw 30 q2 ∷
   rw 29 q11 ∷
   rw 28 q4 ∷
   re 28 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 27 q5 ∷
   re 28 5 (CK30 ∷ []) ∷
   rw 30 q1 ∷
   rw 29 q6 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q5 ∷
   rw 29 q10 ∷
   rw⁻ 28 q6 ∷
   rw 31 q1 ∷
   re 29 3 (CK30 ∷ []) ∷
   rw 30 q5 ∷
   rw⁻ 25 q8 ∷
   rw⁻ 26 q9 ∷
   rw⁻ 27 q8 ∷
   rw 26 q1 ∷
   rw 25 q6 ∷
   re 24 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 26 q5 ∷
   rw 25 q10 ∷
   rw⁻ 24 q6 ∷
   rw 27 q1 ∷
   re 25 3 (CK30 ∷ []) ∷
   rw 26 q5 ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   re 29 3 (CX13 ∷ []) ∷
   rw 28 q2 ∷
   rw 27 q11 ∷
   rw 26 q4 ∷
   re 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q5 ∷
   re 26 5 (CK30 ∷ []) ∷
   rw 28 q1 ∷
   rw 27 q6 ∷
   re 26 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 28 q5 ∷
   rw 27 q10 ∷
   rw⁻ 26 q6 ∷
   rw 29 q1 ∷
   re 27 3 (CK30 ∷ []) ∷
   rw 28 q5 ∷
   rw 23 q12 ∷
   rw 17 q13 ∷
   rw 91 q14 ∷
   rw⁻ 90 q15 ∷
   rw 89 q16 ∷
   rw⁻ 88 q15 ∷
   rw⁻ 87 q15 ∷
   rw⁻ 86 q15 ∷
   rw⁻ 85 q15 ∷
   rw 84 q16 ∷
   rw⁻ 83 q15 ∷
   rw⁻ 82 q15 ∷
   rw⁻ 81 q15 ∷
   rw 80 q17 ∷
   rw 79 q17 ∷
   rw 78 q17 ∷
   rw 77 q17 ∷
   rw 76 q17 ∷
   rw 75 q17 ∷
   rw 74 q17 ∷
   rw 73 q17 ∷
   rw 72 q17 ∷
   rw⁻ 71 q15 ∷
   rw 70 q16 ∷
   rw⁻ 69 q15 ∷
   rw⁻ 68 q15 ∷
   rw⁻ 67 q15 ∷
   rw 66 q17 ∷
   rw 65 q17 ∷
   rw 64 q17 ∷
   rw 63 q17 ∷
   rw 62 q17 ∷
   rw 61 q17 ∷
   rw 60 q17 ∷
   rw 59 q17 ∷
   rw 58 q17 ∷
   rw 57 q17 ∷
   rw 56 q17 ∷
   rw 55 q17 ∷
   rw 54 q17 ∷
   rw 53 q17 ∷
   rw 52 q17 ∷
   rw 51 q17 ∷
   rw 50 q17 ∷
   rw 49 q17 ∷
   re 48 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q18 ∷
   rw 49 q16 ∷
   rw⁻ 48 q18 ∷
   re 49 3 (CK31 ∷ []) ∷
   re 47 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q18 ∷
   rw 48 q16 ∷
   rw⁻ 47 q18 ∷
   re 48 3 (CK31 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q18 ∷
   rw 47 q17 ∷
   rw⁻ 46 q18 ∷
   re 47 3 (CS13 ∷ []) ∷
   re 45 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q18 ∷
   rw 46 q16 ∷
   rw⁻ 45 q18 ∷
   re 46 3 (CK31 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q18 ∷
   rw 45 q17 ∷
   rw⁻ 44 q18 ∷
   re 45 3 (CS13 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q18 ∷
   rw 44 q17 ∷
   rw⁻ 43 q18 ∷
   re 44 3 (CS13 ∷ []) ∷
   rw 44 q19 ∷
   rw 43 q20 ∷
   rw 44 q20 ∷
   rw 45 q20 ∷
   rw 46 q20 ∷
   rw 47 q20 ∷
   rw 48 q20 ∷
   rw 49 q20 ∷
   rw 50 q20 ∷
   rw 51 q20 ∷
   rw 52 q20 ∷
   rw 53 q20 ∷
   rw 54 q20 ∷
   rw 55 q20 ∷
   rw 56 q20 ∷
   rw 57 q20 ∷
   rw 58 q20 ∷
   rw 59 q20 ∷
   rw 60 q20 ∷
   rw 61 q15 ∷
   rw 62 q15 ∷
   rw 63 q15 ∷
   rw 64 q21 ∷
   rw 65 q15 ∷
   rw 66 q20 ∷
   rw 67 q20 ∷
   rw 68 q20 ∷
   rw 69 q20 ∷
   rw 70 q20 ∷
   rw 71 q20 ∷
   rw 72 q20 ∷
   rw 73 q20 ∷
   rw 74 q20 ∷
   rw 75 q15 ∷
   rw 76 q15 ∷
   rw 77 q15 ∷
   rw 78 q21 ∷
   rw 79 q15 ∷
   rw 80 q15 ∷
   rw 81 q15 ∷
   rw 82 q15 ∷
   rw 83 q21 ∷
   rw 84 q15 ∷
   re 86 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 85 q18 ∷
   rw 86 q20 ∷
   rw 87 q18 ∷
   re 85 3 (CS03 ∷ []) ∷
   re 87 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 86 q18 ∷
   rw 87 q20 ∷
   rw 88 q18 ∷
   re 86 3 (CS03 ∷ []) ∷
   re 88 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 87 q18 ∷
   rw 88 q21 ∷
   rw 89 q18 ∷
   re 87 3 (CK30 ∷ []) ∷
   re 89 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 88 q18 ∷
   rw 89 q20 ∷
   rw 90 q18 ∷
   re 88 3 (CS03 ∷ []) ∷
   re 90 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 89 q18 ∷
   rw 90 q21 ∷
   rw 91 q18 ∷
   re 89 3 (CK30 ∷ []) ∷
   re 91 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 90 q18 ∷
   rw 91 q21 ∷
   rw 92 q18 ∷
   re 90 3 (CK30 ∷ []) ∷
   rw 91 q22 ∷
   re 43 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 42 q23 ∷
   rw⁻ 43 q3 ∷
   rw 44 q24 ∷
   re 42 3 (CS02 ∷ []) ∷
   re 44 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 43 q23 ∷
   rw⁻ 44 q3 ∷
   rw 45 q24 ∷
   re 43 3 (CS02 ∷ []) ∷
   re 45 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 44 q23 ∷
   rw⁻ 45 q3 ∷
   rw 46 q24 ∷
   re 44 3 (CS02 ∷ []) ∷
   re 46 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 45 q23 ∷
   rw⁻ 46 q3 ∷
   rw 47 q24 ∷
   re 45 3 (CS02 ∷ []) ∷
   re 47 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 46 q23 ∷
   rw⁻ 47 q3 ∷
   rw 48 q24 ∷
   re 46 3 (CS02 ∷ []) ∷
   re 48 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 47 q23 ∷
   rw⁻ 48 q3 ∷
   rw 49 q24 ∷
   re 47 3 (CS02 ∷ []) ∷
   re 49 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 48 q23 ∷
   rw⁻ 49 q3 ∷
   rw 50 q24 ∷
   re 48 3 (CS02 ∷ []) ∷
   re 50 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 49 q23 ∷
   rw⁻ 50 q3 ∷
   rw 51 q24 ∷
   re 49 3 (CS02 ∷ []) ∷
   re 51 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 50 q23 ∷
   rw⁻ 51 q3 ∷
   rw 52 q24 ∷
   re 50 3 (CS02 ∷ []) ∷
   re 52 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 51 q23 ∷
   rw⁻ 52 q3 ∷
   rw 53 q24 ∷
   re 51 3 (CS02 ∷ []) ∷
   re 53 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 52 q23 ∷
   rw⁻ 53 q3 ∷
   rw 54 q24 ∷
   re 52 3 (CS02 ∷ []) ∷
   re 54 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 53 q23 ∷
   rw⁻ 54 q3 ∷
   rw 55 q24 ∷
   re 53 3 (CS02 ∷ []) ∷
   re 55 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 54 q23 ∷
   rw⁻ 55 q3 ∷
   rw 56 q24 ∷
   re 54 3 (CS02 ∷ []) ∷
   re 56 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 55 q23 ∷
   rw⁻ 56 q3 ∷
   rw 57 q24 ∷
   re 55 3 (CS02 ∷ []) ∷
   re 57 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 56 q23 ∷
   rw⁻ 57 q3 ∷
   rw 58 q24 ∷
   re 56 3 (CS02 ∷ []) ∷
   re 58 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 57 q23 ∷
   rw⁻ 58 q3 ∷
   rw 59 q24 ∷
   re 57 3 (CS02 ∷ []) ∷
   re 59 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 58 q23 ∷
   rw⁻ 59 q3 ∷
   rw 60 q24 ∷
   re 58 3 (CS02 ∷ []) ∷
   re 60 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 59 q23 ∷
   rw⁻ 60 q3 ∷
   rw 61 q24 ∷
   re 59 3 (CS02 ∷ []) ∷
   rw 60 q25 ∷
   rw 61 q25 ∷
   rw 62 q25 ∷
   re 64 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 63 q23 ∷
   rw⁻ 64 q11 ∷
   rw 65 q24 ∷
   re 63 3 (CK20 ∷ []) ∷
   rw 64 q25 ∷
   re 66 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 65 q23 ∷
   rw⁻ 66 q3 ∷
   rw 67 q24 ∷
   re 65 3 (CS02 ∷ []) ∷
   re 67 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 66 q23 ∷
   rw⁻ 67 q3 ∷
   rw 68 q24 ∷
   re 66 3 (CS02 ∷ []) ∷
   re 68 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 67 q23 ∷
   rw⁻ 68 q3 ∷
   rw 69 q24 ∷
   re 67 3 (CS02 ∷ []) ∷
   re 69 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 68 q23 ∷
   rw⁻ 69 q3 ∷
   rw 70 q24 ∷
   re 68 3 (CS02 ∷ []) ∷
   re 70 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 69 q23 ∷
   rw⁻ 70 q3 ∷
   rw 71 q24 ∷
   re 69 3 (CS02 ∷ []) ∷
   re 71 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 70 q23 ∷
   rw⁻ 71 q3 ∷
   rw 72 q24 ∷
   re 70 3 (CS02 ∷ []) ∷
   re 72 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 71 q23 ∷
   rw⁻ 72 q3 ∷
   rw 73 q24 ∷
   re 71 3 (CS02 ∷ []) ∷
   re 73 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 72 q23 ∷
   rw⁻ 73 q3 ∷
   rw 74 q24 ∷
   re 72 3 (CS02 ∷ []) ∷
   re 74 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 73 q23 ∷
   rw⁻ 74 q3 ∷
   rw 75 q24 ∷
   re 73 3 (CS02 ∷ []) ∷
   rw 74 q25 ∷
   rw 75 q25 ∷
   rw 76 q25 ∷
   re 78 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 77 q23 ∷
   rw⁻ 78 q11 ∷
   rw 79 q24 ∷
   re 77 3 (CK20 ∷ []) ∷
   rw 78 q25 ∷
   rw 79 q25 ∷
   rw 80 q25 ∷
   rw 81 q25 ∷
   re 83 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 82 q23 ∷
   rw⁻ 83 q11 ∷
   rw 84 q24 ∷
   re 82 3 (CK20 ∷ []) ∷
   rw 83 q25 ∷
   rw 84 q14 ∷
   rw⁻ 83 q15 ∷
   rw 82 q16 ∷
   rw⁻ 81 q15 ∷
   rw⁻ 80 q15 ∷
   rw⁻ 79 q15 ∷
   rw⁻ 78 q15 ∷
   rw 77 q16 ∷
   rw⁻ 76 q15 ∷
   rw⁻ 75 q15 ∷
   rw⁻ 74 q15 ∷
   rw 73 q17 ∷
   rw 72 q17 ∷
   rw 71 q17 ∷
   rw 70 q17 ∷
   rw 69 q17 ∷
   rw 68 q17 ∷
   rw 67 q17 ∷
   rw 66 q17 ∷
   rw 65 q17 ∷
   rw⁻ 64 q15 ∷
   rw 63 q16 ∷
   rw⁻ 62 q15 ∷
   rw⁻ 61 q15 ∷
   rw⁻ 60 q15 ∷
   rw 59 q17 ∷
   rw 58 q17 ∷
   rw 57 q17 ∷
   rw 56 q17 ∷
   rw 55 q17 ∷
   rw 54 q17 ∷
   rw 53 q17 ∷
   rw 52 q17 ∷
   rw 51 q17 ∷
   rw 50 q17 ∷
   rw 49 q17 ∷
   rw 48 q17 ∷
   rw 47 q17 ∷
   rw 46 q17 ∷
   rw 45 q17 ∷
   rw 44 q17 ∷
   rw 43 q17 ∷
   rw 42 q17 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q18 ∷
   rw 42 q17 ∷
   rw⁻ 41 q18 ∷
   re 42 3 (CS13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q18 ∷
   rw 41 q17 ∷
   rw⁻ 40 q18 ∷
   re 41 3 (CS13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q18 ∷
   rw 40 q17 ∷
   rw⁻ 39 q18 ∷
   re 40 3 (CS13 ∷ []) ∷ []) Eq.refl

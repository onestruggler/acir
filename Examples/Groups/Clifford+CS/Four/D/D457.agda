{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D457 (W : Ws) where

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
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 3 W
  q3 : Eqn
  q3 = wE 157 W
  q4 : Eqn
  q4 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q5 : Eqn
  q5 = wE 158 W
  q6 : Eqn
  q6 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q7 : Eqn
  q7 = wE 879 W
  q8 : Eqn
  q8 = wE 880 W
  q9 : Eqn
  q9 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q10 : Eqn
  q10 = wE 881 W
  q11 : Eqn
  q11 = eqn (X1 ∷ S3 ∷ []) (S3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((S ↑)))
  q12 : Eqn
  q12 = eqn (CX12 ∷ S3 ∷ []) (S3 ∷ CX12 ∷ []) (low₃-comm ((CX₀₁ ↑)) (S))
  q13 : Eqn
  q13 = wE 882 W
  q14 : Eqn
  q14 = wE 5 W
  q15 : Eqn
  q15 = wE 140 W
  q16 : Eqn
  q16 = wE 7 W

-- Bar(SSKSKK;1,3->0) passes groups of WBar(SSKSKK;~1,2->0) part2: 500 steps
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part2 : ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ X1 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X1 ∷ CX12 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ Sw01 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part2 = derive (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ X1 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X1 ∷ CX12 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ Sw01 ∷ [])
  (rw 57 q1 ∷
   re 55 3 (CK30 ∷ []) ∷
   rw 56 q2 ∷
   re 55 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 61 q1 ∷
   re 59 3 (CX13 ∷ []) ∷
   rw 58 q3 ∷
   rw 57 q4 ∷
   rw 56 q5 ∷
   re 56 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 55 q2 ∷
   re 56 5 (CK30 ∷ []) ∷
   rw 58 q1 ∷
   rw 57 q6 ∷
   re 56 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 58 q2 ∷
   rw 57 q7 ∷
   rw⁻ 56 q6 ∷
   rw 59 q1 ∷
   re 57 3 (CK30 ∷ []) ∷
   rw 58 q2 ∷
   rw 55 q1 ∷
   rw 54 q6 ∷
   re 53 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 55 q2 ∷
   rw 54 q7 ∷
   rw⁻ 53 q6 ∷
   rw 56 q1 ∷
   re 54 3 (CK30 ∷ []) ∷
   rw 55 q2 ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 60 q1 ∷
   re 58 3 (CX13 ∷ []) ∷
   rw 57 q3 ∷
   rw 56 q4 ∷
   rw 55 q5 ∷
   re 55 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 54 q2 ∷
   re 55 5 (CK30 ∷ []) ∷
   rw 57 q1 ∷
   rw 56 q6 ∷
   re 55 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 57 q2 ∷
   rw 56 q7 ∷
   rw⁻ 55 q6 ∷
   rw 58 q1 ∷
   re 56 3 (CK30 ∷ []) ∷
   rw 57 q2 ∷
   rw 54 q1 ∷
   rw 53 q6 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 54 q2 ∷
   rw 53 q8 ∷
   rw⁻ 52 q6 ∷
   rw 55 q1 ∷
   re 53 3 (CS03 ∷ []) ∷
   rw 54 q2 ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q1 ∷
   re 57 3 (CX13 ∷ []) ∷
   rw 56 q3 ∷
   rw 55 q9 ∷
   rw 54 q5 ∷
   re 54 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 53 q2 ∷
   re 54 5 (CS03 ∷ []) ∷
   rw 56 q1 ∷
   rw 55 q6 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q2 ∷
   rw 55 q8 ∷
   rw⁻ 54 q6 ∷
   rw 57 q1 ∷
   re 55 3 (CS03 ∷ []) ∷
   rw 56 q2 ∷
   rw 53 q1 ∷
   rw 52 q6 ∷
   re 51 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 53 q2 ∷
   rw 52 q7 ∷
   rw⁻ 51 q6 ∷
   rw 54 q1 ∷
   re 52 3 (CK30 ∷ []) ∷
   rw 53 q2 ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q1 ∷
   re 56 3 (CX13 ∷ []) ∷
   rw 55 q3 ∷
   rw 54 q4 ∷
   rw 53 q5 ∷
   re 53 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 52 q2 ∷
   re 53 5 (CK30 ∷ []) ∷
   rw 55 q1 ∷
   rw 54 q6 ∷
   re 53 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 55 q2 ∷
   rw 54 q7 ∷
   rw⁻ 53 q6 ∷
   rw 56 q1 ∷
   re 54 3 (CK30 ∷ []) ∷
   rw 55 q2 ∷
   rw 52 q1 ∷
   rw 51 q6 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q2 ∷
   rw 51 q8 ∷
   rw⁻ 50 q6 ∷
   rw 53 q1 ∷
   re 51 3 (CS03 ∷ []) ∷
   rw 52 q2 ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 57 q1 ∷
   re 55 3 (CX13 ∷ []) ∷
   rw 54 q3 ∷
   rw 53 q9 ∷
   rw 52 q5 ∷
   re 52 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 51 q2 ∷
   re 52 5 (CS03 ∷ []) ∷
   rw 54 q1 ∷
   rw 53 q6 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 54 q2 ∷
   rw 53 q8 ∷
   rw⁻ 52 q6 ∷
   rw 55 q1 ∷
   re 53 3 (CS03 ∷ []) ∷
   rw 54 q2 ∷
   rw 51 q1 ∷
   rw 50 q6 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q2 ∷
   rw 50 q8 ∷
   rw⁻ 49 q6 ∷
   rw 52 q1 ∷
   re 50 3 (CS03 ∷ []) ∷
   rw 51 q2 ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q1 ∷
   re 54 3 (CX13 ∷ []) ∷
   rw 53 q3 ∷
   rw 52 q9 ∷
   rw 51 q5 ∷
   re 51 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 50 q2 ∷
   re 51 5 (CS03 ∷ []) ∷
   rw 53 q1 ∷
   rw 52 q6 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q2 ∷
   rw 52 q8 ∷
   rw⁻ 51 q6 ∷
   rw 54 q1 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw 53 q2 ∷
   rw 48 q10 ∷
   rw 49 q1 ∷
   rw 48 q6 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q2 ∷
   rw 48 q8 ∷
   rw⁻ 47 q6 ∷
   rw 50 q1 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 49 q2 ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q1 ∷
   re 52 3 (CX13 ∷ []) ∷
   rw 51 q3 ∷
   rw 50 q9 ∷
   rw 49 q5 ∷
   re 49 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 48 q2 ∷
   re 49 5 (CS03 ∷ []) ∷
   rw 51 q1 ∷
   rw 50 q6 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q2 ∷
   rw 50 q8 ∷
   rw⁻ 49 q6 ∷
   rw 52 q1 ∷
   re 50 3 (CS03 ∷ []) ∷
   rw 51 q2 ∷
   rw 48 q1 ∷
   rw 47 q6 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q2 ∷
   rw 47 q8 ∷
   rw⁻ 46 q6 ∷
   rw 49 q1 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 48 q2 ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q1 ∷
   re 51 3 (CX13 ∷ []) ∷
   rw 50 q3 ∷
   rw 49 q9 ∷
   rw 48 q5 ∷
   re 48 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 47 q2 ∷
   re 48 5 (CS03 ∷ []) ∷
   rw 50 q1 ∷
   rw 49 q6 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q2 ∷
   rw 49 q8 ∷
   rw⁻ 48 q6 ∷
   rw 51 q1 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 50 q2 ∷
   rw 47 q1 ∷
   rw 46 q6 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q2 ∷
   rw 46 q8 ∷
   rw⁻ 45 q6 ∷
   rw 48 q1 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 47 q2 ∷
   re 46 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q1 ∷
   re 50 3 (CX13 ∷ []) ∷
   rw 49 q3 ∷
   rw 48 q9 ∷
   rw 47 q5 ∷
   re 47 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 46 q2 ∷
   re 47 5 (CS03 ∷ []) ∷
   rw 49 q1 ∷
   rw 48 q6 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q2 ∷
   rw 48 q8 ∷
   rw⁻ 47 q6 ∷
   rw 50 q1 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 49 q2 ∷
   rw 46 q1 ∷
   rw 45 q6 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q2 ∷
   rw 45 q8 ∷
   rw⁻ 44 q6 ∷
   rw 47 q1 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 46 q2 ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q1 ∷
   re 49 3 (CX13 ∷ []) ∷
   rw 48 q3 ∷
   rw 47 q9 ∷
   rw 46 q5 ∷
   re 46 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 45 q2 ∷
   re 46 5 (CS03 ∷ []) ∷
   rw 48 q1 ∷
   rw 47 q6 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q2 ∷
   rw 47 q8 ∷
   rw⁻ 46 q6 ∷
   rw 49 q1 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 48 q2 ∷
   rw 45 q1 ∷
   rw 44 q6 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q2 ∷
   rw 44 q8 ∷
   rw⁻ 43 q6 ∷
   rw 46 q1 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 45 q2 ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q1 ∷
   re 48 3 (CX13 ∷ []) ∷
   rw 47 q3 ∷
   rw 46 q9 ∷
   rw 45 q5 ∷
   re 45 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 44 q2 ∷
   re 45 5 (CS03 ∷ []) ∷
   rw 47 q1 ∷
   rw 46 q6 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q2 ∷
   rw 46 q8 ∷
   rw⁻ 45 q6 ∷
   rw 48 q1 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 47 q2 ∷
   rw 44 q1 ∷
   rw 43 q6 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q2 ∷
   rw 43 q8 ∷
   rw⁻ 42 q6 ∷
   rw 45 q1 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 44 q2 ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   re 47 3 (CX13 ∷ []) ∷
   rw 46 q3 ∷
   rw 45 q9 ∷
   rw 44 q5 ∷
   re 44 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 43 q2 ∷
   re 44 5 (CS03 ∷ []) ∷
   rw 46 q1 ∷
   rw 45 q6 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q2 ∷
   rw 45 q8 ∷
   rw⁻ 44 q6 ∷
   rw 47 q1 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 46 q2 ∷
   rw⁻ 41 q11 ∷
   rw⁻ 42 q12 ∷
   rw⁻ 43 q11 ∷
   rw 42 q1 ∷
   rw 41 q6 ∷
   re 40 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 42 q2 ∷
   rw 41 q7 ∷
   rw⁻ 40 q6 ∷
   rw 43 q1 ∷
   re 41 3 (CK30 ∷ []) ∷
   rw 42 q2 ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   re 45 3 (CX13 ∷ []) ∷
   rw 44 q3 ∷
   rw 43 q4 ∷
   rw 42 q5 ∷
   re 42 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 41 q2 ∷
   re 42 5 (CK30 ∷ []) ∷
   rw 44 q1 ∷
   rw 43 q6 ∷
   re 42 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 44 q2 ∷
   rw 43 q7 ∷
   rw⁻ 42 q6 ∷
   rw 45 q1 ∷
   re 43 3 (CK30 ∷ []) ∷
   rw 44 q2 ∷
   rw 41 q1 ∷
   rw 40 q6 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q2 ∷
   rw 40 q8 ∷
   rw⁻ 39 q6 ∷
   rw 42 q1 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q2 ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q1 ∷
   re 44 3 (CX13 ∷ []) ∷
   rw 43 q3 ∷
   rw 42 q9 ∷
   rw 41 q5 ∷
   re 41 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 40 q2 ∷
   re 41 5 (CS03 ∷ []) ∷
   rw 43 q1 ∷
   rw 42 q6 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q2 ∷
   rw 42 q8 ∷
   rw⁻ 41 q6 ∷
   rw 44 q1 ∷
   re 42 3 (CS03 ∷ []) ∷
   rw 43 q2 ∷
   rw 40 q1 ∷
   rw 39 q6 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q2 ∷
   rw 39 q8 ∷
   rw⁻ 38 q6 ∷
   rw 41 q1 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 40 q2 ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q1 ∷
   re 43 3 (CX13 ∷ []) ∷
   rw 42 q3 ∷
   rw 41 q9 ∷
   rw 40 q5 ∷
   re 40 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 39 q2 ∷
   re 40 5 (CS03 ∷ []) ∷
   rw 42 q1 ∷
   rw 41 q6 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q2 ∷
   rw 41 q8 ∷
   rw⁻ 40 q6 ∷
   rw 43 q1 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 42 q2 ∷
   rw 39 q1 ∷
   rw 38 q6 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q2 ∷
   rw 38 q8 ∷
   rw⁻ 37 q6 ∷
   rw 40 q1 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 39 q2 ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   re 42 3 (CX13 ∷ []) ∷
   rw 41 q3 ∷
   rw 40 q9 ∷
   rw 39 q5 ∷
   re 39 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 38 q2 ∷
   re 39 5 (CS03 ∷ []) ∷
   rw 41 q1 ∷
   rw 40 q6 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q2 ∷
   rw 40 q8 ∷
   rw⁻ 39 q6 ∷
   rw 42 q1 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q2 ∷
   rw⁻ 36 q11 ∷
   rw⁻ 37 q12 ∷
   rw⁻ 38 q11 ∷
   rw 37 q1 ∷
   rw 36 q6 ∷
   re 35 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 37 q2 ∷
   rw 36 q7 ∷
   rw⁻ 35 q6 ∷
   rw 38 q1 ∷
   re 36 3 (CK30 ∷ []) ∷
   rw 37 q2 ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   re 40 3 (CX13 ∷ []) ∷
   rw 39 q3 ∷
   rw 38 q4 ∷
   rw 37 q5 ∷
   re 37 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   re 37 5 (CK30 ∷ []) ∷
   rw 39 q1 ∷
   rw 38 q6 ∷
   re 37 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 39 q2 ∷
   rw 38 q7 ∷
   rw⁻ 37 q6 ∷
   rw 40 q1 ∷
   re 38 3 (CK30 ∷ []) ∷
   rw 39 q2 ∷
   rw⁻ 34 q11 ∷
   rw⁻ 35 q12 ∷
   rw⁻ 36 q11 ∷
   rw 35 q1 ∷
   rw 34 q6 ∷
   re 33 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   rw 34 q7 ∷
   rw⁻ 33 q6 ∷
   rw 36 q1 ∷
   re 34 3 (CK30 ∷ []) ∷
   rw 35 q2 ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   re 38 3 (CX13 ∷ []) ∷
   rw 37 q3 ∷
   rw 36 q4 ∷
   rw 35 q5 ∷
   re 35 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   re 35 5 (CK30 ∷ []) ∷
   rw 37 q1 ∷
   rw 36 q6 ∷
   re 35 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 37 q2 ∷
   rw 36 q7 ∷
   rw⁻ 35 q6 ∷
   rw 38 q1 ∷
   re 36 3 (CK30 ∷ []) ∷
   rw 37 q2 ∷
   rw 32 q10 ∷
   rw 26 q13 ∷
   rw 64 q14 ∷
   rw 63 q15 ∷
   rw 62 q15 ∷
   rw 61 q16 ∷
   rw 60 q15 ∷
   rw 59 q16 ∷
   rw 58 q16 ∷
   re 57 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷ []) Eq.refl

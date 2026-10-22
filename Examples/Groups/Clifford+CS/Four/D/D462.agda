{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D462 (W : Ws) where

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
  q1 = wE 880 W
  q2 : Eqn
  q2 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = wE 157 W
  q6 : Eqn
  q6 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q7 : Eqn
  q7 = wE 158 W
  q8 : Eqn
  q8 = eqn (X1 ∷ S3 ∷ []) (S3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((S ↑)))
  q9 : Eqn
  q9 = eqn (CX12 ∷ S3 ∷ []) (S3 ∷ CX12 ∷ []) (low₃-comm ((CX₀₁ ↑)) (S))
  q10 : Eqn
  q10 = wE 879 W
  q11 : Eqn
  q11 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q12 : Eqn
  q12 = wE 881 W
  q13 : Eqn
  q13 = wE 946 W
  q14 : Eqn
  q14 = wE 5 W
  q15 : Eqn
  q15 = wE 140 W
  q16 : Eqn
  q16 = wE 7 W
  q17 : Eqn
  q17 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q18 : Eqn
  q18 = wE 802 W
  q19 : Eqn
  q19 = wE 27 W
  q20 : Eqn
  q20 = wE 142 W
  q21 : Eqn
  q21 = wE 31 W
  q22 : Eqn
  q22 = wE 36 W
  q23 : Eqn
  q23 = wE 37 W
  q24 : Eqn
  q24 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q25 : Eqn
  q25 = wE 1180 W

-- Bar(SSSKSS;1,3->0) passes groups of WBar(SSKSKK;~1,2->0) part3: 500 steps
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part3 : ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ X1 ∷ Sw23 ∷ CX12 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X1 ∷ CX12 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part3 = derive (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ X1 ∷ Sw23 ∷ CX12 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X1 ∷ CX12 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw 43 q1 ∷
   rw⁻ 42 q2 ∷
   rw 45 q3 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 44 q4 ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q3 ∷
   re 47 3 (CX13 ∷ []) ∷
   rw 46 q5 ∷
   rw 45 q6 ∷
   rw 44 q7 ∷
   re 44 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 43 q4 ∷
   re 44 5 (CS03 ∷ []) ∷
   rw 46 q3 ∷
   rw 45 q2 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q4 ∷
   rw 45 q1 ∷
   rw⁻ 44 q2 ∷
   rw 47 q3 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 46 q4 ∷
   rw 43 q3 ∷
   rw 42 q2 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q4 ∷
   rw 42 q1 ∷
   rw⁻ 41 q2 ∷
   rw 44 q3 ∷
   re 42 3 (CS03 ∷ []) ∷
   rw 43 q4 ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q3 ∷
   re 46 3 (CX13 ∷ []) ∷
   rw 45 q5 ∷
   rw 44 q6 ∷
   rw 43 q7 ∷
   re 43 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 42 q4 ∷
   re 43 5 (CS03 ∷ []) ∷
   rw 45 q3 ∷
   rw 44 q2 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q4 ∷
   rw 44 q1 ∷
   rw⁻ 43 q2 ∷
   rw 46 q3 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 45 q4 ∷
   rw⁻ 40 q8 ∷
   rw⁻ 41 q9 ∷
   rw⁻ 42 q8 ∷
   rw 41 q3 ∷
   rw 40 q2 ∷
   re 39 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 41 q4 ∷
   rw 40 q10 ∷
   rw⁻ 39 q2 ∷
   rw 42 q3 ∷
   re 40 3 (CK30 ∷ []) ∷
   rw 41 q4 ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q3 ∷
   re 44 3 (CX13 ∷ []) ∷
   rw 43 q5 ∷
   rw 42 q11 ∷
   rw 41 q7 ∷
   re 41 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 40 q4 ∷
   re 41 5 (CK30 ∷ []) ∷
   rw 43 q3 ∷
   rw 42 q2 ∷
   re 41 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 43 q4 ∷
   rw 42 q10 ∷
   rw⁻ 41 q2 ∷
   rw 44 q3 ∷
   re 42 3 (CK30 ∷ []) ∷
   rw 43 q4 ∷
   rw 40 q3 ∷
   rw 39 q2 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q4 ∷
   rw 39 q1 ∷
   rw⁻ 38 q2 ∷
   rw 41 q3 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 40 q4 ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q3 ∷
   re 43 3 (CX13 ∷ []) ∷
   rw 42 q5 ∷
   rw 41 q6 ∷
   rw 40 q7 ∷
   re 40 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 39 q4 ∷
   re 40 5 (CS03 ∷ []) ∷
   rw 42 q3 ∷
   rw 41 q2 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q4 ∷
   rw 41 q1 ∷
   rw⁻ 40 q2 ∷
   rw 43 q3 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 42 q4 ∷
   rw 39 q3 ∷
   rw 38 q2 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q4 ∷
   rw 38 q1 ∷
   rw⁻ 37 q2 ∷
   rw 40 q3 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 39 q4 ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q3 ∷
   re 42 3 (CX13 ∷ []) ∷
   rw 41 q5 ∷
   rw 40 q6 ∷
   rw 39 q7 ∷
   re 39 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 38 q4 ∷
   re 39 5 (CS03 ∷ []) ∷
   rw 41 q3 ∷
   rw 40 q2 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q4 ∷
   rw 40 q1 ∷
   rw⁻ 39 q2 ∷
   rw 42 q3 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q4 ∷
   rw 38 q3 ∷
   rw 37 q2 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q4 ∷
   rw 37 q1 ∷
   rw⁻ 36 q2 ∷
   rw 39 q3 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 38 q4 ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q3 ∷
   re 41 3 (CX13 ∷ []) ∷
   rw 40 q5 ∷
   rw 39 q6 ∷
   rw 38 q7 ∷
   re 38 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 37 q4 ∷
   re 38 5 (CS03 ∷ []) ∷
   rw 40 q3 ∷
   rw 39 q2 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q4 ∷
   rw 39 q1 ∷
   rw⁻ 38 q2 ∷
   rw 41 q3 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 40 q4 ∷
   rw 37 q3 ∷
   rw 36 q2 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q4 ∷
   rw 36 q1 ∷
   rw⁻ 35 q2 ∷
   rw 38 q3 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q4 ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q3 ∷
   re 40 3 (CX13 ∷ []) ∷
   rw 39 q5 ∷
   rw 38 q6 ∷
   rw 37 q7 ∷
   re 37 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 36 q4 ∷
   re 37 5 (CS03 ∷ []) ∷
   rw 39 q3 ∷
   rw 38 q2 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q4 ∷
   rw 38 q1 ∷
   rw⁻ 37 q2 ∷
   rw 40 q3 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 39 q4 ∷
   rw 36 q3 ∷
   rw 35 q2 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q4 ∷
   rw 35 q1 ∷
   rw⁻ 34 q2 ∷
   rw 37 q3 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q4 ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q3 ∷
   re 39 3 (CX13 ∷ []) ∷
   rw 38 q5 ∷
   rw 37 q6 ∷
   rw 36 q7 ∷
   re 36 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 35 q4 ∷
   re 36 5 (CS03 ∷ []) ∷
   rw 38 q3 ∷
   rw 37 q2 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q4 ∷
   rw 37 q1 ∷
   rw⁻ 36 q2 ∷
   rw 39 q3 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 38 q4 ∷
   rw 35 q3 ∷
   rw 34 q2 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q4 ∷
   rw 34 q1 ∷
   rw⁻ 33 q2 ∷
   rw 36 q3 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 35 q4 ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q3 ∷
   re 38 3 (CX13 ∷ []) ∷
   rw 37 q5 ∷
   rw 36 q6 ∷
   rw 35 q7 ∷
   re 35 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 34 q4 ∷
   re 35 5 (CS03 ∷ []) ∷
   rw 37 q3 ∷
   rw 36 q2 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q4 ∷
   rw 36 q1 ∷
   rw⁻ 35 q2 ∷
   rw 38 q3 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q4 ∷
   rw 32 q12 ∷
   rw 26 q13 ∷
   rw 66 q14 ∷
   rw 65 q15 ∷
   rw 64 q15 ∷
   rw 63 q16 ∷
   rw 62 q15 ∷
   rw 61 q16 ∷
   rw 60 q16 ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 61 q17 ∷
   rw 60 q16 ∷
   rw⁻ 59 q17 ∷
   re 60 3 (CS13 ∷ []) ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 60 q17 ∷
   rw 59 q16 ∷
   rw⁻ 58 q17 ∷
   re 59 3 (CS13 ∷ []) ∷
   re 57 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 59 q17 ∷
   rw 58 q15 ∷
   rw⁻ 57 q17 ∷
   re 58 3 (CK31 ∷ []) ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 58 q17 ∷
   rw 57 q16 ∷
   rw⁻ 56 q17 ∷
   re 57 3 (CS13 ∷ []) ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 57 q17 ∷
   rw 56 q16 ∷
   rw⁻ 55 q17 ∷
   re 56 3 (CS13 ∷ []) ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 56 q17 ∷
   rw 55 q16 ∷
   rw⁻ 54 q17 ∷
   re 55 3 (CS13 ∷ []) ∷
   rw 55 q18 ∷
   rw 54 q19 ∷
   rw 55 q19 ∷
   rw 56 q20 ∷
   rw 57 q19 ∷
   rw 58 q20 ∷
   rw 59 q20 ∷
   re 61 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 60 q17 ∷
   rw 61 q19 ∷
   rw 62 q17 ∷
   re 60 3 (CS03 ∷ []) ∷
   re 62 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 61 q17 ∷
   rw 62 q19 ∷
   rw 63 q17 ∷
   re 61 3 (CS03 ∷ []) ∷
   re 63 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 62 q17 ∷
   rw 63 q19 ∷
   rw 64 q17 ∷
   re 62 3 (CS03 ∷ []) ∷
   re 64 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 63 q17 ∷
   rw 64 q20 ∷
   rw 65 q17 ∷
   re 63 3 (CK30 ∷ []) ∷
   re 65 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 64 q17 ∷
   rw 65 q19 ∷
   rw 66 q17 ∷
   re 64 3 (CS03 ∷ []) ∷
   re 66 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 65 q17 ∷
   rw 66 q19 ∷
   rw 67 q17 ∷
   re 65 3 (CS03 ∷ []) ∷
   rw 66 q21 ∷
   re 54 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 53 q22 ∷
   rw⁻ 54 q6 ∷
   rw 55 q23 ∷
   re 53 3 (CS02 ∷ []) ∷
   re 55 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 54 q22 ∷
   rw⁻ 55 q6 ∷
   rw 56 q23 ∷
   re 54 3 (CS02 ∷ []) ∷
   re 56 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 55 q22 ∷
   rw⁻ 56 q11 ∷
   rw 57 q23 ∷
   re 55 3 (CK20 ∷ []) ∷
   re 57 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 56 q22 ∷
   rw⁻ 57 q6 ∷
   rw 58 q23 ∷
   re 56 3 (CS02 ∷ []) ∷
   re 58 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 57 q22 ∷
   rw⁻ 58 q11 ∷
   rw 59 q23 ∷
   re 57 3 (CK20 ∷ []) ∷
   re 59 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 58 q22 ∷
   rw⁻ 59 q11 ∷
   rw 60 q23 ∷
   re 58 3 (CK20 ∷ []) ∷
   rw 59 q14 ∷
   rw 58 q15 ∷
   rw 57 q15 ∷
   rw 56 q16 ∷
   rw 55 q15 ∷
   rw 54 q16 ∷
   rw 53 q16 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 54 q17 ∷
   rw 53 q16 ∷
   rw⁻ 52 q17 ∷
   re 53 3 (CS13 ∷ []) ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q17 ∷
   rw 52 q16 ∷
   rw⁻ 51 q17 ∷
   re 52 3 (CS13 ∷ []) ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q17 ∷
   rw 51 q16 ∷
   rw⁻ 50 q17 ∷
   re 51 3 (CS13 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q17 ∷
   rw 50 q16 ∷
   rw⁻ 49 q17 ∷
   re 50 3 (CS13 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q17 ∷
   rw 49 q16 ∷
   rw⁻ 48 q17 ∷
   re 49 3 (CS13 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q17 ∷
   rw 48 q16 ∷
   rw⁻ 47 q17 ∷
   re 48 3 (CS13 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q17 ∷
   rw 47 q16 ∷
   rw⁻ 46 q17 ∷
   re 47 3 (CS13 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q17 ∷
   rw 46 q16 ∷
   rw⁻ 45 q17 ∷
   re 46 3 (CS13 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q17 ∷
   rw 45 q16 ∷
   rw⁻ 44 q17 ∷
   re 45 3 (CS13 ∷ []) ∷
   rw⁻ 43 q24 ∷
   re 42 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q17 ∷
   rw 43 q15 ∷
   rw⁻ 42 q17 ∷
   re 43 3 (CK31 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q17 ∷
   rw 42 q16 ∷
   rw⁻ 41 q17 ∷
   re 42 3 (CS13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q17 ∷
   rw 41 q16 ∷
   rw⁻ 40 q17 ∷
   re 41 3 (CS13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q17 ∷
   rw 40 q16 ∷
   rw⁻ 39 q17 ∷
   re 40 3 (CS13 ∷ []) ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q17 ∷
   rw 39 q16 ∷
   rw⁻ 38 q17 ∷
   re 39 3 (CS13 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q17 ∷
   rw 38 q16 ∷
   rw⁻ 37 q17 ∷
   re 38 3 (CS13 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q17 ∷
   rw 37 q16 ∷
   rw⁻ 36 q17 ∷
   re 37 3 (CS13 ∷ []) ∷
   rw 37 q25 ∷
   rw 36 q19 ∷
   rw 37 q19 ∷
   rw 38 q20 ∷
   rw 39 q19 ∷
   rw 40 q20 ∷
   rw 41 q20 ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q17 ∷
   rw 43 q19 ∷
   rw 44 q17 ∷
   re 42 3 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q17 ∷
   rw 44 q19 ∷
   rw 45 q17 ∷
   re 43 3 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q17 ∷
   rw 45 q19 ∷
   rw 46 q17 ∷
   re 44 3 (CS03 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 45 q17 ∷
   rw 46 q19 ∷
   rw 47 q17 ∷
   re 45 3 (CS03 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 46 q17 ∷
   rw 47 q19 ∷
   rw 48 q17 ∷
   re 46 3 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q17 ∷
   rw 48 q19 ∷
   rw 49 q17 ∷
   re 47 3 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 48 q17 ∷
   rw 49 q20 ∷
   rw 50 q17 ∷
   re 48 3 (CK30 ∷ []) ∷
   rw 49 q24 ∷
   re 51 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 50 q17 ∷
   rw 51 q19 ∷
   rw 52 q17 ∷
   re 50 3 (CS03 ∷ []) ∷
   re 52 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 51 q17 ∷
   rw 52 q19 ∷
   rw 53 q17 ∷
   re 51 3 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 52 q17 ∷
   rw 53 q19 ∷
   rw 54 q17 ∷
   re 52 3 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 53 q17 ∷
   rw 54 q19 ∷
   rw 55 q17 ∷
   re 53 3 (CS03 ∷ []) ∷ []) Eq.refl

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D455 (W : Ws) where

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
  q2 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q3 : Eqn
  q3 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q4 : Eqn
  q4 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q5 : Eqn
  q5 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q6 : Eqn
  q6 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q7 : Eqn
  q7 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (wn 1214 W)
  q8 : Eqn
  q8 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)
  q9 : Eqn
  q9 = eqn (CK20 ∷ X1 ∷ []) (X1 ∷ CK20 ∷ []) (wn 879 W)
  q10 : Eqn
  q10 = eqn (Sw12 ∷ CX13 ∷ []) (CX23 ∷ Sw12 ∷ []) (wn 157 W)
  q11 : Eqn
  q11 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q12 : Eqn
  q12 = eqn (Sw12 ∷ CX23 ∷ []) (CX13 ∷ Sw12 ∷ []) (wn 158 W)
  q13 : Eqn
  q13 = eqn (CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ []) (wn 880 W)
  q14 : Eqn
  q14 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q15 : Eqn
  q15 = eqn (CX13 ∷ X1 ∷ CX12 ∷ X1 ∷ []) (X1 ∷ CX12 ∷ X1 ∷ CX13 ∷ []) (wn 881 W)
  q16 : Eqn
  q16 = eqn (X1 ∷ S3 ∷ []) (S3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((S ↑)))
  q17 : Eqn
  q17 = eqn (CX12 ∷ S3 ∷ []) (S3 ∷ CX12 ∷ []) (low₃-comm ((CX₀₁ ↑)) (S))

-- Bar(SSKSKK;1,3->0) passes groups of WBar(SSKSKK;~1,2->0) part0: 500 steps
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part0 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ X1 ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ X1 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part0 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ X1 ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ X1 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 37 q1 ∷
   rw 36 q2 ∷
   rw 35 q3 ∷
   rw 34 q3 ∷
   rw 33 q4 ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   rw 30 q4 ∷
   rw 29 q2 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q5 ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 29 q5 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q5 ∷
   re 25 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 27 q5 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q5 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q5 ∷
   re 22 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 24 q5 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q5 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q5 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q5 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q5 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q5 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q5 ∷
   rw 15 q6 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 16 q5 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q5 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw 10 q6 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw 8 q6 ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 5 q3 ∷
   rw 4 q3 ∷
   rw 3 q4 ∷
   rw 2 q3 ∷
   rw 1 q4 ∷
   rw 0 q4 ∷
   rw 1 q7 ∷
   rw⁻ 0 q2 ∷
   rw⁻ 1 q4 ∷
   rw⁻ 2 q4 ∷
   rw⁻ 3 q3 ∷
   rw⁻ 4 q4 ∷
   rw⁻ 5 q3 ∷
   rw⁻ 6 q3 ∷
   rw⁻ 7 q2 ∷
   rw⁻ 8 q4 ∷
   rw⁻ 9 q4 ∷
   rw⁻ 10 q3 ∷
   rw⁻ 11 q4 ∷
   rw⁻ 12 q3 ∷
   rw⁻ 13 q3 ∷
   rw 16 q1 ∷
   re 14 3 (CX13 ∷ []) ∷
   rw 17 q1 ∷
   re 15 3 (CK30 ∷ []) ∷
   rw 16 q8 ∷
   rw 19 q1 ∷
   re 17 3 (CK30 ∷ []) ∷
   rw 18 q8 ∷
   rw 21 q1 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 22 q1 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 23 q1 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 24 q1 ∷
   re 22 3 (CK30 ∷ []) ∷
   rw 23 q8 ∷
   rw 26 q1 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 27 q1 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 28 q1 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q1 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 30 q1 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 31 q1 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CX13 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 34 q1 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 35 q1 ∷
   re 33 3 (CK30 ∷ []) ∷
   rw 36 q1 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 37 q1 ∷
   re 35 3 (CK30 ∷ []) ∷
   rw 38 q1 ∷
   re 36 3 (CK30 ∷ []) ∷
   rw 37 q5 ∷
   rw 38 q1 ∷
   rw 37 q2 ∷
   re 36 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 38 q5 ∷
   rw 37 q9 ∷
   rw⁻ 36 q2 ∷
   rw 39 q1 ∷
   re 37 3 (CK30 ∷ []) ∷
   rw 38 q5 ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   re 41 3 (CX13 ∷ []) ∷
   rw 40 q10 ∷
   rw 39 q11 ∷
   rw 38 q12 ∷
   re 38 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 37 q5 ∷
   re 38 5 (CK30 ∷ []) ∷
   rw 40 q1 ∷
   rw 39 q2 ∷
   re 38 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 40 q5 ∷
   rw 39 q9 ∷
   rw⁻ 38 q2 ∷
   rw 41 q1 ∷
   re 39 3 (CK30 ∷ []) ∷
   rw 40 q5 ∷
   rw 37 q1 ∷
   rw 36 q2 ∷
   re 35 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 37 q5 ∷
   rw 36 q9 ∷
   rw⁻ 35 q2 ∷
   rw 38 q1 ∷
   re 36 3 (CK30 ∷ []) ∷
   rw 37 q5 ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   re 40 3 (CX13 ∷ []) ∷
   rw 39 q10 ∷
   rw 38 q11 ∷
   rw 37 q12 ∷
   re 37 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 36 q5 ∷
   re 37 5 (CK30 ∷ []) ∷
   rw 39 q1 ∷
   rw 38 q2 ∷
   re 37 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 39 q5 ∷
   rw 38 q9 ∷
   rw⁻ 37 q2 ∷
   rw 40 q1 ∷
   re 38 3 (CK30 ∷ []) ∷
   rw 39 q5 ∷
   rw 36 q1 ∷
   rw 35 q2 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q5 ∷
   rw 35 q13 ∷
   rw⁻ 34 q2 ∷
   rw 37 q1 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q5 ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   re 39 3 (CX13 ∷ []) ∷
   rw 38 q10 ∷
   rw 37 q14 ∷
   rw 36 q12 ∷
   re 36 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 35 q5 ∷
   re 36 5 (CS03 ∷ []) ∷
   rw 38 q1 ∷
   rw 37 q2 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q5 ∷
   rw 37 q13 ∷
   rw⁻ 36 q2 ∷
   rw 39 q1 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 38 q5 ∷
   rw 35 q1 ∷
   rw 34 q2 ∷
   re 33 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 35 q5 ∷
   rw 34 q9 ∷
   rw⁻ 33 q2 ∷
   rw 36 q1 ∷
   re 34 3 (CK30 ∷ []) ∷
   rw 35 q5 ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   re 38 3 (CX13 ∷ []) ∷
   rw 37 q10 ∷
   rw 36 q11 ∷
   rw 35 q12 ∷
   re 35 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 34 q5 ∷
   re 35 5 (CK30 ∷ []) ∷
   rw 37 q1 ∷
   rw 36 q2 ∷
   re 35 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 37 q5 ∷
   rw 36 q9 ∷
   rw⁻ 35 q2 ∷
   rw 38 q1 ∷
   re 36 3 (CK30 ∷ []) ∷
   rw 37 q5 ∷
   rw 34 q1 ∷
   rw 33 q2 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q5 ∷
   rw 33 q13 ∷
   rw⁻ 32 q2 ∷
   rw 35 q1 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 34 q5 ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q1 ∷
   re 37 3 (CX13 ∷ []) ∷
   rw 36 q10 ∷
   rw 35 q14 ∷
   rw 34 q12 ∷
   re 34 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 33 q5 ∷
   re 34 5 (CS03 ∷ []) ∷
   rw 36 q1 ∷
   rw 35 q2 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q5 ∷
   rw 35 q13 ∷
   rw⁻ 34 q2 ∷
   rw 37 q1 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q5 ∷
   rw 33 q1 ∷
   rw 32 q2 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q5 ∷
   rw 32 q13 ∷
   rw⁻ 31 q2 ∷
   rw 34 q1 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 33 q5 ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q1 ∷
   re 36 3 (CX13 ∷ []) ∷
   rw 35 q10 ∷
   rw 34 q14 ∷
   rw 33 q12 ∷
   re 33 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 32 q5 ∷
   re 33 5 (CS03 ∷ []) ∷
   rw 35 q1 ∷
   rw 34 q2 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q5 ∷
   rw 34 q13 ∷
   rw⁻ 33 q2 ∷
   rw 36 q1 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 35 q5 ∷
   rw 30 q15 ∷
   rw 31 q1 ∷
   rw 30 q2 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q5 ∷
   rw 30 q13 ∷
   rw⁻ 29 q2 ∷
   rw 32 q1 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 31 q5 ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
   re 34 3 (CX13 ∷ []) ∷
   rw 33 q10 ∷
   rw 32 q14 ∷
   rw 31 q12 ∷
   re 31 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 30 q5 ∷
   re 31 5 (CS03 ∷ []) ∷
   rw 33 q1 ∷
   rw 32 q2 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q5 ∷
   rw 32 q13 ∷
   rw⁻ 31 q2 ∷
   rw 34 q1 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 33 q5 ∷
   rw 30 q1 ∷
   rw 29 q2 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q5 ∷
   rw 29 q13 ∷
   rw⁻ 28 q2 ∷
   rw 31 q1 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 30 q5 ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   re 33 3 (CX13 ∷ []) ∷
   rw 32 q10 ∷
   rw 31 q14 ∷
   rw 30 q12 ∷
   re 30 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 29 q5 ∷
   re 30 5 (CS03 ∷ []) ∷
   rw 32 q1 ∷
   rw 31 q2 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q5 ∷
   rw 31 q13 ∷
   rw⁻ 30 q2 ∷
   rw 33 q1 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 32 q5 ∷
   rw 29 q1 ∷
   rw 28 q2 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q5 ∷
   rw 28 q13 ∷
   rw⁻ 27 q2 ∷
   rw 30 q1 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 29 q5 ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   re 32 3 (CX13 ∷ []) ∷
   rw 31 q10 ∷
   rw 30 q14 ∷
   rw 29 q12 ∷
   re 29 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 28 q5 ∷
   re 29 5 (CS03 ∷ []) ∷
   rw 31 q1 ∷
   rw 30 q2 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q5 ∷
   rw 30 q13 ∷
   rw⁻ 29 q2 ∷
   rw 32 q1 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 31 q5 ∷
   rw 28 q1 ∷
   rw 27 q2 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q5 ∷
   rw 27 q13 ∷
   rw⁻ 26 q2 ∷
   rw 29 q1 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 28 q5 ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CX13 ∷ []) ∷
   rw 30 q10 ∷
   rw 29 q14 ∷
   rw 28 q12 ∷
   re 28 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 27 q5 ∷
   re 28 5 (CS03 ∷ []) ∷
   rw 30 q1 ∷
   rw 29 q2 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q5 ∷
   rw 29 q13 ∷
   rw⁻ 28 q2 ∷
   rw 31 q1 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 30 q5 ∷
   rw 27 q1 ∷
   rw 26 q2 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q5 ∷
   rw 26 q13 ∷
   rw⁻ 25 q2 ∷
   rw 28 q1 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 27 q5 ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CX13 ∷ []) ∷
   rw 29 q10 ∷
   rw 28 q14 ∷
   rw 27 q12 ∷
   re 27 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 26 q5 ∷
   re 27 5 (CS03 ∷ []) ∷
   rw 29 q1 ∷
   rw 28 q2 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q5 ∷
   rw 28 q13 ∷
   rw⁻ 27 q2 ∷
   rw 30 q1 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 29 q5 ∷
   rw 26 q1 ∷
   rw 25 q2 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q5 ∷
   rw 25 q13 ∷
   rw⁻ 24 q2 ∷
   rw 27 q1 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 26 q5 ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   re 29 3 (CX13 ∷ []) ∷
   rw 28 q10 ∷
   rw 27 q14 ∷
   rw 26 q12 ∷
   re 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q5 ∷
   re 26 5 (CS03 ∷ []) ∷
   rw 28 q1 ∷
   rw 27 q2 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q5 ∷
   rw 27 q13 ∷
   rw⁻ 26 q2 ∷
   rw 29 q1 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 28 q5 ∷
   rw⁻ 23 q16 ∷
   rw⁻ 24 q17 ∷
   rw⁻ 25 q16 ∷
   rw 24 q1 ∷
   rw 23 q2 ∷
   re 22 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 24 q5 ∷
   rw 23 q9 ∷
   rw⁻ 22 q2 ∷
   rw 25 q1 ∷
   re 23 3 (CK30 ∷ []) ∷
   rw 24 q5 ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   re 27 3 (CX13 ∷ []) ∷
   rw 26 q10 ∷
   rw 25 q11 ∷
   rw 24 q12 ∷
   re 24 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 23 q5 ∷
   re 24 5 (CK30 ∷ []) ∷
   rw 26 q1 ∷
   rw 25 q2 ∷
   re 24 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 26 q5 ∷
   rw 25 q9 ∷
   rw⁻ 24 q2 ∷
   rw 27 q1 ∷
   re 25 3 (CK30 ∷ []) ∷
   rw 26 q5 ∷
   rw 23 q1 ∷
   rw 22 q2 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q5 ∷
   rw 22 q13 ∷
   rw⁻ 21 q2 ∷
   rw 24 q1 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 23 q5 ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   re 26 3 (CX13 ∷ []) ∷
   rw 25 q10 ∷
   rw 24 q14 ∷
   rw 23 q12 ∷
   re 23 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 22 q5 ∷
   re 23 5 (CS03 ∷ []) ∷
   rw 25 q1 ∷
   rw 24 q2 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q5 ∷
   rw 24 q13 ∷
   rw⁻ 23 q2 ∷
   rw 26 q1 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 25 q5 ∷
   rw 22 q1 ∷ []) Eq.refl

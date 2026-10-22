{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D465 (W : Ws) where

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
  q2 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q3 : Eqn
  q3 = eqn (CK01 ∷ Sw23 ∷ []) (Sw23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (Swap))
  q4 : Eqn
  q4 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 464 W
  q7 : Eqn
  q7 = wE 1217 W
  q8 : Eqn
  q8 = wE 151 W
  q9 : Eqn
  q9 = eqn (X0 ∷ CK31 ∷ []) (CK31 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • CK₁₀ • Swap ↑)))
  q10 : Eqn
  q10 = wE 279 W
  q11 : Eqn
  q11 = eqn (CX01 ∷ CK32 ∷ []) (CK32 ∷ CX01 ∷ []) (low-comm (CX₀₁) (CK₁₀))
  q12 : Eqn
  q12 = wE 280 W
  q13 : Eqn
  q13 = eqn (X0 ∷ CS13 ∷ []) (CS13 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))
  q14 : Eqn
  q14 = wE 65 W
  q15 : Eqn
  q15 = eqn (CX01 ∷ CS23 ∷ []) (CS23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (CS))
  q16 : Eqn
  q16 = wE 48 W
  q17 : Eqn
  q17 = wE 5 W
  q18 : Eqn
  q18 = wE 1106 W
  q19 : Eqn
  q19 = wE 74 W
  q20 : Eqn
  q20 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q21 : Eqn
  q21 = wE 881 W
  q22 : Eqn
  q22 = wE 317 W
  q23 : Eqn
  q23 = wE 30 W
  q24 : Eqn
  q24 = wE 31 W
  q25 : Eqn
  q25 = eqn (X0 ∷ S3 ∷ []) (S3 ∷ X0 ∷ []) (low₁-comm (X) ((S ↑ ↑)))
  q26 : Eqn
  q26 = eqn (CX02 ∷ S3 ∷ []) (S3 ∷ CX02 ∷ []) (low₃-comm ((Swap ↑ • CX₀₁ • Swap ↑)) (S))
  q27 : Eqn
  q27 = wE 1218 W
  q28 : Eqn
  q28 = wE 763 W
  q29 : Eqn
  q29 = wE 359 W
  q30 : Eqn
  q30 = wE 361 W
  q31 : Eqn
  q31 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q32 : Eqn
  q32 = wE 883 W
  q33 : Eqn
  q33 = wE 20 W
  q34 : Eqn
  q34 = wE 49 W
  q35 : Eqn
  q35 = wE 885 W
  q36 : Eqn
  q36 = wE 1219 W
  q37 : Eqn
  q37 = wE 766 W
  q38 : Eqn
  q38 = wE 1144 W
  q39 : Eqn
  q39 = wE 1220 W

-- Bar(SSKSKK;0,3->1) passes groups of WBar(SSKSKK;~0,2->1): 885 steps
lem-Bar⟨SSKSKK03-⟶1⟩-passes-groups-of-WBar⟨SSKSKK~02-⟶1⟩ : ⟪ (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX03 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X0 ∷ CX02 ∷ X0 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CX02 ∷ X0 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X0 ∷ CX02 ∷ X0 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CX02 ∷ X0 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX03 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK03-⟶1⟩-passes-groups-of-WBar⟨SSKSKK~02-⟶1⟩ = derive (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX03 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X0 ∷ CX02 ∷ X0 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CX02 ∷ X0 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (X0 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X0 ∷ CX02 ∷ X0 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CX02 ∷ X0 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX03 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ [])
  (rw 37 q1 ∷
   rw 36 q2 ∷
   rw 35 q3 ∷
   rw 34 q3 ∷
   rw 33 q4 ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   rw 30 q4 ∷
   rw 29 q2 ∷
   re 28 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 30 q5 ∷
   re 27 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 29 q5 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q5 ∷
   re 25 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 27 q5 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q5 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q5 ∷
   re 22 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 24 q5 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q5 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q5 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q5 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q5 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q5 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q5 ∷
   rw 15 q6 ∷
   re 14 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 16 q5 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q5 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw 10 q6 ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw 8 q6 ∷
   re 7 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
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
   re 14 3 (CX03 ∷ []) ∷
   rw 17 q1 ∷
   re 15 3 (CK31 ∷ []) ∷
   rw 16 q8 ∷
   rw 19 q1 ∷
   re 17 3 (CK31 ∷ []) ∷
   rw 18 q8 ∷
   rw 21 q1 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 22 q1 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 23 q1 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 24 q1 ∷
   re 22 3 (CK31 ∷ []) ∷
   rw 23 q8 ∷
   rw 26 q1 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 27 q1 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 28 q1 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 29 q1 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 30 q1 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 31 q1 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CX03 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 34 q1 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw 35 q1 ∷
   re 33 3 (CK31 ∷ []) ∷
   rw 36 q1 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw 37 q1 ∷
   re 35 3 (CK31 ∷ []) ∷
   rw 38 q1 ∷
   re 36 3 (CK31 ∷ []) ∷
   rw 37 q5 ∷
   rw⁻ 36 q9 ∷
   re 38 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 37 q10 ∷
   rw⁻ 38 q11 ∷
   rw 39 q12 ∷
   re 37 3 (CX02 ∷ []) ∷
   rw⁻ 38 q9 ∷
   rw⁻ 35 q9 ∷
   re 37 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 36 q10 ∷
   rw⁻ 37 q11 ∷
   rw 38 q12 ∷
   re 36 3 (CX02 ∷ []) ∷
   rw⁻ 37 q9 ∷
   rw⁻ 34 q13 ∷
   re 36 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 35 q14 ∷
   rw⁻ 36 q15 ∷
   rw 37 q16 ∷
   re 35 3 (CX02 ∷ []) ∷
   rw⁻ 36 q13 ∷
   rw⁻ 33 q9 ∷
   re 35 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 34 q10 ∷
   rw⁻ 35 q11 ∷
   rw 36 q12 ∷
   re 34 3 (CX02 ∷ []) ∷
   rw⁻ 35 q9 ∷
   rw⁻ 32 q13 ∷
   re 34 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 33 q14 ∷
   rw⁻ 34 q15 ∷
   rw 35 q16 ∷
   re 33 3 (CX02 ∷ []) ∷
   rw⁻ 34 q13 ∷
   rw⁻ 31 q13 ∷
   re 33 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 32 q14 ∷
   rw⁻ 33 q15 ∷
   rw 34 q16 ∷
   re 32 3 (CX02 ∷ []) ∷
   rw⁻ 33 q13 ∷
   rw 34 q17 ∷
   rw 33 q18 ∷
   rw 32 q19 ∷
   rw 31 q18 ∷
   re 30 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q20 ∷
   rw 31 q19 ∷
   rw⁻ 30 q20 ∷
   re 31 3 (CX13 ∷ []) ∷
   rw 31 q21 ∷
   rw 30 q22 ∷
   rw 31 q23 ∷
   rw 32 q22 ∷
   re 34 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 33 q20 ∷
   rw 34 q23 ∷
   rw 35 q20 ∷
   re 33 3 (CX03 ∷ []) ∷
   rw 34 q24 ∷
   rw⁻ 29 q13 ∷
   re 31 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 30 q14 ∷
   rw⁻ 31 q15 ∷
   rw 32 q16 ∷
   re 30 3 (CX02 ∷ []) ∷
   rw⁻ 31 q13 ∷
   rw⁻ 28 q13 ∷
   re 30 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 29 q14 ∷
   rw⁻ 30 q15 ∷
   rw 31 q16 ∷
   re 29 3 (CX02 ∷ []) ∷
   rw⁻ 30 q13 ∷
   rw⁻ 27 q13 ∷
   re 29 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 28 q14 ∷
   rw⁻ 29 q15 ∷
   rw 30 q16 ∷
   re 28 3 (CX02 ∷ []) ∷
   rw⁻ 29 q13 ∷
   rw⁻ 26 q13 ∷
   re 28 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 27 q14 ∷
   rw⁻ 28 q15 ∷
   rw 29 q16 ∷
   re 27 3 (CX02 ∷ []) ∷
   rw⁻ 28 q13 ∷
   rw⁻ 25 q13 ∷
   re 27 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 26 q14 ∷
   rw⁻ 27 q15 ∷
   rw 28 q16 ∷
   re 26 3 (CX02 ∷ []) ∷
   rw⁻ 27 q13 ∷
   rw⁻ 24 q13 ∷
   re 26 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 25 q14 ∷
   rw⁻ 26 q15 ∷
   rw 27 q16 ∷
   re 25 3 (CX02 ∷ []) ∷
   rw⁻ 26 q13 ∷
   rw⁻ 23 q25 ∷
   rw⁻ 24 q26 ∷
   rw⁻ 25 q25 ∷
   rw⁻ 22 q9 ∷
   re 24 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 23 q10 ∷
   rw⁻ 24 q11 ∷
   rw 25 q12 ∷
   re 23 3 (CX02 ∷ []) ∷
   rw⁻ 24 q9 ∷
   rw⁻ 21 q13 ∷
   re 23 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 22 q14 ∷
   rw⁻ 23 q15 ∷
   rw 24 q16 ∷
   re 22 3 (CX02 ∷ []) ∷
   rw⁻ 23 q13 ∷
   rw⁻ 20 q13 ∷
   re 22 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 21 q14 ∷
   rw⁻ 22 q15 ∷
   rw 23 q16 ∷
   re 21 3 (CX02 ∷ []) ∷
   rw⁻ 22 q13 ∷
   rw⁻ 19 q13 ∷
   re 21 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 20 q14 ∷
   rw⁻ 21 q15 ∷
   rw 22 q16 ∷
   re 20 3 (CX02 ∷ []) ∷
   rw⁻ 21 q13 ∷
   rw⁻ 18 q25 ∷
   rw⁻ 19 q26 ∷
   rw⁻ 20 q25 ∷
   rw⁻ 17 q9 ∷
   re 19 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 18 q10 ∷
   rw⁻ 19 q11 ∷
   rw 20 q12 ∷
   re 18 3 (CX02 ∷ []) ∷
   rw⁻ 19 q9 ∷
   rw⁻ 16 q25 ∷
   rw⁻ 17 q26 ∷
   rw⁻ 18 q25 ∷
   rw⁻ 15 q9 ∷
   re 17 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 16 q10 ∷
   rw⁻ 17 q11 ∷
   rw 18 q12 ∷
   re 16 3 (CX02 ∷ []) ∷
   rw⁻ 17 q9 ∷
   rw 18 q17 ∷
   rw 17 q18 ∷
   rw 16 q19 ∷
   rw 15 q18 ∷
   re 14 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q20 ∷
   rw 15 q19 ∷
   rw⁻ 14 q20 ∷
   re 15 3 (CX13 ∷ []) ∷
   rw 15 q21 ∷
   rw 14 q22 ∷
   rw 15 q23 ∷
   rw 16 q22 ∷
   re 18 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 17 q20 ∷
   rw 18 q23 ∷
   rw 19 q20 ∷
   re 17 3 (CX03 ∷ []) ∷
   rw 18 q24 ∷
   rw 8 q27 ∷
   rw 34 q28 ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q1 ∷
   re 37 3 (CK31 ∷ []) ∷
   rw 36 q29 ∷
   rw 35 q11 ∷
   rw 34 q30 ∷
   re 34 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 33 q5 ∷
   re 34 5 (CX03 ∷ []) ∷
   rw 36 q17 ∷
   rw⁻ 35 q31 ∷
   re 34 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q20 ∷
   rw 35 q19 ∷
   rw⁻ 34 q20 ∷
   re 35 3 (CX13 ∷ []) ∷
   rw 35 q32 ∷
   rw 34 q31 ∷
   re 36 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 35 q20 ∷
   rw 36 q23 ∷
   rw 37 q20 ∷
   re 35 3 (CX03 ∷ []) ∷
   rw 36 q24 ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   re 39 3 (CK31 ∷ []) ∷
   rw 38 q29 ∷
   rw 37 q11 ∷
   rw 36 q30 ∷
   re 36 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 35 q5 ∷
   re 36 5 (CX03 ∷ []) ∷
   rw 38 q17 ∷
   rw⁻ 37 q31 ∷
   re 36 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q20 ∷
   rw 37 q19 ∷
   rw⁻ 36 q20 ∷
   re 37 3 (CX13 ∷ []) ∷
   rw 37 q32 ∷
   rw 36 q31 ∷
   re 38 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 37 q20 ∷
   rw 38 q23 ∷
   rw 39 q20 ∷
   re 37 3 (CX03 ∷ []) ∷
   rw 38 q24 ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   re 41 3 (CS13 ∷ []) ∷
   rw 40 q33 ∷
   rw 39 q15 ∷
   rw 38 q34 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q5 ∷
   re 38 5 (CX03 ∷ []) ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   re 42 3 (CS13 ∷ []) ∷
   rw 41 q33 ∷
   rw 40 q15 ∷
   rw 39 q34 ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q5 ∷
   re 39 5 (CX03 ∷ []) ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q1 ∷
   re 43 3 (CS13 ∷ []) ∷
   rw 42 q33 ∷
   rw 41 q15 ∷
   rw 40 q34 ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q5 ∷
   re 40 5 (CX03 ∷ []) ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q1 ∷
   re 44 3 (CK31 ∷ []) ∷
   rw 43 q29 ∷
   rw 42 q11 ∷
   rw 41 q30 ∷
   re 41 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 40 q5 ∷
   re 41 5 (CX03 ∷ []) ∷
   rw 43 q17 ∷
   rw⁻ 42 q31 ∷
   re 41 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q20 ∷
   rw 42 q19 ∷
   rw⁻ 41 q20 ∷
   re 42 3 (CX13 ∷ []) ∷
   rw 42 q32 ∷
   rw 41 q31 ∷
   re 43 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 42 q20 ∷
   rw 43 q23 ∷
   rw 44 q20 ∷
   re 42 3 (CX03 ∷ []) ∷
   rw 43 q24 ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q1 ∷
   re 46 3 (CS13 ∷ []) ∷
   rw 45 q33 ∷
   rw 44 q15 ∷
   rw 43 q34 ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q5 ∷
   re 43 5 (CX03 ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   re 47 3 (CS13 ∷ []) ∷
   rw 46 q33 ∷
   rw 45 q15 ∷
   rw 44 q34 ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q5 ∷
   re 44 5 (CX03 ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q1 ∷
   re 48 3 (CS13 ∷ []) ∷
   rw 47 q33 ∷
   rw 46 q15 ∷
   rw 45 q34 ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q5 ∷
   re 45 5 (CX03 ∷ []) ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q1 ∷
   re 49 3 (CS13 ∷ []) ∷
   rw 48 q33 ∷
   rw 47 q15 ∷
   rw 46 q34 ∷
   re 46 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 45 q5 ∷
   re 46 5 (CX03 ∷ []) ∷
   re 46 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q1 ∷
   re 50 3 (CS13 ∷ []) ∷
   rw 49 q33 ∷
   rw 48 q15 ∷
   rw 47 q34 ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 46 q5 ∷
   re 47 5 (CX03 ∷ []) ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q1 ∷
   re 51 3 (CS13 ∷ []) ∷
   rw 50 q33 ∷
   rw 49 q15 ∷
   rw 48 q34 ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q5 ∷
   re 48 5 (CX03 ∷ []) ∷
   rw 18 q35 ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   re 21 3 (CK31 ∷ []) ∷
   rw 20 q29 ∷
   rw 19 q11 ∷
   rw 18 q30 ∷
   re 18 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   re 18 5 (CX03 ∷ []) ∷
   rw 20 q17 ∷
   rw⁻ 19 q31 ∷
   re 18 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q20 ∷
   rw 19 q19 ∷
   rw⁻ 18 q20 ∷
   re 19 3 (CX13 ∷ []) ∷
   rw 19 q32 ∷
   rw 18 q31 ∷
   re 20 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 19 q20 ∷
   rw 20 q23 ∷
   rw 21 q20 ∷
   re 19 3 (CX03 ∷ []) ∷
   rw 20 q24 ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 23 3 (CK31 ∷ []) ∷
   rw 22 q29 ∷
   rw 21 q11 ∷
   rw 20 q30 ∷
   re 20 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 19 q5 ∷
   re 20 5 (CX03 ∷ []) ∷
   rw 22 q17 ∷
   rw⁻ 21 q31 ∷
   re 20 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q20 ∷
   rw 21 q19 ∷
   rw⁻ 20 q20 ∷
   re 21 3 (CX13 ∷ []) ∷
   rw 21 q32 ∷
   rw 20 q31 ∷
   re 22 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 21 q20 ∷
   rw 22 q23 ∷
   rw 23 q20 ∷
   re 21 3 (CX03 ∷ []) ∷
   rw 22 q24 ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 24 q33 ∷
   rw 23 q15 ∷
   rw 22 q34 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q5 ∷
   re 22 5 (CX03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 25 q33 ∷
   rw 24 q15 ∷
   rw 23 q34 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q5 ∷
   re 23 5 (CX03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 26 q33 ∷
   rw 25 q15 ∷
   rw 24 q34 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q5 ∷
   re 24 5 (CX03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   re 28 3 (CK31 ∷ []) ∷
   rw 27 q29 ∷
   rw 26 q11 ∷
   rw 25 q30 ∷
   re 25 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 24 q5 ∷
   re 25 5 (CX03 ∷ []) ∷
   rw 27 q17 ∷
   rw⁻ 26 q31 ∷
   re 25 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q20 ∷
   rw 26 q19 ∷
   rw⁻ 25 q20 ∷
   re 26 3 (CX13 ∷ []) ∷
   rw 26 q32 ∷
   rw 25 q31 ∷
   re 27 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 26 q20 ∷
   rw 27 q23 ∷
   rw 28 q20 ∷
   re 26 3 (CX03 ∷ []) ∷
   rw 27 q24 ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw 29 q33 ∷
   rw 28 q15 ∷
   rw 27 q34 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q5 ∷
   re 27 5 (CX03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 30 q33 ∷
   rw 29 q15 ∷
   rw 28 q34 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q5 ∷
   re 28 5 (CX03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw 31 q33 ∷
   rw 30 q15 ∷
   rw 29 q34 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q5 ∷
   re 29 5 (CX03 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw 32 q33 ∷
   rw 31 q15 ∷
   rw 30 q34 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q5 ∷
   re 30 5 (CX03 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw 33 q33 ∷
   rw 32 q15 ∷
   rw 31 q34 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q5 ∷
   re 31 5 (CX03 ∷ []) ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q1 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw 34 q33 ∷
   rw 33 q15 ∷
   rw 32 q34 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q5 ∷
   re 32 5 (CX03 ∷ []) ∷
   rw 11 q36 ∷
   rw⁻ 54 q9 ∷
   re 56 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 55 q10 ∷
   rw⁻ 56 q11 ∷
   rw 57 q12 ∷
   re 55 3 (CX02 ∷ []) ∷
   rw⁻ 56 q9 ∷
   rw⁻ 53 q9 ∷
   re 55 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 54 q10 ∷
   rw⁻ 55 q11 ∷
   rw 56 q12 ∷
   re 54 3 (CX02 ∷ []) ∷
   rw⁻ 55 q9 ∷
   rw⁻ 52 q13 ∷
   re 54 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 53 q14 ∷
   rw⁻ 54 q15 ∷
   rw 55 q16 ∷
   re 53 3 (CX02 ∷ []) ∷
   rw⁻ 54 q13 ∷
   rw⁻ 51 q9 ∷
   re 53 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 52 q10 ∷
   rw⁻ 53 q11 ∷
   rw 54 q12 ∷
   re 52 3 (CX02 ∷ []) ∷
   rw⁻ 53 q9 ∷
   rw⁻ 50 q13 ∷
   re 52 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 51 q14 ∷
   rw⁻ 52 q15 ∷
   rw 53 q16 ∷
   re 51 3 (CX02 ∷ []) ∷
   rw⁻ 52 q13 ∷
   rw⁻ 49 q13 ∷
   re 51 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 50 q14 ∷
   rw⁻ 51 q15 ∷
   rw 52 q16 ∷
   re 50 3 (CX02 ∷ []) ∷
   rw⁻ 51 q13 ∷
   rw 52 q17 ∷
   rw 51 q18 ∷
   rw 50 q19 ∷
   rw 49 q18 ∷
   re 48 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q20 ∷
   rw 49 q19 ∷
   rw⁻ 48 q20 ∷
   re 49 3 (CX13 ∷ []) ∷
   rw 49 q21 ∷
   rw 48 q22 ∷
   rw 49 q23 ∷
   rw 50 q22 ∷
   re 52 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 51 q20 ∷
   rw 52 q23 ∷
   rw 53 q20 ∷
   re 51 3 (CX03 ∷ []) ∷
   rw 52 q24 ∷
   rw⁻ 47 q13 ∷
   re 49 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 48 q14 ∷
   rw⁻ 49 q15 ∷
   rw 50 q16 ∷
   re 48 3 (CX02 ∷ []) ∷
   rw⁻ 49 q13 ∷
   rw⁻ 46 q13 ∷
   re 48 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 47 q14 ∷
   rw⁻ 48 q15 ∷
   rw 49 q16 ∷
   re 47 3 (CX02 ∷ []) ∷
   rw⁻ 48 q13 ∷
   rw⁻ 45 q13 ∷
   re 47 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 46 q14 ∷
   rw⁻ 47 q15 ∷
   rw 48 q16 ∷
   re 46 3 (CX02 ∷ []) ∷
   rw⁻ 47 q13 ∷
   rw⁻ 44 q13 ∷
   re 46 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 45 q14 ∷
   rw⁻ 46 q15 ∷
   rw 47 q16 ∷
   re 45 3 (CX02 ∷ []) ∷
   rw⁻ 46 q13 ∷
   rw⁻ 43 q13 ∷
   re 45 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 44 q14 ∷
   rw⁻ 45 q15 ∷
   rw 46 q16 ∷
   re 44 3 (CX02 ∷ []) ∷
   rw⁻ 45 q13 ∷
   rw⁻ 42 q13 ∷
   re 44 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 43 q14 ∷
   rw⁻ 44 q15 ∷
   rw 45 q16 ∷
   re 43 3 (CX02 ∷ []) ∷
   rw⁻ 44 q13 ∷
   rw⁻ 41 q25 ∷
   rw⁻ 42 q26 ∷
   rw⁻ 43 q25 ∷
   rw⁻ 40 q9 ∷
   re 42 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 41 q10 ∷
   rw⁻ 42 q11 ∷
   rw 43 q12 ∷
   re 41 3 (CX02 ∷ []) ∷
   rw⁻ 42 q9 ∷
   rw⁻ 39 q13 ∷
   re 41 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 40 q14 ∷
   rw⁻ 41 q15 ∷
   rw 42 q16 ∷
   re 40 3 (CX02 ∷ []) ∷
   rw⁻ 41 q13 ∷
   rw⁻ 38 q13 ∷
   re 40 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 39 q14 ∷
   rw⁻ 40 q15 ∷
   rw 41 q16 ∷
   re 39 3 (CX02 ∷ []) ∷
   rw⁻ 40 q13 ∷
   rw⁻ 37 q13 ∷
   re 39 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 38 q14 ∷
   rw⁻ 39 q15 ∷
   rw 40 q16 ∷
   re 38 3 (CX02 ∷ []) ∷
   rw⁻ 39 q13 ∷
   rw⁻ 36 q25 ∷
   rw⁻ 37 q26 ∷
   rw⁻ 38 q25 ∷
   rw⁻ 35 q9 ∷
   re 37 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 36 q10 ∷
   rw⁻ 37 q11 ∷
   rw 38 q12 ∷
   re 36 3 (CX02 ∷ []) ∷
   rw⁻ 37 q9 ∷
   rw⁻ 34 q25 ∷
   rw⁻ 35 q26 ∷
   rw⁻ 36 q25 ∷
   rw⁻ 33 q9 ∷
   re 35 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 34 q10 ∷
   rw⁻ 35 q11 ∷
   rw 36 q12 ∷
   re 34 3 (CX02 ∷ []) ∷
   rw⁻ 35 q9 ∷
   rw 36 q17 ∷
   rw 35 q18 ∷
   rw 34 q19 ∷
   rw 33 q18 ∷
   re 32 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q20 ∷
   rw 33 q19 ∷
   rw⁻ 32 q20 ∷
   re 33 3 (CX13 ∷ []) ∷
   rw 33 q21 ∷
   rw 32 q22 ∷
   rw 33 q23 ∷
   rw 34 q22 ∷
   re 36 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 35 q20 ∷
   rw 36 q23 ∷
   rw 37 q20 ∷
   re 35 3 (CX03 ∷ []) ∷
   rw 36 q24 ∷
   rw 26 q27 ∷
   rw 52 q37 ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 57 q1 ∷
   re 55 3 (CS13 ∷ []) ∷
   rw 54 q33 ∷
   rw 53 q15 ∷
   rw 52 q34 ∷
   re 52 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 51 q5 ∷
   re 52 5 (CX03 ∷ []) ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q1 ∷
   re 56 3 (CS13 ∷ []) ∷
   rw 55 q33 ∷
   rw 54 q15 ∷
   rw 53 q34 ∷
   re 53 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 52 q5 ∷
   re 53 5 (CX03 ∷ []) ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q1 ∷
   re 57 3 (CK31 ∷ []) ∷
   rw 56 q29 ∷
   rw 55 q11 ∷
   rw 54 q30 ∷
   re 54 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 53 q5 ∷
   re 54 5 (CX03 ∷ []) ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 60 q1 ∷
   re 58 3 (CS13 ∷ []) ∷
   rw 57 q33 ∷
   rw 56 q15 ∷
   rw 55 q34 ∷
   re 55 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 54 q5 ∷
   re 55 5 (CX03 ∷ []) ∷
   re 55 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 61 q1 ∷
   re 59 3 (CK31 ∷ []) ∷
   rw 58 q29 ∷
   rw 57 q11 ∷
   rw 56 q30 ∷
   re 56 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 55 q5 ∷
   re 56 5 (CX03 ∷ []) ∷
   re 56 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 62 q1 ∷
   re 60 3 (CK31 ∷ []) ∷
   rw 59 q29 ∷
   rw 58 q11 ∷
   rw 57 q30 ∷
   re 57 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 56 q5 ∷
   re 57 5 (CX03 ∷ []) ∷
   rw 36 q38 ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   re 39 3 (CS13 ∷ []) ∷
   rw 38 q33 ∷
   rw 37 q15 ∷
   rw 36 q34 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q5 ∷
   re 36 5 (CX03 ∷ []) ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   re 40 3 (CS13 ∷ []) ∷
   rw 39 q33 ∷
   rw 38 q15 ∷
   rw 37 q34 ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q5 ∷
   re 37 5 (CX03 ∷ []) ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   re 41 3 (CK31 ∷ []) ∷
   rw 40 q29 ∷
   rw 39 q11 ∷
   rw 38 q30 ∷
   re 38 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 37 q5 ∷
   re 38 5 (CX03 ∷ []) ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   re 42 3 (CS13 ∷ []) ∷
   rw 41 q33 ∷
   rw 40 q15 ∷
   rw 39 q34 ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q5 ∷
   re 39 5 (CX03 ∷ []) ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q1 ∷
   re 43 3 (CK31 ∷ []) ∷
   rw 42 q29 ∷
   rw 41 q11 ∷
   rw 40 q30 ∷
   re 40 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 39 q5 ∷
   re 40 5 (CX03 ∷ []) ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q1 ∷
   re 44 3 (CK31 ∷ []) ∷
   rw 43 q29 ∷
   rw 42 q11 ∷
   rw 41 q30 ∷
   re 41 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 40 q5 ∷
   re 41 5 (CX03 ∷ []) ∷
   rw 29 q39 ∷ []) Eq.refl

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D389 (W : Ws) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Four.Str using (ℓ)

private
  q1 : Eqn
  q1 = wE 656 W
  q2 : Eqn
  q2 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q3 : Eqn
  q3 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q4 : Eqn
  q4 = wE 914 W
  q5 : Eqn
  q5 = eqn (ℓ "与乌") (ℓ "乌与") (low-comm ((S ↑)) (CX₀₁))
  q6 : Eqn
  q6 = wE 5 W
  q7 : Eqn
  q7 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q8 : Eqn
  q8 = wE 7 W
  q9 : Eqn
  q9 = wE 915 W
  q10 : Eqn
  q10 = wE 27 W
  q11 : Eqn
  q11 = wE 31 W
  q12 : Eqn
  q12 = wE 140 W
  q13 : Eqn
  q13 = wE 917 W
  q14 : Eqn
  q14 = wE 142 W
  q15 : Eqn
  q15 = wE 655 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX12 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CS02 CK20 CS02 CS02] [CX23]: 69 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CX23 : ⟪ (ℓ "丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧乌") ⟫ʷ ≈ ⟪ (ℓ "乌丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CX23 = derive (ℓ "丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧乌") (ℓ "乌丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧")
  (rw 0 q1 ∷
   rw 30 q2 ∷
   rw 29 q2 ∷
   rw 28 q3 ∷
   rw 27 q2 ∷
   rw 26 q2 ∷
   rw 25 q2 ∷
   rw 24 q4 ∷
   rw 23 q2 ∷
   rw 22 q2 ∷
   rw 21 q2 ∷
   rw 20 q2 ∷
   rw 19 q2 ∷
   rw 18 q2 ∷
   rw 17 q2 ∷
   rw 16 q2 ∷
   rw 15 q2 ∷
   rw 14 q5 ∷
   rw 13 q3 ∷
   rw 12 q2 ∷
   rw 11 q2 ∷
   rw 10 q2 ∷
   rw 9 q2 ∷
   rw 8 q2 ∷
   rw 7 q2 ∷
   rw 6 q4 ∷
   rw 7 q6 ∷
   rw⁻ 6 q7 ∷
   rw 5 q8 ∷
   rw 6 q9 ∷
   rw 5 q7 ∷
   rw 6 q10 ∷
   rw 7 q11 ∷
   rw 6 q6 ∷
   rw⁻ 5 q7 ∷
   rw 4 q8 ∷
   rw 5 q9 ∷
   rw 4 q7 ∷
   rw 5 q10 ∷
   rw 6 q11 ∷
   rw 5 q6 ∷
   rw⁻ 4 q7 ∷
   rw 3 q12 ∷
   rw 4 q13 ∷
   rw 3 q7 ∷
   rw 4 q14 ∷
   rw 5 q11 ∷
   rw 4 q6 ∷
   rw⁻ 3 q7 ∷
   rw 2 q8 ∷
   rw 3 q9 ∷
   rw 2 q7 ∷
   rw 3 q10 ∷
   rw 4 q11 ∷
   rw 3 q6 ∷
   rw⁻ 2 q7 ∷
   rw 1 q8 ∷
   rw 2 q9 ∷
   rw 1 q7 ∷
   rw 2 q10 ∷
   rw 3 q11 ∷
   rw 2 q6 ∷
   rw⁻ 1 q7 ∷
   rw 0 q8 ∷
   rw 1 q9 ∷
   rw 0 q7 ∷
   rw 1 q10 ∷
   rw 2 q11 ∷
   rw 1 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = wE 1 W
  q17 : Eqn
  q17 = wE 21 W
  q18 : Eqn
  q18 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q19 : Eqn
  q19 = wE 51 W
  q20 : Eqn
  q20 = wE 3 W
  q21 : Eqn
  q21 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q22 : Eqn
  q22 = wE 696 W
  q23 : Eqn
  q23 = wE 211 W
  q24 : Eqn
  q24 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q25 : Eqn
  q25 = wE 200 W
  q26 : Eqn
  q26 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q27 : Eqn
  q27 = wE 609 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX12 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CS02 CK20 CS02 CS02] [CSd13]: 387 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CSd13 : ⟪ (ℓ "丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧举") ⟫ʷ ≈ ⟪ (ℓ "举丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CSd13 = derive (ℓ "丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧举") (ℓ "举丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧")
  (re 31 1 (ℓ "乏丷乏") ∷
   rw 30 q16 ∷
   re 31 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q16 ∷
   re 35 3 (ℓ "举") ∷
   rw 34 q17 ∷
   rw 33 q18 ∷
   rw 32 q19 ∷
   re 32 1 (ℓ "乏丷乏") ∷
   rw 31 q20 ∷
   re 32 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q20 ∷
   re 30 3 (ℓ "举") ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q16 ∷
   re 30 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q16 ∷
   re 34 3 (ℓ "举") ∷
   rw 33 q17 ∷
   rw 32 q18 ∷
   rw 31 q19 ∷
   re 31 1 (ℓ "乏丷乏") ∷
   rw 30 q20 ∷
   re 31 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q20 ∷
   re 29 3 (ℓ "举") ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q16 ∷
   re 29 3 (ℓ "乑") ∷
   re 29 1 (ℓ "乏丼临丼乏") ∷
   rw 35 q16 ∷
   re 33 3 (ℓ "举") ∷
   rw 32 q17 ∷
   rw 31 q21 ∷
   rw 30 q19 ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q20 ∷
   re 30 5 (ℓ "乑") ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw 32 q20 ∷
   re 28 3 (ℓ "举") ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q16 ∷
   re 28 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q16 ∷
   re 32 3 (ℓ "举") ∷
   rw 31 q17 ∷
   rw 30 q18 ∷
   rw 29 q19 ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q20 ∷
   re 29 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q20 ∷
   re 27 3 (ℓ "举") ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q16 ∷
   re 27 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q16 ∷
   re 31 3 (ℓ "举") ∷
   rw 30 q17 ∷
   rw 29 q18 ∷
   rw 28 q19 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q20 ∷
   re 28 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q20 ∷
   re 26 3 (ℓ "举") ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q16 ∷
   re 26 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q16 ∷
   re 30 3 (ℓ "举") ∷
   rw 29 q17 ∷
   rw 28 q18 ∷
   rw 27 q19 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q20 ∷
   re 27 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q20 ∷
   re 25 3 (ℓ "举") ∷
   rw 24 q22 ∷
   re 24 1 (ℓ "乏丷乏") ∷
   rw 23 q16 ∷
   re 24 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q16 ∷
   re 28 3 (ℓ "举") ∷
   rw 27 q17 ∷
   rw 26 q18 ∷
   rw 25 q19 ∷
   re 25 1 (ℓ "乏丷乏") ∷
   rw 24 q20 ∷
   re 25 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q20 ∷
   re 23 3 (ℓ "举") ∷
   re 23 1 (ℓ "乏丷乏") ∷
   rw 22 q16 ∷
   re 23 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q16 ∷
   re 27 3 (ℓ "举") ∷
   rw 26 q17 ∷
   rw 25 q18 ∷
   rw 24 q19 ∷
   re 24 1 (ℓ "乏丷乏") ∷
   rw 23 q20 ∷
   re 24 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q20 ∷
   re 22 3 (ℓ "举") ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q16 ∷
   re 22 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q16 ∷
   re 26 3 (ℓ "举") ∷
   rw 25 q17 ∷
   rw 24 q18 ∷
   rw 23 q19 ∷
   re 23 1 (ℓ "乏丷乏") ∷
   rw 22 q20 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q20 ∷
   re 21 3 (ℓ "举") ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q16 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q16 ∷
   re 25 3 (ℓ "举") ∷
   rw 24 q17 ∷
   rw 23 q18 ∷
   rw 22 q19 ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q20 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q20 ∷
   re 20 3 (ℓ "举") ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q16 ∷
   re 20 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q16 ∷
   re 24 3 (ℓ "举") ∷
   rw 23 q17 ∷
   rw 22 q18 ∷
   rw 21 q19 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q20 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q20 ∷
   re 19 3 (ℓ "举") ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q16 ∷
   re 19 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q16 ∷
   re 23 3 (ℓ "举") ∷
   rw 22 q17 ∷
   rw 21 q18 ∷
   rw 20 q19 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q20 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q20 ∷
   re 18 3 (ℓ "举") ∷
   re 18 1 (ℓ "乏丷乏") ∷
   rw 17 q16 ∷
   re 18 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q16 ∷
   re 22 3 (ℓ "举") ∷
   rw 21 q17 ∷
   rw 20 q18 ∷
   rw 19 q19 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q20 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q20 ∷
   re 17 3 (ℓ "举") ∷
   re 17 1 (ℓ "乏丷乏") ∷
   rw 16 q16 ∷
   re 17 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q16 ∷
   re 21 3 (ℓ "举") ∷
   rw 20 q17 ∷
   rw 19 q18 ∷
   rw 18 q19 ∷
   re 18 1 (ℓ "乏丷乏") ∷
   rw 17 q20 ∷
   re 18 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q20 ∷
   re 16 3 (ℓ "举") ∷
   re 16 1 (ℓ "乏丷乏") ∷
   rw 15 q16 ∷
   re 16 3 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q16 ∷
   re 20 3 (ℓ "举") ∷
   rw 19 q17 ∷
   rw 18 q18 ∷
   rw 17 q19 ∷
   re 17 1 (ℓ "乏丷乏") ∷
   rw 16 q20 ∷
   re 17 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q20 ∷
   re 15 3 (ℓ "举") ∷
   rw 14 q23 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q16 ∷
   re 14 3 (ℓ "乑") ∷
   re 14 1 (ℓ "乏丼临丼乏") ∷
   rw 20 q16 ∷
   re 18 3 (ℓ "举") ∷
   rw 17 q17 ∷
   rw 16 q21 ∷
   rw 15 q19 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 14 q20 ∷
   re 15 5 (ℓ "乑") ∷
   re 15 1 (ℓ "乏乄乏") ∷
   rw 17 q20 ∷
   re 13 3 (ℓ "举") ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q16 ∷
   re 13 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q16 ∷
   re 17 3 (ℓ "举") ∷
   rw 16 q17 ∷
   rw 15 q18 ∷
   rw 14 q19 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q20 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q20 ∷
   re 12 3 (ℓ "举") ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q16 ∷
   re 12 3 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q16 ∷
   re 16 3 (ℓ "举") ∷
   rw 15 q17 ∷
   rw 14 q18 ∷
   rw 13 q19 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q20 ∷
   re 13 5 (ℓ "中") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q20 ∷
   re 11 3 (ℓ "举") ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q16 ∷
   re 11 3 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q16 ∷
   re 15 3 (ℓ "举") ∷
   rw 14 q17 ∷
   rw 13 q18 ∷
   rw 12 q19 ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q20 ∷
   re 12 5 (ℓ "中") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q20 ∷
   re 10 3 (ℓ "举") ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q16 ∷
   re 10 3 (ℓ "中") ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q16 ∷
   re 14 3 (ℓ "举") ∷
   rw 13 q17 ∷
   rw 12 q18 ∷
   rw 11 q19 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q20 ∷
   re 11 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q20 ∷
   re 9 3 (ℓ "举") ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q16 ∷
   re 9 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q16 ∷
   re 13 3 (ℓ "举") ∷
   rw 12 q17 ∷
   rw 11 q18 ∷
   rw 10 q19 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q20 ∷
   re 10 5 (ℓ "中") ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q20 ∷
   re 8 3 (ℓ "举") ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q16 ∷
   re 8 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 14 q16 ∷
   re 12 3 (ℓ "举") ∷
   rw 11 q17 ∷
   rw 10 q18 ∷
   rw 9 q19 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q20 ∷
   re 9 5 (ℓ "中") ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q20 ∷
   re 7 3 (ℓ "举") ∷
   rw 6 q22 ∷
   rw 7 q16 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q20 ∷
   rw 5 q24 ∷
   rw 6 q25 ∷
   rw 7 q16 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q24 ∷
   rw 7 q20 ∷
   rw 6 q16 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q20 ∷
   rw 4 q24 ∷
   rw 5 q25 ∷
   rw 6 q16 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q24 ∷
   rw 6 q20 ∷
   rw 5 q16 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q20 ∷
   rw 3 q26 ∷
   rw 4 q27 ∷
   rw 5 q16 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q26 ∷
   rw 5 q20 ∷
   rw 4 q16 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q20 ∷
   rw 2 q24 ∷
   rw 3 q25 ∷
   rw 4 q16 ∷
   re 2 3 (ℓ "举") ∷
   rw⁻ 3 q24 ∷
   rw 4 q20 ∷
   rw 3 q16 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 4 q20 ∷
   rw 1 q24 ∷
   rw 2 q25 ∷
   rw 3 q16 ∷
   re 1 3 (ℓ "举") ∷
   rw⁻ 2 q24 ∷
   rw 3 q20 ∷
   rw 2 q16 ∷
   re 1 1 (ℓ "乏丷乏") ∷
   rw 3 q20 ∷
   rw 0 q24 ∷
   rw 1 q25 ∷
   rw 2 q16 ∷
   re 0 3 (ℓ "举") ∷
   rw⁻ 1 q24 ∷
   rw 2 q20 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = wE 952 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX12 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CS02 CK20 CS02 CS02] [X1 CKd12 X1]: 1 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-X1-CKd12-X1 : ⟪ (ℓ "丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧丒主丒") ⟫ʷ ≈ ⟪ (ℓ "丒主丒丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-X1-CKd12-X1 = derive (ℓ "丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧丒主丒") (ℓ "丒主丒丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧")
  (rw 0 q28 ∷ []) Eq.refl

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD780 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D780 (W : Ws) (Sᴰ : SD780) where

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

-- The lemmas of other derivation modules (DSig).
private
  lem-F7a-gad-inv : St 3461
  lem-F7a-gad-inv = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = wE 2549 W
  q3 : Eqn
  q3 = wE 1731 W
  q4 : Eqn
  q4 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = wE 9 W
  q6 : Eqn
  q6 = wE 127 W
  q7 : Eqn
  q7 = wE 271 W
  q8 : Eqn
  q8 = wE 7 W
  q9 : Eqn
  q9 = wE 8 W
  q10 : Eqn
  q10 = wE 10 W
  q11 : Eqn
  q11 = wE 272 W
  q12 : Eqn
  q12 = wE 1207 W
  q13 : Eqn
  q13 = wE 118 W
  q14 : Eqn
  q14 = wE 274 W
  q15 : Eqn
  q15 = wE 76 W
  q16 : Eqn
  q16 = sE 3461 lem-F7a-gad-inv
  q17 : Eqn
  q17 = wE 311 W
  q18 : Eqn
  q18 = wE 123 W
  q19 : Eqn
  q19 = wE 27 W
  q20 : Eqn
  q20 = wE 28 W
  q21 : Eqn
  q21 = wE 29 W
  q22 : Eqn
  q22 = wE 25 W
  q23 : Eqn
  q23 = wE 124 W
  q24 : Eqn
  q24 = wE 322 W
  q25 : Eqn
  q25 = wE 313 W
  q26 : Eqn
  q26 = wE 312 W
  q27 : Eqn
  q27 = wE 121 W
  q28 : Eqn
  q28 = wE 31 W

-- F7a gad inv @1023: 171 steps
lem-F7a-gad-inv-at1023 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-F7a-gad-inv-at1023 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  (rw 12 q1 ∷
   rw 11 q2 ∷
   rw 10 q3 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q4 ∷
   rw 10 q5 ∷
   rw⁻ 9 q4 ∷
   re 10 3 (CS03⁻ ∷ []) ∷
   re 8 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 15 q6 ∷
   rw 14 q7 ∷
   rw 13 q8 ∷
   rw 12 q9 ∷
   rw 11 q5 ∷
   rw 10 q9 ∷
   rw 9 q10 ∷
   rw 8 q7 ∷
   rw 9 q11 ∷
   re 9 8 (Toff012 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q4 ∷
   rw 8 q10 ∷
   rw⁻ 7 q4 ∷
   re 8 3 (CS03 ∷ []) ∷
   re 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 13 q6 ∷
   rw 12 q7 ∷
   rw 11 q8 ∷
   rw 10 q9 ∷
   rw 9 q5 ∷
   rw 8 q9 ∷
   rw 7 q10 ∷
   rw 6 q7 ∷
   rw 7 q11 ∷
   re 7 8 (Toff012 ∷ []) ∷
   rw 5 q7 ∷
   rw 4 q12 ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 10 q6 ∷
   rw 9 q13 ∷
   rw 8 q8 ∷
   rw 7 q9 ∷
   rw 6 q5 ∷
   rw 5 q9 ∷
   rw 4 q10 ∷
   rw 3 q13 ∷
   rw 4 q14 ∷
   re 4 8 (Toff102 ∷ []) ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 3 q15 ∷
   rw⁻ 2 q4 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 8 q6 ∷
   rw 7 q13 ∷
   rw 6 q8 ∷
   rw 5 q9 ∷
   rw 4 q5 ∷
   rw 3 q9 ∷
   rw 2 q10 ∷
   rw 1 q13 ∷
   rw 2 q14 ∷
   re 2 8 (Toff102 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 1 q8 ∷
   rw⁻ 0 q4 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q16 ∷
   rw 0 q17 ∷
   rw 1 q18 ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 2 q18 ∷
   rw 3 q19 ∷
   rw 4 q20 ∷
   rw 5 q21 ∷
   rw 6 q20 ∷
   rw 7 q22 ∷
   rw 8 q18 ∷
   rw 9 q23 ∷
   rw 2 q14 ∷
   re 2 8 (Toff102 ∷ []) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   rw 4 q22 ∷
   rw 5 q4 ∷
   re 3 3 (CS13 ∷ []) ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 4 q18 ∷
   rw 5 q19 ∷
   rw 6 q20 ∷
   rw 7 q21 ∷
   rw 8 q20 ∷
   rw 9 q22 ∷
   rw 10 q18 ∷
   rw 11 q23 ∷
   rw 4 q14 ∷
   re 4 8 (Toff102 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q4 ∷
   rw 6 q24 ∷
   rw 7 q4 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw 6 q25 ∷
   rw 7 q26 ∷
   re 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 8 q18 ∷
   rw 9 q19 ∷
   rw 10 q20 ∷
   rw 11 q21 ∷
   rw 12 q20 ∷
   rw 13 q22 ∷
   rw 14 q18 ∷
   rw 15 q23 ∷
   rw 8 q14 ∷
   re 8 8 (Toff102 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q4 ∷
   rw 10 q22 ∷
   rw 11 q4 ∷
   re 9 3 (CS13 ∷ []) ∷
   re 11 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 10 q18 ∷
   rw 11 q19 ∷
   rw 12 q20 ∷
   rw 13 q21 ∷
   rw 14 q20 ∷
   rw 15 q22 ∷
   rw 16 q18 ∷
   rw 17 q23 ∷
   rw 10 q14 ∷
   re 10 8 (Toff102 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q4 ∷
   rw 12 q24 ∷
   rw 13 q4 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q4 ∷
   rw 13 q19 ∷
   rw 14 q4 ∷
   re 12 3 (CS03 ∷ []) ∷
   re 14 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 13 q27 ∷
   rw 14 q19 ∷
   rw 15 q20 ∷
   rw 16 q21 ∷
   rw 17 q20 ∷
   rw 18 q22 ∷
   rw 19 q27 ∷
   rw 20 q23 ∷
   rw 13 q11 ∷
   re 13 8 (Toff012 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q4 ∷
   rw 15 q21 ∷
   rw 16 q4 ∷
   re 14 3 (CS03⁻ ∷ []) ∷
   re 16 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 15 q27 ∷
   rw 16 q19 ∷
   rw 17 q20 ∷
   rw 18 q21 ∷
   rw 19 q20 ∷
   rw 20 q22 ∷
   rw 21 q27 ∷
   rw 22 q23 ∷
   rw 15 q11 ∷
   re 15 8 (Toff012 ∷ []) ∷
   rw 16 q28 ∷ []) Eq.refl

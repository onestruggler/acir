{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D006 (W : Ws) where

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
  q1 = wE 116 W
  q2 : Eqn
  q2 = wE 117 W
  q3 : Eqn
  q3 = wE 5 W
  q4 : Eqn
  q4 = wE 118 W
  q5 : Eqn
  q5 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q6 : Eqn
  q6 = wE 30 W
  q7 : Eqn
  q7 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q8 : Eqn
  q8 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q9 : Eqn
  q9 = wE 27 W
  q10 : Eqn
  q10 = wE 31 W
  q11 : Eqn
  q11 = wE 7 W
  q12 : Eqn
  q12 = wE 74 W
  q13 : Eqn
  q13 = wE 26 W
  q14 : Eqn
  q14 = wE 119 W
  q15 : Eqn
  q15 = wE 120 W
  q16 : Eqn
  q16 = wE 121 W
  q17 : Eqn
  q17 = wE 122 W
  q18 : Eqn
  q18 = wE 123 W
  q19 : Eqn
  q19 = wE 24 W
  q20 : Eqn
  q20 = wE 25 W
  q21 : Eqn
  q21 = wE 124 W
  q22 : Eqn
  q22 = wE 125 W
  q23 : Eqn
  q23 = wE 126 W

-- Rk: 119 steps
lem-Rk : ⟪ (ℓ "下临乛丵乛上") ⟫ʷ ≈ ⟪ (ℓ "临也丵也") ⟫ʷ
lem-Rk = derive (ℓ "下临乛丵乛上") (ℓ "临也丵也")
  (rw 4 q1 ∷
   rw 3 q1 ∷
   rw 2 q1 ∷
   rw 0 q2 ∷
   rw 4 q3 ∷
   rw 3 q4 ∷
   re 2 1 (ℓ "並乜並") ∷
   re 3 1 (ℓ "义丹乊丹丽") ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   rw 4 q7 ∷
   rw 5 q6 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q8 ∷
   rw 7 q9 ∷
   rw 8 q8 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q10 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q8 ∷
   rw 7 q11 ∷
   rw⁻ 6 q8 ∷
   re 7 3 (ℓ "丽") ∷
   rw 5 q12 ∷
   rw⁻ 4 q7 ∷
   rw 3 q12 ∷
   rw⁻ 2 q5 ∷
   rw 3 q13 ∷
   re 3 5 (ℓ "乜") ∷
   rw 1 q14 ∷
   rw 2 q15 ∷
   re 2 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 1 q16 ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   rw 4 q7 ∷
   rw 5 q6 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q8 ∷
   rw 7 q9 ∷
   rw 8 q8 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q16 ∷
   rw 8 q17 ∷
   rw 1 q3 ∷
   rw 2 q18 ∷
   rw 3 q5 ∷
   rw 4 q19 ∷
   rw 5 q7 ∷
   rw 6 q19 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q8 ∷
   rw 8 q20 ∷
   rw 9 q8 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q18 ∷
   rw 9 q21 ∷
   rw 2 q22 ∷
   re 2 8 (ℓ "乢") ∷
   re 1 3 (ℓ "也") ∷
   rw 2 q10 ∷
   rw 2 q23 ∷
   rw 6 q3 ∷
   rw 5 q4 ∷
   re 4 1 (ℓ "並乜並") ∷
   re 5 1 (ℓ "义丹乊丹丽") ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q8 ∷
   rw 9 q9 ∷
   rw 10 q8 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q10 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q8 ∷
   rw 9 q11 ∷
   rw⁻ 8 q8 ∷
   re 9 3 (ℓ "丽") ∷
   rw 7 q12 ∷
   rw⁻ 6 q7 ∷
   rw 5 q12 ∷
   rw⁻ 4 q5 ∷
   rw 5 q13 ∷
   re 5 5 (ℓ "乜") ∷
   rw 3 q14 ∷
   rw 4 q15 ∷
   re 4 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 3 q16 ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q8 ∷
   rw 9 q9 ∷
   rw 10 q8 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q16 ∷
   rw 10 q17 ∷
   rw 3 q3 ∷
   rw 4 q18 ∷
   rw 5 q5 ∷
   rw 6 q19 ∷
   rw 7 q7 ∷
   rw 8 q19 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q8 ∷
   rw 10 q20 ∷
   rw 11 q8 ∷
   re 9 3 (ℓ "丽") ∷
   rw 10 q18 ∷
   rw 11 q21 ∷
   rw 4 q22 ∷
   re 4 8 (ℓ "乢") ∷
   re 3 3 (ℓ "也") ∷
   rw 4 q10 ∷ []) Eq.refl

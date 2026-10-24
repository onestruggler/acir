{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D454 (W : Ws) where

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
  q1 = wE 5 W
  q2 : Eqn
  q2 = wE 7 W
  q3 : Eqn
  q3 = wE 772 W
  q4 : Eqn
  q4 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = wE 6 W
  q6 : Eqn
  q6 = wE 481 W
  q7 : Eqn
  q7 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q8 : Eqn
  q8 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q9 : Eqn
  q9 = wE 1212 W
  q10 : Eqn
  q10 = wE 27 W
  q11 : Eqn
  q11 = wE 329 W
  q12 : Eqn
  q12 = wE 30 W
  q13 : Eqn
  q13 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q14 : Eqn
  q14 = wE 31 W
  q15 : Eqn
  q15 = wE 1213 W
  q16 : Eqn
  q16 = wE 315 W

-- respell hyb CS23 CS23 CK32 CS23 CX30 CS02 CS02 CS02  -> CS02 CS02 CK02 CS02 CX03 CS23 CS23 CS23 : 192 steps
lem-respell-hyb-CS23-CS23-CK32-CS23-CX30-CS02-CS02-CS02---⟶-CS02-CS02-CK02-CS02-CX03-CS23-CS23-CS23- : ⟪ (ℓ "义义乗义乐丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧为丧丧丧丈丫丧丧丧丧丧丧乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丈丫丧丧丧丧丧丧丧丧丧乐义义义业乗义义义义义义与为") ⟫ʷ ≈ ⟪ (ℓ "丧丧丫丧丰义义义乗业义义义义义义丰义义乗义为义义义业乗义义义义义义丰义义义义义义义义义义义义义义义义义义业业业业乗义义义义义义义义义丰丧丧丧丈丫丧丧丧丧丧丧与为") ⟫ʷ
lem-respell-hyb-CS23-CS23-CK32-CS23-CX30-CS02-CS02-CS02---⟶-CS02-CS02-CK02-CS02-CX03-CS23-CS23-CS23- = derive (ℓ "义义乗义乐丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧为丧丧丧丈丫丧丧丧丧丧丧乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丈丫丧丧丧丧丧丧丧丧丧乐义义义业乗义义义义义义与为") (ℓ "丧丧丫丧丰义义义乗业义义义义义义丰义义乗义为义义义业乗义义义义义义丰义义义义义义义义义义义义义义义义义义业业业业乗义义义义义义义义义丰丧丧丧丈丫丧丧丧丧丧丧与为")
  (rw 21 q1 ∷
   rw 20 q2 ∷
   rw 19 q3 ∷
   rw 18 q2 ∷
   rw 17 q2 ∷
   re 16 1 (ℓ "乏乃乏") ∷
   rw⁻ 18 q4 ∷
   rw 17 q5 ∷
   rw⁻ 16 q4 ∷
   re 17 3 (ℓ "乓") ∷
   rw 15 q2 ∷
   rw 14 q2 ∷
   rw 13 q2 ∷
   rw 12 q2 ∷
   rw 11 q2 ∷
   rw 10 q2 ∷
   rw 9 q6 ∷
   rw 8 q3 ∷
   rw 7 q2 ∷
   rw 6 q2 ∷
   rw 5 q2 ∷
   re 4 1 (ℓ "乏乃乏") ∷
   rw⁻ 6 q4 ∷
   rw 5 q5 ∷
   rw⁻ 4 q4 ∷
   re 5 3 (ℓ "乓") ∷
   rw⁻ 3 q7 ∷
   rw⁻ 2 q8 ∷
   rw⁻ 1 q7 ∷
   rw⁻ 0 q7 ∷
   rw 1 q9 ∷
   rw 0 q10 ∷
   rw 1 q10 ∷
   rw 2 q11 ∷
   rw 3 q10 ∷
   re 5 1 (ℓ "乏丹乏") ∷
   rw 4 q4 ∷
   rw 5 q12 ∷
   rw 6 q4 ∷
   re 4 3 (ℓ "丰") ∷
   rw 5 q7 ∷
   rw 6 q7 ∷
   rw 7 q7 ∷
   rw 8 q8 ∷
   rw 9 q13 ∷
   rw 10 q7 ∷
   rw 11 q7 ∷
   rw 12 q7 ∷
   rw 13 q7 ∷
   rw 14 q7 ∷
   rw 15 q7 ∷
   re 17 1 (ℓ "乏丹乏") ∷
   rw 16 q4 ∷
   rw 17 q12 ∷
   rw 18 q4 ∷
   re 16 3 (ℓ "丰") ∷
   rw 17 q7 ∷
   rw 18 q7 ∷
   rw 19 q8 ∷
   rw 20 q7 ∷
   rw 21 q14 ∷
   rw 78 q1 ∷
   rw⁻ 77 q7 ∷
   rw⁻ 76 q7 ∷
   rw⁻ 75 q7 ∷
   rw⁻ 74 q7 ∷
   rw⁻ 73 q7 ∷
   rw⁻ 72 q7 ∷
   rw⁻ 71 q8 ∷
   rw⁻ 70 q13 ∷
   rw⁻ 69 q7 ∷
   rw⁻ 68 q7 ∷
   rw⁻ 67 q7 ∷
   re 66 1 (ℓ "乏乃乏") ∷
   rw⁻ 68 q4 ∷
   rw 67 q5 ∷
   rw⁻ 66 q4 ∷
   re 67 3 (ℓ "乓") ∷
   rw 65 q2 ∷
   rw 64 q2 ∷
   rw 63 q2 ∷
   rw 62 q2 ∷
   rw 61 q2 ∷
   rw 60 q2 ∷
   rw 59 q2 ∷
   rw 58 q2 ∷
   rw 57 q2 ∷
   rw 56 q3 ∷
   rw 55 q6 ∷
   rw 54 q6 ∷
   rw 53 q6 ∷
   rw 52 q6 ∷
   rw 51 q2 ∷
   rw 50 q2 ∷
   rw 49 q2 ∷
   rw 48 q2 ∷
   rw 47 q2 ∷
   rw 46 q2 ∷
   rw 45 q2 ∷
   rw 44 q2 ∷
   rw 43 q2 ∷
   rw 42 q2 ∷
   rw 41 q2 ∷
   rw 40 q2 ∷
   rw 39 q2 ∷
   rw 38 q2 ∷
   rw 37 q2 ∷
   rw 36 q2 ∷
   rw 35 q2 ∷
   rw 34 q2 ∷
   re 33 1 (ℓ "乏乃乏") ∷
   rw⁻ 35 q4 ∷
   rw 34 q5 ∷
   rw⁻ 33 q4 ∷
   re 34 3 (ℓ "乓") ∷
   rw 32 q2 ∷
   rw 31 q2 ∷
   rw 30 q2 ∷
   rw 29 q2 ∷
   rw 28 q2 ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   rw 25 q6 ∷
   rw 24 q2 ∷
   rw 23 q2 ∷
   rw 22 q2 ∷
   rw 23 q15 ∷
   rw 22 q7 ∷
   rw 23 q7 ∷
   rw 24 q7 ∷
   rw 25 q13 ∷
   rw 26 q8 ∷
   rw 27 q7 ∷
   rw 28 q7 ∷
   rw 29 q7 ∷
   rw 30 q7 ∷
   rw 31 q7 ∷
   rw 32 q7 ∷
   re 34 1 (ℓ "乏丹乏") ∷
   rw 33 q4 ∷
   rw 34 q12 ∷
   rw 35 q4 ∷
   re 33 3 (ℓ "丰") ∷
   rw 34 q7 ∷
   rw 35 q7 ∷
   rw 36 q7 ∷
   rw 37 q7 ∷
   rw 38 q7 ∷
   rw 39 q7 ∷
   rw 40 q7 ∷
   rw 41 q7 ∷
   rw 42 q7 ∷
   rw 43 q7 ∷
   rw 44 q7 ∷
   rw 45 q7 ∷
   rw 46 q7 ∷
   rw 47 q7 ∷
   rw 48 q7 ∷
   rw 49 q7 ∷
   rw 50 q7 ∷
   rw 51 q7 ∷
   rw 52 q13 ∷
   rw 53 q13 ∷
   rw 54 q13 ∷
   rw 55 q13 ∷
   rw 56 q8 ∷
   rw 57 q7 ∷
   rw 58 q7 ∷
   rw 59 q7 ∷
   rw 60 q7 ∷
   rw 61 q7 ∷
   rw 62 q7 ∷
   rw 63 q7 ∷
   rw 64 q7 ∷
   rw 65 q7 ∷
   re 67 1 (ℓ "乏丹乏") ∷
   rw 66 q4 ∷
   rw 67 q12 ∷
   rw 68 q4 ∷
   re 66 3 (ℓ "丰") ∷
   rw 67 q10 ∷
   rw 68 q10 ∷
   rw 69 q10 ∷
   rw 70 q16 ∷
   rw 71 q11 ∷
   rw 72 q10 ∷
   rw 73 q10 ∷
   rw 74 q10 ∷
   rw 75 q10 ∷
   rw 76 q10 ∷
   rw 77 q10 ∷
   rw 78 q14 ∷ []) Eq.refl

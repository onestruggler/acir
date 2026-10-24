{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D206 (W : Ws) where

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
  q2 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = wE 772 W
  q4 : Eqn
  q4 = wE 7 W
  q5 : Eqn
  q5 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q6 : Eqn
  q6 = wE 6 W
  q7 : Eqn
  q7 = wE 481 W
  q8 : Eqn
  q8 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q9 : Eqn
  q9 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q10 : Eqn
  q10 = wE 140 W
  q11 : Eqn
  q11 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q12 : Eqn
  q12 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q13 : Eqn
  q13 = wE 805 W
  q14 : Eqn
  q14 = wE 39 W
  q15 : Eqn
  q15 = wE 329 W
  q16 : Eqn
  q16 = wE 315 W
  q17 : Eqn
  q17 = wE 27 W
  q18 : Eqn
  q18 = wE 142 W
  q19 : Eqn
  q19 = wE 31 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 CS23 CS23 CK32 CS23 CK32 CK32 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CX30 CS02 CS02 CK02 CS02 CK02 CK02 X3]: 187 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丞") ⟫ʷ ≈ ⟪ (ℓ "丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丞") (ℓ "丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 60 q1 ∷
   rw⁻ 59 q2 ∷
   rw 58 q3 ∷
   rw 57 q3 ∷
   rw 56 q4 ∷
   rw 55 q3 ∷
   rw 54 q4 ∷
   rw 53 q4 ∷
   re 52 1 (ℓ "乏乃乏") ∷
   rw⁻ 54 q5 ∷
   rw 53 q6 ∷
   rw⁻ 52 q5 ∷
   re 53 3 (ℓ "乓") ∷
   rw 51 q4 ∷
   rw 50 q4 ∷
   rw 49 q4 ∷
   rw 48 q4 ∷
   rw 47 q4 ∷
   rw 46 q4 ∷
   rw 45 q7 ∷
   rw 44 q3 ∷
   rw 43 q4 ∷
   rw 42 q4 ∷
   rw 41 q4 ∷
   rw 40 q7 ∷
   rw 39 q3 ∷
   rw 38 q7 ∷
   rw 37 q3 ∷
   re 36 1 (ℓ "乏乃乏") ∷
   rw⁻ 38 q5 ∷
   rw 37 q6 ∷
   rw⁻ 36 q5 ∷
   re 37 3 (ℓ "乓") ∷
   rw⁻ 35 q8 ∷
   rw⁻ 34 q8 ∷
   rw⁻ 33 q9 ∷
   rw⁻ 32 q8 ∷
   rw⁻ 31 q9 ∷
   rw⁻ 30 q9 ∷
   rw⁻ 29 q2 ∷
   rw 28 q10 ∷
   rw 27 q10 ∷
   rw 26 q4 ∷
   rw 25 q10 ∷
   rw 24 q4 ∷
   rw 23 q4 ∷
   rw⁻ 22 q11 ∷
   rw 21 q4 ∷
   rw 20 q4 ∷
   rw 19 q4 ∷
   rw 18 q4 ∷
   rw 17 q4 ∷
   rw 16 q4 ∷
   rw⁻ 15 q12 ∷
   rw 14 q10 ∷
   rw 13 q4 ∷
   rw 12 q4 ∷
   rw 11 q4 ∷
   rw⁻ 10 q12 ∷
   rw 9 q10 ∷
   rw⁻ 8 q12 ∷
   rw 7 q10 ∷
   rw⁻ 6 q11 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q5 ∷
   rw 6 q10 ∷
   rw⁻ 5 q5 ∷
   re 6 3 (ℓ "乔") ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw⁻ 6 q5 ∷
   rw 5 q10 ∷
   rw⁻ 4 q5 ∷
   re 5 3 (ℓ "乔") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q5 ∷
   rw 4 q4 ∷
   rw⁻ 3 q5 ∷
   re 4 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw⁻ 4 q5 ∷
   rw 3 q10 ∷
   rw⁻ 2 q5 ∷
   re 3 3 (ℓ "乔") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q5 ∷
   rw 2 q4 ∷
   rw⁻ 1 q5 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q5 ∷
   rw 1 q4 ∷
   rw⁻ 0 q5 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q13 ∷
   rw 0 q2 ∷
   rw 1 q9 ∷
   rw 2 q9 ∷
   rw 3 q8 ∷
   rw 4 q9 ∷
   rw 5 q8 ∷
   rw 6 q8 ∷
   re 8 1 (ℓ "乏乆乏") ∷
   rw 7 q5 ∷
   rw 8 q14 ∷
   rw 9 q5 ∷
   re 7 3 (ℓ "乐") ∷
   rw 8 q15 ∷
   rw 9 q16 ∷
   rw 10 q15 ∷
   rw 11 q16 ∷
   rw 12 q17 ∷
   rw 13 q17 ∷
   rw 14 q17 ∷
   rw 15 q15 ∷
   rw 16 q16 ∷
   rw 17 q17 ∷
   rw 18 q17 ∷
   rw 19 q17 ∷
   rw 20 q17 ∷
   rw 21 q17 ∷
   rw 22 q17 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 23 q5 ∷
   rw 24 q14 ∷
   rw 25 q5 ∷
   re 23 3 (ℓ "乐") ∷
   rw 24 q17 ∷
   rw 25 q17 ∷
   rw 26 q15 ∷
   rw 27 q17 ∷
   rw 28 q15 ∷
   rw 29 q15 ∷
   rw 30 q2 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q5 ∷
   rw 32 q17 ∷
   rw 33 q5 ∷
   re 31 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q5 ∷
   rw 33 q17 ∷
   rw 34 q5 ∷
   re 32 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏乇乏") ∷
   rw 33 q5 ∷
   rw 34 q18 ∷
   rw 35 q5 ∷
   re 33 3 (ℓ "乑") ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q5 ∷
   rw 35 q17 ∷
   rw 36 q5 ∷
   re 34 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏乇乏") ∷
   rw 35 q5 ∷
   rw 36 q18 ∷
   rw 37 q5 ∷
   re 35 3 (ℓ "乑") ∷
   re 37 1 (ℓ "乏乇乏") ∷
   rw 36 q5 ∷
   rw 37 q18 ∷
   rw 38 q5 ∷
   re 36 3 (ℓ "乑") ∷
   rw 37 q11 ∷
   rw 38 q18 ∷
   rw 39 q12 ∷
   rw 40 q18 ∷
   rw 41 q12 ∷
   rw 42 q17 ∷
   rw 43 q17 ∷
   rw 44 q17 ∷
   rw 45 q18 ∷
   rw 46 q12 ∷
   rw 47 q17 ∷
   rw 48 q17 ∷
   rw 49 q17 ∷
   rw 50 q17 ∷
   rw 51 q17 ∷
   rw 52 q17 ∷
   rw 53 q11 ∷
   rw 54 q17 ∷
   rw 55 q17 ∷
   rw 56 q18 ∷
   rw 57 q17 ∷
   rw 58 q18 ∷
   rw 59 q18 ∷
   rw 60 q19 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = wE 806 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 CK32 X3]: 115 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK32-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乗丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK32-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乗丞") (ℓ "丞乗丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 32 q1 ∷
   rw⁻ 31 q2 ∷
   rw⁻ 30 q8 ∷
   rw⁻ 29 q2 ∷
   rw 28 q10 ∷
   rw 27 q10 ∷
   rw 26 q4 ∷
   rw 25 q10 ∷
   rw 24 q4 ∷
   rw 23 q4 ∷
   rw⁻ 22 q11 ∷
   rw 21 q4 ∷
   rw 20 q4 ∷
   rw 19 q4 ∷
   rw 18 q4 ∷
   rw 17 q4 ∷
   rw 16 q4 ∷
   rw⁻ 15 q12 ∷
   rw 14 q10 ∷
   rw 13 q4 ∷
   rw 12 q4 ∷
   rw 11 q4 ∷
   rw⁻ 10 q12 ∷
   rw 9 q10 ∷
   rw⁻ 8 q12 ∷
   rw 7 q10 ∷
   rw⁻ 6 q11 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q5 ∷
   rw 6 q10 ∷
   rw⁻ 5 q5 ∷
   re 6 3 (ℓ "乔") ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw⁻ 6 q5 ∷
   rw 5 q10 ∷
   rw⁻ 4 q5 ∷
   re 5 3 (ℓ "乔") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q5 ∷
   rw 4 q4 ∷
   rw⁻ 3 q5 ∷
   re 4 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw⁻ 4 q5 ∷
   rw 3 q10 ∷
   rw⁻ 2 q5 ∷
   re 3 3 (ℓ "乔") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q5 ∷
   rw 2 q4 ∷
   rw⁻ 1 q5 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q5 ∷
   rw 1 q4 ∷
   rw⁻ 0 q5 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q20 ∷
   rw 0 q2 ∷
   rw 1 q8 ∷
   rw 2 q2 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q5 ∷
   rw 4 q17 ∷
   rw 5 q5 ∷
   re 3 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw 5 q17 ∷
   rw 6 q5 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏乇乏") ∷
   rw 5 q5 ∷
   rw 6 q18 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "乑") ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw 7 q17 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏乇乏") ∷
   rw 7 q5 ∷
   rw 8 q18 ∷
   rw 9 q5 ∷
   re 7 3 (ℓ "乑") ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q5 ∷
   rw 9 q18 ∷
   rw 10 q5 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q11 ∷
   rw 10 q18 ∷
   rw 11 q12 ∷
   rw 12 q18 ∷
   rw 13 q12 ∷
   rw 14 q17 ∷
   rw 15 q17 ∷
   rw 16 q17 ∷
   rw 17 q18 ∷
   rw 18 q12 ∷
   rw 19 q17 ∷
   rw 20 q17 ∷
   rw 21 q17 ∷
   rw 22 q17 ∷
   rw 23 q17 ∷
   rw 24 q17 ∷
   rw 25 q11 ∷
   rw 26 q17 ∷
   rw 27 q17 ∷
   rw 28 q18 ∷
   rw 29 q17 ∷
   rw 30 q18 ∷
   rw 31 q18 ∷
   rw 32 q19 ∷ []) Eq.refl

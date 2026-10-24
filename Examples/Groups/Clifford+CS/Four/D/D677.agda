{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD677 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D677 (W : Ws) (Sᴰ : SD677) where

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

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-CCZ013-CS02 : St 14
  lem-comm-CCZ013-CS02 = pickᴰ 0 Sᴰ
  lem-S2 : St 1778
  lem-S2 = pickᴰ 1 Sᴰ

private
  q1 : Eqn
  q1 = sE 1778 lem-S2
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q4 : Eqn
  q4 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q5 : Eqn
  q5 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 56 W
  q8 : Eqn
  q8 = wE 2012 W
  q9 : Eqn
  q9 = wE 43 W
  q10 : Eqn
  q10 = wE 251 W
  q11 : Eqn
  q11 = wE 205 W
  q12 : Eqn
  q12 = sE 14 lem-comm-CCZ013-CS02
  q13 : Eqn
  q13 = wE 65 W
  q14 : Eqn
  q14 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q15 : Eqn
  q15 = wE 48 W
  q16 : Eqn
  q16 = wE 2013 W
  q17 : Eqn
  q17 = wE 5 W
  q18 : Eqn
  q18 = wE 7 W
  q19 : Eqn
  q19 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q20 : Eqn
  q20 = wE 101 W
  q21 : Eqn
  q21 = wE 27 W
  q22 : Eqn
  q22 = wE 31 W
  q23 : Eqn
  q23 = wE 527 W
  q24 : Eqn
  q24 = wE 2014 W
  q25 : Eqn
  q25 = wE 2015 W
  q26 : Eqn
  q26 = wE 76 W
  q27 : Eqn
  q27 = wE 198 W
  q28 : Eqn
  q28 = wE 29 W
  q29 : Eqn
  q29 = sE 1778 lem-S2

-- C3-PP3: 478 steps
lem-C3-PP3 : ⟪ (ℓ "中九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮中") ⟫ʷ
lem-C3-PP3 = derive (ℓ "中九中九丮") (ℓ "九中九丮中")
  (rw 1 q1 ∷
   rw 2 q2 ∷
   re 1 1 (ℓ "乏九乏") ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q3 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q4 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 9 q6 ∷
   rw 8 q5 ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q6 ∷
   rw 3 q4 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q6 ∷
   rw 1 q3 ∷
   rw 2 q7 ∷
   re 2 8 (ℓ "九") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q6 ∷
   rw 1 q8 ∷
   re 1 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 0 q3 ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q4 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q3 ∷
   rw⁻ 7 q5 ∷
   rw 0 q2 ∷
   rw⁻ 1 q3 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q6 ∷
   rw⁻ 3 q4 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q6 ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 1 q7 ∷
   re 1 8 (ℓ "九") ∷
   re 0 3 (ℓ "乞") ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "丽") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q4 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "中") ∷
   rw 2 q2 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q6 ∷
   rw 3 q9 ∷
   re 3 5 (ℓ "乙") ∷
   re 2 3 (ℓ "乚") ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q6 ∷
   rw 4 q2 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q6 ∷
   re 2 1 (ℓ "乏乙乏") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q4 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q6 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q6 ∷
   rw 3 q4 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q6 ∷
   rw 3 q9 ∷
   re 3 5 (ℓ "乙") ∷
   rw 3 q10 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "中") ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q4 ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "中") ∷
   rw 3 q2 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q6 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   rw 4 q9 ∷
   re 4 5 (ℓ "乙") ∷
   re 3 3 (ℓ "乚") ∷
   rw 4 q6 ∷
   rw 3 q2 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q6 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q6 ∷
   rw 2 q11 ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "中") ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "丽") ∷
   rw 3 q6 ∷
   rw 3 q12 ∷
   re 3 1 (ℓ "丼丠丼") ∷
   rw 2 q13 ∷
   rw⁻ 3 q14 ∷
   rw 4 q15 ∷
   re 2 3 (ℓ "丧") ∷
   rw 6 q2 ∷
   re 5 1 (ℓ "乏九乏") ∷
   re 6 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 5 q3 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q4 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q4 ∷
   rw 12 q2 ∷
   re 10 3 (ℓ "中") ∷
   rw⁻ 11 q3 ∷
   rw⁻ 12 q5 ∷
   rw 13 q6 ∷
   rw 12 q5 ∷
   rw 11 q3 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q6 ∷
   rw 9 q4 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 10 q6 ∷
   rw 7 q4 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 5 q3 ∷
   rw 6 q7 ∷
   re 6 8 (ℓ "九") ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q4 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q6 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q6 ∷
   rw 7 q4 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q6 ∷
   rw 5 q9 ∷
   re 5 5 (ℓ "乙") ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 4 q16 ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q3 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q4 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q5 ∷
   rw 3 q2 ∷
   rw⁻ 4 q3 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q6 ∷
   rw⁻ 8 q4 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q6 ∷
   rw⁻ 10 q3 ∷
   rw⁻ 11 q5 ∷
   rw 4 q7 ∷
   re 4 8 (ℓ "九") ∷
   re 3 3 (ℓ "乞") ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "举") ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q4 ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q4 ∷
   rw 11 q2 ∷
   re 9 3 (ℓ "中") ∷
   rw 5 q2 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q6 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q6 ∷
   rw⁻ 9 q4 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q6 ∷
   rw 6 q9 ∷
   re 6 5 (ℓ "乙") ∷
   re 5 3 (ℓ "乚") ∷
   rw 6 q6 ∷
   rw 3 q17 ∷
   rw 2 q18 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q19 ∷
   rw 2 q18 ∷
   rw⁻ 1 q19 ∷
   re 2 3 (ℓ "丽") ∷
   rw 2 q20 ∷
   rw 1 q21 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q19 ∷
   rw 3 q21 ∷
   rw 4 q19 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q22 ∷
   rw 4 q2 ∷
   re 3 1 (ℓ "乏九乏") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q3 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q4 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q5 ∷
   rw 11 q6 ∷
   rw 10 q5 ∷
   rw 9 q3 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q6 ∷
   rw 7 q4 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q6 ∷
   rw 3 q3 ∷
   rw 4 q7 ∷
   re 4 8 (ℓ "九") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q6 ∷
   rw 3 q8 ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q3 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q4 ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q2 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q6 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q5 ∷
   rw 3 q7 ∷
   re 3 8 (ℓ "九") ∷
   re 2 3 (ℓ "乞") ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "丽") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q4 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "中") ∷
   rw 4 q2 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q6 ∷
   rw⁻ 8 q4 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q6 ∷
   rw 5 q9 ∷
   re 5 5 (ℓ "乙") ∷
   re 4 3 (ℓ "乚") ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q6 ∷
   rw 7 q2 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q6 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q6 ∷
   rw 6 q23 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "举") ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q6 ∷
   rw 8 q2 ∷
   re 7 1 (ℓ "乏乙乏") ∷
   re 8 1 (ℓ "丶丣丷丣丧") ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q4 ∷
   rw 11 q2 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q4 ∷
   rw 13 q2 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q6 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q6 ∷
   rw 10 q4 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 11 q6 ∷
   rw 8 q4 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 9 q6 ∷
   rw 8 q9 ∷
   re 8 5 (ℓ "乙") ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   rw 7 q24 ∷
   re 7 1 (ℓ "丶丣丷丣丧") ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q4 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q4 ∷
   rw 12 q2 ∷
   re 10 3 (ℓ "中") ∷
   rw 6 q2 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   rw⁻ 8 q4 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q6 ∷
   rw⁻ 10 q4 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q6 ∷
   rw 7 q9 ∷
   re 7 5 (ℓ "乙") ∷
   re 6 3 (ℓ "乚") ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q6 ∷
   rw 7 q2 ∷
   re 6 1 (ℓ "乏乙乏") ∷
   re 7 1 (ℓ "丶丣丷丣丧") ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q4 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q4 ∷
   rw 12 q2 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q6 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q6 ∷
   rw 9 q4 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 10 q6 ∷
   rw 7 q4 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 7 q9 ∷
   re 7 5 (ℓ "乙") ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q6 ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q4 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q6 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q6 ∷
   rw 7 q4 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q6 ∷
   rw 5 q9 ∷
   re 5 5 (ℓ "乙") ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 4 q25 ∷
   rw 3 q6 ∷
   rw 5 q17 ∷
   rw 4 q26 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q19 ∷
   rw 4 q18 ∷
   rw⁻ 3 q19 ∷
   re 4 3 (ℓ "丽") ∷
   rw 4 q27 ∷
   rw 3 q28 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q19 ∷
   rw 5 q21 ∷
   rw 6 q19 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q22 ∷
   rw⁻ 0 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = wE 12 W
  q31 : Eqn
  q31 = wE 22 W
  q32 : Eqn
  q32 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q33 : Eqn
  q33 = wE 23 W
  q34 : Eqn
  q34 = eqn (ℓ "一丼") (ℓ "丼一") (low₁-comm (iI) (Swap))
  q35 : Eqn
  q35 = eqn (ℓ "上丼") (ℓ "丼上") (low₁-comm (K) (Swap))
  q36 : Eqn
  q36 = wE 14 W
  q37 : Eqn
  q37 = wE 15 W
  q38 : Eqn
  q38 = wE 16 W
  q39 : Eqn
  q39 = wE 46 W
  q40 : Eqn
  q40 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q41 : Eqn
  q41 = wE 20 W
  q42 : Eqn
  q42 = wE 21 W
  q43 : Eqn
  q43 = wE 123 W
  q44 : Eqn
  q44 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q45 : Eqn
  q45 = wE 24 W
  q46 : Eqn
  q46 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q47 : Eqn
  q47 = wE 25 W
  q48 : Eqn
  q48 = wE 124 W
  q49 : Eqn
  q49 = wE 125 W

-- S2 @0213: 133 steps
lem-S2-at0213 : ⟪ (ℓ "九中九丮") ⟫ʷ ≈ ⟪ (ℓ "也丠也両") ⟫ʷ
lem-S2-at0213 = derive (ℓ "九中九丮") (ℓ "也丠也両")
  (rw 4 q30 ∷
   re 3 1 (ℓ "乏丼両丼乏") ∷
   rw 6 q31 ∷
   rw 5 q32 ∷
   rw 3 q33 ∷
   re 4 5 (ℓ "丮") ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 9 q34 ∷
   rw 8 q35 ∷
   re 7 1 (ℓ "丼丠丼") ∷
   rw 9 q36 ∷
   rw 6 q30 ∷
   re 7 3 (ℓ "个") ∷
   rw 5 q37 ∷
   rw 4 q30 ∷
   re 5 3 (ℓ "个") ∷
   rw 3 q38 ∷
   rw 2 q35 ∷
   rw 3 q39 ∷
   re 3 8 (ℓ "九") ∷
   re 1 1 (ℓ "乏丼丠丼乏") ∷
   rw 4 q31 ∷
   rw 3 q40 ∷
   rw 1 q33 ∷
   re 2 5 (ℓ "中") ∷
   re 0 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 7 q34 ∷
   rw 6 q35 ∷
   re 5 1 (ℓ "丼丠丼") ∷
   rw 7 q36 ∷
   rw 4 q30 ∷
   re 5 3 (ℓ "个") ∷
   rw 3 q37 ∷
   rw 2 q30 ∷
   re 3 3 (ℓ "个") ∷
   rw 1 q38 ∷
   rw 0 q35 ∷
   rw 1 q39 ∷
   re 1 8 (ℓ "九") ∷
   rw 1 q1 ∷
   re 1 1 (ℓ "乏九乏") ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q3 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q4 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 9 q6 ∷
   rw⁻ 0 q35 ∷
   rw 1 q41 ∷
   rw 4 q30 ∷
   re 2 3 (ℓ "个") ∷
   rw 3 q42 ∷
   rw 6 q30 ∷
   re 4 3 (ℓ "个") ∷
   re 6 1 (ℓ "乏丼丠丼乏") ∷
   rw 5 q31 ∷
   rw⁻ 7 q40 ∷
   rw 8 q33 ∷
   re 5 5 (ℓ "中") ∷
   rw⁻ 6 q35 ∷
   rw⁻ 7 q34 ∷
   rw 0 q17 ∷
   rw 1 q43 ∷
   rw 2 q44 ∷
   rw 3 q45 ∷
   rw 4 q46 ∷
   rw 5 q45 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q19 ∷
   rw 7 q47 ∷
   rw 8 q19 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q43 ∷
   rw 8 q48 ∷
   rw 1 q49 ∷
   re 1 8 (ℓ "乢") ∷
   re 0 3 (ℓ "也") ∷
   re 2 1 (ℓ "丼丠丼") ∷
   rw 1 q36 ∷
   re 3 1 (ℓ "乏九乏") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q3 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q4 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q5 ∷
   rw 11 q6 ∷
   rw⁻ 2 q35 ∷
   rw 3 q41 ∷
   rw 6 q30 ∷
   re 4 3 (ℓ "个") ∷
   rw 5 q42 ∷
   rw 8 q30 ∷
   re 6 3 (ℓ "个") ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 7 q31 ∷
   rw⁻ 9 q40 ∷
   rw 10 q33 ∷
   re 7 5 (ℓ "中") ∷
   rw⁻ 8 q35 ∷
   rw⁻ 9 q34 ∷
   rw 2 q17 ∷
   rw 3 q43 ∷
   rw 4 q44 ∷
   rw 5 q45 ∷
   rw 6 q46 ∷
   rw 7 q45 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q19 ∷
   rw 9 q47 ∷
   rw 10 q19 ∷
   re 8 3 (ℓ "丽") ∷
   rw 9 q43 ∷
   rw 10 q48 ∷
   rw 3 q49 ∷
   re 3 8 (ℓ "乢") ∷
   re 2 3 (ℓ "也") ∷
   re 4 1 (ℓ "丼両丼") ∷
   rw 3 q36 ∷
   rw 4 q36 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = wE 9 W
  q51 : Eqn
  q51 = wE 127 W
  q52 : Eqn
  q52 = wE 271 W
  q53 : Eqn
  q53 = wE 8 W
  q54 : Eqn
  q54 = wE 10 W
  q55 : Eqn
  q55 = wE 272 W
  q56 : Eqn
  q56 = wE 28 W
  q57 : Eqn
  q57 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q58 : Eqn
  q58 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q59 : Eqn
  q59 = eqn (ℓ "丁乏") (ℓ "乏丁") (low-comm ((iI ↑)) (Swap))
  q60 : Eqn
  q60 = wE 274 W
  q61 : Eqn
  q61 = wE 322 W

-- S2 @1023: 135 steps
lem-S2-at1023 : ⟪ (ℓ "习丽习举") ⟫ʷ ≈ ⟪ (ℓ "乡丶乡丷") ⟫ʷ
lem-S2-at1023 = derive (ℓ "习丽习举") (ℓ "乡丶乡丷")
  (rw 4 q17 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw⁻ 5 q19 ∷
   rw 4 q50 ∷
   rw⁻ 3 q19 ∷
   re 4 3 (ℓ "丮") ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 9 q51 ∷
   rw 8 q52 ∷
   rw 7 q18 ∷
   rw 6 q53 ∷
   rw 5 q50 ∷
   rw 4 q53 ∷
   rw 3 q54 ∷
   rw 2 q52 ∷
   rw 3 q55 ∷
   re 3 8 (ℓ "九") ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw⁻ 3 q19 ∷
   rw 2 q54 ∷
   rw⁻ 1 q19 ∷
   re 2 3 (ℓ "中") ∷
   re 0 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 7 q51 ∷
   rw 6 q52 ∷
   rw 5 q18 ∷
   rw 4 q53 ∷
   rw 3 q50 ∷
   rw 2 q53 ∷
   rw 1 q54 ∷
   rw 0 q52 ∷
   rw 1 q55 ∷
   re 1 8 (ℓ "九") ∷
   rw 1 q1 ∷
   re 1 1 (ℓ "乏九乏") ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q3 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q4 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 9 q6 ∷
   rw 0 q43 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q19 ∷
   rw 2 q21 ∷
   rw 3 q19 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q56 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q19 ∷
   rw 4 q28 ∷
   rw 5 q19 ∷
   re 3 3 (ℓ "丮") ∷
   rw 4 q56 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q19 ∷
   rw 6 q47 ∷
   rw 7 q19 ∷
   re 5 3 (ℓ "丽") ∷
   rw 6 q43 ∷
   rw 7 q48 ∷
   rw 0 q2 ∷
   rw⁻ 1 q57 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 2 q6 ∷
   rw⁻ 3 q58 ∷
   re 5 1 (ℓ "乏丨乏") ∷
   rw 4 q6 ∷
   rw⁻ 5 q58 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q6 ∷
   rw⁻ 7 q57 ∷
   rw⁻ 8 q59 ∷
   rw 1 q60 ∷
   re 1 8 (ℓ "习") ∷
   re 0 3 (ℓ "乡") ∷
   rw 1 q47 ∷
   re 3 1 (ℓ "乏九乏") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q3 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q4 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q5 ∷
   rw 11 q6 ∷
   rw 2 q43 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q19 ∷
   rw 4 q21 ∷
   rw 5 q19 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q56 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q19 ∷
   rw 6 q28 ∷
   rw 7 q19 ∷
   re 5 3 (ℓ "丮") ∷
   rw 6 q56 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q19 ∷
   rw 8 q47 ∷
   rw 9 q19 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q43 ∷
   rw 9 q48 ∷
   rw 2 q2 ∷
   rw⁻ 3 q57 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 4 q6 ∷
   rw⁻ 5 q58 ∷
   re 7 1 (ℓ "乏丨乏") ∷
   rw 6 q6 ∷
   rw⁻ 7 q58 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw⁻ 9 q57 ∷
   rw⁻ 10 q59 ∷
   rw 3 q60 ∷
   re 3 8 (ℓ "习") ∷
   re 2 3 (ℓ "乡") ∷
   rw 3 q61 ∷
   rw 4 q22 ∷ []) Eq.refl

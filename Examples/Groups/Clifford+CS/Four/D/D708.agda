{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD708 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D708 (W : Ws) (Sᴰ : SD708) where

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
  lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 1926
  lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 0 Sᴰ
  lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 1930
  lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 1 Sᴰ
  lem-pass-X1-CK13-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 2008
  lem-pass-X1-CK13-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 2 Sᴰ
  lem-pass-X1-CKd13-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 2009
  lem-pass-X1-CKd13-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 3 Sᴰ
  lem-pass-X1-TOFF012-CS03-TOFF012-CSd03-X1-vs-CCZ123 : St 2016
  lem-pass-X1-TOFF012-CS03-TOFF012-CSd03-X1-vs-CCZ123 = pickᴰ 4 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q3 : Eqn
  q3 = wE 173 W
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = wE 1682 W
  q6 : Eqn
  q6 = wE 175 W
  q7 : Eqn
  q7 = wE 1490 W
  q8 : Eqn
  q8 = sE 1926 lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [X3 CS30 X3] [X1 TOFF012 CS03 TOFF012 CSd03 X1]: 49 steps
lem-pass-X3-CS30-X3-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : ⟪ (ℓ "丞中丞丒九中九丮丒") ⟫ʷ ≈ ⟪ (ℓ "丒九中九丮丒丞中丞") ⟫ʷ
lem-pass-X3-CS30-X3-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = derive (ℓ "丞中丞丒九中九丮丒") (ℓ "丒九中九丮丒丞中丞")
  (rw 4 q1 ∷
   rw 3 q2 ∷
   rw 2 q3 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q4 ∷
   rw 0 q3 ∷
   rw 1 q5 ∷
   rw⁻ 0 q2 ∷
   rw 1 q6 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 4 q1 ∷
   rw 3 q3 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q4 ∷
   rw 1 q3 ∷
   rw 2 q7 ∷
   rw 1 q6 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 1 q8 ∷
   rw 8 q1 ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q4 ∷
   rw 5 q3 ∷
   rw 6 q7 ∷
   rw 5 q6 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q6 ∷
   rw 8 q4 ∷
   rw 9 q1 ∷
   rw 8 q2 ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q4 ∷
   rw 5 q3 ∷
   rw 6 q5 ∷
   rw⁻ 5 q2 ∷
   rw 6 q6 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q6 ∷
   rw 9 q4 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = wE 1681 W
  q10 : Eqn
  q10 = eqn (ℓ "三乏") (ℓ "乏三") (low₁-comm ((S • S • S)) ((Swap ↑)))
  q11 : Eqn
  q11 = wE 1667 W
  q12 : Eqn
  q12 = sE 1930 lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q13 : Eqn
  q13 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q14 : Eqn
  q14 = wE 1668 W

-- pass [X3 CSd30 X3] [X1 Sd0 TOFF012 CS03 TOFF012 CSd03 S0 X1]: 53 steps
lem-pass-X3-CSd30-X3-vs-X1-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X1 : ⟪ (ℓ "丞丮丞丒三九中九丮丈丒") ⟫ʷ ≈ ⟪ (ℓ "丒三九中九丮丈丒丞丮丞") ⟫ʷ
lem-pass-X3-CSd30-X3-vs-X1-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X1 = derive (ℓ "丞丮丞丒三九中九丮丈丒") (ℓ "丒三九中九丮丈丒丞丮丞")
  (rw 4 q1 ∷
   rw 3 q2 ∷
   rw 2 q3 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw 3 q4 ∷
   rw 0 q3 ∷
   rw 1 q9 ∷
   rw⁻ 0 q2 ∷
   rw 1 q6 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 5 q1 ∷
   rw 4 q10 ∷
   rw 3 q3 ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q4 ∷
   rw 1 q3 ∷
   rw 2 q11 ∷
   rw⁻ 1 q10 ∷
   rw 2 q6 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丮") ∷
   rw 4 q6 ∷
   rw 5 q4 ∷
   rw 2 q12 ∷
   rw 10 q1 ∷
   rw 9 q13 ∷
   rw 8 q3 ∷
   re 7 1 (ℓ "乏丨乏") ∷
   rw 9 q4 ∷
   rw 6 q3 ∷
   rw 7 q14 ∷
   rw⁻ 6 q13 ∷
   rw 7 q6 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "丮") ∷
   rw 9 q6 ∷
   rw 10 q4 ∷
   rw 11 q1 ∷
   rw 10 q2 ∷
   rw 9 q3 ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw 10 q4 ∷
   rw 7 q3 ∷
   rw 8 q9 ∷
   rw⁻ 7 q2 ∷
   rw 8 q6 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "丮") ∷
   rw 10 q6 ∷
   rw 11 q4 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = wE 2082 W
  q16 : Eqn
  q16 = sE 2009 lem-pass-X1-CKd13-X1-vs-TOFF012-CS03-TOFF012-CSd03
  q17 : Eqn
  q17 = wE 2083 W

-- pass [CKd13] [X1 TOFF012 CS03 TOFF012 CSd03 X1]: 3 steps
lem-pass-CKd13-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : ⟪ (ℓ "乂丒九中九丮丒") ⟫ʷ ≈ ⟪ (ℓ "丒九中九丮丒乂") ⟫ʷ
lem-pass-CKd13-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = derive (ℓ "乂丒九中九丮丒") (ℓ "丒九中九丮丒乂")
  (rw 0 q15 ∷
   rw 1 q16 ∷
   rw 5 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = sE 2016 lem-pass-X1-TOFF012-CS03-TOFF012-CSd03-X1-vs-CCZ123

-- pass [CCZ123] [X1 TOFF012 CS03 TOFF012 CSd03 X1]: 1 steps
lem-pass-CCZ123-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : ⟪ (ℓ "乜丒九中九丮丒") ⟫ʷ ≈ ⟪ (ℓ "丒九中九丮丒乜") ⟫ʷ
lem-pass-CCZ123-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = derive (ℓ "乜丒九中九丮丒") (ℓ "丒九中九丮丒乜")
  (rw⁻ 0 q18 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = wE 2084 W
  q20 : Eqn
  q20 = sE 2008 lem-pass-X1-CK13-X1-vs-TOFF012-CS03-TOFF012-CSd03
  q21 : Eqn
  q21 = wE 2085 W

-- pass [CK13] [X1 TOFF012 CS03 TOFF012 CSd03 X1]: 3 steps
lem-pass-CK13-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : ⟪ (ℓ "乁丒九中九丮丒") ⟫ʷ ≈ ⟪ (ℓ "丒九中九丮丒乁") ⟫ʷ
lem-pass-CK13-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = derive (ℓ "乁丒九中九丮丒") (ℓ "丒九中九丮丒乁")
  (rw 0 q19 ∷
   rw 1 q20 ∷
   rw 5 q21 ∷ []) Eq.refl

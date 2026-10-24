{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD620 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D620 (W : Ws) (Sᴰ : SD620) where

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
  lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-TOFF201-X0 : St 1409
  lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-TOFF201-X0 = pickᴰ 0 Sᴰ
  lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-X0-TOFF201-X0 : St 1410
  lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-X0-TOFF201-X0 = pickᴰ 1 Sᴰ

private
  q1 : Eqn
  q1 = sE 1409 lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-TOFF201-X0

-- Bar(SSKSKK;0,2->3) passes factors of X0 TOFF201 X0: 1 steps
lem-Bar⟨SSKSKK02-⟶3⟩-passes-factors-of-X0-TOFF201-X0 : ⟪ (ℓ "中中丱中丱丱个乍且乍且义义义乍且义义义义义义个义义乍义乍乍丌乣丌") ⟫ʷ ≈ ⟪ (ℓ "丌乣丌中中丱中丱丱个乍且乍且义义义乍且义义义义义义个义义乍义乍乍") ⟫ʷ
lem-Bar⟨SSKSKK02-⟶3⟩-passes-factors-of-X0-TOFF201-X0 = derive (ℓ "中中丱中丱丱个乍且乍且义义义乍且义义义义义义个义义乍义乍乍丌乣丌") (ℓ "丌乣丌中中丱中丱丱个乍且乍且义义义乍且义义义义义义个义义乍义乍乍")
  (rw 0 q1 ∷ []) Eq.refl

private
  q2 : Eqn
  q2 = sE 1410 lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-X0-TOFF201-X0

-- Bar(SSSKSS;0,2->3) passes factors of X0 TOFF201 X0: 1 steps
lem-Bar⟨SSSKSS02-⟶3⟩-passes-factors-of-X0-TOFF201-X0 : ⟪ (ℓ "中中中丱中中个义义义义义义乍且义义义义义义义义义个义义义乍义义丌乣丌") ⟫ʷ ≈ ⟪ (ℓ "丌乣丌中中中丱中中个义义义义义义乍且义义义义义义义义义个义义义乍义义") ⟫ʷ
lem-Bar⟨SSSKSS02-⟶3⟩-passes-factors-of-X0-TOFF201-X0 = derive (ℓ "中中中丱中中个义义义义义义乍且义义义义义义义义义个义义义乍义义丌乣丌") (ℓ "丌乣丌中中中丱中中个义义义义义义乍且义义义义义义义义义个义义义乍义义")
  (rw 0 q2 ∷ []) Eq.refl

private
  q3 : Eqn
  q3 = wE 1855 W
  q4 : Eqn
  q4 = wE 5 W
  q5 : Eqn
  q5 = wE 1106 W
  q6 : Eqn
  q6 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q7 : Eqn
  q7 = eqn (ℓ "並乍") (ℓ "乍並") (low-comm (Swap) (CK₀₁))
  q8 : Eqn
  q8 = wE 74 W
  q9 : Eqn
  q9 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q10 : Eqn
  q10 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q11 : Eqn
  q11 = wE 7 W
  q12 : Eqn
  q12 = wE 772 W
  q13 : Eqn
  q13 = wE 1861 W
  q14 : Eqn
  q14 = wE 27 W
  q15 : Eqn
  q15 = wE 329 W
  q16 : Eqn
  q16 = wE 30 W
  q17 : Eqn
  q17 = wE 317 W
  q18 : Eqn
  q18 = wE 31 W
  q19 : Eqn
  q19 = sE 1410 lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-X0-TOFF201-X0
  q20 : Eqn
  q20 = wE 1862 W
  q21 : Eqn
  q21 = wE 1858 W

-- pass [TOFF201] [X0 CS03 CS03 CS03 CK03 CS03 CS03 CX02 CS23 CS23 CS23 CS23 CS23 CS23 CK23 S2 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX02 CS23 CS23 CS23 CK23 CS23 CS23 X0]: 237 steps
lem-pass-TOFF201-vs-X0-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-X0 : ⟪ (ℓ "乣丌中中中丱中中个义义义义义义乍且义义义义义义义义义个义义义乍义义丌") ⟫ʷ ≈ ⟪ (ℓ "丌中中中丱中中个义义义义义义乍且义义义义义义义义义个义义义乍义义丌乣") ⟫ʷ
lem-pass-TOFF201-vs-X0-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-X0 = derive (ℓ "乣丌中中中丱中中个义义义义义义乍且义义义义义义义义义个义义义乍义义丌") (ℓ "丌中中中丱中中个义义义义义义乍且义义义义义义义义义个义义义乍义义丌乣")
  (rw 0 q3 ∷
   rw 38 q4 ∷
   rw 37 q5 ∷
   rw⁻ 36 q6 ∷
   rw⁻ 35 q6 ∷
   rw⁻ 34 q7 ∷
   rw⁻ 33 q6 ∷
   rw⁻ 32 q6 ∷
   rw⁻ 31 q6 ∷
   rw 30 q8 ∷
   rw⁻ 29 q6 ∷
   rw⁻ 28 q6 ∷
   rw⁻ 27 q6 ∷
   rw⁻ 26 q6 ∷
   rw⁻ 25 q6 ∷
   rw⁻ 24 q6 ∷
   rw⁻ 23 q6 ∷
   rw⁻ 22 q6 ∷
   rw⁻ 21 q6 ∷
   rw⁻ 20 q9 ∷
   rw⁻ 19 q7 ∷
   rw⁻ 18 q6 ∷
   rw⁻ 17 q6 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 15 q6 ∷
   rw⁻ 14 q6 ∷
   rw⁻ 13 q6 ∷
   rw 12 q8 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q10 ∷
   rw 12 q11 ∷
   rw⁻ 11 q10 ∷
   re 12 3 (ℓ "丽") ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q10 ∷
   rw 11 q11 ∷
   rw⁻ 10 q10 ∷
   re 11 3 (ℓ "丽") ∷
   re 9 1 (ℓ "乏丫乏") ∷
   rw⁻ 11 q10 ∷
   rw 10 q12 ∷
   rw⁻ 9 q10 ∷
   re 10 3 (ℓ "乁") ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q10 ∷
   rw 9 q11 ∷
   rw⁻ 8 q10 ∷
   re 9 3 (ℓ "丽") ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q10 ∷
   rw 8 q11 ∷
   rw⁻ 7 q10 ∷
   re 8 3 (ℓ "丽") ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q10 ∷
   rw 7 q11 ∷
   rw⁻ 6 q10 ∷
   re 7 3 (ℓ "丽") ∷
   rw 5 q5 ∷
   rw 4 q5 ∷
   rw 5 q13 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q10 ∷
   rw 5 q14 ∷
   rw 6 q10 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q10 ∷
   rw 6 q14 ∷
   rw 7 q10 ∷
   re 5 3 (ℓ "中") ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q10 ∷
   rw 7 q14 ∷
   rw 8 q10 ∷
   re 6 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏为乏") ∷
   rw 7 q10 ∷
   rw 8 q15 ∷
   rw 9 q10 ∷
   re 7 3 (ℓ "丱") ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q10 ∷
   rw 9 q14 ∷
   rw 10 q10 ∷
   re 8 3 (ℓ "中") ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q10 ∷
   rw 10 q14 ∷
   rw 11 q10 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q16 ∷
   rw 11 q6 ∷
   rw 12 q6 ∷
   rw 13 q6 ∷
   rw 14 q6 ∷
   rw 15 q6 ∷
   rw 16 q6 ∷
   rw 17 q7 ∷
   rw 18 q9 ∷
   rw 19 q6 ∷
   rw 20 q6 ∷
   rw 21 q6 ∷
   rw 22 q6 ∷
   rw 23 q6 ∷
   rw 24 q6 ∷
   rw 25 q6 ∷
   rw 26 q6 ∷
   rw 27 q6 ∷
   rw 28 q16 ∷
   rw 29 q6 ∷
   rw 30 q6 ∷
   rw 31 q6 ∷
   rw 32 q7 ∷
   rw 33 q6 ∷
   rw 34 q6 ∷
   rw 35 q17 ∷
   rw 36 q18 ∷
   rw⁻ 1 q19 ∷
   rw 32 q4 ∷
   rw⁻ 31 q6 ∷
   rw⁻ 30 q6 ∷
   rw⁻ 29 q7 ∷
   rw⁻ 28 q6 ∷
   rw⁻ 27 q6 ∷
   rw⁻ 26 q6 ∷
   rw 25 q8 ∷
   rw⁻ 24 q6 ∷
   rw⁻ 23 q6 ∷
   rw⁻ 22 q6 ∷
   rw⁻ 21 q6 ∷
   rw⁻ 20 q6 ∷
   rw⁻ 19 q6 ∷
   rw⁻ 18 q6 ∷
   rw⁻ 17 q6 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 15 q9 ∷
   rw⁻ 14 q7 ∷
   rw⁻ 13 q6 ∷
   rw⁻ 12 q6 ∷
   rw⁻ 11 q6 ∷
   rw⁻ 10 q6 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 8 q6 ∷
   rw 7 q8 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q10 ∷
   rw 7 q11 ∷
   rw⁻ 6 q10 ∷
   re 7 3 (ℓ "丽") ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q10 ∷
   rw 6 q11 ∷
   rw⁻ 5 q10 ∷
   re 6 3 (ℓ "丽") ∷
   re 4 1 (ℓ "乏丫乏") ∷
   rw⁻ 6 q10 ∷
   rw 5 q12 ∷
   rw⁻ 4 q10 ∷
   re 5 3 (ℓ "乁") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q10 ∷
   rw 4 q11 ∷
   rw⁻ 3 q10 ∷
   re 4 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q10 ∷
   rw 3 q11 ∷
   rw⁻ 2 q10 ∷
   re 3 3 (ℓ "丽") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q10 ∷
   rw 2 q11 ∷
   rw⁻ 1 q10 ∷
   re 2 3 (ℓ "丽") ∷
   rw 0 q5 ∷
   rw 1 q20 ∷
   rw 0 q17 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q10 ∷
   rw 2 q14 ∷
   rw 3 q10 ∷
   re 1 3 (ℓ "中") ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q10 ∷
   rw 3 q14 ∷
   rw 4 q10 ∷
   re 2 3 (ℓ "中") ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q10 ∷
   rw 4 q14 ∷
   rw 5 q10 ∷
   re 3 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏为乏") ∷
   rw 4 q10 ∷
   rw 5 q15 ∷
   rw 6 q10 ∷
   re 4 3 (ℓ "丱") ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q10 ∷
   rw 6 q14 ∷
   rw 7 q10 ∷
   re 5 3 (ℓ "中") ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q10 ∷
   rw 7 q14 ∷
   rw 8 q10 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q16 ∷
   rw 8 q6 ∷
   rw 9 q6 ∷
   rw 10 q6 ∷
   rw 11 q6 ∷
   rw 12 q6 ∷
   rw 13 q6 ∷
   rw 14 q7 ∷
   rw 15 q9 ∷
   rw 16 q6 ∷
   rw 17 q6 ∷
   rw 18 q6 ∷
   rw 19 q6 ∷
   rw 20 q6 ∷
   rw 21 q6 ∷
   rw 22 q6 ∷
   rw 23 q6 ∷
   rw 24 q6 ∷
   rw 25 q16 ∷
   rw 26 q6 ∷
   rw 27 q6 ∷
   rw 28 q6 ∷
   rw 29 q7 ∷
   rw 30 q6 ∷
   rw 31 q6 ∷
   rw 32 q17 ∷
   rw 33 q17 ∷
   rw 34 q18 ∷
   rw 33 q21 ∷ []) Eq.refl

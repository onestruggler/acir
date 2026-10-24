{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D494 (W : Ws) where

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
  q2 = wE 1106 W
  q3 : Eqn
  q3 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = wE 772 W
  q5 : Eqn
  q5 = wE 7 W
  q6 : Eqn
  q6 = eqn (ℓ "並乍") (ℓ "乍並") (low-comm (Swap) (CK₀₁))
  q7 : Eqn
  q7 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q8 : Eqn
  q8 = wE 74 W
  q9 : Eqn
  q9 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q10 : Eqn
  q10 = wE 1303 W
  q11 : Eqn
  q11 = wE 317 W
  q12 : Eqn
  q12 = wE 27 W
  q13 : Eqn
  q13 = wE 329 W
  q14 : Eqn
  q14 = wE 30 W
  q15 : Eqn
  q15 = wE 31 W
  q16 : Eqn
  q16 = eqn (ℓ "丌乍") (ℓ "乍丌") (low₁-comm (X) ((CK₀₁ ↑)))
  q17 : Eqn
  q17 = eqn (ℓ "丣乍") (ℓ "乍丣") (low-comm (CX₀₁) (CK₀₁))
  q18 : Eqn
  q18 = eqn (ℓ "丌义") (ℓ "义丌") (low₁-comm (X) ((CS ↑)))
  q19 : Eqn
  q19 = eqn (ℓ "丣义") (ℓ "义丣") (low-comm (CX₀₁) (CS))
  q20 : Eqn
  q20 = wE 1244 W
  q21 : Eqn
  q21 = eqn (ℓ "丌且") (ℓ "且丌") (low₁-comm (X) ((S ↑)))
  q22 : Eqn
  q22 = eqn (ℓ "丣且") (ℓ "且丣") (low-comm (CX₀₁) (S))
  q23 : Eqn
  q23 = wE 1 W
  q24 : Eqn
  q24 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q25 : Eqn
  q25 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q26 : Eqn
  q26 = wE 3 W
  q27 : Eqn
  q27 = wE 1245 W
  q28 : Eqn
  q28 = wE 1304 W
  q29 : Eqn
  q29 = wE 352 W
  q30 : Eqn
  q30 = wE 357 W
  q31 : Eqn
  q31 = wE 1247 W
  q32 : Eqn
  q32 = wE 20 W
  q33 : Eqn
  q33 = wE 49 W
  q34 : Eqn
  q34 = wE 1305 W

-- Bar(SSKSKK;0,2->3) passes groups of WBar(SSKSKK;~0,1->3) part0: 500 steps
lem-Bar⟨SSKSKK02-⟶3⟩-passes-groups-of-WBar⟨SSKSKK~01-⟶3⟩-part0 : ⟪ (ℓ "中中丱中丱丱个乍且乍且义义义乍且义义义义义义个义义乍义乍乍丌中中丱中丱丱丌丌丣丌乁与乁与丽丽丽乁与丽丽丽丽丽丽丌丣丌丽丽乁丽乁乁") ⟫ʷ ≈ ⟪ (ℓ "丌中中丱中丱丱丌丌丣丌中中丱中丱丱乁与乁与乏丶丰乏丽丽乁与丽丽丽丽丽丽乍且乍且义义义乍且义义义义义义个义义乍义乍乍丌丣丌丽丽乁丽乁乁") ⟫ʷ
lem-Bar⟨SSKSKK02-⟶3⟩-passes-groups-of-WBar⟨SSKSKK~01-⟶3⟩-part0 = derive (ℓ "中中丱中丱丱个乍且乍且义义义乍且义义义义义义个义义乍义乍乍丌中中丱中丱丱丌丌丣丌乁与乁与丽丽丽乁与丽丽丽丽丽丽丌丣丌丽丽乁丽乁乁") (ℓ "丌中中丱中丱丱丌丌丣丌中中丱中丱丱乁与乁与乏丶丰乏丽丽乁与丽丽丽丽丽丽乍且乍且义义义乍且义义义义义义个义义乍义乍乍丌丣丌丽丽乁丽乁乁")
  (rw 37 q1 ∷
   rw 36 q2 ∷
   re 35 1 (ℓ "乏丫乏") ∷
   rw⁻ 37 q3 ∷
   rw 36 q4 ∷
   rw⁻ 35 q3 ∷
   re 36 3 (ℓ "乁") ∷
   re 34 1 (ℓ "乏丫乏") ∷
   rw⁻ 36 q3 ∷
   rw 35 q4 ∷
   rw⁻ 34 q3 ∷
   re 35 3 (ℓ "乁") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q3 ∷
   rw 34 q5 ∷
   rw⁻ 33 q3 ∷
   re 34 3 (ℓ "丽") ∷
   re 32 1 (ℓ "乏丫乏") ∷
   rw⁻ 34 q3 ∷
   rw 33 q4 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (ℓ "乁") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q3 ∷
   rw 32 q5 ∷
   rw⁻ 31 q3 ∷
   re 32 3 (ℓ "丽") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q3 ∷
   rw 31 q5 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (ℓ "丽") ∷
   rw 29 q2 ∷
   rw⁻ 28 q6 ∷
   rw⁻ 27 q6 ∷
   rw⁻ 26 q7 ∷
   rw⁻ 25 q6 ∷
   rw⁻ 24 q7 ∷
   rw⁻ 23 q7 ∷
   rw 22 q8 ∷
   rw⁻ 21 q7 ∷
   rw⁻ 20 q7 ∷
   rw⁻ 19 q7 ∷
   rw⁻ 18 q7 ∷
   rw⁻ 17 q7 ∷
   rw⁻ 16 q7 ∷
   rw⁻ 15 q9 ∷
   rw⁻ 14 q6 ∷
   rw⁻ 13 q7 ∷
   rw⁻ 12 q7 ∷
   rw⁻ 11 q7 ∷
   rw⁻ 10 q9 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 8 q9 ∷
   rw⁻ 7 q6 ∷
   rw 6 q8 ∷
   re 5 1 (ℓ "乏丫乏") ∷
   rw⁻ 7 q3 ∷
   rw 6 q4 ∷
   rw⁻ 5 q3 ∷
   re 6 3 (ℓ "乁") ∷
   re 4 1 (ℓ "乏丫乏") ∷
   rw⁻ 6 q3 ∷
   rw 5 q4 ∷
   rw⁻ 4 q3 ∷
   re 5 3 (ℓ "乁") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q3 ∷
   rw 4 q5 ∷
   rw⁻ 3 q3 ∷
   re 4 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乏丫乏") ∷
   rw⁻ 4 q3 ∷
   rw 3 q4 ∷
   rw⁻ 2 q3 ∷
   re 3 3 (ℓ "乁") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q3 ∷
   rw 2 q5 ∷
   rw⁻ 1 q3 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q3 ∷
   rw 1 q5 ∷
   rw⁻ 0 q3 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q10 ∷
   rw 0 q11 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q3 ∷
   rw 2 q12 ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "中") ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q3 ∷
   rw 3 q12 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "中") ∷
   re 4 1 (ℓ "乏为乏") ∷
   rw 3 q3 ∷
   rw 4 q13 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "丱") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q3 ∷
   rw 5 q12 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏为乏") ∷
   rw 5 q3 ∷
   rw 6 q13 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "丱") ∷
   re 7 1 (ℓ "乏为乏") ∷
   rw 6 q3 ∷
   rw 7 q13 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "丱") ∷
   rw 7 q11 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q3 ∷
   rw 9 q12 ∷
   rw 10 q3 ∷
   re 8 3 (ℓ "中") ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q3 ∷
   rw 10 q12 ∷
   rw 11 q3 ∷
   re 9 3 (ℓ "中") ∷
   re 11 1 (ℓ "乏为乏") ∷
   rw 10 q3 ∷
   rw 11 q13 ∷
   rw 12 q3 ∷
   re 10 3 (ℓ "丱") ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q3 ∷
   rw 12 q12 ∷
   rw 13 q3 ∷
   re 11 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏为乏") ∷
   rw 12 q3 ∷
   rw 13 q13 ∷
   rw 14 q3 ∷
   re 12 3 (ℓ "丱") ∷
   re 14 1 (ℓ "乏为乏") ∷
   rw 13 q3 ∷
   rw 14 q13 ∷
   rw 15 q3 ∷
   re 13 3 (ℓ "丱") ∷
   rw 14 q14 ∷
   rw 15 q6 ∷
   rw 16 q9 ∷
   rw 17 q6 ∷
   rw 18 q9 ∷
   rw 19 q7 ∷
   rw 20 q7 ∷
   rw 21 q7 ∷
   rw 22 q6 ∷
   rw 23 q9 ∷
   rw 24 q7 ∷
   rw 25 q7 ∷
   rw 26 q7 ∷
   rw 27 q7 ∷
   rw 28 q7 ∷
   rw 29 q7 ∷
   rw 30 q14 ∷
   rw 31 q7 ∷
   rw 32 q7 ∷
   rw 33 q6 ∷
   rw 34 q7 ∷
   rw 35 q6 ∷
   rw 36 q6 ∷
   rw 37 q15 ∷
   rw⁻ 36 q16 ∷
   rw⁻ 37 q17 ∷
   rw⁻ 38 q16 ∷
   rw⁻ 35 q16 ∷
   rw⁻ 36 q17 ∷
   rw⁻ 37 q16 ∷
   rw⁻ 34 q18 ∷
   rw⁻ 35 q19 ∷
   rw⁻ 36 q18 ∷
   rw⁻ 33 q16 ∷
   rw⁻ 34 q17 ∷
   rw⁻ 35 q16 ∷
   rw⁻ 32 q18 ∷
   rw⁻ 33 q19 ∷
   rw⁻ 34 q18 ∷
   rw⁻ 31 q18 ∷
   rw⁻ 32 q19 ∷
   rw⁻ 33 q18 ∷
   rw 30 q20 ∷
   rw⁻ 29 q18 ∷
   rw⁻ 30 q19 ∷
   rw⁻ 31 q18 ∷
   rw⁻ 28 q18 ∷
   rw⁻ 29 q19 ∷
   rw⁻ 30 q18 ∷
   rw⁻ 27 q18 ∷
   rw⁻ 28 q19 ∷
   rw⁻ 29 q18 ∷
   rw⁻ 26 q18 ∷
   rw⁻ 27 q19 ∷
   rw⁻ 28 q18 ∷
   rw⁻ 25 q18 ∷
   rw⁻ 26 q19 ∷
   rw⁻ 27 q18 ∷
   rw⁻ 24 q18 ∷
   rw⁻ 25 q19 ∷
   rw⁻ 26 q18 ∷
   rw⁻ 23 q21 ∷
   rw⁻ 24 q22 ∷
   rw⁻ 25 q21 ∷
   rw⁻ 22 q16 ∷
   rw⁻ 23 q17 ∷
   rw⁻ 24 q16 ∷
   rw⁻ 21 q18 ∷
   rw⁻ 22 q19 ∷
   rw⁻ 23 q18 ∷
   rw⁻ 20 q18 ∷
   rw⁻ 21 q19 ∷
   rw⁻ 22 q18 ∷
   rw⁻ 19 q18 ∷
   rw⁻ 20 q19 ∷
   rw⁻ 21 q18 ∷
   rw⁻ 18 q21 ∷
   rw⁻ 19 q22 ∷
   rw⁻ 20 q21 ∷
   rw⁻ 17 q16 ∷
   rw⁻ 18 q17 ∷
   rw⁻ 19 q16 ∷
   rw⁻ 16 q21 ∷
   rw⁻ 17 q22 ∷
   rw⁻ 18 q21 ∷
   rw⁻ 15 q16 ∷
   rw⁻ 16 q17 ∷
   rw⁻ 17 q16 ∷
   rw 14 q20 ∷
   rw 17 q23 ∷
   rw 16 q24 ∷
   rw 15 q25 ∷
   rw 14 q24 ∷
   re 13 1 (ℓ "乏丫乏") ∷
   rw 15 q26 ∷
   re 12 1 (ℓ "乏丫乏") ∷
   rw 14 q26 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q26 ∷
   re 10 1 (ℓ "乏丫乏") ∷
   rw 12 q26 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q26 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q26 ∷
   rw 9 q27 ∷
   rw⁻ 8 q24 ∷
   rw⁻ 9 q25 ∷
   rw⁻ 10 q24 ∷
   rw 13 q23 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q23 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q23 ∷
   re 13 3 (ℓ "丱") ∷
   rw 16 q23 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q23 ∷
   re 15 3 (ℓ "丱") ∷
   rw 18 q23 ∷
   re 16 3 (ℓ "丱") ∷
   rw 17 q26 ∷
   rw 34 q28 ∷
   re 34 1 (ℓ "乏为乏") ∷
   rw 33 q23 ∷
   re 34 3 (ℓ "丰") ∷
   re 34 1 (ℓ "乏丼丣丼乏") ∷
   rw 40 q23 ∷
   re 38 3 (ℓ "乁") ∷
   rw 37 q29 ∷
   rw 36 q17 ∷
   rw 35 q30 ∷
   re 35 1 (ℓ "乏为乏") ∷
   rw 34 q26 ∷
   re 35 5 (ℓ "丰") ∷
   re 35 1 (ℓ "乏个乏") ∷
   rw 37 q26 ∷
   re 33 3 (ℓ "乁") ∷
   rw 34 q31 ∷
   re 36 1 (ℓ "乏为乏") ∷
   rw 35 q23 ∷
   re 36 3 (ℓ "丰") ∷
   re 36 1 (ℓ "乏丼丣丼乏") ∷
   rw 42 q23 ∷
   re 40 3 (ℓ "乁") ∷
   rw 39 q29 ∷
   rw 38 q17 ∷
   rw 37 q30 ∷
   re 37 1 (ℓ "乏为乏") ∷
   rw 36 q26 ∷
   re 37 5 (ℓ "丰") ∷
   re 37 1 (ℓ "乏个乏") ∷
   rw 39 q26 ∷
   re 35 3 (ℓ "乁") ∷
   rw 36 q31 ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q23 ∷
   re 38 3 (ℓ "丰") ∷
   re 38 1 (ℓ "乏丼丣丼乏") ∷
   rw 44 q23 ∷
   re 42 3 (ℓ "丽") ∷
   rw 41 q32 ∷
   rw 40 q19 ∷
   rw 39 q33 ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q26 ∷
   re 39 5 (ℓ "丰") ∷
   re 39 1 (ℓ "乏个乏") ∷
   rw 41 q26 ∷
   re 37 3 (ℓ "丽") ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q23 ∷
   re 39 3 (ℓ "丰") ∷
   re 39 1 (ℓ "乏丼丣丼乏") ∷
   rw 45 q23 ∷
   re 43 3 (ℓ "丽") ∷
   rw 42 q32 ∷
   rw 41 q19 ∷
   rw 40 q33 ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 39 q26 ∷
   re 40 5 (ℓ "丰") ∷
   re 40 1 (ℓ "乏个乏") ∷
   rw 42 q26 ∷
   re 38 3 (ℓ "丽") ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 39 q23 ∷
   re 40 3 (ℓ "丰") ∷
   re 40 1 (ℓ "乏丼丣丼乏") ∷
   rw 46 q23 ∷
   re 44 3 (ℓ "丽") ∷
   rw 43 q32 ∷
   rw 42 q19 ∷
   rw 41 q33 ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q26 ∷
   re 41 5 (ℓ "丰") ∷
   re 41 1 (ℓ "乏个乏") ∷
   rw 43 q26 ∷
   re 39 3 (ℓ "丽") ∷
   re 41 1 (ℓ "乏为乏") ∷
   rw 40 q23 ∷
   re 41 3 (ℓ "丰") ∷
   re 41 1 (ℓ "乏丼丣丼乏") ∷
   rw 47 q23 ∷
   re 45 3 (ℓ "乁") ∷
   rw 44 q29 ∷
   rw 43 q17 ∷
   rw 42 q30 ∷
   re 42 1 (ℓ "乏为乏") ∷
   rw 41 q26 ∷
   re 42 5 (ℓ "丰") ∷
   re 42 1 (ℓ "乏个乏") ∷
   rw 44 q26 ∷
   re 40 3 (ℓ "乁") ∷
   rw 41 q31 ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q23 ∷
   re 43 3 (ℓ "丰") ∷
   re 43 1 (ℓ "乏丼丣丼乏") ∷
   rw 49 q23 ∷
   re 47 3 (ℓ "丽") ∷
   rw 46 q32 ∷
   rw 45 q19 ∷
   rw 44 q33 ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q26 ∷
   re 44 5 (ℓ "丰") ∷
   re 44 1 (ℓ "乏个乏") ∷
   rw 46 q26 ∷
   re 42 3 (ℓ "丽") ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q23 ∷
   re 44 3 (ℓ "丰") ∷
   re 44 1 (ℓ "乏丼丣丼乏") ∷
   rw 50 q23 ∷
   re 48 3 (ℓ "丽") ∷
   rw 47 q32 ∷
   rw 46 q19 ∷
   rw 45 q33 ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 44 q26 ∷
   re 45 5 (ℓ "丰") ∷
   re 45 1 (ℓ "乏个乏") ∷
   rw 47 q26 ∷
   re 43 3 (ℓ "丽") ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 44 q23 ∷
   re 45 3 (ℓ "丰") ∷
   re 45 1 (ℓ "乏丼丣丼乏") ∷
   rw 51 q23 ∷
   re 49 3 (ℓ "丽") ∷
   rw 48 q32 ∷
   rw 47 q19 ∷
   rw 46 q33 ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q26 ∷
   re 46 5 (ℓ "丰") ∷
   re 46 1 (ℓ "乏个乏") ∷
   rw 48 q26 ∷
   re 44 3 (ℓ "丽") ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q23 ∷
   re 46 3 (ℓ "丰") ∷
   re 46 1 (ℓ "乏丼丣丼乏") ∷
   rw 52 q23 ∷
   re 50 3 (ℓ "丽") ∷
   rw 49 q32 ∷
   rw 48 q19 ∷
   rw 47 q33 ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q26 ∷
   re 47 5 (ℓ "丰") ∷
   re 47 1 (ℓ "乏个乏") ∷
   rw 49 q26 ∷
   re 45 3 (ℓ "丽") ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q23 ∷
   re 47 3 (ℓ "丰") ∷
   re 47 1 (ℓ "乏丼丣丼乏") ∷
   rw 53 q23 ∷
   re 51 3 (ℓ "丽") ∷
   rw 50 q32 ∷
   rw 49 q19 ∷
   rw 48 q33 ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q26 ∷
   re 48 5 (ℓ "丰") ∷
   re 48 1 (ℓ "乏个乏") ∷
   rw 50 q26 ∷
   re 46 3 (ℓ "丽") ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q23 ∷
   re 48 3 (ℓ "丰") ∷
   re 48 1 (ℓ "乏丼丣丼乏") ∷
   rw 54 q23 ∷
   re 52 3 (ℓ "丽") ∷
   rw 51 q32 ∷
   rw 50 q19 ∷
   rw 49 q33 ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 48 q26 ∷
   re 49 5 (ℓ "丰") ∷
   re 49 1 (ℓ "乏个乏") ∷
   rw 51 q26 ∷
   re 47 3 (ℓ "丽") ∷
   rw 18 q34 ∷
   re 18 1 (ℓ "乏为乏") ∷
   rw 17 q23 ∷
   re 18 3 (ℓ "丰") ∷
   re 18 1 (ℓ "乏丼丣丼乏") ∷
   rw 24 q23 ∷
   re 22 3 (ℓ "乁") ∷
   rw 21 q29 ∷
   rw 20 q17 ∷
   rw 19 q30 ∷
   re 19 1 (ℓ "乏为乏") ∷
   rw 18 q26 ∷
   re 19 5 (ℓ "丰") ∷
   re 19 1 (ℓ "乏个乏") ∷
   rw 21 q26 ∷
   re 17 3 (ℓ "乁") ∷
   rw 18 q31 ∷
   re 20 1 (ℓ "乏为乏") ∷
   rw 19 q23 ∷
   re 20 3 (ℓ "丰") ∷
   re 20 1 (ℓ "乏丼丣丼乏") ∷
   rw 26 q23 ∷
   re 24 3 (ℓ "乁") ∷
   rw 23 q29 ∷
   rw 22 q17 ∷
   rw 21 q30 ∷
   re 21 1 (ℓ "乏为乏") ∷
   rw 20 q26 ∷
   re 21 5 (ℓ "丰") ∷
   re 21 1 (ℓ "乏个乏") ∷
   rw 23 q26 ∷
   re 19 3 (ℓ "乁") ∷
   rw 20 q31 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q23 ∷
   re 22 3 (ℓ "丰") ∷
   re 22 1 (ℓ "乏丼丣丼乏") ∷
   rw 28 q23 ∷
   re 26 3 (ℓ "丽") ∷
   rw 25 q32 ∷
   rw 24 q19 ∷
   rw 23 q33 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q26 ∷
   re 23 5 (ℓ "丰") ∷ []) Eq.refl

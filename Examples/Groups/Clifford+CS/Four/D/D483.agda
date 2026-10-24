{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D483 (W : Ws) where

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
  q3 = wE 772 W
  q4 : Eqn
  q4 = wE 7 W
  q5 : Eqn
  q5 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q6 : Eqn
  q6 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q7 : Eqn
  q7 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 74 W
  q9 : Eqn
  q9 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q10 : Eqn
  q10 = wE 1275 W
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
  q16 = eqn (ℓ "丌义") (ℓ "义丌") (low₁-comm (X) ((CS ↑)))
  q17 : Eqn
  q17 = eqn (ℓ "丣义") (ℓ "义丣") (low-comm (CX₀₁) (CS))
  q18 : Eqn
  q18 = eqn (ℓ "丌乗") (ℓ "乗丌") (low₁-comm (X) ((CK₁₀ ↑)))
  q19 : Eqn
  q19 = eqn (ℓ "丣乗") (ℓ "乗丣") (low-comm (CX₀₁) (CK₁₀))
  q20 : Eqn
  q20 = wE 1 W
  q21 : Eqn
  q21 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q22 : Eqn
  q22 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q23 : Eqn
  q23 = wE 3 W
  q24 : Eqn
  q24 = wE 1244 W
  q25 : Eqn
  q25 = eqn (ℓ "丌业") (ℓ "业丌") (low₁-comm (X) ((S ↑ ↑)))
  q26 : Eqn
  q26 = eqn (ℓ "丣业") (ℓ "业丣") (low-comm (CX₀₁) ((S ↑)))
  q27 : Eqn
  q27 = wE 1276 W
  q28 : Eqn
  q28 = wE 1277 W
  q29 : Eqn
  q29 = wE 352 W
  q30 : Eqn
  q30 = eqn (ℓ "丣乍") (ℓ "乍丣") (low-comm (CX₀₁) (CK₀₁))
  q31 : Eqn
  q31 = wE 357 W
  q32 : Eqn
  q32 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q33 : Eqn
  q33 = wE 1247 W
  q34 : Eqn
  q34 = wE 20 W
  q35 : Eqn
  q35 = wE 49 W
  q36 : Eqn
  q36 = wE 1278 W
  q37 : Eqn
  q37 = wE 1279 W
  q38 : Eqn
  q38 = wE 1280 W
  q39 : Eqn
  q39 = wE 1281 W
  q40 : Eqn
  q40 = wE 1282 W

-- Bar(SSSKSS;0,3->2) passes groups of WBar(SSKSKK;~0,1->2): 673 steps
lem-Bar⟨SSSKSS03-⟶2⟩-passes-groups-of-WBar⟨SSKSKK~01-⟶2⟩ : ⟪ (ℓ "丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义丌丧丧丫丧丫丫丌丌丣丌为与为与丶丶丶为与丶丶丶丶丶丶丌丣丌丶丶为丶为为") ⟫ʷ ≈ ⟪ (ℓ "丌丧丧丫丧丫丫丌丌丣丌为与为与丶丶丶为与丶丶丶丶丶丶丌丣丌丶丶为丶为为丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义") ⟫ʷ
lem-Bar⟨SSSKSS03-⟶2⟩-passes-groups-of-WBar⟨SSKSKK~01-⟶2⟩ = derive (ℓ "丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义丌丧丧丫丧丫丫丌丌丣丌为与为与丶丶丶为与丶丶丶丶丶丶丌丣丌丶丶为丶为为") (ℓ "丌丧丧丫丧丫丫丌丌丣丌为与为与丶丶丶为与丶丶丶丶丶丶丌丣丌丶丶为丶为为丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义")
  (rw 39 q1 ∷
   rw 38 q2 ∷
   rw 37 q3 ∷
   rw 36 q3 ∷
   rw 35 q4 ∷
   rw 34 q3 ∷
   rw 33 q4 ∷
   rw 32 q4 ∷
   rw 31 q2 ∷
   rw⁻ 30 q5 ∷
   rw⁻ 29 q5 ∷
   rw⁻ 28 q6 ∷
   rw⁻ 27 q5 ∷
   rw⁻ 26 q5 ∷
   rw⁻ 25 q5 ∷
   re 24 1 (ℓ "乏个乏") ∷
   rw⁻ 26 q7 ∷
   rw 25 q8 ∷
   rw⁻ 24 q7 ∷
   re 25 3 (ℓ "乀") ∷
   rw⁻ 23 q5 ∷
   rw⁻ 22 q5 ∷
   rw⁻ 21 q5 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 18 q5 ∷
   rw⁻ 17 q5 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 15 q5 ∷
   rw⁻ 14 q9 ∷
   rw⁻ 13 q6 ∷
   rw⁻ 12 q5 ∷
   rw⁻ 11 q5 ∷
   rw⁻ 10 q5 ∷
   rw⁻ 9 q5 ∷
   rw⁻ 8 q5 ∷
   rw⁻ 7 q5 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw⁻ 8 q7 ∷
   rw 7 q8 ∷
   rw⁻ 6 q7 ∷
   re 7 3 (ℓ "乀") ∷
   rw 5 q4 ∷
   rw 4 q4 ∷
   rw 3 q3 ∷
   rw 2 q4 ∷
   rw 1 q4 ∷
   rw 0 q4 ∷
   rw 1 q10 ∷
   rw 0 q11 ∷
   rw 1 q12 ∷
   rw 2 q12 ∷
   rw 3 q13 ∷
   rw 4 q12 ∷
   rw 5 q13 ∷
   rw 6 q13 ∷
   rw 7 q11 ∷
   rw 8 q12 ∷
   rw 9 q12 ∷
   rw 10 q12 ∷
   rw 11 q13 ∷
   rw 12 q12 ∷
   rw 13 q12 ∷
   re 15 1 (ℓ "乏丹乏") ∷
   rw 14 q7 ∷
   rw 15 q14 ∷
   rw 16 q7 ∷
   re 14 3 (ℓ "丰") ∷
   rw 15 q5 ∷
   rw 16 q5 ∷
   rw 17 q5 ∷
   rw 18 q5 ∷
   rw 19 q5 ∷
   rw 20 q5 ∷
   rw 21 q6 ∷
   rw 22 q9 ∷
   rw 23 q5 ∷
   rw 24 q5 ∷
   rw 25 q5 ∷
   rw 26 q5 ∷
   rw 27 q5 ∷
   rw 28 q5 ∷
   rw 29 q5 ∷
   rw 30 q5 ∷
   rw 31 q5 ∷
   re 33 1 (ℓ "乏丹乏") ∷
   rw 32 q7 ∷
   rw 33 q14 ∷
   rw 34 q7 ∷
   re 32 3 (ℓ "丰") ∷
   rw 33 q5 ∷
   rw 34 q5 ∷
   rw 35 q5 ∷
   rw 36 q6 ∷
   rw 37 q5 ∷
   rw 38 q5 ∷
   rw 39 q15 ∷
   rw⁻ 38 q16 ∷
   rw⁻ 39 q17 ∷
   rw⁻ 40 q16 ∷
   rw⁻ 37 q16 ∷
   rw⁻ 38 q17 ∷
   rw⁻ 39 q16 ∷
   rw⁻ 36 q18 ∷
   rw⁻ 37 q19 ∷
   rw⁻ 38 q18 ∷
   rw⁻ 35 q16 ∷
   rw⁻ 36 q17 ∷
   rw⁻ 37 q16 ∷
   rw⁻ 34 q16 ∷
   rw⁻ 35 q17 ∷
   rw⁻ 36 q16 ∷
   rw⁻ 33 q16 ∷
   rw⁻ 34 q17 ∷
   rw⁻ 35 q16 ∷
   rw 36 q20 ∷
   rw 35 q21 ∷
   rw 34 q22 ∷
   rw 33 q21 ∷
   re 32 1 (ℓ "乏个乏") ∷
   rw 34 q23 ∷
   rw 33 q24 ∷
   rw⁻ 32 q21 ∷
   rw⁻ 33 q22 ∷
   rw⁻ 34 q21 ∷
   rw 37 q20 ∷
   re 35 3 (ℓ "丰") ∷
   rw 36 q23 ∷
   rw⁻ 31 q16 ∷
   rw⁻ 32 q17 ∷
   rw⁻ 33 q16 ∷
   rw⁻ 30 q16 ∷
   rw⁻ 31 q17 ∷
   rw⁻ 32 q16 ∷
   rw⁻ 29 q16 ∷
   rw⁻ 30 q17 ∷
   rw⁻ 31 q16 ∷
   rw⁻ 28 q16 ∷
   rw⁻ 29 q17 ∷
   rw⁻ 30 q16 ∷
   rw⁻ 27 q16 ∷
   rw⁻ 28 q17 ∷
   rw⁻ 29 q16 ∷
   rw⁻ 26 q16 ∷
   rw⁻ 27 q17 ∷
   rw⁻ 28 q16 ∷
   rw⁻ 25 q16 ∷
   rw⁻ 26 q17 ∷
   rw⁻ 27 q16 ∷
   rw⁻ 24 q16 ∷
   rw⁻ 25 q17 ∷
   rw⁻ 26 q16 ∷
   rw⁻ 23 q16 ∷
   rw⁻ 24 q17 ∷
   rw⁻ 25 q16 ∷
   rw⁻ 22 q25 ∷
   rw⁻ 23 q26 ∷
   rw⁻ 24 q25 ∷
   rw⁻ 21 q18 ∷
   rw⁻ 22 q19 ∷
   rw⁻ 23 q18 ∷
   rw⁻ 20 q16 ∷
   rw⁻ 21 q17 ∷
   rw⁻ 22 q16 ∷
   rw⁻ 19 q16 ∷
   rw⁻ 20 q17 ∷
   rw⁻ 21 q16 ∷
   rw⁻ 18 q16 ∷
   rw⁻ 19 q17 ∷
   rw⁻ 20 q16 ∷
   rw⁻ 17 q16 ∷
   rw⁻ 18 q17 ∷
   rw⁻ 19 q16 ∷
   rw⁻ 16 q16 ∷
   rw⁻ 17 q17 ∷
   rw⁻ 18 q16 ∷
   rw⁻ 15 q16 ∷
   rw⁻ 16 q17 ∷
   rw⁻ 17 q16 ∷
   rw 18 q20 ∷
   rw 17 q21 ∷
   rw 16 q22 ∷
   rw 15 q21 ∷
   re 14 1 (ℓ "乏个乏") ∷
   rw 16 q23 ∷
   rw 15 q24 ∷
   rw⁻ 14 q21 ∷
   rw⁻ 15 q22 ∷
   rw⁻ 16 q21 ∷
   rw 19 q20 ∷
   re 17 3 (ℓ "丰") ∷
   rw 18 q23 ∷
   rw 8 q27 ∷
   rw 36 q28 ∷
   re 35 1 (ℓ "乏丼丣丼乏") ∷
   rw 41 q20 ∷
   re 39 3 (ℓ "乁") ∷
   rw 38 q29 ∷
   rw 37 q30 ∷
   rw 36 q31 ∷
   re 36 1 (ℓ "乏为乏") ∷
   rw 35 q23 ∷
   re 36 5 (ℓ "丰") ∷
   rw 38 q20 ∷
   rw 37 q32 ∷
   re 36 1 (ℓ "乏个乏") ∷
   rw 38 q23 ∷
   rw 37 q33 ∷
   rw⁻ 36 q32 ∷
   rw 39 q20 ∷
   re 37 3 (ℓ "丰") ∷
   rw 38 q23 ∷
   re 37 1 (ℓ "乏丼丣丼乏") ∷
   rw 43 q20 ∷
   re 41 3 (ℓ "乁") ∷
   rw 40 q29 ∷
   rw 39 q30 ∷
   rw 38 q31 ∷
   re 38 1 (ℓ "乏为乏") ∷
   rw 37 q23 ∷
   re 38 5 (ℓ "丰") ∷
   rw 40 q20 ∷
   rw 39 q32 ∷
   re 38 1 (ℓ "乏个乏") ∷
   rw 40 q23 ∷
   rw 39 q33 ∷
   rw⁻ 38 q32 ∷
   rw 41 q20 ∷
   re 39 3 (ℓ "丰") ∷
   rw 40 q23 ∷
   re 39 1 (ℓ "乏丼丣丼乏") ∷
   rw 45 q20 ∷
   re 43 3 (ℓ "丽") ∷
   rw 42 q34 ∷
   rw 41 q17 ∷
   rw 40 q35 ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 39 q23 ∷
   re 40 5 (ℓ "丰") ∷
   re 40 1 (ℓ "乏丼丣丼乏") ∷
   rw 46 q20 ∷
   re 44 3 (ℓ "丽") ∷
   rw 43 q34 ∷
   rw 42 q17 ∷
   rw 41 q35 ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q23 ∷
   re 41 5 (ℓ "丰") ∷
   re 41 1 (ℓ "乏丼丣丼乏") ∷
   rw 47 q20 ∷
   re 45 3 (ℓ "丽") ∷
   rw 44 q34 ∷
   rw 43 q17 ∷
   rw 42 q35 ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q23 ∷
   re 42 5 (ℓ "丰") ∷
   re 42 1 (ℓ "乏丼丣丼乏") ∷
   rw 48 q20 ∷
   re 46 3 (ℓ "乁") ∷
   rw 45 q29 ∷
   rw 44 q30 ∷
   rw 43 q31 ∷
   re 43 1 (ℓ "乏为乏") ∷
   rw 42 q23 ∷
   re 43 5 (ℓ "丰") ∷
   rw 45 q20 ∷
   rw 44 q32 ∷
   re 43 1 (ℓ "乏个乏") ∷
   rw 45 q23 ∷
   rw 44 q33 ∷
   rw⁻ 43 q32 ∷
   rw 46 q20 ∷
   re 44 3 (ℓ "丰") ∷
   rw 45 q23 ∷
   re 44 1 (ℓ "乏丼丣丼乏") ∷
   rw 50 q20 ∷
   re 48 3 (ℓ "丽") ∷
   rw 47 q34 ∷
   rw 46 q17 ∷
   rw 45 q35 ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 44 q23 ∷
   re 45 5 (ℓ "丰") ∷
   re 45 1 (ℓ "乏丼丣丼乏") ∷
   rw 51 q20 ∷
   re 49 3 (ℓ "丽") ∷
   rw 48 q34 ∷
   rw 47 q17 ∷
   rw 46 q35 ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q23 ∷
   re 46 5 (ℓ "丰") ∷
   re 46 1 (ℓ "乏丼丣丼乏") ∷
   rw 52 q20 ∷
   re 50 3 (ℓ "丽") ∷
   rw 49 q34 ∷
   rw 48 q17 ∷
   rw 47 q35 ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q23 ∷
   re 47 5 (ℓ "丰") ∷
   re 47 1 (ℓ "乏丼丣丼乏") ∷
   rw 53 q20 ∷
   re 51 3 (ℓ "丽") ∷
   rw 50 q34 ∷
   rw 49 q17 ∷
   rw 48 q35 ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q23 ∷
   re 48 5 (ℓ "丰") ∷
   re 48 1 (ℓ "乏丼丣丼乏") ∷
   rw 54 q20 ∷
   re 52 3 (ℓ "丽") ∷
   rw 51 q34 ∷
   rw 50 q17 ∷
   rw 49 q35 ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 48 q23 ∷
   re 49 5 (ℓ "丰") ∷
   re 49 1 (ℓ "乏丼丣丼乏") ∷
   rw 55 q20 ∷
   re 53 3 (ℓ "丽") ∷
   rw 52 q34 ∷
   rw 51 q17 ∷
   rw 50 q35 ∷
   re 50 1 (ℓ "乏丶乏") ∷
   rw 49 q23 ∷
   re 50 5 (ℓ "丰") ∷
   rw 18 q36 ∷
   re 17 1 (ℓ "乏丼丣丼乏") ∷
   rw 23 q20 ∷
   re 21 3 (ℓ "乁") ∷
   rw 20 q29 ∷
   rw 19 q30 ∷
   rw 18 q31 ∷
   re 18 1 (ℓ "乏为乏") ∷
   rw 17 q23 ∷
   re 18 5 (ℓ "丰") ∷
   rw 20 q20 ∷
   rw 19 q32 ∷
   re 18 1 (ℓ "乏个乏") ∷
   rw 20 q23 ∷
   rw 19 q33 ∷
   rw⁻ 18 q32 ∷
   rw 21 q20 ∷
   re 19 3 (ℓ "丰") ∷
   rw 20 q23 ∷
   re 19 1 (ℓ "乏丼丣丼乏") ∷
   rw 25 q20 ∷
   re 23 3 (ℓ "乁") ∷
   rw 22 q29 ∷
   rw 21 q30 ∷
   rw 20 q31 ∷
   re 20 1 (ℓ "乏为乏") ∷
   rw 19 q23 ∷
   re 20 5 (ℓ "丰") ∷
   rw 22 q20 ∷
   rw 21 q32 ∷
   re 20 1 (ℓ "乏个乏") ∷
   rw 22 q23 ∷
   rw 21 q33 ∷
   rw⁻ 20 q32 ∷
   rw 23 q20 ∷
   re 21 3 (ℓ "丰") ∷
   rw 22 q23 ∷
   re 21 1 (ℓ "乏丼丣丼乏") ∷
   rw 27 q20 ∷
   re 25 3 (ℓ "丽") ∷
   rw 24 q34 ∷
   rw 23 q17 ∷
   rw 22 q35 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q23 ∷
   re 22 5 (ℓ "丰") ∷
   re 22 1 (ℓ "乏丼丣丼乏") ∷
   rw 28 q20 ∷
   re 26 3 (ℓ "丽") ∷
   rw 25 q34 ∷
   rw 24 q17 ∷
   rw 23 q35 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q23 ∷
   re 23 5 (ℓ "丰") ∷
   re 23 1 (ℓ "乏丼丣丼乏") ∷
   rw 29 q20 ∷
   re 27 3 (ℓ "丽") ∷
   rw 26 q34 ∷
   rw 25 q17 ∷
   rw 24 q35 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q23 ∷
   re 24 5 (ℓ "丰") ∷
   re 24 1 (ℓ "乏丼丣丼乏") ∷
   rw 30 q20 ∷
   re 28 3 (ℓ "乁") ∷
   rw 27 q29 ∷
   rw 26 q30 ∷
   rw 25 q31 ∷
   re 25 1 (ℓ "乏为乏") ∷
   rw 24 q23 ∷
   re 25 5 (ℓ "丰") ∷
   rw 27 q20 ∷
   rw 26 q32 ∷
   re 25 1 (ℓ "乏个乏") ∷
   rw 27 q23 ∷
   rw 26 q33 ∷
   rw⁻ 25 q32 ∷
   rw 28 q20 ∷
   re 26 3 (ℓ "丰") ∷
   rw 27 q23 ∷
   re 26 1 (ℓ "乏丼丣丼乏") ∷
   rw 32 q20 ∷
   re 30 3 (ℓ "丽") ∷
   rw 29 q34 ∷
   rw 28 q17 ∷
   rw 27 q35 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q23 ∷
   re 27 5 (ℓ "丰") ∷
   re 27 1 (ℓ "乏丼丣丼乏") ∷
   rw 33 q20 ∷
   re 31 3 (ℓ "丽") ∷
   rw 30 q34 ∷
   rw 29 q17 ∷
   rw 28 q35 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q23 ∷
   re 28 5 (ℓ "丰") ∷
   re 28 1 (ℓ "乏丼丣丼乏") ∷
   rw 34 q20 ∷
   re 32 3 (ℓ "丽") ∷
   rw 31 q34 ∷
   rw 30 q17 ∷
   rw 29 q35 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q23 ∷
   re 29 5 (ℓ "丰") ∷
   re 29 1 (ℓ "乏丼丣丼乏") ∷
   rw 35 q20 ∷
   re 33 3 (ℓ "丽") ∷
   rw 32 q34 ∷
   rw 31 q17 ∷
   rw 30 q35 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q23 ∷
   re 30 5 (ℓ "丰") ∷
   re 30 1 (ℓ "乏丼丣丼乏") ∷
   rw 36 q20 ∷
   re 34 3 (ℓ "丽") ∷
   rw 33 q34 ∷
   rw 32 q17 ∷
   rw 31 q35 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q23 ∷
   re 31 5 (ℓ "丰") ∷
   re 31 1 (ℓ "乏丼丣丼乏") ∷
   rw 37 q20 ∷
   re 35 3 (ℓ "丽") ∷
   rw 34 q34 ∷
   rw 33 q17 ∷
   rw 32 q35 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q23 ∷
   re 32 5 (ℓ "丰") ∷
   rw 11 q37 ∷
   rw⁻ 56 q16 ∷
   rw⁻ 57 q17 ∷
   rw⁻ 58 q16 ∷
   rw⁻ 55 q16 ∷
   rw⁻ 56 q17 ∷
   rw⁻ 57 q16 ∷
   rw⁻ 54 q18 ∷
   rw⁻ 55 q19 ∷
   rw⁻ 56 q18 ∷
   rw⁻ 53 q16 ∷
   rw⁻ 54 q17 ∷
   rw⁻ 55 q16 ∷
   rw⁻ 52 q16 ∷
   rw⁻ 53 q17 ∷
   rw⁻ 54 q16 ∷
   rw⁻ 51 q16 ∷
   rw⁻ 52 q17 ∷
   rw⁻ 53 q16 ∷
   rw 54 q20 ∷
   rw 53 q21 ∷
   rw 52 q22 ∷
   rw 51 q21 ∷
   re 50 1 (ℓ "乏个乏") ∷
   rw 52 q23 ∷
   rw 51 q24 ∷
   rw⁻ 50 q21 ∷
   rw⁻ 51 q22 ∷
   rw⁻ 52 q21 ∷
   rw 55 q20 ∷
   re 53 3 (ℓ "丰") ∷
   rw 54 q23 ∷
   rw⁻ 49 q16 ∷
   rw⁻ 50 q17 ∷
   rw⁻ 51 q16 ∷
   rw⁻ 48 q16 ∷
   rw⁻ 49 q17 ∷
   rw⁻ 50 q16 ∷
   rw⁻ 47 q16 ∷
   rw⁻ 48 q17 ∷
   rw⁻ 49 q16 ∷
   rw⁻ 46 q16 ∷
   rw⁻ 47 q17 ∷
   rw⁻ 48 q16 ∷
   rw⁻ 45 q16 ∷
   rw⁻ 46 q17 ∷
   rw⁻ 47 q16 ∷
   rw⁻ 44 q16 ∷
   rw⁻ 45 q17 ∷
   rw⁻ 46 q16 ∷
   rw⁻ 43 q16 ∷
   rw⁻ 44 q17 ∷
   rw⁻ 45 q16 ∷
   rw⁻ 42 q16 ∷
   rw⁻ 43 q17 ∷
   rw⁻ 44 q16 ∷
   rw⁻ 41 q16 ∷
   rw⁻ 42 q17 ∷
   rw⁻ 43 q16 ∷
   rw⁻ 40 q25 ∷
   rw⁻ 41 q26 ∷
   rw⁻ 42 q25 ∷
   rw⁻ 39 q18 ∷
   rw⁻ 40 q19 ∷
   rw⁻ 41 q18 ∷
   rw⁻ 38 q16 ∷
   rw⁻ 39 q17 ∷
   rw⁻ 40 q16 ∷
   rw⁻ 37 q16 ∷
   rw⁻ 38 q17 ∷
   rw⁻ 39 q16 ∷
   rw⁻ 36 q16 ∷
   rw⁻ 37 q17 ∷
   rw⁻ 38 q16 ∷
   rw⁻ 35 q16 ∷
   rw⁻ 36 q17 ∷
   rw⁻ 37 q16 ∷
   rw⁻ 34 q16 ∷
   rw⁻ 35 q17 ∷
   rw⁻ 36 q16 ∷
   rw⁻ 33 q16 ∷
   rw⁻ 34 q17 ∷
   rw⁻ 35 q16 ∷
   rw 36 q20 ∷
   rw 35 q21 ∷
   rw 34 q22 ∷
   rw 33 q21 ∷
   re 32 1 (ℓ "乏个乏") ∷
   rw 34 q23 ∷
   rw 33 q24 ∷
   rw⁻ 32 q21 ∷
   rw⁻ 33 q22 ∷
   rw⁻ 34 q21 ∷
   rw 37 q20 ∷
   re 35 3 (ℓ "丰") ∷
   rw 36 q23 ∷
   rw 26 q27 ∷
   rw 54 q38 ∷
   re 53 1 (ℓ "乏丼丣丼乏") ∷
   rw 59 q20 ∷
   re 57 3 (ℓ "丽") ∷
   rw 56 q34 ∷
   rw 55 q17 ∷
   rw 54 q35 ∷
   re 54 1 (ℓ "乏丶乏") ∷
   rw 53 q23 ∷
   re 54 5 (ℓ "丰") ∷
   re 54 1 (ℓ "乏丼丣丼乏") ∷
   rw 60 q20 ∷
   re 58 3 (ℓ "丽") ∷
   rw 57 q34 ∷
   rw 56 q17 ∷
   rw 55 q35 ∷
   re 55 1 (ℓ "乏丶乏") ∷
   rw 54 q23 ∷
   re 55 5 (ℓ "丰") ∷
   re 55 1 (ℓ "乏丼丣丼乏") ∷
   rw 61 q20 ∷
   re 59 3 (ℓ "乁") ∷
   rw 58 q29 ∷
   rw 57 q30 ∷
   rw 56 q31 ∷
   re 56 1 (ℓ "乏为乏") ∷
   rw 55 q23 ∷
   re 56 5 (ℓ "丰") ∷
   re 56 1 (ℓ "乏丼丣丼乏") ∷
   rw 62 q20 ∷
   re 60 3 (ℓ "丽") ∷
   rw 59 q34 ∷
   rw 58 q17 ∷
   rw 57 q35 ∷
   re 57 1 (ℓ "乏丶乏") ∷
   rw 56 q23 ∷
   re 57 5 (ℓ "丰") ∷
   re 57 1 (ℓ "乏丼丣丼乏") ∷
   rw 63 q20 ∷
   re 61 3 (ℓ "乁") ∷
   rw 60 q29 ∷
   rw 59 q30 ∷
   rw 58 q31 ∷
   re 58 1 (ℓ "乏为乏") ∷
   rw 57 q23 ∷
   re 58 5 (ℓ "丰") ∷
   re 58 1 (ℓ "乏丼丣丼乏") ∷
   rw 64 q20 ∷
   re 62 3 (ℓ "乁") ∷
   rw 61 q29 ∷
   rw 60 q30 ∷
   rw 59 q31 ∷
   re 59 1 (ℓ "乏为乏") ∷
   rw 58 q23 ∷
   re 59 5 (ℓ "丰") ∷
   rw 36 q39 ∷
   re 35 1 (ℓ "乏丼丣丼乏") ∷
   rw 41 q20 ∷
   re 39 3 (ℓ "丽") ∷
   rw 38 q34 ∷
   rw 37 q17 ∷
   rw 36 q35 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q23 ∷
   re 36 5 (ℓ "丰") ∷
   re 36 1 (ℓ "乏丼丣丼乏") ∷
   rw 42 q20 ∷
   re 40 3 (ℓ "丽") ∷
   rw 39 q34 ∷
   rw 38 q17 ∷
   rw 37 q35 ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q23 ∷
   re 37 5 (ℓ "丰") ∷
   re 37 1 (ℓ "乏丼丣丼乏") ∷
   rw 43 q20 ∷
   re 41 3 (ℓ "乁") ∷
   rw 40 q29 ∷
   rw 39 q30 ∷
   rw 38 q31 ∷
   re 38 1 (ℓ "乏为乏") ∷
   rw 37 q23 ∷
   re 38 5 (ℓ "丰") ∷
   re 38 1 (ℓ "乏丼丣丼乏") ∷
   rw 44 q20 ∷
   re 42 3 (ℓ "丽") ∷
   rw 41 q34 ∷
   rw 40 q17 ∷
   rw 39 q35 ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q23 ∷
   re 39 5 (ℓ "丰") ∷
   re 39 1 (ℓ "乏丼丣丼乏") ∷
   rw 45 q20 ∷
   re 43 3 (ℓ "乁") ∷
   rw 42 q29 ∷
   rw 41 q30 ∷
   rw 40 q31 ∷
   re 40 1 (ℓ "乏为乏") ∷
   rw 39 q23 ∷
   re 40 5 (ℓ "丰") ∷
   re 40 1 (ℓ "乏丼丣丼乏") ∷
   rw 46 q20 ∷
   re 44 3 (ℓ "乁") ∷
   rw 43 q29 ∷
   rw 42 q30 ∷
   rw 41 q31 ∷
   re 41 1 (ℓ "乏为乏") ∷
   rw 40 q23 ∷
   re 41 5 (ℓ "丰") ∷
   rw 29 q40 ∷ []) Eq.refl

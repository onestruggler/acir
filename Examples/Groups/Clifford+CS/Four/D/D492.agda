{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D492 (W : Ws) where

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
  q1 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q2 : Eqn
  q2 = wE 25 W
  q3 : Eqn
  q3 = wE 275 W
  q4 : Eqn
  q4 = eqn (ℓ "並东") (ℓ "东並") (low-comm (Swap) ((K ↑)))
  q5 : Eqn
  q5 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q6 : Eqn
  q6 = wE 30 W
  q7 : Eqn
  q7 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q8 : Eqn
  q8 = wE 27 W
  q9 : Eqn
  q9 = wE 122 W
  q10 : Eqn
  q10 = wE 5 W
  q11 : Eqn
  q11 = wE 24 W
  q12 : Eqn
  q12 = wE 124 W
  q13 : Eqn
  q13 = wE 337 W
  q14 : Eqn
  q14 = wE 219 W
  q15 : Eqn
  q15 = wE 327 W
  q16 : Eqn
  q16 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q17 : Eqn
  q17 = wE 31 W
  q18 : Eqn
  q18 = wE 12 W
  q19 : Eqn
  q19 = wE 14 W
  q20 : Eqn
  q20 = wE 355 W
  q21 : Eqn
  q21 = wE 343 W
  q22 : Eqn
  q22 = wE 18 W
  q23 : Eqn
  q23 = eqn (ℓ "丼东") (ℓ "东丼") (low₃-comm ((Swap ↑)) (K))
  q24 : Eqn
  q24 = wE 49 W
  q25 : Eqn
  q25 = wE 51 W
  q26 : Eqn
  q26 = wE 22 W
  q27 : Eqn
  q27 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q28 : Eqn
  q28 = wE 23 W
  q29 : Eqn
  q29 = eqn (ℓ "一丼") (ℓ "丼一") (low₁-comm (iI) (Swap))
  q30 : Eqn
  q30 = wE 1 W
  q31 : Eqn
  q31 = wE 336 W
  q32 : Eqn
  q32 = wE 3 W
  q33 : Eqn
  q33 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q34 : Eqn
  q34 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q35 : Eqn
  q35 = wE 368 W
  q36 : Eqn
  q36 = wE 20 W
  q37 : Eqn
  q37 = wE 359 W
  q38 : Eqn
  q38 = eqn (ℓ "丼业") (ℓ "业丼") (low₃-comm ((Swap ↑)) (S))
  q39 : Eqn
  q39 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q40 : Eqn
  q40 = wE 335 W
  q41 : Eqn
  q41 = wE 71 W
  q42 : Eqn
  q42 = wE 382 W
  q43 : Eqn
  q43 = wE 372 W

-- AXIOM LF @3012 part1: 500 steps
lem-AXIOM-LF-at3012-part1 : ⟪ (ℓ "乏丼丠丠两丠两两个乇且乇且丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乇乇乧丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽乏丶乏並中乑中中乨丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑並丼乏") ⟫ʷ ≈ ⟪ (ℓ "中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁乣中中中丱中中个义义义义义义乍且义义义义义义义义义个义义义乍义义乏东丽丣乏丷乏乏丣丧世一乏丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗乏") ⟫ʷ
lem-AXIOM-LF-at3012-part1 = derive (ℓ "乏丼丠丠两丠两两个乇且乇且丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乇乇乧丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽乏丶乏並中乑中中乨丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑並丼乏") (ℓ "中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁乣中中中丱中中个义义义义义义乍且义义义义义义义义义个义义义乍义义乏东丽丣乏丷乏乏丣丧世一乏丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗乏")
  (re 58 3 (ℓ "丽") ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 59 q1 ∷
   rw 60 q2 ∷
   rw 61 q1 ∷
   re 59 3 (ℓ "丽") ∷
   re 61 1 (ℓ "乏乄乏") ∷
   rw 60 q1 ∷
   rw 61 q3 ∷
   rw 62 q1 ∷
   re 60 3 (ℓ "乔") ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 61 q1 ∷
   rw 62 q2 ∷
   rw 63 q1 ∷
   re 61 3 (ℓ "丽") ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 62 q1 ∷
   rw 63 q2 ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "丽") ∷
   re 64 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 63 q4 ∷
   rw 64 q5 ∷
   rw 65 q6 ∷
   rw 66 q7 ∷
   rw 67 q6 ∷
   re 69 1 (ℓ "乏丶乏") ∷
   rw 68 q1 ∷
   rw 69 q8 ∷
   rw 70 q1 ∷
   re 68 3 (ℓ "中") ∷
   rw 69 q4 ∷
   rw 70 q9 ∷
   rw 63 q10 ∷
   rw 64 q4 ∷
   rw 65 q5 ∷
   rw 66 q11 ∷
   rw 67 q7 ∷
   rw 68 q11 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw 69 q1 ∷
   rw 70 q2 ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "丽") ∷
   rw 70 q4 ∷
   rw 71 q12 ∷
   rw 64 q13 ∷
   re 64 8 (ℓ "乨") ∷
   re 63 3 (ℓ "乧") ∷
   rw 64 q14 ∷
   rw 65 q14 ∷
   rw 66 q15 ∷
   rw 67 q14 ∷
   rw 68 q15 ∷
   rw 69 q15 ∷
   re 71 1 (ℓ "乏丹乏") ∷
   rw 70 q1 ∷
   rw 71 q6 ∷
   rw 72 q1 ∷
   re 70 3 (ℓ "丰") ∷
   re 72 1 (ℓ "乏乄乏") ∷
   rw 71 q1 ∷
   rw 72 q3 ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "乔") ∷
   rw 72 q16 ∷
   re 74 1 (ℓ "乏乄乏") ∷
   rw 73 q1 ∷
   rw 74 q3 ∷
   rw 75 q1 ∷
   re 73 3 (ℓ "乔") ∷
   rw 74 q16 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 75 q1 ∷
   rw 76 q2 ∷
   rw 77 q1 ∷
   re 75 3 (ℓ "丽") ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 76 q1 ∷
   rw 77 q2 ∷
   rw 78 q1 ∷
   re 76 3 (ℓ "丽") ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw 77 q1 ∷
   rw 78 q2 ∷
   rw 79 q1 ∷
   re 77 3 (ℓ "丽") ∷
   re 79 1 (ℓ "乏乄乏") ∷
   rw 78 q1 ∷
   rw 79 q3 ∷
   rw 80 q1 ∷
   re 78 3 (ℓ "乔") ∷
   rw 79 q16 ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw 80 q1 ∷
   rw 81 q2 ∷
   rw 82 q1 ∷
   re 80 3 (ℓ "丽") ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 81 q1 ∷
   rw 82 q2 ∷
   rw 83 q1 ∷
   re 81 3 (ℓ "丽") ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw 82 q1 ∷
   rw 83 q2 ∷
   rw 84 q1 ∷
   re 82 3 (ℓ "丽") ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw 83 q1 ∷
   rw 84 q2 ∷
   rw 85 q1 ∷
   re 83 3 (ℓ "丽") ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw 84 q1 ∷
   rw 85 q2 ∷
   rw 86 q1 ∷
   re 84 3 (ℓ "丽") ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw 85 q1 ∷
   rw 86 q2 ∷
   rw 87 q1 ∷
   re 85 3 (ℓ "丽") ∷
   re 87 1 (ℓ "乏丹乏") ∷
   rw 86 q1 ∷
   rw 87 q6 ∷
   rw 88 q1 ∷
   re 86 3 (ℓ "丰") ∷
   re 88 1 (ℓ "乏丧乏") ∷
   rw 87 q1 ∷
   rw 88 q2 ∷
   rw 89 q1 ∷
   re 87 3 (ℓ "丽") ∷
   re 89 1 (ℓ "乏丧乏") ∷
   rw 88 q1 ∷
   rw 89 q2 ∷
   rw 90 q1 ∷
   re 88 3 (ℓ "丽") ∷
   re 90 1 (ℓ "乏乄乏") ∷
   rw 89 q1 ∷
   rw 90 q3 ∷
   rw 91 q1 ∷
   re 89 3 (ℓ "乔") ∷
   re 91 1 (ℓ "乏丧乏") ∷
   rw 90 q1 ∷
   rw 91 q2 ∷
   rw 92 q1 ∷
   re 90 3 (ℓ "丽") ∷
   re 92 1 (ℓ "乏乄乏") ∷
   rw 91 q1 ∷
   rw 92 q3 ∷
   rw 93 q1 ∷
   re 91 3 (ℓ "乔") ∷
   re 93 1 (ℓ "乏乄乏") ∷
   rw 92 q1 ∷
   rw 93 q3 ∷
   rw 94 q1 ∷
   re 92 3 (ℓ "乔") ∷
   rw 93 q17 ∷
   rw 3 q18 ∷
   re 1 3 (ℓ "丧") ∷
   rw 4 q18 ∷
   re 2 3 (ℓ "丧") ∷
   rw 5 q18 ∷
   re 3 3 (ℓ "丫") ∷
   rw 6 q18 ∷
   re 4 3 (ℓ "丧") ∷
   rw 7 q18 ∷
   re 5 3 (ℓ "丫") ∷
   rw 8 q18 ∷
   re 6 3 (ℓ "丫") ∷
   re 8 1 (ℓ "丼丣丼") ∷
   rw 7 q19 ∷
   rw 8 q20 ∷
   rw 9 q21 ∷
   rw 10 q20 ∷
   rw 11 q21 ∷
   rw 12 q22 ∷
   rw 13 q22 ∷
   rw 14 q22 ∷
   rw 15 q20 ∷
   rw 16 q21 ∷
   rw 17 q22 ∷
   rw 18 q22 ∷
   rw 19 q22 ∷
   rw 20 q22 ∷
   rw 21 q22 ∷
   rw 22 q22 ∷
   re 24 1 (ℓ "丼丣丼") ∷
   rw 23 q19 ∷
   rw 24 q22 ∷
   rw 25 q22 ∷
   rw 26 q20 ∷
   rw 27 q22 ∷
   rw 28 q20 ∷
   rw 29 q20 ∷
   re 31 1 (ℓ "並乨並") ∷
   re 32 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 31 q4 ∷
   rw 32 q5 ∷
   rw 33 q6 ∷
   rw 34 q7 ∷
   rw 35 q6 ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q1 ∷
   rw 37 q8 ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "中") ∷
   rw 37 q4 ∷
   rw 38 q9 ∷
   rw 39 q17 ∷
   rw 30 q23 ∷
   rw 31 q24 ∷
   re 33 1 (ℓ "丼丣丼") ∷
   rw 32 q19 ∷
   rw 33 q25 ∷
   re 35 1 (ℓ "丼丣丼") ∷
   rw 34 q19 ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q26 ∷
   rw⁻ 37 q27 ∷
   rw 38 q28 ∷
   re 35 5 (ℓ "中") ∷
   rw 36 q23 ∷
   rw⁻ 37 q29 ∷
   rw 30 q30 ∷
   rw 31 q31 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q32 ∷
   rw⁻ 33 q33 ∷
   re 35 1 (ℓ "乏丷乏") ∷
   rw 34 q32 ∷
   rw⁻ 35 q33 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 36 q32 ∷
   rw 37 q31 ∷
   rw⁻ 38 q34 ∷
   rw 31 q35 ∷
   re 31 8 (ℓ "乣") ∷
   re 30 3 (ℓ "书") ∷
   rw 33 q18 ∷
   re 31 3 (ℓ "丧") ∷
   rw 34 q18 ∷
   re 32 3 (ℓ "丧") ∷
   rw 35 q18 ∷
   re 33 3 (ℓ "丧") ∷
   rw 36 q18 ∷
   re 34 3 (ℓ "丫") ∷
   rw 37 q18 ∷
   re 35 3 (ℓ "丧") ∷
   rw 38 q18 ∷
   re 36 3 (ℓ "丧") ∷
   re 38 1 (ℓ "乏丼丣丼乏") ∷
   rw 37 q26 ∷
   rw⁻ 39 q33 ∷
   rw 40 q28 ∷
   re 37 5 (ℓ "丰") ∷
   rw 38 q36 ∷
   rw 39 q36 ∷
   rw 40 q36 ∷
   rw 41 q36 ∷
   rw 42 q36 ∷
   rw 43 q36 ∷
   rw 44 q37 ∷
   rw 45 q38 ∷
   rw 46 q36 ∷
   rw 47 q36 ∷
   rw 48 q36 ∷
   rw 49 q36 ∷
   rw 50 q36 ∷
   rw 51 q36 ∷
   rw 52 q36 ∷
   rw 53 q36 ∷
   rw 54 q36 ∷
   re 56 1 (ℓ "乏丼丣丼乏") ∷
   rw 55 q26 ∷
   rw⁻ 57 q33 ∷
   rw 58 q28 ∷
   re 55 5 (ℓ "丰") ∷
   rw 56 q36 ∷
   rw 57 q36 ∷
   rw 58 q36 ∷
   rw 59 q37 ∷
   rw 60 q36 ∷
   rw 61 q36 ∷
   re 63 1 (ℓ "並乨並") ∷
   re 64 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 63 q4 ∷
   rw 64 q5 ∷
   rw 65 q6 ∷
   rw 66 q7 ∷
   rw 67 q6 ∷
   re 69 1 (ℓ "乏丶乏") ∷
   rw 68 q1 ∷
   rw 69 q8 ∷
   rw 70 q1 ∷
   re 68 3 (ℓ "中") ∷
   rw 69 q4 ∷
   rw 70 q9 ∷
   rw 71 q17 ∷
   rw 62 q23 ∷
   rw 63 q24 ∷
   re 65 1 (ℓ "丼丣丼") ∷
   rw 64 q19 ∷
   rw 65 q25 ∷
   re 67 1 (ℓ "丼丣丼") ∷
   rw 66 q19 ∷
   re 68 1 (ℓ "乏丼丠丼乏") ∷
   rw 67 q26 ∷
   rw⁻ 69 q27 ∷
   rw 70 q28 ∷
   re 67 5 (ℓ "中") ∷
   rw 68 q23 ∷
   rw⁻ 69 q29 ∷
   rw 62 q30 ∷
   rw 63 q31 ∷
   re 65 1 (ℓ "乏丶乏") ∷
   rw 64 q32 ∷
   rw⁻ 65 q33 ∷
   re 67 1 (ℓ "乏丷乏") ∷
   rw 66 q32 ∷
   rw⁻ 67 q33 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 68 q32 ∷
   rw 69 q31 ∷
   rw⁻ 70 q34 ∷
   rw 63 q35 ∷
   re 63 8 (ℓ "乣") ∷
   re 62 3 (ℓ "书") ∷
   rw 65 q18 ∷
   re 63 3 (ℓ "丧") ∷
   rw 66 q18 ∷
   re 64 3 (ℓ "丧") ∷
   rw 67 q18 ∷
   re 65 3 (ℓ "丫") ∷
   rw 68 q18 ∷
   re 66 3 (ℓ "丧") ∷
   rw 69 q18 ∷
   re 67 3 (ℓ "丫") ∷
   rw 70 q18 ∷
   re 68 3 (ℓ "丫") ∷
   re 70 1 (ℓ "乏丼丣丼乏") ∷
   rw 69 q26 ∷
   rw⁻ 71 q33 ∷
   rw 72 q28 ∷
   re 69 5 (ℓ "丰") ∷
   rw 70 q37 ∷
   rw 71 q38 ∷
   rw 72 q37 ∷
   rw 73 q38 ∷
   rw 74 q36 ∷
   rw 75 q36 ∷
   rw 76 q36 ∷
   rw 77 q37 ∷
   rw 78 q38 ∷
   rw 79 q36 ∷
   rw 80 q36 ∷
   rw 81 q36 ∷
   rw 82 q36 ∷
   rw 83 q36 ∷
   rw 84 q36 ∷
   re 86 1 (ℓ "乏丼丣丼乏") ∷
   rw 85 q26 ∷
   rw⁻ 87 q33 ∷
   rw 88 q28 ∷
   re 85 5 (ℓ "丰") ∷
   rw 86 q36 ∷
   rw 87 q36 ∷
   rw 88 q37 ∷
   rw 89 q36 ∷
   rw 90 q37 ∷
   rw 91 q37 ∷
   rw 92 q19 ∷
   rw 2 q30 ∷
   re 0 3 (ℓ "中") ∷
   rw 3 q30 ∷
   re 1 3 (ℓ "中") ∷
   rw 4 q30 ∷
   re 2 3 (ℓ "丱") ∷
   rw 5 q30 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q30 ∷
   re 4 3 (ℓ "丱") ∷
   rw 7 q30 ∷
   re 5 3 (ℓ "丱") ∷
   rw⁻ 6 q33 ∷
   rw 9 q30 ∷
   re 7 3 (ℓ "乁") ∷
   rw⁻ 8 q39 ∷
   rw 11 q30 ∷
   re 9 3 (ℓ "乁") ∷
   rw⁻ 10 q39 ∷
   rw 13 q30 ∷
   re 11 3 (ℓ "丽") ∷
   rw 14 q30 ∷
   re 12 3 (ℓ "丽") ∷
   rw 15 q30 ∷
   re 13 3 (ℓ "丽") ∷
   rw 16 q30 ∷
   re 14 3 (ℓ "乁") ∷
   rw⁻ 15 q39 ∷
   rw 18 q30 ∷
   re 16 3 (ℓ "丽") ∷
   rw 19 q30 ∷
   re 17 3 (ℓ "丽") ∷
   rw 20 q30 ∷
   re 18 3 (ℓ "丽") ∷
   rw 21 q30 ∷
   re 19 3 (ℓ "丽") ∷
   rw 22 q30 ∷
   re 20 3 (ℓ "丽") ∷
   rw 23 q30 ∷
   re 21 3 (ℓ "丽") ∷
   rw⁻ 22 q33 ∷
   rw 25 q30 ∷
   re 23 3 (ℓ "丽") ∷
   rw 26 q30 ∷
   re 24 3 (ℓ "丽") ∷
   rw 27 q30 ∷
   re 25 3 (ℓ "乁") ∷
   rw 28 q30 ∷
   re 26 3 (ℓ "丽") ∷
   rw 29 q30 ∷
   re 27 3 (ℓ "乁") ∷
   rw 30 q30 ∷
   re 28 3 (ℓ "乁") ∷
   re 30 1 (ℓ "乏乣乏") ∷
   re 31 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 30 q40 ∷
   rw 33 q30 ∷
   re 31 3 (ℓ "丽") ∷
   rw⁻ 32 q33 ∷
   rw 35 q30 ∷
   re 33 3 (ℓ "举") ∷
   rw⁻ 34 q33 ∷
   rw 37 q30 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q40 ∷
   rw⁻ 37 q34 ∷
   rw 38 q32 ∷
   rw 29 q31 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q32 ∷
   rw⁻ 31 q33 ∷
   re 33 1 (ℓ "乏丷乏") ∷
   rw 32 q32 ∷
   rw⁻ 33 q33 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 34 q32 ∷
   rw 35 q31 ∷
   rw⁻ 36 q34 ∷
   rw 29 q35 ∷
   re 29 8 (ℓ "乣") ∷
   rw 32 q30 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q30 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q30 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q30 ∷
   re 33 3 (ℓ "丱") ∷
   rw 36 q30 ∷
   re 34 3 (ℓ "中") ∷
   rw 37 q30 ∷
   re 35 3 (ℓ "中") ∷
   re 37 1 (ℓ "乏个乏") ∷
   rw 36 q32 ∷
   rw 37 q41 ∷
   rw 38 q41 ∷
   rw 39 q41 ∷
   rw 40 q41 ∷
   rw 41 q41 ∷
   rw 42 q41 ∷
   rw 43 q42 ∷
   rw 44 q43 ∷
   rw 45 q41 ∷
   rw 46 q41 ∷
   rw 47 q41 ∷
   rw 48 q41 ∷
   rw 49 q41 ∷
   rw 50 q41 ∷
   rw 51 q41 ∷
   rw 52 q41 ∷
   rw 53 q41 ∷
   re 55 1 (ℓ "乏个乏") ∷
   rw 54 q32 ∷
   rw 55 q41 ∷
   rw 56 q41 ∷
   rw 57 q41 ∷
   rw 58 q42 ∷
   rw 59 q41 ∷
   rw 60 q41 ∷
   re 62 1 (ℓ "乏乣乏") ∷
   re 63 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 62 q40 ∷
   rw 65 q30 ∷
   re 63 3 (ℓ "丽") ∷
   rw⁻ 64 q33 ∷
   rw 67 q30 ∷ []) Eq.refl

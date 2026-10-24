{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D025 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

private
  q1 : Eqn
  q1 = wE 474 W

-- pass [CSd13] [Sd3]: 1 steps
lem-pass-CSd13-vs-Sd3 : ⟪ (ℓ "举丛") ⟫ʷ ≈ ⟪ (ℓ "丛举") ⟫ʷ
lem-pass-CSd13-vs-Sd3 = derive (ℓ "举丛") (ℓ "丛举")
  (rw 0 q1 ∷ []) Eq.refl

private
  q2 : Eqn
  q2 = wE 475 W

-- pass [CSd13] [S3]: 1 steps
lem-pass-CSd13-vs-S3 : ⟪ (ℓ "举业") ⟫ʷ ≈ ⟪ (ℓ "业举") ⟫ʷ
lem-pass-CSd13-vs-S3 = derive (ℓ "举业") (ℓ "业举")
  (rw 0 q2 ∷ []) Eq.refl

private
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 476 W
  q5 : Eqn
  q5 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q6 : Eqn
  q6 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q7 : Eqn
  q7 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q8 : Eqn
  q8 = wE 3 W
  q9 : Eqn
  q9 = wE 464 W
  q10 : Eqn
  q10 = eqn (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))
  q11 : Eqn
  q11 = wE 151 W
  q12 : Eqn
  q12 = wE 336 W
  q13 : Eqn
  q13 = wE 71 W
  q14 : Eqn
  q14 = wE 72 W
  q15 : Eqn
  q15 = eqn (ℓ "丁乏") (ℓ "乏丁") (low-comm ((iI ↑)) (Swap))
  q16 : Eqn
  q16 = wE 386 W
  q17 : Eqn
  q17 = wE 372 W

-- AXIOM LF @0132: 322 steps
lem-AXIOM-LF-at0132 : ⟪ (ℓ "丠丠临丠乀中中中乑业中中中中中中乀中中乑中乄中中中业乑中中中中中中乀中中中中中中中中中中中中中中中中中中业业业业乑中中中中中中中中中乀丠丠丠与临丠丠丠丠丠丠且乄") ⟫ʷ ≈ ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑乥丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧乥丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄") ⟫ʷ
lem-AXIOM-LF-at0132 = derive (ℓ "丠丠临丠乀中中中乑业中中中中中中乀中中乑中乄中中中业乑中中中中中中乀中中中中中中中中中中中中中中中中中中业业业业乑中中中中中中中中中乀丠丠丠与临丠丠丠丠丠丠且乄") (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑乥丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧乥丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄")
  (rw 80 q3 ∷
   rw 79 q3 ∷
   re 80 3 (ℓ "乑") ∷
   rw 78 q4 ∷
   rw 77 q5 ∷
   rw 76 q5 ∷
   rw 75 q5 ∷
   rw 74 q5 ∷
   rw 73 q5 ∷
   rw 72 q5 ∷
   rw 71 q6 ∷
   rw 70 q7 ∷
   rw 69 q5 ∷
   rw 68 q5 ∷
   rw 67 q5 ∷
   re 66 1 (ℓ "乏丹乏") ∷
   rw 68 q8 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 67 q8 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 66 q8 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 65 q8 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 64 q8 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 63 q8 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 62 q8 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 61 q8 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q8 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q8 ∷
   re 56 1 (ℓ "乏乄乏") ∷
   rw 58 q8 ∷
   rw 55 q9 ∷
   rw 54 q9 ∷
   rw 53 q9 ∷
   rw 52 q9 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q8 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q8 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q8 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q8 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q8 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q8 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q8 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q8 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q8 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q8 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q8 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q8 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q8 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q8 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q8 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q8 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q8 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q8 ∷
   re 33 1 (ℓ "乏丹乏") ∷
   rw 35 q8 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q8 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q8 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q8 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q8 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q8 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q8 ∷
   re 26 1 (ℓ "乏乄乏") ∷
   rw 28 q8 ∷
   rw 25 q9 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q8 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q8 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q8 ∷
   rw 21 q3 ∷
   re 22 3 (ℓ "乑") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q8 ∷
   re 19 1 (ℓ "乏乄乏") ∷
   rw 21 q8 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q8 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q8 ∷
   re 16 1 (ℓ "乏丹乏") ∷
   rw 18 q8 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q8 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q8 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q8 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q8 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q8 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q8 ∷
   rw 9 q9 ∷
   re 8 1 (ℓ "乏乄乏") ∷
   rw 10 q8 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q8 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q8 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q8 ∷
   re 4 1 (ℓ "乏丹乏") ∷
   rw 6 q8 ∷
   rw 3 q5 ∷
   rw 2 q6 ∷
   rw 1 q5 ∷
   rw 0 q5 ∷
   rw 1 q10 ∷
   rw⁻ 0 q5 ∷
   rw⁻ 1 q5 ∷
   rw⁻ 2 q6 ∷
   rw⁻ 3 q5 ∷
   rw⁻ 4 q6 ∷
   rw⁻ 5 q6 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "乀") ∷
   rw 9 q3 ∷
   re 7 3 (ℓ "乑") ∷
   rw 8 q11 ∷
   rw 11 q3 ∷
   re 9 3 (ℓ "乑") ∷
   rw 10 q11 ∷
   rw 13 q3 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q3 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q3 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q3 ∷
   re 14 3 (ℓ "乑") ∷
   rw 15 q11 ∷
   rw 18 q3 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q3 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q3 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q3 ∷
   re 19 3 (ℓ "中") ∷
   rw 22 q3 ∷
   re 20 3 (ℓ "中") ∷
   rw 23 q3 ∷
   re 21 3 (ℓ "中") ∷
   rw 24 q3 ∷
   re 22 3 (ℓ "乀") ∷
   rw 25 q3 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q3 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q3 ∷
   re 25 3 (ℓ "乑") ∷
   rw 28 q3 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q3 ∷
   re 27 3 (ℓ "乑") ∷
   rw 30 q3 ∷
   re 28 3 (ℓ "乑") ∷
   re 30 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 29 q12 ∷
   rw 30 q13 ∷
   rw 33 q3 ∷
   re 31 3 (ℓ "乀") ∷
   rw 32 q14 ∷
   rw 35 q3 ∷
   re 33 3 (ℓ "乀") ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q8 ∷
   rw 35 q12 ∷
   rw⁻ 36 q15 ∷
   rw 29 q16 ∷
   re 29 8 (ℓ "乥") ∷
   rw⁻ 30 q5 ∷
   rw⁻ 31 q5 ∷
   rw⁻ 32 q5 ∷
   rw⁻ 33 q6 ∷
   rw⁻ 34 q5 ∷
   rw⁻ 35 q5 ∷
   re 37 1 (ℓ "乏丹乏") ∷
   rw 36 q8 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 37 q8 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 38 q8 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 39 q8 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 40 q8 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 41 q8 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 42 q8 ∷
   re 44 1 (ℓ "乏乄乏") ∷
   rw 43 q8 ∷
   rw 44 q17 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 45 q8 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 46 q8 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 47 q8 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 48 q8 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 49 q8 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 50 q8 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 51 q8 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 52 q8 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 53 q8 ∷
   re 55 1 (ℓ "乏丹乏") ∷
   rw 54 q8 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw 55 q8 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 56 q8 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 57 q8 ∷
   re 59 1 (ℓ "乏乄乏") ∷
   rw 58 q8 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 59 q8 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 60 q8 ∷
   re 62 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 61 q12 ∷
   rw 62 q13 ∷
   rw 65 q3 ∷
   re 63 3 (ℓ "乀") ∷
   rw 64 q14 ∷
   rw 67 q3 ∷
   re 65 3 (ℓ "乀") ∷
   re 67 1 (ℓ "乏丶乏") ∷
   rw 66 q8 ∷
   rw 67 q12 ∷
   rw⁻ 68 q15 ∷
   rw 61 q16 ∷
   re 61 8 (ℓ "乥") ∷
   rw⁻ 62 q5 ∷
   rw⁻ 63 q5 ∷
   rw⁻ 64 q6 ∷
   rw⁻ 65 q5 ∷
   rw⁻ 66 q6 ∷
   rw⁻ 67 q6 ∷
   re 69 1 (ℓ "乏丹乏") ∷
   rw 68 q8 ∷
   re 70 1 (ℓ "乏乄乏") ∷
   rw 69 q8 ∷
   rw 70 q17 ∷
   re 72 1 (ℓ "乏乄乏") ∷
   rw 71 q8 ∷
   rw 72 q17 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 73 q8 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 74 q8 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 75 q8 ∷
   re 77 1 (ℓ "乏乄乏") ∷
   rw 76 q8 ∷
   rw 77 q17 ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw 78 q8 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 79 q8 ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw 80 q8 ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 81 q8 ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw 82 q8 ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw 83 q8 ∷
   re 85 1 (ℓ "乏丹乏") ∷
   rw 84 q8 ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw 85 q8 ∷
   re 87 1 (ℓ "乏丧乏") ∷
   rw 86 q8 ∷
   re 88 1 (ℓ "乏乄乏") ∷
   rw 87 q8 ∷
   re 89 1 (ℓ "乏丧乏") ∷
   rw 88 q8 ∷
   re 90 1 (ℓ "乏乄乏") ∷
   rw 89 q8 ∷
   re 91 1 (ℓ "乏乄乏") ∷
   rw 90 q8 ∷
   rw 91 q8 ∷ []) Eq.refl

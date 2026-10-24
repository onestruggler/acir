{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD685 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D685 (W : Ws) (Sᴰ : SD685) where

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
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~30-⟶1⟩ : St 1810
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~30-⟶1⟩ = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 173 W
  q3 : Eqn
  q3 = eqn (ℓ "两乏") (ℓ "乏两") (low-comm (CK₀₁) (Swap))
  q4 : Eqn
  q4 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q7 : Eqn
  q7 = wE 2022 W
  q8 : Eqn
  q8 = wE 175 W
  q9 : Eqn
  q9 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q10 : Eqn
  q10 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q11 : Eqn
  q11 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q12 : Eqn
  q12 = wE 56 W
  q13 : Eqn
  q13 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q14 : Eqn
  q14 = wE 196 W
  q15 : Eqn
  q15 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q16 : Eqn
  q16 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q17 : Eqn
  q17 = sE 1810 lem-Bar⟨SSKSKK32-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~30-⟶1⟩
  q18 : Eqn
  q18 = wE 2023 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 CS13 CS13 CK31 CS13 CK31 CK31 CX30 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX30 CS01 CS01 CK01 CS01 CK01 CK01 X3]: 511 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两丞") (ℓ "丞丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 60 q1 ∷
   rw 59 q2 ∷
   rw 58 q3 ∷
   rw 57 q3 ∷
   rw 56 q4 ∷
   rw 55 q3 ∷
   rw 54 q4 ∷
   rw 53 q4 ∷
   re 52 1 (ℓ "乏乃乏") ∷
   rw 54 q5 ∷
   rw 51 q4 ∷
   rw 50 q4 ∷
   rw 49 q4 ∷
   rw 48 q4 ∷
   rw 47 q4 ∷
   rw 46 q4 ∷
   rw 45 q6 ∷
   rw 44 q3 ∷
   rw 43 q4 ∷
   rw 42 q4 ∷
   rw 41 q4 ∷
   rw 40 q6 ∷
   rw 39 q3 ∷
   rw 38 q6 ∷
   rw 37 q3 ∷
   re 36 1 (ℓ "乏乃乏") ∷
   rw 38 q5 ∷
   re 35 1 (ℓ "乏乇乏") ∷
   rw 37 q5 ∷
   re 34 1 (ℓ "乏乇乏") ∷
   rw 36 q5 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 35 q5 ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 34 q5 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 33 q5 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 32 q5 ∷
   rw 29 q2 ∷
   rw 30 q7 ∷
   rw 29 q8 ∷
   re 31 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 30 q9 ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "丽") ∷
   rw⁻ 32 q10 ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "举") ∷
   rw⁻ 34 q10 ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "中") ∷
   rw⁻ 36 q9 ∷
   rw⁻ 37 q11 ∷
   rw 30 q1 ∷
   rw⁻ 31 q9 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q5 ∷
   rw⁻ 33 q10 ∷
   re 35 1 (ℓ "乏丷乏") ∷
   rw 34 q5 ∷
   rw⁻ 35 q10 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 36 q5 ∷
   rw⁻ 37 q9 ∷
   rw⁻ 38 q11 ∷
   rw 31 q12 ∷
   re 31 8 (ℓ "九") ∷
   re 30 3 (ℓ "乞") ∷
   rw 31 q8 ∷
   rw 32 q8 ∷
   re 34 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 33 q13 ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "丽") ∷
   rw⁻ 35 q10 ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "举") ∷
   rw⁻ 37 q10 ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "中") ∷
   rw⁻ 39 q13 ∷
   rw⁻ 40 q11 ∷
   rw 33 q1 ∷
   rw⁻ 34 q13 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q5 ∷
   rw⁻ 36 q10 ∷
   re 38 1 (ℓ "乏丷乏") ∷
   rw 37 q5 ∷
   rw⁻ 38 q10 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 39 q5 ∷
   rw⁻ 40 q13 ∷
   rw⁻ 41 q11 ∷
   rw 34 q14 ∷
   re 34 8 (ℓ "习") ∷
   re 33 3 (ℓ "乡") ∷
   rw 34 q8 ∷
   rw 35 q8 ∷
   re 37 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 36 q9 ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "丽") ∷
   rw⁻ 38 q10 ∷
   rw 41 q1 ∷
   re 39 3 (ℓ "举") ∷
   rw⁻ 40 q10 ∷
   rw 43 q1 ∷
   re 41 3 (ℓ "中") ∷
   rw⁻ 42 q9 ∷
   rw⁻ 43 q11 ∷
   rw 36 q1 ∷
   rw⁻ 37 q9 ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q5 ∷
   rw⁻ 39 q10 ∷
   re 41 1 (ℓ "乏丷乏") ∷
   rw 40 q5 ∷
   rw⁻ 41 q10 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 42 q5 ∷
   rw⁻ 43 q9 ∷
   rw⁻ 44 q11 ∷
   rw 37 q12 ∷
   re 37 8 (ℓ "九") ∷
   re 36 3 (ℓ "乞") ∷
   rw 37 q8 ∷
   rw 38 q8 ∷
   rw 41 q1 ∷
   re 39 3 (ℓ "中") ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "中") ∷
   rw 43 q1 ∷
   re 41 3 (ℓ "乑") ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "中") ∷
   rw 45 q1 ∷
   re 43 3 (ℓ "乑") ∷
   rw 46 q1 ∷
   re 44 3 (ℓ "乑") ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "乓") ∷
   rw⁻ 46 q15 ∷
   rw⁻ 47 q16 ∷
   rw⁻ 48 q15 ∷
   rw⁻ 49 q16 ∷
   rw⁻ 50 q4 ∷
   rw⁻ 51 q4 ∷
   rw⁻ 52 q4 ∷
   rw⁻ 53 q15 ∷
   rw⁻ 54 q16 ∷
   rw⁻ 55 q4 ∷
   rw⁻ 56 q4 ∷
   rw⁻ 57 q4 ∷
   rw⁻ 58 q4 ∷
   rw⁻ 59 q4 ∷
   rw⁻ 60 q4 ∷
   rw 63 q1 ∷
   re 61 3 (ℓ "乓") ∷
   rw⁻ 62 q4 ∷
   rw⁻ 63 q4 ∷
   rw⁻ 64 q15 ∷
   rw⁻ 65 q4 ∷
   rw⁻ 66 q15 ∷
   rw⁻ 67 q15 ∷
   rw 68 q8 ∷
   rw 69 q8 ∷
   re 71 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 70 q9 ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "丽") ∷
   rw⁻ 72 q10 ∷
   rw 75 q1 ∷
   re 73 3 (ℓ "举") ∷
   rw⁻ 74 q10 ∷
   rw 77 q1 ∷
   re 75 3 (ℓ "中") ∷
   rw⁻ 76 q9 ∷
   rw⁻ 77 q11 ∷
   rw 70 q1 ∷
   rw⁻ 71 q9 ∷
   re 73 1 (ℓ "乏丶乏") ∷
   rw 72 q5 ∷
   rw⁻ 73 q10 ∷
   re 75 1 (ℓ "乏丷乏") ∷
   rw 74 q5 ∷
   rw⁻ 75 q10 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 76 q5 ∷
   rw⁻ 77 q9 ∷
   rw⁻ 78 q11 ∷
   rw 71 q12 ∷
   re 71 8 (ℓ "九") ∷
   re 70 3 (ℓ "乞") ∷
   rw 71 q8 ∷
   rw 72 q8 ∷
   re 74 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 73 q13 ∷
   rw 76 q1 ∷
   re 74 3 (ℓ "丽") ∷
   rw⁻ 75 q10 ∷
   rw 78 q1 ∷
   re 76 3 (ℓ "举") ∷
   rw⁻ 77 q10 ∷
   rw 80 q1 ∷
   re 78 3 (ℓ "中") ∷
   rw⁻ 79 q13 ∷
   rw⁻ 80 q11 ∷
   rw 73 q1 ∷
   rw⁻ 74 q13 ∷
   re 76 1 (ℓ "乏丶乏") ∷
   rw 75 q5 ∷
   rw⁻ 76 q10 ∷
   re 78 1 (ℓ "乏丷乏") ∷
   rw 77 q5 ∷
   rw⁻ 78 q10 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 79 q5 ∷
   rw⁻ 80 q13 ∷
   rw⁻ 81 q11 ∷
   rw 74 q14 ∷
   re 74 8 (ℓ "习") ∷
   re 73 3 (ℓ "乡") ∷
   rw 74 q8 ∷
   rw 75 q8 ∷
   re 77 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 76 q9 ∷
   rw 79 q1 ∷
   re 77 3 (ℓ "丽") ∷
   rw⁻ 78 q10 ∷
   rw 81 q1 ∷
   re 79 3 (ℓ "举") ∷
   rw⁻ 80 q10 ∷
   rw 83 q1 ∷
   re 81 3 (ℓ "中") ∷
   rw⁻ 82 q9 ∷
   rw⁻ 83 q11 ∷
   rw 76 q1 ∷
   rw⁻ 77 q9 ∷
   re 79 1 (ℓ "乏丶乏") ∷
   rw 78 q5 ∷
   rw⁻ 79 q10 ∷
   re 81 1 (ℓ "乏丷乏") ∷
   rw 80 q5 ∷
   rw⁻ 81 q10 ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw 82 q5 ∷
   rw⁻ 83 q9 ∷
   rw⁻ 84 q11 ∷
   rw 77 q12 ∷
   re 77 8 (ℓ "九") ∷
   re 76 3 (ℓ "乞") ∷
   rw 77 q8 ∷
   rw 78 q5 ∷
   rw 0 q17 ∷
   rw 49 q1 ∷
   rw 48 q2 ∷
   re 47 1 (ℓ "乏九乏") ∷
   re 48 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 47 q9 ∷
   rw 50 q1 ∷
   re 48 3 (ℓ "丽") ∷
   rw⁻ 49 q10 ∷
   rw 52 q1 ∷
   re 50 3 (ℓ "举") ∷
   rw⁻ 51 q10 ∷
   rw 54 q1 ∷
   re 52 3 (ℓ "中") ∷
   rw⁻ 53 q9 ∷
   rw⁻ 54 q11 ∷
   rw 55 q5 ∷
   rw 54 q11 ∷
   rw 53 q9 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q5 ∷
   rw 51 q10 ∷
   re 50 1 (ℓ "乏丷乏") ∷
   rw 52 q5 ∷
   rw 49 q10 ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 50 q5 ∷
   rw 47 q9 ∷
   rw 48 q12 ∷
   re 48 8 (ℓ "九") ∷
   rw 46 q2 ∷
   rw 45 q2 ∷
   re 44 1 (ℓ "乏习乏") ∷
   re 45 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 44 q13 ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "丽") ∷
   rw⁻ 46 q10 ∷
   rw 49 q1 ∷
   re 47 3 (ℓ "举") ∷
   rw⁻ 48 q10 ∷
   rw 51 q1 ∷
   re 49 3 (ℓ "中") ∷
   rw⁻ 50 q13 ∷
   rw⁻ 51 q11 ∷
   rw 52 q5 ∷
   rw 51 q11 ∷
   rw 50 q13 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q5 ∷
   rw 48 q10 ∷
   re 47 1 (ℓ "乏丷乏") ∷
   rw 49 q5 ∷
   rw 46 q10 ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 47 q5 ∷
   rw 44 q13 ∷
   rw 45 q14 ∷
   re 45 8 (ℓ "习") ∷
   rw 43 q2 ∷
   rw 42 q2 ∷
   re 41 1 (ℓ "乏九乏") ∷
   re 42 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 41 q9 ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "丽") ∷
   rw⁻ 43 q10 ∷
   rw 46 q1 ∷
   re 44 3 (ℓ "举") ∷
   rw⁻ 45 q10 ∷
   rw 48 q1 ∷
   re 46 3 (ℓ "中") ∷
   rw⁻ 47 q9 ∷
   rw⁻ 48 q11 ∷
   rw 49 q5 ∷
   rw 48 q11 ∷
   rw 47 q9 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q5 ∷
   rw 45 q10 ∷
   re 44 1 (ℓ "乏丷乏") ∷
   rw 46 q5 ∷
   rw 43 q10 ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 44 q5 ∷
   rw 41 q9 ∷
   rw 42 q12 ∷
   re 42 8 (ℓ "九") ∷
   rw 40 q2 ∷
   rw 39 q2 ∷
   rw 38 q15 ∷
   rw 37 q15 ∷
   rw 36 q4 ∷
   rw 35 q15 ∷
   rw 34 q4 ∷
   rw 33 q4 ∷
   re 32 1 (ℓ "乏乆乏") ∷
   rw 34 q5 ∷
   rw 31 q4 ∷
   rw 30 q4 ∷
   rw 29 q4 ∷
   rw 28 q4 ∷
   rw 27 q4 ∷
   rw 26 q4 ∷
   rw 25 q16 ∷
   rw 24 q15 ∷
   rw 23 q4 ∷
   rw 22 q4 ∷
   rw 21 q4 ∷
   rw 20 q16 ∷
   rw 19 q15 ∷
   rw 18 q16 ∷
   rw 17 q15 ∷
   re 16 1 (ℓ "乏乆乏") ∷
   rw 18 q5 ∷
   re 15 1 (ℓ "乏乄乏") ∷
   rw 17 q5 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw 16 q5 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q5 ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw 14 q5 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q5 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q5 ∷
   rw 9 q2 ∷
   rw 8 q2 ∷
   re 7 1 (ℓ "乏九乏") ∷
   re 8 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 7 q9 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 9 q10 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "举") ∷
   rw⁻ 11 q10 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw⁻ 13 q9 ∷
   rw⁻ 14 q11 ∷
   rw 15 q5 ∷
   rw 14 q11 ∷
   rw 13 q9 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q5 ∷
   rw 11 q10 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 12 q5 ∷
   rw 9 q10 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 10 q5 ∷
   rw 7 q9 ∷
   rw 8 q12 ∷
   re 8 8 (ℓ "九") ∷
   rw 6 q2 ∷
   rw 5 q2 ∷
   re 4 1 (ℓ "乏习乏") ∷
   re 5 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 4 q13 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q10 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q10 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q13 ∷
   rw⁻ 11 q11 ∷
   rw 12 q5 ∷
   rw 11 q11 ∷
   rw 10 q13 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q5 ∷
   rw 8 q10 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q5 ∷
   rw 6 q10 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q5 ∷
   rw 4 q13 ∷
   rw 5 q14 ∷
   re 5 8 (ℓ "习") ∷
   rw 3 q2 ∷
   rw 2 q2 ∷
   re 1 1 (ℓ "乏九乏") ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q9 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q10 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q10 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q9 ∷
   rw⁻ 8 q11 ∷
   rw 9 q5 ∷
   rw 8 q11 ∷
   rw 7 q9 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q5 ∷
   rw 5 q10 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q5 ∷
   rw 3 q10 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw 1 q9 ∷
   rw 2 q12 ∷
   re 2 8 (ℓ "九") ∷
   rw 0 q2 ∷
   rw 1 q18 ∷
   rw 0 q8 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "乔") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "乔") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乔") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "乐") ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 10 q3 ∷
   rw⁻ 11 q6 ∷
   rw⁻ 12 q4 ∷
   rw⁻ 13 q4 ∷
   rw⁻ 14 q4 ∷
   rw⁻ 15 q3 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 17 q4 ∷
   rw⁻ 18 q4 ∷
   rw⁻ 19 q4 ∷
   rw⁻ 20 q4 ∷
   rw⁻ 21 q4 ∷
   rw⁻ 22 q4 ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "乐") ∷
   rw⁻ 24 q4 ∷
   rw⁻ 25 q4 ∷
   rw⁻ 26 q3 ∷
   rw⁻ 27 q4 ∷
   rw⁻ 28 q3 ∷
   rw⁻ 29 q3 ∷
   rw 30 q8 ∷
   rw 31 q5 ∷ []) Eq.refl

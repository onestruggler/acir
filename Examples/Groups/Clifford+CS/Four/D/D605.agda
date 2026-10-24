{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD605 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D605 (W : Ws) (Sᴰ : SD605) where

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
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-factors-of-X0-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-X0-X3 : St 1302
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-factors-of-X0-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-X0-X3 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = wE 1106 W
  q4 : Eqn
  q4 = wE 140 W
  q5 : Eqn
  q5 = wE 7 W
  q6 : Eqn
  q6 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q7 : Eqn
  q7 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q8 : Eqn
  q8 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q9 : Eqn
  q9 = wE 1632 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = wE 27 W
  q12 : Eqn
  q12 = wE 139 W
  q13 : Eqn
  q13 = wE 31 W
  q14 : Eqn
  q14 = sE 1302 lem-Bar⟨SSKSKK31-⟶0⟩-passes-factors-of-X0-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-X0-X3
  q15 : Eqn
  q15 = wE 137 W
  q16 : Eqn
  q16 = wE 1633 W
  q17 : Eqn
  q17 = wE 317 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X0 X3 CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20 X0 X3]: 319 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-X0-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丌丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-X0-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丌丞") (ℓ "丌丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丌丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 62 q1 ∷
   rw⁻ 61 q2 ∷
   rw 60 q3 ∷
   rw 59 q4 ∷
   rw 58 q4 ∷
   rw 57 q5 ∷
   rw 56 q4 ∷
   rw 55 q5 ∷
   rw 54 q5 ∷
   rw⁻ 53 q6 ∷
   rw 52 q5 ∷
   rw 51 q5 ∷
   rw 50 q5 ∷
   rw 49 q5 ∷
   rw 48 q5 ∷
   rw 47 q5 ∷
   rw⁻ 46 q7 ∷
   rw 45 q4 ∷
   rw 44 q5 ∷
   rw 43 q5 ∷
   rw 42 q5 ∷
   rw⁻ 41 q7 ∷
   rw 40 q4 ∷
   rw⁻ 39 q7 ∷
   rw 38 q4 ∷
   rw⁻ 37 q6 ∷
   re 36 1 (ℓ "乏乄乏") ∷
   rw⁻ 38 q8 ∷
   rw 37 q4 ∷
   rw⁻ 36 q8 ∷
   re 37 3 (ℓ "乔") ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw⁻ 37 q8 ∷
   rw 36 q4 ∷
   rw⁻ 35 q8 ∷
   re 36 3 (ℓ "乔") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw⁻ 36 q8 ∷
   rw 35 q5 ∷
   rw⁻ 34 q8 ∷
   re 35 3 (ℓ "丽") ∷
   re 33 1 (ℓ "乏乄乏") ∷
   rw⁻ 35 q8 ∷
   rw 34 q4 ∷
   rw⁻ 33 q8 ∷
   re 34 3 (ℓ "乔") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q8 ∷
   rw 33 q5 ∷
   rw⁻ 32 q8 ∷
   re 33 3 (ℓ "丽") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q8 ∷
   rw 32 q5 ∷
   rw⁻ 31 q8 ∷
   re 32 3 (ℓ "丽") ∷
   rw⁻ 30 q2 ∷
   rw 29 q3 ∷
   rw 30 q9 ∷
   rw 29 q2 ∷
   re 31 1 (ℓ "乏乇乏") ∷
   rw 30 q8 ∷
   rw 31 q10 ∷
   rw 32 q8 ∷
   re 30 3 (ℓ "乑") ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q8 ∷
   rw 32 q11 ∷
   rw 33 q8 ∷
   re 31 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q8 ∷
   rw 33 q11 ∷
   rw 34 q8 ∷
   re 32 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏么乏") ∷
   rw 33 q8 ∷
   rw 34 q12 ∷
   rw 35 q8 ∷
   re 33 3 (ℓ "乒") ∷
   rw 34 q2 ∷
   rw 35 q2 ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q8 ∷
   rw 37 q11 ∷
   rw 38 q8 ∷
   re 36 3 (ℓ "中") ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q8 ∷
   rw 38 q11 ∷
   rw 39 q8 ∷
   re 37 3 (ℓ "中") ∷
   re 39 1 (ℓ "乏乇乏") ∷
   rw 38 q8 ∷
   rw 39 q10 ∷
   rw 40 q8 ∷
   re 38 3 (ℓ "乑") ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 39 q8 ∷
   rw 40 q11 ∷
   rw 41 q8 ∷
   re 39 3 (ℓ "中") ∷
   re 41 1 (ℓ "乏乇乏") ∷
   rw 40 q8 ∷
   rw 41 q10 ∷
   rw 42 q8 ∷
   re 40 3 (ℓ "乑") ∷
   re 42 1 (ℓ "乏乇乏") ∷
   rw 41 q8 ∷
   rw 42 q10 ∷
   rw 43 q8 ∷
   re 41 3 (ℓ "乑") ∷
   rw 42 q6 ∷
   rw 43 q10 ∷
   rw 44 q7 ∷
   rw 45 q10 ∷
   rw 46 q7 ∷
   rw 47 q11 ∷
   rw 48 q11 ∷
   rw 49 q11 ∷
   rw 50 q10 ∷
   rw 51 q7 ∷
   rw 52 q11 ∷
   rw 53 q11 ∷
   rw 54 q11 ∷
   rw 55 q11 ∷
   rw 56 q11 ∷
   rw 57 q11 ∷
   rw 58 q6 ∷
   rw 59 q11 ∷
   rw 60 q11 ∷
   rw 61 q10 ∷
   rw 62 q11 ∷
   rw 63 q10 ∷
   rw 64 q10 ∷
   rw 65 q2 ∷
   rw 66 q2 ∷
   re 68 1 (ℓ "乏乇乏") ∷
   rw 67 q8 ∷
   rw 68 q10 ∷
   rw 69 q8 ∷
   re 67 3 (ℓ "乑") ∷
   re 69 1 (ℓ "乏丶乏") ∷
   rw 68 q8 ∷
   rw 69 q11 ∷
   rw 70 q8 ∷
   re 68 3 (ℓ "中") ∷
   re 70 1 (ℓ "乏丶乏") ∷
   rw 69 q8 ∷
   rw 70 q11 ∷
   rw 71 q8 ∷
   re 69 3 (ℓ "中") ∷
   re 71 1 (ℓ "乏么乏") ∷
   rw 70 q8 ∷
   rw 71 q12 ∷
   rw 72 q8 ∷
   re 70 3 (ℓ "乒") ∷
   rw 71 q2 ∷
   rw 72 q13 ∷
   rw 0 q14 ∷
   rw 43 q1 ∷
   rw⁻ 42 q2 ∷
   re 41 1 (ℓ "乏久乏") ∷
   rw⁻ 43 q8 ∷
   rw 42 q15 ∷
   rw⁻ 41 q8 ∷
   re 42 3 (ℓ "乕") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q8 ∷
   rw 41 q5 ∷
   rw⁻ 40 q8 ∷
   re 41 3 (ℓ "丽") ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q8 ∷
   rw 40 q5 ∷
   rw⁻ 39 q8 ∷
   re 40 3 (ℓ "丽") ∷
   re 38 1 (ℓ "乏乄乏") ∷
   rw⁻ 40 q8 ∷
   rw 39 q4 ∷
   rw⁻ 38 q8 ∷
   re 39 3 (ℓ "乔") ∷
   rw⁻ 37 q2 ∷
   rw⁻ 36 q2 ∷
   rw 35 q4 ∷
   rw 34 q4 ∷
   rw 33 q5 ∷
   rw 32 q4 ∷
   rw 31 q5 ∷
   rw 30 q5 ∷
   rw⁻ 29 q6 ∷
   rw 28 q5 ∷
   rw 27 q5 ∷
   rw 26 q5 ∷
   rw 25 q5 ∷
   rw 24 q5 ∷
   rw 23 q5 ∷
   rw⁻ 22 q7 ∷
   rw 21 q4 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw⁻ 17 q7 ∷
   rw 16 q4 ∷
   rw⁻ 15 q7 ∷
   rw 14 q4 ∷
   rw⁻ 13 q6 ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw⁻ 14 q8 ∷
   rw 13 q4 ∷
   rw⁻ 12 q8 ∷
   re 13 3 (ℓ "乔") ∷
   re 11 1 (ℓ "乏乄乏") ∷
   rw⁻ 13 q8 ∷
   rw 12 q4 ∷
   rw⁻ 11 q8 ∷
   re 12 3 (ℓ "乔") ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q8 ∷
   rw 11 q5 ∷
   rw⁻ 10 q8 ∷
   re 11 3 (ℓ "丽") ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw⁻ 11 q8 ∷
   rw 10 q4 ∷
   rw⁻ 9 q8 ∷
   re 10 3 (ℓ "乔") ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q8 ∷
   rw 9 q5 ∷
   rw⁻ 8 q8 ∷
   re 9 3 (ℓ "丽") ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q8 ∷
   rw 8 q5 ∷
   rw⁻ 7 q8 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 6 q2 ∷
   rw⁻ 5 q2 ∷
   re 4 1 (ℓ "乏久乏") ∷
   rw⁻ 6 q8 ∷
   rw 5 q15 ∷
   rw⁻ 4 q8 ∷
   re 5 3 (ℓ "乕") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q8 ∷
   rw 4 q5 ∷
   rw⁻ 3 q8 ∷
   re 4 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q8 ∷
   rw 3 q5 ∷
   rw⁻ 2 q8 ∷
   re 3 3 (ℓ "丽") ∷
   re 1 1 (ℓ "乏乄乏") ∷
   rw⁻ 3 q8 ∷
   rw 2 q4 ∷
   rw⁻ 1 q8 ∷
   re 2 3 (ℓ "乔") ∷
   rw⁻ 0 q2 ∷
   rw 1 q16 ∷
   rw 0 q17 ∷
   rw 1 q2 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q8 ∷
   rw 3 q11 ∷
   rw 4 q8 ∷
   re 2 3 (ℓ "中") ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q8 ∷
   rw 4 q11 ∷
   rw 5 q8 ∷
   re 3 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏乇乏") ∷
   rw 4 q8 ∷
   rw 5 q10 ∷
   rw 6 q8 ∷
   re 4 3 (ℓ "乑") ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q8 ∷
   rw 6 q11 ∷
   rw 7 q8 ∷
   re 5 3 (ℓ "中") ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 6 q8 ∷
   rw 7 q10 ∷
   rw 8 q8 ∷
   re 6 3 (ℓ "乑") ∷
   re 8 1 (ℓ "乏乇乏") ∷
   rw 7 q8 ∷
   rw 8 q10 ∷
   rw 9 q8 ∷
   re 7 3 (ℓ "乑") ∷
   rw 8 q6 ∷
   rw 9 q10 ∷
   rw 10 q7 ∷
   rw 11 q10 ∷
   rw 12 q7 ∷
   rw 13 q11 ∷
   rw 14 q11 ∷
   rw 15 q11 ∷
   rw 16 q10 ∷
   rw 17 q7 ∷
   rw 18 q11 ∷
   rw 19 q11 ∷
   rw 20 q11 ∷
   rw 21 q11 ∷
   rw 22 q11 ∷
   rw 23 q11 ∷
   rw 24 q6 ∷
   rw 25 q11 ∷
   rw 26 q11 ∷
   rw 27 q10 ∷
   rw 28 q11 ∷
   rw 29 q10 ∷
   rw 30 q10 ∷
   rw 31 q17 ∷
   rw 32 q2 ∷
   rw 33 q13 ∷ []) Eq.refl

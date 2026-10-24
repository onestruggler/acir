{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D458 (W : Ws) where

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
  q2 = wE 140 W
  q3 : Eqn
  q3 = wE 7 W
  q4 : Eqn
  q4 = wE 766 W
  q5 : Eqn
  q5 = wE 27 W
  q6 : Eqn
  q6 = wE 142 W
  q7 : Eqn
  q7 = wE 31 W
  q8 : Eqn
  q8 = wE 36 W
  q9 : Eqn
  q9 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q10 : Eqn
  q10 = wE 37 W
  q11 : Eqn
  q11 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q12 : Eqn
  q12 = wE 5 W
  q13 : Eqn
  q13 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q14 : Eqn
  q14 = wE 1144 W
  q15 : Eqn
  q15 = wE 764 W

-- Bar(SSKSKK;1,3->0) passes groups of WBar(SSKSKK;~1,2->0) part3: 269 steps
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part3 : ⟪ (ℓ "丒丠丠临丠临临丒丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丹丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乏乄乏並丶丶乇丶乇乇並") ⟫ʷ ≈ ⟪ (ℓ "丒丠丠临丠临临丒丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丹丒丧丧乄丧乄乄丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") ⟫ʷ
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part3 = derive (ℓ "丒丠丠临丠临临丒丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丹丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乏乄乏並丶丶乇丶乇乇並") (ℓ "丒丠丠临丠临临丒丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丹丒丧丧乄丧乄乄丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑")
  (rw⁻ 59 q1 ∷
   rw 58 q2 ∷
   rw⁻ 57 q1 ∷
   re 58 3 (ℓ "乔") ∷
   re 56 1 (ℓ "乏乄乏") ∷
   rw⁻ 58 q1 ∷
   rw 57 q2 ∷
   rw⁻ 56 q1 ∷
   re 57 3 (ℓ "乔") ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw⁻ 57 q1 ∷
   rw 56 q3 ∷
   rw⁻ 55 q1 ∷
   re 56 3 (ℓ "丽") ∷
   re 54 1 (ℓ "乏乄乏") ∷
   rw⁻ 56 q1 ∷
   rw 55 q2 ∷
   rw⁻ 54 q1 ∷
   re 55 3 (ℓ "乔") ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw⁻ 55 q1 ∷
   rw 54 q3 ∷
   rw⁻ 53 q1 ∷
   re 54 3 (ℓ "丽") ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw⁻ 54 q1 ∷
   rw 53 q3 ∷
   rw⁻ 52 q1 ∷
   re 53 3 (ℓ "丽") ∷
   rw 53 q4 ∷
   rw 52 q5 ∷
   rw 53 q5 ∷
   rw 54 q6 ∷
   rw 55 q5 ∷
   rw 56 q6 ∷
   rw 57 q6 ∷
   re 59 1 (ℓ "乏丶乏") ∷
   rw 58 q1 ∷
   rw 59 q5 ∷
   rw 60 q1 ∷
   re 58 3 (ℓ "中") ∷
   re 60 1 (ℓ "乏丶乏") ∷
   rw 59 q1 ∷
   rw 60 q5 ∷
   rw 61 q1 ∷
   re 59 3 (ℓ "中") ∷
   re 61 1 (ℓ "乏乇乏") ∷
   rw 60 q1 ∷
   rw 61 q6 ∷
   rw 62 q1 ∷
   re 60 3 (ℓ "乑") ∷
   re 62 1 (ℓ "乏丶乏") ∷
   rw 61 q1 ∷
   rw 62 q5 ∷
   rw 63 q1 ∷
   re 61 3 (ℓ "中") ∷
   re 63 1 (ℓ "乏乇乏") ∷
   rw 62 q1 ∷
   rw 63 q6 ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "乑") ∷
   re 64 1 (ℓ "乏乇乏") ∷
   rw 63 q1 ∷
   rw 64 q6 ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "乑") ∷
   rw 64 q7 ∷
   re 52 1 (ℓ "丼丠丼") ∷
   rw 51 q8 ∷
   rw⁻ 52 q9 ∷
   rw 53 q10 ∷
   re 51 3 (ℓ "丧") ∷
   re 53 1 (ℓ "丼丠丼") ∷
   rw 52 q8 ∷
   rw⁻ 53 q9 ∷
   rw 54 q10 ∷
   re 52 3 (ℓ "丧") ∷
   re 54 1 (ℓ "丼临丼") ∷
   rw 53 q8 ∷
   rw⁻ 54 q11 ∷
   rw 55 q10 ∷
   re 53 3 (ℓ "乄") ∷
   re 55 1 (ℓ "丼丠丼") ∷
   rw 54 q8 ∷
   rw⁻ 55 q9 ∷
   rw 56 q10 ∷
   re 54 3 (ℓ "丧") ∷
   re 56 1 (ℓ "丼临丼") ∷
   rw 55 q8 ∷
   rw⁻ 56 q11 ∷
   rw 57 q10 ∷
   re 55 3 (ℓ "乄") ∷
   re 57 1 (ℓ "丼临丼") ∷
   rw 56 q8 ∷
   rw⁻ 57 q11 ∷
   rw 58 q10 ∷
   re 56 3 (ℓ "乄") ∷
   rw 57 q12 ∷
   rw 56 q2 ∷
   rw 55 q2 ∷
   rw 54 q3 ∷
   rw 53 q2 ∷
   rw 52 q3 ∷
   rw 51 q3 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw⁻ 52 q1 ∷
   rw 51 q3 ∷
   rw⁻ 50 q1 ∷
   re 51 3 (ℓ "丽") ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw⁻ 51 q1 ∷
   rw 50 q3 ∷
   rw⁻ 49 q1 ∷
   re 50 3 (ℓ "丽") ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw⁻ 50 q1 ∷
   rw 49 q3 ∷
   rw⁻ 48 q1 ∷
   re 49 3 (ℓ "丽") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw⁻ 49 q1 ∷
   rw 48 q3 ∷
   rw⁻ 47 q1 ∷
   re 48 3 (ℓ "丽") ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw⁻ 48 q1 ∷
   rw 47 q3 ∷
   rw⁻ 46 q1 ∷
   re 47 3 (ℓ "丽") ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw⁻ 47 q1 ∷
   rw 46 q3 ∷
   rw⁻ 45 q1 ∷
   re 46 3 (ℓ "丽") ∷
   rw⁻ 44 q13 ∷
   re 43 1 (ℓ "乏乄乏") ∷
   rw⁻ 45 q1 ∷
   rw 44 q2 ∷
   rw⁻ 43 q1 ∷
   re 44 3 (ℓ "乔") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw⁻ 44 q1 ∷
   rw 43 q3 ∷
   rw⁻ 42 q1 ∷
   re 43 3 (ℓ "丽") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw⁻ 43 q1 ∷
   rw 42 q3 ∷
   rw⁻ 41 q1 ∷
   re 42 3 (ℓ "丽") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q1 ∷
   rw 41 q3 ∷
   rw⁻ 40 q1 ∷
   re 41 3 (ℓ "丽") ∷
   rw⁻ 39 q13 ∷
   re 38 1 (ℓ "乏乄乏") ∷
   rw⁻ 40 q1 ∷
   rw 39 q2 ∷
   rw⁻ 38 q1 ∷
   re 39 3 (ℓ "乔") ∷
   rw⁻ 37 q13 ∷
   re 36 1 (ℓ "乏乄乏") ∷
   rw⁻ 38 q1 ∷
   rw 37 q2 ∷
   rw⁻ 36 q1 ∷
   re 37 3 (ℓ "乔") ∷
   rw 37 q14 ∷
   rw 36 q5 ∷
   rw 37 q5 ∷
   rw 38 q6 ∷
   rw 39 q5 ∷
   rw 40 q6 ∷
   rw 41 q6 ∷
   re 43 1 (ℓ "乏乇乏") ∷
   rw 42 q1 ∷
   rw 43 q6 ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "乑") ∷
   rw 43 q13 ∷
   re 45 1 (ℓ "乏乇乏") ∷
   rw 44 q1 ∷
   rw 45 q6 ∷
   rw 46 q1 ∷
   re 44 3 (ℓ "乑") ∷
   rw 45 q13 ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q1 ∷
   rw 47 q5 ∷
   rw 48 q1 ∷
   re 46 3 (ℓ "中") ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q1 ∷
   rw 48 q5 ∷
   rw 49 q1 ∷
   re 47 3 (ℓ "中") ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 48 q1 ∷
   rw 49 q5 ∷
   rw 50 q1 ∷
   re 48 3 (ℓ "中") ∷
   re 50 1 (ℓ "乏乇乏") ∷
   rw 49 q1 ∷
   rw 50 q6 ∷
   rw 51 q1 ∷
   re 49 3 (ℓ "乑") ∷
   rw 50 q13 ∷
   re 52 1 (ℓ "乏丶乏") ∷
   rw 51 q1 ∷
   rw 52 q5 ∷
   rw 53 q1 ∷
   re 51 3 (ℓ "中") ∷
   re 53 1 (ℓ "乏丶乏") ∷
   rw 52 q1 ∷
   rw 53 q5 ∷
   rw 54 q1 ∷
   re 52 3 (ℓ "中") ∷
   re 54 1 (ℓ "乏丶乏") ∷
   rw 53 q1 ∷
   rw 54 q5 ∷
   rw 55 q1 ∷
   re 53 3 (ℓ "中") ∷
   re 55 1 (ℓ "乏丶乏") ∷
   rw 54 q1 ∷
   rw 55 q5 ∷
   rw 56 q1 ∷
   re 54 3 (ℓ "中") ∷
   re 56 1 (ℓ "乏丶乏") ∷
   rw 55 q1 ∷
   rw 56 q5 ∷
   rw 57 q1 ∷
   re 55 3 (ℓ "中") ∷
   re 57 1 (ℓ "乏丶乏") ∷
   rw 56 q1 ∷
   rw 57 q5 ∷
   rw 58 q1 ∷
   re 56 3 (ℓ "中") ∷
   rw 57 q7 ∷
   re 36 1 (ℓ "丼丠丼") ∷
   rw 35 q8 ∷
   rw⁻ 36 q9 ∷
   rw 37 q10 ∷
   re 35 3 (ℓ "丧") ∷
   re 37 1 (ℓ "丼丠丼") ∷
   rw 36 q8 ∷
   rw⁻ 37 q9 ∷
   rw 38 q10 ∷
   re 36 3 (ℓ "丧") ∷
   re 38 1 (ℓ "丼临丼") ∷
   rw 37 q8 ∷
   rw⁻ 38 q11 ∷
   rw 39 q10 ∷
   re 37 3 (ℓ "乄") ∷
   re 39 1 (ℓ "丼丠丼") ∷
   rw 38 q8 ∷
   rw⁻ 39 q9 ∷
   rw 40 q10 ∷
   re 38 3 (ℓ "丧") ∷
   re 40 1 (ℓ "丼临丼") ∷
   rw 39 q8 ∷
   rw⁻ 40 q11 ∷
   rw 41 q10 ∷
   re 39 3 (ℓ "乄") ∷
   re 41 1 (ℓ "丼临丼") ∷
   rw 40 q8 ∷
   rw⁻ 41 q11 ∷
   rw 42 q10 ∷
   re 40 3 (ℓ "乄") ∷
   rw 29 q15 ∷ []) Eq.refl

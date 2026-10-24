{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D029 (W : Ws) where

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
  q2 = wE 275 W
  q3 : Eqn
  q3 = wE 25 W
  q4 : Eqn
  q4 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q5 : Eqn
  q5 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q6 : Eqn
  q6 = eqn (ℓ "並世") (ℓ "世並") (low-comm (Swap) (K))
  q7 : Eqn
  q7 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q8 : Eqn
  q8 = wE 30 W
  q9 : Eqn
  q9 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q10 : Eqn
  q10 = wE 27 W
  q11 : Eqn
  q11 = wE 122 W
  q12 : Eqn
  q12 = wE 5 W
  q13 : Eqn
  q13 = wE 24 W
  q14 : Eqn
  q14 = wE 124 W
  q15 : Eqn
  q15 = wE 334 W
  q16 : Eqn
  q16 = wE 31 W

-- AXIOM LF @1302 part2: 124 steps
lem-AXIOM-LF-at1302-part2 : ⟪ (ℓ "丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两乤丽丽乏丶乏並乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧乥中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄並") ⟫ʷ ≈ ⟪ (ℓ "丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两乤丽丽丽乔丽丽乖丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶乤丽丽乔丽乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇") ⟫ʷ
lem-AXIOM-LF-at1302-part2 = derive (ℓ "丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两乤丽丽乏丶乏並乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧乥中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄並") (ℓ "丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两乤丽丽丽乔丽丽乖丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶乤丽丽乔丽乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇")
  (re 32 3 (ℓ "丽") ∷
   re 34 1 (ℓ "乏乄乏") ∷
   rw 33 q1 ∷
   rw 34 q2 ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "乔") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 34 q1 ∷
   rw 35 q3 ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "丽") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 35 q1 ∷
   rw 36 q3 ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "丽") ∷
   rw 36 q4 ∷
   rw 37 q3 ∷
   rw 38 q3 ∷
   rw 39 q3 ∷
   rw 40 q3 ∷
   rw 41 q3 ∷
   rw 42 q3 ∷
   rw 43 q2 ∷
   rw 44 q5 ∷
   rw 45 q3 ∷
   rw 46 q3 ∷
   rw 47 q3 ∷
   rw 48 q3 ∷
   rw 49 q3 ∷
   rw 50 q3 ∷
   rw 51 q3 ∷
   rw 52 q3 ∷
   rw 53 q3 ∷
   rw 54 q4 ∷
   rw 55 q3 ∷
   rw 56 q3 ∷
   rw 57 q3 ∷
   rw 58 q2 ∷
   rw 59 q3 ∷
   rw 60 q3 ∷
   re 62 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 61 q6 ∷
   rw 62 q7 ∷
   rw 63 q8 ∷
   rw 64 q9 ∷
   rw 65 q8 ∷
   re 67 1 (ℓ "乏丶乏") ∷
   rw 66 q1 ∷
   rw 67 q10 ∷
   rw 68 q1 ∷
   re 66 3 (ℓ "中") ∷
   rw 67 q6 ∷
   rw 68 q11 ∷
   rw 61 q12 ∷
   rw 62 q6 ∷
   rw 63 q7 ∷
   rw 64 q13 ∷
   rw 65 q9 ∷
   rw 66 q13 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 67 q1 ∷
   rw 68 q3 ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "丽") ∷
   rw 68 q6 ∷
   rw 69 q14 ∷
   rw 62 q15 ∷
   re 62 8 (ℓ "乥") ∷
   re 61 3 (ℓ "乤") ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 62 q1 ∷
   rw 63 q3 ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "丽") ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 63 q1 ∷
   rw 64 q3 ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "丽") ∷
   re 65 1 (ℓ "乏乄乏") ∷
   rw 64 q1 ∷
   rw 65 q2 ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "乔") ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw 65 q1 ∷
   rw 66 q3 ∷
   rw 67 q1 ∷
   re 65 3 (ℓ "丽") ∷
   re 67 1 (ℓ "乏乄乏") ∷
   rw 66 q1 ∷
   rw 67 q2 ∷
   rw 68 q1 ∷
   re 66 3 (ℓ "乔") ∷
   re 68 1 (ℓ "乏乄乏") ∷
   rw 67 q1 ∷
   rw 68 q2 ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "乔") ∷
   rw 68 q4 ∷
   rw 69 q2 ∷
   rw 70 q5 ∷
   rw 71 q2 ∷
   rw 72 q5 ∷
   rw 73 q3 ∷
   rw 74 q3 ∷
   rw 75 q3 ∷
   rw 76 q2 ∷
   rw 77 q5 ∷
   rw 78 q3 ∷
   rw 79 q3 ∷
   rw 80 q3 ∷
   rw 81 q3 ∷
   rw 82 q3 ∷
   rw 83 q3 ∷
   rw 84 q4 ∷
   rw 85 q3 ∷
   rw 86 q3 ∷
   rw 87 q2 ∷
   rw 88 q3 ∷
   rw 89 q2 ∷
   rw 90 q2 ∷
   rw 91 q16 ∷ []) Eq.refl

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D251 (W : Ws) where

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
  q1 = wE 825 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X2 CK21 CS12 CS12 CKd21 X2]: 1 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK21-CS12-CS12-CKd21-X2 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘乇丶丶么丘") ⟫ʷ ≈ ⟪ (ℓ "丘乇丶丶么丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK21-CS12-CS12-CKd21-X2 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘乇丶丶么丘") (ℓ "丘乇丶丶么丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 0 q1 ∷ []) Eq.refl

private
  q2 : Eqn
  q2 = wE 5 W
  q3 : Eqn
  q3 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q4 : Eqn
  q4 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = wE 137 W
  q6 : Eqn
  q6 = wE 7 W
  q7 : Eqn
  q7 = wE 140 W
  q8 : Eqn
  q8 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q9 : Eqn
  q9 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q10 : Eqn
  q10 = wE 826 W
  q11 : Eqn
  q11 = wE 142 W
  q12 : Eqn
  q12 = wE 27 W
  q13 : Eqn
  q13 = wE 139 W
  q14 : Eqn
  q14 = wE 31 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 CK30 CS03 CS03 CKd30 X3]: 153 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK30-CS03-CS03-CKd30-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乑中中乒丞") ⟫ʷ ≈ ⟪ (ℓ "丞乑中中乒丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK30-CS03-CS03-CKd30-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乑中中乒丞") (ℓ "丞乑中中乒丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 35 q2 ∷
   rw⁻ 34 q3 ∷
   re 33 1 (ℓ "乏久乏") ∷
   rw⁻ 35 q4 ∷
   rw 34 q5 ∷
   rw⁻ 33 q4 ∷
   re 34 3 (ℓ "乕") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q4 ∷
   rw 33 q6 ∷
   rw⁻ 32 q4 ∷
   re 33 3 (ℓ "丽") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q4 ∷
   rw 32 q6 ∷
   rw⁻ 31 q4 ∷
   re 32 3 (ℓ "丽") ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw⁻ 32 q4 ∷
   rw 31 q7 ∷
   rw⁻ 30 q4 ∷
   re 31 3 (ℓ "乔") ∷
   rw⁻ 29 q3 ∷
   rw 28 q7 ∷
   rw 27 q7 ∷
   rw 26 q6 ∷
   rw 25 q7 ∷
   rw 24 q6 ∷
   rw 23 q6 ∷
   rw⁻ 22 q8 ∷
   rw 21 q6 ∷
   rw 20 q6 ∷
   rw 19 q6 ∷
   rw 18 q6 ∷
   rw 17 q6 ∷
   rw 16 q6 ∷
   rw⁻ 15 q9 ∷
   rw 14 q7 ∷
   rw 13 q6 ∷
   rw 12 q6 ∷
   rw 11 q6 ∷
   rw⁻ 10 q9 ∷
   rw 9 q7 ∷
   rw⁻ 8 q9 ∷
   rw 7 q7 ∷
   rw⁻ 6 q8 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q4 ∷
   rw 6 q7 ∷
   rw⁻ 5 q4 ∷
   re 6 3 (ℓ "乔") ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw⁻ 6 q4 ∷
   rw 5 q7 ∷
   rw⁻ 4 q4 ∷
   re 5 3 (ℓ "乔") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q4 ∷
   rw 4 q6 ∷
   rw⁻ 3 q4 ∷
   re 4 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw⁻ 4 q4 ∷
   rw 3 q7 ∷
   rw⁻ 2 q4 ∷
   re 3 3 (ℓ "乔") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q4 ∷
   rw 2 q6 ∷
   rw⁻ 1 q4 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q4 ∷
   rw 1 q6 ∷
   rw⁻ 0 q4 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q10 ∷
   rw 0 q3 ∷
   re 2 1 (ℓ "乏乇乏") ∷
   rw 1 q4 ∷
   rw 2 q11 ∷
   rw 3 q4 ∷
   re 1 3 (ℓ "乑") ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q4 ∷
   rw 3 q12 ∷
   rw 4 q4 ∷
   re 2 3 (ℓ "中") ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q4 ∷
   rw 4 q12 ∷
   rw 5 q4 ∷
   re 3 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏么乏") ∷
   rw 4 q4 ∷
   rw 5 q13 ∷
   rw 6 q4 ∷
   re 4 3 (ℓ "乒") ∷
   rw 5 q3 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q4 ∷
   rw 7 q12 ∷
   rw 8 q4 ∷
   re 6 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q4 ∷
   rw 8 q12 ∷
   rw 9 q4 ∷
   re 7 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q4 ∷
   rw 9 q11 ∷
   rw 10 q4 ∷
   re 8 3 (ℓ "乑") ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q4 ∷
   rw 10 q12 ∷
   rw 11 q4 ∷
   re 9 3 (ℓ "中") ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q4 ∷
   rw 11 q11 ∷
   rw 12 q4 ∷
   re 10 3 (ℓ "乑") ∷
   re 12 1 (ℓ "乏乇乏") ∷
   rw 11 q4 ∷
   rw 12 q11 ∷
   rw 13 q4 ∷
   re 11 3 (ℓ "乑") ∷
   rw 12 q8 ∷
   rw 13 q11 ∷
   rw 14 q9 ∷
   rw 15 q11 ∷
   rw 16 q9 ∷
   rw 17 q12 ∷
   rw 18 q12 ∷
   rw 19 q12 ∷
   rw 20 q11 ∷
   rw 21 q9 ∷
   rw 22 q12 ∷
   rw 23 q12 ∷
   rw 24 q12 ∷
   rw 25 q12 ∷
   rw 26 q12 ∷
   rw 27 q12 ∷
   rw 28 q8 ∷
   rw 29 q12 ∷
   rw 30 q12 ∷
   rw 31 q11 ∷
   rw 32 q12 ∷
   rw 33 q11 ∷
   rw 34 q11 ∷
   rw 35 q14 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = wE 827 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02 X3]: 223 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞") ⟫ʷ ≈ ⟪ (ℓ "丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞") (ℓ "丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 62 q2 ∷
   rw⁻ 61 q3 ∷
   rw 60 q6 ∷
   rw 59 q6 ∷
   rw 58 q7 ∷
   rw 57 q6 ∷
   rw 56 q6 ∷
   rw 55 q6 ∷
   rw⁻ 54 q8 ∷
   rw 53 q6 ∷
   rw 52 q6 ∷
   rw 51 q6 ∷
   rw 50 q6 ∷
   rw 49 q6 ∷
   rw 48 q6 ∷
   rw 47 q6 ∷
   rw 46 q6 ∷
   rw 45 q6 ∷
   rw⁻ 44 q9 ∷
   rw 43 q7 ∷
   rw 42 q6 ∷
   rw 41 q6 ∷
   rw 40 q6 ∷
   rw 39 q6 ∷
   rw 38 q6 ∷
   rw 37 q6 ∷
   rw⁻ 36 q8 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q4 ∷
   rw 36 q6 ∷
   rw⁻ 35 q4 ∷
   re 36 3 (ℓ "丽") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw⁻ 36 q4 ∷
   rw 35 q6 ∷
   rw⁻ 34 q4 ∷
   re 35 3 (ℓ "丽") ∷
   re 33 1 (ℓ "乏乄乏") ∷
   rw⁻ 35 q4 ∷
   rw 34 q7 ∷
   rw⁻ 33 q4 ∷
   re 34 3 (ℓ "乔") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q4 ∷
   rw 33 q6 ∷
   rw⁻ 32 q4 ∷
   re 33 3 (ℓ "丽") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q4 ∷
   rw 32 q6 ∷
   rw⁻ 31 q4 ∷
   re 32 3 (ℓ "丽") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q4 ∷
   rw 31 q6 ∷
   rw⁻ 30 q4 ∷
   re 31 3 (ℓ "丽") ∷
   rw⁻ 29 q3 ∷
   rw 28 q7 ∷
   rw 27 q7 ∷
   rw 26 q6 ∷
   rw 25 q7 ∷
   rw 24 q6 ∷
   rw 23 q6 ∷
   rw⁻ 22 q8 ∷
   rw 21 q6 ∷
   rw 20 q6 ∷
   rw 19 q6 ∷
   rw 18 q6 ∷
   rw 17 q6 ∷
   rw 16 q6 ∷
   rw⁻ 15 q9 ∷
   rw 14 q7 ∷
   rw 13 q6 ∷
   rw 12 q6 ∷
   rw 11 q6 ∷
   rw⁻ 10 q9 ∷
   rw 9 q7 ∷
   rw⁻ 8 q9 ∷
   rw 7 q7 ∷
   rw⁻ 6 q8 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q4 ∷
   rw 6 q7 ∷
   rw⁻ 5 q4 ∷
   re 6 3 (ℓ "乔") ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw⁻ 6 q4 ∷
   rw 5 q7 ∷
   rw⁻ 4 q4 ∷
   re 5 3 (ℓ "乔") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q4 ∷
   rw 4 q6 ∷
   rw⁻ 3 q4 ∷
   re 4 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw⁻ 4 q4 ∷
   rw 3 q7 ∷
   rw⁻ 2 q4 ∷
   re 3 3 (ℓ "乔") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q4 ∷
   rw 2 q6 ∷
   rw⁻ 1 q4 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q4 ∷
   rw 1 q6 ∷
   rw⁻ 0 q4 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q15 ∷
   rw 0 q3 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q4 ∷
   rw 2 q12 ∷
   rw 3 q4 ∷
   re 1 3 (ℓ "中") ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q4 ∷
   rw 3 q12 ∷
   rw 4 q4 ∷
   re 2 3 (ℓ "中") ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q4 ∷
   rw 4 q12 ∷
   rw 5 q4 ∷
   re 3 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏乇乏") ∷
   rw 4 q4 ∷
   rw 5 q11 ∷
   rw 6 q4 ∷
   re 4 3 (ℓ "乑") ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q4 ∷
   rw 6 q12 ∷
   rw 7 q4 ∷
   re 5 3 (ℓ "中") ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q4 ∷
   rw 7 q12 ∷
   rw 8 q4 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q8 ∷
   rw 8 q12 ∷
   rw 9 q12 ∷
   rw 10 q12 ∷
   rw 11 q12 ∷
   rw 12 q12 ∷
   rw 13 q12 ∷
   rw 14 q11 ∷
   rw 15 q9 ∷
   rw 16 q12 ∷
   rw 17 q12 ∷
   rw 18 q12 ∷
   rw 19 q12 ∷
   rw 20 q12 ∷
   rw 21 q12 ∷
   rw 22 q12 ∷
   rw 23 q12 ∷
   rw 24 q12 ∷
   rw 25 q8 ∷
   rw 26 q12 ∷
   rw 27 q12 ∷
   rw 28 q12 ∷
   rw 29 q11 ∷
   rw 30 q12 ∷
   rw 31 q12 ∷
   rw 32 q3 ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q4 ∷
   rw 34 q12 ∷
   rw 35 q4 ∷
   re 33 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q4 ∷
   rw 35 q12 ∷
   rw 36 q4 ∷
   re 34 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏乇乏") ∷
   rw 35 q4 ∷
   rw 36 q11 ∷
   rw 37 q4 ∷
   re 35 3 (ℓ "乑") ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q4 ∷
   rw 37 q12 ∷
   rw 38 q4 ∷
   re 36 3 (ℓ "中") ∷
   re 38 1 (ℓ "乏乇乏") ∷
   rw 37 q4 ∷
   rw 38 q11 ∷
   rw 39 q4 ∷
   re 37 3 (ℓ "乑") ∷
   re 39 1 (ℓ "乏乇乏") ∷
   rw 38 q4 ∷
   rw 39 q11 ∷
   rw 40 q4 ∷
   re 38 3 (ℓ "乑") ∷
   rw 39 q8 ∷
   rw 40 q11 ∷
   rw 41 q9 ∷
   rw 42 q11 ∷
   rw 43 q9 ∷
   rw 44 q12 ∷
   rw 45 q12 ∷
   rw 46 q12 ∷
   rw 47 q11 ∷
   rw 48 q9 ∷
   rw 49 q12 ∷
   rw 50 q12 ∷
   rw 51 q12 ∷
   rw 52 q12 ∷
   rw 53 q12 ∷
   rw 54 q12 ∷
   rw 55 q8 ∷
   rw 56 q12 ∷
   rw 57 q12 ∷
   rw 58 q11 ∷
   rw 59 q12 ∷
   rw 60 q11 ∷
   rw 61 q11 ∷
   rw 62 q14 ∷ []) Eq.refl

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD664 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D664 (W : Ws) (Sᴰ : SD664) where

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
  lem-pass-CK30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 1764
  lem-pass-CK30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 0 Sᴰ
  lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 1765
  lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 1 Sᴰ
  lem-pass-CSd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 1766
  lem-pass-CSd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 2 Sᴰ
  lem-pass-CKd30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 1767
  lem-pass-CKd30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 3 Sᴰ
  lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CZ13-CCZ123 : St 1768
  lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CZ13-CCZ123 = pickᴰ 4 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = wE 140 W
  q3 : Eqn
  q3 = wE 7 W
  q4 : Eqn
  q4 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q5 : Eqn
  q5 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q6 : Eqn
  q6 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = wE 2004 W
  q8 : Eqn
  q8 = wE 142 W
  q9 : Eqn
  q9 = wE 27 W
  q10 : Eqn
  q10 = wE 139 W
  q11 : Eqn
  q11 = wE 29 W
  q12 : Eqn
  q12 = wE 31 W
  q13 : Eqn
  q13 = sE 1766 lem-pass-CSd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q14 : Eqn
  q14 = sE 1767 lem-pass-CKd30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q15 : Eqn
  q15 = sE 1765 lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q16 : Eqn
  q16 = sE 1764 lem-pass-CK30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q17 : Eqn
  q17 = wE 76 W
  q18 : Eqn
  q18 = wE 137 W
  q19 : Eqn
  q19 = wE 2005 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 140 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丘丞中九丮九丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞中九丮九丘丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丘丞中九丮九丘丞") (ℓ "丘丞中九丮九丘丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 29 q1 ∷
   rw 28 q2 ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   rw 25 q2 ∷
   rw 24 q3 ∷
   rw 23 q3 ∷
   rw⁻ 22 q4 ∷
   rw 21 q3 ∷
   rw 20 q3 ∷
   rw 19 q3 ∷
   rw 18 q3 ∷
   rw 17 q3 ∷
   rw 16 q3 ∷
   rw⁻ 15 q5 ∷
   rw 14 q2 ∷
   rw 13 q3 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   rw⁻ 10 q5 ∷
   rw 9 q2 ∷
   rw⁻ 8 q5 ∷
   rw 7 q2 ∷
   rw⁻ 6 q4 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q6 ∷
   rw 6 q2 ∷
   rw⁻ 5 q6 ∷
   re 6 3 (ℓ "乔") ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw⁻ 6 q6 ∷
   rw 5 q2 ∷
   rw⁻ 4 q6 ∷
   re 5 3 (ℓ "乔") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q6 ∷
   rw 4 q3 ∷
   rw⁻ 3 q6 ∷
   re 4 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw⁻ 4 q6 ∷
   rw 3 q2 ∷
   rw⁻ 2 q6 ∷
   re 3 3 (ℓ "乔") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q6 ∷
   rw 2 q3 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q6 ∷
   rw 1 q3 ∷
   rw⁻ 0 q6 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q7 ∷
   re 1 1 (ℓ "乏乇乏") ∷
   rw 0 q6 ∷
   rw 1 q8 ∷
   rw 2 q6 ∷
   re 0 3 (ℓ "乑") ∷
   rw 1 q9 ∷
   re 3 1 (ℓ "乏么乏") ∷
   rw 2 q6 ∷
   rw 3 q10 ∷
   rw 4 q6 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q11 ∷
   rw 4 q12 ∷
   rw 3 q13 ∷
   rw 2 q14 ∷
   rw 1 q15 ∷
   rw 0 q16 ∷
   rw 12 q1 ∷
   rw 11 q17 ∷
   re 10 1 (ℓ "乏久乏") ∷
   rw⁻ 12 q6 ∷
   rw 11 q18 ∷
   rw⁻ 10 q6 ∷
   re 11 3 (ℓ "乕") ∷
   rw 9 q3 ∷
   re 8 1 (ℓ "乏乄乏") ∷
   rw⁻ 10 q6 ∷
   rw 9 q2 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (ℓ "乔") ∷
   rw 9 q19 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 9 q9 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "中") ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q6 ∷
   rw 10 q9 ∷
   rw 11 q6 ∷
   re 9 3 (ℓ "中") ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q6 ∷
   rw 11 q8 ∷
   rw 12 q6 ∷
   re 10 3 (ℓ "乑") ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q6 ∷
   rw 12 q9 ∷
   rw 13 q6 ∷
   re 11 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏乇乏") ∷
   rw 12 q6 ∷
   rw 13 q8 ∷
   rw 14 q6 ∷
   re 12 3 (ℓ "乑") ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 13 q6 ∷
   rw 14 q8 ∷
   rw 15 q6 ∷
   re 13 3 (ℓ "乑") ∷
   rw 14 q4 ∷
   rw 15 q8 ∷
   rw 16 q5 ∷
   rw 17 q8 ∷
   rw 18 q5 ∷
   rw 19 q9 ∷
   rw 20 q9 ∷
   rw 21 q9 ∷
   rw 22 q8 ∷
   rw 23 q5 ∷
   rw 24 q9 ∷
   rw 25 q9 ∷
   rw 26 q9 ∷
   rw 27 q9 ∷
   rw 28 q9 ∷
   rw 29 q9 ∷
   rw 30 q4 ∷
   rw 31 q9 ∷
   rw 32 q9 ∷
   rw 33 q8 ∷
   rw 34 q9 ∷
   rw 35 q8 ∷
   rw 36 q8 ∷
   rw 37 q12 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = wE 1987 W
  q21 : Eqn
  q21 = eqn (ℓ "丌丿") (ℓ "丿丌") (low₁-comm (X) ((Swap ↑ • CZ • Swap ↑)))
  q22 : Eqn
  q22 = eqn (ℓ "丌乜") (ℓ "乜丌") (low₁-comm (X) (CCZ))
  q23 : Eqn
  q23 = sE 1768 lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CZ13-CCZ123
  q24 : Eqn
  q24 = wE 1989 W
  q25 : Eqn
  q25 = wE 2006 W

-- pass [X0 X2 CS13 TOFF102 CSd13 TOFF102 X0 X2] [CCZ123]: 10 steps
lem-pass-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2-vs-CCZ123 : ⟪ (ℓ "丌丘丽习举习丌丘乜") ⟫ʷ ≈ ⟪ (ℓ "乜丌丘丽习举习丌丘") ⟫ʷ
lem-pass-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2-vs-CCZ123 = derive (ℓ "丌丘丽习举习丌丘乜") (ℓ "乜丌丘丽习举习丌丘")
  (rw 7 q20 ∷
   rw 6 q21 ∷
   rw 7 q22 ∷
   rw 2 q23 ∷
   rw 1 q24 ∷
   rw 2 q20 ∷
   rw 0 q21 ∷
   rw 1 q21 ∷
   rw 2 q22 ∷
   rw 0 q25 ∷ []) Eq.refl

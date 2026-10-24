{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD547 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D547 (W : Ws) (Sᴰ : SD547) where

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
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1 : St 921
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 173 W
  q3 : Eqn
  q3 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q4 : Eqn
  q4 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q5 : Eqn
  q5 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 56 W
  q8 : Eqn
  q8 = wE 1567 W
  q9 : Eqn
  q9 = wE 175 W
  q10 : Eqn
  q10 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q11 : Eqn
  q11 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q12 : Eqn
  q12 = eqn (ℓ "丏乏") (ℓ "乏丏") (low-comm (((S • S • S) ↑)) (Swap))
  q13 : Eqn
  q13 = sE 921 lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1
  q14 : Eqn
  q14 = wE 1568 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 TOFF013 X3]: 237 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF013-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乞丞") ⟫ʷ ≈ ⟪ (ℓ "丞乞丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF013-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乞丞") (ℓ "丞乞丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 32 q1 ∷
   rw 31 q2 ∷
   re 30 1 (ℓ "乏九乏") ∷
   re 31 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 30 q3 ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "丽") ∷
   rw⁻ 32 q4 ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "举") ∷
   rw⁻ 34 q4 ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "中") ∷
   rw⁻ 36 q3 ∷
   rw⁻ 37 q5 ∷
   rw 38 q6 ∷
   rw 37 q5 ∷
   rw 36 q3 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q6 ∷
   rw 34 q4 ∷
   re 33 1 (ℓ "乏丷乏") ∷
   rw 35 q6 ∷
   rw 32 q4 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 33 q6 ∷
   rw 30 q3 ∷
   rw 31 q7 ∷
   re 31 8 (ℓ "九") ∷
   rw 29 q2 ∷
   rw 30 q8 ∷
   rw 29 q9 ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "举") ∷
   rw 31 q9 ∷
   rw⁻ 32 q10 ∷
   rw⁻ 33 q11 ∷
   rw⁻ 34 q10 ∷
   rw⁻ 35 q10 ∷
   rw 36 q9 ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "乓") ∷
   rw 38 q9 ∷
   rw⁻ 39 q10 ∷
   rw⁻ 40 q10 ∷
   rw⁻ 41 q10 ∷
   rw⁻ 42 q10 ∷
   rw⁻ 43 q10 ∷
   rw⁻ 44 q10 ∷
   rw⁻ 45 q12 ∷
   rw⁻ 46 q11 ∷
   rw⁻ 47 q10 ∷
   rw⁻ 48 q10 ∷
   rw⁻ 49 q10 ∷
   rw 50 q9 ∷
   rw 53 q1 ∷
   re 51 3 (ℓ "乓") ∷
   rw 52 q9 ∷
   rw 53 q9 ∷
   rw 56 q1 ∷
   re 54 3 (ℓ "丮") ∷
   rw 57 q1 ∷
   re 55 3 (ℓ "乒") ∷
   rw 58 q1 ∷
   re 56 3 (ℓ "丮") ∷
   rw 59 q1 ∷
   re 57 3 (ℓ "丮") ∷
   rw 58 q9 ∷
   rw 59 q9 ∷
   rw 62 q1 ∷
   re 60 3 (ℓ "中") ∷
   rw 63 q1 ∷
   re 61 3 (ℓ "中") ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "中") ∷
   rw 63 q9 ∷
   rw⁻ 64 q10 ∷
   rw⁻ 65 q11 ∷
   rw⁻ 66 q10 ∷
   rw⁻ 67 q10 ∷
   rw 68 q9 ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "乓") ∷
   rw 70 q9 ∷
   rw⁻ 71 q10 ∷
   rw⁻ 72 q10 ∷
   rw⁻ 73 q10 ∷
   rw⁻ 74 q10 ∷
   rw⁻ 75 q10 ∷
   rw⁻ 76 q10 ∷
   rw⁻ 77 q12 ∷
   rw⁻ 78 q11 ∷
   rw⁻ 79 q10 ∷
   rw⁻ 80 q10 ∷
   rw⁻ 81 q10 ∷
   rw 82 q9 ∷
   rw 85 q1 ∷
   re 83 3 (ℓ "乓") ∷
   rw 84 q9 ∷
   rw 85 q9 ∷
   rw 88 q1 ∷
   re 86 3 (ℓ "丮") ∷
   rw 89 q1 ∷
   re 87 3 (ℓ "乒") ∷
   rw 90 q1 ∷
   re 88 3 (ℓ "丮") ∷
   rw 91 q1 ∷
   re 89 3 (ℓ "丮") ∷
   rw 90 q9 ∷
   rw 91 q9 ∷
   rw 94 q1 ∷
   re 92 3 (ℓ "丮") ∷
   rw 95 q1 ∷
   re 93 3 (ℓ "丮") ∷
   rw 96 q1 ∷
   re 94 3 (ℓ "丮") ∷
   rw 95 q9 ∷
   rw 96 q6 ∷
   rw 0 q13 ∷
   rw 67 q1 ∷
   rw 66 q2 ∷
   re 65 1 (ℓ "乏丨乏") ∷
   rw 67 q6 ∷
   re 64 1 (ℓ "乏丨乏") ∷
   rw 66 q6 ∷
   re 63 1 (ℓ "乏丨乏") ∷
   rw 65 q6 ∷
   rw 62 q2 ∷
   rw 61 q2 ∷
   re 60 1 (ℓ "乏丨乏") ∷
   rw 62 q6 ∷
   re 59 1 (ℓ "乏丨乏") ∷
   rw 61 q6 ∷
   re 58 1 (ℓ "乏久乏") ∷
   rw 60 q6 ∷
   re 57 1 (ℓ "乏丨乏") ∷
   rw 59 q6 ∷
   rw 56 q2 ∷
   rw 55 q2 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 56 q6 ∷
   rw 53 q2 ∷
   rw 52 q10 ∷
   rw 51 q10 ∷
   rw 50 q10 ∷
   rw 49 q11 ∷
   rw 48 q12 ∷
   rw 47 q10 ∷
   rw 46 q10 ∷
   rw 45 q10 ∷
   rw 44 q10 ∷
   rw 43 q10 ∷
   rw 42 q10 ∷
   rw 41 q2 ∷
   re 40 1 (ℓ "乏乆乏") ∷
   rw 42 q6 ∷
   rw 39 q2 ∷
   rw 38 q10 ∷
   rw 37 q10 ∷
   rw 36 q11 ∷
   rw 35 q10 ∷
   rw 34 q2 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q6 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q6 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q6 ∷
   rw 30 q2 ∷
   rw 29 q2 ∷
   re 28 1 (ℓ "乏丨乏") ∷
   rw 30 q6 ∷
   re 27 1 (ℓ "乏丨乏") ∷
   rw 29 q6 ∷
   re 26 1 (ℓ "乏久乏") ∷
   rw 28 q6 ∷
   re 25 1 (ℓ "乏丨乏") ∷
   rw 27 q6 ∷
   rw 24 q2 ∷
   rw 23 q2 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 24 q6 ∷
   rw 21 q2 ∷
   rw 20 q10 ∷
   rw 19 q10 ∷
   rw 18 q10 ∷
   rw 17 q11 ∷
   rw 16 q12 ∷
   rw 15 q10 ∷
   rw 14 q10 ∷
   rw 13 q10 ∷
   rw 12 q10 ∷
   rw 11 q10 ∷
   rw 10 q10 ∷
   rw 9 q2 ∷
   re 8 1 (ℓ "乏乆乏") ∷
   rw 10 q6 ∷
   rw 7 q2 ∷
   rw 6 q10 ∷
   rw 5 q10 ∷
   rw 4 q11 ∷
   rw 3 q10 ∷
   rw 2 q2 ∷
   re 1 1 (ℓ "乏丷乏") ∷
   rw 3 q6 ∷
   rw 0 q2 ∷
   rw 1 q14 ∷
   rw 0 q9 ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 1 q1 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q6 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q7 ∷
   re 2 8 (ℓ "九") ∷
   re 1 3 (ℓ "乞") ∷
   rw 2 q9 ∷
   rw 3 q6 ∷ []) Eq.refl

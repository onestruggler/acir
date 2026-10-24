{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D019 (W : Ws) where

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
  q1 = wE 335 W
  q2 : Eqn
  q2 = wE 71 W
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 72 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = eqn (ℓ "丁乏") (ℓ "乏丁") (low-comm ((iI ↑)) (Swap))
  q7 : Eqn
  q7 = wE 385 W

-- sw2 TOFF213: 15 steps
lem-sw2-TOFF213 : ⟪ (ℓ "乏乥乏") ⟫ʷ ≈ ⟪ (ℓ "乨") ⟫ʷ
lem-sw2-TOFF213 = derive (ℓ "乏乥乏") (ℓ "乨")
  (re 1 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 0 q1 ∷
   rw 1 q2 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "乀") ∷
   rw 3 q4 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "乀") ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw 6 q1 ∷
   rw⁻ 7 q6 ∷
   rw 0 q7 ∷
   re 0 8 (ℓ "乨") ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q8 : Eqn
  q8 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q9 : Eqn
  q9 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q10 : Eqn
  q10 = wE 336 W
  q11 : Eqn
  q11 = wE 368 W

-- sw2 TOFF301: 28 steps
lem-sw2-TOFF301 : ⟪ (ℓ "乏书乏") ⟫ʷ ≈ ⟪ (ℓ "乣") ⟫ʷ
lem-sw2-TOFF301 = derive (ℓ "乏书乏") (ℓ "乣")
  (re 1 1 (ℓ "乏乣乏") ∷
   re 2 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 1 q1 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q8 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q8 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q1 ∷
   rw⁻ 8 q9 ∷
   rw 9 q5 ∷
   rw 0 q10 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q5 ∷
   rw⁻ 2 q8 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q5 ∷
   rw⁻ 4 q8 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q5 ∷
   rw 6 q10 ∷
   rw⁻ 7 q9 ∷
   rw 0 q11 ∷
   re 0 8 (ℓ "乣") ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = eqn (ℓ "並东") (ℓ "东並") (low-comm (Swap) ((K ↑)))
  q13 : Eqn
  q13 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q14 : Eqn
  q14 = wE 30 W
  q15 : Eqn
  q15 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q16 : Eqn
  q16 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q17 : Eqn
  q17 = wE 27 W
  q18 : Eqn
  q18 = wE 122 W
  q19 : Eqn
  q19 = wE 31 W
  q20 : Eqn
  q20 = wE 5 W
  q21 : Eqn
  q21 = eqn (ℓ "並世") (ℓ "世並") (low-comm (Swap) (K))
  q22 : Eqn
  q22 = wE 24 W
  q23 : Eqn
  q23 = wE 25 W
  q24 : Eqn
  q24 = wE 124 W
  q25 : Eqn
  q25 = wE 386 W

-- sw2 TOFF302: 47 steps
lem-sw2-TOFF302 : ⟪ (ℓ "乏乧乏") ⟫ʷ ≈ ⟪ (ℓ "乤") ⟫ʷ
lem-sw2-TOFF302 = derive (ℓ "乏乧乏") (ℓ "乤")
  (re 1 1 (ℓ "並乨並") ∷
   re 2 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 1 q12 ∷
   rw 2 q13 ∷
   rw 3 q14 ∷
   rw 4 q15 ∷
   rw 5 q14 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q16 ∷
   rw 7 q17 ∷
   rw 8 q16 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q12 ∷
   rw 8 q18 ∷
   rw 9 q19 ∷
   rw 0 q10 ∷
   rw 1 q2 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "丰") ∷
   rw 3 q4 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "丰") ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q5 ∷
   rw 6 q10 ∷
   rw⁻ 7 q9 ∷
   rw 0 q20 ∷
   rw 1 q21 ∷
   rw 2 q13 ∷
   re 4 1 (ℓ "乏个乏") ∷
   rw 3 q16 ∷
   rw 4 q22 ∷
   rw 5 q16 ∷
   re 3 3 (ℓ "乀") ∷
   rw 4 q15 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw 5 q16 ∷
   rw 6 q22 ∷
   rw 7 q16 ∷
   re 5 3 (ℓ "乀") ∷
   rw 6 q23 ∷
   rw 7 q21 ∷
   rw 8 q24 ∷
   rw 1 q25 ∷
   re 1 8 (ℓ "乥") ∷
   re 0 3 (ℓ "乤") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 TOFF312: 15 steps
lem-sw2-TOFF312 : ⟪ (ℓ "乏乨乏") ⟫ʷ ≈ ⟪ (ℓ "乥") ⟫ʷ
lem-sw2-TOFF312 = derive (ℓ "乏乨乏") (ℓ "乥")
  (re 1 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 0 q10 ∷
   rw 1 q2 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "乀") ∷
   rw 3 q4 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "乀") ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw 6 q10 ∷
   rw⁻ 7 q6 ∷
   rw 0 q25 ∷
   re 0 8 (ℓ "乥") ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 387 W

-- xx0: 1 steps
lem-xx0 : ⟪ (ℓ "丌丌") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xx0 = derive (ℓ "丌丌") []
  (rw 0 q26 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = eqn (ℓ "丌丒") (ℓ "丒丌") (low₁-comm (X) (X))

-- xc01: 1 steps
lem-xc01 : ⟪ (ℓ "丌丒") ⟫ʷ ≈ ⟪ (ℓ "丒丌") ⟫ʷ
lem-xc01 = derive (ℓ "丌丒") (ℓ "丒丌")
  (rw 0 q27 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))

-- xc02: 1 steps
lem-xc02 : ⟪ (ℓ "丌丘") ⟫ʷ ≈ ⟪ (ℓ "丘丌") ⟫ʷ
lem-xc02 = derive (ℓ "丌丘") (ℓ "丘丌")
  (rw 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))

-- xc03: 1 steps
lem-xc03 : ⟪ (ℓ "丌丞") ⟫ʷ ≈ ⟪ (ℓ "丞丌") ⟫ʷ
lem-xc03 = derive (ℓ "丌丞") (ℓ "丞丌")
  (rw 0 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = wE 388 W

-- xx1: 1 steps
lem-xx1 : ⟪ (ℓ "丒丒") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xx1 = derive (ℓ "丒丒") []
  (rw 0 q30 ∷ []) Eq.refl

-- xc10: 1 steps
lem-xc10 : ⟪ (ℓ "丒丌") ⟫ʷ ≈ ⟪ (ℓ "丌丒") ⟫ʷ
lem-xc10 = derive (ℓ "丒丌") (ℓ "丌丒")
  (rw⁻ 0 q27 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = eqn (ℓ "丒丘") (ℓ "丘丒") (low-comm ((X ↑)) (X))

-- xc12: 1 steps
lem-xc12 : ⟪ (ℓ "丒丘") ⟫ʷ ≈ ⟪ (ℓ "丘丒") ⟫ʷ
lem-xc12 = derive (ℓ "丒丘") (ℓ "丘丒")
  (rw 0 q31 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = eqn (ℓ "丒丞") (ℓ "丞丒") (low-comm ((X ↑)) ((X ↑)))

-- xc13: 1 steps
lem-xc13 : ⟪ (ℓ "丒丞") ⟫ʷ ≈ ⟪ (ℓ "丞丒") ⟫ʷ
lem-xc13 = derive (ℓ "丒丞") (ℓ "丞丒")
  (rw 0 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = wE 389 W

-- xx2: 1 steps
lem-xx2 : ⟪ (ℓ "丘丘") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xx2 = derive (ℓ "丘丘") []
  (rw 0 q33 ∷ []) Eq.refl

-- xc20: 1 steps
lem-xc20 : ⟪ (ℓ "丘丌") ⟫ʷ ≈ ⟪ (ℓ "丌丘") ⟫ʷ
lem-xc20 = derive (ℓ "丘丌") (ℓ "丌丘")
  (rw⁻ 0 q28 ∷ []) Eq.refl

-- xc21: 1 steps
lem-xc21 : ⟪ (ℓ "丘丒") ⟫ʷ ≈ ⟪ (ℓ "丒丘") ⟫ʷ
lem-xc21 = derive (ℓ "丘丒") (ℓ "丒丘")
  (rw⁻ 0 q31 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))

-- xc23: 1 steps
lem-xc23 : ⟪ (ℓ "丘丞") ⟫ʷ ≈ ⟪ (ℓ "丞丘") ⟫ʷ
lem-xc23 = derive (ℓ "丘丞") (ℓ "丞丘")
  (rw 0 q34 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = wE 390 W

-- xx3: 1 steps
lem-xx3 : ⟪ (ℓ "丞丞") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xx3 = derive (ℓ "丞丞") []
  (rw 0 q35 ∷ []) Eq.refl

-- xc30: 1 steps
lem-xc30 : ⟪ (ℓ "丞丌") ⟫ʷ ≈ ⟪ (ℓ "丌丞") ⟫ʷ
lem-xc30 = derive (ℓ "丞丌") (ℓ "丌丞")
  (rw⁻ 0 q29 ∷ []) Eq.refl

-- xc31: 1 steps
lem-xc31 : ⟪ (ℓ "丞丒") ⟫ʷ ≈ ⟪ (ℓ "丒丞") ⟫ʷ
lem-xc31 = derive (ℓ "丞丒") (ℓ "丒丞")
  (rw⁻ 0 q32 ∷ []) Eq.refl

-- xc32: 1 steps
lem-xc32 : ⟪ (ℓ "丞丘") ⟫ʷ ≈ ⟪ (ℓ "丘丞") ⟫ʷ
lem-xc32 = derive (ℓ "丞丘") (ℓ "丘丞")
  (rw⁻ 0 q34 ∷ []) Eq.refl

-- swsw0: 1 steps
lem-swsw0 : ⟪ (ℓ "並並") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-swsw0 = derive (ℓ "並並") []
  (rw 0 q19 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = wE 14 W

-- swsw1: 1 steps
lem-swsw1 : ⟪ (ℓ "丼丼") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-swsw1 = derive (ℓ "丼丼") []
  (rw 0 q36 ∷ []) Eq.refl

-- swsw2: 1 steps
lem-swsw2 : ⟪ (ℓ "乏乏") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-swsw2 = derive (ℓ "乏乏") []
  (rw 0 q5 ∷ []) Eq.refl

-- xt0 0000: 0 steps
lem-xt0-0000 : ⟪ (ℓ "丌") ⟫ʷ ≈ ⟪ (ℓ "丌") ⟫ʷ
lem-xt0-0000 = refl

-- xs0 0000: 0 steps
lem-xs0-0000 : ⟪ (ℓ "丌") ⟫ʷ ≈ ⟪ (ℓ "丌") ⟫ʷ
lem-xs0-0000 = refl

-- xt0 1000: 1 steps
lem-xt0-1000 : ⟪ (ℓ "丌丌") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xt0-1000 = derive (ℓ "丌丌") []
  (rw 0 q26 ∷ []) Eq.refl

-- xs0 1000: 1 steps
lem-xs0-1000 : ⟪ (ℓ "丌丌") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xs0-1000 = derive (ℓ "丌丌") []
  (rw 0 q26 ∷ []) Eq.refl

-- xt0 0100: 0 steps
lem-xt0-0100 : ⟪ (ℓ "丌丒") ⟫ʷ ≈ ⟪ (ℓ "丌丒") ⟫ʷ
lem-xt0-0100 = refl

-- xs0 0100: 1 steps
lem-xs0-0100 : ⟪ (ℓ "丒丌") ⟫ʷ ≈ ⟪ (ℓ "丌丒") ⟫ʷ
lem-xs0-0100 = derive (ℓ "丒丌") (ℓ "丌丒")
  (rw⁻ 0 q27 ∷ []) Eq.refl

-- xt0 1100: 1 steps
lem-xt0-1100 : ⟪ (ℓ "丌丌丒") ⟫ʷ ≈ ⟪ (ℓ "丒") ⟫ʷ
lem-xt0-1100 = derive (ℓ "丌丌丒") (ℓ "丒")
  (rw 0 q26 ∷ []) Eq.refl

-- xs0 1100: 2 steps
lem-xs0-1100 : ⟪ (ℓ "丌丒丌") ⟫ʷ ≈ ⟪ (ℓ "丒") ⟫ʷ
lem-xs0-1100 = derive (ℓ "丌丒丌") (ℓ "丒")
  (rw⁻ 1 q27 ∷
   rw 0 q26 ∷ []) Eq.refl

-- xt0 0010: 0 steps
lem-xt0-0010 : ⟪ (ℓ "丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘") ⟫ʷ
lem-xt0-0010 = refl

-- xs0 0010: 1 steps
lem-xs0-0010 : ⟪ (ℓ "丘丌") ⟫ʷ ≈ ⟪ (ℓ "丌丘") ⟫ʷ
lem-xs0-0010 = derive (ℓ "丘丌") (ℓ "丌丘")
  (rw⁻ 0 q28 ∷ []) Eq.refl

-- xt0 1010: 1 steps
lem-xt0-1010 : ⟪ (ℓ "丌丌丘") ⟫ʷ ≈ ⟪ (ℓ "丘") ⟫ʷ
lem-xt0-1010 = derive (ℓ "丌丌丘") (ℓ "丘")
  (rw 0 q26 ∷ []) Eq.refl

-- xs0 1010: 2 steps
lem-xs0-1010 : ⟪ (ℓ "丌丘丌") ⟫ʷ ≈ ⟪ (ℓ "丘") ⟫ʷ
lem-xs0-1010 = derive (ℓ "丌丘丌") (ℓ "丘")
  (rw⁻ 1 q28 ∷
   rw 0 q26 ∷ []) Eq.refl

-- xt0 0110: 0 steps
lem-xt0-0110 : ⟪ (ℓ "丌丒丘") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘") ⟫ʷ
lem-xt0-0110 = refl

-- xs0 0110: 2 steps
lem-xs0-0110 : ⟪ (ℓ "丒丘丌") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘") ⟫ʷ
lem-xs0-0110 = derive (ℓ "丒丘丌") (ℓ "丌丒丘")
  (rw⁻ 1 q28 ∷
   rw⁻ 0 q27 ∷ []) Eq.refl

-- xt0 1110: 1 steps
lem-xt0-1110 : ⟪ (ℓ "丌丌丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘") ⟫ʷ
lem-xt0-1110 = derive (ℓ "丌丌丒丘") (ℓ "丒丘")
  (rw 0 q26 ∷ []) Eq.refl

-- xs0 1110: 3 steps
lem-xs0-1110 : ⟪ (ℓ "丌丒丘丌") ⟫ʷ ≈ ⟪ (ℓ "丒丘") ⟫ʷ
lem-xs0-1110 = derive (ℓ "丌丒丘丌") (ℓ "丒丘")
  (rw⁻ 2 q28 ∷
   rw⁻ 1 q27 ∷
   rw 0 q26 ∷ []) Eq.refl

-- xt0 0001: 0 steps
lem-xt0-0001 : ⟪ (ℓ "丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞") ⟫ʷ
lem-xt0-0001 = refl

-- xs0 0001: 1 steps
lem-xs0-0001 : ⟪ (ℓ "丞丌") ⟫ʷ ≈ ⟪ (ℓ "丌丞") ⟫ʷ
lem-xs0-0001 = derive (ℓ "丞丌") (ℓ "丌丞")
  (rw⁻ 0 q29 ∷ []) Eq.refl

-- xt0 1001: 1 steps
lem-xt0-1001 : ⟪ (ℓ "丌丌丞") ⟫ʷ ≈ ⟪ (ℓ "丞") ⟫ʷ
lem-xt0-1001 = derive (ℓ "丌丌丞") (ℓ "丞")
  (rw 0 q26 ∷ []) Eq.refl

-- xs0 1001: 2 steps
lem-xs0-1001 : ⟪ (ℓ "丌丞丌") ⟫ʷ ≈ ⟪ (ℓ "丞") ⟫ʷ
lem-xs0-1001 = derive (ℓ "丌丞丌") (ℓ "丞")
  (rw⁻ 1 q29 ∷
   rw 0 q26 ∷ []) Eq.refl

-- xt0 0101: 0 steps
lem-xt0-0101 : ⟪ (ℓ "丌丒丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒丞") ⟫ʷ
lem-xt0-0101 = refl

-- xs0 0101: 2 steps
lem-xs0-0101 : ⟪ (ℓ "丒丞丌") ⟫ʷ ≈ ⟪ (ℓ "丌丒丞") ⟫ʷ
lem-xs0-0101 = derive (ℓ "丒丞丌") (ℓ "丌丒丞")
  (rw⁻ 1 q29 ∷
   rw⁻ 0 q27 ∷ []) Eq.refl

-- xt0 1101: 1 steps
lem-xt0-1101 : ⟪ (ℓ "丌丌丒丞") ⟫ʷ ≈ ⟪ (ℓ "丒丞") ⟫ʷ
lem-xt0-1101 = derive (ℓ "丌丌丒丞") (ℓ "丒丞")
  (rw 0 q26 ∷ []) Eq.refl

-- xs0 1101: 3 steps
lem-xs0-1101 : ⟪ (ℓ "丌丒丞丌") ⟫ʷ ≈ ⟪ (ℓ "丒丞") ⟫ʷ
lem-xs0-1101 = derive (ℓ "丌丒丞丌") (ℓ "丒丞")
  (rw⁻ 2 q29 ∷
   rw⁻ 1 q27 ∷
   rw 0 q26 ∷ []) Eq.refl

-- xt0 0011: 0 steps
lem-xt0-0011 : ⟪ (ℓ "丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞") ⟫ʷ
lem-xt0-0011 = refl

-- xs0 0011: 2 steps
lem-xs0-0011 : ⟪ (ℓ "丘丞丌") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞") ⟫ʷ
lem-xs0-0011 = derive (ℓ "丘丞丌") (ℓ "丌丘丞")
  (rw⁻ 1 q29 ∷
   rw⁻ 0 q28 ∷ []) Eq.refl

-- xt0 1011: 1 steps
lem-xt0-1011 : ⟪ (ℓ "丌丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞") ⟫ʷ
lem-xt0-1011 = derive (ℓ "丌丌丘丞") (ℓ "丘丞")
  (rw 0 q26 ∷ []) Eq.refl

-- xs0 1011: 3 steps
lem-xs0-1011 : ⟪ (ℓ "丌丘丞丌") ⟫ʷ ≈ ⟪ (ℓ "丘丞") ⟫ʷ
lem-xs0-1011 = derive (ℓ "丌丘丞丌") (ℓ "丘丞")
  (rw⁻ 2 q29 ∷
   rw⁻ 1 q28 ∷
   rw 0 q26 ∷ []) Eq.refl

-- xt0 0111: 0 steps
lem-xt0-0111 : ⟪ (ℓ "丌丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘丞") ⟫ʷ
lem-xt0-0111 = refl

-- xs0 0111: 3 steps
lem-xs0-0111 : ⟪ (ℓ "丒丘丞丌") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘丞") ⟫ʷ
lem-xs0-0111 = derive (ℓ "丒丘丞丌") (ℓ "丌丒丘丞")
  (rw⁻ 2 q29 ∷
   rw⁻ 1 q28 ∷
   rw⁻ 0 q27 ∷ []) Eq.refl

-- xt0 1111: 1 steps
lem-xt0-1111 : ⟪ (ℓ "丌丌丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞") ⟫ʷ
lem-xt0-1111 = derive (ℓ "丌丌丒丘丞") (ℓ "丒丘丞")
  (rw 0 q26 ∷ []) Eq.refl

-- xs0 1111: 4 steps
lem-xs0-1111 : ⟪ (ℓ "丌丒丘丞丌") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞") ⟫ʷ
lem-xs0-1111 = derive (ℓ "丌丒丘丞丌") (ℓ "丒丘丞")
  (rw⁻ 3 q29 ∷
   rw⁻ 2 q28 ∷
   rw⁻ 1 q27 ∷
   rw 0 q26 ∷ []) Eq.refl

-- xt1 0000: 0 steps
lem-xt1-0000 : ⟪ (ℓ "丒") ⟫ʷ ≈ ⟪ (ℓ "丒") ⟫ʷ
lem-xt1-0000 = refl

-- xs1 0000: 0 steps
lem-xs1-0000 : ⟪ (ℓ "丒") ⟫ʷ ≈ ⟪ (ℓ "丒") ⟫ʷ
lem-xs1-0000 = refl

-- xt1 1000: 1 steps
lem-xt1-1000 : ⟪ (ℓ "丒丌") ⟫ʷ ≈ ⟪ (ℓ "丌丒") ⟫ʷ
lem-xt1-1000 = derive (ℓ "丒丌") (ℓ "丌丒")
  (rw⁻ 0 q27 ∷ []) Eq.refl

-- xs1 1000: 0 steps
lem-xs1-1000 : ⟪ (ℓ "丌丒") ⟫ʷ ≈ ⟪ (ℓ "丌丒") ⟫ʷ
lem-xs1-1000 = refl

-- xt1 0100: 1 steps
lem-xt1-0100 : ⟪ (ℓ "丒丒") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xt1-0100 = derive (ℓ "丒丒") []
  (rw 0 q30 ∷ []) Eq.refl

-- xs1 0100: 1 steps
lem-xs1-0100 : ⟪ (ℓ "丒丒") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xs1-0100 = derive (ℓ "丒丒") []
  (rw 0 q30 ∷ []) Eq.refl

-- xt1 1100: 2 steps
lem-xt1-1100 : ⟪ (ℓ "丒丌丒") ⟫ʷ ≈ ⟪ (ℓ "丌") ⟫ʷ
lem-xt1-1100 = derive (ℓ "丒丌丒") (ℓ "丌")
  (rw⁻ 0 q27 ∷
   rw 1 q30 ∷ []) Eq.refl

-- xs1 1100: 1 steps
lem-xs1-1100 : ⟪ (ℓ "丌丒丒") ⟫ʷ ≈ ⟪ (ℓ "丌") ⟫ʷ
lem-xs1-1100 = derive (ℓ "丌丒丒") (ℓ "丌")
  (rw 1 q30 ∷ []) Eq.refl

-- xt1 0010: 0 steps
lem-xt1-0010 : ⟪ (ℓ "丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘") ⟫ʷ
lem-xt1-0010 = refl

-- xs1 0010: 1 steps
lem-xs1-0010 : ⟪ (ℓ "丘丒") ⟫ʷ ≈ ⟪ (ℓ "丒丘") ⟫ʷ
lem-xs1-0010 = derive (ℓ "丘丒") (ℓ "丒丘")
  (rw⁻ 0 q31 ∷ []) Eq.refl

-- xt1 1010: 1 steps
lem-xt1-1010 : ⟪ (ℓ "丒丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘") ⟫ʷ
lem-xt1-1010 = derive (ℓ "丒丌丘") (ℓ "丌丒丘")
  (rw⁻ 0 q27 ∷ []) Eq.refl

-- xs1 1010: 1 steps
lem-xs1-1010 : ⟪ (ℓ "丌丘丒") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘") ⟫ʷ
lem-xs1-1010 = derive (ℓ "丌丘丒") (ℓ "丌丒丘")
  (rw⁻ 1 q31 ∷ []) Eq.refl

-- xt1 0110: 1 steps
lem-xt1-0110 : ⟪ (ℓ "丒丒丘") ⟫ʷ ≈ ⟪ (ℓ "丘") ⟫ʷ
lem-xt1-0110 = derive (ℓ "丒丒丘") (ℓ "丘")
  (rw 0 q30 ∷ []) Eq.refl

-- xs1 0110: 2 steps
lem-xs1-0110 : ⟪ (ℓ "丒丘丒") ⟫ʷ ≈ ⟪ (ℓ "丘") ⟫ʷ
lem-xs1-0110 = derive (ℓ "丒丘丒") (ℓ "丘")
  (rw⁻ 1 q31 ∷
   rw 0 q30 ∷ []) Eq.refl

-- xt1 1110: 2 steps
lem-xt1-1110 : ⟪ (ℓ "丒丌丒丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘") ⟫ʷ
lem-xt1-1110 = derive (ℓ "丒丌丒丘") (ℓ "丌丘")
  (rw⁻ 0 q27 ∷
   rw 1 q30 ∷ []) Eq.refl

-- xs1 1110: 2 steps
lem-xs1-1110 : ⟪ (ℓ "丌丒丘丒") ⟫ʷ ≈ ⟪ (ℓ "丌丘") ⟫ʷ
lem-xs1-1110 = derive (ℓ "丌丒丘丒") (ℓ "丌丘")
  (rw⁻ 2 q31 ∷
   rw 1 q30 ∷ []) Eq.refl

-- xt1 0001: 0 steps
lem-xt1-0001 : ⟪ (ℓ "丒丞") ⟫ʷ ≈ ⟪ (ℓ "丒丞") ⟫ʷ
lem-xt1-0001 = refl

-- xs1 0001: 1 steps
lem-xs1-0001 : ⟪ (ℓ "丞丒") ⟫ʷ ≈ ⟪ (ℓ "丒丞") ⟫ʷ
lem-xs1-0001 = derive (ℓ "丞丒") (ℓ "丒丞")
  (rw⁻ 0 q32 ∷ []) Eq.refl

-- xt1 1001: 1 steps
lem-xt1-1001 : ⟪ (ℓ "丒丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒丞") ⟫ʷ
lem-xt1-1001 = derive (ℓ "丒丌丞") (ℓ "丌丒丞")
  (rw⁻ 0 q27 ∷ []) Eq.refl

-- xs1 1001: 1 steps
lem-xs1-1001 : ⟪ (ℓ "丌丞丒") ⟫ʷ ≈ ⟪ (ℓ "丌丒丞") ⟫ʷ
lem-xs1-1001 = derive (ℓ "丌丞丒") (ℓ "丌丒丞")
  (rw⁻ 1 q32 ∷ []) Eq.refl

-- xt1 0101: 1 steps
lem-xt1-0101 : ⟪ (ℓ "丒丒丞") ⟫ʷ ≈ ⟪ (ℓ "丞") ⟫ʷ
lem-xt1-0101 = derive (ℓ "丒丒丞") (ℓ "丞")
  (rw 0 q30 ∷ []) Eq.refl

-- xs1 0101: 2 steps
lem-xs1-0101 : ⟪ (ℓ "丒丞丒") ⟫ʷ ≈ ⟪ (ℓ "丞") ⟫ʷ
lem-xs1-0101 = derive (ℓ "丒丞丒") (ℓ "丞")
  (rw⁻ 1 q32 ∷
   rw 0 q30 ∷ []) Eq.refl

-- xt1 1101: 2 steps
lem-xt1-1101 : ⟪ (ℓ "丒丌丒丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞") ⟫ʷ
lem-xt1-1101 = derive (ℓ "丒丌丒丞") (ℓ "丌丞")
  (rw⁻ 0 q27 ∷
   rw 1 q30 ∷ []) Eq.refl

-- xs1 1101: 2 steps
lem-xs1-1101 : ⟪ (ℓ "丌丒丞丒") ⟫ʷ ≈ ⟪ (ℓ "丌丞") ⟫ʷ
lem-xs1-1101 = derive (ℓ "丌丒丞丒") (ℓ "丌丞")
  (rw⁻ 2 q32 ∷
   rw 1 q30 ∷ []) Eq.refl

-- xt1 0011: 0 steps
lem-xt1-0011 : ⟪ (ℓ "丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞") ⟫ʷ
lem-xt1-0011 = refl

-- xs1 0011: 2 steps
lem-xs1-0011 : ⟪ (ℓ "丘丞丒") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞") ⟫ʷ
lem-xs1-0011 = derive (ℓ "丘丞丒") (ℓ "丒丘丞")
  (rw⁻ 1 q32 ∷
   rw⁻ 0 q31 ∷ []) Eq.refl

-- xt1 1011: 1 steps
lem-xt1-1011 : ⟪ (ℓ "丒丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘丞") ⟫ʷ
lem-xt1-1011 = derive (ℓ "丒丌丘丞") (ℓ "丌丒丘丞")
  (rw⁻ 0 q27 ∷ []) Eq.refl

-- xs1 1011: 2 steps
lem-xs1-1011 : ⟪ (ℓ "丌丘丞丒") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘丞") ⟫ʷ
lem-xs1-1011 = derive (ℓ "丌丘丞丒") (ℓ "丌丒丘丞")
  (rw⁻ 2 q32 ∷
   rw⁻ 1 q31 ∷ []) Eq.refl

-- xt1 0111: 1 steps
lem-xt1-0111 : ⟪ (ℓ "丒丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞") ⟫ʷ
lem-xt1-0111 = derive (ℓ "丒丒丘丞") (ℓ "丘丞")
  (rw 0 q30 ∷ []) Eq.refl

-- xs1 0111: 3 steps
lem-xs1-0111 : ⟪ (ℓ "丒丘丞丒") ⟫ʷ ≈ ⟪ (ℓ "丘丞") ⟫ʷ
lem-xs1-0111 = derive (ℓ "丒丘丞丒") (ℓ "丘丞")
  (rw⁻ 2 q32 ∷
   rw⁻ 1 q31 ∷
   rw 0 q30 ∷ []) Eq.refl

-- xt1 1111: 2 steps
lem-xt1-1111 : ⟪ (ℓ "丒丌丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞") ⟫ʷ
lem-xt1-1111 = derive (ℓ "丒丌丒丘丞") (ℓ "丌丘丞")
  (rw⁻ 0 q27 ∷
   rw 1 q30 ∷ []) Eq.refl

-- xs1 1111: 3 steps
lem-xs1-1111 : ⟪ (ℓ "丌丒丘丞丒") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞") ⟫ʷ
lem-xs1-1111 = derive (ℓ "丌丒丘丞丒") (ℓ "丌丘丞")
  (rw⁻ 3 q32 ∷
   rw⁻ 2 q31 ∷
   rw 1 q30 ∷ []) Eq.refl

-- xt2 0000: 0 steps
lem-xt2-0000 : ⟪ (ℓ "丘") ⟫ʷ ≈ ⟪ (ℓ "丘") ⟫ʷ
lem-xt2-0000 = refl

-- xs2 0000: 0 steps
lem-xs2-0000 : ⟪ (ℓ "丘") ⟫ʷ ≈ ⟪ (ℓ "丘") ⟫ʷ
lem-xs2-0000 = refl

-- xt2 1000: 1 steps
lem-xt2-1000 : ⟪ (ℓ "丘丌") ⟫ʷ ≈ ⟪ (ℓ "丌丘") ⟫ʷ
lem-xt2-1000 = derive (ℓ "丘丌") (ℓ "丌丘")
  (rw⁻ 0 q28 ∷ []) Eq.refl

-- xs2 1000: 0 steps
lem-xs2-1000 : ⟪ (ℓ "丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘") ⟫ʷ
lem-xs2-1000 = refl

-- xt2 0100: 1 steps
lem-xt2-0100 : ⟪ (ℓ "丘丒") ⟫ʷ ≈ ⟪ (ℓ "丒丘") ⟫ʷ
lem-xt2-0100 = derive (ℓ "丘丒") (ℓ "丒丘")
  (rw⁻ 0 q31 ∷ []) Eq.refl

-- xs2 0100: 0 steps
lem-xs2-0100 : ⟪ (ℓ "丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘") ⟫ʷ
lem-xs2-0100 = refl

-- xt2 1100: 2 steps
lem-xt2-1100 : ⟪ (ℓ "丘丌丒") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘") ⟫ʷ
lem-xt2-1100 = derive (ℓ "丘丌丒") (ℓ "丌丒丘")
  (rw⁻ 0 q28 ∷
   rw⁻ 1 q31 ∷ []) Eq.refl

-- xs2 1100: 0 steps
lem-xs2-1100 : ⟪ (ℓ "丌丒丘") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘") ⟫ʷ
lem-xs2-1100 = refl

-- xt2 0010: 1 steps
lem-xt2-0010 : ⟪ (ℓ "丘丘") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xt2-0010 = derive (ℓ "丘丘") []
  (rw 0 q33 ∷ []) Eq.refl

-- xs2 0010: 1 steps
lem-xs2-0010 : ⟪ (ℓ "丘丘") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xs2-0010 = derive (ℓ "丘丘") []
  (rw 0 q33 ∷ []) Eq.refl

-- xt2 1010: 2 steps
lem-xt2-1010 : ⟪ (ℓ "丘丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌") ⟫ʷ
lem-xt2-1010 = derive (ℓ "丘丌丘") (ℓ "丌")
  (rw⁻ 0 q28 ∷
   rw 1 q33 ∷ []) Eq.refl

-- xs2 1010: 1 steps
lem-xs2-1010 : ⟪ (ℓ "丌丘丘") ⟫ʷ ≈ ⟪ (ℓ "丌") ⟫ʷ
lem-xs2-1010 = derive (ℓ "丌丘丘") (ℓ "丌")
  (rw 1 q33 ∷ []) Eq.refl

-- xt2 0110: 2 steps
lem-xt2-0110 : ⟪ (ℓ "丘丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒") ⟫ʷ
lem-xt2-0110 = derive (ℓ "丘丒丘") (ℓ "丒")
  (rw⁻ 0 q31 ∷
   rw 1 q33 ∷ []) Eq.refl

-- xs2 0110: 1 steps
lem-xs2-0110 : ⟪ (ℓ "丒丘丘") ⟫ʷ ≈ ⟪ (ℓ "丒") ⟫ʷ
lem-xs2-0110 = derive (ℓ "丒丘丘") (ℓ "丒")
  (rw 1 q33 ∷ []) Eq.refl

-- xt2 1110: 3 steps
lem-xt2-1110 : ⟪ (ℓ "丘丌丒丘") ⟫ʷ ≈ ⟪ (ℓ "丌丒") ⟫ʷ
lem-xt2-1110 = derive (ℓ "丘丌丒丘") (ℓ "丌丒")
  (rw⁻ 0 q28 ∷
   rw⁻ 1 q31 ∷
   rw 2 q33 ∷ []) Eq.refl

-- xs2 1110: 1 steps
lem-xs2-1110 : ⟪ (ℓ "丌丒丘丘") ⟫ʷ ≈ ⟪ (ℓ "丌丒") ⟫ʷ
lem-xs2-1110 = derive (ℓ "丌丒丘丘") (ℓ "丌丒")
  (rw 2 q33 ∷ []) Eq.refl

-- xt2 0001: 0 steps
lem-xt2-0001 : ⟪ (ℓ "丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞") ⟫ʷ
lem-xt2-0001 = refl

-- xs2 0001: 1 steps
lem-xs2-0001 : ⟪ (ℓ "丞丘") ⟫ʷ ≈ ⟪ (ℓ "丘丞") ⟫ʷ
lem-xs2-0001 = derive (ℓ "丞丘") (ℓ "丘丞")
  (rw⁻ 0 q34 ∷ []) Eq.refl

-- xt2 1001: 1 steps
lem-xt2-1001 : ⟪ (ℓ "丘丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞") ⟫ʷ
lem-xt2-1001 = derive (ℓ "丘丌丞") (ℓ "丌丘丞")
  (rw⁻ 0 q28 ∷ []) Eq.refl

-- xs2 1001: 1 steps
lem-xs2-1001 : ⟪ (ℓ "丌丞丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞") ⟫ʷ
lem-xs2-1001 = derive (ℓ "丌丞丘") (ℓ "丌丘丞")
  (rw⁻ 1 q34 ∷ []) Eq.refl

-- xt2 0101: 1 steps
lem-xt2-0101 : ⟪ (ℓ "丘丒丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞") ⟫ʷ
lem-xt2-0101 = derive (ℓ "丘丒丞") (ℓ "丒丘丞")
  (rw⁻ 0 q31 ∷ []) Eq.refl

-- xs2 0101: 1 steps
lem-xs2-0101 : ⟪ (ℓ "丒丞丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞") ⟫ʷ
lem-xs2-0101 = derive (ℓ "丒丞丘") (ℓ "丒丘丞")
  (rw⁻ 1 q34 ∷ []) Eq.refl

-- xt2 1101: 2 steps
lem-xt2-1101 : ⟪ (ℓ "丘丌丒丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘丞") ⟫ʷ
lem-xt2-1101 = derive (ℓ "丘丌丒丞") (ℓ "丌丒丘丞")
  (rw⁻ 0 q28 ∷
   rw⁻ 1 q31 ∷ []) Eq.refl

-- xs2 1101: 1 steps
lem-xs2-1101 : ⟪ (ℓ "丌丒丞丘") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘丞") ⟫ʷ
lem-xs2-1101 = derive (ℓ "丌丒丞丘") (ℓ "丌丒丘丞")
  (rw⁻ 2 q34 ∷ []) Eq.refl

-- xt2 0011: 1 steps
lem-xt2-0011 : ⟪ (ℓ "丘丘丞") ⟫ʷ ≈ ⟪ (ℓ "丞") ⟫ʷ
lem-xt2-0011 = derive (ℓ "丘丘丞") (ℓ "丞")
  (rw 0 q33 ∷ []) Eq.refl

-- xs2 0011: 2 steps
lem-xs2-0011 : ⟪ (ℓ "丘丞丘") ⟫ʷ ≈ ⟪ (ℓ "丞") ⟫ʷ
lem-xs2-0011 = derive (ℓ "丘丞丘") (ℓ "丞")
  (rw⁻ 1 q34 ∷
   rw 0 q33 ∷ []) Eq.refl

-- xt2 1011: 2 steps
lem-xt2-1011 : ⟪ (ℓ "丘丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞") ⟫ʷ
lem-xt2-1011 = derive (ℓ "丘丌丘丞") (ℓ "丌丞")
  (rw⁻ 0 q28 ∷
   rw 1 q33 ∷ []) Eq.refl

-- xs2 1011: 2 steps
lem-xs2-1011 : ⟪ (ℓ "丌丘丞丘") ⟫ʷ ≈ ⟪ (ℓ "丌丞") ⟫ʷ
lem-xs2-1011 = derive (ℓ "丌丘丞丘") (ℓ "丌丞")
  (rw⁻ 2 q34 ∷
   rw 1 q33 ∷ []) Eq.refl

-- xt2 0111: 2 steps
lem-xt2-0111 : ⟪ (ℓ "丘丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丞") ⟫ʷ
lem-xt2-0111 = derive (ℓ "丘丒丘丞") (ℓ "丒丞")
  (rw⁻ 0 q31 ∷
   rw 1 q33 ∷ []) Eq.refl

-- xs2 0111: 2 steps
lem-xs2-0111 : ⟪ (ℓ "丒丘丞丘") ⟫ʷ ≈ ⟪ (ℓ "丒丞") ⟫ʷ
lem-xs2-0111 = derive (ℓ "丒丘丞丘") (ℓ "丒丞")
  (rw⁻ 2 q34 ∷
   rw 1 q33 ∷ []) Eq.refl

-- xt2 1111: 3 steps
lem-xt2-1111 : ⟪ (ℓ "丘丌丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒丞") ⟫ʷ
lem-xt2-1111 = derive (ℓ "丘丌丒丘丞") (ℓ "丌丒丞")
  (rw⁻ 0 q28 ∷
   rw⁻ 1 q31 ∷
   rw 2 q33 ∷ []) Eq.refl

-- xs2 1111: 2 steps
lem-xs2-1111 : ⟪ (ℓ "丌丒丘丞丘") ⟫ʷ ≈ ⟪ (ℓ "丌丒丞") ⟫ʷ
lem-xs2-1111 = derive (ℓ "丌丒丘丞丘") (ℓ "丌丒丞")
  (rw⁻ 3 q34 ∷
   rw 2 q33 ∷ []) Eq.refl

-- xt3 0000: 0 steps
lem-xt3-0000 : ⟪ (ℓ "丞") ⟫ʷ ≈ ⟪ (ℓ "丞") ⟫ʷ
lem-xt3-0000 = refl

-- xs3 0000: 0 steps
lem-xs3-0000 : ⟪ (ℓ "丞") ⟫ʷ ≈ ⟪ (ℓ "丞") ⟫ʷ
lem-xs3-0000 = refl

-- xt3 1000: 1 steps
lem-xt3-1000 : ⟪ (ℓ "丞丌") ⟫ʷ ≈ ⟪ (ℓ "丌丞") ⟫ʷ
lem-xt3-1000 = derive (ℓ "丞丌") (ℓ "丌丞")
  (rw⁻ 0 q29 ∷ []) Eq.refl

-- xs3 1000: 0 steps
lem-xs3-1000 : ⟪ (ℓ "丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞") ⟫ʷ
lem-xs3-1000 = refl

-- xt3 0100: 1 steps
lem-xt3-0100 : ⟪ (ℓ "丞丒") ⟫ʷ ≈ ⟪ (ℓ "丒丞") ⟫ʷ
lem-xt3-0100 = derive (ℓ "丞丒") (ℓ "丒丞")
  (rw⁻ 0 q32 ∷ []) Eq.refl

-- xs3 0100: 0 steps
lem-xs3-0100 : ⟪ (ℓ "丒丞") ⟫ʷ ≈ ⟪ (ℓ "丒丞") ⟫ʷ
lem-xs3-0100 = refl

-- xt3 1100: 2 steps
lem-xt3-1100 : ⟪ (ℓ "丞丌丒") ⟫ʷ ≈ ⟪ (ℓ "丌丒丞") ⟫ʷ
lem-xt3-1100 = derive (ℓ "丞丌丒") (ℓ "丌丒丞")
  (rw⁻ 0 q29 ∷
   rw⁻ 1 q32 ∷ []) Eq.refl

-- xs3 1100: 0 steps
lem-xs3-1100 : ⟪ (ℓ "丌丒丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒丞") ⟫ʷ
lem-xs3-1100 = refl

-- xt3 0010: 1 steps
lem-xt3-0010 : ⟪ (ℓ "丞丘") ⟫ʷ ≈ ⟪ (ℓ "丘丞") ⟫ʷ
lem-xt3-0010 = derive (ℓ "丞丘") (ℓ "丘丞")
  (rw⁻ 0 q34 ∷ []) Eq.refl

-- xs3 0010: 0 steps
lem-xs3-0010 : ⟪ (ℓ "丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞") ⟫ʷ
lem-xs3-0010 = refl

-- xt3 1010: 2 steps
lem-xt3-1010 : ⟪ (ℓ "丞丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞") ⟫ʷ
lem-xt3-1010 = derive (ℓ "丞丌丘") (ℓ "丌丘丞")
  (rw⁻ 0 q29 ∷
   rw⁻ 1 q34 ∷ []) Eq.refl

-- xs3 1010: 0 steps
lem-xs3-1010 : ⟪ (ℓ "丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞") ⟫ʷ
lem-xs3-1010 = refl

-- xt3 0110: 2 steps
lem-xt3-0110 : ⟪ (ℓ "丞丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞") ⟫ʷ
lem-xt3-0110 = derive (ℓ "丞丒丘") (ℓ "丒丘丞")
  (rw⁻ 0 q32 ∷
   rw⁻ 1 q34 ∷ []) Eq.refl

-- xs3 0110: 0 steps
lem-xs3-0110 : ⟪ (ℓ "丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞") ⟫ʷ
lem-xs3-0110 = refl

-- xt3 1110: 3 steps
lem-xt3-1110 : ⟪ (ℓ "丞丌丒丘") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘丞") ⟫ʷ
lem-xt3-1110 = derive (ℓ "丞丌丒丘") (ℓ "丌丒丘丞")
  (rw⁻ 0 q29 ∷
   rw⁻ 1 q32 ∷
   rw⁻ 2 q34 ∷ []) Eq.refl

-- xs3 1110: 0 steps
lem-xs3-1110 : ⟪ (ℓ "丌丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘丞") ⟫ʷ
lem-xs3-1110 = refl

-- xt3 0001: 1 steps
lem-xt3-0001 : ⟪ (ℓ "丞丞") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xt3-0001 = derive (ℓ "丞丞") []
  (rw 0 q35 ∷ []) Eq.refl

-- xs3 0001: 1 steps
lem-xs3-0001 : ⟪ (ℓ "丞丞") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xs3-0001 = derive (ℓ "丞丞") []
  (rw 0 q35 ∷ []) Eq.refl

-- xt3 1001: 2 steps
lem-xt3-1001 : ⟪ (ℓ "丞丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌") ⟫ʷ
lem-xt3-1001 = derive (ℓ "丞丌丞") (ℓ "丌")
  (rw⁻ 0 q29 ∷
   rw 1 q35 ∷ []) Eq.refl

-- xs3 1001: 1 steps
lem-xs3-1001 : ⟪ (ℓ "丌丞丞") ⟫ʷ ≈ ⟪ (ℓ "丌") ⟫ʷ
lem-xs3-1001 = derive (ℓ "丌丞丞") (ℓ "丌")
  (rw 1 q35 ∷ []) Eq.refl

-- xt3 0101: 2 steps
lem-xt3-0101 : ⟪ (ℓ "丞丒丞") ⟫ʷ ≈ ⟪ (ℓ "丒") ⟫ʷ
lem-xt3-0101 = derive (ℓ "丞丒丞") (ℓ "丒")
  (rw⁻ 0 q32 ∷
   rw 1 q35 ∷ []) Eq.refl

-- xs3 0101: 1 steps
lem-xs3-0101 : ⟪ (ℓ "丒丞丞") ⟫ʷ ≈ ⟪ (ℓ "丒") ⟫ʷ
lem-xs3-0101 = derive (ℓ "丒丞丞") (ℓ "丒")
  (rw 1 q35 ∷ []) Eq.refl

-- xt3 1101: 3 steps
lem-xt3-1101 : ⟪ (ℓ "丞丌丒丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒") ⟫ʷ
lem-xt3-1101 = derive (ℓ "丞丌丒丞") (ℓ "丌丒")
  (rw⁻ 0 q29 ∷
   rw⁻ 1 q32 ∷
   rw 2 q35 ∷ []) Eq.refl

-- xs3 1101: 1 steps
lem-xs3-1101 : ⟪ (ℓ "丌丒丞丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒") ⟫ʷ
lem-xs3-1101 = derive (ℓ "丌丒丞丞") (ℓ "丌丒")
  (rw 2 q35 ∷ []) Eq.refl

-- xt3 0011: 2 steps
lem-xt3-0011 : ⟪ (ℓ "丞丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘") ⟫ʷ
lem-xt3-0011 = derive (ℓ "丞丘丞") (ℓ "丘")
  (rw⁻ 0 q34 ∷
   rw 1 q35 ∷ []) Eq.refl

-- xs3 0011: 1 steps
lem-xs3-0011 : ⟪ (ℓ "丘丞丞") ⟫ʷ ≈ ⟪ (ℓ "丘") ⟫ʷ
lem-xs3-0011 = derive (ℓ "丘丞丞") (ℓ "丘")
  (rw 1 q35 ∷ []) Eq.refl

-- xt3 1011: 3 steps
lem-xt3-1011 : ⟪ (ℓ "丞丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘") ⟫ʷ
lem-xt3-1011 = derive (ℓ "丞丌丘丞") (ℓ "丌丘")
  (rw⁻ 0 q29 ∷
   rw⁻ 1 q34 ∷
   rw 2 q35 ∷ []) Eq.refl

-- xs3 1011: 1 steps
lem-xs3-1011 : ⟪ (ℓ "丌丘丞丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘") ⟫ʷ
lem-xs3-1011 = derive (ℓ "丌丘丞丞") (ℓ "丌丘")
  (rw 2 q35 ∷ []) Eq.refl

-- xt3 0111: 3 steps
lem-xt3-0111 : ⟪ (ℓ "丞丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘") ⟫ʷ
lem-xt3-0111 = derive (ℓ "丞丒丘丞") (ℓ "丒丘")
  (rw⁻ 0 q32 ∷
   rw⁻ 1 q34 ∷
   rw 2 q35 ∷ []) Eq.refl

-- xs3 0111: 1 steps
lem-xs3-0111 : ⟪ (ℓ "丒丘丞丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘") ⟫ʷ
lem-xs3-0111 = derive (ℓ "丒丘丞丞") (ℓ "丒丘")
  (rw 2 q35 ∷ []) Eq.refl

-- xt3 1111: 4 steps
lem-xt3-1111 : ⟪ (ℓ "丞丌丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘") ⟫ʷ
lem-xt3-1111 = derive (ℓ "丞丌丒丘丞") (ℓ "丌丒丘")
  (rw⁻ 0 q29 ∷
   rw⁻ 1 q32 ∷
   rw⁻ 2 q34 ∷
   rw 3 q35 ∷ []) Eq.refl

-- xs3 1111: 1 steps
lem-xs3-1111 : ⟪ (ℓ "丌丒丘丞丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘") ⟫ʷ
lem-xs3-1111 = derive (ℓ "丌丒丘丞丞") (ℓ "丌丒丘")
  (rw 3 q35 ∷ []) Eq.refl

-- xr0 0000: 0 steps
lem-xr0-0000 : ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xr0-0000 = refl

-- xr0 1000: 0 steps
lem-xr0-1000 : ⟪ (ℓ "丒") ⟫ʷ ≈ ⟪ (ℓ "丒") ⟫ʷ
lem-xr0-1000 = refl

-- xr0 0100: 0 steps
lem-xr0-0100 : ⟪ (ℓ "丌") ⟫ʷ ≈ ⟪ (ℓ "丌") ⟫ʷ
lem-xr0-0100 = refl

-- xr0 1100: 1 steps
lem-xr0-1100 : ⟪ (ℓ "丒丌") ⟫ʷ ≈ ⟪ (ℓ "丌丒") ⟫ʷ
lem-xr0-1100 = derive (ℓ "丒丌") (ℓ "丌丒")
  (rw⁻ 0 q27 ∷ []) Eq.refl

-- xr0 0010: 0 steps
lem-xr0-0010 : ⟪ (ℓ "丘") ⟫ʷ ≈ ⟪ (ℓ "丘") ⟫ʷ
lem-xr0-0010 = refl

-- xr0 1010: 0 steps
lem-xr0-1010 : ⟪ (ℓ "丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘") ⟫ʷ
lem-xr0-1010 = refl

-- xr0 0110: 0 steps
lem-xr0-0110 : ⟪ (ℓ "丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘") ⟫ʷ
lem-xr0-0110 = refl

-- xr0 1110: 1 steps
lem-xr0-1110 : ⟪ (ℓ "丒丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘") ⟫ʷ
lem-xr0-1110 = derive (ℓ "丒丌丘") (ℓ "丌丒丘")
  (rw⁻ 0 q27 ∷ []) Eq.refl

-- xr0 0001: 0 steps
lem-xr0-0001 : ⟪ (ℓ "丞") ⟫ʷ ≈ ⟪ (ℓ "丞") ⟫ʷ
lem-xr0-0001 = refl

-- xr0 1001: 0 steps
lem-xr0-1001 : ⟪ (ℓ "丒丞") ⟫ʷ ≈ ⟪ (ℓ "丒丞") ⟫ʷ
lem-xr0-1001 = refl

-- xr0 0101: 0 steps
lem-xr0-0101 : ⟪ (ℓ "丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞") ⟫ʷ
lem-xr0-0101 = refl

-- xr0 1101: 1 steps
lem-xr0-1101 : ⟪ (ℓ "丒丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒丞") ⟫ʷ
lem-xr0-1101 = derive (ℓ "丒丌丞") (ℓ "丌丒丞")
  (rw⁻ 0 q27 ∷ []) Eq.refl

-- xr0 0011: 0 steps
lem-xr0-0011 : ⟪ (ℓ "丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞") ⟫ʷ
lem-xr0-0011 = refl

-- xr0 1011: 0 steps
lem-xr0-1011 : ⟪ (ℓ "丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞") ⟫ʷ
lem-xr0-1011 = refl

-- xr0 0111: 0 steps
lem-xr0-0111 : ⟪ (ℓ "丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞") ⟫ʷ
lem-xr0-0111 = refl

-- xr0 1111: 1 steps
lem-xr0-1111 : ⟪ (ℓ "丒丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘丞") ⟫ʷ
lem-xr0-1111 = derive (ℓ "丒丌丘丞") (ℓ "丌丒丘丞")
  (rw⁻ 0 q27 ∷ []) Eq.refl

-- xr1 0000: 0 steps
lem-xr1-0000 : ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xr1-0000 = refl

-- xr1 1000: 0 steps
lem-xr1-1000 : ⟪ (ℓ "丌") ⟫ʷ ≈ ⟪ (ℓ "丌") ⟫ʷ
lem-xr1-1000 = refl

-- xr1 0100: 0 steps
lem-xr1-0100 : ⟪ (ℓ "丘") ⟫ʷ ≈ ⟪ (ℓ "丘") ⟫ʷ
lem-xr1-0100 = refl

-- xr1 1100: 0 steps
lem-xr1-1100 : ⟪ (ℓ "丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘") ⟫ʷ
lem-xr1-1100 = refl

-- xr1 0010: 0 steps
lem-xr1-0010 : ⟪ (ℓ "丒") ⟫ʷ ≈ ⟪ (ℓ "丒") ⟫ʷ
lem-xr1-0010 = refl

-- xr1 1010: 0 steps
lem-xr1-1010 : ⟪ (ℓ "丌丒") ⟫ʷ ≈ ⟪ (ℓ "丌丒") ⟫ʷ
lem-xr1-1010 = refl

-- xr1 0110: 1 steps
lem-xr1-0110 : ⟪ (ℓ "丘丒") ⟫ʷ ≈ ⟪ (ℓ "丒丘") ⟫ʷ
lem-xr1-0110 = derive (ℓ "丘丒") (ℓ "丒丘")
  (rw⁻ 0 q31 ∷ []) Eq.refl

-- xr1 1110: 1 steps
lem-xr1-1110 : ⟪ (ℓ "丌丘丒") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘") ⟫ʷ
lem-xr1-1110 = derive (ℓ "丌丘丒") (ℓ "丌丒丘")
  (rw⁻ 1 q31 ∷ []) Eq.refl

-- xr1 0001: 0 steps
lem-xr1-0001 : ⟪ (ℓ "丞") ⟫ʷ ≈ ⟪ (ℓ "丞") ⟫ʷ
lem-xr1-0001 = refl

-- xr1 1001: 0 steps
lem-xr1-1001 : ⟪ (ℓ "丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞") ⟫ʷ
lem-xr1-1001 = refl

-- xr1 0101: 0 steps
lem-xr1-0101 : ⟪ (ℓ "丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞") ⟫ʷ
lem-xr1-0101 = refl

-- xr1 1101: 0 steps
lem-xr1-1101 : ⟪ (ℓ "丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞") ⟫ʷ
lem-xr1-1101 = refl

-- xr1 0011: 0 steps
lem-xr1-0011 : ⟪ (ℓ "丒丞") ⟫ʷ ≈ ⟪ (ℓ "丒丞") ⟫ʷ
lem-xr1-0011 = refl

-- xr1 1011: 0 steps
lem-xr1-1011 : ⟪ (ℓ "丌丒丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒丞") ⟫ʷ
lem-xr1-1011 = refl

-- xr1 0111: 1 steps
lem-xr1-0111 : ⟪ (ℓ "丘丒丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞") ⟫ʷ
lem-xr1-0111 = derive (ℓ "丘丒丞") (ℓ "丒丘丞")
  (rw⁻ 0 q31 ∷ []) Eq.refl

-- xr1 1111: 1 steps
lem-xr1-1111 : ⟪ (ℓ "丌丘丒丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘丞") ⟫ʷ
lem-xr1-1111 = derive (ℓ "丌丘丒丞") (ℓ "丌丒丘丞")
  (rw⁻ 1 q31 ∷ []) Eq.refl

-- xr2 0000: 0 steps
lem-xr2-0000 : ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xr2-0000 = refl

-- xr2 1000: 0 steps
lem-xr2-1000 : ⟪ (ℓ "丌") ⟫ʷ ≈ ⟪ (ℓ "丌") ⟫ʷ
lem-xr2-1000 = refl

-- xr2 0100: 0 steps
lem-xr2-0100 : ⟪ (ℓ "丒") ⟫ʷ ≈ ⟪ (ℓ "丒") ⟫ʷ
lem-xr2-0100 = refl

-- xr2 1100: 0 steps
lem-xr2-1100 : ⟪ (ℓ "丌丒") ⟫ʷ ≈ ⟪ (ℓ "丌丒") ⟫ʷ
lem-xr2-1100 = refl

-- xr2 0010: 0 steps
lem-xr2-0010 : ⟪ (ℓ "丞") ⟫ʷ ≈ ⟪ (ℓ "丞") ⟫ʷ
lem-xr2-0010 = refl

-- xr2 1010: 0 steps
lem-xr2-1010 : ⟪ (ℓ "丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞") ⟫ʷ
lem-xr2-1010 = refl

-- xr2 0110: 0 steps
lem-xr2-0110 : ⟪ (ℓ "丒丞") ⟫ʷ ≈ ⟪ (ℓ "丒丞") ⟫ʷ
lem-xr2-0110 = refl

-- xr2 1110: 0 steps
lem-xr2-1110 : ⟪ (ℓ "丌丒丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒丞") ⟫ʷ
lem-xr2-1110 = refl

-- xr2 0001: 0 steps
lem-xr2-0001 : ⟪ (ℓ "丘") ⟫ʷ ≈ ⟪ (ℓ "丘") ⟫ʷ
lem-xr2-0001 = refl

-- xr2 1001: 0 steps
lem-xr2-1001 : ⟪ (ℓ "丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘") ⟫ʷ
lem-xr2-1001 = refl

-- xr2 0101: 0 steps
lem-xr2-0101 : ⟪ (ℓ "丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘") ⟫ʷ
lem-xr2-0101 = refl

-- xr2 1101: 0 steps
lem-xr2-1101 : ⟪ (ℓ "丌丒丘") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘") ⟫ʷ
lem-xr2-1101 = refl

-- xr2 0011: 1 steps
lem-xr2-0011 : ⟪ (ℓ "丞丘") ⟫ʷ ≈ ⟪ (ℓ "丘丞") ⟫ʷ
lem-xr2-0011 = derive (ℓ "丞丘") (ℓ "丘丞")
  (rw⁻ 0 q34 ∷ []) Eq.refl

-- xr2 1011: 1 steps
lem-xr2-1011 : ⟪ (ℓ "丌丞丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞") ⟫ʷ
lem-xr2-1011 = derive (ℓ "丌丞丘") (ℓ "丌丘丞")
  (rw⁻ 1 q34 ∷ []) Eq.refl

-- xr2 0111: 1 steps
lem-xr2-0111 : ⟪ (ℓ "丒丞丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞") ⟫ʷ
lem-xr2-0111 = derive (ℓ "丒丞丘") (ℓ "丒丘丞")
  (rw⁻ 1 q34 ∷ []) Eq.refl

-- xr2 1111: 1 steps
lem-xr2-1111 : ⟪ (ℓ "丌丒丞丘") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘丞") ⟫ʷ
lem-xr2-1111 = derive (ℓ "丌丒丞丘") (ℓ "丌丒丘丞")
  (rw⁻ 2 q34 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = wE 391 W
  q38 : Eqn
  q38 = wE 392 W

-- b2g 1001R0: 3 steps
lem-b2g-1001R0 : ⟪ (ℓ "丌丞丈上中九丮九下三丌丞") ⟫ʷ ≈ ⟪ (ℓ "丞三下丈丈中九丮九三三上丈丞") ⟫ʷ
lem-b2g-1001R0 = derive (ℓ "丌丞丈上中九丮九下三丌丞") (ℓ "丞三下丈丈中九丮九三三上丈丞")
  (rw 0 q29 ∷
   rw 1 q37 ∷
   rw 9 q38 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = wE 393 W
  q40 : Eqn
  q40 = wE 394 W

-- b2g 0011R2: 3 steps
lem-b2g-0011R2 : ⟪ (ℓ "丘丞且世义乣乊乣丗丕丘丞") ⟫ʷ ≈ ⟪ (ℓ "丞丕丗且且义乣乊乣丕丕世且丞") ⟫ʷ
lem-b2g-0011R2 = derive (ℓ "丘丞且世义乣乊乣丗丕丘丞") (ℓ "丞丕丗且且义乣乊乣丕丕世且丞")
  (rw 0 q34 ∷
   rw 1 q39 ∷
   rw 9 q40 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = wE 127 W
  q42 : Eqn
  q42 = wE 7 W
  q43 : Eqn
  q43 = wE 74 W
  q44 : Eqn
  q44 = wE 334 W
  q45 : Eqn
  q45 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q46 : Eqn
  q46 = wE 395 W

-- pass [X3 CS32 X3] [TOFF203]: 67 steps
lem-pass-X3-CS32-X3-vs-TOFF203 : ⟪ (ℓ "丞义丞乤") ⟫ʷ ≈ ⟪ (ℓ "乤丞义丞") ⟫ʷ
lem-pass-X3-CS32-X3-vs-TOFF203 = derive (ℓ "丞义丞乤") (ℓ "乤丞义丞")
  (rw 4 q20 ∷
   re 3 1 (ℓ "並乥並") ∷
   re 4 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 3 q21 ∷
   rw 4 q13 ∷
   rw 5 q14 ∷
   rw 6 q15 ∷
   rw 7 q14 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q16 ∷
   rw 9 q17 ∷
   rw 10 q16 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q21 ∷
   rw 10 q18 ∷
   rw 11 q19 ∷
   rw 10 q41 ∷
   rw⁻ 9 q21 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q16 ∷
   rw 9 q42 ∷
   rw⁻ 8 q16 ∷
   re 9 3 (ℓ "丽") ∷
   rw 7 q43 ∷
   rw⁻ 6 q15 ∷
   rw 5 q43 ∷
   rw⁻ 4 q13 ∷
   rw⁻ 3 q21 ∷
   rw 4 q44 ∷
   re 4 8 (ℓ "乥") ∷
   rw⁻ 2 q45 ∷
   rw⁻ 1 q13 ∷
   rw⁻ 0 q45 ∷
   rw 1 q46 ∷
   re 1 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 0 q21 ∷
   rw 1 q13 ∷
   rw 2 q14 ∷
   rw 3 q15 ∷
   rw 4 q14 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q16 ∷
   rw 6 q17 ∷
   rw 7 q16 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q21 ∷
   rw 7 q18 ∷
   rw 0 q20 ∷
   rw 1 q21 ∷
   rw 2 q13 ∷
   rw 3 q22 ∷
   rw 4 q15 ∷
   rw 5 q22 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q16 ∷
   rw 7 q23 ∷
   rw 8 q16 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q21 ∷
   rw 8 q24 ∷
   rw 1 q44 ∷
   re 1 8 (ℓ "乥") ∷
   re 0 3 (ℓ "乤") ∷
   rw 1 q45 ∷
   rw 2 q13 ∷
   rw 3 q45 ∷
   rw 4 q19 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = wE 396 W

-- pass [X3 CS32 X3] [CS12]: 1 steps
lem-pass-X3-CS32-X3-vs-CS12 : ⟪ (ℓ "丞义丞丶") ⟫ʷ ≈ ⟪ (ℓ "丶丞义丞") ⟫ʷ
lem-pass-X3-CS32-X3-vs-CS12 = derive (ℓ "丞义丞丶") (ℓ "丶丞义丞")
  (rw 0 q47 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = wE 397 W

-- pass [X3 CS32 X3] [CSd12]: 1 steps
lem-pass-X3-CS32-X3-vs-CSd12 : ⟪ (ℓ "丞义丞丷") ⟫ʷ ≈ ⟪ (ℓ "丷丞义丞") ⟫ʷ
lem-pass-X3-CS32-X3-vs-CSd12 = derive (ℓ "丞义丞丷") (ℓ "丷丞义丞")
  (rw 0 q48 ∷ []) Eq.refl

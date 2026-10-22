{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D019 (W : Ws) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

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
  q6 = eqn (ι1 ∷ Sw23 ∷ []) (Sw23 ∷ ι1 ∷ []) (low-comm ((iI ↑)) (Swap))
  q7 : Eqn
  q7 = wE 385 W

-- sw2 TOFF213: 15 steps
lem-sw2-TOFF213 : ⟪ (Sw23 ∷ Toff213 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
lem-sw2-TOFF213 = derive (Sw23 ∷ Toff213 ∷ Sw23 ∷ []) (Toff312 ∷ [])
  (re 1 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 0 q1 ∷
   rw 1 q2 ∷
   rw 4 q3 ∷
   re 2 3 (CX13 ∷ []) ∷
   rw 3 q4 ∷
   rw 6 q3 ∷
   re 4 3 (CX13 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q1 ∷
   rw⁻ 7 q6 ∷
   rw 0 q7 ∷
   re 0 8 (Toff312 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q8 : Eqn
  q8 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q9 : Eqn
  q9 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q10 : Eqn
  q10 = wE 336 W
  q11 : Eqn
  q11 = wE 368 W

-- sw2 TOFF301: 28 steps
lem-sw2-TOFF301 : ⟪ (Sw23 ∷ Toff301 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ []) ⟫ʷ
lem-sw2-TOFF301 = derive (Sw23 ∷ Toff301 ∷ Sw23 ∷ []) (Toff201 ∷ [])
  (re 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 2 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 1 q1 ∷
   rw 4 q3 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q8 ∷
   rw 6 q3 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q8 ∷
   rw 8 q3 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q1 ∷
   rw⁻ 8 q9 ∷
   rw 9 q5 ∷
   rw 0 q10 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   rw⁻ 2 q8 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw⁻ 4 q8 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q10 ∷
   rw⁻ 7 q9 ∷
   rw 0 q11 ∷
   re 0 8 (Toff201 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = eqn (Sw01 ∷ K3 ∷ []) (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑)))
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q14 : Eqn
  q14 = wE 30 W
  q15 : Eqn
  q15 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q16 : Eqn
  q16 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q17 : Eqn
  q17 = wE 27 W
  q18 : Eqn
  q18 = wE 122 W
  q19 : Eqn
  q19 = wE 31 W
  q20 : Eqn
  q20 = wE 5 W
  q21 : Eqn
  q21 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q22 : Eqn
  q22 = wE 24 W
  q23 : Eqn
  q23 = wE 25 W
  q24 : Eqn
  q24 = wE 124 W
  q25 : Eqn
  q25 = wE 386 W

-- sw2 TOFF302: 47 steps
lem-sw2-TOFF302 : ⟪ (Sw23 ∷ Toff302 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ []) ⟫ʷ
lem-sw2-TOFF302 = derive (Sw23 ∷ Toff302 ∷ Sw23 ∷ []) (Toff203 ∷ [])
  (re 1 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) ∷
   re 2 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 1 q12 ∷
   rw 2 q13 ∷
   rw 3 q14 ∷
   rw 4 q15 ∷
   rw 5 q14 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q16 ∷
   rw 7 q17 ∷
   rw 8 q16 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q12 ∷
   rw 8 q18 ∷
   rw 9 q19 ∷
   rw 0 q10 ∷
   rw 1 q2 ∷
   rw 4 q3 ∷
   re 2 3 (CX03 ∷ []) ∷
   rw 3 q4 ∷
   rw 6 q3 ∷
   re 4 3 (CX03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q10 ∷
   rw⁻ 7 q9 ∷
   rw 0 q20 ∷
   rw 1 q21 ∷
   rw 2 q13 ∷
   re 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 3 q16 ∷
   rw 4 q22 ∷
   rw 5 q16 ∷
   re 3 3 (CX13 ∷ []) ∷
   rw 4 q15 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 q16 ∷
   rw 6 q22 ∷
   rw 7 q16 ∷
   re 5 3 (CX13 ∷ []) ∷
   rw 6 q23 ∷
   rw 7 q21 ∷
   rw 8 q24 ∷
   rw 1 q25 ∷
   re 1 8 (Toff213 ∷ []) ∷
   re 0 3 (Toff203 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 TOFF312: 15 steps
lem-sw2-TOFF312 : ⟪ (Sw23 ∷ Toff312 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ []) ⟫ʷ
lem-sw2-TOFF312 = derive (Sw23 ∷ Toff312 ∷ Sw23 ∷ []) (Toff213 ∷ [])
  (re 1 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 0 q10 ∷
   rw 1 q2 ∷
   rw 4 q3 ∷
   re 2 3 (CX13 ∷ []) ∷
   rw 3 q4 ∷
   rw 6 q3 ∷
   re 4 3 (CX13 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q10 ∷
   rw⁻ 7 q6 ∷
   rw 0 q25 ∷
   re 0 8 (Toff213 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 387 W

-- xx0: 1 steps
lem-xx0 : ⟪ (X0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xx0 = derive (X0 ∷ X0 ∷ []) []
  (rw 0 q26 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = eqn (X0 ∷ X1 ∷ []) (X1 ∷ X0 ∷ []) (low₁-comm (X) (X))

-- xc01: 1 steps
lem-xc01 : ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X0 ∷ []) ⟫ʷ
lem-xc01 = derive (X0 ∷ X1 ∷ []) (X1 ∷ X0 ∷ [])
  (rw 0 q27 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = eqn (X0 ∷ X2 ∷ []) (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑)))

-- xc02: 1 steps
lem-xc02 : ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X0 ∷ []) ⟫ʷ
lem-xc02 = derive (X0 ∷ X2 ∷ []) (X2 ∷ X0 ∷ [])
  (rw 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn (X0 ∷ X3 ∷ []) (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑)))

-- xc03: 1 steps
lem-xc03 : ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X0 ∷ []) ⟫ʷ
lem-xc03 = derive (X0 ∷ X3 ∷ []) (X3 ∷ X0 ∷ [])
  (rw 0 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = wE 388 W

-- xx1: 1 steps
lem-xx1 : ⟪ (X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xx1 = derive (X1 ∷ X1 ∷ []) []
  (rw 0 q30 ∷ []) Eq.refl

-- xc10: 1 steps
lem-xc10 : ⟪ (X1 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xc10 = derive (X1 ∷ X0 ∷ []) (X0 ∷ X1 ∷ [])
  (rw⁻ 0 q27 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = eqn (X1 ∷ X2 ∷ []) (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X))

-- xc12: 1 steps
lem-xc12 : ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X1 ∷ []) ⟫ʷ
lem-xc12 = derive (X1 ∷ X2 ∷ []) (X2 ∷ X1 ∷ [])
  (rw 0 q31 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = eqn (X1 ∷ X3 ∷ []) (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑)))

-- xc13: 1 steps
lem-xc13 : ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X1 ∷ []) ⟫ʷ
lem-xc13 = derive (X1 ∷ X3 ∷ []) (X3 ∷ X1 ∷ [])
  (rw 0 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = wE 389 W

-- xx2: 1 steps
lem-xx2 : ⟪ (X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xx2 = derive (X2 ∷ X2 ∷ []) []
  (rw 0 q33 ∷ []) Eq.refl

-- xc20: 1 steps
lem-xc20 : ⟪ (X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xc20 = derive (X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ [])
  (rw⁻ 0 q28 ∷ []) Eq.refl

-- xc21: 1 steps
lem-xc21 : ⟪ (X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xc21 = derive (X2 ∷ X1 ∷ []) (X1 ∷ X2 ∷ [])
  (rw⁻ 0 q31 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))

-- xc23: 1 steps
lem-xc23 : ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X2 ∷ []) ⟫ʷ
lem-xc23 = derive (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ [])
  (rw 0 q34 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = wE 390 W

-- xx3: 1 steps
lem-xx3 : ⟪ (X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xx3 = derive (X3 ∷ X3 ∷ []) []
  (rw 0 q35 ∷ []) Eq.refl

-- xc30: 1 steps
lem-xc30 : ⟪ (X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xc30 = derive (X3 ∷ X0 ∷ []) (X0 ∷ X3 ∷ [])
  (rw⁻ 0 q29 ∷ []) Eq.refl

-- xc31: 1 steps
lem-xc31 : ⟪ (X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xc31 = derive (X3 ∷ X1 ∷ []) (X1 ∷ X3 ∷ [])
  (rw⁻ 0 q32 ∷ []) Eq.refl

-- xc32: 1 steps
lem-xc32 : ⟪ (X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xc32 = derive (X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ [])
  (rw⁻ 0 q34 ∷ []) Eq.refl

-- swsw0: 1 steps
lem-swsw0 : ⟪ (Sw01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-swsw0 = derive (Sw01 ∷ Sw01 ∷ []) []
  (rw 0 q19 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = wE 14 W

-- swsw1: 1 steps
lem-swsw1 : ⟪ (Sw12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-swsw1 = derive (Sw12 ∷ Sw12 ∷ []) []
  (rw 0 q36 ∷ []) Eq.refl

-- swsw2: 1 steps
lem-swsw2 : ⟪ (Sw23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-swsw2 = derive (Sw23 ∷ Sw23 ∷ []) []
  (rw 0 q5 ∷ []) Eq.refl

-- xt0 0000: 0 steps
lem-xt0-0000 : ⟪ (X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xt0-0000 = refl

-- xs0 0000: 0 steps
lem-xs0-0000 : ⟪ (X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xs0-0000 = refl

-- xt0 1000: 1 steps
lem-xt0-1000 : ⟪ (X0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xt0-1000 = derive (X0 ∷ X0 ∷ []) []
  (rw 0 q26 ∷ []) Eq.refl

-- xs0 1000: 1 steps
lem-xs0-1000 : ⟪ (X0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xs0-1000 = derive (X0 ∷ X0 ∷ []) []
  (rw 0 q26 ∷ []) Eq.refl

-- xt0 0100: 0 steps
lem-xt0-0100 : ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xt0-0100 = refl

-- xs0 0100: 1 steps
lem-xs0-0100 : ⟪ (X1 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xs0-0100 = derive (X1 ∷ X0 ∷ []) (X0 ∷ X1 ∷ [])
  (rw⁻ 0 q27 ∷ []) Eq.refl

-- xt0 1100: 1 steps
lem-xt0-1100 : ⟪ (X0 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xt0-1100 = derive (X0 ∷ X0 ∷ X1 ∷ []) (X1 ∷ [])
  (rw 0 q26 ∷ []) Eq.refl

-- xs0 1100: 2 steps
lem-xs0-1100 : ⟪ (X0 ∷ X1 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xs0-1100 = derive (X0 ∷ X1 ∷ X0 ∷ []) (X1 ∷ [])
  (rw⁻ 1 q27 ∷
   rw 0 q26 ∷ []) Eq.refl

-- xt0 0010: 0 steps
lem-xt0-0010 : ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xt0-0010 = refl

-- xs0 0010: 1 steps
lem-xs0-0010 : ⟪ (X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xs0-0010 = derive (X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ [])
  (rw⁻ 0 q28 ∷ []) Eq.refl

-- xt0 1010: 1 steps
lem-xt0-1010 : ⟪ (X0 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xt0-1010 = derive (X0 ∷ X0 ∷ X2 ∷ []) (X2 ∷ [])
  (rw 0 q26 ∷ []) Eq.refl

-- xs0 1010: 2 steps
lem-xs0-1010 : ⟪ (X0 ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xs0-1010 = derive (X0 ∷ X2 ∷ X0 ∷ []) (X2 ∷ [])
  (rw⁻ 1 q28 ∷
   rw 0 q26 ∷ []) Eq.refl

-- xt0 0110: 0 steps
lem-xt0-0110 : ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xt0-0110 = refl

-- xs0 0110: 2 steps
lem-xs0-0110 : ⟪ (X1 ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xs0-0110 = derive (X1 ∷ X2 ∷ X0 ∷ []) (X0 ∷ X1 ∷ X2 ∷ [])
  (rw⁻ 1 q28 ∷
   rw⁻ 0 q27 ∷ []) Eq.refl

-- xt0 1110: 1 steps
lem-xt0-1110 : ⟪ (X0 ∷ X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xt0-1110 = derive (X0 ∷ X0 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ [])
  (rw 0 q26 ∷ []) Eq.refl

-- xs0 1110: 3 steps
lem-xs0-1110 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xs0-1110 = derive (X0 ∷ X1 ∷ X2 ∷ X0 ∷ []) (X1 ∷ X2 ∷ [])
  (rw⁻ 2 q28 ∷
   rw⁻ 1 q27 ∷
   rw 0 q26 ∷ []) Eq.refl

-- xt0 0001: 0 steps
lem-xt0-0001 : ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xt0-0001 = refl

-- xs0 0001: 1 steps
lem-xs0-0001 : ⟪ (X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xs0-0001 = derive (X3 ∷ X0 ∷ []) (X0 ∷ X3 ∷ [])
  (rw⁻ 0 q29 ∷ []) Eq.refl

-- xt0 1001: 1 steps
lem-xt0-1001 : ⟪ (X0 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xt0-1001 = derive (X0 ∷ X0 ∷ X3 ∷ []) (X3 ∷ [])
  (rw 0 q26 ∷ []) Eq.refl

-- xs0 1001: 2 steps
lem-xs0-1001 : ⟪ (X0 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xs0-1001 = derive (X0 ∷ X3 ∷ X0 ∷ []) (X3 ∷ [])
  (rw⁻ 1 q29 ∷
   rw 0 q26 ∷ []) Eq.refl

-- xt0 0101: 0 steps
lem-xt0-0101 : ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xt0-0101 = refl

-- xs0 0101: 2 steps
lem-xs0-0101 : ⟪ (X1 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xs0-0101 = derive (X1 ∷ X3 ∷ X0 ∷ []) (X0 ∷ X1 ∷ X3 ∷ [])
  (rw⁻ 1 q29 ∷
   rw⁻ 0 q27 ∷ []) Eq.refl

-- xt0 1101: 1 steps
lem-xt0-1101 : ⟪ (X0 ∷ X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xt0-1101 = derive (X0 ∷ X0 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ [])
  (rw 0 q26 ∷ []) Eq.refl

-- xs0 1101: 3 steps
lem-xs0-1101 : ⟪ (X0 ∷ X1 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xs0-1101 = derive (X0 ∷ X1 ∷ X3 ∷ X0 ∷ []) (X1 ∷ X3 ∷ [])
  (rw⁻ 2 q29 ∷
   rw⁻ 1 q27 ∷
   rw 0 q26 ∷ []) Eq.refl

-- xt0 0011: 0 steps
lem-xt0-0011 : ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt0-0011 = refl

-- xs0 0011: 2 steps
lem-xs0-0011 : ⟪ (X2 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs0-0011 = derive (X2 ∷ X3 ∷ X0 ∷ []) (X0 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 1 q29 ∷
   rw⁻ 0 q28 ∷ []) Eq.refl

-- xt0 1011: 1 steps
lem-xt0-1011 : ⟪ (X0 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt0-1011 = derive (X0 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ [])
  (rw 0 q26 ∷ []) Eq.refl

-- xs0 1011: 3 steps
lem-xs0-1011 : ⟪ (X0 ∷ X2 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs0-1011 = derive (X0 ∷ X2 ∷ X3 ∷ X0 ∷ []) (X2 ∷ X3 ∷ [])
  (rw⁻ 2 q29 ∷
   rw⁻ 1 q28 ∷
   rw 0 q26 ∷ []) Eq.refl

-- xt0 0111: 0 steps
lem-xt0-0111 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt0-0111 = refl

-- xs0 0111: 3 steps
lem-xs0-0111 : ⟪ (X1 ∷ X2 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs0-0111 = derive (X1 ∷ X2 ∷ X3 ∷ X0 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 2 q29 ∷
   rw⁻ 1 q28 ∷
   rw⁻ 0 q27 ∷ []) Eq.refl

-- xt0 1111: 1 steps
lem-xt0-1111 : ⟪ (X0 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt0-1111 = derive (X0 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ [])
  (rw 0 q26 ∷ []) Eq.refl

-- xs0 1111: 4 steps
lem-xs0-1111 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs0-1111 = derive (X0 ∷ X1 ∷ X2 ∷ X3 ∷ X0 ∷ []) (X1 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 3 q29 ∷
   rw⁻ 2 q28 ∷
   rw⁻ 1 q27 ∷
   rw 0 q26 ∷ []) Eq.refl

-- xt1 0000: 0 steps
lem-xt1-0000 : ⟪ (X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xt1-0000 = refl

-- xs1 0000: 0 steps
lem-xs1-0000 : ⟪ (X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xs1-0000 = refl

-- xt1 1000: 1 steps
lem-xt1-1000 : ⟪ (X1 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xt1-1000 = derive (X1 ∷ X0 ∷ []) (X0 ∷ X1 ∷ [])
  (rw⁻ 0 q27 ∷ []) Eq.refl

-- xs1 1000: 0 steps
lem-xs1-1000 : ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xs1-1000 = refl

-- xt1 0100: 1 steps
lem-xt1-0100 : ⟪ (X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xt1-0100 = derive (X1 ∷ X1 ∷ []) []
  (rw 0 q30 ∷ []) Eq.refl

-- xs1 0100: 1 steps
lem-xs1-0100 : ⟪ (X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xs1-0100 = derive (X1 ∷ X1 ∷ []) []
  (rw 0 q30 ∷ []) Eq.refl

-- xt1 1100: 2 steps
lem-xt1-1100 : ⟪ (X1 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xt1-1100 = derive (X1 ∷ X0 ∷ X1 ∷ []) (X0 ∷ [])
  (rw⁻ 0 q27 ∷
   rw 1 q30 ∷ []) Eq.refl

-- xs1 1100: 1 steps
lem-xs1-1100 : ⟪ (X0 ∷ X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xs1-1100 = derive (X0 ∷ X1 ∷ X1 ∷ []) (X0 ∷ [])
  (rw 1 q30 ∷ []) Eq.refl

-- xt1 0010: 0 steps
lem-xt1-0010 : ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xt1-0010 = refl

-- xs1 0010: 1 steps
lem-xs1-0010 : ⟪ (X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xs1-0010 = derive (X2 ∷ X1 ∷ []) (X1 ∷ X2 ∷ [])
  (rw⁻ 0 q31 ∷ []) Eq.refl

-- xt1 1010: 1 steps
lem-xt1-1010 : ⟪ (X1 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xt1-1010 = derive (X1 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X1 ∷ X2 ∷ [])
  (rw⁻ 0 q27 ∷ []) Eq.refl

-- xs1 1010: 1 steps
lem-xs1-1010 : ⟪ (X0 ∷ X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xs1-1010 = derive (X0 ∷ X2 ∷ X1 ∷ []) (X0 ∷ X1 ∷ X2 ∷ [])
  (rw⁻ 1 q31 ∷ []) Eq.refl

-- xt1 0110: 1 steps
lem-xt1-0110 : ⟪ (X1 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xt1-0110 = derive (X1 ∷ X1 ∷ X2 ∷ []) (X2 ∷ [])
  (rw 0 q30 ∷ []) Eq.refl

-- xs1 0110: 2 steps
lem-xs1-0110 : ⟪ (X1 ∷ X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xs1-0110 = derive (X1 ∷ X2 ∷ X1 ∷ []) (X2 ∷ [])
  (rw⁻ 1 q31 ∷
   rw 0 q30 ∷ []) Eq.refl

-- xt1 1110: 2 steps
lem-xt1-1110 : ⟪ (X1 ∷ X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xt1-1110 = derive (X1 ∷ X0 ∷ X1 ∷ X2 ∷ []) (X0 ∷ X2 ∷ [])
  (rw⁻ 0 q27 ∷
   rw 1 q30 ∷ []) Eq.refl

-- xs1 1110: 2 steps
lem-xs1-1110 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xs1-1110 = derive (X0 ∷ X1 ∷ X2 ∷ X1 ∷ []) (X0 ∷ X2 ∷ [])
  (rw⁻ 2 q31 ∷
   rw 1 q30 ∷ []) Eq.refl

-- xt1 0001: 0 steps
lem-xt1-0001 : ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xt1-0001 = refl

-- xs1 0001: 1 steps
lem-xs1-0001 : ⟪ (X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xs1-0001 = derive (X3 ∷ X1 ∷ []) (X1 ∷ X3 ∷ [])
  (rw⁻ 0 q32 ∷ []) Eq.refl

-- xt1 1001: 1 steps
lem-xt1-1001 : ⟪ (X1 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xt1-1001 = derive (X1 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X3 ∷ [])
  (rw⁻ 0 q27 ∷ []) Eq.refl

-- xs1 1001: 1 steps
lem-xs1-1001 : ⟪ (X0 ∷ X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xs1-1001 = derive (X0 ∷ X3 ∷ X1 ∷ []) (X0 ∷ X1 ∷ X3 ∷ [])
  (rw⁻ 1 q32 ∷ []) Eq.refl

-- xt1 0101: 1 steps
lem-xt1-0101 : ⟪ (X1 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xt1-0101 = derive (X1 ∷ X1 ∷ X3 ∷ []) (X3 ∷ [])
  (rw 0 q30 ∷ []) Eq.refl

-- xs1 0101: 2 steps
lem-xs1-0101 : ⟪ (X1 ∷ X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xs1-0101 = derive (X1 ∷ X3 ∷ X1 ∷ []) (X3 ∷ [])
  (rw⁻ 1 q32 ∷
   rw 0 q30 ∷ []) Eq.refl

-- xt1 1101: 2 steps
lem-xt1-1101 : ⟪ (X1 ∷ X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xt1-1101 = derive (X1 ∷ X0 ∷ X1 ∷ X3 ∷ []) (X0 ∷ X3 ∷ [])
  (rw⁻ 0 q27 ∷
   rw 1 q30 ∷ []) Eq.refl

-- xs1 1101: 2 steps
lem-xs1-1101 : ⟪ (X0 ∷ X1 ∷ X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xs1-1101 = derive (X0 ∷ X1 ∷ X3 ∷ X1 ∷ []) (X0 ∷ X3 ∷ [])
  (rw⁻ 2 q32 ∷
   rw 1 q30 ∷ []) Eq.refl

-- xt1 0011: 0 steps
lem-xt1-0011 : ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt1-0011 = refl

-- xs1 0011: 2 steps
lem-xs1-0011 : ⟪ (X2 ∷ X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs1-0011 = derive (X2 ∷ X3 ∷ X1 ∷ []) (X1 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 1 q32 ∷
   rw⁻ 0 q31 ∷ []) Eq.refl

-- xt1 1011: 1 steps
lem-xt1-1011 : ⟪ (X1 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt1-1011 = derive (X1 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 0 q27 ∷ []) Eq.refl

-- xs1 1011: 2 steps
lem-xs1-1011 : ⟪ (X0 ∷ X2 ∷ X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs1-1011 = derive (X0 ∷ X2 ∷ X3 ∷ X1 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 2 q32 ∷
   rw⁻ 1 q31 ∷ []) Eq.refl

-- xt1 0111: 1 steps
lem-xt1-0111 : ⟪ (X1 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt1-0111 = derive (X1 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ [])
  (rw 0 q30 ∷ []) Eq.refl

-- xs1 0111: 3 steps
lem-xs1-0111 : ⟪ (X1 ∷ X2 ∷ X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs1-0111 = derive (X1 ∷ X2 ∷ X3 ∷ X1 ∷ []) (X2 ∷ X3 ∷ [])
  (rw⁻ 2 q32 ∷
   rw⁻ 1 q31 ∷
   rw 0 q30 ∷ []) Eq.refl

-- xt1 1111: 2 steps
lem-xt1-1111 : ⟪ (X1 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt1-1111 = derive (X1 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 0 q27 ∷
   rw 1 q30 ∷ []) Eq.refl

-- xs1 1111: 3 steps
lem-xs1-1111 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs1-1111 = derive (X0 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ []) (X0 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 3 q32 ∷
   rw⁻ 2 q31 ∷
   rw 1 q30 ∷ []) Eq.refl

-- xt2 0000: 0 steps
lem-xt2-0000 : ⟪ (X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xt2-0000 = refl

-- xs2 0000: 0 steps
lem-xs2-0000 : ⟪ (X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xs2-0000 = refl

-- xt2 1000: 1 steps
lem-xt2-1000 : ⟪ (X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xt2-1000 = derive (X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ [])
  (rw⁻ 0 q28 ∷ []) Eq.refl

-- xs2 1000: 0 steps
lem-xs2-1000 : ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xs2-1000 = refl

-- xt2 0100: 1 steps
lem-xt2-0100 : ⟪ (X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xt2-0100 = derive (X2 ∷ X1 ∷ []) (X1 ∷ X2 ∷ [])
  (rw⁻ 0 q31 ∷ []) Eq.refl

-- xs2 0100: 0 steps
lem-xs2-0100 : ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xs2-0100 = refl

-- xt2 1100: 2 steps
lem-xt2-1100 : ⟪ (X2 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xt2-1100 = derive (X2 ∷ X0 ∷ X1 ∷ []) (X0 ∷ X1 ∷ X2 ∷ [])
  (rw⁻ 0 q28 ∷
   rw⁻ 1 q31 ∷ []) Eq.refl

-- xs2 1100: 0 steps
lem-xs2-1100 : ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xs2-1100 = refl

-- xt2 0010: 1 steps
lem-xt2-0010 : ⟪ (X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xt2-0010 = derive (X2 ∷ X2 ∷ []) []
  (rw 0 q33 ∷ []) Eq.refl

-- xs2 0010: 1 steps
lem-xs2-0010 : ⟪ (X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xs2-0010 = derive (X2 ∷ X2 ∷ []) []
  (rw 0 q33 ∷ []) Eq.refl

-- xt2 1010: 2 steps
lem-xt2-1010 : ⟪ (X2 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xt2-1010 = derive (X2 ∷ X0 ∷ X2 ∷ []) (X0 ∷ [])
  (rw⁻ 0 q28 ∷
   rw 1 q33 ∷ []) Eq.refl

-- xs2 1010: 1 steps
lem-xs2-1010 : ⟪ (X0 ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xs2-1010 = derive (X0 ∷ X2 ∷ X2 ∷ []) (X0 ∷ [])
  (rw 1 q33 ∷ []) Eq.refl

-- xt2 0110: 2 steps
lem-xt2-0110 : ⟪ (X2 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xt2-0110 = derive (X2 ∷ X1 ∷ X2 ∷ []) (X1 ∷ [])
  (rw⁻ 0 q31 ∷
   rw 1 q33 ∷ []) Eq.refl

-- xs2 0110: 1 steps
lem-xs2-0110 : ⟪ (X1 ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xs2-0110 = derive (X1 ∷ X2 ∷ X2 ∷ []) (X1 ∷ [])
  (rw 1 q33 ∷ []) Eq.refl

-- xt2 1110: 3 steps
lem-xt2-1110 : ⟪ (X2 ∷ X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xt2-1110 = derive (X2 ∷ X0 ∷ X1 ∷ X2 ∷ []) (X0 ∷ X1 ∷ [])
  (rw⁻ 0 q28 ∷
   rw⁻ 1 q31 ∷
   rw 2 q33 ∷ []) Eq.refl

-- xs2 1110: 1 steps
lem-xs2-1110 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xs2-1110 = derive (X0 ∷ X1 ∷ X2 ∷ X2 ∷ []) (X0 ∷ X1 ∷ [])
  (rw 2 q33 ∷ []) Eq.refl

-- xt2 0001: 0 steps
lem-xt2-0001 : ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt2-0001 = refl

-- xs2 0001: 1 steps
lem-xs2-0001 : ⟪ (X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs2-0001 = derive (X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ [])
  (rw⁻ 0 q34 ∷ []) Eq.refl

-- xt2 1001: 1 steps
lem-xt2-1001 : ⟪ (X2 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt2-1001 = derive (X2 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 0 q28 ∷ []) Eq.refl

-- xs2 1001: 1 steps
lem-xs2-1001 : ⟪ (X0 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs2-1001 = derive (X0 ∷ X3 ∷ X2 ∷ []) (X0 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 1 q34 ∷ []) Eq.refl

-- xt2 0101: 1 steps
lem-xt2-0101 : ⟪ (X2 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt2-0101 = derive (X2 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 0 q31 ∷ []) Eq.refl

-- xs2 0101: 1 steps
lem-xs2-0101 : ⟪ (X1 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs2-0101 = derive (X1 ∷ X3 ∷ X2 ∷ []) (X1 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 1 q34 ∷ []) Eq.refl

-- xt2 1101: 2 steps
lem-xt2-1101 : ⟪ (X2 ∷ X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt2-1101 = derive (X2 ∷ X0 ∷ X1 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 0 q28 ∷
   rw⁻ 1 q31 ∷ []) Eq.refl

-- xs2 1101: 1 steps
lem-xs2-1101 : ⟪ (X0 ∷ X1 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs2-1101 = derive (X0 ∷ X1 ∷ X3 ∷ X2 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 2 q34 ∷ []) Eq.refl

-- xt2 0011: 1 steps
lem-xt2-0011 : ⟪ (X2 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xt2-0011 = derive (X2 ∷ X2 ∷ X3 ∷ []) (X3 ∷ [])
  (rw 0 q33 ∷ []) Eq.refl

-- xs2 0011: 2 steps
lem-xs2-0011 : ⟪ (X2 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xs2-0011 = derive (X2 ∷ X3 ∷ X2 ∷ []) (X3 ∷ [])
  (rw⁻ 1 q34 ∷
   rw 0 q33 ∷ []) Eq.refl

-- xt2 1011: 2 steps
lem-xt2-1011 : ⟪ (X2 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xt2-1011 = derive (X2 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X3 ∷ [])
  (rw⁻ 0 q28 ∷
   rw 1 q33 ∷ []) Eq.refl

-- xs2 1011: 2 steps
lem-xs2-1011 : ⟪ (X0 ∷ X2 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xs2-1011 = derive (X0 ∷ X2 ∷ X3 ∷ X2 ∷ []) (X0 ∷ X3 ∷ [])
  (rw⁻ 2 q34 ∷
   rw 1 q33 ∷ []) Eq.refl

-- xt2 0111: 2 steps
lem-xt2-0111 : ⟪ (X2 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xt2-0111 = derive (X2 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X3 ∷ [])
  (rw⁻ 0 q31 ∷
   rw 1 q33 ∷ []) Eq.refl

-- xs2 0111: 2 steps
lem-xs2-0111 : ⟪ (X1 ∷ X2 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xs2-0111 = derive (X1 ∷ X2 ∷ X3 ∷ X2 ∷ []) (X1 ∷ X3 ∷ [])
  (rw⁻ 2 q34 ∷
   rw 1 q33 ∷ []) Eq.refl

-- xt2 1111: 3 steps
lem-xt2-1111 : ⟪ (X2 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xt2-1111 = derive (X2 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X3 ∷ [])
  (rw⁻ 0 q28 ∷
   rw⁻ 1 q31 ∷
   rw 2 q33 ∷ []) Eq.refl

-- xs2 1111: 2 steps
lem-xs2-1111 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xs2-1111 = derive (X0 ∷ X1 ∷ X2 ∷ X3 ∷ X2 ∷ []) (X0 ∷ X1 ∷ X3 ∷ [])
  (rw⁻ 3 q34 ∷
   rw 2 q33 ∷ []) Eq.refl

-- xt3 0000: 0 steps
lem-xt3-0000 : ⟪ (X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xt3-0000 = refl

-- xs3 0000: 0 steps
lem-xs3-0000 : ⟪ (X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xs3-0000 = refl

-- xt3 1000: 1 steps
lem-xt3-1000 : ⟪ (X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xt3-1000 = derive (X3 ∷ X0 ∷ []) (X0 ∷ X3 ∷ [])
  (rw⁻ 0 q29 ∷ []) Eq.refl

-- xs3 1000: 0 steps
lem-xs3-1000 : ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xs3-1000 = refl

-- xt3 0100: 1 steps
lem-xt3-0100 : ⟪ (X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xt3-0100 = derive (X3 ∷ X1 ∷ []) (X1 ∷ X3 ∷ [])
  (rw⁻ 0 q32 ∷ []) Eq.refl

-- xs3 0100: 0 steps
lem-xs3-0100 : ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xs3-0100 = refl

-- xt3 1100: 2 steps
lem-xt3-1100 : ⟪ (X3 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xt3-1100 = derive (X3 ∷ X0 ∷ X1 ∷ []) (X0 ∷ X1 ∷ X3 ∷ [])
  (rw⁻ 0 q29 ∷
   rw⁻ 1 q32 ∷ []) Eq.refl

-- xs3 1100: 0 steps
lem-xs3-1100 : ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xs3-1100 = refl

-- xt3 0010: 1 steps
lem-xt3-0010 : ⟪ (X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt3-0010 = derive (X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ [])
  (rw⁻ 0 q34 ∷ []) Eq.refl

-- xs3 0010: 0 steps
lem-xs3-0010 : ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs3-0010 = refl

-- xt3 1010: 2 steps
lem-xt3-1010 : ⟪ (X3 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt3-1010 = derive (X3 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 0 q29 ∷
   rw⁻ 1 q34 ∷ []) Eq.refl

-- xs3 1010: 0 steps
lem-xs3-1010 : ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs3-1010 = refl

-- xt3 0110: 2 steps
lem-xt3-0110 : ⟪ (X3 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt3-0110 = derive (X3 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 0 q32 ∷
   rw⁻ 1 q34 ∷ []) Eq.refl

-- xs3 0110: 0 steps
lem-xs3-0110 : ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs3-0110 = refl

-- xt3 1110: 3 steps
lem-xt3-1110 : ⟪ (X3 ∷ X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt3-1110 = derive (X3 ∷ X0 ∷ X1 ∷ X2 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 0 q29 ∷
   rw⁻ 1 q32 ∷
   rw⁻ 2 q34 ∷ []) Eq.refl

-- xs3 1110: 0 steps
lem-xs3-1110 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs3-1110 = refl

-- xt3 0001: 1 steps
lem-xt3-0001 : ⟪ (X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xt3-0001 = derive (X3 ∷ X3 ∷ []) []
  (rw 0 q35 ∷ []) Eq.refl

-- xs3 0001: 1 steps
lem-xs3-0001 : ⟪ (X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xs3-0001 = derive (X3 ∷ X3 ∷ []) []
  (rw 0 q35 ∷ []) Eq.refl

-- xt3 1001: 2 steps
lem-xt3-1001 : ⟪ (X3 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xt3-1001 = derive (X3 ∷ X0 ∷ X3 ∷ []) (X0 ∷ [])
  (rw⁻ 0 q29 ∷
   rw 1 q35 ∷ []) Eq.refl

-- xs3 1001: 1 steps
lem-xs3-1001 : ⟪ (X0 ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xs3-1001 = derive (X0 ∷ X3 ∷ X3 ∷ []) (X0 ∷ [])
  (rw 1 q35 ∷ []) Eq.refl

-- xt3 0101: 2 steps
lem-xt3-0101 : ⟪ (X3 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xt3-0101 = derive (X3 ∷ X1 ∷ X3 ∷ []) (X1 ∷ [])
  (rw⁻ 0 q32 ∷
   rw 1 q35 ∷ []) Eq.refl

-- xs3 0101: 1 steps
lem-xs3-0101 : ⟪ (X1 ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xs3-0101 = derive (X1 ∷ X3 ∷ X3 ∷ []) (X1 ∷ [])
  (rw 1 q35 ∷ []) Eq.refl

-- xt3 1101: 3 steps
lem-xt3-1101 : ⟪ (X3 ∷ X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xt3-1101 = derive (X3 ∷ X0 ∷ X1 ∷ X3 ∷ []) (X0 ∷ X1 ∷ [])
  (rw⁻ 0 q29 ∷
   rw⁻ 1 q32 ∷
   rw 2 q35 ∷ []) Eq.refl

-- xs3 1101: 1 steps
lem-xs3-1101 : ⟪ (X0 ∷ X1 ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xs3-1101 = derive (X0 ∷ X1 ∷ X3 ∷ X3 ∷ []) (X0 ∷ X1 ∷ [])
  (rw 2 q35 ∷ []) Eq.refl

-- xt3 0011: 2 steps
lem-xt3-0011 : ⟪ (X3 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xt3-0011 = derive (X3 ∷ X2 ∷ X3 ∷ []) (X2 ∷ [])
  (rw⁻ 0 q34 ∷
   rw 1 q35 ∷ []) Eq.refl

-- xs3 0011: 1 steps
lem-xs3-0011 : ⟪ (X2 ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xs3-0011 = derive (X2 ∷ X3 ∷ X3 ∷ []) (X2 ∷ [])
  (rw 1 q35 ∷ []) Eq.refl

-- xt3 1011: 3 steps
lem-xt3-1011 : ⟪ (X3 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xt3-1011 = derive (X3 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ [])
  (rw⁻ 0 q29 ∷
   rw⁻ 1 q34 ∷
   rw 2 q35 ∷ []) Eq.refl

-- xs3 1011: 1 steps
lem-xs3-1011 : ⟪ (X0 ∷ X2 ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xs3-1011 = derive (X0 ∷ X2 ∷ X3 ∷ X3 ∷ []) (X0 ∷ X2 ∷ [])
  (rw 2 q35 ∷ []) Eq.refl

-- xt3 0111: 3 steps
lem-xt3-0111 : ⟪ (X3 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xt3-0111 = derive (X3 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ [])
  (rw⁻ 0 q32 ∷
   rw⁻ 1 q34 ∷
   rw 2 q35 ∷ []) Eq.refl

-- xs3 0111: 1 steps
lem-xs3-0111 : ⟪ (X1 ∷ X2 ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xs3-0111 = derive (X1 ∷ X2 ∷ X3 ∷ X3 ∷ []) (X1 ∷ X2 ∷ [])
  (rw 2 q35 ∷ []) Eq.refl

-- xt3 1111: 4 steps
lem-xt3-1111 : ⟪ (X3 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xt3-1111 = derive (X3 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X2 ∷ [])
  (rw⁻ 0 q29 ∷
   rw⁻ 1 q32 ∷
   rw⁻ 2 q34 ∷
   rw 3 q35 ∷ []) Eq.refl

-- xs3 1111: 1 steps
lem-xs3-1111 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xs3-1111 = derive (X0 ∷ X1 ∷ X2 ∷ X3 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X2 ∷ [])
  (rw 3 q35 ∷ []) Eq.refl

-- xr0 0000: 0 steps
lem-xr0-0000 : ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xr0-0000 = refl

-- xr0 1000: 0 steps
lem-xr0-1000 : ⟪ (X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xr0-1000 = refl

-- xr0 0100: 0 steps
lem-xr0-0100 : ⟪ (X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xr0-0100 = refl

-- xr0 1100: 1 steps
lem-xr0-1100 : ⟪ (X1 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xr0-1100 = derive (X1 ∷ X0 ∷ []) (X0 ∷ X1 ∷ [])
  (rw⁻ 0 q27 ∷ []) Eq.refl

-- xr0 0010: 0 steps
lem-xr0-0010 : ⟪ (X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xr0-0010 = refl

-- xr0 1010: 0 steps
lem-xr0-1010 : ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xr0-1010 = refl

-- xr0 0110: 0 steps
lem-xr0-0110 : ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xr0-0110 = refl

-- xr0 1110: 1 steps
lem-xr0-1110 : ⟪ (X1 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xr0-1110 = derive (X1 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X1 ∷ X2 ∷ [])
  (rw⁻ 0 q27 ∷ []) Eq.refl

-- xr0 0001: 0 steps
lem-xr0-0001 : ⟪ (X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xr0-0001 = refl

-- xr0 1001: 0 steps
lem-xr0-1001 : ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xr0-1001 = refl

-- xr0 0101: 0 steps
lem-xr0-0101 : ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xr0-0101 = refl

-- xr0 1101: 1 steps
lem-xr0-1101 : ⟪ (X1 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xr0-1101 = derive (X1 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X3 ∷ [])
  (rw⁻ 0 q27 ∷ []) Eq.refl

-- xr0 0011: 0 steps
lem-xr0-0011 : ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr0-0011 = refl

-- xr0 1011: 0 steps
lem-xr0-1011 : ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr0-1011 = refl

-- xr0 0111: 0 steps
lem-xr0-0111 : ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr0-0111 = refl

-- xr0 1111: 1 steps
lem-xr0-1111 : ⟪ (X1 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr0-1111 = derive (X1 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 0 q27 ∷ []) Eq.refl

-- xr1 0000: 0 steps
lem-xr1-0000 : ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xr1-0000 = refl

-- xr1 1000: 0 steps
lem-xr1-1000 : ⟪ (X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xr1-1000 = refl

-- xr1 0100: 0 steps
lem-xr1-0100 : ⟪ (X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xr1-0100 = refl

-- xr1 1100: 0 steps
lem-xr1-1100 : ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xr1-1100 = refl

-- xr1 0010: 0 steps
lem-xr1-0010 : ⟪ (X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xr1-0010 = refl

-- xr1 1010: 0 steps
lem-xr1-1010 : ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xr1-1010 = refl

-- xr1 0110: 1 steps
lem-xr1-0110 : ⟪ (X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xr1-0110 = derive (X2 ∷ X1 ∷ []) (X1 ∷ X2 ∷ [])
  (rw⁻ 0 q31 ∷ []) Eq.refl

-- xr1 1110: 1 steps
lem-xr1-1110 : ⟪ (X0 ∷ X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xr1-1110 = derive (X0 ∷ X2 ∷ X1 ∷ []) (X0 ∷ X1 ∷ X2 ∷ [])
  (rw⁻ 1 q31 ∷ []) Eq.refl

-- xr1 0001: 0 steps
lem-xr1-0001 : ⟪ (X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xr1-0001 = refl

-- xr1 1001: 0 steps
lem-xr1-1001 : ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xr1-1001 = refl

-- xr1 0101: 0 steps
lem-xr1-0101 : ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr1-0101 = refl

-- xr1 1101: 0 steps
lem-xr1-1101 : ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr1-1101 = refl

-- xr1 0011: 0 steps
lem-xr1-0011 : ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xr1-0011 = refl

-- xr1 1011: 0 steps
lem-xr1-1011 : ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xr1-1011 = refl

-- xr1 0111: 1 steps
lem-xr1-0111 : ⟪ (X2 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr1-0111 = derive (X2 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 0 q31 ∷ []) Eq.refl

-- xr1 1111: 1 steps
lem-xr1-1111 : ⟪ (X0 ∷ X2 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr1-1111 = derive (X0 ∷ X2 ∷ X1 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 1 q31 ∷ []) Eq.refl

-- xr2 0000: 0 steps
lem-xr2-0000 : ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xr2-0000 = refl

-- xr2 1000: 0 steps
lem-xr2-1000 : ⟪ (X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xr2-1000 = refl

-- xr2 0100: 0 steps
lem-xr2-0100 : ⟪ (X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xr2-0100 = refl

-- xr2 1100: 0 steps
lem-xr2-1100 : ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xr2-1100 = refl

-- xr2 0010: 0 steps
lem-xr2-0010 : ⟪ (X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xr2-0010 = refl

-- xr2 1010: 0 steps
lem-xr2-1010 : ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xr2-1010 = refl

-- xr2 0110: 0 steps
lem-xr2-0110 : ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xr2-0110 = refl

-- xr2 1110: 0 steps
lem-xr2-1110 : ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xr2-1110 = refl

-- xr2 0001: 0 steps
lem-xr2-0001 : ⟪ (X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xr2-0001 = refl

-- xr2 1001: 0 steps
lem-xr2-1001 : ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xr2-1001 = refl

-- xr2 0101: 0 steps
lem-xr2-0101 : ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xr2-0101 = refl

-- xr2 1101: 0 steps
lem-xr2-1101 : ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xr2-1101 = refl

-- xr2 0011: 1 steps
lem-xr2-0011 : ⟪ (X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr2-0011 = derive (X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ [])
  (rw⁻ 0 q34 ∷ []) Eq.refl

-- xr2 1011: 1 steps
lem-xr2-1011 : ⟪ (X0 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr2-1011 = derive (X0 ∷ X3 ∷ X2 ∷ []) (X0 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 1 q34 ∷ []) Eq.refl

-- xr2 0111: 1 steps
lem-xr2-0111 : ⟪ (X1 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr2-0111 = derive (X1 ∷ X3 ∷ X2 ∷ []) (X1 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 1 q34 ∷ []) Eq.refl

-- xr2 1111: 1 steps
lem-xr2-1111 : ⟪ (X0 ∷ X1 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr2-1111 = derive (X0 ∷ X1 ∷ X3 ∷ X2 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 2 q34 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = wE 391 W
  q38 : Eqn
  q38 = wE 392 W

-- b2g 1001R0: 3 steps
lem-b2g-1001R0 : ⟪ (X0 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) ⟫ʷ
lem-b2g-1001R0 = derive (X0 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X0 ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ [])
  (rw 0 q29 ∷
   rw 1 q37 ∷
   rw 9 q38 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = wE 393 W
  q40 : Eqn
  q40 = wE 394 W

-- b2g 0011R2: 3 steps
lem-b2g-0011R2 : ⟪ (X2 ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ []) ⟫ʷ
lem-b2g-0011R2 = derive (X2 ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X2 ∷ X3 ∷ []) (X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ [])
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
  q45 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q46 : Eqn
  q46 = wE 395 W

-- pass [X3 CS32 X3] [TOFF203]: 67 steps
lem-pass-X3-CS32-X3-vs-TOFF203 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-TOFF203 = derive (X3 ∷ CS23 ∷ X3 ∷ Toff203 ∷ []) (Toff203 ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  (rw 4 q20 ∷
   re 3 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 4 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 3 q21 ∷
   rw 4 q13 ∷
   rw 5 q14 ∷
   rw 6 q15 ∷
   rw 7 q14 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q16 ∷
   rw 9 q17 ∷
   rw 10 q16 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q21 ∷
   rw 10 q18 ∷
   rw 11 q19 ∷
   rw 10 q41 ∷
   rw⁻ 9 q21 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q16 ∷
   rw 9 q42 ∷
   rw⁻ 8 q16 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q43 ∷
   rw⁻ 6 q15 ∷
   rw 5 q43 ∷
   rw⁻ 4 q13 ∷
   rw⁻ 3 q21 ∷
   rw 4 q44 ∷
   re 4 8 (Toff213 ∷ []) ∷
   rw⁻ 2 q45 ∷
   rw⁻ 1 q13 ∷
   rw⁻ 0 q45 ∷
   rw 1 q46 ∷
   re 1 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 0 q21 ∷
   rw 1 q13 ∷
   rw 2 q14 ∷
   rw 3 q15 ∷
   rw 4 q14 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q16 ∷
   rw 6 q17 ∷
   rw 7 q16 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q21 ∷
   rw 7 q18 ∷
   rw 0 q20 ∷
   rw 1 q21 ∷
   rw 2 q13 ∷
   rw 3 q22 ∷
   rw 4 q15 ∷
   rw 5 q22 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q16 ∷
   rw 7 q23 ∷
   rw 8 q16 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q21 ∷
   rw 8 q24 ∷
   rw 1 q44 ∷
   re 1 8 (Toff213 ∷ []) ∷
   re 0 3 (Toff203 ∷ []) ∷
   rw 1 q45 ∷
   rw 2 q13 ∷
   rw 3 q45 ∷
   rw 4 q19 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = wE 396 W

-- pass [X3 CS32 X3] [CS12]: 1 steps
lem-pass-X3-CS32-X3-vs-CS12 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-CS12 = derive (X3 ∷ CS23 ∷ X3 ∷ CS12 ∷ []) (CS12 ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  (rw 0 q47 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = wE 397 W

-- pass [X3 CS32 X3] [CSd12]: 1 steps
lem-pass-X3-CS32-X3-vs-CSd12 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-CSd12 = derive (X3 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  (rw 0 q48 ∷ []) Eq.refl

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D017 (W : Ws) where

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
  q1 = wE 121 W
  q2 : Eqn
  q2 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q3 : Eqn
  q3 = wE 30 W
  q4 : Eqn
  q4 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q5 : Eqn
  q5 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q6 : Eqn
  q6 = wE 27 W
  q7 : Eqn
  q7 = wE 122 W
  q8 : Eqn
  q8 = wE 31 W
  q9 : Eqn
  q9 = wE 123 W
  q10 : Eqn
  q10 = wE 24 W
  q11 : Eqn
  q11 = wE 25 W
  q12 : Eqn
  q12 = wE 124 W
  q13 : Eqn
  q13 = wE 125 W

-- sw0 TOFF023: 30 steps
lem-sw0-TOFF023 : ⟪ (Sw01 ∷ Toff023 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ []) ⟫ʷ
lem-sw0-TOFF023 = derive (Sw01 ∷ Toff023 ∷ Sw01 ∷ []) (Toff123 ∷ [])
  (re 1 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 1 q1 ∷
   rw 2 q2 ∷
   rw 3 q3 ∷
   rw 4 q4 ∷
   rw 5 q3 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q6 ∷
   rw 8 q5 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q1 ∷
   rw 8 q7 ∷
   rw 9 q8 ∷
   rw 0 q9 ∷
   rw 1 q2 ∷
   rw 2 q10 ∷
   rw 3 q4 ∷
   rw 4 q10 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q11 ∷
   rw 7 q5 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 6 q9 ∷
   rw 7 q12 ∷
   rw 0 q13 ∷
   re 0 8 (Toff123 ∷ []) ∷
   rw 1 q8 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = wE 28 W
  q15 : Eqn
  q15 = wE 29 W
  q16 : Eqn
  q16 = wE 272 W

-- sw0 TOFF102: 12 steps
lem-sw0-TOFF102 : ⟪ (Sw01 ∷ Toff102 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
lem-sw0-TOFF102 = derive (Sw01 ∷ Toff102 ∷ Sw01 ∷ []) (Toff012 ∷ [])
  (re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 0 q1 ∷
   rw 1 q6 ∷
   rw 2 q14 ∷
   rw 3 q15 ∷
   rw 4 q14 ∷
   rw 5 q11 ∷
   rw 6 q1 ∷
   rw 7 q12 ∷
   rw 0 q16 ∷
   re 0 8 (Toff012 ∷ []) ∷
   rw 1 q8 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q18 : Eqn
  q18 = wE 1 W
  q19 : Eqn
  q19 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q20 : Eqn
  q20 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q21 : Eqn
  q21 = wE 3 W
  q22 : Eqn
  q22 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q23 : Eqn
  q23 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))
  q24 : Eqn
  q24 = eqn (ι1 ∷ Sw23 ∷ []) (Sw23 ∷ ι1 ∷ []) (low-comm ((iI ↑)) (Swap))

-- sw0 TOFF103: 50 steps
lem-sw0-TOFF103 : ⟪ (Sw01 ∷ Toff103 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ []) ⟫ʷ
lem-sw0-TOFF103 = derive (Sw01 ∷ Toff103 ∷ Sw01 ∷ []) (Toff013 ∷ [])
  (re 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 q17 ∷
   rw 4 q18 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q19 ∷
   rw 6 q18 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q19 ∷
   rw 8 q18 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q17 ∷
   rw⁻ 8 q20 ∷
   rw 9 q21 ∷
   rw 0 q1 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   rw 2 q6 ∷
   rw 3 q5 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q14 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 4 q15 ∷
   rw 5 q5 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q14 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q11 ∷
   rw 7 q5 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 6 q1 ∷
   rw 7 q12 ∷
   rw 0 q18 ∷
   rw⁻ 1 q22 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q21 ∷
   rw⁻ 3 q23 ∷
   re 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q21 ∷
   rw⁻ 5 q23 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q21 ∷
   rw⁻ 7 q22 ∷
   rw⁻ 8 q24 ∷
   rw 1 q16 ∷
   re 1 8 (Toff012 ∷ []) ∷
   re 0 3 (Toff013 ∷ []) ∷
   rw 1 q8 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = wE 5 W

-- sw0 TOFF123: 30 steps
lem-sw0-TOFF123 : ⟪ (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ []) ⟫ʷ
lem-sw0-TOFF123 = derive (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (Toff023 ∷ [])
  (re 1 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 0 q1 ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q3 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q1 ∷
   rw 7 q7 ∷
   rw 0 q25 ∷
   rw 1 q9 ∷
   rw 2 q2 ∷
   rw 3 q10 ∷
   rw 4 q4 ∷
   rw 5 q10 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q11 ∷
   rw 8 q5 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q9 ∷
   rw 8 q12 ∷
   rw 1 q13 ∷
   re 1 8 (Toff123 ∷ []) ∷
   re 0 3 (Toff023 ∷ []) ∷
   rw 1 q8 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q27 : Eqn
  q27 = wE 333 W

-- sw0 TOFF201: 12 steps
lem-sw0-TOFF201 : ⟪ (Sw01 ∷ Toff201 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ []) ⟫ʷ
lem-sw0-TOFF201 = derive (Sw01 ∷ Toff201 ∷ Sw01 ∷ []) (Toff201 ∷ [])
  (re 1 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 0 q26 ∷
   rw 1 q6 ∷
   rw 2 q14 ∷
   rw 3 q15 ∷
   rw 4 q14 ∷
   rw 5 q11 ∷
   rw 6 q26 ∷
   rw 7 q12 ∷
   rw 0 q27 ∷
   re 0 8 (Toff201 ∷ []) ∷
   rw 1 q8 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = wE 334 W

-- sw0 TOFF203: 30 steps
lem-sw0-TOFF203 : ⟪ (Sw01 ∷ Toff203 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ []) ⟫ʷ
lem-sw0-TOFF203 = derive (Sw01 ∷ Toff203 ∷ Sw01 ∷ []) (Toff213 ∷ [])
  (re 1 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 2 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 1 q26 ∷
   rw 2 q2 ∷
   rw 3 q3 ∷
   rw 4 q4 ∷
   rw 5 q3 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q6 ∷
   rw 8 q5 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q26 ∷
   rw 8 q7 ∷
   rw 9 q8 ∷
   rw 0 q26 ∷
   rw 1 q2 ∷
   rw 2 q10 ∷
   rw 3 q4 ∷
   rw 4 q10 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q11 ∷
   rw 7 q5 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 6 q26 ∷
   rw 7 q12 ∷
   rw 0 q28 ∷
   re 0 8 (Toff213 ∷ []) ∷
   rw 1 q8 ∷ []) Eq.refl

-- sw0 TOFF213: 30 steps
lem-sw0-TOFF213 : ⟪ (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ []) ⟫ʷ
lem-sw0-TOFF213 = derive (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) (Toff203 ∷ [])
  (re 1 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 0 q26 ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q3 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q26 ∷
   rw 7 q7 ∷
   rw 0 q25 ∷
   rw 1 q26 ∷
   rw 2 q2 ∷
   rw 3 q10 ∷
   rw 4 q4 ∷
   rw 5 q10 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q11 ∷
   rw 8 q5 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q26 ∷
   rw 8 q12 ∷
   rw 1 q28 ∷
   re 1 8 (Toff213 ∷ []) ∷
   re 0 3 (Toff203 ∷ []) ∷
   rw 1 q8 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 335 W
  q30 : Eqn
  q30 = eqn (Sw01 ∷ K3 ∷ []) (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑)))
  q31 : Eqn
  q31 = wE 336 W

-- sw0 TOFF301: 50 steps
lem-sw0-TOFF301 : ⟪ (Sw01 ∷ Toff301 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ []) ⟫ʷ
lem-sw0-TOFF301 = derive (Sw01 ∷ Toff301 ∷ Sw01 ∷ []) (Toff301 ∷ [])
  (re 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 2 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 1 q29 ∷
   rw 4 q18 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q19 ∷
   rw 6 q18 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q19 ∷
   rw 8 q18 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q29 ∷
   rw⁻ 8 q20 ∷
   rw 9 q21 ∷
   rw 0 q30 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   rw 2 q6 ∷
   rw 3 q5 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q14 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 4 q15 ∷
   rw 5 q5 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q14 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q11 ∷
   rw 7 q5 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 6 q30 ∷
   rw 7 q12 ∷
   rw 0 q18 ∷
   rw 1 q31 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q21 ∷
   rw⁻ 3 q23 ∷
   re 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q21 ∷
   rw⁻ 5 q23 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q21 ∷
   rw 7 q31 ∷
   rw⁻ 8 q24 ∷
   rw 1 q27 ∷
   re 1 8 (Toff201 ∷ []) ∷
   re 0 3 (Toff301 ∷ []) ∷
   rw 1 q8 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = wE 337 W

-- sw0 TOFF302: 30 steps
lem-sw0-TOFF302 : ⟪ (Sw01 ∷ Toff302 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
lem-sw0-TOFF302 = derive (Sw01 ∷ Toff302 ∷ Sw01 ∷ []) (Toff312 ∷ [])
  (re 1 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) ∷
   re 2 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 1 q30 ∷
   rw 2 q2 ∷
   rw 3 q3 ∷
   rw 4 q4 ∷
   rw 5 q3 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q6 ∷
   rw 8 q5 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q30 ∷
   rw 8 q7 ∷
   rw 9 q8 ∷
   rw 0 q30 ∷
   rw 1 q2 ∷
   rw 2 q10 ∷
   rw 3 q4 ∷
   rw 4 q10 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q11 ∷
   rw 7 q5 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 6 q30 ∷
   rw 7 q12 ∷
   rw 0 q32 ∷
   re 0 8 (Toff312 ∷ []) ∷
   rw 1 q8 ∷ []) Eq.refl

-- sw0 TOFF312: 30 steps
lem-sw0-TOFF312 : ⟪ (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ []) ⟫ʷ
lem-sw0-TOFF312 = derive (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) (Toff302 ∷ [])
  (re 1 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 0 q30 ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q3 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q30 ∷
   rw 7 q7 ∷
   rw 0 q25 ∷
   rw 1 q30 ∷
   rw 2 q2 ∷
   rw 3 q10 ∷
   rw 4 q4 ∷
   rw 5 q10 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q11 ∷
   rw 8 q5 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q30 ∷
   rw 8 q12 ∷
   rw 1 q32 ∷
   re 1 8 (Toff312 ∷ []) ∷
   re 0 3 (Toff302 ∷ []) ∷
   rw 1 q8 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = eqn (S0 ∷ Sw12 ∷ []) (Sw12 ∷ S0 ∷ []) (low₁-comm (S) (Swap))
  q34 : Eqn
  q34 = wE 14 W

-- sw1 S0: 2 steps
lem-sw1-S0 : ⟪ (Sw12 ∷ S0 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ []) ⟫ʷ
lem-sw1-S0 = derive (Sw12 ∷ S0 ∷ Sw12 ∷ []) (S0 ∷ [])
  (rw⁻ 0 q33 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = eqn (S0⁻ ∷ Sw12 ∷ []) (Sw12 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) (Swap))

-- sw1 Sd0: 2 steps
lem-sw1-Sd0 : ⟪ (Sw12 ∷ S0⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ []) ⟫ʷ
lem-sw1-Sd0 = derive (Sw12 ∷ S0⁻ ∷ Sw12 ∷ []) (S0⁻ ∷ [])
  (rw⁻ 0 q35 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap))

-- sw1 K0: 2 steps
lem-sw1-K0 : ⟪ (Sw12 ∷ K0 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ []) ⟫ʷ
lem-sw1-K0 = derive (Sw12 ∷ K0 ∷ Sw12 ∷ []) (K0 ∷ [])
  (rw⁻ 0 q36 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = eqn (K0⁻ ∷ Sw12 ∷ []) (Sw12 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) (Swap))

-- sw1 Kd0: 2 steps
lem-sw1-Kd0 : ⟪ (Sw12 ∷ K0⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ []) ⟫ʷ
lem-sw1-Kd0 = derive (Sw12 ∷ K0⁻ ∷ Sw12 ∷ []) (K0⁻ ∷ [])
  (rw⁻ 0 q37 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = eqn (X0 ∷ Sw12 ∷ []) (Sw12 ∷ X0 ∷ []) (low₁-comm (X) (Swap))

-- sw1 X0: 2 steps
lem-sw1-X0 : ⟪ (Sw12 ∷ X0 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-sw1-X0 = derive (Sw12 ∷ X0 ∷ Sw12 ∷ []) (X0 ∷ [])
  (rw⁻ 0 q38 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = eqn (Z0 ∷ Sw12 ∷ []) (Sw12 ∷ Z0 ∷ []) (low₁-comm (Z) (Swap))

-- sw1 Z0: 2 steps
lem-sw1-Z0 : ⟪ (Sw12 ∷ Z0 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Z0 ∷ []) ⟫ʷ
lem-sw1-Z0 = derive (Sw12 ∷ Z0 ∷ Sw12 ∷ []) (Z0 ∷ [])
  (rw⁻ 0 q39 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = wE 338 W

-- sw1 S1: 2 steps
lem-sw1-S1 : ⟪ (Sw12 ∷ S1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ []) ⟫ʷ
lem-sw1-S1 = derive (Sw12 ∷ S1 ∷ Sw12 ∷ []) (S2 ∷ [])
  (rw 0 q40 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = wE 339 W

-- sw1 Sd1: 2 steps
lem-sw1-Sd1 : ⟪ (Sw12 ∷ S1⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ []) ⟫ʷ
lem-sw1-Sd1 = derive (Sw12 ∷ S1⁻ ∷ Sw12 ∷ []) (S2⁻ ∷ [])
  (rw 0 q41 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = wE 340 W

-- sw1 K1: 2 steps
lem-sw1-K1 : ⟪ (Sw12 ∷ K1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ []) ⟫ʷ
lem-sw1-K1 = derive (Sw12 ∷ K1 ∷ Sw12 ∷ []) (K2 ∷ [])
  (rw 0 q42 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = wE 341 W

-- sw1 Kd1: 2 steps
lem-sw1-Kd1 : ⟪ (Sw12 ∷ K1⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ []) ⟫ʷ
lem-sw1-Kd1 = derive (Sw12 ∷ K1⁻ ∷ Sw12 ∷ []) (K2⁻ ∷ [])
  (rw 0 q43 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = wE 222 W

-- sw1 X1: 2 steps
lem-sw1-X1 : ⟪ (Sw12 ∷ X1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-sw1-X1 = derive (Sw12 ∷ X1 ∷ Sw12 ∷ []) (X2 ∷ [])
  (rw 0 q44 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 342 W

-- sw1 Z1: 2 steps
lem-sw1-Z1 : ⟪ (Sw12 ∷ Z1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ []) ⟫ʷ
lem-sw1-Z1 = derive (Sw12 ∷ Z1 ∷ Sw12 ∷ []) (Z2 ∷ [])
  (rw 0 q45 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = wE 343 W

-- sw1 S2: 2 steps
lem-sw1-S2 : ⟪ (Sw12 ∷ S2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ []) ⟫ʷ
lem-sw1-S2 = derive (Sw12 ∷ S2 ∷ Sw12 ∷ []) (S1 ∷ [])
  (rw 0 q46 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = wE 344 W

-- sw1 Sd2: 2 steps
lem-sw1-Sd2 : ⟪ (Sw12 ∷ S2⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ []) ⟫ʷ
lem-sw1-Sd2 = derive (Sw12 ∷ S2⁻ ∷ Sw12 ∷ []) (S1⁻ ∷ [])
  (rw 0 q47 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = wE 345 W

-- sw1 K2: 2 steps
lem-sw1-K2 : ⟪ (Sw12 ∷ K2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ []) ⟫ʷ
lem-sw1-K2 = derive (Sw12 ∷ K2 ∷ Sw12 ∷ []) (K1 ∷ [])
  (rw 0 q48 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = wE 346 W

-- sw1 Kd2: 2 steps
lem-sw1-Kd2 : ⟪ (Sw12 ∷ K2⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ []) ⟫ʷ
lem-sw1-Kd2 = derive (Sw12 ∷ K2⁻ ∷ Sw12 ∷ []) (K1⁻ ∷ [])
  (rw 0 q49 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = wE 347 W

-- sw1 X2: 2 steps
lem-sw1-X2 : ⟪ (Sw12 ∷ X2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-sw1-X2 = derive (Sw12 ∷ X2 ∷ Sw12 ∷ []) (X1 ∷ [])
  (rw 0 q50 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = wE 348 W

-- sw1 Z2: 2 steps
lem-sw1-Z2 : ⟪ (Sw12 ∷ Z2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ []) ⟫ʷ
lem-sw1-Z2 = derive (Sw12 ∷ Z2 ∷ Sw12 ∷ []) (Z1 ∷ [])
  (rw 0 q51 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = eqn (Sw12 ∷ S3 ∷ []) (S3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (S))

-- sw1 S3: 2 steps
lem-sw1-S3 : ⟪ (Sw12 ∷ S3 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ []) ⟫ʷ
lem-sw1-S3 = derive (Sw12 ∷ S3 ∷ Sw12 ∷ []) (S3 ∷ [])
  (rw 0 q52 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = eqn (Sw12 ∷ S3⁻ ∷ []) (S3⁻ ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) ((S • S • S)))

-- sw1 Sd3: 2 steps
lem-sw1-Sd3 : ⟪ (Sw12 ∷ S3⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ []) ⟫ʷ
lem-sw1-Sd3 = derive (Sw12 ∷ S3⁻ ∷ Sw12 ∷ []) (S3⁻ ∷ [])
  (rw 0 q53 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = eqn (Sw12 ∷ K3 ∷ []) (K3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (K))

-- sw1 K3: 2 steps
lem-sw1-K3 : ⟪ (Sw12 ∷ K3 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ []) ⟫ʷ
lem-sw1-K3 = derive (Sw12 ∷ K3 ∷ Sw12 ∷ []) (K3 ∷ [])
  (rw 0 q54 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = eqn (Sw12 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) ((K • iI)))

-- sw1 Kd3: 2 steps
lem-sw1-Kd3 : ⟪ (Sw12 ∷ K3⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ []) ⟫ʷ
lem-sw1-Kd3 = derive (Sw12 ∷ K3⁻ ∷ Sw12 ∷ []) (K3⁻ ∷ [])
  (rw 0 q55 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = eqn (Sw12 ∷ X3 ∷ []) (X3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (X))

-- sw1 X3: 2 steps
lem-sw1-X3 : ⟪ (Sw12 ∷ X3 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-sw1-X3 = derive (Sw12 ∷ X3 ∷ Sw12 ∷ []) (X3 ∷ [])
  (rw 0 q56 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = eqn (Sw12 ∷ Z3 ∷ []) (Z3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (Z))

-- sw1 Z3: 2 steps
lem-sw1-Z3 : ⟪ (Sw12 ∷ Z3 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Z3 ∷ []) ⟫ʷ
lem-sw1-Z3 = derive (Sw12 ∷ Z3 ∷ Sw12 ∷ []) (Z3 ∷ [])
  (rw 0 q57 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = wE 12 W

-- sw1 CS01: 3 steps
lem-sw1-CS01 : ⟪ (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
lem-sw1-CS01 = derive (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (CS02 ∷ [])
  (rw 2 q58 ∷
   re 0 3 (CS02 ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CSd01: 3 steps
lem-sw1-CSd01 : ⟪ (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ []) ⟫ʷ
lem-sw1-CSd01 = derive (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (CS02⁻ ∷ [])
  (rw 2 q58 ∷
   re 0 3 (CS02⁻ ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CZ01: 3 steps
lem-sw1-CZ01 : ⟪ (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ []) ⟫ʷ
lem-sw1-CZ01 = derive (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) (CZ02 ∷ [])
  (rw 2 q58 ∷
   re 0 3 (CZ02 ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CX01: 3 steps
lem-sw1-CX01 : ⟪ (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ []) ⟫ʷ
lem-sw1-CX01 = derive (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (CX02 ∷ [])
  (rw 2 q58 ∷
   re 0 3 (CX02 ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CK01: 3 steps
lem-sw1-CK01 : ⟪ (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ []) ⟫ʷ
lem-sw1-CK01 = derive (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (CK02 ∷ [])
  (rw 2 q58 ∷
   re 0 3 (CK02 ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CKd01: 3 steps
lem-sw1-CKd01 : ⟪ (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK02⁻ ∷ []) ⟫ʷ
lem-sw1-CKd01 = derive (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (CK02⁻ ∷ [])
  (rw 2 q58 ∷
   re 0 3 (CK02⁻ ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CS02: 3 steps
lem-sw1-CS02 : ⟪ (Sw12 ∷ CS02 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
lem-sw1-CS02 = derive (Sw12 ∷ CS02 ∷ Sw12 ∷ []) (CS01 ∷ [])
  (re 1 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 0 q34 ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CSd02: 3 steps
lem-sw1-CSd02 : ⟪ (Sw12 ∷ CS02⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ []) ⟫ʷ
lem-sw1-CSd02 = derive (Sw12 ∷ CS02⁻ ∷ Sw12 ∷ []) (CS01⁻ ∷ [])
  (re 1 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 0 q34 ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CZ02: 3 steps
lem-sw1-CZ02 : ⟪ (Sw12 ∷ CZ02 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ []) ⟫ʷ
lem-sw1-CZ02 = derive (Sw12 ∷ CZ02 ∷ Sw12 ∷ []) (CZ01 ∷ [])
  (re 1 1 (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) ∷
   rw 0 q34 ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CX02: 3 steps
lem-sw1-CX02 : ⟪ (Sw12 ∷ CX02 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ []) ⟫ʷ
lem-sw1-CX02 = derive (Sw12 ∷ CX02 ∷ Sw12 ∷ []) (CX01 ∷ [])
  (re 1 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 0 q34 ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CK02: 3 steps
lem-sw1-CK02 : ⟪ (Sw12 ∷ CK02 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ []) ⟫ʷ
lem-sw1-CK02 = derive (Sw12 ∷ CK02 ∷ Sw12 ∷ []) (CK01 ∷ [])
  (re 1 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 0 q34 ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CKd02: 3 steps
lem-sw1-CKd02 : ⟪ (Sw12 ∷ CK02⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK01⁻ ∷ []) ⟫ʷ
lem-sw1-CKd02 = derive (Sw12 ∷ CK02⁻ ∷ Sw12 ∷ []) (CK01⁻ ∷ [])
  (re 1 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) ∷
   rw 0 q34 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = wE 22 W
  q60 : Eqn
  q60 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q61 : Eqn
  q61 = wE 23 W

-- sw1 CS03: 6 steps
lem-sw1-CS03 : ⟪ (Sw12 ∷ CS03 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ []) ⟫ʷ
lem-sw1-CS03 = derive (Sw12 ∷ CS03 ∷ Sw12 ∷ []) (CS03 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 0 q59 ∷
   rw⁻ 2 q60 ∷
   rw 3 q61 ∷
   re 0 5 (CS03 ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))

-- sw1 CSd03: 6 steps
lem-sw1-CSd03 : ⟪ (Sw12 ∷ CS03⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ []) ⟫ʷ
lem-sw1-CSd03 = derive (Sw12 ∷ CS03⁻ ∷ Sw12 ∷ []) (CS03⁻ ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 0 q59 ∷
   rw⁻ 2 q62 ∷
   rw 3 q61 ∷
   re 0 5 (CS03⁻ ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = eqn (CZ01 ∷ Sw23 ∷ []) (Sw23 ∷ CZ01 ∷ []) (low-comm (CZ) (Swap))

-- sw1 CZ03: 6 steps
lem-sw1-CZ03 : ⟪ (Sw12 ∷ CZ03 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ []) ⟫ʷ
lem-sw1-CZ03 = derive (Sw12 ∷ CZ03 ∷ Sw12 ∷ []) (CZ03 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 0 q59 ∷
   rw⁻ 2 q63 ∷
   rw 3 q61 ∷
   re 0 5 (CZ03 ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CX03: 6 steps
lem-sw1-CX03 : ⟪ (Sw12 ∷ CX03 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ []) ⟫ʷ
lem-sw1-CX03 = derive (Sw12 ∷ CX03 ∷ Sw12 ∷ []) (CX03 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 0 q59 ∷
   rw⁻ 2 q19 ∷
   rw 3 q61 ∷
   re 0 5 (CX03 ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = eqn (CK01 ∷ Sw23 ∷ []) (Sw23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (Swap))

-- sw1 CK03: 6 steps
lem-sw1-CK03 : ⟪ (Sw12 ∷ CK03 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ []) ⟫ʷ
lem-sw1-CK03 = derive (Sw12 ∷ CK03 ∷ Sw12 ∷ []) (CK03 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 0 q59 ∷
   rw⁻ 2 q64 ∷
   rw 3 q61 ∷
   re 0 5 (CK03 ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = eqn (CK01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CK01⁻ ∷ []) (low-comm ((S • CK₀₁)) (Swap))

-- sw1 CKd03: 6 steps
lem-sw1-CKd03 : ⟪ (Sw12 ∷ CK03⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK03⁻ ∷ []) ⟫ʷ
lem-sw1-CKd03 = derive (Sw12 ∷ CK03⁻ ∷ Sw12 ∷ []) (CK03⁻ ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 0 q59 ∷
   rw⁻ 2 q65 ∷
   rw 3 q61 ∷
   re 0 5 (CK03⁻ ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CX10: 3 steps
lem-sw1-CX10 : ⟪ (Sw12 ∷ CX10 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ []) ⟫ʷ
lem-sw1-CX10 = derive (Sw12 ∷ CX10 ∷ Sw12 ∷ []) (CX20 ∷ [])
  (rw 2 q58 ∷
   re 0 3 (CX20 ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CK10: 3 steps
lem-sw1-CK10 : ⟪ (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ []) ⟫ʷ
lem-sw1-CK10 = derive (Sw12 ∷ CK10 ∷ Sw12 ∷ []) (CK20 ∷ [])
  (rw 2 q58 ∷
   re 0 3 (CK20 ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CKd10: 3 steps
lem-sw1-CKd10 : ⟪ (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ []) ⟫ʷ
lem-sw1-CKd10 = derive (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) (CK20⁻ ∷ [])
  (rw 2 q58 ∷
   re 0 3 (CK20⁻ ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = wE 18 W

-- sw1 CS12: 2 steps
lem-sw1-CS12 : ⟪ (Sw12 ∷ CS12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
lem-sw1-CS12 = derive (Sw12 ∷ CS12 ∷ Sw12 ∷ []) (CS12 ∷ [])
  (rw 0 q66 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = wE 19 W

-- sw1 CSd12: 2 steps
lem-sw1-CSd12 : ⟪ (Sw12 ∷ CS12⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ []) ⟫ʷ
lem-sw1-CSd12 = derive (Sw12 ∷ CS12⁻ ∷ Sw12 ∷ []) (CS12⁻ ∷ [])
  (rw 0 q67 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = wE 349 W

-- sw1 CZ12: 2 steps
lem-sw1-CZ12 : ⟪ (Sw12 ∷ CZ12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ []) ⟫ʷ
lem-sw1-CZ12 = derive (Sw12 ∷ CZ12 ∷ Sw12 ∷ []) (CZ12 ∷ [])
  (rw 0 q68 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q69 : Eqn
  q69 = wE 50 W

-- sw1 CX12: 2 steps
lem-sw1-CX12 : ⟪ (Sw12 ∷ CX12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
lem-sw1-CX12 = derive (Sw12 ∷ CX12 ∷ Sw12 ∷ []) (CX21 ∷ [])
  (rw 0 q69 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = wE 350 W

-- sw1 CK12: 2 steps
lem-sw1-CK12 : ⟪ (Sw12 ∷ CK12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ []) ⟫ʷ
lem-sw1-CK12 = derive (Sw12 ∷ CK12 ∷ Sw12 ∷ []) (CK21 ∷ [])
  (rw 0 q70 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = wE 351 W

-- sw1 CKd12: 2 steps
lem-sw1-CKd12 : ⟪ (Sw12 ∷ CK12⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK21⁻ ∷ []) ⟫ʷ
lem-sw1-CKd12 = derive (Sw12 ∷ CK12⁻ ∷ Sw12 ∷ []) (CK21⁻ ∷ [])
  (rw 0 q71 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = wE 20 W

-- sw1 CS13: 2 steps
lem-sw1-CS13 : ⟪ (Sw12 ∷ CS13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ []) ⟫ʷ
lem-sw1-CS13 = derive (Sw12 ∷ CS13 ∷ Sw12 ∷ []) (CS23 ∷ [])
  (rw 0 q72 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q73 : Eqn
  q73 = wE 21 W

-- sw1 CSd13: 2 steps
lem-sw1-CSd13 : ⟪ (Sw12 ∷ CS13⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ []) ⟫ʷ
lem-sw1-CSd13 = derive (Sw12 ∷ CS13⁻ ∷ Sw12 ∷ []) (CS23⁻ ∷ [])
  (rw 0 q73 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q74 : Eqn
  q74 = wE 107 W

-- sw1 CZ13: 2 steps
lem-sw1-CZ13 : ⟪ (Sw12 ∷ CZ13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ []) ⟫ʷ
lem-sw1-CZ13 = derive (Sw12 ∷ CZ13 ∷ Sw12 ∷ []) (CZ23 ∷ [])
  (rw 0 q74 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = wE 157 W

-- sw1 CX13: 2 steps
lem-sw1-CX13 : ⟪ (Sw12 ∷ CX13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ []) ⟫ʷ
lem-sw1-CX13 = derive (Sw12 ∷ CX13 ∷ Sw12 ∷ []) (CX23 ∷ [])
  (rw 0 q75 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = wE 352 W

-- sw1 CK13: 2 steps
lem-sw1-CK13 : ⟪ (Sw12 ∷ CK13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK23 ∷ []) ⟫ʷ
lem-sw1-CK13 = derive (Sw12 ∷ CK13 ∷ Sw12 ∷ []) (CK23 ∷ [])
  (rw 0 q76 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = wE 353 W

-- sw1 CKd13: 2 steps
lem-sw1-CKd13 : ⟪ (Sw12 ∷ CK13⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK23⁻ ∷ []) ⟫ʷ
lem-sw1-CKd13 = derive (Sw12 ∷ CK13⁻ ∷ Sw12 ∷ []) (CK23⁻ ∷ [])
  (rw 0 q77 ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CX20: 3 steps
lem-sw1-CX20 : ⟪ (Sw12 ∷ CX20 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
lem-sw1-CX20 = derive (Sw12 ∷ CX20 ∷ Sw12 ∷ []) (CX10 ∷ [])
  (re 1 1 (Sw12 ∷ CX10 ∷ Sw12 ∷ []) ∷
   rw 0 q34 ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CK20: 3 steps
lem-sw1-CK20 : ⟪ (Sw12 ∷ CK20 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ []) ⟫ʷ
lem-sw1-CK20 = derive (Sw12 ∷ CK20 ∷ Sw12 ∷ []) (CK10 ∷ [])
  (re 1 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 0 q34 ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CKd20: 3 steps
lem-sw1-CKd20 : ⟪ (Sw12 ∷ CK20⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ []) ⟫ʷ
lem-sw1-CKd20 = derive (Sw12 ∷ CK20⁻ ∷ Sw12 ∷ []) (CK10⁻ ∷ [])
  (re 1 1 (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) ∷
   rw 0 q34 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = wE 354 W

-- sw1 CX21: 2 steps
lem-sw1-CX21 : ⟪ (Sw12 ∷ CX21 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ []) ⟫ʷ
lem-sw1-CX21 = derive (Sw12 ∷ CX21 ∷ Sw12 ∷ []) (CX12 ∷ [])
  (rw 0 q78 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = wE 355 W

-- sw1 CK21: 2 steps
lem-sw1-CK21 : ⟪ (Sw12 ∷ CK21 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK12 ∷ []) ⟫ʷ
lem-sw1-CK21 = derive (Sw12 ∷ CK21 ∷ Sw12 ∷ []) (CK12 ∷ [])
  (rw 0 q79 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q80 : Eqn
  q80 = wE 356 W

-- sw1 CKd21: 2 steps
lem-sw1-CKd21 : ⟪ (Sw12 ∷ CK21⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK12⁻ ∷ []) ⟫ʷ
lem-sw1-CKd21 = derive (Sw12 ∷ CK21⁻ ∷ Sw12 ∷ []) (CK12⁻ ∷ [])
  (rw 0 q80 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = wE 49 W

-- sw1 CS23: 2 steps
lem-sw1-CS23 : ⟪ (Sw12 ∷ CS23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ []) ⟫ʷ
lem-sw1-CS23 = derive (Sw12 ∷ CS23 ∷ Sw12 ∷ []) (CS13 ∷ [])
  (rw 0 q81 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = wE 51 W

-- sw1 CSd23: 2 steps
lem-sw1-CSd23 : ⟪ (Sw12 ∷ CS23⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ []) ⟫ʷ
lem-sw1-CSd23 = derive (Sw12 ∷ CS23⁻ ∷ Sw12 ∷ []) (CS13⁻ ∷ [])
  (rw 0 q82 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q83 : Eqn
  q83 = wE 108 W

-- sw1 CZ23: 2 steps
lem-sw1-CZ23 : ⟪ (Sw12 ∷ CZ23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ []) ⟫ʷ
lem-sw1-CZ23 = derive (Sw12 ∷ CZ23 ∷ Sw12 ∷ []) (CZ13 ∷ [])
  (rw 0 q83 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = wE 158 W

-- sw1 CX23: 2 steps
lem-sw1-CX23 : ⟪ (Sw12 ∷ CX23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ []) ⟫ʷ
lem-sw1-CX23 = derive (Sw12 ∷ CX23 ∷ Sw12 ∷ []) (CX13 ∷ [])
  (rw 0 q84 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = wE 357 W

-- sw1 CK23: 2 steps
lem-sw1-CK23 : ⟪ (Sw12 ∷ CK23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK13 ∷ []) ⟫ʷ
lem-sw1-CK23 = derive (Sw12 ∷ CK23 ∷ Sw12 ∷ []) (CK13 ∷ [])
  (rw 0 q85 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = wE 358 W

-- sw1 CKd23: 2 steps
lem-sw1-CKd23 : ⟪ (Sw12 ∷ CK23⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK13⁻ ∷ []) ⟫ʷ
lem-sw1-CKd23 = derive (Sw12 ∷ CK23⁻ ∷ Sw12 ∷ []) (CK13⁻ ∷ [])
  (rw 0 q86 ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CX30: 6 steps
lem-sw1-CX30 : ⟪ (Sw12 ∷ CX30 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ []) ⟫ʷ
lem-sw1-CX30 = derive (Sw12 ∷ CX30 ∷ Sw12 ∷ []) (CX30 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 0 q59 ∷
   rw⁻ 2 q23 ∷
   rw 3 q61 ∷
   re 0 5 (CX30 ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q87 : Eqn
  q87 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))

-- sw1 CK30: 6 steps
lem-sw1-CK30 : ⟪ (Sw12 ∷ CK30 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK30 ∷ []) ⟫ʷ
lem-sw1-CK30 = derive (Sw12 ∷ CK30 ∷ Sw12 ∷ []) (CK30 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 0 q59 ∷
   rw⁻ 2 q87 ∷
   rw 3 q61 ∷
   re 0 5 (CK30 ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q88 : Eqn
  q88 = eqn (CK10⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap))

-- sw1 CKd30: 6 steps
lem-sw1-CKd30 : ⟪ (Sw12 ∷ CK30⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK30⁻ ∷ []) ⟫ʷ
lem-sw1-CKd30 = derive (Sw12 ∷ CK30⁻ ∷ Sw12 ∷ []) (CK30⁻ ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 0 q59 ∷
   rw⁻ 2 q88 ∷
   rw 3 q61 ∷
   re 0 5 (CK30⁻ ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = wE 113 W

-- sw1 CX31: 2 steps
lem-sw1-CX31 : ⟪ (Sw12 ∷ CX31 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ []) ⟫ʷ
lem-sw1-CX31 = derive (Sw12 ∷ CX31 ∷ Sw12 ∷ []) (CX32 ∷ [])
  (rw 0 q89 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = wE 359 W

-- sw1 CK31: 2 steps
lem-sw1-CK31 : ⟪ (Sw12 ∷ CK31 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK32 ∷ []) ⟫ʷ
lem-sw1-CK31 = derive (Sw12 ∷ CK31 ∷ Sw12 ∷ []) (CK32 ∷ [])
  (rw 0 q90 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q91 : Eqn
  q91 = wE 360 W

-- sw1 CKd31: 2 steps
lem-sw1-CKd31 : ⟪ (Sw12 ∷ CK31⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK32⁻ ∷ []) ⟫ʷ
lem-sw1-CKd31 = derive (Sw12 ∷ CK31⁻ ∷ Sw12 ∷ []) (CK32⁻ ∷ [])
  (rw 0 q91 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = wE 114 W

-- sw1 CX32: 2 steps
lem-sw1-CX32 : ⟪ (Sw12 ∷ CX32 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ []) ⟫ʷ
lem-sw1-CX32 = derive (Sw12 ∷ CX32 ∷ Sw12 ∷ []) (CX31 ∷ [])
  (rw 0 q92 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q93 : Eqn
  q93 = wE 361 W

-- sw1 CK32: 2 steps
lem-sw1-CK32 : ⟪ (Sw12 ∷ CK32 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK31 ∷ []) ⟫ʷ
lem-sw1-CK32 = derive (Sw12 ∷ CK32 ∷ Sw12 ∷ []) (CK31 ∷ [])
  (rw 0 q93 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q94 : Eqn
  q94 = wE 362 W

-- sw1 CKd32: 2 steps
lem-sw1-CKd32 : ⟪ (Sw12 ∷ CK32⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK31⁻ ∷ []) ⟫ʷ
lem-sw1-CKd32 = derive (Sw12 ∷ CK32⁻ ∷ Sw12 ∷ []) (CK31⁻ ∷ [])
  (rw 0 q94 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q95 : Eqn
  q95 = wE 17 W

-- sw1 CCZ012: 12 steps
lem-sw1-CCZ012 : ⟪ (Sw12 ∷ CCZ012 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
lem-sw1-CCZ012 = derive (Sw12 ∷ CCZ012 ∷ Sw12 ∷ []) (CCZ012 ∷ [])
  (re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 0 q66 ∷
   rw 3 q58 ∷
   re 1 3 (CX02 ∷ []) ∷
   rw 2 q67 ∷
   rw 5 q58 ∷
   re 3 3 (CX02 ∷ []) ∷
   re 5 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 4 q34 ∷
   rw 0 q95 ∷
   re 0 5 (CCZ012 ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q96 : Eqn
  q96 = wE 26 W

-- sw1 CCZ013: 36 steps
lem-sw1-CCZ013 : ⟪ (Sw12 ∷ CCZ013 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ []) ⟫ʷ
lem-sw1-CCZ013 = derive (Sw12 ∷ CCZ013 ∷ Sw12 ∷ []) (CCZ023 ∷ [])
  (re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q18 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q19 ∷
   rw 5 q18 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q19 ∷
   rw 7 q18 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q21 ∷
   rw 0 q72 ∷
   rw 3 q58 ∷
   re 1 3 (CX02 ∷ []) ∷
   rw 2 q73 ∷
   rw 5 q58 ∷
   re 3 3 (CX02 ∷ []) ∷
   re 5 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 4 q59 ∷
   rw⁻ 6 q60 ∷
   rw 7 q61 ∷
   re 4 5 (CS03 ∷ []) ∷
   rw 0 q25 ∷
   rw 1 q2 ∷
   rw 2 q10 ∷
   rw 3 q4 ∷
   rw 4 q10 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q11 ∷
   rw 7 q5 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 1 q96 ∷
   re 1 5 (CCZ123 ∷ []) ∷
   re 0 3 (CCZ023 ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q97 : Eqn
  q97 = wE 43 W

-- sw1 CCZ023: 36 steps
lem-sw1-CCZ023 : ⟪ (Sw12 ∷ CCZ023 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ []) ⟫ʷ
lem-sw1-CCZ023 = derive (Sw12 ∷ CCZ023 ∷ Sw12 ∷ []) (CCZ013 ∷ [])
  (re 1 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q3 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q8 ∷
   rw 0 q81 ∷
   re 2 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 1 q34 ∷
   rw 2 q82 ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 q34 ∷
   re 5 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 4 q59 ∷
   rw⁻ 6 q60 ∷
   rw 7 q61 ∷
   re 4 5 (CS03 ∷ []) ∷
   rw 0 q18 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q21 ∷
   rw⁻ 2 q19 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q21 ∷
   rw⁻ 4 q19 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q21 ∷
   rw 1 q97 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   re 0 3 (CCZ013 ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q98 : Eqn
  q98 = wE 52 W

-- sw1 CCZ123: 9 steps
lem-sw1-CCZ123 : ⟪ (Sw12 ∷ CCZ123 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
lem-sw1-CCZ123 = derive (Sw12 ∷ CCZ123 ∷ Sw12 ∷ []) (CCZ123 ∷ [])
  (re 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 0 q81 ∷
   rw 1 q69 ∷
   rw 2 q82 ∷
   rw 3 q69 ∷
   rw 4 q72 ∷
   rw 0 q98 ∷
   re 0 5 (CCZ123 ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q99 : Eqn
  q99 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q100 : Eqn
  q100 = wE 46 W

-- sw1 TOFF012: 15 steps
lem-sw1-TOFF012 : ⟪ (Sw12 ∷ Toff012 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
lem-sw1-TOFF012 = derive (Sw12 ∷ Toff012 ∷ Sw12 ∷ []) (Toff012 ∷ [])
  (re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q36 ∷
   rw 1 q66 ∷
   rw 4 q58 ∷
   re 2 3 (CX02 ∷ []) ∷
   rw 3 q67 ∷
   rw 6 q58 ∷
   re 4 3 (CX02 ∷ []) ∷
   re 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 5 q34 ∷
   rw⁻ 6 q36 ∷
   rw⁻ 7 q99 ∷
   rw 0 q100 ∷
   re 0 8 (Toff012 ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 TOFF013: 45 steps
lem-sw1-TOFF013 : ⟪ (Sw12 ∷ Toff013 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ []) ⟫ʷ
lem-sw1-TOFF013 = derive (Sw12 ∷ Toff013 ∷ Sw12 ∷ []) (Toff023 ∷ [])
  (re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q22 ∷
   rw 4 q18 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q19 ∷
   rw 6 q18 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q19 ∷
   rw 8 q18 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q22 ∷
   rw⁻ 8 q20 ∷
   rw 9 q21 ∷
   rw⁻ 0 q36 ∷
   rw 1 q72 ∷
   rw 4 q58 ∷
   re 2 3 (CX02 ∷ []) ∷
   rw 3 q73 ∷
   rw 6 q58 ∷
   re 4 3 (CX02 ∷ []) ∷
   re 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 5 q59 ∷
   rw⁻ 7 q60 ∷
   rw 8 q61 ∷
   re 5 5 (CS03 ∷ []) ∷
   rw⁻ 6 q36 ∷
   rw⁻ 7 q99 ∷
   rw 0 q25 ∷
   rw 1 q9 ∷
   rw 2 q2 ∷
   rw 3 q10 ∷
   rw 4 q4 ∷
   rw 5 q10 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q11 ∷
   rw 8 q5 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q9 ∷
   rw 8 q12 ∷
   rw 1 q13 ∷
   re 1 8 (Toff123 ∷ []) ∷
   re 0 3 (Toff023 ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q101 : Eqn
  q101 = wE 56 W

-- sw1 TOFF023: 45 steps
lem-sw1-TOFF023 : ⟪ (Sw12 ∷ Toff023 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ []) ⟫ʷ
lem-sw1-TOFF023 = derive (Sw12 ∷ Toff023 ∷ Sw12 ∷ []) (Toff013 ∷ [])
  (re 1 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 1 q1 ∷
   rw 2 q2 ∷
   rw 3 q3 ∷
   rw 4 q4 ∷
   rw 5 q3 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q6 ∷
   rw 8 q5 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q1 ∷
   rw 8 q7 ∷
   rw 9 q8 ∷
   rw⁻ 0 q36 ∷
   rw 1 q81 ∷
   re 3 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 2 q34 ∷
   rw 3 q82 ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 q34 ∷
   re 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 5 q59 ∷
   rw⁻ 7 q60 ∷
   rw 8 q61 ∷
   re 5 5 (CS03 ∷ []) ∷
   rw⁻ 6 q36 ∷
   rw⁻ 7 q99 ∷
   rw 0 q18 ∷
   rw⁻ 1 q22 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q21 ∷
   rw⁻ 3 q19 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q21 ∷
   rw⁻ 5 q19 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q21 ∷
   rw⁻ 7 q22 ∷
   rw⁻ 8 q20 ∷
   rw 1 q101 ∷
   re 1 8 (Toff012 ∷ []) ∷
   re 0 3 (Toff013 ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q102 : Eqn
  q102 = wE 363 W

-- sw1 TOFF102: 15 steps
lem-sw1-TOFF102 : ⟪ (Sw12 ∷ Toff102 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ []) ⟫ʷ
lem-sw1-TOFF102 = derive (Sw12 ∷ Toff102 ∷ Sw12 ∷ []) (Toff201 ∷ [])
  (re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 0 q42 ∷
   rw 1 q66 ∷
   rw 4 q58 ∷
   re 2 3 (CX02 ∷ []) ∷
   rw 3 q67 ∷
   rw 6 q58 ∷
   re 4 3 (CX02 ∷ []) ∷
   re 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 5 q34 ∷
   rw 6 q42 ∷
   rw⁻ 7 q99 ∷
   rw 0 q102 ∷
   re 0 8 (Toff201 ∷ []) ∷
   rw 1 q34 ∷ []) Eq.refl

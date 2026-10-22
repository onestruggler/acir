{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D018 (W : Ws) where

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
  q1 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q4 : Eqn
  q4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 340 W
  q7 : Eqn
  q7 = wE 20 W
  q8 : Eqn
  q8 = wE 12 W
  q9 : Eqn
  q9 = wE 21 W
  q10 : Eqn
  q10 = wE 22 W
  q11 : Eqn
  q11 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q12 : Eqn
  q12 = wE 23 W
  q13 : Eqn
  q13 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q14 : Eqn
  q14 = wE 5 W
  q15 : Eqn
  q15 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q16 : Eqn
  q16 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q17 : Eqn
  q17 = wE 24 W
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q19 : Eqn
  q19 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q20 : Eqn
  q20 = wE 25 W
  q21 : Eqn
  q21 = wE 124 W
  q22 : Eqn
  q22 = wE 334 W
  q23 : Eqn
  q23 = wE 14 W

-- sw1 TOFF103: 45 steps
lem-sw1-TOFF103 : ⟪ (Sw12 ∷ Toff103 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ []) ⟫ʷ
lem-sw1-TOFF103 = derive (Sw12 ∷ Toff103 ∷ Sw12 ∷ []) (Toff203 ∷ [])
  (re 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 q1 ∷
   rw 4 q2 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 6 q2 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q2 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q1 ∷
   rw⁻ 8 q4 ∷
   rw 9 q5 ∷
   rw 0 q6 ∷
   rw 1 q7 ∷
   rw 4 q8 ∷
   re 2 3 (CX02 ∷ []) ∷
   rw 3 q9 ∷
   rw 6 q8 ∷
   re 4 3 (CX02 ∷ []) ∷
   re 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 5 q10 ∷
   rw⁻ 7 q11 ∷
   rw 8 q12 ∷
   re 5 5 (CS03 ∷ []) ∷
   rw 6 q6 ∷
   rw⁻ 7 q13 ∷
   rw 0 q14 ∷
   rw 1 q15 ∷
   rw 2 q16 ∷
   rw 3 q17 ∷
   rw 4 q18 ∷
   rw 5 q17 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q19 ∷
   rw 7 q20 ∷
   rw 8 q19 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q15 ∷
   rw 8 q21 ∷
   rw 1 q22 ∷
   re 1 8 (Toff213 ∷ []) ∷
   re 0 3 (Toff203 ∷ []) ∷
   rw 1 q23 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = wE 49 W
  q25 : Eqn
  q25 = wE 50 W
  q26 : Eqn
  q26 = wE 51 W
  q27 : Eqn
  q27 = wE 364 W
  q28 : Eqn
  q28 = wE 365 W

-- sw1 TOFF123: 12 steps
lem-sw1-TOFF123 : ⟪ (Sw12 ∷ Toff123 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ []) ⟫ʷ
lem-sw1-TOFF123 = derive (Sw12 ∷ Toff123 ∷ Sw12 ∷ []) (Toff213 ∷ [])
  (re 1 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 0 q6 ∷
   rw 1 q24 ∷
   rw 2 q25 ∷
   rw 3 q26 ∷
   rw 4 q25 ∷
   rw 5 q7 ∷
   rw 6 q6 ∷
   rw 7 q27 ∷
   rw 0 q28 ∷
   re 0 8 (Toff213 ∷ []) ∷
   rw 1 q23 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 345 W
  q30 : Eqn
  q30 = wE 18 W
  q31 : Eqn
  q31 = wE 19 W
  q32 : Eqn
  q32 = wE 366 W

-- sw1 TOFF201: 15 steps
lem-sw1-TOFF201 : ⟪ (Sw12 ∷ Toff201 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ []) ⟫ʷ
lem-sw1-TOFF201 = derive (Sw12 ∷ Toff201 ∷ Sw12 ∷ []) (Toff102 ∷ [])
  (re 1 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 0 q29 ∷
   rw 1 q30 ∷
   rw 4 q8 ∷
   re 2 3 (CX02 ∷ []) ∷
   rw 3 q31 ∷
   rw 6 q8 ∷
   re 4 3 (CX02 ∷ []) ∷
   re 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 5 q23 ∷
   rw 6 q29 ∷
   rw⁻ 7 q13 ∷
   rw 0 q32 ∷
   re 0 8 (Toff102 ∷ []) ∷
   rw 1 q23 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = wE 30 W
  q34 : Eqn
  q34 = wE 27 W
  q35 : Eqn
  q35 = wE 122 W
  q36 : Eqn
  q36 = wE 31 W
  q37 : Eqn
  q37 = wE 196 W

-- sw1 TOFF203: 45 steps
lem-sw1-TOFF203 : ⟪ (Sw12 ∷ Toff203 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ []) ⟫ʷ
lem-sw1-TOFF203 = derive (Sw12 ∷ Toff203 ∷ Sw12 ∷ []) (Toff103 ∷ [])
  (re 1 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 2 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 1 q15 ∷
   rw 2 q16 ∷
   rw 3 q33 ∷
   rw 4 q18 ∷
   rw 5 q33 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q19 ∷
   rw 7 q34 ∷
   rw 8 q19 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q15 ∷
   rw 8 q35 ∷
   rw 9 q36 ∷
   rw 0 q29 ∷
   rw 1 q24 ∷
   re 3 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 2 q23 ∷
   rw 3 q26 ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 q23 ∷
   re 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 5 q10 ∷
   rw⁻ 7 q11 ∷
   rw 8 q12 ∷
   re 5 5 (CS03 ∷ []) ∷
   rw 6 q29 ∷
   rw⁻ 7 q13 ∷
   rw 0 q2 ∷
   rw⁻ 1 q1 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q1 ∷
   rw⁻ 8 q4 ∷
   rw 1 q37 ∷
   re 1 8 (Toff102 ∷ []) ∷
   re 0 3 (Toff103 ∷ []) ∷
   rw 1 q23 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = wE 367 W

-- sw1 TOFF213: 12 steps
lem-sw1-TOFF213 : ⟪ (Sw12 ∷ Toff213 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ []) ⟫ʷ
lem-sw1-TOFF213 = derive (Sw12 ∷ Toff213 ∷ Sw12 ∷ []) (Toff123 ∷ [])
  (re 1 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 0 q29 ∷
   rw 1 q24 ∷
   rw 2 q25 ∷
   rw 3 q26 ∷
   rw 4 q25 ∷
   rw 5 q7 ∷
   rw 6 q29 ∷
   rw 7 q27 ∷
   rw 0 q38 ∷
   re 0 8 (Toff123 ∷ []) ∷
   rw 1 q23 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = wE 335 W
  q40 : Eqn
  q40 = eqn (Sw12 ∷ K3 ∷ []) (K3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (K))
  q41 : Eqn
  q41 = eqn (Sw01 ∷ K3 ∷ []) (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑)))
  q42 : Eqn
  q42 = wE 337 W

-- sw1 TOFF301: 45 steps
lem-sw1-TOFF301 : ⟪ (Sw12 ∷ Toff301 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ []) ⟫ʷ
lem-sw1-TOFF301 = derive (Sw12 ∷ Toff301 ∷ Sw12 ∷ []) (Toff302 ∷ [])
  (re 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 2 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 1 q39 ∷
   rw 4 q2 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 6 q2 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q2 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q39 ∷
   rw⁻ 8 q4 ∷
   rw 9 q5 ∷
   rw 0 q40 ∷
   rw 1 q7 ∷
   rw 4 q8 ∷
   re 2 3 (CX02 ∷ []) ∷
   rw 3 q9 ∷
   rw 6 q8 ∷
   re 4 3 (CX02 ∷ []) ∷
   re 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 5 q10 ∷
   rw⁻ 7 q11 ∷
   rw 8 q12 ∷
   re 5 5 (CS03 ∷ []) ∷
   rw 6 q40 ∷
   rw⁻ 7 q13 ∷
   rw 0 q14 ∷
   rw 1 q41 ∷
   rw 2 q16 ∷
   rw 3 q17 ∷
   rw 4 q18 ∷
   rw 5 q17 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q19 ∷
   rw 7 q20 ∷
   rw 8 q19 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q41 ∷
   rw 8 q21 ∷
   rw 1 q42 ∷
   re 1 8 (Toff312 ∷ []) ∷
   re 0 3 (Toff302 ∷ []) ∷
   rw 1 q23 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = wE 336 W
  q44 : Eqn
  q44 = wE 368 W

-- sw1 TOFF302: 45 steps
lem-sw1-TOFF302 : ⟪ (Sw12 ∷ Toff302 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ []) ⟫ʷ
lem-sw1-TOFF302 = derive (Sw12 ∷ Toff302 ∷ Sw12 ∷ []) (Toff301 ∷ [])
  (re 1 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) ∷
   re 2 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 1 q41 ∷
   rw 2 q16 ∷
   rw 3 q33 ∷
   rw 4 q18 ∷
   rw 5 q33 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q19 ∷
   rw 7 q34 ∷
   rw 8 q19 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q41 ∷
   rw 8 q35 ∷
   rw 9 q36 ∷
   rw 0 q40 ∷
   rw 1 q24 ∷
   re 3 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 2 q23 ∷
   rw 3 q26 ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 q23 ∷
   re 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 5 q10 ∷
   rw⁻ 7 q11 ∷
   rw 8 q12 ∷
   re 5 5 (CS03 ∷ []) ∷
   rw 6 q40 ∷
   rw⁻ 7 q13 ∷
   rw 0 q2 ∷
   rw 1 q43 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q43 ∷
   rw⁻ 8 q4 ∷
   rw 1 q44 ∷
   re 1 8 (Toff201 ∷ []) ∷
   re 0 3 (Toff301 ∷ []) ∷
   rw 1 q23 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 369 W

-- sw1 TOFF312: 12 steps
lem-sw1-TOFF312 : ⟪ (Sw12 ∷ Toff312 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
lem-sw1-TOFF312 = derive (Sw12 ∷ Toff312 ∷ Sw12 ∷ []) (Toff312 ∷ [])
  (re 1 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 0 q40 ∷
   rw 1 q24 ∷
   rw 2 q25 ∷
   rw 3 q26 ∷
   rw 4 q25 ∷
   rw 5 q7 ∷
   rw 6 q40 ∷
   rw 7 q27 ∷
   rw 0 q45 ∷
   re 0 8 (Toff312 ∷ []) ∷
   rw 1 q23 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))

-- sw2 S0: 2 steps
lem-sw2-S0 : ⟪ (Sw23 ∷ S0 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ []) ⟫ʷ
lem-sw2-S0 = derive (Sw23 ∷ S0 ∷ Sw23 ∷ []) (S0 ∷ [])
  (rw⁻ 0 q46 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))

-- sw2 Sd0: 2 steps
lem-sw2-Sd0 : ⟪ (Sw23 ∷ S0⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ []) ⟫ʷ
lem-sw2-Sd0 = derive (Sw23 ∷ S0⁻ ∷ Sw23 ∷ []) (S0⁻ ∷ [])
  (rw⁻ 0 q47 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))

-- sw2 K0: 2 steps
lem-sw2-K0 : ⟪ (Sw23 ∷ K0 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ []) ⟫ʷ
lem-sw2-K0 = derive (Sw23 ∷ K0 ∷ Sw23 ∷ []) (K0 ∷ [])
  (rw⁻ 0 q48 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑)))

-- sw2 Kd0: 2 steps
lem-sw2-Kd0 : ⟪ (Sw23 ∷ K0⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ []) ⟫ʷ
lem-sw2-Kd0 = derive (Sw23 ∷ K0⁻ ∷ Sw23 ∷ []) (K0⁻ ∷ [])
  (rw⁻ 0 q49 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))

-- sw2 X0: 2 steps
lem-sw2-X0 : ⟪ (Sw23 ∷ X0 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-sw2-X0 = derive (Sw23 ∷ X0 ∷ Sw23 ∷ []) (X0 ∷ [])
  (rw⁻ 0 q50 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = eqn (Z0 ∷ Sw23 ∷ []) (Sw23 ∷ Z0 ∷ []) (low₁-comm (Z) ((Swap ↑)))

-- sw2 Z0: 2 steps
lem-sw2-Z0 : ⟪ (Sw23 ∷ Z0 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Z0 ∷ []) ⟫ʷ
lem-sw2-Z0 = derive (Sw23 ∷ Z0 ∷ Sw23 ∷ []) (Z0 ∷ [])
  (rw⁻ 0 q51 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))

-- sw2 S1: 2 steps
lem-sw2-S1 : ⟪ (Sw23 ∷ S1 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ []) ⟫ʷ
lem-sw2-S1 = derive (Sw23 ∷ S1 ∷ Sw23 ∷ []) (S1 ∷ [])
  (rw⁻ 0 q52 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = eqn (S1⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (Swap))

-- sw2 Sd1: 2 steps
lem-sw2-Sd1 : ⟪ (Sw23 ∷ S1⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ []) ⟫ʷ
lem-sw2-Sd1 = derive (Sw23 ∷ S1⁻ ∷ Sw23 ∷ []) (S1⁻ ∷ [])
  (rw⁻ 0 q53 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 K1: 2 steps
lem-sw2-K1 : ⟪ (Sw23 ∷ K1 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ []) ⟫ʷ
lem-sw2-K1 = derive (Sw23 ∷ K1 ∷ Sw23 ∷ []) (K1 ∷ [])
  (rw⁻ 0 q1 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = eqn (K1⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K1⁻ ∷ []) (low-comm (((K • iI) ↑)) (Swap))

-- sw2 Kd1: 2 steps
lem-sw2-Kd1 : ⟪ (Sw23 ∷ K1⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ []) ⟫ʷ
lem-sw2-Kd1 = derive (Sw23 ∷ K1⁻ ∷ Sw23 ∷ []) (K1⁻ ∷ [])
  (rw⁻ 0 q54 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))

-- sw2 X1: 2 steps
lem-sw2-X1 : ⟪ (Sw23 ∷ X1 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-sw2-X1 = derive (Sw23 ∷ X1 ∷ Sw23 ∷ []) (X1 ∷ [])
  (rw⁻ 0 q55 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = eqn (Z1 ∷ Sw23 ∷ []) (Sw23 ∷ Z1 ∷ []) (low-comm ((Z ↑)) (Swap))

-- sw2 Z1: 2 steps
lem-sw2-Z1 : ⟪ (Sw23 ∷ Z1 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ []) ⟫ʷ
lem-sw2-Z1 = derive (Sw23 ∷ Z1 ∷ Sw23 ∷ []) (Z1 ∷ [])
  (rw⁻ 0 q56 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = wE 151 W

-- sw2 S2: 2 steps
lem-sw2-S2 : ⟪ (Sw23 ∷ S2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ []) ⟫ʷ
lem-sw2-S2 = derive (Sw23 ∷ S2 ∷ Sw23 ∷ []) (S3 ∷ [])
  (rw 0 q57 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = wE 153 W

-- sw2 Sd2: 2 steps
lem-sw2-Sd2 : ⟪ (Sw23 ∷ S2⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ []) ⟫ʷ
lem-sw2-Sd2 = derive (Sw23 ∷ S2⁻ ∷ Sw23 ∷ []) (S3⁻ ∷ [])
  (rw 0 q58 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 K2: 2 steps
lem-sw2-K2 : ⟪ (Sw23 ∷ K2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ []) ⟫ʷ
lem-sw2-K2 = derive (Sw23 ∷ K2 ∷ Sw23 ∷ []) (K3 ∷ [])
  (rw 0 q39 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = wE 370 W

-- sw2 Kd2: 2 steps
lem-sw2-Kd2 : ⟪ (Sw23 ∷ K2⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ []) ⟫ʷ
lem-sw2-Kd2 = derive (Sw23 ∷ K2⁻ ∷ Sw23 ∷ []) (K3⁻ ∷ [])
  (rw 0 q59 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = wE 175 W

-- sw2 X2: 2 steps
lem-sw2-X2 : ⟪ (Sw23 ∷ X2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-sw2-X2 = derive (Sw23 ∷ X2 ∷ Sw23 ∷ []) (X3 ∷ [])
  (rw 0 q60 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = wE 371 W

-- sw2 Z2: 2 steps
lem-sw2-Z2 : ⟪ (Sw23 ∷ Z2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Z3 ∷ []) ⟫ʷ
lem-sw2-Z2 = derive (Sw23 ∷ Z2 ∷ Sw23 ∷ []) (Z3 ∷ [])
  (rw 0 q61 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = wE 372 W

-- sw2 S3: 2 steps
lem-sw2-S3 : ⟪ (Sw23 ∷ S3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ []) ⟫ʷ
lem-sw2-S3 = derive (Sw23 ∷ S3 ∷ Sw23 ∷ []) (S2 ∷ [])
  (rw 0 q62 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 373 W

-- sw2 Sd3: 2 steps
lem-sw2-Sd3 : ⟪ (Sw23 ∷ S3⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ []) ⟫ʷ
lem-sw2-Sd3 = derive (Sw23 ∷ S3⁻ ∷ Sw23 ∷ []) (S2⁻ ∷ [])
  (rw 0 q63 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 K3: 2 steps
lem-sw2-K3 : ⟪ (Sw23 ∷ K3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ []) ⟫ʷ
lem-sw2-K3 = derive (Sw23 ∷ K3 ∷ Sw23 ∷ []) (K2 ∷ [])
  (rw 0 q43 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = wE 374 W

-- sw2 Kd3: 2 steps
lem-sw2-Kd3 : ⟪ (Sw23 ∷ K3⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ []) ⟫ʷ
lem-sw2-Kd3 = derive (Sw23 ∷ K3⁻ ∷ Sw23 ∷ []) (K2⁻ ∷ [])
  (rw 0 q64 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = wE 375 W

-- sw2 X3: 2 steps
lem-sw2-X3 : ⟪ (Sw23 ∷ X3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-sw2-X3 = derive (Sw23 ∷ X3 ∷ Sw23 ∷ []) (X2 ∷ [])
  (rw 0 q65 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = wE 376 W

-- sw2 Z3: 2 steps
lem-sw2-Z3 : ⟪ (Sw23 ∷ Z3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ []) ⟫ʷ
lem-sw2-Z3 = derive (Sw23 ∷ Z3 ∷ Sw23 ∷ []) (Z2 ∷ [])
  (rw 0 q66 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CS01: 2 steps
lem-sw2-CS01 : ⟪ (Sw23 ∷ CS01 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
lem-sw2-CS01 = derive (Sw23 ∷ CS01 ∷ Sw23 ∷ []) (CS01 ∷ [])
  (rw⁻ 0 q11 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))

-- sw2 CSd01: 2 steps
lem-sw2-CSd01 : ⟪ (Sw23 ∷ CS01⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ []) ⟫ʷ
lem-sw2-CSd01 = derive (Sw23 ∷ CS01⁻ ∷ Sw23 ∷ []) (CS01⁻ ∷ [])
  (rw⁻ 0 q67 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = eqn (CZ01 ∷ Sw23 ∷ []) (Sw23 ∷ CZ01 ∷ []) (low-comm (CZ) (Swap))

-- sw2 CZ01: 2 steps
lem-sw2-CZ01 : ⟪ (Sw23 ∷ CZ01 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ []) ⟫ʷ
lem-sw2-CZ01 = derive (Sw23 ∷ CZ01 ∷ Sw23 ∷ []) (CZ01 ∷ [])
  (rw⁻ 0 q68 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CX01: 2 steps
lem-sw2-CX01 : ⟪ (Sw23 ∷ CX01 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ []) ⟫ʷ
lem-sw2-CX01 = derive (Sw23 ∷ CX01 ∷ Sw23 ∷ []) (CX01 ∷ [])
  (rw⁻ 0 q3 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q69 : Eqn
  q69 = eqn (CK01 ∷ Sw23 ∷ []) (Sw23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (Swap))

-- sw2 CK01: 2 steps
lem-sw2-CK01 : ⟪ (Sw23 ∷ CK01 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ []) ⟫ʷ
lem-sw2-CK01 = derive (Sw23 ∷ CK01 ∷ Sw23 ∷ []) (CK01 ∷ [])
  (rw⁻ 0 q69 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = eqn (CK01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CK01⁻ ∷ []) (low-comm ((S • CK₀₁)) (Swap))

-- sw2 CKd01: 2 steps
lem-sw2-CKd01 : ⟪ (Sw23 ∷ CK01⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK01⁻ ∷ []) ⟫ʷ
lem-sw2-CKd01 = derive (Sw23 ∷ CK01⁻ ∷ Sw23 ∷ []) (CK01⁻ ∷ [])
  (rw⁻ 0 q70 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CS02: 3 steps
lem-sw2-CS02 : ⟪ (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ []) ⟫ʷ
lem-sw2-CS02 = derive (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (CS03 ∷ [])
  (rw 2 q2 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CSd02: 3 steps
lem-sw2-CSd02 : ⟪ (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ []) ⟫ʷ
lem-sw2-CSd02 = derive (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (CS03⁻ ∷ [])
  (rw 2 q2 ∷
   re 0 3 (CS03⁻ ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CZ02: 3 steps
lem-sw2-CZ02 : ⟪ (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ []) ⟫ʷ
lem-sw2-CZ02 = derive (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (CZ03 ∷ [])
  (rw 2 q2 ∷
   re 0 3 (CZ03 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CX02: 3 steps
lem-sw2-CX02 : ⟪ (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ []) ⟫ʷ
lem-sw2-CX02 = derive (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (CX03 ∷ [])
  (rw 2 q2 ∷
   re 0 3 (CX03 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CK02: 3 steps
lem-sw2-CK02 : ⟪ (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ []) ⟫ʷ
lem-sw2-CK02 = derive (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (CK03 ∷ [])
  (rw 2 q2 ∷
   re 0 3 (CK03 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CKd02: 3 steps
lem-sw2-CKd02 : ⟪ (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK03⁻ ∷ []) ⟫ʷ
lem-sw2-CKd02 = derive (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) (CK03⁻ ∷ [])
  (rw 2 q2 ∷
   re 0 3 (CK03⁻ ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CS03: 3 steps
lem-sw2-CS03 : ⟪ (Sw23 ∷ CS03 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
lem-sw2-CS03 = derive (Sw23 ∷ CS03 ∷ Sw23 ∷ []) (CS02 ∷ [])
  (re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CSd03: 3 steps
lem-sw2-CSd03 : ⟪ (Sw23 ∷ CS03⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ []) ⟫ʷ
lem-sw2-CSd03 = derive (Sw23 ∷ CS03⁻ ∷ Sw23 ∷ []) (CS02⁻ ∷ [])
  (re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CZ03: 3 steps
lem-sw2-CZ03 : ⟪ (Sw23 ∷ CZ03 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ []) ⟫ʷ
lem-sw2-CZ03 = derive (Sw23 ∷ CZ03 ∷ Sw23 ∷ []) (CZ02 ∷ [])
  (re 1 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CX03: 3 steps
lem-sw2-CX03 : ⟪ (Sw23 ∷ CX03 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ []) ⟫ʷ
lem-sw2-CX03 = derive (Sw23 ∷ CX03 ∷ Sw23 ∷ []) (CX02 ∷ [])
  (re 1 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CK03: 3 steps
lem-sw2-CK03 : ⟪ (Sw23 ∷ CK03 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ []) ⟫ʷ
lem-sw2-CK03 = derive (Sw23 ∷ CK03 ∷ Sw23 ∷ []) (CK02 ∷ [])
  (re 1 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CKd03: 3 steps
lem-sw2-CKd03 : ⟪ (Sw23 ∷ CK03⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK02⁻ ∷ []) ⟫ʷ
lem-sw2-CKd03 = derive (Sw23 ∷ CK03⁻ ∷ Sw23 ∷ []) (CK02⁻ ∷ [])
  (re 1 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))

-- sw2 CX10: 2 steps
lem-sw2-CX10 : ⟪ (Sw23 ∷ CX10 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
lem-sw2-CX10 = derive (Sw23 ∷ CX10 ∷ Sw23 ∷ []) (CX10 ∷ [])
  (rw⁻ 0 q71 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))

-- sw2 CK10: 2 steps
lem-sw2-CK10 : ⟪ (Sw23 ∷ CK10 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ []) ⟫ʷ
lem-sw2-CK10 = derive (Sw23 ∷ CK10 ∷ Sw23 ∷ []) (CK10 ∷ [])
  (rw⁻ 0 q72 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q73 : Eqn
  q73 = eqn (CK10⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap))

-- sw2 CKd10: 2 steps
lem-sw2-CKd10 : ⟪ (Sw23 ∷ CK10⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ []) ⟫ʷ
lem-sw2-CKd10 = derive (Sw23 ∷ CK10⁻ ∷ Sw23 ∷ []) (CK10⁻ ∷ [])
  (rw⁻ 0 q73 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CS12: 3 steps
lem-sw2-CS12 : ⟪ (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ []) ⟫ʷ
lem-sw2-CS12 = derive (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (CS13 ∷ [])
  (rw 2 q2 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CSd12: 3 steps
lem-sw2-CSd12 : ⟪ (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ []) ⟫ʷ
lem-sw2-CSd12 = derive (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (CS13⁻ ∷ [])
  (rw 2 q2 ∷
   re 0 3 (CS13⁻ ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CZ12: 3 steps
lem-sw2-CZ12 : ⟪ (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ []) ⟫ʷ
lem-sw2-CZ12 = derive (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (CZ13 ∷ [])
  (rw 2 q2 ∷
   re 0 3 (CZ13 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CX12: 3 steps
lem-sw2-CX12 : ⟪ (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ []) ⟫ʷ
lem-sw2-CX12 = derive (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (CX13 ∷ [])
  (rw 2 q2 ∷
   re 0 3 (CX13 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CK12: 3 steps
lem-sw2-CK12 : ⟪ (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK13 ∷ []) ⟫ʷ
lem-sw2-CK12 = derive (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (CK13 ∷ [])
  (rw 2 q2 ∷
   re 0 3 (CK13 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CKd12: 3 steps
lem-sw2-CKd12 : ⟪ (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK13⁻ ∷ []) ⟫ʷ
lem-sw2-CKd12 = derive (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (CK13⁻ ∷ [])
  (rw 2 q2 ∷
   re 0 3 (CK13⁻ ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CS13: 3 steps
lem-sw2-CS13 : ⟪ (Sw23 ∷ CS13 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
lem-sw2-CS13 = derive (Sw23 ∷ CS13 ∷ Sw23 ∷ []) (CS12 ∷ [])
  (re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CSd13: 3 steps
lem-sw2-CSd13 : ⟪ (Sw23 ∷ CS13⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ []) ⟫ʷ
lem-sw2-CSd13 = derive (Sw23 ∷ CS13⁻ ∷ Sw23 ∷ []) (CS12⁻ ∷ [])
  (re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CZ13: 3 steps
lem-sw2-CZ13 : ⟪ (Sw23 ∷ CZ13 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ []) ⟫ʷ
lem-sw2-CZ13 = derive (Sw23 ∷ CZ13 ∷ Sw23 ∷ []) (CZ12 ∷ [])
  (re 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CX13: 3 steps
lem-sw2-CX13 : ⟪ (Sw23 ∷ CX13 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ []) ⟫ʷ
lem-sw2-CX13 = derive (Sw23 ∷ CX13 ∷ Sw23 ∷ []) (CX12 ∷ [])
  (re 1 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CK13: 3 steps
lem-sw2-CK13 : ⟪ (Sw23 ∷ CK13 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK12 ∷ []) ⟫ʷ
lem-sw2-CK13 = derive (Sw23 ∷ CK13 ∷ Sw23 ∷ []) (CK12 ∷ [])
  (re 1 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CKd13: 3 steps
lem-sw2-CKd13 : ⟪ (Sw23 ∷ CK13⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK12⁻ ∷ []) ⟫ʷ
lem-sw2-CKd13 = derive (Sw23 ∷ CK13⁻ ∷ Sw23 ∷ []) (CK12⁻ ∷ [])
  (re 1 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CX20: 3 steps
lem-sw2-CX20 : ⟪ (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ []) ⟫ʷ
lem-sw2-CX20 = derive (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (CX30 ∷ [])
  (rw 2 q2 ∷
   re 0 3 (CX30 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CK20: 3 steps
lem-sw2-CK20 : ⟪ (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK30 ∷ []) ⟫ʷ
lem-sw2-CK20 = derive (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (CK30 ∷ [])
  (rw 2 q2 ∷
   re 0 3 (CK30 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CKd20: 3 steps
lem-sw2-CKd20 : ⟪ (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK30⁻ ∷ []) ⟫ʷ
lem-sw2-CKd20 = derive (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (CK30⁻ ∷ [])
  (rw 2 q2 ∷
   re 0 3 (CK30⁻ ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CX21: 3 steps
lem-sw2-CX21 : ⟪ (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ []) ⟫ʷ
lem-sw2-CX21 = derive (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (CX31 ∷ [])
  (rw 2 q2 ∷
   re 0 3 (CX31 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CK21: 3 steps
lem-sw2-CK21 : ⟪ (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK31 ∷ []) ⟫ʷ
lem-sw2-CK21 = derive (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (CK31 ∷ [])
  (rw 2 q2 ∷
   re 0 3 (CK31 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CKd21: 3 steps
lem-sw2-CKd21 : ⟪ (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK31⁻ ∷ []) ⟫ʷ
lem-sw2-CKd21 = derive (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (CK31⁻ ∷ [])
  (rw 2 q2 ∷
   re 0 3 (CK31⁻ ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q74 : Eqn
  q74 = wE 71 W

-- sw2 CS23: 2 steps
lem-sw2-CS23 : ⟪ (Sw23 ∷ CS23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ []) ⟫ʷ
lem-sw2-CS23 = derive (Sw23 ∷ CS23 ∷ Sw23 ∷ []) (CS23 ∷ [])
  (rw 0 q74 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = wE 72 W

-- sw2 CSd23: 2 steps
lem-sw2-CSd23 : ⟪ (Sw23 ∷ CS23⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ []) ⟫ʷ
lem-sw2-CSd23 = derive (Sw23 ∷ CS23⁻ ∷ Sw23 ∷ []) (CS23⁻ ∷ [])
  (rw 0 q75 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = wE 377 W

-- sw2 CZ23: 2 steps
lem-sw2-CZ23 : ⟪ (Sw23 ∷ CZ23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ []) ⟫ʷ
lem-sw2-CZ23 = derive (Sw23 ∷ CZ23 ∷ Sw23 ∷ []) (CZ23 ∷ [])
  (rw 0 q76 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = wE 378 W

-- sw2 CX23: 2 steps
lem-sw2-CX23 : ⟪ (Sw23 ∷ CX23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ []) ⟫ʷ
lem-sw2-CX23 = derive (Sw23 ∷ CX23 ∷ Sw23 ∷ []) (CX32 ∷ [])
  (rw 0 q77 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = wE 379 W

-- sw2 CK23: 2 steps
lem-sw2-CK23 : ⟪ (Sw23 ∷ CK23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK32 ∷ []) ⟫ʷ
lem-sw2-CK23 = derive (Sw23 ∷ CK23 ∷ Sw23 ∷ []) (CK32 ∷ [])
  (rw 0 q78 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = wE 380 W

-- sw2 CKd23: 2 steps
lem-sw2-CKd23 : ⟪ (Sw23 ∷ CK23⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK32⁻ ∷ []) ⟫ʷ
lem-sw2-CKd23 = derive (Sw23 ∷ CK23⁻ ∷ Sw23 ∷ []) (CK32⁻ ∷ [])
  (rw 0 q79 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CX30: 3 steps
lem-sw2-CX30 : ⟪ (Sw23 ∷ CX30 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ []) ⟫ʷ
lem-sw2-CX30 = derive (Sw23 ∷ CX30 ∷ Sw23 ∷ []) (CX20 ∷ [])
  (re 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CK30: 3 steps
lem-sw2-CK30 : ⟪ (Sw23 ∷ CK30 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ []) ⟫ʷ
lem-sw2-CK30 = derive (Sw23 ∷ CK30 ∷ Sw23 ∷ []) (CK20 ∷ [])
  (re 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CKd30: 3 steps
lem-sw2-CKd30 : ⟪ (Sw23 ∷ CK30⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ []) ⟫ʷ
lem-sw2-CKd30 = derive (Sw23 ∷ CK30⁻ ∷ Sw23 ∷ []) (CK20⁻ ∷ [])
  (re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CX31: 3 steps
lem-sw2-CX31 : ⟪ (Sw23 ∷ CX31 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
lem-sw2-CX31 = derive (Sw23 ∷ CX31 ∷ Sw23 ∷ []) (CX21 ∷ [])
  (re 1 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CK31: 3 steps
lem-sw2-CK31 : ⟪ (Sw23 ∷ CK31 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ []) ⟫ʷ
lem-sw2-CK31 = derive (Sw23 ∷ CK31 ∷ Sw23 ∷ []) (CK21 ∷ [])
  (re 1 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CKd31: 3 steps
lem-sw2-CKd31 : ⟪ (Sw23 ∷ CK31⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK21⁻ ∷ []) ⟫ʷ
lem-sw2-CKd31 = derive (Sw23 ∷ CK31⁻ ∷ Sw23 ∷ []) (CK21⁻ ∷ [])
  (re 1 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q80 : Eqn
  q80 = wE 381 W

-- sw2 CX32: 2 steps
lem-sw2-CX32 : ⟪ (Sw23 ∷ CX32 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ []) ⟫ʷ
lem-sw2-CX32 = derive (Sw23 ∷ CX32 ∷ Sw23 ∷ []) (CX23 ∷ [])
  (rw 0 q80 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = wE 382 W

-- sw2 CK32: 2 steps
lem-sw2-CK32 : ⟪ (Sw23 ∷ CK32 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK23 ∷ []) ⟫ʷ
lem-sw2-CK32 = derive (Sw23 ∷ CK32 ∷ Sw23 ∷ []) (CK23 ∷ [])
  (rw 0 q81 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = wE 383 W

-- sw2 CKd32: 2 steps
lem-sw2-CKd32 : ⟪ (Sw23 ∷ CK32⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK23⁻ ∷ []) ⟫ʷ
lem-sw2-CKd32 = derive (Sw23 ∷ CK32⁻ ∷ Sw23 ∷ []) (CK23⁻ ∷ [])
  (rw 0 q82 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q83 : Eqn
  q83 = wE 43 W

-- sw2 CCZ012: 22 steps
lem-sw2-CCZ012 : ⟪ (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ []) ⟫ʷ
lem-sw2-CCZ012 = derive (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (CCZ013 ∷ [])
  (re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q2 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q3 ∷
   rw 4 q2 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 6 q2 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 0 q2 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw⁻ 4 q3 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 1 q83 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   re 0 3 (CCZ013 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CCZ013: 22 steps
lem-sw2-CCZ013 : ⟪ (Sw23 ∷ CCZ013 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
lem-sw2-CCZ013 = derive (Sw23 ∷ CCZ013 ∷ Sw23 ∷ []) (CCZ012 ∷ [])
  (re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q5 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q5 ∷
   rw⁻ 1 q3 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 0 q83 ∷
   re 0 5 (CCZ012 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = wE 73 W

-- sw2 CCZ023: 38 steps
lem-sw2-CCZ023 : ⟪ (Sw23 ∷ CCZ023 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ []) ⟫ʷ
lem-sw2-CCZ023 = derive (Sw23 ∷ CCZ023 ∷ Sw23 ∷ []) (CCZ023 ∷ [])
  (re 1 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q16 ∷
   rw 2 q33 ∷
   rw 3 q18 ∷
   rw 4 q33 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q19 ∷
   rw 6 q34 ∷
   rw 7 q19 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q36 ∷
   rw 0 q74 ∷
   rw 3 q2 ∷
   re 1 3 (CX03 ∷ []) ∷
   rw 2 q75 ∷
   rw 5 q2 ∷
   re 3 3 (CX03 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 0 q14 ∷
   rw 1 q16 ∷
   re 3 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 2 q19 ∷
   rw 3 q17 ∷
   rw 4 q19 ∷
   re 2 3 (CX13 ∷ []) ∷
   rw 3 q18 ∷
   re 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 4 q19 ∷
   rw 5 q17 ∷
   rw 6 q19 ∷
   re 4 3 (CX13 ∷ []) ∷
   rw 5 q20 ∷
   rw 1 q84 ∷
   re 1 5 (CCZ123 ∷ []) ∷
   re 0 3 (CCZ023 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CCZ123: 12 steps
lem-sw2-CCZ123 : ⟪ (Sw23 ∷ CCZ123 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
lem-sw2-CCZ123 = derive (Sw23 ∷ CCZ123 ∷ Sw23 ∷ []) (CCZ123 ∷ [])
  (re 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 0 q74 ∷
   rw 3 q2 ∷
   re 1 3 (CX13 ∷ []) ∷
   rw 2 q75 ∷
   rw 5 q2 ∷
   re 3 3 (CX13 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 0 q84 ∷
   re 0 5 (CCZ123 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = wE 56 W

-- sw2 TOFF012: 28 steps
lem-sw2-TOFF012 : ⟪ (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ []) ⟫ʷ
lem-sw2-TOFF012 = derive (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (Toff013 ∷ [])
  (re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q48 ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q48 ∷
   rw⁻ 7 q4 ∷
   rw 0 q2 ∷
   rw⁻ 1 q48 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q48 ∷
   rw⁻ 8 q4 ∷
   rw 1 q85 ∷
   re 1 8 (Toff012 ∷ []) ∷
   re 0 3 (Toff013 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 TOFF013: 28 steps
lem-sw2-TOFF013 : ⟪ (Sw23 ∷ Toff013 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
lem-sw2-TOFF013 = derive (Sw23 ∷ Toff013 ∷ Sw23 ∷ []) (Toff012 ∷ [])
  (re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q48 ∷
   rw 4 q2 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 6 q2 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q2 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q48 ∷
   rw⁻ 8 q4 ∷
   rw 9 q5 ∷
   rw⁻ 0 q48 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw⁻ 4 q3 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q48 ∷
   rw⁻ 7 q4 ∷
   rw 0 q85 ∷
   re 0 8 (Toff012 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = wE 121 W
  q87 : Eqn
  q87 = wE 123 W
  q88 : Eqn
  q88 = wE 384 W

-- sw2 TOFF023: 47 steps
lem-sw2-TOFF023 : ⟪ (Sw23 ∷ Toff023 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ []) ⟫ʷ
lem-sw2-TOFF023 = derive (Sw23 ∷ Toff023 ∷ Sw23 ∷ []) (Toff023 ∷ [])
  (re 1 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 1 q86 ∷
   rw 2 q16 ∷
   rw 3 q33 ∷
   rw 4 q18 ∷
   rw 5 q33 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q19 ∷
   rw 7 q34 ∷
   rw 8 q19 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q86 ∷
   rw 8 q35 ∷
   rw 9 q36 ∷
   rw⁻ 0 q48 ∷
   rw 1 q74 ∷
   rw 4 q2 ∷
   re 2 3 (CX03 ∷ []) ∷
   rw 3 q75 ∷
   rw 6 q2 ∷
   re 4 3 (CX03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q48 ∷
   rw⁻ 7 q4 ∷
   rw 0 q14 ∷
   rw 1 q87 ∷
   rw 2 q16 ∷
   re 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 3 q19 ∷
   rw 4 q17 ∷
   rw 5 q19 ∷
   re 3 3 (CX13 ∷ []) ∷
   rw 4 q18 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 q19 ∷
   rw 6 q17 ∷
   rw 7 q19 ∷
   re 5 3 (CX13 ∷ []) ∷
   rw 6 q20 ∷
   rw 7 q87 ∷
   rw 8 q21 ∷
   rw 1 q88 ∷
   re 1 8 (Toff123 ∷ []) ∷
   re 0 3 (Toff023 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 TOFF102: 28 steps
lem-sw2-TOFF102 : ⟪ (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ []) ⟫ʷ
lem-sw2-TOFF102 = derive (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (Toff103 ∷ [])
  (re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 0 q1 ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q1 ∷
   rw⁻ 7 q4 ∷
   rw 0 q2 ∷
   rw⁻ 1 q1 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q1 ∷
   rw⁻ 8 q4 ∷
   rw 1 q37 ∷
   re 1 8 (Toff102 ∷ []) ∷
   re 0 3 (Toff103 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 TOFF103: 28 steps
lem-sw2-TOFF103 : ⟪ (Sw23 ∷ Toff103 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ []) ⟫ʷ
lem-sw2-TOFF103 = derive (Sw23 ∷ Toff103 ∷ Sw23 ∷ []) (Toff102 ∷ [])
  (re 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 q1 ∷
   rw 4 q2 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 6 q2 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q2 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q1 ∷
   rw⁻ 8 q4 ∷
   rw 9 q5 ∷
   rw⁻ 0 q1 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw⁻ 4 q3 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q1 ∷
   rw⁻ 7 q4 ∷
   rw 0 q37 ∷
   re 0 8 (Toff102 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = eqn (ι1 ∷ Sw23 ∷ []) (Sw23 ∷ ι1 ∷ []) (low-comm ((iI ↑)) (Swap))

-- sw2 TOFF123: 15 steps
lem-sw2-TOFF123 : ⟪ (Sw23 ∷ Toff123 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ []) ⟫ʷ
lem-sw2-TOFF123 = derive (Sw23 ∷ Toff123 ∷ Sw23 ∷ []) (Toff123 ∷ [])
  (re 1 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw⁻ 0 q1 ∷
   rw 1 q74 ∷
   rw 4 q2 ∷
   re 2 3 (CX13 ∷ []) ∷
   rw 3 q75 ∷
   rw 6 q2 ∷
   re 4 3 (CX13 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q1 ∷
   rw⁻ 7 q89 ∷
   rw 0 q88 ∷
   re 0 8 (Toff123 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 TOFF201: 28 steps
lem-sw2-TOFF201 : ⟪ (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ []) ⟫ʷ
lem-sw2-TOFF201 = derive (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (Toff301 ∷ [])
  (re 1 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 0 q39 ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q39 ∷
   rw⁻ 7 q4 ∷
   rw 0 q2 ∷
   rw 1 q43 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q43 ∷
   rw⁻ 8 q4 ∷
   rw 1 q44 ∷
   re 1 8 (Toff201 ∷ []) ∷
   re 0 3 (Toff301 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = wE 385 W

-- sw2 TOFF203: 47 steps
lem-sw2-TOFF203 : ⟪ (Sw23 ∷ Toff203 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ []) ⟫ʷ
lem-sw2-TOFF203 = derive (Sw23 ∷ Toff203 ∷ Sw23 ∷ []) (Toff302 ∷ [])
  (re 1 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 2 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 1 q15 ∷
   rw 2 q16 ∷
   rw 3 q33 ∷
   rw 4 q18 ∷
   rw 5 q33 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q19 ∷
   rw 7 q34 ∷
   rw 8 q19 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q15 ∷
   rw 8 q35 ∷
   rw 9 q36 ∷
   rw 0 q39 ∷
   rw 1 q74 ∷
   rw 4 q2 ∷
   re 2 3 (CX03 ∷ []) ∷
   rw 3 q75 ∷
   rw 6 q2 ∷
   re 4 3 (CX03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q39 ∷
   rw⁻ 7 q4 ∷
   rw 0 q14 ∷
   rw 1 q41 ∷
   rw 2 q16 ∷
   re 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 3 q19 ∷
   rw 4 q17 ∷
   rw 5 q19 ∷
   re 3 3 (CX13 ∷ []) ∷
   rw 4 q18 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 q19 ∷
   rw 6 q17 ∷
   rw 7 q19 ∷
   re 5 3 (CX13 ∷ []) ∷
   rw 6 q20 ∷
   rw 7 q41 ∷
   rw 8 q21 ∷
   rw 1 q90 ∷
   re 1 8 (Toff312 ∷ []) ∷
   re 0 3 (Toff302 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

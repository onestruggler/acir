{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D021 (W : Ws) where

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
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q3 : Eqn
  q3 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q4 : Eqn
  q4 = wE 30 W
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = wE 27 W
  q8 : Eqn
  q8 = wE 122 W
  q9 : Eqn
  q9 = wE 31 W
  q10 : Eqn
  q10 = wE 127 W
  q11 : Eqn
  q11 = wE 7 W
  q12 : Eqn
  q12 = wE 74 W
  q13 : Eqn
  q13 = wE 334 W
  q14 : Eqn
  q14 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q15 : Eqn
  q15 = wE 400 W
  q16 : Eqn
  q16 = wE 24 W
  q17 : Eqn
  q17 = wE 25 W
  q18 : Eqn
  q18 = wE 124 W

-- pass [X3 CSd32 X3] [TOFF203]: 67 steps
lem-pass-X3-CSd32-X3-vs-TOFF203 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd32-X3-vs-TOFF203 = derive (X3 ∷ CS23⁻ ∷ X3 ∷ Toff203 ∷ []) (Toff203 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 4 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 3 q2 ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q2 ∷
   rw 10 q8 ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw⁻ 9 q2 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q6 ∷
   rw 9 q11 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q12 ∷
   rw⁻ 6 q5 ∷
   rw 5 q12 ∷
   rw⁻ 4 q3 ∷
   rw⁻ 3 q2 ∷
   rw 4 q13 ∷
   re 4 8 (Toff213 ∷ []) ∷
   rw⁻ 2 q14 ∷
   rw⁻ 1 q5 ∷
   rw⁻ 0 q14 ∷
   rw 1 q15 ∷
   re 1 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q2 ∷
   rw 7 q8 ∷
   rw 0 q1 ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q16 ∷
   rw 4 q5 ∷
   rw 5 q16 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q17 ∷
   rw 8 q6 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q2 ∷
   rw 8 q18 ∷
   rw 1 q13 ∷
   re 1 8 (Toff213 ∷ []) ∷
   re 0 3 (Toff203 ∷ []) ∷
   rw 1 q14 ∷
   rw 2 q5 ∷
   rw 3 q14 ∷
   rw 4 q9 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = wE 401 W

-- pass [X3 CSd32 X3] [CS12]: 1 steps
lem-pass-X3-CSd32-X3-vs-CS12 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd32-X3-vs-CS12 = derive (X3 ∷ CS23⁻ ∷ X3 ∷ CS12 ∷ []) (CS12 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ [])
  (rw 0 q19 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = wE 402 W

-- pass [X3 CSd32 X3] [CSd12]: 1 steps
lem-pass-X3-CSd32-X3-vs-CSd12 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd32-X3-vs-CSd12 = derive (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X3 ∷ CS23⁻ ∷ X3 ∷ [])
  (rw 0 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = wE 121 W
  q22 : Eqn
  q22 = wE 118 W
  q23 : Eqn
  q23 = wE 125 W
  q24 : Eqn
  q24 = wE 403 W
  q25 : Eqn
  q25 = wE 123 W

-- pass [X3 CSd32 X3] [TOFF023]: 67 steps
lem-pass-X3-CSd32-X3-vs-TOFF023 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd32-X3-vs-TOFF023 = derive (X3 ∷ CS23⁻ ∷ X3 ∷ Toff023 ∷ []) (Toff023 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 4 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 3 q21 ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q21 ∷
   rw 10 q8 ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw 9 q22 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q6 ∷
   rw 9 q11 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q12 ∷
   rw⁻ 6 q5 ∷
   rw 5 q12 ∷
   rw⁻ 4 q3 ∷
   rw 3 q22 ∷
   rw 4 q23 ∷
   re 4 8 (Toff123 ∷ []) ∷
   rw⁻ 2 q14 ∷
   rw⁻ 1 q5 ∷
   rw⁻ 0 q14 ∷
   rw 1 q24 ∷
   re 1 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 0 q21 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q21 ∷
   rw 7 q8 ∷
   rw 0 q1 ∷
   rw 1 q25 ∷
   rw 2 q3 ∷
   rw 3 q16 ∷
   rw 4 q5 ∷
   rw 5 q16 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q17 ∷
   rw 8 q6 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q25 ∷
   rw 8 q18 ∷
   rw 1 q23 ∷
   re 1 8 (Toff123 ∷ []) ∷
   re 0 3 (Toff023 ∷ []) ∷
   rw 1 q14 ∷
   rw 2 q5 ∷
   rw 3 q14 ∷
   rw 4 q9 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q27 : Eqn
  q27 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))

-- pass [X3 CSd32 X3] [CS01]: 3 steps
lem-pass-X3-CSd32-X3-vs-CS01 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd32-X3-vs-CS01 = derive (X3 ∷ CS23⁻ ∷ X3 ∷ CS01 ∷ []) (CS01 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ [])
  (rw⁻ 2 q26 ∷
   rw⁻ 1 q27 ∷
   rw⁻ 0 q26 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = eqn (CS01⁻ ∷ X3 ∷ []) (X3 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((X ↑)))
  q29 : Eqn
  q29 = eqn (CS01⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((CS • CS • CS)))

-- pass [X3 CSd32 X3] [CSd01]: 3 steps
lem-pass-X3-CSd32-X3-vs-CSd01 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd32-X3-vs-CSd01 = derive (X3 ∷ CS23⁻ ∷ X3 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ X3 ∷ CS23⁻ ∷ X3 ∷ [])
  (rw⁻ 2 q28 ∷
   rw⁻ 1 q29 ∷
   rw⁻ 0 q28 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = eqn (Sw01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑ • CK₁₀)))
  q31 : Eqn
  q31 = wE 404 W

-- pass [X3 CKd32 X3] [TOFF023]: 67 steps
lem-pass-X3-CKd32-X3-vs-TOFF023 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd32-X3-vs-TOFF023 = derive (X3 ∷ CK32⁻ ∷ X3 ∷ Toff023 ∷ []) (Toff023 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 4 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 3 q21 ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q21 ∷
   rw 10 q8 ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw 9 q22 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q6 ∷
   rw 9 q11 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q12 ∷
   rw⁻ 6 q5 ∷
   rw 5 q12 ∷
   rw⁻ 4 q3 ∷
   rw 3 q22 ∷
   rw 4 q23 ∷
   re 4 8 (Toff123 ∷ []) ∷
   rw⁻ 2 q14 ∷
   rw⁻ 1 q30 ∷
   rw⁻ 0 q14 ∷
   rw 1 q31 ∷
   re 1 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 0 q21 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q21 ∷
   rw 7 q8 ∷
   rw 0 q1 ∷
   rw 1 q25 ∷
   rw 2 q3 ∷
   rw 3 q16 ∷
   rw 4 q5 ∷
   rw 5 q16 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q17 ∷
   rw 8 q6 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q25 ∷
   rw 8 q18 ∷
   rw 1 q23 ∷
   re 1 8 (Toff123 ∷ []) ∷
   re 0 3 (Toff023 ∷ []) ∷
   rw 1 q14 ∷
   rw 2 q30 ∷
   rw 3 q14 ∷
   rw 4 q9 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = eqn (CS01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CS01 ∷ []) (low-comm (CS) ((S ↑ • CK₁₀)))

-- pass [X3 CKd32 X3] [CS01]: 3 steps
lem-pass-X3-CKd32-X3-vs-CS01 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd32-X3-vs-CS01 = derive (X3 ∷ CK32⁻ ∷ X3 ∷ CS01 ∷ []) (CS01 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ [])
  (rw⁻ 2 q26 ∷
   rw⁻ 1 q32 ∷
   rw⁻ 0 q26 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = eqn (CS01⁻ ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((S ↑ • CK₁₀)))

-- pass [X3 CKd32 X3] [CSd01]: 3 steps
lem-pass-X3-CKd32-X3-vs-CSd01 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd32-X3-vs-CSd01 = derive (X3 ∷ CK32⁻ ∷ X3 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ X3 ∷ CK32⁻ ∷ X3 ∷ [])
  (rw⁻ 2 q28 ∷
   rw⁻ 1 q33 ∷
   rw⁻ 0 q28 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = wE 405 W

-- pass [X3 CS32 X3] [TOFF023]: 67 steps
lem-pass-X3-CS32-X3-vs-TOFF023 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-TOFF023 = derive (X3 ∷ CS23 ∷ X3 ∷ Toff023 ∷ []) (Toff023 ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 4 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 3 q21 ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q21 ∷
   rw 10 q8 ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw 9 q22 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q6 ∷
   rw 9 q11 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q12 ∷
   rw⁻ 6 q5 ∷
   rw 5 q12 ∷
   rw⁻ 4 q3 ∷
   rw 3 q22 ∷
   rw 4 q23 ∷
   re 4 8 (Toff123 ∷ []) ∷
   rw⁻ 2 q14 ∷
   rw⁻ 1 q3 ∷
   rw⁻ 0 q14 ∷
   rw 1 q34 ∷
   re 1 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 0 q21 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q21 ∷
   rw 7 q8 ∷
   rw 0 q1 ∷
   rw 1 q25 ∷
   rw 2 q3 ∷
   rw 3 q16 ∷
   rw 4 q5 ∷
   rw 5 q16 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q17 ∷
   rw 8 q6 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q25 ∷
   rw 8 q18 ∷
   rw 1 q23 ∷
   re 1 8 (Toff123 ∷ []) ∷
   re 0 3 (Toff023 ∷ []) ∷
   rw 1 q14 ∷
   rw 2 q3 ∷
   rw 3 q14 ∷
   rw 4 q9 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))

-- pass [X3 CS32 X3] [CS01]: 3 steps
lem-pass-X3-CS32-X3-vs-CS01 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-CS01 = derive (X3 ∷ CS23 ∷ X3 ∷ CS01 ∷ []) (CS01 ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  (rw⁻ 2 q26 ∷
   rw⁻ 1 q35 ∷
   rw⁻ 0 q26 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (CS01⁻ ∷ CS23 ∷ []) (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS))

-- pass [X3 CS32 X3] [CSd01]: 3 steps
lem-pass-X3-CS32-X3-vs-CSd01 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-CSd01 = derive (X3 ∷ CS23 ∷ X3 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  (rw⁻ 2 q28 ∷
   rw⁻ 1 q36 ∷
   rw⁻ 0 q28 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = wE 100 W
  q38 : Eqn
  q38 = wE 406 W
  q39 : Eqn
  q39 = wE 6 W
  q40 : Eqn
  q40 = wE 407 W
  q41 : Eqn
  q41 = wE 39 W
  q42 : Eqn
  q42 = wE 104 W

-- comm CCZ012 CS23: 19 steps
lem-comm-CCZ012-CS23 : ⟪ (CCZ012 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ012 ∷ []) ⟫ʷ
lem-comm-CCZ012-CS23 = derive (CCZ012 ∷ CS23 ∷ []) (CS23 ∷ CCZ012 ∷ [])
  (rw 0 q37 ∷
   rw 4 q38 ∷
   rw 5 q1 ∷
   rw⁻ 4 q3 ∷
   rw 3 q39 ∷
   rw 4 q40 ∷
   rw 3 q3 ∷
   rw 4 q41 ∷
   rw 5 q9 ∷
   rw 2 q36 ∷
   rw 3 q1 ∷
   rw⁻ 2 q3 ∷
   rw 1 q39 ∷
   rw 2 q40 ∷
   rw 1 q3 ∷
   rw 2 q41 ∷
   rw 3 q9 ∷
   rw 0 q35 ∷
   rw 1 q42 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = wE 408 W

-- pass [CS23] [S0]: 1 steps
lem-pass-CS23-vs-S0 : ⟪ (CS23 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-S0 = derive (CS23 ∷ S0 ∷ []) (S0 ∷ CS23 ∷ [])
  (rw 0 q43 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = wE 76 W
  q45 : Eqn
  q45 = wE 82 W
  q46 : Eqn
  q46 = wE 29 W

-- pass [CS23] [CSd03]: 15 steps
lem-pass-CS23-vs-CSd03 : ⟪ (CS23 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-CSd03 = derive (CS23 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS23 ∷ [])
  (rw 2 q1 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 2 q44 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 0 q3 ∷
   rw 1 q45 ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q6 ∷
   rw 1 q46 ∷
   rw 2 q6 ∷
   re 0 3 (CS03⁻ ∷ []) ∷
   rw 1 q3 ∷
   rw 2 q9 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = wE 409 W

-- pass [CS23] [Sd0]: 1 steps
lem-pass-CS23-vs-Sd0 : ⟪ (CS23 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-Sd0 = derive (CS23 ∷ S0⁻ ∷ []) (S0⁻ ∷ CS23 ∷ [])
  (rw 0 q47 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = wE 91 W

-- pass [CS23] [CS03]: 15 steps
lem-pass-CS23-vs-CS03 : ⟪ (CS23 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-CS03 = derive (CS23 ∷ CS03 ∷ []) (CS03 ∷ CS23 ∷ [])
  (rw 2 q1 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 2 q11 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 0 q3 ∷
   rw 1 q48 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q6 ∷
   rw 1 q7 ∷
   rw 2 q6 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q3 ∷
   rw 2 q9 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = wE 1 W
  q50 : Eqn
  q50 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q51 : Eqn
  q51 = wE 3 W
  q52 : Eqn
  q52 = wE 43 W
  q53 : Eqn
  q53 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q54 : Eqn
  q54 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q55 : Eqn
  q55 = wE 410 W
  q56 : Eqn
  q56 = wE 411 W

-- comm CCZ013 CS23: 97 steps
lem-comm-CCZ013-CS23 : ⟪ (CCZ013 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CS23 = derive (CCZ013 ∷ CS23 ∷ []) (CS23 ∷ CCZ013 ∷ [])
  (rw 1 q49 ∷
   re 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q49 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q50 ∷
   rw 4 q49 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q50 ∷
   rw 6 q49 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q51 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q51 ∷
   rw 3 q50 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q51 ∷
   rw 1 q50 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q51 ∷
   rw 1 q52 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   rw 1 q37 ∷
   rw⁻ 0 q53 ∷
   rw 3 q49 ∷
   re 1 3 (CX30 ∷ []) ∷
   rw⁻ 2 q54 ∷
   rw 5 q49 ∷
   re 3 3 (CX30 ∷ []) ∷
   rw 6 q49 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 5 q51 ∷
   rw 4 q55 ∷
   rw 5 q1 ∷
   rw⁻ 4 q3 ∷
   re 3 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q6 ∷
   rw 4 q39 ∷
   rw⁻ 3 q6 ∷
   re 4 3 (CX31 ∷ []) ∷
   rw 4 q56 ∷
   rw 3 q3 ∷
   re 5 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 5 q41 ∷
   rw 6 q6 ∷
   re 4 3 (CX30 ∷ []) ∷
   rw 5 q9 ∷
   rw 2 q36 ∷
   rw 3 q1 ∷
   rw⁻ 2 q3 ∷
   re 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 2 q39 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (CX31 ∷ []) ∷
   rw 2 q56 ∷
   rw 1 q3 ∷
   re 3 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw 3 q41 ∷
   rw 4 q6 ∷
   re 2 3 (CX30 ∷ []) ∷
   rw 3 q9 ∷
   rw 0 q35 ∷
   rw 6 q49 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q51 ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 6 q51 ∷
   rw 3 q54 ∷
   re 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 4 q51 ∷
   rw 1 q53 ∷
   rw 2 q42 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q49 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q50 ∷
   rw 5 q49 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q50 ∷
   rw 7 q49 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q49 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q51 ∷
   rw⁻ 3 q50 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q51 ∷
   rw⁻ 5 q50 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q51 ∷
   rw 2 q52 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw 2 q51 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = wE 412 W

-- pass [CS23] [CS02]: 7 steps
lem-pass-CS23-vs-CS02 : ⟪ (CS23 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-CS02 = derive (CS23 ∷ CS02 ∷ []) (CS02 ∷ CS23 ∷ [])
  (rw 2 q1 ∷
   rw 1 q11 ∷
   rw⁻ 0 q3 ∷
   rw 1 q57 ∷
   rw 0 q7 ∷
   rw 1 q3 ∷
   rw 2 q9 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = wE 77 W

-- pass [CS23] [CSd02]: 7 steps
lem-pass-CS23-vs-CSd02 : ⟪ (CS23 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-CSd02 = derive (CS23 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS23 ∷ [])
  (rw 2 q1 ∷
   rw 1 q44 ∷
   rw⁻ 0 q3 ∷
   rw 1 q58 ∷
   rw 0 q46 ∷
   rw 1 q3 ∷
   rw 2 q9 ∷ []) Eq.refl

-- pass [CS23] [CSd01]: 1 steps
lem-pass-CS23-vs-CSd01 : ⟪ (CS23 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-CSd01 = derive (CS23 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS23 ∷ [])
  (rw⁻ 0 q36 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = wE 413 W

-- pass [CS23] [X3 TOFF023 X3]: 67 steps
lem-pass-CS23-vs-X3-TOFF023-X3 : ⟪ (CS23 ∷ X3 ∷ Toff023 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff023 ∷ X3 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-X3-TOFF023-X3 = derive (CS23 ∷ X3 ∷ Toff023 ∷ X3 ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS23 ∷ [])
  (rw 4 q1 ∷
   rw⁻ 3 q14 ∷
   re 2 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 3 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 2 q21 ∷
   rw 3 q3 ∷
   rw 4 q4 ∷
   rw 5 q5 ∷
   rw 6 q4 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 8 q7 ∷
   rw 9 q6 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q21 ∷
   rw 9 q8 ∷
   rw 10 q9 ∷
   rw 9 q10 ∷
   rw 8 q22 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q6 ∷
   rw 8 q11 ∷
   rw⁻ 7 q6 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 6 q12 ∷
   rw⁻ 5 q5 ∷
   rw 4 q12 ∷
   rw⁻ 3 q3 ∷
   rw 2 q22 ∷
   rw 3 q23 ∷
   re 3 8 (Toff123 ∷ []) ∷
   rw⁻ 1 q14 ∷
   rw⁻ 0 q3 ∷
   rw 1 q59 ∷
   rw 0 q14 ∷
   re 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 1 q21 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q5 ∷
   rw 5 q4 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q7 ∷
   rw 8 q6 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q21 ∷
   rw 8 q8 ∷
   rw 1 q1 ∷
   rw 2 q25 ∷
   rw 3 q3 ∷
   rw 4 q16 ∷
   rw 5 q5 ∷
   rw 6 q16 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 8 q17 ∷
   rw 9 q6 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q25 ∷
   rw 9 q18 ∷
   rw 2 q23 ∷
   re 2 8 (Toff123 ∷ []) ∷
   re 1 3 (Toff023 ∷ []) ∷
   rw 2 q14 ∷
   rw 3 q3 ∷
   rw 4 q9 ∷ []) Eq.refl

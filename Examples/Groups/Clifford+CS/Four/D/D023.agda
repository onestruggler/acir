{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D023 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = wE 121 W
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
  q11 = wE 118 W
  q12 : Eqn
  q12 = wE 7 W
  q13 : Eqn
  q13 = wE 74 W
  q14 : Eqn
  q14 = wE 125 W
  q15 : Eqn
  q15 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q16 : Eqn
  q16 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q17 : Eqn
  q17 = wE 419 W
  q18 : Eqn
  q18 = wE 123 W
  q19 : Eqn
  q19 = wE 24 W
  q20 : Eqn
  q20 = wE 25 W
  q21 : Eqn
  q21 = wE 124 W

-- pass [X3 CK32 X3] [TOFF023]: 67 steps
lem-pass-X3-CK32-X3-vs-TOFF023 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK32-X3-vs-TOFF023 = derive (X3 ∷ CK32 ∷ X3 ∷ Toff023 ∷ []) (Toff023 ∷ X3 ∷ CK32 ∷ X3 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 4 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
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
   rw 9 q11 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q6 ∷
   rw 9 q12 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q13 ∷
   rw⁻ 6 q5 ∷
   rw 5 q13 ∷
   rw⁻ 4 q3 ∷
   rw 3 q11 ∷
   rw 4 q14 ∷
   re 4 8 (Toff123 ∷ []) ∷
   rw⁻ 2 q15 ∷
   rw⁻ 1 q16 ∷
   rw⁻ 0 q15 ∷
   rw 1 q17 ∷
   re 1 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
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
   rw 1 q18 ∷
   rw 2 q3 ∷
   rw 3 q19 ∷
   rw 4 q5 ∷
   rw 5 q19 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q20 ∷
   rw 8 q6 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q18 ∷
   rw 8 q21 ∷
   rw 1 q14 ∷
   re 1 8 (Toff123 ∷ []) ∷
   re 0 3 (Toff023 ∷ []) ∷
   rw 1 q15 ∷
   rw 2 q16 ∷
   rw 3 q15 ∷
   rw 4 q9 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q23 : Eqn
  q23 = eqn (CS01 ∷ CK32 ∷ []) (CK32 ∷ CS01 ∷ []) (low-comm (CS) (CK₁₀))

-- pass [X3 CK32 X3] [CS01]: 3 steps
lem-pass-X3-CK32-X3-vs-CS01 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK32-X3-vs-CS01 = derive (X3 ∷ CK32 ∷ X3 ∷ CS01 ∷ []) (CS01 ∷ X3 ∷ CK32 ∷ X3 ∷ [])
  (rw⁻ 2 q22 ∷
   rw⁻ 1 q23 ∷
   rw⁻ 0 q22 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = eqn (CS01⁻ ∷ X3 ∷ []) (X3 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((X ↑)))
  q25 : Eqn
  q25 = eqn (CS01⁻ ∷ CK32 ∷ []) (CK32 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CK₁₀))

-- pass [X3 CK32 X3] [CSd01]: 3 steps
lem-pass-X3-CK32-X3-vs-CSd01 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK32-X3-vs-CSd01 = derive (X3 ∷ CK32 ∷ X3 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ [])
  (rw⁻ 2 q24 ∷
   rw⁻ 1 q25 ∷
   rw⁻ 0 q24 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = eqn (ι ∷ []) (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑)))))
  q27 : Eqn
  q27 = wE 420 W
  q28 : Eqn
  q28 = eqn (ι3 ∷ []) (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI))))

-- pass [CS13] [iI]: 3 steps
lem-pass-CS13-vs-iI : ⟪ (CS13 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-iI = derive (CS13 ∷ ι ∷ []) (ι ∷ CS13 ∷ [])
  (rw 1 q26 ∷
   rw 0 q27 ∷
   rw 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 421 W

-- pass [CS13] [Sd3]: 1 steps
lem-pass-CS13-vs-Sd3 : ⟪ (CS13 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-Sd3 = derive (CS13 ∷ S3⁻ ∷ []) (S3⁻ ∷ CS13 ∷ [])
  (rw 0 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = wE 422 W

-- pass [CS13] [S3]: 1 steps
lem-pass-CS13-vs-S3 : ⟪ (CS13 ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-S3 = derive (CS13 ∷ S3 ∷ []) (S3 ∷ CS13 ∷ [])
  (rw 0 q30 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = wE 1 W
  q32 : Eqn
  q32 = wE 173 W
  q33 : Eqn
  q33 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q34 : Eqn
  q34 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q35 : Eqn
  q35 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q36 : Eqn
  q36 = wE 3 W
  q37 : Eqn
  q37 = wE 56 W
  q38 : Eqn
  q38 = wE 423 W
  q39 : Eqn
  q39 = wE 175 W

-- pass [CS13] [X3 TOFF013 X3]: 65 steps
lem-pass-CS13-vs-X3-TOFF013-X3 : ⟪ (CS13 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-X3-TOFF013-X3 = derive (CS13 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS13 ∷ [])
  (rw 4 q31 ∷
   rw 3 q32 ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q33 ∷
   rw 5 q31 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q34 ∷
   rw 7 q31 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q34 ∷
   rw 9 q31 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q33 ∷
   rw⁻ 9 q35 ∷
   rw 10 q36 ∷
   rw 9 q35 ∷
   rw 8 q33 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q36 ∷
   rw 6 q34 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q36 ∷
   rw 4 q34 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q36 ∷
   rw 2 q33 ∷
   rw 3 q37 ∷
   re 3 8 (Toff012 ∷ []) ∷
   rw 1 q32 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q36 ∷
   rw 1 q38 ∷
   rw 0 q39 ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q33 ∷
   rw 4 q31 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q34 ∷
   rw 6 q31 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q34 ∷
   rw 8 q31 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q33 ∷
   rw⁻ 8 q35 ∷
   rw 1 q31 ∷
   rw⁻ 2 q33 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q36 ∷
   rw⁻ 4 q34 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q36 ∷
   rw⁻ 6 q34 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q36 ∷
   rw⁻ 8 q33 ∷
   rw⁻ 9 q35 ∷
   rw 2 q37 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 2 q39 ∷
   rw 5 q31 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw 4 q36 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = wE 26 W
  q41 : Eqn
  q41 = wE 75 W
  q42 : Eqn
  q42 = wE 39 W
  q43 : Eqn
  q43 = wE 29 W
  q44 : Eqn
  q44 = wE 91 W
  q45 : Eqn
  q45 = wE 424 W
  q46 : Eqn
  q46 = wE 20 W
  q47 : Eqn
  q47 = eqn (CS01⁻ ∷ CS23 ∷ []) (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS))
  q48 : Eqn
  q48 = wE 49 W
  q49 : Eqn
  q49 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q50 : Eqn
  q50 = wE 6 W
  q51 : Eqn
  q51 = wE 76 W
  q52 : Eqn
  q52 = wE 81 W

-- comm CCZ023 CS13: 131 steps
lem-comm-CCZ023-CS13 : ⟪ (CCZ023 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ023 ∷ []) ⟫ʷ
lem-comm-CCZ023-CS13 = derive (CCZ023 ∷ CS13 ∷ []) (CS13 ∷ CCZ023 ∷ [])
  (rw 1 q1 ∷
   re 0 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 0 q3 ∷
   rw 1 q4 ∷
   rw 2 q5 ∷
   rw 3 q4 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 5 q7 ∷
   rw 6 q6 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q9 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q6 ∷
   rw 5 q12 ∷
   rw⁻ 4 q6 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 3 q13 ∷
   rw⁻ 2 q5 ∷
   rw 1 q13 ∷
   rw⁻ 0 q3 ∷
   rw 1 q40 ∷
   re 1 5 (CCZ123 ∷ []) ∷
   rw 1 q41 ∷
   rw 0 q7 ∷
   re 2 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 1 q6 ∷
   rw 2 q42 ∷
   rw 3 q6 ∷
   re 1 3 (CX30 ∷ []) ∷
   rw 2 q43 ∷
   re 4 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 4 q42 ∷
   rw 5 q6 ∷
   re 3 3 (CX30 ∷ []) ∷
   rw 4 q3 ∷
   rw 5 q9 ∷
   rw 4 q44 ∷
   rw 5 q31 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q36 ∷
   re 3 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 5 q36 ∷
   rw 4 q45 ∷
   rw 5 q31 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw 6 q31 ∷
   re 4 3 (CX30 ∷ []) ∷
   rw 5 q36 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q31 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   re 3 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 9 q31 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 6 q46 ∷
   rw 5 q47 ∷
   rw 4 q48 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q36 ∷
   re 4 5 (CS03⁻ ∷ []) ∷
   re 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q36 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 3 q31 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q36 ∷
   re 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 3 q36 ∷
   rw 2 q45 ∷
   rw 3 q31 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 4 q31 ∷
   re 2 3 (CX30 ∷ []) ∷
   rw 3 q36 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q31 ∷
   re 1 3 (CS03 ∷ []) ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q31 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 4 q46 ∷
   rw 3 q49 ∷
   rw 2 q48 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q36 ∷
   re 2 5 (CS03 ∷ []) ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q36 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw 6 q1 ∷
   rw⁻ 5 q3 ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q6 ∷
   rw 5 q50 ∷
   rw⁻ 4 q6 ∷
   re 5 3 (CX31 ∷ []) ∷
   rw 3 q51 ∷
   re 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q6 ∷
   rw 3 q50 ∷
   rw⁻ 2 q6 ∷
   re 3 3 (CX31 ∷ []) ∷
   rw 1 q12 ∷
   rw 2 q52 ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q1 ∷
   rw 2 q3 ∷
   rw 3 q19 ∷
   rw 4 q5 ∷
   rw 5 q19 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q20 ∷
   rw 8 q6 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 2 q40 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 1 3 (CCZ023 ∷ []) ∷
   rw 2 q9 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q54 : Eqn
  q54 = wE 425 W

-- pass [CS13] [CSd01]: 9 steps
lem-pass-CS13-vs-CSd01 : ⟪ (CS13 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-CSd01 = derive (CS13 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS13 ∷ [])
  (rw 2 q31 ∷
   rw 1 q53 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q36 ∷
   rw 1 q54 ∷
   rw⁻ 0 q53 ∷
   rw 3 q31 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 2 q36 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q56 : Eqn
  q56 = wE 67 W

-- pass [CS13] [CS01]: 9 steps
lem-pass-CS13-vs-CS01 : ⟪ (CS13 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-CS01 = derive (CS13 ∷ CS01 ∷ []) (CS01 ∷ CS13 ∷ [])
  (rw 2 q31 ∷
   rw 1 q55 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q36 ∷
   rw 1 q56 ∷
   rw⁻ 0 q55 ∷
   rw 3 q31 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 2 q36 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q58 : Eqn
  q58 = eqn (X0 ∷ X2 ∷ []) (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑)))
  q59 : Eqn
  q59 = wE 393 W
  q60 : Eqn
  q60 = wE 394 W

-- b2g 1011R2: 4 steps
lem-b2g-1011R2 : ⟪ (X0 ∷ X2 ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ []) ⟫ʷ
lem-b2g-1011R2 = derive (X0 ∷ X2 ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ [])
  (rw 1 q57 ∷
   rw 11 q58 ∷
   rw 2 q59 ∷
   rw 10 q60 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = wE 426 W

-- pass [CS23] [iI]: 3 steps
lem-pass-CS23-vs-iI : ⟪ (CS23 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-iI = derive (CS23 ∷ ι ∷ []) (ι ∷ CS23 ∷ [])
  (rw 1 q26 ∷
   rw 0 q61 ∷
   rw 0 q28 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = wE 427 W

-- pass [CS23] [Sd3]: 1 steps
lem-pass-CS23-vs-Sd3 : ⟪ (CS23 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-Sd3 = derive (CS23 ∷ S3⁻ ∷ []) (S3⁻ ∷ CS23 ∷ [])
  (rw 0 q62 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 428 W

-- pass [CS23] [S3]: 1 steps
lem-pass-CS23-vs-S3 : ⟪ (CS23 ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-S3 = derive (CS23 ∷ S3 ∷ []) (S3 ∷ CS23 ∷ [])
  (rw 0 q63 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = wE 429 W

-- pass [TOFF201] [iI]: 1 steps
lem-pass-TOFF201-vs-iI : ⟪ (Toff201 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-TOFF201-vs-iI = derive (Toff201 ∷ ι ∷ []) (ι ∷ Toff201 ∷ [])
  (rw 0 q64 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = wE 430 W

-- pass [CSd23] [iI]: 3 steps
lem-pass-CSd23-vs-iI : ⟪ (CS23⁻ ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-CSd23-vs-iI = derive (CS23⁻ ∷ ι ∷ []) (ι ∷ CS23⁻ ∷ [])
  (rw 1 q26 ∷
   rw 0 q65 ∷
   rw 0 q28 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = wE 431 W

-- pass [Sd0] [CSd23]: 1 steps
lem-pass-Sd0-vs-CSd23 : ⟪ (S0⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-pass-Sd0-vs-CSd23 = derive (S0⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S0⁻ ∷ [])
  (rw 0 q66 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = wE 432 W

-- pass [Sd3] [CSd23]: 1 steps
lem-pass-Sd3-vs-CSd23 : ⟪ (S3⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S3⁻ ∷ []) ⟫ʷ
lem-pass-Sd3-vs-CSd23 = derive (S3⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S3⁻ ∷ [])
  (rw 0 q67 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = wE 433 W

-- pass [CS03] [CSd23]: 15 steps
lem-pass-CS03-vs-CSd23 : ⟪ (CS03 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-CSd23 = derive (CS03 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS03 ∷ [])
  (rw 2 q1 ∷
   rw⁻ 1 q5 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q6 ∷
   rw 1 q12 ∷
   rw⁻ 0 q6 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q68 ∷
   rw 0 q5 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q6 ∷
   rw 2 q7 ∷
   rw 3 q6 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q9 ∷ []) Eq.refl

private
  q69 : Eqn
  q69 = eqn (Sw01 ∷ S3⁻ ∷ []) (S3⁻ ∷ Sw01 ∷ []) (low-comm (Swap) (((S • S • S) ↑)))
  q70 : Eqn
  q70 = wE 434 W
  q71 : Eqn
  q71 = wE 435 W
  q72 : Eqn
  q72 = wE 436 W
  q73 : Eqn
  q73 = wE 437 W
  q74 : Eqn
  q74 = wE 316 W

-- pass [CS23] [iI Sd0 Sd3 CS03]: 23 steps
lem-pass-CS23-vs-iI-Sd0-Sd3-CS03 : ⟪ (CS23 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-iI-Sd0-Sd3-CS03 = derive (CS23 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ CS23 ∷ [])
  (rw 5 q1 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q6 ∷
   rw 5 q12 ∷
   rw⁻ 4 q6 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 3 q69 ∷
   rw 2 q70 ∷
   rw 1 q71 ∷
   rw⁻ 0 q3 ∷
   rw 2 q26 ∷
   rw 1 q72 ∷
   rw 1 q28 ∷
   rw 0 q73 ∷
   rw 1 q74 ∷
   rw 2 q69 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 4 q7 ∷
   rw 5 q6 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q3 ∷
   rw 5 q9 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = wE 438 W

-- pass [TOFF201] [Sd0]: 1 steps
lem-pass-TOFF201-vs-Sd0 : ⟪ (Toff201 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-TOFF201-vs-Sd0 = derive (Toff201 ∷ S0⁻ ∷ []) (S0⁻ ∷ Toff201 ∷ [])
  (rw 0 q75 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = eqn (Toff201 ∷ S3⁻ ∷ []) (S3⁻ ∷ Toff201 ∷ []) (low₃-comm (Toffᵗ) ((S • S • S)))

-- pass [TOFF201] [Sd3]: 1 steps
lem-pass-TOFF201-vs-Sd3 : ⟪ (Toff201 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-TOFF201-vs-Sd3 = derive (Toff201 ∷ S3⁻ ∷ []) (S3⁻ ∷ Toff201 ∷ [])
  (rw 0 q76 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = wE 439 W

-- pass [CSd23] [iI Sd0 Sd3 CS03]: 23 steps
lem-pass-CSd23-vs-iI-Sd0-Sd3-CS03 : ⟪ (CS23⁻ ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-CSd23-vs-iI-Sd0-Sd3-CS03 = derive (CS23⁻ ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ CS23⁻ ∷ [])
  (rw 5 q1 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q6 ∷
   rw 5 q12 ∷
   rw⁻ 4 q6 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 3 q69 ∷
   rw 2 q70 ∷
   rw 1 q71 ∷
   rw⁻ 0 q5 ∷
   rw 2 q26 ∷
   rw 1 q77 ∷
   rw 1 q28 ∷
   rw 0 q73 ∷
   rw 1 q74 ∷
   rw 2 q69 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 4 q7 ∷
   rw 5 q6 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q5 ∷
   rw 5 q9 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = wE 440 W

-- pass [CS23] [S2]: 1 steps
lem-pass-CS23-vs-S2 : ⟪ (CS23 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-S2 = derive (CS23 ∷ S2 ∷ []) (S2 ∷ CS23 ∷ [])
  (rw 0 q78 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = wE 441 W

-- pass [CS23] [Sd2]: 1 steps
lem-pass-CS23-vs-Sd2 : ⟪ (CS23 ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-Sd2 = derive (CS23 ∷ S2⁻ ∷ []) (S2⁻ ∷ CS23 ∷ [])
  (rw 0 q79 ∷ []) Eq.refl

private
  q80 : Eqn
  q80 = wE 442 W

-- pass [CS23] [S1]: 1 steps
lem-pass-CS23-vs-S1 : ⟪ (CS23 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-S1 = derive (CS23 ∷ S1 ∷ []) (S1 ∷ CS23 ∷ [])
  (rw 0 q80 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = wE 443 W

-- pass [CS23] [Sd1]: 1 steps
lem-pass-CS23-vs-Sd1 : ⟪ (CS23 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-Sd1 = derive (CS23 ∷ S1⁻ ∷ []) (S1⁻ ∷ CS23 ∷ [])
  (rw 0 q81 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = wE 444 W

-- pass [CCZ012] [CS01]: 1 steps
lem-pass-CCZ012-vs-CS01 : ⟪ (CCZ012 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CS01 = derive (CCZ012 ∷ CS01 ∷ []) (CS01 ∷ CCZ012 ∷ [])
  (rw 0 q82 ∷ []) Eq.refl

private
  q83 : Eqn
  q83 = wE 445 W

-- pass [S2] [CSd23]: 1 steps
lem-pass-S2-vs-CSd23 : ⟪ (S2 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S2 ∷ []) ⟫ʷ
lem-pass-S2-vs-CSd23 = derive (S2 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S2 ∷ [])
  (rw 0 q83 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = wE 446 W

-- pass [CCZ012] [CSd01]: 1 steps
lem-pass-CCZ012-vs-CSd01 : ⟪ (CCZ012 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CSd01 = derive (CCZ012 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ012 ∷ [])
  (rw 0 q84 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = wE 447 W

-- pass [Sd2] [CSd23]: 1 steps
lem-pass-Sd2-vs-CSd23 : ⟪ (S2⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S2⁻ ∷ []) ⟫ʷ
lem-pass-Sd2-vs-CSd23 = derive (S2⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S2⁻ ∷ [])
  (rw 0 q85 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q87 : Eqn
  q87 = wE 334 W
  q88 : Eqn
  q88 = wE 140 W
  q89 : Eqn
  q89 = wE 448 W
  q90 : Eqn
  q90 = wE 142 W

-- pass [X3 CK30 X3] [TOFF203]: 75 steps
lem-pass-X3-CK30-X3-vs-TOFF203 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-TOFF203 = derive (X3 ∷ CK30 ∷ X3 ∷ Toff203 ∷ []) (Toff203 ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 4 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 3 q86 ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q86 ∷
   rw 10 q8 ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw⁻ 9 q86 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q6 ∷
   rw 9 q12 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q13 ∷
   rw⁻ 6 q5 ∷
   rw 5 q13 ∷
   rw⁻ 4 q3 ∷
   rw⁻ 3 q86 ∷
   rw 4 q87 ∷
   re 4 8 (Toff213 ∷ []) ∷
   rw⁻ 2 q15 ∷
   re 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 2 q88 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (CK31 ∷ []) ∷
   rw⁻ 0 q15 ∷
   rw 1 q89 ∷
   re 1 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 0 q86 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q86 ∷
   rw 7 q8 ∷
   rw 0 q1 ∷
   rw 1 q86 ∷
   rw 2 q3 ∷
   rw 3 q19 ∷
   rw 4 q5 ∷
   rw 5 q19 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q20 ∷
   rw 8 q6 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q86 ∷
   rw 8 q21 ∷
   rw 1 q87 ∷
   re 1 8 (Toff213 ∷ []) ∷
   re 0 3 (Toff203 ∷ []) ∷
   rw 1 q15 ∷
   re 3 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw 3 q90 ∷
   rw 4 q6 ∷
   re 2 3 (CK30 ∷ []) ∷
   rw 3 q15 ∷
   rw 4 q9 ∷ []) Eq.refl

private
  q91 : Eqn
  q91 = wE 449 W

-- pass [X3 CS30 X3] [TOFF203]: 75 steps
lem-pass-X3-CS30-X3-vs-TOFF203 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-TOFF203 = derive (X3 ∷ CS03 ∷ X3 ∷ Toff203 ∷ []) (Toff203 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 4 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 3 q86 ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q86 ∷
   rw 10 q8 ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw⁻ 9 q86 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q6 ∷
   rw 9 q12 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q13 ∷
   rw⁻ 6 q5 ∷
   rw 5 q13 ∷
   rw⁻ 4 q3 ∷
   rw⁻ 3 q86 ∷
   rw 4 q87 ∷
   re 4 8 (Toff213 ∷ []) ∷
   rw⁻ 2 q15 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 2 q12 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 0 q15 ∷
   rw 1 q91 ∷
   re 1 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 0 q86 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q86 ∷
   rw 7 q8 ∷
   rw 0 q1 ∷
   rw 1 q86 ∷
   rw 2 q3 ∷
   rw 3 q19 ∷
   rw 4 q5 ∷
   rw 5 q19 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q20 ∷
   rw 8 q6 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q86 ∷
   rw 8 q21 ∷
   rw 1 q87 ∷
   re 1 8 (Toff213 ∷ []) ∷
   re 0 3 (Toff203 ∷ []) ∷
   rw 1 q15 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw 3 q7 ∷
   rw 4 q6 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q15 ∷
   rw 4 q9 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = wE 450 W

-- pass [X3 CSd30 X3] [TOFF203]: 75 steps
lem-pass-X3-CSd30-X3-vs-TOFF203 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-TOFF203 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ Toff203 ∷ []) (Toff203 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 4 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 3 q86 ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q86 ∷
   rw 10 q8 ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw⁻ 9 q86 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q6 ∷
   rw 9 q12 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q13 ∷
   rw⁻ 6 q5 ∷
   rw 5 q13 ∷
   rw⁻ 4 q3 ∷
   rw⁻ 3 q86 ∷
   rw 4 q87 ∷
   re 4 8 (Toff213 ∷ []) ∷
   rw⁻ 2 q15 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 2 q51 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 0 q15 ∷
   rw 1 q92 ∷
   re 1 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 0 q86 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q86 ∷
   rw 7 q8 ∷
   rw 0 q1 ∷
   rw 1 q86 ∷
   rw 2 q3 ∷
   rw 3 q19 ∷
   rw 4 q5 ∷
   rw 5 q19 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q20 ∷
   rw 8 q6 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q86 ∷
   rw 8 q21 ∷
   rw 1 q87 ∷
   re 1 8 (Toff213 ∷ []) ∷
   re 0 3 (Toff203 ∷ []) ∷
   rw 1 q15 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw 3 q43 ∷
   rw 4 q6 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q15 ∷
   rw 4 q9 ∷ []) Eq.refl

private
  q93 : Eqn
  q93 = wE 137 W
  q94 : Eqn
  q94 = wE 451 W
  q95 : Eqn
  q95 = wE 139 W

-- pass [X3 CKd30 X3] [TOFF203]: 75 steps
lem-pass-X3-CKd30-X3-vs-TOFF203 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-TOFF203 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ Toff203 ∷ []) (Toff203 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 4 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 3 q86 ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q86 ∷
   rw 10 q8 ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw⁻ 9 q86 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q6 ∷
   rw 9 q12 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q13 ∷
   rw⁻ 6 q5 ∷
   rw 5 q13 ∷
   rw⁻ 4 q3 ∷
   rw⁻ 3 q86 ∷
   rw 4 q87 ∷
   re 4 8 (Toff213 ∷ []) ∷
   rw⁻ 2 q15 ∷
   re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 2 q93 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (CK31⁻ ∷ []) ∷
   rw⁻ 0 q15 ∷
   rw 1 q94 ∷
   re 1 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 0 q86 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q86 ∷
   rw 7 q8 ∷
   rw 0 q1 ∷
   rw 1 q86 ∷
   rw 2 q3 ∷
   rw 3 q19 ∷
   rw 4 q5 ∷
   rw 5 q19 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q20 ∷
   rw 8 q6 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q86 ∷
   rw 8 q21 ∷
   rw 1 q87 ∷
   re 1 8 (Toff213 ∷ []) ∷
   re 0 3 (Toff203 ∷ []) ∷
   rw 1 q15 ∷
   re 3 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw 3 q95 ∷
   rw 4 q6 ∷
   re 2 3 (CK30⁻ ∷ []) ∷
   rw 3 q15 ∷
   rw 4 q9 ∷ []) Eq.refl

private
  q96 : Eqn
  q96 = eqn (X1 ∷ X2 ∷ []) (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X))
  q97 : Eqn
  q97 = eqn (X1 ∷ X3 ∷ []) (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑)))
  q98 : Eqn
  q98 = wE 452 W
  q99 : Eqn
  q99 = wE 453 W

-- b2g 0111R1: 4 steps
lem-b2g-0111R1 : ⟪ (X1 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-b2g-0111R1 = derive (X1 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ [])
  (rw 0 q96 ∷
   rw 1 q97 ∷
   rw 2 q98 ∷
   rw 10 q99 ∷ []) Eq.refl

private
  q100 : Eqn
  q100 = eqn (X0 ∷ X1 ∷ []) (X1 ∷ X0 ∷ []) (low₁-comm (X) (X))
  q101 : Eqn
  q101 = eqn (X0 ∷ X3 ∷ []) (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑)))
  q102 : Eqn
  q102 = wE 391 W
  q103 : Eqn
  q103 = wE 392 W

-- b2g 1111R0: 5 steps
lem-b2g-1111R0 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-b2g-1111R0 = derive (X0 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  (rw 0 q100 ∷
   rw 1 q58 ∷
   rw 2 q101 ∷
   rw 3 q102 ∷
   rw 11 q103 ∷ []) Eq.refl

private
  q104 : Eqn
  q104 = wE 454 W

-- pass [X1 CSd10 X1] [TOFF012]: 1 steps
lem-pass-X1-CSd10-X1-vs-TOFF012 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-TOFF012 = derive (X1 ∷ CS01⁻ ∷ X1 ∷ Toff012 ∷ []) (Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  (rw 0 q104 ∷ []) Eq.refl

private
  q105 : Eqn
  q105 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q106 : Eqn
  q106 = wE 455 W

-- pass [X1 CSd10 X1] [CS03]: 13 steps
lem-pass-X1-CSd10-X1-vs-CS03 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-CS03 = derive (X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ []) (CS03 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  (rw 4 q31 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q36 ∷
   rw 2 q105 ∷
   rw 1 q53 ∷
   rw 0 q105 ∷
   rw 1 q106 ∷
   rw 2 q31 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw⁻ 1 q105 ∷
   rw⁻ 2 q53 ∷
   rw⁻ 3 q105 ∷
   rw 4 q36 ∷ []) Eq.refl

private
  q107 : Eqn
  q107 = wE 456 W

-- pass [X1 CSd10 X1] [CSd03]: 13 steps
lem-pass-X1-CSd10-X1-vs-CSd03 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-CSd03 = derive (X1 ∷ CS01⁻ ∷ X1 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  (rw 4 q31 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q36 ∷
   rw 2 q105 ∷
   rw 1 q53 ∷
   rw 0 q105 ∷
   rw 1 q107 ∷
   rw 2 q31 ∷
   re 0 3 (CS03⁻ ∷ []) ∷
   rw⁻ 1 q105 ∷
   rw⁻ 2 q53 ∷
   rw⁻ 3 q105 ∷
   rw 4 q36 ∷ []) Eq.refl

private
  q108 : Eqn
  q108 = wE 100 W
  q109 : Eqn
  q109 = wE 416 W
  q110 : Eqn
  q110 = wE 457 W
  q111 : Eqn
  q111 = eqn (CS01⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((CS • CS • CS)))
  q112 : Eqn
  q112 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q113 : Eqn
  q113 = wE 104 W

-- comm CCZ012 CSd23: 19 steps
lem-comm-CCZ012-CSd23 : ⟪ (CCZ012 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-comm-CCZ012-CSd23 = derive (CCZ012 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ012 ∷ [])
  (rw 0 q108 ∷
   rw 4 q109 ∷
   rw 5 q1 ∷
   rw⁻ 4 q5 ∷
   rw 3 q50 ∷
   rw 4 q110 ∷
   rw 3 q5 ∷
   rw 4 q42 ∷
   rw 5 q9 ∷
   rw 2 q111 ∷
   rw 3 q1 ∷
   rw⁻ 2 q5 ∷
   rw 1 q50 ∷
   rw 2 q110 ∷
   rw 1 q5 ∷
   rw 2 q42 ∷
   rw 3 q9 ∷
   rw 0 q112 ∷
   rw 1 q113 ∷ []) Eq.refl

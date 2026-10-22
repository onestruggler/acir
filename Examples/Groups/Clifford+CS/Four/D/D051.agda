{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D051 (W : Ws) where

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
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 173 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = eqn (CK01 ∷ Sw23 ∷ []) (Sw23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (Swap))
  q5 : Eqn
  q5 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q6 : Eqn
  q6 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q7 : Eqn
  q7 = wE 546 W
  q8 : Eqn
  q8 = wE 175 W

-- pass [CS13 CS13 CK31 CS13 CK31 CK31 CX30 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX30 CS01 CS01 CK01 CS01 CK01 CK01] [X3 CKd31 X3]: 85 steps
lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CKd31-X3 : ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) ⟫ʷ
lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CKd31-X3 = derive (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (X3 ∷ CK31⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ [])
  (rw 32 q1 ∷
   rw 31 q2 ∷
   re 30 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 32 q3 ∷
   rw 29 q2 ∷
   rw 28 q4 ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   rw 25 q4 ∷
   rw 24 q5 ∷
   rw 23 q5 ∷
   re 22 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 24 q3 ∷
   rw 21 q5 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   rw 16 q5 ∷
   rw 15 q6 ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   rw 9 q4 ∷
   rw 8 q6 ∷
   rw 7 q4 ∷
   re 6 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   re 5 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   re 4 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   re 2 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q3 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q3 ∷
   rw 1 q7 ∷
   rw 0 q8 ∷
   rw 3 q1 ∷
   re 1 3 (CK31⁻ ∷ []) ∷
   rw 2 q8 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CK31 ∷ []) ∷
   rw 8 q1 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 9 q1 ∷
   re 7 3 (CK31 ∷ []) ∷
   rw 10 q1 ∷
   re 8 3 (CK31 ∷ []) ∷
   rw 11 q1 ∷
   re 9 3 (CX30 ∷ []) ∷
   rw⁻ 10 q4 ∷
   rw⁻ 11 q6 ∷
   rw⁻ 12 q4 ∷
   rw⁻ 13 q6 ∷
   rw⁻ 14 q5 ∷
   rw⁻ 15 q5 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 17 q4 ∷
   rw⁻ 18 q6 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 21 q5 ∷
   rw⁻ 22 q5 ∷
   rw⁻ 23 q5 ∷
   rw⁻ 24 q5 ∷
   rw 27 q1 ∷
   re 25 3 (CX30 ∷ []) ∷
   rw⁻ 26 q5 ∷
   rw⁻ 27 q5 ∷
   rw⁻ 28 q4 ∷
   rw⁻ 29 q5 ∷
   rw⁻ 30 q4 ∷
   rw⁻ 31 q4 ∷
   rw 32 q3 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = eqn (CK01 ∷ X3 ∷ []) (X3 ∷ CK01 ∷ []) (low-comm (CK₀₁) ((X ↑)))
  q10 : Eqn
  q10 = eqn (CK01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CK01 ∷ []) (low-comm (CK₀₁) ((S ↑ • CK₁₀)))
  q11 : Eqn
  q11 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q12 : Eqn
  q12 = eqn (CS01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CS01 ∷ []) (low-comm (CS) ((S ↑ • CK₁₀)))
  q13 : Eqn
  q13 = wE 5 W
  q14 : Eqn
  q14 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q15 : Eqn
  q15 = eqn (Sw01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑ • CK₁₀)))
  q16 : Eqn
  q16 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q17 : Eqn
  q17 = wE 6 W
  q18 : Eqn
  q18 = wE 547 W
  q19 : Eqn
  q19 = wE 39 W
  q20 : Eqn
  q20 = wE 31 W
  q21 : Eqn
  q21 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q22 : Eqn
  q22 = eqn (S0 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ S0 ∷ []) (low₁-comm (S) (((S ↑ • CK₁₀) ↑)))
  q23 : Eqn
  q23 = wE 548 W
  q24 : Eqn
  q24 = wE 549 W

-- pass [CS13 CS13 CK31 CS13 CK31 CK31 CX30 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX30 CS01 CS01 CK01 CS01 CK01 CK01] [X3 CKd32 X3]: 107 steps
lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CKd32-X3 : ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) ⟫ʷ
lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CKd32-X3 = derive (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (X3 ∷ CK32⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ [])
  (rw 28 q9 ∷
   rw 29 q10 ∷
   rw 30 q9 ∷
   rw 27 q9 ∷
   rw 28 q10 ∷
   rw 29 q9 ∷
   rw 26 q11 ∷
   rw 27 q12 ∷
   rw 28 q11 ∷
   rw 25 q9 ∷
   rw 26 q10 ∷
   rw 27 q9 ∷
   rw 24 q11 ∷
   rw 25 q12 ∷
   rw 26 q11 ∷
   rw 23 q11 ∷
   rw 24 q12 ∷
   rw 25 q11 ∷
   rw 26 q13 ∷
   rw⁻ 25 q14 ∷
   rw⁻ 24 q15 ∷
   rw⁻ 23 q14 ∷
   re 22 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q16 ∷
   rw 23 q17 ∷
   rw⁻ 22 q16 ∷
   re 23 3 (CX31 ∷ []) ∷
   rw 23 q18 ∷
   rw 22 q14 ∷
   rw 23 q15 ∷
   rw 24 q14 ∷
   re 26 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 25 q16 ∷
   rw 26 q19 ∷
   rw 27 q16 ∷
   re 25 3 (CX30 ∷ []) ∷
   rw 26 q20 ∷
   rw 21 q11 ∷
   rw 22 q12 ∷
   rw 23 q11 ∷
   rw 20 q11 ∷
   rw 21 q12 ∷
   rw 22 q11 ∷
   rw 19 q11 ∷
   rw 20 q12 ∷
   rw 21 q11 ∷
   rw 18 q11 ∷
   rw 19 q12 ∷
   rw 20 q11 ∷
   rw 17 q11 ∷
   rw 18 q12 ∷
   rw 19 q11 ∷
   rw 16 q11 ∷
   rw 17 q12 ∷
   rw 18 q11 ∷
   rw 15 q21 ∷
   rw 16 q22 ∷
   rw 17 q21 ∷
   rw 14 q9 ∷
   rw 15 q10 ∷
   rw 16 q9 ∷
   rw 13 q11 ∷
   rw 14 q12 ∷
   rw 15 q11 ∷
   rw 12 q11 ∷
   rw 13 q12 ∷
   rw 14 q11 ∷
   rw 11 q11 ∷
   rw 12 q12 ∷
   rw 13 q11 ∷
   rw 10 q21 ∷
   rw 11 q22 ∷
   rw 12 q21 ∷
   rw 9 q9 ∷
   rw 10 q10 ∷
   rw 11 q9 ∷
   rw 8 q21 ∷
   rw 9 q22 ∷
   rw 10 q21 ∷
   rw 7 q9 ∷
   rw 8 q10 ∷
   rw 9 q9 ∷
   rw 10 q13 ∷
   rw⁻ 9 q14 ∷
   rw⁻ 8 q15 ∷
   rw⁻ 7 q14 ∷
   re 6 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q16 ∷
   rw 7 q17 ∷
   rw⁻ 6 q16 ∷
   re 7 3 (CX31 ∷ []) ∷
   rw 7 q18 ∷
   rw 6 q14 ∷
   rw 7 q15 ∷
   rw 8 q14 ∷
   re 10 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 9 q16 ∷
   rw 10 q19 ∷
   rw 11 q16 ∷
   re 9 3 (CX30 ∷ []) ∷
   rw 10 q20 ∷
   rw 5 q23 ∷
   rw 4 q23 ∷
   rw 3 q24 ∷
   rw 2 q23 ∷
   rw 1 q24 ∷
   rw 0 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q26 : Eqn
  q26 = wE 30 W
  q27 : Eqn
  q27 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q28 : Eqn
  q28 = wE 27 W
  q29 : Eqn
  q29 = wE 7 W
  q30 : Eqn
  q30 = wE 74 W
  q31 : Eqn
  q31 = wE 26 W
  q32 : Eqn
  q32 = wE 75 W
  q33 : Eqn
  q33 = wE 29 W
  q34 : Eqn
  q34 = wE 550 W
  q35 : Eqn
  q35 = wE 107 W
  q36 : Eqn
  q36 = eqn (CX10 ∷ CZ23 ∷ []) (CZ23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (CZ))
  q37 : Eqn
  q37 = wE 108 W
  q38 : Eqn
  q38 = wE 551 W
  q39 : Eqn
  q39 = wE 552 W
  q40 : Eqn
  q40 = wE 76 W
  q41 : Eqn
  q41 = wE 81 W
  q42 : Eqn
  q42 = wE 24 W
  q43 : Eqn
  q43 = wE 25 W

-- comm CCZ023 CZ12: 99 steps
lem-comm-CCZ023-CZ12 : ⟪ (CCZ023 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CCZ023 ∷ []) ⟫ʷ
lem-comm-CCZ023-CZ12 = derive (CCZ023 ∷ CZ12 ∷ []) (CZ12 ∷ CCZ023 ∷ [])
  (rw 1 q13 ∷
   re 0 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 0 q25 ∷
   rw 1 q26 ∷
   rw 2 q27 ∷
   rw 3 q26 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q16 ∷
   rw 5 q28 ∷
   rw 6 q16 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q20 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q16 ∷
   rw 5 q29 ∷
   rw⁻ 4 q16 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 3 q30 ∷
   rw⁻ 2 q27 ∷
   rw 1 q30 ∷
   rw⁻ 0 q25 ∷
   rw 1 q31 ∷
   re 1 5 (CCZ123 ∷ []) ∷
   rw 1 q32 ∷
   rw 0 q28 ∷
   re 2 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 1 q16 ∷
   rw 2 q19 ∷
   rw 3 q16 ∷
   re 1 3 (CX30 ∷ []) ∷
   rw 2 q33 ∷
   re 4 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 3 q16 ∷
   rw 4 q19 ∷
   rw 5 q16 ∷
   re 3 3 (CX30 ∷ []) ∷
   rw 4 q25 ∷
   rw 5 q20 ∷
   rw 4 q34 ∷
   re 3 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 9 q1 ∷
   re 7 3 (CZ13 ∷ []) ∷
   rw 6 q35 ∷
   rw 5 q36 ∷
   rw 4 q37 ∷
   re 4 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 3 q3 ∷
   re 4 5 (CX30 ∷ []) ∷
   rw 2 q38 ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CZ13 ∷ []) ∷
   rw 4 q35 ∷
   rw 3 q36 ∷
   rw 2 q37 ∷
   re 2 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 1 q3 ∷
   re 2 5 (CX30 ∷ []) ∷
   rw 0 q39 ∷
   rw 6 q13 ∷
   rw⁻ 5 q25 ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q16 ∷
   rw 5 q17 ∷
   rw⁻ 4 q16 ∷
   re 5 3 (CX31 ∷ []) ∷
   rw 3 q40 ∷
   re 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q16 ∷
   rw 3 q17 ∷
   rw⁻ 2 q16 ∷
   re 3 3 (CX31 ∷ []) ∷
   rw 1 q29 ∷
   rw 2 q41 ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q25 ∷
   rw 2 q26 ∷
   rw 3 q27 ∷
   rw 4 q26 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q16 ∷
   rw 6 q28 ∷
   rw 7 q16 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q13 ∷
   rw 2 q25 ∷
   rw 3 q42 ∷
   rw 4 q27 ∷
   rw 5 q42 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q16 ∷
   rw 7 q43 ∷
   rw 8 q16 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 2 q31 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 1 3 (CCZ023 ∷ []) ∷
   rw 2 q20 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = wE 553 W

-- pass [CS13 CS13 CS13 CK31 CS13 CS13 CX32 CS12 CS12 CS12 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CX32 CS12 CS12 CS12 CK21 CS12 CS12] [X3 TOFF213 X3]: 1 steps
lem-pass-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-vs-X3-TOFF213-X3 : ⟪ (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ Toff213 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff213 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-vs-X3-TOFF213-X3 = derive (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ Toff213 ∷ X3 ∷ []) (X3 ∷ Toff213 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ [])
  (rw 0 q44 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 509 W

-- pass [CS13 CS13 CK31 CS13 CK31 CK31 CX32 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX32 CS12 CS12 CK21 CS12 CK21 CK21] [X3 TOFF213 X3]: 1 steps
lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-vs-X3-TOFF213-X3 : ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ Toff213 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff213 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-vs-X3-TOFF213-X3 = derive (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ Toff213 ∷ X3 ∷ []) (X3 ∷ Toff213 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ [])
  (rw 0 q45 ∷ []) Eq.refl

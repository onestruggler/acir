{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D003 (W : Ws) where

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
  q1 = wE 75 W
  q2 : Eqn
  q2 = wE 5 W
  q3 : Eqn
  q3 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = wE 7 W
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q6 : Eqn
  q6 = wE 91 W
  q7 : Eqn
  q7 = wE 27 W
  q8 : Eqn
  q8 = wE 31 W
  q9 : Eqn
  q9 = wE 1 W
  q10 : Eqn
  q10 = wE 3 W
  q11 : Eqn
  q11 = wE 92 W
  q12 : Eqn
  q12 = wE 84 W
  q13 : Eqn
  q13 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q14 : Eqn
  q14 = wE 47 W
  q15 : Eqn
  q15 = wE 65 W
  q16 : Eqn
  q16 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q17 : Eqn
  q17 = wE 48 W
  q18 : Eqn
  q18 = wE 81 W

-- comm CCZ123 CS03: 57 steps
lem-comm-CCZ123-CS03 : ⟪ (CCZ123 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CCZ123 ∷ []) ⟫ʷ
lem-comm-CCZ123-CS03 = derive (CCZ123 ∷ CS03 ∷ []) (CS03 ∷ CCZ123 ∷ [])
  (rw 0 q1 ∷
   rw 6 q2 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 6 q4 ∷
   rw⁻ 5 q3 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 4 q5 ∷
   rw 5 q6 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   rw 5 q7 ∷
   rw 6 q3 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q8 ∷
   rw 5 q9 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q10 ∷
   re 3 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 5 q10 ∷
   rw 4 q11 ∷
   rw 5 q9 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 6 q9 ∷
   re 4 3 (CX31 ∷ []) ∷
   rw 5 q10 ∷
   re 3 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 2 q9 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw 3 q12 ∷
   rw⁻ 4 q13 ∷
   rw 5 q14 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q10 ∷
   re 2 5 (CS03 ∷ []) ∷
   rw 3 q9 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q10 ∷
   re 1 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 3 q10 ∷
   rw 2 q11 ∷
   rw 3 q9 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 4 q9 ∷
   re 2 3 (CX31 ∷ []) ∷
   rw 3 q10 ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 0 q9 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q15 ∷
   rw⁻ 2 q16 ∷
   rw 3 q17 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q10 ∷
   re 0 5 (CS03 ∷ []) ∷
   rw 1 q18 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = wE 85 W
  q20 : Eqn
  q20 = wE 93 W
  q21 : Eqn
  q21 = wE 13 W
  q22 : Eqn
  q22 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q23 : Eqn
  q23 = wE 78 W
  q24 : Eqn
  q24 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q25 : Eqn
  q25 = wE 94 W
  q26 : Eqn
  q26 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q27 : Eqn
  q27 = wE 95 W
  q28 : Eqn
  q28 = wE 89 W

-- comm CCZ012 CS03: 53 steps
lem-comm-CCZ012-CS03 : ⟪ (CCZ012 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CCZ012 ∷ []) ⟫ʷ
lem-comm-CCZ012-CS03 = derive (CCZ012 ∷ CS03 ∷ []) (CS03 ∷ CCZ012 ∷ [])
  (rw 0 q19 ∷
   rw 6 q2 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 6 q4 ∷
   rw⁻ 5 q3 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 4 q4 ∷
   rw 5 q20 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   rw 5 q7 ∷
   rw 6 q3 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q7 ∷
   rw 6 q8 ∷
   re 4 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 3 q9 ∷
   re 4 3 (CX31 ∷ []) ∷
   rw 4 q21 ∷
   rw⁻ 5 q22 ∷
   rw 6 q23 ∷
   re 7 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 9 q10 ∷
   re 3 5 (CS03 ∷ []) ∷
   rw 4 q9 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q10 ∷
   rw 2 q24 ∷
   rw 3 q25 ∷
   rw 4 q9 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw⁻ 3 q24 ∷
   rw 4 q10 ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 1 q9 ∷
   re 2 3 (CX31 ∷ []) ∷
   rw 2 q21 ∷
   rw⁻ 3 q22 ∷
   rw 4 q23 ∷
   re 5 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 7 q10 ∷
   re 1 5 (CS03 ∷ []) ∷
   rw 2 q9 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q10 ∷
   rw 0 q26 ∷
   rw 1 q27 ∷
   rw 2 q9 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw⁻ 1 q26 ∷
   rw 2 q10 ∷
   rw 1 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 64 W
  q30 : Eqn
  q30 = eqn (K0 ∷ CZ13 ∷ []) (CZ13 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑ • CZ • Swap ↑)))
  q31 : Eqn
  q31 = wE 96 W
  q32 : Eqn
  q32 = eqn (CS01 ∷ CZ23 ∷ []) (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ))
  q33 : Eqn
  q33 = wE 97 W
  q34 : Eqn
  q34 = wE 98 W
  q35 : Eqn
  q35 = eqn (CS01⁻ ∷ CZ23 ∷ []) (CZ23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CZ))
  q36 : Eqn
  q36 = wE 99 W
  q37 : Eqn
  q37 = eqn (K0⁻ ∷ CZ13 ∷ []) (CZ13 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑ • CZ • Swap ↑)))
  q38 : Eqn
  q38 = wE 68 W

-- CZ13 passes T: 25 steps
lem-CZ13-passes-T : ⟪ (CZ13 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CZ13 ∷ []) ⟫ʷ
lem-CZ13-passes-T = derive (CZ13 ∷ Toff012 ∷ []) (Toff012 ∷ CZ13 ∷ [])
  (rw 1 q29 ∷
   rw⁻ 0 q30 ∷
   re 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 1 q31 ∷
   rw⁻ 2 q32 ∷
   rw 3 q33 ∷
   re 1 3 (CS02 ∷ []) ∷
   rw 2 q34 ∷
   re 4 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 3 q31 ∷
   rw⁻ 4 q35 ∷
   rw 5 q33 ∷
   re 3 3 (CS02⁻ ∷ []) ∷
   rw 4 q34 ∷
   rw 7 q9 ∷
   rw 6 q26 ∷
   re 5 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 7 q10 ∷
   rw 6 q36 ∷
   rw⁻ 5 q26 ∷
   rw 8 q9 ∷
   re 6 3 (CZ13 ∷ []) ∷
   rw 7 q10 ∷
   rw⁻ 6 q37 ∷
   rw 0 q38 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = wE 2 W
  q40 : Eqn
  q40 = wE 4 W
  q41 : Eqn
  q41 = wE 6 W
  q42 : Eqn
  q42 = wE 8 W
  q43 : Eqn
  q43 = wE 9 W
  q44 : Eqn
  q44 = wE 10 W
  q45 : Eqn
  q45 = wE 11 W
  q46 : Eqn
  q46 = wE 12 W
  q47 : Eqn
  q47 = wE 14 W
  q48 : Eqn
  q48 = wE 15 W
  q49 : Eqn
  q49 = wE 16 W
  q50 : Eqn
  q50 = wE 17 W
  q51 : Eqn
  q51 = eqn (CX32 ∷ CCZ012 ∷ CX32 ∷ []) (CCZ012 ∷ CCZ013 ∷ []) (ax cx-ccz)
  q52 : Eqn
  q52 = wE 18 W
  q53 : Eqn
  q53 = wE 19 W
  q54 : Eqn
  q54 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q55 : Eqn
  q55 = wE 20 W
  q56 : Eqn
  q56 = wE 21 W
  q57 : Eqn
  q57 = wE 22 W
  q58 : Eqn
  q58 = wE 23 W
  q59 : Eqn
  q59 = wE 24 W
  q60 : Eqn
  q60 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q61 : Eqn
  q61 = wE 25 W
  q62 : Eqn
  q62 = wE 26 W
  q63 : Eqn
  q63 = wE 28 W
  q64 : Eqn
  q64 = wE 29 W
  q65 : Eqn
  q65 = wE 30 W
  q66 : Eqn
  q66 = wE 32 W
  q67 : Eqn
  q67 = wE 33 W

-- comm CCZ123 CCZ012: 243 steps
lem-comm-CCZ123-CCZ012 : ⟪ (CCZ123 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ123 ∷ []) ⟫ʷ
lem-comm-CCZ123-CCZ012 = derive (CCZ123 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ123 ∷ [])
  (rw 2 q9 ∷
   rw 3 q39 ∷
   rw 4 q9 ∷
   re 2 3 (CX30 ∷ []) ∷
   rw 5 q9 ∷
   re 3 3 (CX30 ∷ []) ∷
   rw 4 q10 ∷
   rw 3 q40 ∷
   rw 4 q9 ∷
   rw 5 q39 ∷
   rw 6 q9 ∷
   re 4 3 (CX30 ∷ []) ∷
   rw 7 q9 ∷
   re 5 3 (CX30 ∷ []) ∷
   rw 6 q10 ∷
   rw 5 q2 ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw 5 q41 ∷
   rw⁻ 4 q3 ∷
   re 5 3 (CX31 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q4 ∷
   rw 6 q42 ∷
   rw 5 q43 ∷
   rw 4 q42 ∷
   rw 3 q44 ∷
   rw 4 q45 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 3 q41 ∷
   rw⁻ 2 q3 ∷
   re 3 3 (CX31 ∷ []) ∷
   rw 6 q46 ∷
   rw 5 q21 ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 10 q47 ∷
   rw 7 q46 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q48 ∷
   rw 5 q46 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q49 ∷
   rw 5 q50 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   rw 3 q21 ∷
   rw 4 q51 ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q52 ∷
   rw 6 q46 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 q53 ∷
   rw 8 q46 ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 q47 ∷
   rw 3 q50 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q9 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q54 ∷
   rw 9 q9 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q54 ∷
   rw 11 q9 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q10 ∷
   rw 4 q55 ∷
   rw 7 q46 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 q56 ∷
   rw 9 q46 ∷
   re 7 3 (CX02 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q57 ∷
   rw⁻ 10 q26 ∷
   rw 11 q58 ∷
   re 8 5 (CS03 ∷ []) ∷
   rw 4 q2 ∷
   rw 5 q5 ∷
   rw 6 q59 ∷
   rw 7 q60 ∷
   rw 8 q59 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q3 ∷
   rw 10 q61 ∷
   rw 11 q3 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q62 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 4 3 (CCZ023 ∷ []) ∷
   rw 5 q47 ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q7 ∷
   rw 3 q63 ∷
   rw 4 q64 ∷
   rw 5 q63 ∷
   rw 6 q61 ∷
   rw 2 q45 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q5 ∷
   rw 5 q65 ∷
   rw 6 q60 ∷
   rw 7 q65 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   rw 9 q7 ∷
   rw 10 q3 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q8 ∷
   rw 3 q5 ∷
   rw 4 q59 ∷
   rw 5 q60 ∷
   rw 6 q59 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   rw 8 q61 ∷
   rw 9 q3 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 3 q62 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   rw 4 q8 ∷
   rw 1 q66 ∷
   rw 0 q67 ∷
   rw 3 q2 ∷
   re 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 3 q41 ∷
   rw⁻ 2 q3 ∷
   re 3 3 (CX31 ∷ []) ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q4 ∷
   rw 4 q42 ∷
   rw 3 q43 ∷
   rw 2 q42 ∷
   rw 1 q44 ∷
   rw 2 q45 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 0 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 1 q41 ∷
   rw⁻ 0 q3 ∷
   re 1 3 (CX31 ∷ []) ∷
   rw 4 q46 ∷
   rw 3 q21 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   re 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 8 q47 ∷
   rw 5 q46 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q48 ∷
   rw 3 q46 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 2 q49 ∷
   rw 3 q50 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   rw 1 q21 ∷
   rw 2 q51 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 1 q52 ∷
   rw 4 q46 ∷
   re 2 3 (CX02 ∷ []) ∷
   rw 3 q53 ∷
   rw 6 q46 ∷
   re 4 3 (CX02 ∷ []) ∷
   re 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 5 q47 ∷
   rw 1 q50 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   re 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q9 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q54 ∷
   rw 7 q9 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q54 ∷
   rw 9 q9 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q10 ∷
   rw 2 q55 ∷
   rw 5 q46 ∷
   re 3 3 (CX02 ∷ []) ∷
   rw 4 q56 ∷
   rw 7 q46 ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 6 q57 ∷
   rw⁻ 8 q26 ∷
   rw 9 q58 ∷
   re 6 5 (CS03 ∷ []) ∷
   rw 2 q2 ∷
   rw 3 q5 ∷
   rw 4 q59 ∷
   rw 5 q60 ∷
   rw 6 q59 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   rw 8 q61 ∷
   rw 9 q3 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 3 q62 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   re 2 3 (CCZ023 ∷ []) ∷
   rw 3 q47 ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 0 q7 ∷
   rw 1 q63 ∷
   rw 2 q64 ∷
   rw 3 q63 ∷
   rw 4 q61 ∷
   rw 0 q45 ∷
   re 0 5 (CCZ012 ∷ []) ∷
   re 2 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 2 q5 ∷
   rw 3 q65 ∷
   rw 4 q60 ∷
   rw 5 q65 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw 7 q7 ∷
   rw 8 q3 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q8 ∷
   rw 1 q5 ∷
   rw 2 q59 ∷
   rw 3 q60 ∷
   rw 4 q59 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   rw 6 q61 ∷
   rw 7 q3 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 1 q62 ∷
   re 1 5 (CCZ123 ∷ []) ∷
   rw 2 q8 ∷ []) Eq.refl

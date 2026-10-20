{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D009 (W : Ws) where

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
  q1 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wn 65 W)
  q2 : Eqn
  q2 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q3 : Eqn
  q3 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)

-- pass [CS13] [CS02]: 5 steps
lem-pass-CS13-vs-CS02 : ⟪ (CS13 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-CS02 = derive (CS13 ∷ CS02 ∷ []) (CS02 ∷ CS13 ∷ [])
  (re 1 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 0 q1 ∷
   rw⁻ 1 q2 ∷
   rw 2 q3 ∷
   re 0 3 (CS02 ∷ []) ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q5 : Eqn
  q5 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q6 : Eqn
  q6 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q7 : Eqn
  q7 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q8 : Eqn
  q8 = eqn (CCZ012 ∷ CS12 ∷ []) (CS12 ∷ CCZ012 ∷ []) (wn 177 W)

-- pass [CCZ013] [CS13]: 49 steps
lem-pass-CCZ013-vs-CS13 : ⟪ (CCZ013 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CS13 = derive (CCZ013 ∷ CS13 ∷ []) (CS13 ∷ CCZ013 ∷ [])
  (rw 2 q4 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   re 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q4 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q6 ∷
   rw 4 q4 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 6 q4 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q5 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q6 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 1 q6 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q7 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   rw 1 q8 ∷
   rw 2 q4 ∷
   re 0 3 (CS13 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q4 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q6 ∷
   rw 5 q4 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q6 ∷
   rw 7 q4 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q4 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw⁻ 3 q6 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q6 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 2 q7 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = eqn (Toff012 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ Toff012 ∷ []) (wn 187 W)

-- pass [TOFF012] [X1 X2 TOFF012 X1 X2]: 1 steps
lem-pass-TOFF012-vs-X1-X2-TOFF012-X1-X2 : ⟪ (Toff012 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-X1-X2-TOFF012-X1-X2 = derive (Toff012 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ Toff012 ∷ [])
  (rw 0 q9 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = eqn (Z0 ∷ Sw23 ∷ []) (Sw23 ∷ Z0 ∷ []) (low₁-comm (Z) ((Swap ↑)))
  q11 : Eqn
  q11 = eqn (CCZ012 ∷ Z0 ∷ []) (Z0 ∷ CCZ012 ∷ []) (wn 188 W)

-- pass [CCZ013] [Z0]: 47 steps
lem-pass-CCZ013-vs-Z0 : ⟪ (CCZ013 ∷ Z0 ∷ []) ⟫ʷ ≈ ⟪ (Z0 ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-Z0 = derive (CCZ013 ∷ Z0 ∷ []) (Z0 ∷ CCZ013 ∷ [])
  (rw 2 q4 ∷
   rw 1 q10 ∷
   re 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q4 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q6 ∷
   rw 4 q4 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 6 q4 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q5 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q6 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 1 q6 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q7 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   rw 1 q11 ∷
   rw⁻ 0 q10 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q4 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q6 ∷
   rw 5 q4 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q6 ∷
   rw 7 q4 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q4 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw⁻ 3 q6 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q6 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 2 q7 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = eqn (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wn 85 W)
  q13 : Eqn
  q13 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q14 : Eqn
  q14 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q15 : Eqn
  q15 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q16 : Eqn
  q16 = eqn (CZ02 ∷ Sw01 ∷ []) (Sw01 ∷ CZ12 ∷ []) (wn 189 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q18 : Eqn
  q18 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q19 : Eqn
  q19 = eqn (CS13 ∷ CZ12 ∷ []) (CZ12 ∷ CS13 ∷ []) (wn 190 W)
  q20 : Eqn
  q20 = eqn (Sw01 ∷ CZ12 ∷ []) (CZ02 ∷ Sw01 ∷ []) (wn 191 W)
  q21 : Eqn
  q21 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q22 : Eqn
  q22 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q23 : Eqn
  q23 = eqn (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) (wn 13 W)
  q24 : Eqn
  q24 = eqn (CZ01 ∷ CX32 ∷ []) (CX32 ∷ CZ01 ∷ []) (low-comm (CZ) (CX₁₀))
  q25 : Eqn
  q25 = eqn (CX32 ∷ Sw12 ∷ []) (Sw12 ∷ CX31 ∷ []) (wn 78 W)
  q26 : Eqn
  q26 = eqn (CS01⁻ ∷ CZ02 ∷ []) (CZ02 ∷ CS01⁻ ∷ []) (wn 192 W)
  q27 : Eqn
  q27 = eqn (CS01 ∷ CZ02 ∷ []) (CZ02 ∷ CS01 ∷ []) (wn 193 W)
  q28 : Eqn
  q28 = eqn (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (CCZ012 ∷ []) (wn 89 W)

-- comm CCZ013 CZ02: 91 steps
lem-comm-CCZ013-CZ02 : ⟪ (CCZ013 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CZ02 = derive (CCZ013 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ013 ∷ [])
  (rw 1 q4 ∷
   re 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q4 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q6 ∷
   rw 4 q4 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 6 q4 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q5 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q6 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 1 q6 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q7 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   rw 1 q12 ∷
   rw⁻ 0 q13 ∷
   rw 3 q4 ∷
   re 1 3 (CX31 ∷ []) ∷
   rw⁻ 2 q14 ∷
   rw 5 q4 ∷
   re 3 3 (CX31 ∷ []) ∷
   rw 6 q4 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q15 ∷
   rw 5 q16 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q17 ∷
   rw 5 q18 ∷
   rw⁻ 4 q17 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 5 q19 ∷
   rw 4 q20 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q17 ∷
   rw 6 q21 ∷
   rw 7 q17 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q22 ∷
   re 4 1 (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) ∷
   rw 3 q23 ∷
   rw⁻ 4 q24 ∷
   rw 5 q25 ∷
   re 3 3 (CZ02 ∷ []) ∷
   rw 2 q26 ∷
   re 2 1 (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) ∷
   rw 1 q23 ∷
   rw⁻ 2 q24 ∷
   rw 3 q25 ∷
   re 1 3 (CZ02 ∷ []) ∷
   rw 0 q27 ∷
   rw 6 q4 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   re 4 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q14 ∷
   re 2 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 1 q13 ∷
   rw 2 q28 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q4 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q6 ∷
   rw 5 q4 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q6 ∷
   rw 7 q4 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q4 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw⁻ 3 q6 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q6 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 2 q7 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn (CS02 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ CS02 ∷ []) (wn 194 W)

-- pass [CS02] [X1 X2 TOFF012 X1 X2]: 1 steps
lem-pass-CS02-vs-X1-X2-TOFF012-X1-X2 : ⟪ (CS02 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS02-vs-X1-X2-TOFF012-X1-X2 = derive (CS02 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ CS02 ∷ [])
  (rw 0 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = eqn (CS02⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ CS02⁻ ∷ []) (wn 195 W)

-- pass [CSd02] [X1 X2 TOFF012 X1 X2]: 1 steps
lem-pass-CSd02-vs-X1-X2-TOFF012-X1-X2 : ⟪ (CS02⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd02-vs-X1-X2-TOFF012-X1-X2 = derive (CS02⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ CS02⁻ ∷ [])
  (rw 0 q30 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q32 : Eqn
  q32 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q33 : Eqn
  q33 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q34 : Eqn
  q34 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q35 : Eqn
  q35 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q36 : Eqn
  q36 = eqn (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 196 W)
  q37 : Eqn
  q37 = eqn (Toff102 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ []) (wn 197 W)
  q38 : Eqn
  q38 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)

-- pass [TOFF103] [X3 TOFF013 X3]: 115 steps
lem-pass-TOFF103-vs-X3-TOFF013-X3 : ⟪ (Toff103 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ Toff103 ∷ []) ⟫ʷ
lem-pass-TOFF103-vs-X3-TOFF013-X3 = derive (Toff103 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ Toff103 ∷ [])
  (rw 4 q4 ∷
   rw 3 q31 ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q32 ∷
   rw 5 q4 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q6 ∷
   rw 7 q4 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q6 ∷
   rw 9 q4 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q32 ∷
   rw⁻ 9 q33 ∷
   rw 10 q5 ∷
   rw 9 q33 ∷
   rw 8 q32 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 6 q6 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 4 q6 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 2 q32 ∷
   rw 3 q34 ∷
   re 3 8 (Toff012 ∷ []) ∷
   rw 1 q31 ∷
   re 0 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 0 q35 ∷
   rw 3 q4 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q6 ∷
   rw 5 q4 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q6 ∷
   rw 7 q4 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q35 ∷
   rw⁻ 7 q33 ∷
   rw 8 q5 ∷
   rw 7 q33 ∷
   rw 6 q35 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 4 q6 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 2 q6 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q35 ∷
   rw 1 q36 ∷
   re 1 8 (Toff102 ∷ []) ∷
   rw 1 q37 ∷
   rw 0 q38 ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q32 ∷
   rw 4 q4 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 6 q4 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q6 ∷
   rw 8 q4 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q32 ∷
   rw⁻ 8 q33 ∷
   rw 1 q4 ∷
   rw⁻ 2 q32 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw⁻ 4 q6 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q6 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw⁻ 8 q32 ∷
   rw⁻ 9 q33 ∷
   rw 2 q34 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 2 q38 ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 3 q35 ∷
   rw 6 q4 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q6 ∷
   rw 8 q4 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q6 ∷
   rw 10 q4 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q35 ∷
   rw⁻ 10 q33 ∷
   rw 3 q4 ∷
   rw⁻ 4 q35 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q6 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw⁻ 8 q6 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw⁻ 10 q35 ∷
   rw⁻ 11 q33 ∷
   rw 4 q36 ∷
   re 4 8 (Toff102 ∷ []) ∷
   re 3 3 (Toff103 ∷ []) ∷
   rw 4 q5 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = eqn (CCZ012 ∷ []) (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wn 100 W)
  q40 : Eqn
  q40 = eqn (CS13 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS13 ∷ []) (wn 198 W)
  q41 : Eqn
  q41 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q42 : Eqn
  q42 = eqn (CX10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CX10 ∷ []) (low-comm (CX₁₀) ((CS • CS • CS)))
  q43 : Eqn
  q43 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q44 : Eqn
  q44 = eqn (CS01⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS01⁻ ∷ []) (wn 199 W)
  q45 : Eqn
  q45 = eqn (CS01 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS01 ∷ []) (wn 200 W)
  q46 : Eqn
  q46 = eqn (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (CCZ012 ∷ []) (wn 104 W)

-- comm CCZ013 CSd12: 85 steps
lem-comm-CCZ013-CSd12 : ⟪ (CCZ013 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CSd12 = derive (CCZ013 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ013 ∷ [])
  (rw 1 q4 ∷
   re 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q4 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q6 ∷
   rw 4 q4 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 6 q4 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q5 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q6 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 1 q6 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q7 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   rw 1 q39 ∷
   rw⁻ 0 q13 ∷
   rw 3 q4 ∷
   re 1 3 (CX30 ∷ []) ∷
   rw⁻ 2 q14 ∷
   rw 5 q4 ∷
   re 3 3 (CX30 ∷ []) ∷
   rw 6 q4 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 5 q5 ∷
   rw 4 q40 ∷
   re 3 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 9 q4 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw 6 q41 ∷
   rw 5 q42 ∷
   rw 4 q43 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   re 4 5 (CX30 ∷ []) ∷
   rw 2 q44 ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q4 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw 4 q41 ∷
   rw 3 q42 ∷
   rw 2 q43 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   re 2 5 (CX30 ∷ []) ∷
   rw 0 q45 ∷
   rw 6 q4 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q14 ∷
   re 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 1 q13 ∷
   rw 2 q46 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q4 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q6 ∷
   rw 5 q4 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q6 ∷
   rw 7 q4 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q4 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw⁻ 3 q6 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q6 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 2 q7 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q48 : Eqn
  q48 = eqn (CS01⁻ ∷ CS23 ∷ []) (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS))
  q49 : Eqn
  q49 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)

-- pass [CSd02] [CS13]: 15 steps
lem-pass-CSd02-vs-CS13 : ⟪ (CS02⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd02-vs-CS13 = derive (CS02⁻ ∷ CS13 ∷ []) (CS13 ∷ CS02⁻ ∷ [])
  (re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q4 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q4 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 4 q47 ∷
   rw 3 q48 ∷
   rw 2 q49 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   re 2 5 (CS03⁻ ∷ []) ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   re 0 3 (CS13 ∷ []) ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = eqn (CS01⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((CS • CS • CS)))

-- pass [CSd02] [CSd13]: 15 steps
lem-pass-CSd02-vs-CSd13 : ⟪ (CS02⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd02-vs-CSd13 = derive (CS02⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS02⁻ ∷ [])
  (re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q4 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q4 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw 4 q41 ∷
   rw 3 q50 ∷
   rw 2 q43 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   re 2 5 (CS03⁻ ∷ []) ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   re 0 3 (CS13⁻ ∷ []) ∷ []) Eq.refl

-- pass [TOFF102] [X2 TOFF012 X2]: 1 steps
lem-pass-TOFF102-vs-X2-TOFF012-X2 : ⟪ (Toff102 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-TOFF102-vs-X2-TOFF012-X2 = derive (Toff102 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ [])
  (rw 0 q37 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = eqn (Toff102 ∷ S0 ∷ []) (S0 ∷ Toff102 ∷ []) (wn 201 W)

-- pass [TOFF102] [S0]: 1 steps
lem-pass-TOFF102-vs-S0 : ⟪ (Toff102 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-TOFF102-vs-S0 = derive (Toff102 ∷ S0 ∷ []) (S0 ∷ Toff102 ∷ [])
  (rw 0 q51 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = eqn (Toff102 ∷ S0⁻ ∷ []) (S0⁻ ∷ Toff102 ∷ []) (wn 202 W)

-- pass [TOFF102] [Sd0]: 1 steps
lem-pass-TOFF102-vs-Sd0 : ⟪ (Toff102 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-TOFF102-vs-Sd0 = derive (Toff102 ∷ S0⁻ ∷ []) (S0⁻ ∷ Toff102 ∷ [])
  (rw 0 q52 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = eqn (CS12 ∷ CS13 ∷ []) (CS13 ∷ CS12 ∷ []) (wn 93 W)
  q54 : Eqn
  q54 = eqn (CX10 ∷ CS23 ∷ []) (CS23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (CS))
  q55 : Eqn
  q55 = eqn (CS01⁻ ∷ CS12 ∷ []) (CS12 ∷ CS01⁻ ∷ []) (wn 102 W)
  q56 : Eqn
  q56 = eqn (CS01 ∷ CS12 ∷ []) (CS12 ∷ CS01 ∷ []) (wn 103 W)

-- comm CCZ012 CS13: 51 steps
lem-comm-CCZ012-CS13 : ⟪ (CCZ012 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ012 ∷ []) ⟫ʷ
lem-comm-CCZ012-CS13 = derive (CCZ012 ∷ CS13 ∷ []) (CS13 ∷ CCZ012 ∷ [])
  (rw 0 q39 ∷
   rw 4 q53 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   re 4 3 (CX30 ∷ []) ∷
   re 4 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q4 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 7 q47 ∷
   rw 6 q54 ∷
   rw 5 q49 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   re 5 5 (CX30 ∷ []) ∷
   re 5 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw 4 q4 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 2 q14 ∷
   rw 3 q55 ∷
   rw 4 q4 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q14 ∷
   rw 4 q5 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q4 ∷
   re 2 3 (CX30 ∷ []) ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q4 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 5 q47 ∷
   rw 4 q54 ∷
   rw 3 q49 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   re 3 5 (CX30 ∷ []) ∷
   re 3 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 2 q4 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q13 ∷
   rw 1 q56 ∷
   rw 2 q4 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q13 ∷
   rw 2 q5 ∷
   rw 1 q46 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q58 : Eqn
  q58 = eqn (CS12 ∷ S0 ∷ []) (S0 ∷ CS12 ∷ []) (wn 203 W)

-- pass [CS13] [S0]: 9 steps
lem-pass-CS13-vs-S0 : ⟪ (CS13 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-S0 = derive (CS13 ∷ S0 ∷ []) (S0 ∷ CS13 ∷ [])
  (rw 2 q4 ∷
   rw 1 q57 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q58 ∷
   rw⁻ 0 q57 ∷
   rw 3 q4 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = eqn (CS12 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS12 ∷ []) (wn 80 W)

-- pass [CS13] [CSd03]: 11 steps
lem-pass-CS13-vs-CSd03 : ⟪ (CS13 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-CSd03 = derive (CS13 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS13 ∷ [])
  (rw 2 q4 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q59 ∷
   rw 2 q4 ∷
   re 0 3 (CS03⁻ ∷ []) ∷
   rw 3 q4 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))
  q61 : Eqn
  q61 = eqn (CS12 ∷ S0⁻ ∷ []) (S0⁻ ∷ CS12 ∷ []) (wn 204 W)

-- pass [CS13] [Sd0]: 9 steps
lem-pass-CS13-vs-Sd0 : ⟪ (CS13 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-Sd0 = derive (CS13 ∷ S0⁻ ∷ []) (S0⁻ ∷ CS13 ∷ [])
  (rw 2 q4 ∷
   rw 1 q60 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q61 ∷
   rw⁻ 0 q60 ∷
   rw 3 q4 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = eqn (CS12 ∷ CS02 ∷ []) (CS02 ∷ CS12 ∷ []) (wn 205 W)

-- pass [CS13] [CS03]: 11 steps
lem-pass-CS13-vs-CS03 : ⟪ (CS13 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-CS03 = derive (CS13 ∷ CS03 ∷ []) (CS03 ∷ CS13 ∷ [])
  (rw 2 q4 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q62 ∷
   rw 2 q4 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 3 q4 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = eqn (CS12 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS12 ∷ []) (wn 86 W)

-- comm CCZ012 CSd13: 51 steps
lem-comm-CCZ012-CSd13 : ⟪ (CCZ012 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-comm-CCZ012-CSd13 = derive (CCZ012 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ012 ∷ [])
  (rw 0 q39 ∷
   rw 4 q63 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   re 4 3 (CX30 ∷ []) ∷
   re 4 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q4 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw 7 q41 ∷
   rw 6 q42 ∷
   rw 5 q43 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   re 5 5 (CX30 ∷ []) ∷
   re 5 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw 4 q4 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 2 q14 ∷
   rw 3 q44 ∷
   rw 4 q4 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q14 ∷
   rw 4 q5 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 1 q4 ∷
   re 2 3 (CX30 ∷ []) ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q4 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw 5 q41 ∷
   rw 4 q42 ∷
   rw 3 q43 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   re 3 5 (CX30 ∷ []) ∷
   re 3 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   re 1 3 (CS13⁻ ∷ []) ∷
   rw 2 q4 ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q13 ∷
   rw 1 q45 ∷
   rw 2 q4 ∷
   re 0 3 (CS13⁻ ∷ []) ∷
   rw⁻ 1 q13 ∷
   rw 2 q5 ∷
   rw 1 q46 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = eqn (CS12⁻ ∷ S0 ∷ []) (S0 ∷ CS12⁻ ∷ []) (wn 206 W)

-- pass [CSd13] [S0]: 9 steps
lem-pass-CSd13-vs-S0 : ⟪ (CS13⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd13-vs-S0 = derive (CS13⁻ ∷ S0 ∷ []) (S0 ∷ CS13⁻ ∷ [])
  (rw 2 q4 ∷
   rw 1 q57 ∷
   re 0 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q64 ∷
   rw⁻ 0 q57 ∷
   rw 3 q4 ∷
   re 1 3 (CS13⁻ ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = eqn (CS12⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS12⁻ ∷ []) (wn 79 W)

-- pass [CSd13] [CSd03]: 11 steps
lem-pass-CSd13-vs-CSd03 : ⟪ (CS13⁻ ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd13-vs-CSd03 = derive (CS13⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS13⁻ ∷ [])
  (rw 2 q4 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   re 0 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q65 ∷
   rw 2 q4 ∷
   re 0 3 (CS03⁻ ∷ []) ∷
   rw 3 q4 ∷
   re 1 3 (CS13⁻ ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = eqn (CS12⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ CS12⁻ ∷ []) (wn 207 W)

-- pass [CSd13] [Sd0]: 9 steps
lem-pass-CSd13-vs-Sd0 : ⟪ (CS13⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd13-vs-Sd0 = derive (CS13⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ CS13⁻ ∷ [])
  (rw 2 q4 ∷
   rw 1 q60 ∷
   re 0 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q66 ∷
   rw⁻ 0 q60 ∷
   rw 3 q4 ∷
   re 1 3 (CS13⁻ ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = eqn (CS12⁻ ∷ CS02 ∷ []) (CS02 ∷ CS12⁻ ∷ []) (wn 208 W)

-- pass [CSd13] [CS03]: 11 steps
lem-pass-CSd13-vs-CS03 : ⟪ (CS13⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd13-vs-CS03 = derive (CS13⁻ ∷ CS03 ∷ []) (CS03 ∷ CS13⁻ ∷ [])
  (rw 2 q4 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   re 0 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q67 ∷
   rw 2 q4 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 3 q4 ∷
   re 1 3 (CS13⁻ ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q69 : Eqn
  q69 = eqn (Toff102 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ Toff102 ∷ []) (wn 209 W)

-- pass [TOFF103] [X1 X3 TOFF013 X1 X3]: 119 steps
lem-pass-TOFF103-vs-X1-X3-TOFF013-X1-X3 : ⟪ (Toff103 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ Toff103 ∷ []) ⟫ʷ
lem-pass-TOFF103-vs-X1-X3-TOFF013-X1-X3 = derive (Toff103 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ Toff103 ∷ [])
  (rw 6 q4 ∷
   rw 5 q31 ∷
   rw 4 q68 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q32 ∷
   rw 6 q4 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q6 ∷
   rw 8 q4 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q6 ∷
   rw 10 q4 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q32 ∷
   rw⁻ 10 q33 ∷
   rw 11 q5 ∷
   rw 10 q33 ∷
   rw 9 q32 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw 7 q6 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 5 q6 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q32 ∷
   rw 4 q34 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 2 q31 ∷
   rw 1 q68 ∷
   re 0 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 0 q35 ∷
   rw 3 q4 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q6 ∷
   rw 5 q4 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q6 ∷
   rw 7 q4 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q35 ∷
   rw⁻ 7 q33 ∷
   rw 8 q5 ∷
   rw 7 q33 ∷
   rw 6 q35 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 4 q6 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 2 q6 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q35 ∷
   rw 1 q36 ∷
   re 1 8 (Toff102 ∷ []) ∷
   rw 1 q69 ∷
   rw⁻ 0 q68 ∷
   rw 1 q38 ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q32 ∷
   rw 5 q4 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q6 ∷
   rw 7 q4 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q6 ∷
   rw 9 q4 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q32 ∷
   rw⁻ 9 q33 ∷
   rw 2 q4 ∷
   rw⁻ 3 q32 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q6 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q6 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw⁻ 9 q32 ∷
   rw⁻ 10 q33 ∷
   rw 3 q34 ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 2 3 (Toff013 ∷ []) ∷
   rw⁻ 3 q68 ∷
   rw 4 q38 ∷
   re 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 5 q35 ∷
   rw 8 q4 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q6 ∷
   rw 10 q4 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q6 ∷
   rw 12 q4 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q35 ∷
   rw⁻ 12 q33 ∷
   rw 5 q4 ∷
   rw⁻ 6 q35 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw⁻ 8 q6 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw⁻ 10 q6 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw⁻ 12 q35 ∷
   rw⁻ 13 q33 ∷
   rw 6 q36 ∷
   re 6 8 (Toff102 ∷ []) ∷
   re 5 3 (Toff103 ∷ []) ∷
   rw 6 q5 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = eqn (S2 ∷ CS13 ∷ []) (CS13 ∷ S2 ∷ []) (wn 210 W)

-- pass [S2] [CS13]: 1 steps
lem-pass-S2-vs-CS13 : ⟪ (S2 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ S2 ∷ []) ⟫ʷ
lem-pass-S2-vs-CS13 = derive (S2 ∷ CS13 ∷ []) (CS13 ∷ S2 ∷ [])
  (rw 0 q70 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = eqn (S2 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S2 ∷ []) (wn 211 W)

-- pass [S2] [CSd13]: 1 steps
lem-pass-S2-vs-CSd13 : ⟪ (S2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ S2 ∷ []) ⟫ʷ
lem-pass-S2-vs-CSd13 = derive (S2 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S2 ∷ [])
  (rw 0 q71 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = eqn (S2⁻ ∷ CS13 ∷ []) (CS13 ∷ S2⁻ ∷ []) (wn 212 W)

-- pass [Sd2] [CS13]: 1 steps
lem-pass-Sd2-vs-CS13 : ⟪ (S2⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ S2⁻ ∷ []) ⟫ʷ
lem-pass-Sd2-vs-CS13 = derive (S2⁻ ∷ CS13 ∷ []) (CS13 ∷ S2⁻ ∷ [])
  (rw 0 q72 ∷ []) Eq.refl

private
  q73 : Eqn
  q73 = eqn (S2⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S2⁻ ∷ []) (wn 213 W)

-- pass [Sd2] [CSd13]: 1 steps
lem-pass-Sd2-vs-CSd13 : ⟪ (S2⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ S2⁻ ∷ []) ⟫ʷ
lem-pass-Sd2-vs-CSd13 = derive (S2⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S2⁻ ∷ [])
  (rw 0 q73 ∷ []) Eq.refl

private
  q74 : Eqn
  q74 = eqn (CZ13 ∷ Sw12 ∷ []) (Sw12 ∷ CZ23 ∷ []) (wn 96 W)
  q75 : Eqn
  q75 = eqn (CS01 ∷ CZ23 ∷ []) (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ))
  q76 : Eqn
  q76 = eqn (CZ23 ∷ Sw12 ∷ []) (Sw12 ∷ CZ13 ∷ []) (wn 97 W)

-- pass [CZ12] [CS03]: 9 steps
lem-pass-CZ12-vs-CS03 : ⟪ (CZ12 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CZ12 ∷ []) ⟫ʷ
lem-pass-CZ12-vs-CS03 = derive (CZ12 ∷ CS03 ∷ []) (CS03 ∷ CZ12 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 0 q4 ∷
   re 1 3 (CZ13 ∷ []) ∷
   rw 1 q74 ∷
   rw⁻ 2 q75 ∷
   rw 3 q76 ∷
   re 4 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   re 0 5 (CS03 ∷ []) ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = eqn (CCZ012 ∷ S0⁻ ∷ []) (S0⁻ ∷ CCZ012 ∷ []) (wn 214 W)

-- pass [CCZ012] [Sd0]: 1 steps
lem-pass-CCZ012-vs-Sd0 : ⟪ (CCZ012 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-Sd0 = derive (CCZ012 ∷ S0⁻ ∷ []) (S0⁻ ∷ CCZ012 ∷ [])
  (rw 0 q77 ∷ []) Eq.refl

-- pass [CS12] [Sd0]: 1 steps
lem-pass-CS12-vs-Sd0 : ⟪ (CS12 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-Sd0 = derive (CS12 ∷ S0⁻ ∷ []) (S0⁻ ∷ CS12 ∷ [])
  (rw 0 q61 ∷ []) Eq.refl

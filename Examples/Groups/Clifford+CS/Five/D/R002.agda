{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wlE)

module Examples.Groups.Clifford+CS.Five.D.R002 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

private
  q1 : WsL → Eqn
  q1 c4 = wlE 3 c4
  q2 : WsL → Eqn
  q2 c4 = wlE 28 c4
  q3 : WsL → Eqn
  q3 c4 = wlE 4 c4
  q4 : WsL → Eqn
  q4 c4 = wlE 12 c4
  q5 : WsL → Eqn
  q5 c4 = eqn (Toff102 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (CS • CS • CS))
  q6 : WsL → Eqn
  q6 c4 = wlE 9 c4
  q7 : WsL → Eqn
  q7 c4 = wlE 29 c4

-- comm CSd12 TOFF304: 15 steps
lem-comm-CSd12-TOFF304 : WsL → ⟪ (CS12⁻ ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-comm-CSd12-TOFF304 c4 = derive (CS12⁻ ∷ Toff304 ∷ []) (Toff304 ∷ CS12⁻ ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CS13⁻ ∷ []) ∷
   rw 1 (q2 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 3 3 (CS24⁻ ∷ []) ∷
   rw 3 (q4 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   re 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 8 (q3 c4) ∷
   rw 7 (q7 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 (q1 c4) ∷
   re 0 9 (Toff304 ∷ []) ∷ []) Eq.refl

-- comm TOFF304 CSd12: 15 steps
lem-comm-TOFF304-CSd12 : WsL → ⟪ (Toff304 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Toff304 ∷ []) ⟫ʷ
lem-comm-TOFF304-CSd12 c4 = derive (Toff304 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff304 ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q7 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (CS24⁻ ∷ []) ∷
   rw⁻ 5 (q6 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   re 3 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 9 (Toff304 ∷ []) ∷ []) Eq.refl

private
  q8 : WsL → Eqn
  q8 c4 = wlE 44 c4
  q9 : WsL → Eqn
  q9 c4 = eqn (CX10 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ))
  q10 : WsL → Eqn
  q10 c4 = wlE 37 c4

-- comm CX40 CCZ123: 13 steps
lem-comm-CX40-CCZ123 : WsL → ⟪ (CX40 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CX40 ∷ []) ⟫ʷ
lem-comm-CX40-CCZ123 c4 = derive (CX40 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX40 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (CCZ124 ∷ []) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CCZ134 ∷ []) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 3 (q9 c4) ∷
   rw⁻ 2 (q10 c4) ∷
   re 2 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 1 (q1 c4) ∷
   re 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 0 (q3 c4) ∷
   re 1 7 (CX40 ∷ []) ∷ []) Eq.refl

private
  q11 : WsL → Eqn
  q11 c4 = wlE 84 c4
  q12 : WsL → Eqn
  q12 c4 = eqn (CS01⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toffᵗ))
  q13 : WsL → Eqn
  q13 c4 = wlE 85 c4

-- comm CSd04 TOFF312: 13 steps
lem-comm-CSd04-TOFF312 : WsL → ⟪ (CS04⁻ ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-comm-CSd04-TOFF312 c4 = derive (CS04⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS04⁻ ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (Toff412 ∷ []) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (Toff413 ∷ []) ∷
   rw 4 (q11 c4) ∷
   rw 3 (q12 c4) ∷
   rw 2 (q13 c4) ∷
   re 2 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 1 (q1 c4) ∷
   re 1 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   rw 0 (q3 c4) ∷
   re 1 7 (CS04⁻ ∷ []) ∷ []) Eq.refl

private
  q14 : WsL → Eqn
  q14 c4 = eqn (CX10 ∷ Toff423 ∷ []) (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ))

-- comm CX40 TOFF312: 13 steps
lem-comm-CX40-TOFF312 : WsL → ⟪ (CX40 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CX40 ∷ []) ⟫ʷ
lem-comm-CX40-TOFF312 c4 = derive (CX40 ∷ Toff312 ∷ []) (Toff312 ∷ CX40 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (Toff412 ∷ []) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (Toff413 ∷ []) ∷
   rw 4 (q11 c4) ∷
   rw 3 (q14 c4) ∷
   rw 2 (q13 c4) ∷
   re 2 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 1 (q1 c4) ∷
   re 1 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   rw 0 (q3 c4) ∷
   re 1 7 (CX40 ∷ []) ∷ []) Eq.refl

private
  q15 : WsL → Eqn
  q15 c4 = wlE 33 c4
  q16 : WsL → Eqn
  q16 c4 = wlE 34 c4
  q17 : WsL → Eqn
  q17 c4 = eqn (Toff102 ∷ CZ34 ∷ []) (CZ34 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (CZ))
  q18 : WsL → Eqn
  q18 c4 = wlE 35 c4
  q19 : WsL → Eqn
  q19 c4 = wlE 36 c4

-- comm CZ12 TOFF304: 15 steps
lem-comm-CZ12-TOFF304 : WsL → ⟪ (CZ12 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CZ12 ∷ []) ⟫ʷ
lem-comm-CZ12-TOFF304 c4 = derive (CZ12 ∷ Toff304 ∷ []) (Toff304 ∷ CZ12 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CZ13 ∷ []) ∷
   rw 1 (q15 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 3 3 (CZ24 ∷ []) ∷
   rw 3 (q16 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 5 (q18 c4) ∷
   re 6 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) ∷
   rw 8 (q3 c4) ∷
   rw 7 (q19 c4) ∷
   re 8 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 10 (q1 c4) ∷
   re 0 9 (Toff304 ∷ []) ∷ []) Eq.refl

private
  q20 : WsL → Eqn
  q20 c4 = eqn (Toff201 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS • CS • CS))

-- comm CSd23 TOFF401: 9 steps
lem-comm-CSd23-TOFF401 : WsL → ⟪ (CS23⁻ ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-comm-CSd23-TOFF401 c4 = derive (CS23⁻ ∷ Toff401 ∷ []) (Toff401 ∷ CS23⁻ ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (CS24⁻ ∷ []) ∷
   rw 1 (q4 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   rw 3 (q6 c4) ∷
   re 4 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q3 c4) ∷
   re 0 5 (Toff401 ∷ []) ∷ []) Eq.refl

private
  q21 : WsL → Eqn
  q21 c4 = wlE 11 c4
  q22 : WsL → Eqn
  q22 c4 = eqn (Toff201 ∷ CS34 ∷ []) (CS34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS))
  q23 : WsL → Eqn
  q23 c4 = wlE 8 c4

-- comm CS23 TOFF401: 9 steps
lem-comm-CS23-TOFF401 : WsL → ⟪ (CS23 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CS23 ∷ []) ⟫ʷ
lem-comm-CS23-TOFF401 c4 = derive (CS23 ∷ Toff401 ∷ []) (Toff401 ∷ CS23 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (CS24 ∷ []) ∷
   rw 1 (q21 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw 3 (q23 c4) ∷
   re 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 6 (q3 c4) ∷
   re 0 5 (Toff401 ∷ []) ∷ []) Eq.refl

-- comm CSd24 TOFF301: 5 steps
lem-comm-CSd24-TOFF301 : WsL → ⟪ (CS24⁻ ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS24⁻ ∷ []) ⟫ʷ
lem-comm-CSd24-TOFF301 c4 = derive (CS24⁻ ∷ Toff301 ∷ []) (Toff301 ∷ CS24⁻ ∷ [])
  (re 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   rw 0 (q4 c4) ∷
   rw⁻ 1 (q20 c4) ∷
   rw 2 (q6 c4) ∷
   re 0 3 (Toff301 ∷ []) ∷ []) Eq.refl

-- comm CS24 TOFF301: 5 steps
lem-comm-CS24-TOFF301 : WsL → ⟪ (CS24 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS24 ∷ []) ⟫ʷ
lem-comm-CS24-TOFF301 c4 = derive (CS24 ∷ Toff301 ∷ []) (Toff301 ∷ CS24 ∷ [])
  (re 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   rw 0 (q21 c4) ∷
   rw⁻ 1 (q22 c4) ∷
   rw 2 (q23 c4) ∷
   re 0 3 (Toff301 ∷ []) ∷ []) Eq.refl

private
  q24 : WsL → Eqn
  q24 c4 = eqn (Sw02 ∷ Sw34 ∷ []) (Sw34 ∷ Sw02 ∷ []) (c₃ (Swap ↑ • Swap • Swap ↑) (Swap))
  q25 : WsL → Eqn
  q25 c4 = wlE 86 c4

-- comm SWAP02 BOX(3;14): 11 steps
lem-comm-SWAP02-BOX⟨3·14⟩ : WsL → ⟪ (Sw02 ∷ Bx3-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-14 ∷ Sw02 ∷ []) ⟫ʷ
lem-comm-SWAP02-BOX⟨3·14⟩ c4 = derive (Sw02 ∷ Bx3-14 ∷ []) (Bx3-14 ∷ Sw02 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   re 1 1 (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 0 (q24 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (Sw03 ∷ []) ∷
   rw⁻ 2 (q25 c4) ∷
   re 3 1 (Sw23 ∷ Sw02 ∷ Sw23 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw 4 (q24 c4) ∷
   re 0 5 (CZ14 ∷ []) ∷
   re 0 1 (Bx3-14 ∷ []) ∷ []) Eq.refl

private
  q26 : WsL → Eqn
  q26 c4 = eqn (Toff201 ∷ CZ34 ∷ []) (CZ34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CZ))

-- comm CZ12 TOFF403: 15 steps
lem-comm-CZ12-TOFF403 : WsL → ⟪ (CZ12 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CZ12 ∷ []) ⟫ʷ
lem-comm-CZ12-TOFF403 c4 = derive (CZ12 ∷ Toff403 ∷ []) (Toff403 ∷ CZ12 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CZ13 ∷ []) ∷
   rw 1 (q15 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 3 3 (CZ24 ∷ []) ∷
   rw 3 (q16 c4) ∷
   rw⁻ 4 (q26 c4) ∷
   rw 5 (q18 c4) ∷
   re 6 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) ∷
   rw 8 (q3 c4) ∷
   rw 7 (q19 c4) ∷
   re 8 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 10 (q1 c4) ∷
   re 0 9 (Toff403 ∷ []) ∷ []) Eq.refl

private
  q27 : WsL → Eqn
  q27 c4 = eqn (CS01 ∷ Toff423 ∷ []) (Toff423 ∷ CS01 ∷ []) (c₂ (CS) (Toffᵗ))

-- comm CS04 TOFF312: 13 steps
lem-comm-CS04-TOFF312 : WsL → ⟪ (CS04 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CS04 ∷ []) ⟫ʷ
lem-comm-CS04-TOFF312 c4 = derive (CS04 ∷ Toff312 ∷ []) (Toff312 ∷ CS04 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (Toff412 ∷ []) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (Toff413 ∷ []) ∷
   rw 4 (q11 c4) ∷
   rw 3 (q27 c4) ∷
   rw 2 (q13 c4) ∷
   re 2 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 1 (q1 c4) ∷
   re 1 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   rw 0 (q3 c4) ∷
   re 1 7 (CS04 ∷ []) ∷ []) Eq.refl

-- comm TOFF312 CS04: 13 steps
lem-comm-TOFF312-CS04 : WsL → ⟪ (Toff312 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Toff312 ∷ []) ⟫ʷ
lem-comm-TOFF312-CS04 c4 = derive (Toff312 ∷ CS04 ∷ []) (CS04 ∷ Toff312 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (Toff412 ∷ []) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (Toff413 ∷ []) ∷
   rw⁻ 2 (q13 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   re 5 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   re 6 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   rw 8 (q3 c4) ∷
   re 0 7 (CS04 ∷ []) ∷ []) Eq.refl

private
  q28 : WsL → Eqn
  q28 c4 = wlE 6 c4
  q29 : WsL → Eqn
  q29 c4 = wlE 87 c4
  q30 : WsL → Eqn
  q30 c4 = wlE 18 c4
  q31 : WsL → Eqn
  q31 c4 = eqn (Sw01 ∷ CK42 ∷ []) (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))

-- resp CK41 at 2: 4 steps
lem-resp-CK41-at-2 : WsL → ⟪ (CK41 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CK42 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CK41-at-2 c4 = derive (CK41 ∷ []) (Sw12 ∷ Sw01 ∷ CK42 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q28 c4) ∷
   rw 0 (q29 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw⁻ 1 (q31 c4) ∷ []) Eq.refl

private
  q32 : WsL → Eqn
  q32 c4 = wlE 45 c4
  q33 : WsL → Eqn
  q33 c4 = eqn (CS01 ∷ Toff324 ∷ []) (Toff324 ∷ CS01 ∷ []) (c₂ (CS) (K ↑ • CCZ • K ↑ • iI))
  q34 : WsL → Eqn
  q34 c4 = wlE 38 c4

-- comm CS04 TOFF213: 13 steps
lem-comm-CS04-TOFF213 : WsL → ⟪ (CS04 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CS04 ∷ []) ⟫ʷ
lem-comm-CS04-TOFF213 c4 = derive (CS04 ∷ Toff213 ∷ []) (Toff213 ∷ CS04 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (Toff214 ∷ []) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (Toff314 ∷ []) ∷
   rw 4 (q32 c4) ∷
   rw 3 (q33 c4) ∷
   rw 2 (q34 c4) ∷
   re 2 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 1 (q1 c4) ∷
   re 1 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   rw 0 (q3 c4) ∷
   re 1 7 (CS04 ∷ []) ∷ []) Eq.refl

private
  q35 : WsL → Eqn
  q35 c4 = wlE 14 c4
  q36 : WsL → Eqn
  q36 c4 = eqn (CCZ012 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS))
  q37 : WsL → Eqn
  q37 c4 = wlE 7 c4

-- comm CSd14 CCZ023: 7 steps
lem-comm-CSd14-CCZ023 : WsL → ⟪ (CS14⁻ ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CS14⁻ ∷ []) ⟫ʷ
lem-comm-CSd14-CCZ023 c4 = derive (CS14⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS14⁻ ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q35 c4) ∷
   rw 1 (q4 c4) ∷
   rw⁻ 2 (q36 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q37 c4) ∷
   re 0 5 (CCZ023 ∷ []) ∷ []) Eq.refl

private
  q38 : WsL → Eqn
  q38 c4 = wlE 13 c4
  q39 : WsL → Eqn
  q39 c4 = eqn (CCZ012 ∷ CS34 ∷ []) (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS))
  q40 : WsL → Eqn
  q40 c4 = wlE 5 c4

-- comm CS14 CCZ023: 7 steps
lem-comm-CS14-CCZ023 : WsL → ⟪ (CS14 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CS14 ∷ []) ⟫ʷ
lem-comm-CS14-CCZ023 c4 = derive (CS14 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS14 ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q38 c4) ∷
   rw 1 (q21 c4) ∷
   rw⁻ 2 (q39 c4) ∷
   rw 3 (q23 c4) ∷
   rw 4 (q40 c4) ∷
   re 0 5 (CCZ023 ∷ []) ∷ []) Eq.refl

private
  q41 : WsL → Eqn
  q41 c4 = eqn (Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap))
  q42 : WsL → Eqn
  q42 c4 = wlE 88 c4

-- comm push CK40 sw1 L: 5 steps
lem-comm-push-CK40-sw1-L : WsL → ⟪ (CK40 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK40 ∷ []) ⟫ʷ
lem-comm-push-CK40-sw1-L c4 = derive (CK40 ∷ Sw12 ∷ []) (Sw12 ∷ CK40 ∷ [])
  (re 0 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q41 c4) ∷
   rw 1 (q42 c4) ∷
   rw⁻ 0 (q41 c4) ∷
   re 1 3 (CK40 ∷ []) ∷ []) Eq.refl

private
  q43 : WsL → Eqn
  q43 c4 = eqn (CS01⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ))

-- comm CSd04 CCZ123: 13 steps
lem-comm-CSd04-CCZ123 : WsL → ⟪ (CS04⁻ ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-comm-CSd04-CCZ123 c4 = derive (CS04⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CS04⁻ ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (CCZ124 ∷ []) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CCZ134 ∷ []) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 3 (q43 c4) ∷
   rw⁻ 2 (q10 c4) ∷
   re 2 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 1 (q1 c4) ∷
   re 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 0 (q3 c4) ∷
   re 1 7 (CS04⁻ ∷ []) ∷ []) Eq.refl

private
  q44 : WsL → Eqn
  q44 c4 = eqn (CS01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ))

-- comm CS04 CCZ123: 13 steps
lem-comm-CS04-CCZ123 : WsL → ⟪ (CS04 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CS04 ∷ []) ⟫ʷ
lem-comm-CS04-CCZ123 c4 = derive (CS04 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS04 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (CCZ124 ∷ []) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CCZ134 ∷ []) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 3 (q44 c4) ∷
   rw⁻ 2 (q10 c4) ∷
   re 2 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 1 (q1 c4) ∷
   re 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 0 (q3 c4) ∷
   re 1 7 (CS04 ∷ []) ∷ []) Eq.refl

private
  q45 : WsL → Eqn
  q45 c4 = eqn (CK10 ∷ Toff324 ∷ []) (Toff324 ∷ CK10 ∷ []) (c₂ (CK₁₀) (K ↑ • CCZ • K ↑ • iI))

-- comm CK40 TOFF213: 13 steps
lem-comm-CK40-TOFF213 : WsL → ⟪ (CK40 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CK40 ∷ []) ⟫ʷ
lem-comm-CK40-TOFF213 c4 = derive (CK40 ∷ Toff213 ∷ []) (Toff213 ∷ CK40 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (Toff214 ∷ []) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (Toff314 ∷ []) ∷
   rw 4 (q32 c4) ∷
   rw 3 (q45 c4) ∷
   rw 2 (q34 c4) ∷
   re 2 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 1 (q1 c4) ∷
   re 1 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   rw 0 (q3 c4) ∷
   re 1 7 (CK40 ∷ []) ∷ []) Eq.refl

private
  q46 : WsL → Eqn
  q46 c4 = wlE 2 c4
  q47 : WsL → Eqn
  q47 c4 = eqn (CK10 ∷ Sw34 ∷ []) (Sw34 ∷ CK10 ∷ []) (c₂ (CK₁₀) (Swap ↑))

-- comm push CK40 sw2 L: 7 steps
lem-comm-push-CK40-sw2-L : WsL → ⟪ (CK40 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CK40 ∷ []) ⟫ʷ
lem-comm-push-CK40-sw2-L c4 = derive (CK40 ∷ Sw23 ∷ []) (Sw23 ∷ CK40 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q46 c4) ∷
   rw 4 (q41 c4) ∷
   rw 3 (q47 c4) ∷
   rw 2 (q41 c4) ∷
   rw⁻ 0 (q46 c4) ∷
   re 1 7 (CK40 ∷ []) ∷ []) Eq.refl

-- comm CSd13 TOFF204: 11 steps
lem-comm-CSd13-TOFF204 : WsL → ⟪ (CS13⁻ ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-comm-CSd13-TOFF204 c4 = derive (CS13⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS13⁻ ∷ [])
  (re 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw 0 (q2 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (CS24⁻ ∷ []) ∷
   rw 2 (q4 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 4 (q6 c4) ∷
   re 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 7 (q3 c4) ∷
   rw 6 (q7 c4) ∷
   re 0 7 (Toff204 ∷ []) ∷ []) Eq.refl

private
  q48 : WsL → Eqn
  q48 c4 = wlE 46 c4
  q49 : WsL → Eqn
  q49 c4 = eqn (Toff102 ∷ CS34 ∷ []) (CS34 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (CS))
  q50 : WsL → Eqn
  q50 c4 = wlE 47 c4

-- comm CS13 TOFF204: 11 steps
lem-comm-CS13-TOFF204 : WsL → ⟪ (CS13 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS13 ∷ []) ⟫ʷ
lem-comm-CS13-TOFF204 c4 = derive (CS13 ∷ Toff204 ∷ []) (Toff204 ∷ CS13 ∷ [])
  (re 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw 0 (q48 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (CS24 ∷ []) ∷
   rw 2 (q21 c4) ∷
   rw⁻ 3 (q49 c4) ∷
   rw 4 (q23 c4) ∷
   re 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 7 (q3 c4) ∷
   rw 6 (q50 c4) ∷
   re 0 7 (Toff204 ∷ []) ∷ []) Eq.refl

private
  q51 : WsL → Eqn
  q51 c4 = wlE 69 c4
  q52 : WsL → Eqn
  q52 c4 = wlE 58 c4
  q53 : WsL → Eqn
  q53 c4 = eqn (CCZ012 ∷ CX43 ∷ []) (CX43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₁₀))
  q54 : WsL → Eqn
  q54 c4 = wlE 59 c4
  q55 : WsL → Eqn
  q55 c4 = wlE 89 c4

-- comm CX41 CCZ023: 7 steps
lem-comm-CX41-CCZ023 : WsL → ⟪ (CX41 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CX41 ∷ []) ⟫ʷ
lem-comm-CX41-CCZ023 c4 = derive (CX41 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX41 ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q51 c4) ∷
   rw 1 (q52 c4) ∷
   rw⁻ 2 (q53 c4) ∷
   rw 3 (q54 c4) ∷
   rw 4 (q55 c4) ∷
   re 0 5 (CCZ023 ∷ []) ∷ []) Eq.refl

private
  q56 : WsL → Eqn
  q56 c4 = eqn (CZ01 ∷ Toff324 ∷ []) (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI))

-- comm CZ03 TOFF214: 9 steps
lem-comm-CZ03-TOFF214 : WsL → ⟪ (CZ03 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CZ03 ∷ []) ⟫ʷ
lem-comm-CZ03-TOFF214 c4 = derive (CZ03 ∷ Toff214 ∷ []) (Toff214 ∷ CZ03 ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (Toff314 ∷ []) ∷
   rw 3 (q32 c4) ∷
   rw 2 (q56 c4) ∷
   rw 1 (q34 c4) ∷
   re 1 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 5 (CZ03 ∷ []) ∷ []) Eq.refl

private
  q57 : WsL → Eqn
  q57 c4 = eqn (CS01⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))

-- comm TOFF214 CSd03: 9 steps
lem-comm-TOFF214-CSd03 : WsL → ⟪ (Toff214 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Toff214 ∷ []) ⟫ʷ
lem-comm-TOFF214-CSd03 c4 = derive (Toff214 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff214 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (Toff314 ∷ []) ∷
   rw⁻ 1 (q34 c4) ∷
   rw⁻ 2 (q57 c4) ∷
   rw⁻ 3 (q32 c4) ∷
   re 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 0 5 (CS03⁻ ∷ []) ∷ []) Eq.refl

-- comm CSd14 TOFF203: 7 steps
lem-comm-CSd14-TOFF203 : WsL → ⟪ (CS14⁻ ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CS14⁻ ∷ []) ⟫ʷ
lem-comm-CSd14-TOFF203 c4 = derive (CS14⁻ ∷ Toff203 ∷ []) (Toff203 ∷ CS14⁻ ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q35 c4) ∷
   rw 1 (q4 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q37 c4) ∷
   re 0 5 (Toff203 ∷ []) ∷ []) Eq.refl

private
  q58 : WsL → Eqn
  q58 c4 = eqn (CZ01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ))

-- comm CZ03 CCZ124: 9 steps
lem-comm-CZ03-CCZ124 : WsL → ⟪ (CZ03 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CZ03 ∷ []) ⟫ʷ
lem-comm-CZ03-CCZ124 c4 = derive (CZ03 ∷ CCZ124 ∷ []) (CCZ124 ∷ CZ03 ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CCZ134 ∷ []) ∷
   rw⁻ 3 (q8 c4) ∷
   rw 2 (q58 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   re 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 5 (CZ03 ∷ []) ∷ []) Eq.refl

private
  q59 : WsL → Eqn
  q59 c4 = eqn (CX01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ))

-- comm CX03 CCZ124: 9 steps
lem-comm-CX03-CCZ124 : WsL → ⟪ (CX03 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CX03 ∷ []) ⟫ʷ
lem-comm-CX03-CCZ124 c4 = derive (CX03 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX03 ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CCZ134 ∷ []) ∷
   rw⁻ 3 (q8 c4) ∷
   rw 2 (q59 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   re 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 5 (CX03 ∷ []) ∷ []) Eq.refl

-- comm CSd03 TOFF214: 9 steps
lem-comm-CSd03-TOFF214 : WsL → ⟪ (CS03⁻ ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-comm-CSd03-TOFF214 c4 = derive (CS03⁻ ∷ Toff214 ∷ []) (Toff214 ∷ CS03⁻ ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (Toff314 ∷ []) ∷
   rw 3 (q32 c4) ∷
   rw 2 (q57 c4) ∷
   rw 1 (q34 c4) ∷
   re 1 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 5 (CS03⁻ ∷ []) ∷ []) Eq.refl

private
  q60 : WsL → Eqn
  q60 c4 = wlE 90 c4
  q61 : WsL → Eqn
  q61 c4 = eqn (CCZ012 ∷ CK43 ∷ []) (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀))
  q62 : WsL → Eqn
  q62 c4 = wlE 91 c4
  q63 : WsL → Eqn
  q63 c4 = wlE 92 c4

-- comm CK41 CCZ023: 7 steps
lem-comm-CK41-CCZ023 : WsL → ⟪ (CK41 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CK41 ∷ []) ⟫ʷ
lem-comm-CK41-CCZ023 c4 = derive (CK41 ∷ CCZ023 ∷ []) (CCZ023 ∷ CK41 ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q29 c4) ∷
   rw 1 (q60 c4) ∷
   rw⁻ 2 (q61 c4) ∷
   rw 3 (q62 c4) ∷
   rw 4 (q63 c4) ∷
   re 0 5 (CCZ023 ∷ []) ∷ []) Eq.refl

private
  q64 : WsL → Eqn
  q64 c4 = eqn (Toff012 ∷ CK43 ∷ []) (CK43 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₁₀))

-- comm CK41 TOFF023: 7 steps
lem-comm-CK41-TOFF023 : WsL → ⟪ (CK41 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CK41 ∷ []) ⟫ʷ
lem-comm-CK41-TOFF023 c4 = derive (CK41 ∷ Toff023 ∷ []) (Toff023 ∷ CK41 ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q29 c4) ∷
   rw 1 (q60 c4) ∷
   rw⁻ 2 (q64 c4) ∷
   rw 3 (q62 c4) ∷
   rw 4 (q63 c4) ∷
   re 0 5 (Toff023 ∷ []) ∷ []) Eq.refl

private
  q65 : WsL → Eqn
  q65 c4 = eqn (Toff012 ∷ CS34 ∷ []) (CS34 ∷ Toff012 ∷ []) (c₃ (Toff) (CS))

-- comm CS23 TOFF014: 9 steps
lem-comm-CS23-TOFF014 : WsL → ⟪ (CS23 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CS23 ∷ []) ⟫ʷ
lem-comm-CS23-TOFF014 c4 = derive (CS23 ∷ Toff014 ∷ []) (Toff014 ∷ CS23 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (CS24 ∷ []) ∷
   rw 1 (q21 c4) ∷
   rw⁻ 2 (q65 c4) ∷
   rw 3 (q23 c4) ∷
   re 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 6 (q3 c4) ∷
   re 0 5 (Toff014 ∷ []) ∷ []) Eq.refl

private
  q66 : WsL → Eqn
  q66 c4 = eqn (Toff012 ∷ CZ34 ∷ []) (CZ34 ∷ Toff012 ∷ []) (c₃ (Toff) (CZ))

-- comm CZ13 TOFF024: 11 steps
lem-comm-CZ13-TOFF024 : WsL → ⟪ (CZ13 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CZ13 ∷ []) ⟫ʷ
lem-comm-CZ13-TOFF024 c4 = derive (CZ13 ∷ Toff024 ∷ []) (Toff024 ∷ CZ13 ∷ [])
  (re 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw 0 (q15 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (CZ24 ∷ []) ∷
   rw 2 (q16 c4) ∷
   rw⁻ 3 (q66 c4) ∷
   rw 4 (q18 c4) ∷
   re 5 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) ∷
   rw 7 (q3 c4) ∷
   rw 6 (q19 c4) ∷
   re 0 7 (Toff024 ∷ []) ∷ []) Eq.refl

-- comm CK42 CCZ013: 5 steps
lem-comm-CK42-CCZ013 : WsL → ⟪ (CK42 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CK42 ∷ []) ⟫ʷ
lem-comm-CK42-CCZ013 c4 = derive (CK42 ∷ CCZ013 ∷ []) (CCZ013 ∷ CK42 ∷ [])
  (re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   rw 0 (q60 c4) ∷
   rw⁻ 1 (q61 c4) ∷
   rw 2 (q62 c4) ∷
   re 0 3 (CCZ013 ∷ []) ∷ []) Eq.refl

-- comm CK42 TOFF013: 5 steps
lem-comm-CK42-TOFF013 : WsL → ⟪ (CK42 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CK42 ∷ []) ⟫ʷ
lem-comm-CK42-TOFF013 c4 = derive (CK42 ∷ Toff013 ∷ []) (Toff013 ∷ CK42 ∷ [])
  (re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   rw 0 (q60 c4) ∷
   rw⁻ 1 (q64 c4) ∷
   rw 2 (q62 c4) ∷
   re 0 3 (Toff013 ∷ []) ∷ []) Eq.refl

private
  q67 : WsL → Eqn
  q67 c4 = wlE 74 c4
  q68 : WsL → Eqn
  q68 c4 = wlE 72 c4
  q69 : WsL → Eqn
  q69 c4 = eqn (CZ01 ∷ Sw24 ∷ []) (Sw24 ∷ CZ01 ∷ []) (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))
  q70 : WsL → Eqn
  q70 c4 = wlE 93 c4

-- comm SWAP14 BOX(2;03): 9 steps
lem-comm-SWAP14-BOX⟨2·03⟩ : WsL → ⟪ (Sw14 ∷ Bx2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-03 ∷ Sw14 ∷ []) ⟫ʷ
lem-comm-SWAP14-BOX⟨2·03⟩ c4 = derive (Sw14 ∷ Bx2-03 ∷ []) (Bx2-03 ∷ Sw14 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 0 (q67 c4) ∷
   rw⁻ 1 (q68 c4) ∷
   rw⁻ 2 (q69 c4) ∷
   rw⁻ 3 (q70 c4) ∷
   rw 4 (q67 c4) ∷
   re 0 5 (CZ03 ∷ []) ∷
   re 0 1 (Bx2-03 ∷ []) ∷ []) Eq.refl

private
  q71 : WsL → Eqn
  q71 c4 = wlE 55 c4
  q72 : WsL → Eqn
  q72 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))

-- resp SWAP24 at 3: 6 steps
lem-resp-SWAP24-at-3 : WsL → ⟪ (Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-SWAP24-at-3 c4 = derive (Sw24 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw⁻ 0 (q71 c4) ∷
   rw⁻ 2 (q28 c4) ∷
   rw⁻ 1 (q41 c4) ∷
   rw⁻ 3 (q30 c4) ∷
   rw⁻ 2 (q72 c4) ∷ []) Eq.refl

private
  q73 : WsL → Eqn
  q73 c4 = eqn (CZ12 ∷ Sw34 ∷ []) (Sw34 ∷ CZ12 ∷ []) (c₃ (CZ ↑) (Swap))
  q74 : WsL → Eqn
  q74 c4 = wlE 56 c4

-- comm SWAP24 BOX(0;13): 7 steps
lem-comm-SWAP24-BOX⟨0·13⟩ : WsL → ⟪ (Sw24 ∷ Bx0-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-13 ∷ Sw24 ∷ []) ⟫ʷ
lem-comm-SWAP24-BOX⟨0·13⟩ c4 = derive (Sw24 ∷ Bx0-13 ∷ []) (Bx0-13 ∷ Sw24 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   re 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q71 c4) ∷
   rw⁻ 1 (q73 c4) ∷
   rw⁻ 2 (q74 c4) ∷
   re 0 3 (CZ13 ∷ []) ∷
   re 0 1 (Bx0-13 ∷ []) ∷ []) Eq.refl

-- comm SWAP23 BOX(0;41): 11 steps
lem-comm-SWAP23-BOX⟨0·41⟩ : WsL → ⟪ (Sw23 ∷ Bx0-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-41 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-SWAP23-BOX⟨0·41⟩ c4 = derive (Sw23 ∷ Bx0-41 ∷ []) (Bx0-41 ∷ Sw23 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   re 1 1 (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (Sw24 ∷ []) ∷
   rw⁻ 1 (q71 c4) ∷
   rw⁻ 2 (q73 c4) ∷
   rw⁻ 3 (q74 c4) ∷
   re 4 1 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q3 c4) ∷
   re 0 5 (CZ14 ∷ []) ∷
   re 0 1 (Bx0-41 ∷ []) ∷ []) Eq.refl

-- comm TOFF213 CSd04: 13 steps
lem-comm-TOFF213-CSd04 : WsL → ⟪ (Toff213 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Toff213 ∷ []) ⟫ʷ
lem-comm-TOFF213-CSd04 c4 = derive (Toff213 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Toff213 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (Toff214 ∷ []) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (Toff314 ∷ []) ∷
   rw⁻ 2 (q34 c4) ∷
   rw⁻ 3 (q57 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   re 5 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   re 6 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   rw 8 (q3 c4) ∷
   re 0 7 (CS04⁻ ∷ []) ∷ []) Eq.refl

-- comm TOFF213 CK40: 13 steps
lem-comm-TOFF213-CK40 : WsL → ⟪ (Toff213 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Toff213 ∷ []) ⟫ʷ
lem-comm-TOFF213-CK40 c4 = derive (Toff213 ∷ CK40 ∷ []) (CK40 ∷ Toff213 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (Toff214 ∷ []) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (Toff314 ∷ []) ∷
   rw⁻ 2 (q34 c4) ∷
   rw⁻ 3 (q45 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   re 5 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   re 6 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   rw 8 (q3 c4) ∷
   re 0 7 (CK40 ∷ []) ∷ []) Eq.refl

-- comm CCZ013 CK42: 15 steps
lem-comm-CCZ013-CK42 : WsL → ⟪ (CCZ013 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CK42 c4 = derive (CCZ013 ∷ CK42 ∷ []) (CK42 ∷ CCZ013 ∷ [])
  (re 1 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (CCZ014 ∷ []) ∷
   re 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CK42 ∷ []) ∷
   rw⁻ 4 (q62 c4) ∷
   rw 3 (q61 c4) ∷
   rw⁻ 2 (q60 c4) ∷
   re 2 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw 1 (q3 c4) ∷
   re 2 5 (CCZ014 ∷ []) ∷
   re 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   rw 4 (q3 c4) ∷
   re 0 3 (CK42 ∷ []) ∷ []) Eq.refl

-- comm TOFF013 CK42: 15 steps
lem-comm-TOFF013-CK42 : WsL → ⟪ (Toff013 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Toff013 ∷ []) ⟫ʷ
lem-comm-TOFF013-CK42 c4 = derive (Toff013 ∷ CK42 ∷ []) (CK42 ∷ Toff013 ∷ [])
  (re 1 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (Toff014 ∷ []) ∷
   re 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CK42 ∷ []) ∷
   rw⁻ 4 (q62 c4) ∷
   rw 3 (q64 c4) ∷
   rw⁻ 2 (q60 c4) ∷
   re 2 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw 1 (q3 c4) ∷
   re 2 5 (Toff014 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   rw 4 (q3 c4) ∷
   re 0 3 (CK42 ∷ []) ∷ []) Eq.refl

private
  q75 : WsL → Eqn
  q75 c4 = wlE 22 c4
  q76 : WsL → Eqn
  q76 c4 = wlE 21 c4
  q77 : WsL → Eqn
  q77 c4 = eqn (CCZ012 ∷ CX34 ∷ []) (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁))
  q78 : WsL → Eqn
  q78 c4 = wlE 20 c4
  q79 : WsL → Eqn
  q79 c4 = wlE 19 c4

-- comm CCZ024 CX13: 11 steps
lem-comm-CCZ024-CX13 : WsL → ⟪ (CCZ024 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CCZ024 ∷ []) ⟫ʷ
lem-comm-CCZ024-CX13 c4 = derive (CCZ024 ∷ CX13 ∷ []) (CX13 ∷ CCZ024 ∷ [])
  (re 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw⁻ 6 (q75 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CX24 ∷ []) ∷
   rw⁻ 4 (q76 c4) ∷
   rw 3 (q77 c4) ∷
   rw⁻ 2 (q78 c4) ∷
   re 2 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw 1 (q3 c4) ∷
   rw⁻ 0 (q79 c4) ∷
   re 1 7 (CCZ024 ∷ []) ∷ []) Eq.refl

private
  q80 : WsL → Eqn
  q80 c4 = eqn (CX01 ∷ Toff324 ∷ []) (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI))

-- comm TOFF213 CX04: 13 steps
lem-comm-TOFF213-CX04 : WsL → ⟪ (Toff213 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ Toff213 ∷ []) ⟫ʷ
lem-comm-TOFF213-CX04 c4 = derive (Toff213 ∷ CX04 ∷ []) (CX04 ∷ Toff213 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (Toff214 ∷ []) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (Toff314 ∷ []) ∷
   rw⁻ 2 (q34 c4) ∷
   rw⁻ 3 (q80 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   re 5 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   re 6 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   rw 8 (q3 c4) ∷
   re 0 7 (CX04 ∷ []) ∷ []) Eq.refl

-- comm CZ02 TOFF314: 23 steps
lem-comm-CZ02-TOFF314 : WsL → ⟪ (CZ02 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CZ02 ∷ []) ⟫ʷ
lem-comm-CZ02-TOFF314 c4 = derive (CZ02 ∷ Toff314 ∷ []) (Toff314 ∷ CZ02 ∷ [])
  (re 1 1 (Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CZ03 ∷ []) ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (CZ04 ∷ []) ∷
   re 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 10 (q3 c4) ∷
   re 8 3 (Toff214 ∷ []) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (Toff314 ∷ []) ∷
   rw 6 (q32 c4) ∷
   rw 5 (q56 c4) ∷
   rw 4 (q34 c4) ∷
   re 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 3 (q1 c4) ∷
   re 3 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   rw 2 (q3 c4) ∷
   re 3 7 (CZ04 ∷ []) ∷
   re 3 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   re 4 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 0 5 (Toff314 ∷ []) ∷ []) Eq.refl

-- comm CSd02 TOFF314: 23 steps
lem-comm-CSd02-TOFF314 : WsL → ⟪ (CS02⁻ ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-comm-CSd02-TOFF314 c4 = derive (CS02⁻ ∷ Toff314 ∷ []) (Toff314 ∷ CS02⁻ ∷ [])
  (re 1 1 (Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (CS04⁻ ∷ []) ∷
   re 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 10 (q3 c4) ∷
   re 8 3 (Toff214 ∷ []) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (Toff314 ∷ []) ∷
   rw 6 (q32 c4) ∷
   rw 5 (q57 c4) ∷
   rw 4 (q34 c4) ∷
   re 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 3 (q1 c4) ∷
   re 3 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   rw 2 (q3 c4) ∷
   re 3 7 (CS04⁻ ∷ []) ∷
   re 3 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   re 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 0 5 (Toff314 ∷ []) ∷ []) Eq.refl

-- comm CS02 TOFF314: 23 steps
lem-comm-CS02-TOFF314 : WsL → ⟪ (CS02 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS02 ∷ []) ⟫ʷ
lem-comm-CS02-TOFF314 c4 = derive (CS02 ∷ Toff314 ∷ []) (Toff314 ∷ CS02 ∷ [])
  (re 1 1 (Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CS03 ∷ []) ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (CS04 ∷ []) ∷
   re 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 10 (q3 c4) ∷
   re 8 3 (Toff214 ∷ []) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (Toff314 ∷ []) ∷
   rw 6 (q32 c4) ∷
   rw 5 (q33 c4) ∷
   rw 4 (q34 c4) ∷
   re 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 3 (q1 c4) ∷
   re 3 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   rw 2 (q3 c4) ∷
   re 3 7 (CS04 ∷ []) ∷
   re 3 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 0 5 (Toff314 ∷ []) ∷ []) Eq.refl

private
  q81 : WsL → Eqn
  q81 c4 = eqn (Sw01 ∷ Toff423 ∷ []) (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ))

-- resp TOFF413 at 2: 4 steps
lem-resp-TOFF413-at-2 : WsL → ⟪ (Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff423 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF413-at-2 c4 = derive (Toff413 ∷ []) (Sw12 ∷ Sw01 ∷ Toff423 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q28 c4) ∷
   rw⁻ 0 (q13 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw⁻ 1 (q81 c4) ∷ []) Eq.refl

private
  q82 : WsL → Eqn
  q82 c4 = eqn (CX01 ∷ Toff423 ∷ []) (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ))

-- comm CX04 TOFF312: 13 steps
lem-comm-CX04-TOFF312 : WsL → ⟪ (CX04 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CX04 ∷ []) ⟫ʷ
lem-comm-CX04-TOFF312 c4 = derive (CX04 ∷ Toff312 ∷ []) (Toff312 ∷ CX04 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (Toff412 ∷ []) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (Toff413 ∷ []) ∷
   rw 4 (q11 c4) ∷
   rw 3 (q82 c4) ∷
   rw 2 (q13 c4) ∷
   re 2 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 1 (q1 c4) ∷
   re 1 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   rw 0 (q3 c4) ∷
   re 1 7 (CX04 ∷ []) ∷ []) Eq.refl

-- comm CX30 CCZ124: 9 steps
lem-comm-CX30-CCZ124 : WsL → ⟪ (CX30 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CX30 ∷ []) ⟫ʷ
lem-comm-CX30-CCZ124 c4 = derive (CX30 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX30 ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CCZ134 ∷ []) ∷
   rw⁻ 3 (q8 c4) ∷
   rw 2 (q9 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   re 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 5 (CX30 ∷ []) ∷ []) Eq.refl

private
  q83 : WsL → Eqn
  q83 c4 = eqn (CX10 ∷ Toff324 ∷ []) (Toff324 ∷ CX10 ∷ []) (c₂ (CX₁₀) (K ↑ • CCZ • K ↑ • iI))

-- comm CX30 TOFF214: 9 steps
lem-comm-CX30-TOFF214 : WsL → ⟪ (CX30 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CX30 ∷ []) ⟫ʷ
lem-comm-CX30-TOFF214 c4 = derive (CX30 ∷ Toff214 ∷ []) (Toff214 ∷ CX30 ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (Toff314 ∷ []) ∷
   rw 3 (q32 c4) ∷
   rw 2 (q83 c4) ∷
   rw 1 (q34 c4) ∷
   re 1 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 5 (CX30 ∷ []) ∷ []) Eq.refl

private
  q84 : WsL → Eqn
  q84 c4 = wlE 32 c4
  q85 : WsL → Eqn
  q85 c4 = wlE 53 c4

-- comm CZ14 TOFF203: 7 steps
lem-comm-CZ14-TOFF203 : WsL → ⟪ (CZ14 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CZ14 ∷ []) ⟫ʷ
lem-comm-CZ14-TOFF203 c4 = derive (CZ14 ∷ Toff203 ∷ []) (Toff203 ∷ CZ14 ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q84 c4) ∷
   rw 1 (q16 c4) ∷
   rw⁻ 2 (q17 c4) ∷
   rw 3 (q18 c4) ∷
   rw 4 (q85 c4) ∷
   re 0 5 (Toff203 ∷ []) ∷ []) Eq.refl

-- comm CS12 TOFF304: 15 steps
lem-comm-CS12-TOFF304 : WsL → ⟪ (CS12 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CS12 ∷ []) ⟫ʷ
lem-comm-CS12-TOFF304 c4 = derive (CS12 ∷ Toff304 ∷ []) (Toff304 ∷ CS12 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 (q48 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 3 3 (CS24 ∷ []) ∷
   rw 3 (q21 c4) ∷
   rw⁻ 4 (q49 c4) ∷
   rw 5 (q23 c4) ∷
   re 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 8 (q3 c4) ∷
   rw 7 (q50 c4) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 (q1 c4) ∷
   re 0 9 (Toff304 ∷ []) ∷ []) Eq.refl

-- comm TOFF314 CSd02: 23 steps
lem-comm-TOFF314-CSd02 : WsL → ⟪ (Toff314 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Toff314 ∷ []) ⟫ʷ
lem-comm-TOFF314-CSd02 c4 = derive (Toff314 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff314 ∷ [])
  (re 0 1 (Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS03⁻ ∷ []) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (CS04⁻ ∷ []) ∷
   re 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q3 c4) ∷
   re 3 3 (Toff214 ∷ []) ∷
   rw⁻ 3 (q1 c4) ∷
   re 4 3 (Toff314 ∷ []) ∷
   rw⁻ 4 (q34 c4) ∷
   rw⁻ 5 (q57 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   re 7 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 9 (q1 c4) ∷
   re 8 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   rw 10 (q3 c4) ∷
   re 2 7 (CS04⁻ ∷ []) ∷
   re 2 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw 1 (q3 c4) ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 5 (Toff314 ∷ []) ∷ []) Eq.refl

-- comm CSd14 TOFF302: 7 steps
lem-comm-CSd14-TOFF302 : WsL → ⟪ (CS14⁻ ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS14⁻ ∷ []) ⟫ʷ
lem-comm-CSd14-TOFF302 c4 = derive (CS14⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS14⁻ ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q35 c4) ∷
   rw 1 (q4 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q37 c4) ∷
   re 0 5 (Toff302 ∷ []) ∷ []) Eq.refl

private
  q86 : WsL → Eqn
  q86 c4 = wlE 80 c4
  q87 : WsL → Eqn
  q87 c4 = wlE 78 c4

-- resp CX30 at 2: 4 steps
lem-resp-CX30-at-2 : WsL → ⟪ (CX30 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX31 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX30-at-2 c4 = derive (CX30 ∷ []) (Sw12 ∷ Sw01 ∷ CX31 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q28 c4) ∷
   rw 0 (q86 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw 1 (q87 c4) ∷ []) Eq.refl

-- comm CSd02 CCZ134: 23 steps
lem-comm-CSd02-CCZ134 : WsL → ⟪ (CS02⁻ ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-comm-CSd02-CCZ134 c4 = derive (CS02⁻ ∷ CCZ134 ∷ []) (CCZ134 ∷ CS02⁻ ∷ [])
  (re 1 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (CS04⁻ ∷ []) ∷
   re 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 10 (q3 c4) ∷
   re 8 3 (CCZ124 ∷ []) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (CCZ134 ∷ []) ∷
   rw⁻ 6 (q8 c4) ∷
   rw 5 (q43 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   re 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 3 (q1 c4) ∷
   re 3 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 2 (q3 c4) ∷
   re 3 7 (CS04⁻ ∷ []) ∷
   re 3 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   re 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 0 5 (CCZ134 ∷ []) ∷ []) Eq.refl

-- comm CS02 CCZ134: 23 steps
lem-comm-CS02-CCZ134 : WsL → ⟪ (CS02 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CS02 ∷ []) ⟫ʷ
lem-comm-CS02-CCZ134 c4 = derive (CS02 ∷ CCZ134 ∷ []) (CCZ134 ∷ CS02 ∷ [])
  (re 1 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CS03 ∷ []) ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (CS04 ∷ []) ∷
   re 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 10 (q3 c4) ∷
   re 8 3 (CCZ124 ∷ []) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (CCZ134 ∷ []) ∷
   rw⁻ 6 (q8 c4) ∷
   rw 5 (q44 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   re 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 3 (q1 c4) ∷
   re 3 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 2 (q3 c4) ∷
   re 3 7 (CS04 ∷ []) ∷
   re 3 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 0 5 (CCZ134 ∷ []) ∷ []) Eq.refl

-- comm CZ14 TOFF302: 7 steps
lem-comm-CZ14-TOFF302 : WsL → ⟪ (CZ14 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CZ14 ∷ []) ⟫ʷ
lem-comm-CZ14-TOFF302 c4 = derive (CZ14 ∷ Toff302 ∷ []) (Toff302 ∷ CZ14 ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q84 c4) ∷
   rw 1 (q16 c4) ∷
   rw⁻ 2 (q26 c4) ∷
   rw 3 (q18 c4) ∷
   rw 4 (q85 c4) ∷
   re 0 5 (Toff302 ∷ []) ∷ []) Eq.refl

-- comm CS03 TOFF214: 9 steps
lem-comm-CS03-TOFF214 : WsL → ⟪ (CS03 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS03 ∷ []) ⟫ʷ
lem-comm-CS03-TOFF214 c4 = derive (CS03 ∷ Toff214 ∷ []) (Toff214 ∷ CS03 ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (Toff314 ∷ []) ∷
   rw 3 (q32 c4) ∷
   rw 2 (q33 c4) ∷
   rw 1 (q34 c4) ∷
   re 1 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 5 (CS03 ∷ []) ∷ []) Eq.refl

-- comm TOFF214 CS03: 9 steps
lem-comm-TOFF214-CS03 : WsL → ⟪ (Toff214 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff214 ∷ []) ⟫ʷ
lem-comm-TOFF214-CS03 c4 = derive (Toff214 ∷ CS03 ∷ []) (CS03 ∷ Toff214 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (Toff314 ∷ []) ∷
   rw⁻ 1 (q34 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   rw⁻ 3 (q32 c4) ∷
   re 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 0 5 (CS03 ∷ []) ∷ []) Eq.refl

-- comm CZ23 TOFF014: 9 steps
lem-comm-CZ23-TOFF014 : WsL → ⟪ (CZ23 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CZ23 ∷ []) ⟫ʷ
lem-comm-CZ23-TOFF014 c4 = derive (CZ23 ∷ Toff014 ∷ []) (Toff014 ∷ CZ23 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (CZ24 ∷ []) ∷
   rw 1 (q16 c4) ∷
   rw⁻ 2 (q66 c4) ∷
   rw 3 (q18 c4) ∷
   re 4 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) ∷
   rw 6 (q3 c4) ∷
   re 0 5 (Toff014 ∷ []) ∷ []) Eq.refl

-- comm CZ24 TOFF301: 5 steps
lem-comm-CZ24-TOFF301 : WsL → ⟪ (CZ24 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CZ24 ∷ []) ⟫ʷ
lem-comm-CZ24-TOFF301 c4 = derive (CZ24 ∷ Toff301 ∷ []) (Toff301 ∷ CZ24 ∷ [])
  (re 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   rw 0 (q16 c4) ∷
   rw⁻ 1 (q26 c4) ∷
   rw 2 (q18 c4) ∷
   re 0 3 (Toff301 ∷ []) ∷ []) Eq.refl

-- comm SWAP14 BOX(3;20): 7 steps
lem-comm-SWAP14-BOX⟨3·20⟩ : WsL → ⟪ (Sw14 ∷ Bx3-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-20 ∷ Sw14 ∷ []) ⟫ʷ
lem-comm-SWAP14-BOX⟨3·20⟩ c4 = derive (Sw14 ∷ Bx3-20 ∷ []) (Bx3-20 ∷ Sw14 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   re 1 1 (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) ∷
   rw⁻ 0 (q68 c4) ∷
   rw⁻ 1 (q69 c4) ∷
   rw⁻ 2 (q70 c4) ∷
   re 0 3 (CZ02 ∷ []) ∷
   re 0 1 (Bx3-20 ∷ []) ∷ []) Eq.refl

private
  q88 : WsL → Eqn
  q88 c4 = wlE 57 c4
  q89 : WsL → Eqn
  q89 c4 = eqn (Toff012 ∷ CX43 ∷ []) (CX43 ∷ Toff012 ∷ []) (c₃ (Toff) (CX₁₀))
  q90 : WsL → Eqn
  q90 c4 = wlE 60 c4

-- comm CX31 TOFF024: 11 steps
lem-comm-CX31-TOFF024 : WsL → ⟪ (CX31 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CX31 ∷ []) ⟫ʷ
lem-comm-CX31-TOFF024 c4 = derive (CX31 ∷ Toff024 ∷ []) (Toff024 ∷ CX31 ∷ [])
  (re 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw 0 (q88 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (CX42 ∷ []) ∷
   rw 2 (q52 c4) ∷
   rw⁻ 3 (q89 c4) ∷
   rw 4 (q54 c4) ∷
   re 5 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) ∷
   rw 7 (q3 c4) ∷
   rw 6 (q90 c4) ∷
   re 0 7 (Toff024 ∷ []) ∷ []) Eq.refl

-- comm CCZ134 CS02: 23 steps
lem-comm-CCZ134-CS02 : WsL → ⟪ (CCZ134 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ134 ∷ []) ⟫ʷ
lem-comm-CCZ134-CS02 c4 = derive (CCZ134 ∷ CS02 ∷ []) (CS02 ∷ CCZ134 ∷ [])
  (re 0 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS03 ∷ []) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (CS04 ∷ []) ∷
   re 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q3 c4) ∷
   re 3 3 (CCZ124 ∷ []) ∷
   rw⁻ 3 (q1 c4) ∷
   re 4 3 (CCZ134 ∷ []) ∷
   rw 4 (q10 c4) ∷
   rw⁻ 5 (q44 c4) ∷
   rw 6 (q8 c4) ∷
   re 7 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 9 (q1 c4) ∷
   re 8 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 10 (q3 c4) ∷
   re 2 7 (CS04 ∷ []) ∷
   re 2 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 1 (q3 c4) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 5 (CCZ134 ∷ []) ∷ []) Eq.refl

-- comm TOFF312 CX04: 13 steps
lem-comm-TOFF312-CX04 : WsL → ⟪ (Toff312 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ Toff312 ∷ []) ⟫ʷ
lem-comm-TOFF312-CX04 c4 = derive (Toff312 ∷ CX04 ∷ []) (CX04 ∷ Toff312 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (Toff412 ∷ []) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (Toff413 ∷ []) ∷
   rw⁻ 2 (q13 c4) ∷
   rw⁻ 3 (q82 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   re 5 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   re 6 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   rw 8 (q3 c4) ∷
   re 0 7 (CX04 ∷ []) ∷ []) Eq.refl

-- comm CZ13 TOFF204: 11 steps
lem-comm-CZ13-TOFF204 : WsL → ⟪ (CZ13 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CZ13 ∷ []) ⟫ʷ
lem-comm-CZ13-TOFF204 c4 = derive (CZ13 ∷ Toff204 ∷ []) (Toff204 ∷ CZ13 ∷ [])
  (re 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw 0 (q15 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (CZ24 ∷ []) ∷
   rw 2 (q16 c4) ∷
   rw⁻ 3 (q17 c4) ∷
   rw 4 (q18 c4) ∷
   re 5 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) ∷
   rw 7 (q3 c4) ∷
   rw 6 (q19 c4) ∷
   re 0 7 (Toff204 ∷ []) ∷ []) Eq.refl

private
  q91 : WsL → Eqn
  q91 c4 = wlE 10 c4
  q92 : WsL → Eqn
  q92 c4 = wlE 16 c4

-- resp CX03 at 2: 4 steps
lem-resp-CX03-at-2 : WsL → ⟪ (CX03 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX13 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX03-at-2 c4 = derive (CX03 ∷ []) (Sw12 ∷ Sw01 ∷ CX13 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q28 c4) ∷
   rw 0 (q91 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw 1 (q92 c4) ∷ []) Eq.refl

-- comm push SWAP04 sw2 L: 7 steps
lem-comm-push-SWAP04-sw2-L : WsL → ⟪ (Sw04 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw04 ∷ []) ⟫ʷ
lem-comm-push-SWAP04-sw2-L c4 = derive (Sw04 ∷ Sw23 ∷ []) (Sw23 ∷ Sw04 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q46 c4) ∷
   rw 4 (q41 c4) ∷
   rw 3 (q72 c4) ∷
   rw 2 (q41 c4) ∷
   rw⁻ 0 (q46 c4) ∷
   re 1 7 (Sw04 ∷ []) ∷ []) Eq.refl

-- comm SWAP14 BOX(2;30): 9 steps
lem-comm-SWAP14-BOX⟨2·30⟩ : WsL → ⟪ (Sw14 ∷ Bx2-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-30 ∷ Sw14 ∷ []) ⟫ʷ
lem-comm-SWAP14-BOX⟨2·30⟩ c4 = derive (Sw14 ∷ Bx2-30 ∷ []) (Bx2-30 ∷ Sw14 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 0 (q67 c4) ∷
   rw⁻ 1 (q68 c4) ∷
   rw⁻ 2 (q69 c4) ∷
   rw⁻ 3 (q70 c4) ∷
   rw 4 (q67 c4) ∷
   re 0 5 (CZ03 ∷ []) ∷
   re 0 1 (Bx2-30 ∷ []) ∷ []) Eq.refl

-- comm CX21 TOFF034: 15 steps
lem-comm-CX21-TOFF034 : WsL → ⟪ (CX21 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX21 ∷ []) ⟫ʷ
lem-comm-CX21-TOFF034 c4 = derive (CX21 ∷ Toff034 ∷ []) (Toff034 ∷ CX21 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CX31 ∷ []) ∷
   rw 1 (q88 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 3 3 (CX42 ∷ []) ∷
   rw 3 (q52 c4) ∷
   rw⁻ 4 (q89 c4) ∷
   rw 5 (q54 c4) ∷
   re 6 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) ∷
   rw 8 (q3 c4) ∷
   rw 7 (q90 c4) ∷
   re 8 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 10 (q1 c4) ∷
   re 0 9 (Toff034 ∷ []) ∷ []) Eq.refl

-- comm CCZ124 CS03: 9 steps
lem-comm-CCZ124-CS03 : WsL → ⟪ (CCZ124 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CCZ124 ∷ []) ⟫ʷ
lem-comm-CCZ124-CS03 c4 = derive (CCZ124 ∷ CS03 ∷ []) (CS03 ∷ CCZ124 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CCZ134 ∷ []) ∷
   rw 1 (q10 c4) ∷
   rw⁻ 2 (q44 c4) ∷
   rw 3 (q8 c4) ∷
   re 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 0 5 (CS03 ∷ []) ∷ []) Eq.refl

-- comm CCZ024 CX31: 11 steps
lem-comm-CCZ024-CX31 : WsL → ⟪ (CCZ024 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CCZ024 ∷ []) ⟫ʷ
lem-comm-CCZ024-CX31 c4 = derive (CCZ024 ∷ CX31 ∷ []) (CX31 ∷ CCZ024 ∷ [])
  (re 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw⁻ 6 (q90 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CX42 ∷ []) ∷
   rw⁻ 4 (q54 c4) ∷
   rw 3 (q53 c4) ∷
   rw⁻ 2 (q52 c4) ∷
   re 2 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) ∷
   rw 1 (q3 c4) ∷
   rw⁻ 0 (q88 c4) ∷
   re 1 7 (CCZ024 ∷ []) ∷ []) Eq.refl

private
  q93 : WsL → Eqn
  q93 c4 = eqn (Toff012 ∷ CX34 ∷ []) (CX34 ∷ Toff012 ∷ []) (c₃ (Toff) (CX₀₁))

-- comm TOFF034 CX12: 15 steps
lem-comm-TOFF034-CX12 : WsL → ⟪ (Toff034 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ Toff034 ∷ []) ⟫ʷ
lem-comm-TOFF034-CX12 c4 = derive (Toff034 ∷ CX12 ∷ []) (CX12 ∷ Toff034 ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (CX13 ∷ []) ∷
   rw⁻ 7 (q75 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (CX24 ∷ []) ∷
   rw⁻ 5 (q76 c4) ∷
   rw 4 (q93 c4) ∷
   rw⁻ 3 (q78 c4) ∷
   re 3 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 1 (q79 c4) ∷
   re 1 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 9 (Toff034 ∷ []) ∷ []) Eq.refl

-- comm CCZ014 CX23: 9 steps
lem-comm-CCZ014-CX23 : WsL → ⟪ (CCZ014 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ014 ∷ []) ⟫ʷ
lem-comm-CCZ014-CX23 c4 = derive (CCZ014 ∷ CX23 ∷ []) (CX23 ∷ CCZ014 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (CX24 ∷ []) ∷
   rw⁻ 3 (q76 c4) ∷
   rw 2 (q77 c4) ∷
   rw⁻ 1 (q78 c4) ∷
   re 1 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw 0 (q3 c4) ∷
   re 1 5 (CCZ014 ∷ []) ∷ []) Eq.refl

-- comm CX23 TOFF014: 9 steps
lem-comm-CX23-TOFF014 : WsL → ⟪ (CX23 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CX23 ∷ []) ⟫ʷ
lem-comm-CX23-TOFF014 c4 = derive (CX23 ∷ Toff014 ∷ []) (Toff014 ∷ CX23 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (CX24 ∷ []) ∷
   rw 1 (q78 c4) ∷
   rw⁻ 2 (q93 c4) ∷
   rw 3 (q76 c4) ∷
   re 4 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw 6 (q3 c4) ∷
   re 0 5 (Toff014 ∷ []) ∷ []) Eq.refl

-- comm CCZ034 CS12: 15 steps
lem-comm-CCZ034-CS12 : WsL → ⟪ (CCZ034 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ034 ∷ []) ⟫ʷ
lem-comm-CCZ034-CS12 c4 = derive (CCZ034 ∷ CS12 ∷ []) (CS12 ∷ CCZ034 ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 7 (q50 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (CS24 ∷ []) ∷
   rw⁻ 5 (q23 c4) ∷
   rw 4 (q39 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   re 3 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 1 (q48 c4) ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 9 (CCZ034 ∷ []) ∷ []) Eq.refl

-- comm TOFF013 CS24: 15 steps
lem-comm-TOFF013-CS24 : WsL → ⟪ (Toff013 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Toff013 ∷ []) ⟫ʷ
lem-comm-TOFF013-CS24 c4 = derive (Toff013 ∷ CS24 ∷ []) (CS24 ∷ Toff013 ∷ [])
  (re 1 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (Toff014 ∷ []) ∷
   re 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CS24 ∷ []) ∷
   rw⁻ 4 (q23 c4) ∷
   rw 3 (q65 c4) ∷
   rw⁻ 2 (q21 c4) ∷
   re 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 1 (q3 c4) ∷
   re 2 5 (Toff014 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   rw 4 (q3 c4) ∷
   re 0 3 (CS24 ∷ []) ∷ []) Eq.refl

-- comm TOFF014 CX23: 9 steps
lem-comm-TOFF014-CX23 : WsL → ⟪ (Toff014 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff014 ∷ []) ⟫ʷ
lem-comm-TOFF014-CX23 c4 = derive (Toff014 ∷ CX23 ∷ []) (CX23 ∷ Toff014 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (CX24 ∷ []) ∷
   rw⁻ 3 (q76 c4) ∷
   rw 2 (q93 c4) ∷
   rw⁻ 1 (q78 c4) ∷
   re 1 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw 0 (q3 c4) ∷
   re 1 5 (Toff014 ∷ []) ∷ []) Eq.refl

-- comm CCZ024 CS13: 11 steps
lem-comm-CCZ024-CS13 : WsL → ⟪ (CCZ024 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ024 ∷ []) ⟫ʷ
lem-comm-CCZ024-CS13 c4 = derive (CCZ024 ∷ CS13 ∷ []) (CS13 ∷ CCZ024 ∷ [])
  (re 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw⁻ 6 (q50 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CS24 ∷ []) ∷
   rw⁻ 4 (q23 c4) ∷
   rw 3 (q39 c4) ∷
   rw⁻ 2 (q21 c4) ∷
   re 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 1 (q3 c4) ∷
   rw⁻ 0 (q48 c4) ∷
   re 1 7 (CCZ024 ∷ []) ∷ []) Eq.refl

-- comm CCZ024 CSd13: 11 steps
lem-comm-CCZ024-CSd13 : WsL → ⟪ (CCZ024 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ024 ∷ []) ⟫ʷ
lem-comm-CCZ024-CSd13 c4 = derive (CCZ024 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ024 ∷ [])
  (re 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw⁻ 6 (q7 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CS24⁻ ∷ []) ∷
   rw⁻ 4 (q6 c4) ∷
   rw 3 (q36 c4) ∷
   rw⁻ 2 (q4 c4) ∷
   re 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 1 (q3 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 7 (CCZ024 ∷ []) ∷ []) Eq.refl

-- comm TOFF013 CX24: 15 steps
lem-comm-TOFF013-CX24 : WsL → ⟪ (Toff013 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ Toff013 ∷ []) ⟫ʷ
lem-comm-TOFF013-CX24 c4 = derive (Toff013 ∷ CX24 ∷ []) (CX24 ∷ Toff013 ∷ [])
  (re 1 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (Toff014 ∷ []) ∷
   re 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CX24 ∷ []) ∷
   rw⁻ 4 (q76 c4) ∷
   rw 3 (q93 c4) ∷
   rw⁻ 2 (q78 c4) ∷
   re 2 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw 1 (q3 c4) ∷
   re 2 5 (Toff014 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   rw 4 (q3 c4) ∷
   re 0 3 (CX24 ∷ []) ∷ []) Eq.refl

-- comm CCZ034 CX12: 15 steps
lem-comm-CCZ034-CX12 : WsL → ⟪ (CCZ034 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CCZ034 ∷ []) ⟫ʷ
lem-comm-CCZ034-CX12 c4 = derive (CCZ034 ∷ CX12 ∷ []) (CX12 ∷ CCZ034 ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (CX13 ∷ []) ∷
   rw⁻ 7 (q75 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (CX24 ∷ []) ∷
   rw⁻ 5 (q76 c4) ∷
   rw 4 (q77 c4) ∷
   rw⁻ 3 (q78 c4) ∷
   re 3 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 1 (q79 c4) ∷
   re 1 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 9 (CCZ034 ∷ []) ∷ []) Eq.refl

private
  q94 : WsL → Eqn
  q94 c4 = wlE 75 c4
  q95 : WsL → Eqn
  q95 c4 = eqn (CZ01 ∷ Sw23 ∷ []) (Sw23 ∷ CZ01 ∷ []) (c₂ (CZ) (Swap))
  q96 : WsL → Eqn
  q96 c4 = wlE 96 c4

-- comm SWAP12 BOX(3;04): 13 steps
lem-comm-SWAP12-BOX⟨3·04⟩ : WsL → ⟪ (Sw12 ∷ Bx3-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-04 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-SWAP12-BOX⟨3·04⟩ c4 = derive (Sw12 ∷ Bx3-04 ∷ []) (Bx3-04 ∷ Sw12 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   re 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 0 (q41 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (Sw13 ∷ []) ∷
   rw⁻ 2 (q94 c4) ∷
   rw⁻ 3 (q95 c4) ∷
   rw⁻ 4 (q96 c4) ∷
   re 5 1 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw 6 (q41 c4) ∷
   re 0 7 (CZ04 ∷ []) ∷
   re 0 1 (Bx3-04 ∷ []) ∷ []) Eq.refl

-- comm TOFF213 CS04: 13 steps
lem-comm-TOFF213-CS04 : WsL → ⟪ (Toff213 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Toff213 ∷ []) ⟫ʷ
lem-comm-TOFF213-CS04 c4 = derive (Toff213 ∷ CS04 ∷ []) (CS04 ∷ Toff213 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (Toff214 ∷ []) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (Toff314 ∷ []) ∷
   rw⁻ 2 (q34 c4) ∷
   rw⁻ 3 (q33 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   re 5 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   re 6 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   rw 8 (q3 c4) ∷
   re 0 7 (CS04 ∷ []) ∷ []) Eq.refl

-- comm CS14 TOFF203: 7 steps
lem-comm-CS14-TOFF203 : WsL → ⟪ (CS14 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CS14 ∷ []) ⟫ʷ
lem-comm-CS14-TOFF203 c4 = derive (CS14 ∷ Toff203 ∷ []) (Toff203 ∷ CS14 ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q38 c4) ∷
   rw 1 (q21 c4) ∷
   rw⁻ 2 (q49 c4) ∷
   rw 3 (q23 c4) ∷
   rw 4 (q40 c4) ∷
   re 0 5 (Toff203 ∷ []) ∷ []) Eq.refl

-- comm CCZ124 CX03: 9 steps
lem-comm-CCZ124-CX03 : WsL → ⟪ (CCZ124 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ CCZ124 ∷ []) ⟫ʷ
lem-comm-CCZ124-CX03 c4 = derive (CCZ124 ∷ CX03 ∷ []) (CX03 ∷ CCZ124 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CCZ134 ∷ []) ∷
   rw 1 (q10 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw 3 (q8 c4) ∷
   re 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 0 5 (CX03 ∷ []) ∷ []) Eq.refl

-- comm CCZ034 CX21: 15 steps
lem-comm-CCZ034-CX21 : WsL → ⟪ (CCZ034 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CCZ034 ∷ []) ⟫ʷ
lem-comm-CCZ034-CX21 c4 = derive (CCZ034 ∷ CX21 ∷ []) (CX21 ∷ CCZ034 ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (CX31 ∷ []) ∷
   rw⁻ 7 (q90 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (CX42 ∷ []) ∷
   rw⁻ 5 (q54 c4) ∷
   rw 4 (q53 c4) ∷
   rw⁻ 3 (q52 c4) ∷
   re 3 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 1 (q88 c4) ∷
   re 1 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 9 (CCZ034 ∷ []) ∷ []) Eq.refl

-- comm SWAP12 BOX(3;40): 13 steps
lem-comm-SWAP12-BOX⟨3·40⟩ : WsL → ⟪ (Sw12 ∷ Bx3-40 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-40 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-SWAP12-BOX⟨3·40⟩ c4 = derive (Sw12 ∷ Bx3-40 ∷ []) (Bx3-40 ∷ Sw12 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   re 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 0 (q41 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (Sw13 ∷ []) ∷
   rw⁻ 2 (q94 c4) ∷
   rw⁻ 3 (q95 c4) ∷
   rw⁻ 4 (q96 c4) ∷
   re 5 1 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw 6 (q41 c4) ∷
   re 0 7 (CZ04 ∷ []) ∷
   re 0 1 (Bx3-40 ∷ []) ∷ []) Eq.refl

private
  q97 : WsL → Eqn
  q97 c4 = wlE 50 c4
  q98 : WsL → Eqn
  q98 c4 = eqn (Toff201 ∷ CX34 ∷ []) (CX34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CX₀₁))
  q99 : WsL → Eqn
  q99 c4 = wlE 51 c4

-- comm CX14 TOFF302: 7 steps
lem-comm-CX14-TOFF302 : WsL → ⟪ (CX14 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CX14 ∷ []) ⟫ʷ
lem-comm-CX14-TOFF302 c4 = derive (CX14 ∷ Toff302 ∷ []) (Toff302 ∷ CX14 ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q97 c4) ∷
   rw 1 (q78 c4) ∷
   rw⁻ 2 (q98 c4) ∷
   rw 3 (q76 c4) ∷
   rw 4 (q99 c4) ∷
   re 0 5 (Toff302 ∷ []) ∷ []) Eq.refl

-- comm TOFF024 CS13: 11 steps
lem-comm-TOFF024-CS13 : WsL → ⟪ (Toff024 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff024 ∷ []) ⟫ʷ
lem-comm-TOFF024-CS13 c4 = derive (Toff024 ∷ CS13 ∷ []) (CS13 ∷ Toff024 ∷ [])
  (re 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw⁻ 6 (q50 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CS24 ∷ []) ∷
   rw⁻ 4 (q23 c4) ∷
   rw 3 (q65 c4) ∷
   rw⁻ 2 (q21 c4) ∷
   re 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 1 (q3 c4) ∷
   rw⁻ 0 (q48 c4) ∷
   re 1 7 (Toff024 ∷ []) ∷ []) Eq.refl

private
  q100 : WsL → Eqn
  q100 c4 = wlE 97 c4
  q101 : WsL → Eqn
  q101 c4 = wlE 98 c4

-- resp SWAP03 at 2: 4 steps
lem-resp-SWAP03-at-2 : WsL → ⟪ (Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Sw13 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-SWAP03-at-2 c4 = derive (Sw03 ∷ []) (Sw12 ∷ Sw01 ∷ Sw13 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q28 c4) ∷
   rw 0 (q100 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw⁻ 1 (q101 c4) ∷ []) Eq.refl

-- resp SWAP03 at 1: 2 steps
lem-resp-SWAP03-at-1 : WsL → ⟪ (Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sw13 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-SWAP03-at-1 c4 = derive (Sw03 ∷ []) (Sw01 ∷ Sw13 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q30 c4) ∷
   rw⁻ 0 (q101 c4) ∷ []) Eq.refl

-- comm CCZ134 CX02: 23 steps
lem-comm-CCZ134-CX02 : WsL → ⟪ (CCZ134 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ CCZ134 ∷ []) ⟫ʷ
lem-comm-CCZ134-CX02 c4 = derive (CCZ134 ∷ CX02 ∷ []) (CX02 ∷ CCZ134 ∷ [])
  (re 0 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (CX04 ∷ []) ∷
   re 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q3 c4) ∷
   re 3 3 (CCZ124 ∷ []) ∷
   rw⁻ 3 (q1 c4) ∷
   re 4 3 (CCZ134 ∷ []) ∷
   rw 4 (q10 c4) ∷
   rw⁻ 5 (q59 c4) ∷
   rw 6 (q8 c4) ∷
   re 7 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 9 (q1 c4) ∷
   re 8 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 10 (q3 c4) ∷
   re 2 7 (CX04 ∷ []) ∷
   re 2 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 1 (q3 c4) ∷
   re 1 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 5 (CCZ134 ∷ []) ∷ []) Eq.refl

private
  q102 : WsL → Eqn
  q102 c4 = eqn (Toff102 ∷ CX34 ∷ []) (CX34 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (CX₀₁))

-- comm TOFF304 CX12: 15 steps
lem-comm-TOFF304-CX12 : WsL → ⟪ (Toff304 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ Toff304 ∷ []) ⟫ʷ
lem-comm-TOFF304-CX12 c4 = derive (Toff304 ∷ CX12 ∷ []) (CX12 ∷ Toff304 ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (CX13 ∷ []) ∷
   rw⁻ 7 (q75 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (CX24 ∷ []) ∷
   rw⁻ 5 (q76 c4) ∷
   rw 4 (q102 c4) ∷
   rw⁻ 3 (q78 c4) ∷
   re 3 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 1 (q79 c4) ∷
   re 1 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 9 (Toff304 ∷ []) ∷ []) Eq.refl

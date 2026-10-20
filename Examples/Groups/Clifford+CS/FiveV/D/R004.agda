{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.R004 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (WsL ; wl ; wp)
open import Examples.Groups.Clifford+CS.FiveV.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.FiveV.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 c4)
  q2 : WsL → Eqn
  q2 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl 4 c4)
  q3 : WsL → Eqn
  q3 c4 = eqn (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) (wl 84 c4)
  q4 : WsL → Eqn
  q4 c4 = eqn (CX10 ∷ Toff423 ∷ []) (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ))
  q5 : WsL → Eqn
  q5 c4 = eqn (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) (wl 85 c4)

-- comm CX20 TOFF413: 23 steps
lem-comm-CX20-TOFF413 : WsL → ⟪ (CX20 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CX20 ∷ []) ⟫ʷ
lem-comm-CX20-TOFF413 c4 = derive (CX20 ∷ Toff413 ∷ []) (Toff413 ∷ CX20 ∷ [])
  (re 1 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CX30 ∷ []) ∷
   rw⁻ 1 (q2 c4) ∷
   re 2 3 (CX40 ∷ []) ∷
   re 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 10 (q2 c4) ∷
   re 8 3 (Toff412 ∷ []) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (Toff413 ∷ []) ∷
   rw 6 (q3 c4) ∷
   rw 5 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   re 4 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 3 (q1 c4) ∷
   re 3 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   rw 2 (q2 c4) ∷
   re 3 7 (CX40 ∷ []) ∷
   re 3 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) ∷
   rw 5 (q2 c4) ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 0 5 (Toff413 ∷ []) ∷ []) Eq.refl

-- comm TOFF413 CX20: 23 steps
lem-comm-TOFF413-CX20 : WsL → ⟪ (Toff413 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ Toff413 ∷ []) ⟫ʷ
lem-comm-TOFF413-CX20 c4 = derive (Toff413 ∷ CX20 ∷ []) (CX20 ∷ Toff413 ∷ [])
  (re 0 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CX30 ∷ []) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (CX40 ∷ []) ∷
   re 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q2 c4) ∷
   re 3 3 (Toff412 ∷ []) ∷
   rw⁻ 3 (q1 c4) ∷
   re 4 3 (Toff413 ∷ []) ∷
   rw⁻ 4 (q5 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 7 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 9 (q1 c4) ∷
   re 8 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   rw 10 (q2 c4) ∷
   re 2 7 (CX40 ∷ []) ∷
   re 2 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) ∷
   rw 1 (q2 c4) ∷
   re 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 5 (Toff413 ∷ []) ∷ []) Eq.refl

private
  q6 : WsL → Eqn
  q6 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl 44 c4)
  q7 : WsL → Eqn
  q7 c4 = eqn (CK01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ))
  q8 : WsL → Eqn
  q8 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl 37 c4)

-- comm CK03 CCZ124: 9 steps
lem-comm-CK03-CCZ124 : WsL → ⟪ (CK03 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CK03 ∷ []) ⟫ʷ
lem-comm-CK03-CCZ124 c4 = derive (CK03 ∷ CCZ124 ∷ []) (CCZ124 ∷ CK03 ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CCZ134 ∷ []) ∷
   rw⁻ 3 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw⁻ 1 (q8 c4) ∷
   re 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 5 (CK03 ∷ []) ∷ []) Eq.refl

private
  q9 : WsL → Eqn
  q9 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl 18 c4)
  q10 : WsL → Eqn
  q10 c4 = eqn (CK03 ∷ Sw01 ∷ []) (Sw01 ∷ CK13 ∷ []) (wl 152 c4)

-- resp CK03 at 1: 2 steps
lem-resp-CK03-at-1 : WsL → ⟪ (CK03 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK13 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CK03-at-1 c4 = derive (CK03 ∷ []) (Sw01 ∷ CK13 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q9 c4) ∷
   rw 0 (q10 c4) ∷ []) Eq.refl

private
  q11 : WsL → Eqn
  q11 c4 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wl 29 c4)
  q12 : WsL → Eqn
  q12 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl 9 c4)
  q13 : WsL → Eqn
  q13 c4 = eqn (Toff201 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS • CS • CS))
  q14 : WsL → Eqn
  q14 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl 12 c4)
  q15 : WsL → Eqn
  q15 c4 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wl 28 c4)

-- comm TOFF403 CSd12: 15 steps
lem-comm-TOFF403-CSd12 : WsL → ⟪ (Toff403 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Toff403 ∷ []) ⟫ʷ
lem-comm-TOFF403-CSd12 c4 = derive (Toff403 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff403 ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q11 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (CS24⁻ ∷ []) ∷
   rw⁻ 5 (q12 c4) ∷
   rw 4 (q13 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   re 3 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 2 (q2 c4) ∷
   rw⁻ 1 (q15 c4) ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 9 (Toff403 ∷ []) ∷ []) Eq.refl

-- comm CCZ124 CK03: 9 steps
lem-comm-CCZ124-CK03 : WsL → ⟪ (CCZ124 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ CCZ124 ∷ []) ⟫ʷ
lem-comm-CCZ124-CK03 c4 = derive (CCZ124 ∷ CK03 ∷ []) (CK03 ∷ CCZ124 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CCZ134 ∷ []) ∷
   rw 1 (q8 c4) ∷
   rw⁻ 2 (q7 c4) ∷
   rw 3 (q6 c4) ∷
   re 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 0 5 (CK03 ∷ []) ∷ []) Eq.refl

private
  q16 : WsL → Eqn
  q16 c4 = eqn (CS01 ∷ Toff423 ∷ []) (Toff423 ∷ CS01 ∷ []) (c₂ (CS) (Toffᵗ))

-- comm CS02 TOFF413: 23 steps
lem-comm-CS02-TOFF413 : WsL → ⟪ (CS02 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CS02 ∷ []) ⟫ʷ
lem-comm-CS02-TOFF413 c4 = derive (CS02 ∷ Toff413 ∷ []) (Toff413 ∷ CS02 ∷ [])
  (re 1 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CS03 ∷ []) ∷
   rw⁻ 1 (q2 c4) ∷
   re 2 3 (CS04 ∷ []) ∷
   re 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 10 (q2 c4) ∷
   re 8 3 (Toff412 ∷ []) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (Toff413 ∷ []) ∷
   rw 6 (q3 c4) ∷
   rw 5 (q16 c4) ∷
   rw 4 (q5 c4) ∷
   re 4 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 3 (q1 c4) ∷
   re 3 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   rw 2 (q2 c4) ∷
   re 3 7 (CS04 ∷ []) ∷
   re 3 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q2 c4) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 0 5 (Toff413 ∷ []) ∷ []) Eq.refl

private
  q17 : WsL → Eqn
  q17 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl 46 c4)
  q18 : WsL → Eqn
  q18 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl 11 c4)
  q19 : WsL → Eqn
  q19 c4 = eqn (Toff201 ∷ CS34 ∷ []) (CS34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS))
  q20 : WsL → Eqn
  q20 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl 8 c4)
  q21 : WsL → Eqn
  q21 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl 47 c4)

-- comm CS12 TOFF403: 15 steps
lem-comm-CS12-TOFF403 : WsL → ⟪ (CS12 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CS12 ∷ []) ⟫ʷ
lem-comm-CS12-TOFF403 c4 = derive (CS12 ∷ Toff403 ∷ []) (Toff403 ∷ CS12 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 (q17 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   re 3 3 (CS24 ∷ []) ∷
   rw 3 (q18 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw 5 (q20 c4) ∷
   re 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 8 (q2 c4) ∷
   rw 7 (q21 c4) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 (q1 c4) ∷
   re 0 9 (Toff403 ∷ []) ∷ []) Eq.refl

private
  q22 : WsL → Eqn
  q22 c4 = eqn (CX41 ∷ Sw12 ∷ []) (Sw12 ∷ CX42 ∷ []) (wl 69 c4)
  q23 : WsL → Eqn
  q23 c4 = eqn (CX42 ∷ Sw23 ∷ []) (Sw23 ∷ CX43 ∷ []) (wl 58 c4)
  q24 : WsL → Eqn
  q24 c4 = eqn (Toff102 ∷ CX43 ∷ []) (CX43 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (CX₁₀))
  q25 : WsL → Eqn
  q25 c4 = eqn (CX43 ∷ Sw23 ∷ []) (Sw23 ∷ CX42 ∷ []) (wl 59 c4)
  q26 : WsL → Eqn
  q26 c4 = eqn (CX42 ∷ Sw12 ∷ []) (Sw12 ∷ CX41 ∷ []) (wl 89 c4)

-- comm CX41 TOFF203: 7 steps
lem-comm-CX41-TOFF203 : WsL → ⟪ (CX41 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CX41 ∷ []) ⟫ʷ
lem-comm-CX41-TOFF203 c4 = derive (CX41 ∷ Toff203 ∷ []) (Toff203 ∷ CX41 ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q22 c4) ∷
   rw 1 (q23 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 3 (q25 c4) ∷
   rw 4 (q26 c4) ∷
   re 0 5 (Toff203 ∷ []) ∷ []) Eq.refl

private
  q27 : WsL → Eqn
  q27 c4 = eqn (CZ01 ∷ Toff423 ∷ []) (Toff423 ∷ CZ01 ∷ []) (c₂ (CZ) (Toffᵗ))

-- comm CZ02 TOFF413: 23 steps
lem-comm-CZ02-TOFF413 : WsL → ⟪ (CZ02 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CZ02 ∷ []) ⟫ʷ
lem-comm-CZ02-TOFF413 c4 = derive (CZ02 ∷ Toff413 ∷ []) (Toff413 ∷ CZ02 ∷ [])
  (re 1 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CZ03 ∷ []) ∷
   rw⁻ 1 (q2 c4) ∷
   re 2 3 (CZ04 ∷ []) ∷
   re 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 10 (q2 c4) ∷
   re 8 3 (Toff412 ∷ []) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (Toff413 ∷ []) ∷
   rw 6 (q3 c4) ∷
   rw 5 (q27 c4) ∷
   rw 4 (q5 c4) ∷
   re 4 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 3 (q1 c4) ∷
   re 3 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   rw 2 (q2 c4) ∷
   re 3 7 (CZ04 ∷ []) ∷
   re 3 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) ∷
   rw 5 (q2 c4) ∷
   re 4 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 0 5 (Toff413 ∷ []) ∷ []) Eq.refl

-- comm TOFF413 CS02: 23 steps
lem-comm-TOFF413-CS02 : WsL → ⟪ (Toff413 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff413 ∷ []) ⟫ʷ
lem-comm-TOFF413-CS02 c4 = derive (Toff413 ∷ CS02 ∷ []) (CS02 ∷ Toff413 ∷ [])
  (re 0 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS03 ∷ []) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (CS04 ∷ []) ∷
   re 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q2 c4) ∷
   re 3 3 (Toff412 ∷ []) ∷
   rw⁻ 3 (q1 c4) ∷
   re 4 3 (Toff413 ∷ []) ∷
   rw⁻ 4 (q5 c4) ∷
   rw⁻ 5 (q16 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 7 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 9 (q1 c4) ∷
   re 8 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   rw 10 (q2 c4) ∷
   re 2 7 (CS04 ∷ []) ∷
   re 2 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 1 (q2 c4) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 5 (Toff413 ∷ []) ∷ []) Eq.refl

private
  q28 : WsL → Eqn
  q28 c4 = eqn (CK02 ∷ Sw01 ∷ []) (Sw01 ∷ CK12 ∷ []) (wl 153 c4)

-- resp CK02 at 1: 2 steps
lem-resp-CK02-at-1 : WsL → ⟪ (CK02 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK12 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CK02-at-1 c4 = derive (CK02 ∷ []) (Sw01 ∷ CK12 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q9 c4) ∷
   rw 0 (q28 c4) ∷ []) Eq.refl

private
  q29 : WsL → Eqn
  q29 c4 = eqn (Sw12 ∷ Sw23 ∷ []) (Sw13 ∷ Sw12 ∷ []) (wl 75 c4)
  q30 : WsL → Eqn
  q30 c4 = eqn (CZ01 ∷ Sw23 ∷ []) (Sw23 ∷ CZ01 ∷ []) (c₂ (CZ) (Swap))
  q31 : WsL → Eqn
  q31 c4 = eqn (Sw12 ∷ Sw13 ∷ []) (Sw23 ∷ Sw12 ∷ []) (wl 96 c4)

-- comm SWAP13 BOX(4;20): 7 steps
lem-comm-SWAP13-BOX⟨4·20⟩ : WsL → ⟪ (Sw13 ∷ Bx4-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-20 ∷ Sw13 ∷ []) ⟫ʷ
lem-comm-SWAP13-BOX⟨4·20⟩ c4 = derive (Sw13 ∷ Bx4-20 ∷ []) (Bx4-20 ∷ Sw13 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   re 1 1 (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) ∷
   rw⁻ 0 (q29 c4) ∷
   rw⁻ 1 (q30 c4) ∷
   rw⁻ 2 (q31 c4) ∷
   re 0 3 (CZ02 ∷ []) ∷
   re 0 1 (Bx4-20 ∷ []) ∷ []) Eq.refl

private
  q32 : WsL → Eqn
  q32 c4 = eqn (Toff201 ∷ CX43 ∷ []) (CX43 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CX₁₀))

-- comm CX41 TOFF302: 7 steps
lem-comm-CX41-TOFF302 : WsL → ⟪ (CX41 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CX41 ∷ []) ⟫ʷ
lem-comm-CX41-TOFF302 c4 = derive (CX41 ∷ Toff302 ∷ []) (Toff302 ∷ CX41 ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q22 c4) ∷
   rw 1 (q23 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 3 (q25 c4) ∷
   rw 4 (q26 c4) ∷
   re 0 5 (Toff302 ∷ []) ∷ []) Eq.refl

private
  q33 : WsL → Eqn
  q33 c4 = eqn (CX23 ∷ Sw12 ∷ []) (Sw12 ∷ CX13 ∷ []) (wl 22 c4)
  q34 : WsL → Eqn
  q34 c4 = eqn (CX34 ∷ Sw23 ∷ []) (Sw23 ∷ CX24 ∷ []) (wl 21 c4)
  q35 : WsL → Eqn
  q35 c4 = eqn (Toff201 ∷ CX34 ∷ []) (CX34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CX₀₁))
  q36 : WsL → Eqn
  q36 c4 = eqn (CX24 ∷ Sw23 ∷ []) (Sw23 ∷ CX34 ∷ []) (wl 20 c4)
  q37 : WsL → Eqn
  q37 c4 = eqn (CX13 ∷ Sw12 ∷ []) (Sw12 ∷ CX23 ∷ []) (wl 19 c4)

-- comm TOFF403 CX12: 15 steps
lem-comm-TOFF403-CX12 : WsL → ⟪ (Toff403 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ Toff403 ∷ []) ⟫ʷ
lem-comm-TOFF403-CX12 c4 = derive (Toff403 ∷ CX12 ∷ []) (CX12 ∷ Toff403 ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (CX13 ∷ []) ∷
   rw⁻ 7 (q33 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (CX24 ∷ []) ∷
   rw⁻ 5 (q34 c4) ∷
   rw 4 (q35 c4) ∷
   rw⁻ 3 (q36 c4) ∷
   re 3 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw 2 (q2 c4) ∷
   rw⁻ 1 (q37 c4) ∷
   re 1 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 9 (Toff403 ∷ []) ∷ []) Eq.refl

private
  q38 : WsL → Eqn
  q38 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl 6 c4)
  q39 : WsL → Eqn
  q39 c4 = eqn (CK03 ∷ Sw12 ∷ []) (Sw12 ∷ CK03 ∷ []) (wl 154 c4)

-- resp CK03 at 2: 4 steps
lem-resp-CK03-at-2 : WsL → ⟪ (CK03 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CK13 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CK03-at-2 c4 = derive (CK03 ∷ []) (Sw12 ∷ Sw01 ∷ CK13 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q38 c4) ∷
   rw 0 (q39 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw 1 (q10 c4) ∷ []) Eq.refl

private
  q40 : WsL → Eqn
  q40 c4 = eqn (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) (wl 57 c4)
  q41 : WsL → Eqn
  q41 c4 = eqn (CX32 ∷ Sw12 ∷ []) (Sw12 ∷ CX31 ∷ []) (wl 60 c4)

-- comm CX21 TOFF403: 15 steps
lem-comm-CX21-TOFF403 : WsL → ⟪ (CX21 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CX21 ∷ []) ⟫ʷ
lem-comm-CX21-TOFF403 c4 = derive (CX21 ∷ Toff403 ∷ []) (Toff403 ∷ CX21 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CX31 ∷ []) ∷
   rw 1 (q40 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   re 3 3 (CX42 ∷ []) ∷
   rw 3 (q23 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 5 (q25 c4) ∷
   re 6 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) ∷
   rw 8 (q2 c4) ∷
   rw 7 (q41 c4) ∷
   re 8 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 10 (q1 c4) ∷
   re 0 9 (Toff403 ∷ []) ∷ []) Eq.refl

-- comm CX12 TOFF403: 15 steps
lem-comm-CX12-TOFF403 : WsL → ⟪ (CX12 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CX12 ∷ []) ⟫ʷ
lem-comm-CX12-TOFF403 c4 = derive (CX12 ∷ Toff403 ∷ []) (Toff403 ∷ CX12 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CX13 ∷ []) ∷
   rw 1 (q37 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   re 3 3 (CX24 ∷ []) ∷
   rw 3 (q36 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   rw 5 (q34 c4) ∷
   re 6 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw 8 (q2 c4) ∷
   rw 7 (q33 c4) ∷
   re 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 10 (q1 c4) ∷
   re 0 9 (Toff403 ∷ []) ∷ []) Eq.refl

-- comm SWAP12 BOX(4;30): 11 steps
lem-comm-SWAP12-BOX⟨4·30⟩ : WsL → ⟪ (Sw12 ∷ Bx4-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-30 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-SWAP12-BOX⟨4·30⟩ c4 = derive (Sw12 ∷ Bx4-30 ∷ []) (Bx4-30 ∷ Sw12 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (Sw13 ∷ []) ∷
   rw⁻ 1 (q29 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw⁻ 3 (q31 c4) ∷
   re 4 1 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 0 5 (CZ03 ∷ []) ∷
   re 0 1 (Bx4-30 ∷ []) ∷ []) Eq.refl

-- comm CX31 TOFF402: 11 steps
lem-comm-CX31-TOFF402 : WsL → ⟪ (CX31 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CX31 ∷ []) ⟫ʷ
lem-comm-CX31-TOFF402 c4 = derive (CX31 ∷ Toff402 ∷ []) (Toff402 ∷ CX31 ∷ [])
  (re 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw 0 (q40 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   re 2 3 (CX42 ∷ []) ∷
   rw 2 (q23 c4) ∷
   rw⁻ 3 (q32 c4) ∷
   rw 4 (q25 c4) ∷
   re 5 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) ∷
   rw 7 (q2 c4) ∷
   rw 6 (q41 c4) ∷
   re 0 7 (Toff402 ∷ []) ∷ []) Eq.refl

-- comm TOFF312 CX40: 13 steps
lem-comm-TOFF312-CX40 : WsL → ⟪ (Toff312 ∷ CX40 ∷ []) ⟫ʷ ≈ ⟪ (CX40 ∷ Toff312 ∷ []) ⟫ʷ
lem-comm-TOFF312-CX40 c4 = derive (Toff312 ∷ CX40 ∷ []) (CX40 ∷ Toff312 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (Toff412 ∷ []) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (Toff413 ∷ []) ∷
   rw⁻ 2 (q5 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 5 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   re 6 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   rw 8 (q2 c4) ∷
   re 0 7 (CX40 ∷ []) ∷ []) Eq.refl

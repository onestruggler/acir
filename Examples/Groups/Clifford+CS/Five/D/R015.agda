{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R015 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)

-- comm CX41 CCZ023: 7 steps
lem-comm-CX41-CCZ023 : Complete 4 → ⟪ (CX41 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CX41 ∷ []) ⟫ʷ
lem-comm-CX41-CCZ023 c4 = run b0
  where
  b0 : Chain (CX41 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX41 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CX42 ∷ []) (lw0 c4 (CX41 ∷ Sw12 ∷ []) (Sw12 ∷ CX42 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CX43 ∷ []) (lw0 c4 (CX42 ∷ Sw23 ∷ []) (Sw23 ∷ CX43 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 3 2 (Sw23 ∷ CX42 ∷ []) (lw0 c4 (CX43 ∷ Sw23 ∷ []) (Sw23 ∷ CX42 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ CX41 ∷ []) (lw0 c4 (CX42 ∷ Sw12 ∷ []) (Sw12 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ03 TOFF214: 9 steps
lem-comm-CZ03-TOFF214 : Complete 4 → ⟪ (CZ03 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CZ03 ∷ []) ⟫ʷ
lem-comm-CZ03-TOFF214 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ03 ∷ Toff214 ∷ []) (Toff214 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b1 : Chain (Toff214 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) (Toff214 ∷ CZ03 ∷ [])
  b1 = at 1 5 (CZ03 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF214 CSd03: 9 steps
lem-comm-TOFF214-CSd03 : Complete 4 → ⟪ (Toff214 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Toff214 ∷ []) ⟫ʷ
lem-comm-TOFF214-CSd03 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff214 ∷ CS03⁻ ∷ []) (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ Toff324 ∷ []) (lw0 c4 (Toff314 ∷ Sw12 ∷ []) (Sw12 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS01⁻ ∷ Toff324 ∷ []) (sym (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 3 2 (Sw12 ∷ Toff314 ∷ []) (lw0 c4 (Toff324 ∷ Sw12 ∷ []) (Sw12 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ []) (CS03⁻ ∷ Toff214 ∷ [])
  b1 = at 0 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd14 TOFF203: 7 steps
lem-comm-CSd14-TOFF203 : Complete 4 → ⟪ (CS14⁻ ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CS14⁻ ∷ []) ⟫ʷ
lem-comm-CSd14-TOFF203 c4 = run b0
  where
  b0 : Chain (CS14⁻ ∷ Toff203 ∷ []) (Toff203 ∷ CS14⁻ ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS24⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CS34⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff102 ∷ CS34⁻ ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CS • CS • CS))) ▸
       at 3 2 (Sw23 ∷ CS24⁻ ∷ []) (lw0 c4 (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ CS14⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 5 (Toff203 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ03 CCZ124: 9 steps
lem-comm-CZ03-CCZ124 : Complete 4 → ⟪ (CZ03 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CZ03 ∷ []) ⟫ʷ
lem-comm-CZ03-CCZ124 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ03 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ124 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) (CCZ124 ∷ CZ03 ∷ [])
  b1 = at 1 5 (CZ03 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX03 CCZ124: 9 steps
lem-comm-CX03-CCZ124 : Complete 4 → ⟪ (CX03 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CX03 ∷ []) ⟫ʷ
lem-comm-CX03-CCZ124 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX03 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ124 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) (CCZ124 ∷ CX03 ∷ [])
  b1 = at 1 5 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF203 CSd14: 181 steps
lem-comm-TOFF203-CSd14 : Complete 4 → ⟪ (Toff203 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Toff203 ∷ []) ⟫ʷ
lem-comm-TOFF203-CSd14 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (run b22))))))))))))))))))))))
  where
  b0 : Chain (Toff203 ∷ CS14⁻ ∷ []) (Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sw12 ∷ Toff103 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ []) (Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ [])
  b1 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b2 : Chain (Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ []) (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ [])
  b2 = at 0 2 (K2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ []) (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ [])
  b3 = at 6 2 (K2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 8 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑)) ▸
       at 6 2 (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap)) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸ done

  b4 : Chain (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ K1 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ [])
  b4 = at 3 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap)) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (K1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K2 ∷ []) (K1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (Sw34 ∷ Sw12 ∷ K1 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ [])
  b5 = at 3 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24⁻ ∷ []) (CS14⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b6 : Chain (Sw34 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ [])
  b6 = at 8 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K2 ∷ []) (K1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw34 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ [])
  b7 = at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸ done

  b8 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw34 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ [])
  b8 = at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b9 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ Toff104 ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ [])
  b9 = at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 4 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff104 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Sw34 ∷ Sw12 ∷ Toff104 ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b10 = at 1 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Toff304 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CS23⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b11 = at 8 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS34⁻ ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (CS • CS • CS)) ▸
       at 5 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (CS13⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b12 = at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 9 (Toff304 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b13 = at 6 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b14 : Chain (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b14 = at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 14 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b15 : Chain (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b15 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 12 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 10 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 12 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 13 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

  b16 : Chain (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b16 = at 4 2 (K2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b17 : Chain (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ Sw34 ∷ ι ∷ [])
  b17 = at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 10 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 9 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 12 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑)) ▸ done

  b18 : Chain (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ Sw34 ∷ ι ∷ []) (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ K2 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ [])
  b18 = at 10 2 (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap)) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b19 : Chain (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ K2 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ []) (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ [])
  b19 = at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K2 ∷ []) (K1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 (CS13⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b20 : Chain (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ []) (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw12 ∷ [])
  b20 = at 11 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K2 ∷ []) (K1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b21 : Chain (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw12 ∷ []) (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw12 ∷ [])
  b21 = at 8 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸ done

  b22 : Chain (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw12 ∷ []) (CS14⁻ ∷ Toff203 ∷ [])
  b22 = at 14 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 7 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸
       at 0 5 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd03 TOFF214: 9 steps
lem-comm-CSd03-TOFF214 : Complete 4 → ⟪ (CS03⁻ ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-comm-CSd03-TOFF214 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03⁻ ∷ Toff214 ∷ []) (Toff214 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b1 : Chain (Toff214 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (Toff214 ∷ CS03⁻ ∷ [])
  b1 = at 1 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK41 CCZ023: 7 steps
lem-comm-CK41-CCZ023 : Complete 4 → ⟪ (CK41 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CK41 ∷ []) ⟫ʷ
lem-comm-CK41-CCZ023 c4 = run b0
  where
  b0 : Chain (CK41 ∷ CCZ023 ∷ []) (CCZ023 ∷ CK41 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CK42 ∷ []) (lw0 c4 (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CK43 ∷ []) (lw0 c4 (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 3 2 (Sw23 ∷ CK42 ∷ []) (lw0 c4 (CK43 ∷ Sw23 ∷ []) (Sw23 ∷ CK42 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ CK41 ∷ []) (lw0 c4 (CK42 ∷ Sw12 ∷ []) (Sw12 ∷ CK41 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK41 TOFF023: 7 steps
lem-comm-CK41-TOFF023 : Complete 4 → ⟪ (CK41 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CK41 ∷ []) ⟫ʷ
lem-comm-CK41-TOFF023 c4 = run b0
  where
  b0 : Chain (CK41 ∷ Toff023 ∷ []) (Toff023 ∷ CK41 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CK42 ∷ []) (lw0 c4 (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CK43 ∷ []) (lw0 c4 (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ CK43 ∷ []) (sym (c₃ (Toff) (CK₁₀))) ▸
       at 3 2 (Sw23 ∷ CK42 ∷ []) (lw0 c4 (CK43 ∷ Sw23 ∷ []) (Sw23 ∷ CK42 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ CK41 ∷ []) (lw0 c4 (CK42 ∷ Sw12 ∷ []) (Sw12 ∷ CK41 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (Toff023 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS23 TOFF014: 9 steps
lem-comm-CS23-TOFF014 : Complete 4 → ⟪ (CS23 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CS23 ∷ []) ⟫ʷ
lem-comm-CS23-TOFF014 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS23 ∷ Toff014 ∷ []) (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ CS34 ∷ []) (lw0 c4 (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ CS34 ∷ []) (sym (c₃ (Toff) (CS))) ▸
       at 3 2 (Sw23 ∷ CS24 ∷ []) (lw0 c4 (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ []) (Toff014 ∷ CS23 ∷ [])
  b1 = at 0 5 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ13 TOFF024: 11 steps
lem-comm-CZ13-TOFF024 : Complete 4 → ⟪ (CZ13 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CZ13 ∷ []) ⟫ʷ
lem-comm-CZ13-TOFF024 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ13 ∷ Toff024 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CZ23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CZ23 ∷ []) (lw4 c4 (CZ13 ∷ Sw12 ∷ []) (Sw12 ∷ CZ23 ∷ []) tt tt Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CZ24 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CZ34 ∷ []) (lw0 c4 (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ CZ34 ∷ []) (sym (c₃ (Toff) (CZ))) ▸
       at 4 2 (Sw23 ∷ CZ24 ∷ []) (lw0 c4 (CZ34 ∷ Sw23 ∷ []) (Sw23 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CZ23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (Toff024 ∷ CZ13 ∷ [])
  b1 = at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (Sw12 ∷ CZ13 ∷ []) (lw4 c4 (CZ23 ∷ Sw12 ∷ []) (Sw12 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 0 7 (Toff024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK42 CCZ013: 5 steps
lem-comm-CK42-CCZ013 : Complete 4 → ⟪ (CK42 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CK42 ∷ []) ⟫ʷ
lem-comm-CK42-CCZ013 c4 = run b0
  where
  b0 : Chain (CK42 ∷ CCZ013 ∷ []) (CCZ013 ∷ CK42 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CK43 ∷ []) (lw0 c4 (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 2 2 (Sw23 ∷ CK42 ∷ []) (lw0 c4 (CK43 ∷ Sw23 ∷ []) (Sw23 ∷ CK42 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK42 TOFF013: 5 steps
lem-comm-CK42-TOFF013 : Complete 4 → ⟪ (CK42 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CK42 ∷ []) ⟫ʷ
lem-comm-CK42-TOFF013 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Toff013 ∷ []) (Toff013 ∷ CK42 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CK43 ∷ []) (lw0 c4 (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ CK43 ∷ []) (sym (c₃ (Toff) (CK₁₀))) ▸
       at 2 2 (Sw23 ∷ CK42 ∷ []) (lw0 c4 (CK43 ∷ Sw23 ∷ []) (Sw23 ∷ CK42 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm SWAP14 BOX(2;03): 9 steps
lem-comm-SWAP14-BOX⟨2·03⟩ : Complete 4 → ⟪ (Sw14 ∷ Bx2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-03 ∷ Sw14 ∷ []) ⟫ʷ
lem-comm-SWAP14-BOX⟨2·03⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx2-03 ∷ []) (CZ03 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Sw23 ∷ []) (Sw23 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw12 ∷ Sw24 ∷ []) (lw0 c4 (Sw14 ∷ Sw12 ∷ []) (Sw12 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CZ01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 3 2 (Sw12 ∷ Sw14 ∷ []) (lw0 c4 (Sw24 ∷ Sw12 ∷ []) (Sw12 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Sw23 ∷ []) (Sw23 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (CZ03 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CZ03 ∷ Sw14 ∷ []) (Bx2-03 ∷ Sw14 ∷ [])
  b1 = at 0 1 (Bx2-03 ∷ []) (refl) ▸ done


-- resp SWAP24 at 3: 6 steps
lem-resp-SWAP24-at-3 : Complete 4 → ⟪ (Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-SWAP24-at-3 c4 = run b0
  where
  b0 : Chain (Sw24 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw24 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸ done


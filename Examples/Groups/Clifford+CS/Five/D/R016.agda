{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R016 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)

-- comm SWAP24 BOX(0;13): 7 steps
lem-comm-SWAP24-BOX⟨0·13⟩ : Complete 4 → ⟪ (Sw24 ∷ Bx0-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-13 ∷ Sw24 ∷ []) ⟫ʷ
lem-comm-SWAP24-BOX⟨0·13⟩ c4 = run b0
  where
  b0 : Chain (Sw24 ∷ Bx0-13 ∷ []) (Bx0-13 ∷ Sw24 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw24 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CZ12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 2 2 (Sw23 ∷ Sw24 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx0-13 ∷ []) (refl) ▸ done


-- comm SWAP23 BOX(0;41): 11 steps
lem-comm-SWAP23-BOX⟨0·41⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-41 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-SWAP23-BOX⟨0·41⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx0-41 ∷ []) (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Sw24 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw24 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CZ12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 3 2 (Sw23 ∷ Sw24 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (Bx0-41 ∷ Sw23 ∷ [])
  b1 = at 6 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 5 (CZ14 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx0-41 ∷ []) (refl) ▸ done


-- comm TOFF213 CSd04: 13 steps
lem-comm-TOFF213-CSd04 : Complete 4 → ⟪ (Toff213 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Toff213 ∷ []) ⟫ʷ
lem-comm-TOFF213-CSd04 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff213 ∷ CS04⁻ ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Toff314 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Toff324 ∷ []) (lw0 c4 (Toff314 ∷ Sw12 ∷ []) (Sw12 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS01⁻ ∷ Toff324 ∷ []) (sym (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 4 2 (Sw12 ∷ Toff314 ∷ []) (lw0 c4 (Toff324 ∷ Sw12 ∷ []) (Sw12 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Toff314 ∷ Sw23 ∷ Sw34 ∷ []) (CS04⁻ ∷ Toff213 ∷ [])
  b1 = at 5 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF213 CK40: 13 steps
lem-comm-TOFF213-CK40 : Complete 4 → ⟪ (Toff213 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Toff213 ∷ []) ⟫ʷ
lem-comm-TOFF213-CK40 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff213 ∷ CK40 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Toff314 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Toff324 ∷ []) (lw0 c4 (Toff314 ∷ Sw12 ∷ []) (Sw12 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CK10 ∷ Toff324 ∷ []) (sym (c₂ (CK₁₀) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 4 2 (Sw12 ∷ Toff314 ∷ []) (lw0 c4 (Toff324 ∷ Sw12 ∷ []) (Sw12 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Toff314 ∷ Sw23 ∷ Sw34 ∷ []) (CK40 ∷ Toff213 ∷ [])
  b1 = at 5 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 7 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ023 CK41: 145 steps
lem-comm-CCZ023-CK41 : Complete 4 → ⟪ (CCZ023 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CCZ023 ∷ []) ⟫ʷ
lem-comm-CCZ023-CK41 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (run b18))))))))))))))))))
  where
  b0 : Chain (CCZ023 ∷ CK41 ∷ []) (Sw12 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sw12 ∷ CCZ013 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (CS23 ∷ CX02 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b1 = at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (CS23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS23 ∷ CX02 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b2 = at 2 2 (CS23⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸ done

  b3 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ CS14 ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b3 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Sw34 ∷ Sw12 ∷ CS14 ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b4 = at 3 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CS14⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24⁻ ∷ []) (CS14⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b5 : Chain (Sw34 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b5 = at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b6 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b6 = at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ CCZ024 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b7 = at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ CCZ024 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ CK43 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b8 = at 2 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 10 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CK32 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CK31 ∷ []) (CK32 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CK43 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK42 ∷ []) (CK43 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ CK43 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ CCZ034 ∷ Sw23 ∷ Sw34 ∷ [])
  b9 = at 6 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸
       at 5 2 (CK42 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK43 ∷ []) (CK42 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (CK31 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CK32 ∷ []) (CK31 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 9 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ CCZ034 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b10 = at 3 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b11 = at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw34 ∷ [])
  b12 = at 5 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 11 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 9 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

  b13 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b13 = at 4 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b14 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ CX02 ∷ CS03 ∷ [])
  b14 = at 9 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b15 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ CX02 ∷ CS03 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ Sw12 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ [])
  b15 = at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done

  b16 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ Sw12 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ [])
  b16 = at 8 2 (CS13⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b17 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ CCZ023 ∷ [])
  b17 = at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 7 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ CCZ023 ∷ []) (CK41 ∷ CCZ023 ∷ [])
  b18 = at 0 5 (CK41 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF023 CK41: 181 steps
lem-comm-TOFF023-CK41 : Complete 4 → ⟪ (Toff023 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Toff023 ∷ []) ⟫ʷ
lem-comm-TOFF023-CK41 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (run b22))))))))))))))))))))))
  where
  b0 : Chain (Toff023 ∷ CK41 ∷ []) (Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sw12 ∷ Toff013 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b1 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b2 : Chain (Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b2 = at 0 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 1 2 (CS23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b3 = at 6 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 8 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑)) ▸
       at 6 2 (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑)) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸ done

  b4 : Chain (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b4 = at 3 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑)) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸ done

  b5 : Chain (Sw34 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b5 = at 3 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24⁻ ∷ []) (CS14⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b6 : Chain (Sw34 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b6 = at 8 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw34 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b7 = at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸ done

  b8 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw34 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b8 = at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b9 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ Toff014 ∷ Sw12 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b9 = at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Sw34 ∷ Sw12 ∷ Toff014 ∷ Sw12 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CK32 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b10 = at 1 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 10 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CK32 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CK31 ∷ []) (CK32 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CK32 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b11 = at 8 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CK43 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK42 ∷ []) (CK43 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CK43 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₁₀)) ▸
       at 5 2 (CK42 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK43 ∷ []) (CK42 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (CK31 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CK32 ∷ []) (CK31 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b12 = at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 9 (Toff034 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b13 = at 6 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b14 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b14 = at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 14 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b15 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b15 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 12 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 10 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 12 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 13 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

  b16 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b16 = at 4 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 5 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b17 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ Sw34 ∷ ι ∷ [])
  b17 = at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 10 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 9 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 11 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 12 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑)) ▸ done

  b18 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ Sw34 ∷ ι ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ K0 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ [])
  b18 = at 10 2 (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑)) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b19 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ K0 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ [])
  b19 = at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 7 2 (CS13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 (CS13⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b20 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b20 = at 11 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 13 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b21 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw12 ∷ [])
  b21 = at 8 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b22 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw12 ∷ []) (CK41 ∷ Toff023 ∷ [])
  b22 = at 14 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 7 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 0 5 (CK41 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ013 CK42: 15 steps
lem-comm-CCZ013-CK42 : Complete 4 → ⟪ (CCZ013 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CK42 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ013 ∷ CK42 ∷ []) (Sw34 ∷ Sw34 ∷ Sw23 ∷ CK43 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CK43 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK42 ∷ []) (CK43 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸ done

  b1 : Chain (Sw34 ∷ Sw34 ∷ Sw23 ∷ CK43 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (CK42 ∷ CCZ013 ∷ [])
  b1 = at 2 2 (CK42 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK43 ∷ []) (CK42 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 2 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF013 CK42: 15 steps
lem-comm-TOFF013-CK42 : Complete 4 → ⟪ (Toff013 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Toff013 ∷ []) ⟫ʷ
lem-comm-TOFF013-CK42 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff013 ∷ CK42 ∷ []) (Sw34 ∷ Sw34 ∷ Sw23 ∷ CK43 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CK43 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK42 ∷ []) (CK43 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CK43 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₁₀)) ▸ done

  b1 : Chain (Sw34 ∷ Sw34 ∷ Sw23 ∷ CK43 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (CK42 ∷ Toff013 ∷ [])
  b1 = at 2 2 (CK42 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK43 ∷ []) (CK42 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 2 5 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ024 CX13: 11 steps
lem-comm-CCZ024-CX13 : Complete 4 → ⟪ (CCZ024 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CCZ024 ∷ []) ⟫ʷ
lem-comm-CCZ024-CX13 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ024 ∷ CX13 ∷ []) (Sw12 ∷ Sw34 ∷ Sw34 ∷ CX23 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CX13 ∷ []) (CX23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX24 ∷ []) (CX34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁)) ▸
       at 2 2 (CX24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX34 ∷ []) (CX24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw34 ∷ CX23 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (CX13 ∷ CCZ024 ∷ [])
  b1 = at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (CX13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CX23 ∷ []) (CX13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 7 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF213 CX04: 13 steps
lem-comm-TOFF213-CX04 : Complete 4 → ⟪ (Toff213 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ Toff213 ∷ []) ⟫ʷ
lem-comm-TOFF213-CX04 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff213 ∷ CX04 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Toff314 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Toff324 ∷ []) (lw0 c4 (Toff314 ∷ Sw12 ∷ []) (Sw12 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX01 ∷ Toff324 ∷ []) (sym (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 4 2 (Sw12 ∷ Toff314 ∷ []) (lw0 c4 (Toff324 ∷ Sw12 ∷ []) (Sw12 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Toff314 ∷ Sw23 ∷ Sw34 ∷ []) (CX04 ∷ Toff213 ∷ [])
  b1 = at 5 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ02 TOFF314: 23 steps
lem-comm-CZ02-TOFF314 : Complete 4 → ⟪ (CZ02 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CZ02 ∷ []) ⟫ʷ
lem-comm-CZ02-TOFF314 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CZ02 ∷ Toff314 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CZ04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Toff314 ∷ CZ02 ∷ [])
  b2 = at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 3 7 (CZ04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 5 (Toff314 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd02 TOFF314: 23 steps
lem-comm-CSd02-TOFF314 : Complete 4 → ⟪ (CS02⁻ ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-comm-CSd02-TOFF314 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02⁻ ∷ Toff314 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Toff314 ∷ CS02⁻ ∷ [])
  b2 = at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 3 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 5 (Toff314 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS02 TOFF314: 23 steps
lem-comm-CS02-TOFF314 : Complete 4 → ⟪ (CS02 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS02 ∷ []) ⟫ʷ
lem-comm-CS02-TOFF314 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02 ∷ Toff314 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff324 ∷ CS01 ∷ []) (c₂ (CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Toff314 ∷ CS02 ∷ [])
  b2 = at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 3 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 5 (Toff314 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF413 at 2: 4 steps
lem-resp-TOFF413-at-2 : Complete 4 → ⟪ (Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff423 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF413-at-2 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ []) (Sw12 ∷ Sw01 ∷ Toff423 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw12 ∷ Toff423 ∷ []) (lw0 c4 (Toff413 ∷ Sw12 ∷ []) (Sw12 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Toff423 ∷ []) (sym (c₂ (Swap) (Toffᵗ))) ▸ done


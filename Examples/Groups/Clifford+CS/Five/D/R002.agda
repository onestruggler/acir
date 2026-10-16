{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R002 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)

-- nat 1 CCZ023: 2 steps
lem-nat-1-CCZ023 : Complete 4 → ⟪ (Sw12 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CCZ023 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CCZ013 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 1 TOFF203: 2 steps
lem-nat-1-TOFF203 : Complete 4 → ⟪ (Sw12 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF203 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Toff203 ∷ []) (Toff103 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Toff103 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 1 BOX(0;24): 3 steps
lem-nat-1-BOX⟨0·24⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-14 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·24⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-24 ∷ []) (Bx0-14 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CZ24 ∷ []) (CZ14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-14 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;034): 8 steps
lem-nat-1-BOX⟨2·034⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-034 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·034⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-034 ∷ []) (Bx1-034 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 2 2 (Bx0-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·24⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx0-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·24⟩ c4) ▸
       at 0 6 (Bx1-034 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;2134): 8 steps
lem-nat-1-BOX⟨0·2134⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·2134⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-2134 ∷ []) (Bx0-1234 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-034 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·034⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-034 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·034⟩ c4) ▸
       at 0 6 (Bx0-1234 ∷ []) (refl) ▸ done


-- nat 1 CCZ034: 107 steps
lem-nat-1-CCZ034 : Complete 4 → ⟪ (Sw12 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CCZ034 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Sw12 ∷ CCZ034 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CS14 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CS14 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Sw12 ∷ Sw23 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b3 = at 5 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Sw12 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS04 ∷ Sw23 ∷ [])
  b4 = at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (Sw12 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS04 ∷ Sw23 ∷ []) (Sw12 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ Sw23 ∷ [])
  b5 = at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw12 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ Sw23 ∷ []) (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ [])
  b6 = at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 1 2 (CX03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CX03 ∷ []) (CX03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS34⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS)) ▸
       at 3 2 (CX03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CX03 ∷ []) (CX03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 5 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ []) (Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS04 ∷ Sw12 ∷ [])
  b7 = at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 4 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS04 ∷ Sw12 ∷ []) (Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ Sw12 ∷ [])
  b8 = at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ [])
  b9 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CS14⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24⁻ ∷ []) (CS14⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Sw23 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b10 = at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b11 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b11 = at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ CCZ013 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b12 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ CCZ013 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (CCZ034 ∷ Sw12 ∷ [])
  b13 = at 2 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 CCZ014: 2 steps
lem-nat-3-CCZ014 : Complete 4 → ⟪ (Sw34 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CCZ014 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CCZ014 ∷ []) (CCZ013 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 3 TOFF104: 2 steps
lem-nat-3-TOFF104 : Complete 4 → ⟪ (Sw34 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF104 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Toff104 ∷ []) (Toff103 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 3 CZ13: 2 steps
lem-nat-3-CZ13 : Complete 4 → ⟪ (Sw34 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ14 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CZ13 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CZ13 ∷ []) (CZ14 ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CZ14 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(0;13): 3 steps
lem-nat-3-BOX⟨0·13⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-14 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·13⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-13 ∷ []) (Bx0-14 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw34 ∷ []) (lem-nat-3-CZ13 c4) ▸
       at 0 1 (Bx0-14 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;043): 8 steps
lem-nat-3-BOX⟨1·043⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-034 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·043⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-043 ∷ []) (Bx1-034 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 1 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 2 2 (Bx0-14 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·13⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 4 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 5 2 (Bx0-14 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·13⟩ c4) ▸
       at 0 6 (Bx1-034 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;1243): 8 steps
lem-nat-3-BOX⟨0·1243⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·1243⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-1243 ∷ []) (Bx0-1234 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-043 ∷ Toff012 ∷ CCZ012 ∷ Bx1-043 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 2 2 (Bx1-034 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·043⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx1-034 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·043⟩ c4) ▸
       at 0 6 (Bx0-1234 ∷ []) (refl) ▸ done


-- nat 3 CCZ034: 117 steps
lem-nat-3-CCZ034 : Complete 4 → ⟪ (Sw34 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CCZ034 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (run b14))))))))))))))
  where
  b0 : Chain (Sw34 ∷ CCZ034 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS14 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS14 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Sw34 ∷ Sw23 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b3 = at 5 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Sw34 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS04 ∷ Sw23 ∷ [])
  b4 = at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (Sw34 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS04 ∷ Sw23 ∷ []) (Sw34 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ Sw23 ∷ [])
  b5 = at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw34 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ Sw23 ∷ []) (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ Sw34 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ [])
  b6 = at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (CS34 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CS34 ∷ []) (CS34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS34⁻ ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ Sw34 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ []) (Sw23 ∷ CS24 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ Sw34 ∷ [])
  b7 = at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b8 : Chain (Sw23 ∷ CS24 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ Sw34 ∷ []) (Sw23 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ [])
  b8 = at 7 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b9 : Chain (Sw23 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ CS14 ∷ Sw34 ∷ Sw12 ∷ CX03 ∷ Sw34 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ [])
  b9 = at 9 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b10 : Chain (Sw23 ∷ Sw12 ∷ CS14 ∷ Sw34 ∷ Sw12 ∷ CX03 ∷ Sw34 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ Sw12 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ [])
  b10 = at 4 2 (CX03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CX03 ∷ []) (CX03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 3 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS14⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24⁻ ∷ []) (CS14⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 2 (CX03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CX03 ∷ []) (CX03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b11 : Chain (Sw23 ∷ Sw12 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ Sw12 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX03 ∷ Sw34 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b11 = at 5 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 5 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX03 ∷ Sw34 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b12 = at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b13 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b13 = at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 4 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸ done

  b14 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (CCZ034 ∷ Sw34 ∷ [])
  b14 = at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 CCZ013: 2 steps
lem-nat-2-CCZ013 : Complete 4 → ⟪ (Sw23 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CCZ013 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 2 TOFF013: 2 steps
lem-nat-2-TOFF013 : Complete 4 → ⟪ (Sw23 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF013 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Toff013 ∷ []) (Toff012 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 2 CCZ012: 2 steps
lem-nat-2-CCZ012 : Complete 4 → ⟪ (Sw23 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CCZ012 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 TOFF102: 2 steps
lem-nat-2-TOFF102 : Complete 4 → ⟪ (Sw23 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF102 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Toff102 ∷ []) (Toff103 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(0;14): 3 steps
lem-nat-2-BOX⟨0·14⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-14 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·14⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-14 ∷ []) (Bx0-14 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ14 ∷ []) (CZ14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-14 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;024): 8 steps
lem-nat-2-BOX⟨1·024⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-034 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·024⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-024 ∷ []) (Bx1-034 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 2 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·14⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·14⟩ c4) ▸
       at 0 6 (Bx1-034 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;1324): 8 steps
lem-nat-2-BOX⟨0·1324⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·1324⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-1324 ∷ []) (Bx0-1234 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 2 2 (Bx1-034 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·024⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx1-034 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·024⟩ c4) ▸
       at 0 6 (Bx0-1234 ∷ []) (refl) ▸ done


-- nat 2 TOFF012: 2 steps
lem-nat-2-TOFF012 : Complete 4 → ⟪ (Sw23 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF012 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Toff012 ∷ []) (Toff013 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 CCZ034: 2 steps
lem-nat-2-CCZ034 : Complete 4 → ⟪ (Sw23 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CCZ034 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 3 TOFF014: 2 steps
lem-nat-3-TOFF014 : Complete 4 → ⟪ (Sw34 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF014 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Toff014 ∷ []) (Toff013 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 3 BOX(1;023): 8 steps
lem-nat-3-BOX⟨1·023⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-024 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·023⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-023 ∷ []) (Bx1-024 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 2 2 (Bx0-14 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·13⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx0-14 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·13⟩ c4) ▸
       at 0 6 (Bx1-024 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;1423): 8 steps
lem-nat-3-BOX⟨0·1423⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·1423⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-1423 ∷ []) (Bx0-1324 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 1 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 2 2 (Bx1-024 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·023⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 4 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 5 2 (Bx1-024 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·023⟩ c4) ▸
       at 0 6 (Bx0-1324 ∷ []) (refl) ▸ done


-- nat 3 TOFF013: 2 steps
lem-nat-3-TOFF013 : Complete 4 → ⟪ (Sw34 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF013 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Toff013 ∷ []) (Toff014 ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 CCZ024: 62 steps
lem-nat-3-CCZ024 : Complete 4 → ⟪ (Sw34 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CCZ024 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Sw34 ∷ CCZ024 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (Sw34 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ [])
  b1 = at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b2 : Chain (Sw34 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ []) (Sw34 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ [])
  b2 = at 6 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Sw34 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ []) (Sw34 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw12 ∷ [])
  b3 = at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b4 : Chain (Sw34 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw12 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw34 ∷ CS04 ∷ [])
  b4 = at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 1 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CX02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))) ▸
       at 3 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (CX02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))) ▸ done

  b5 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw34 ∷ CS04 ∷ []) (Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ [])
  b5 = at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (CS13⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ []) (Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ [])
  b6 = at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b7 : Chain (Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ []) (CCZ023 ∷ Sw34 ∷ [])
  b7 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 2 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 CCZ024: 2 steps
lem-nat-1-CCZ024 : Complete 4 → ⟪ (Sw12 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CCZ024 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 1 TOFF024: 2 steps
lem-nat-1-TOFF024 : Complete 4 → ⟪ (Sw12 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF024 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Toff024 ∷ []) (Toff014 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 1 BOX(0;23): 3 steps
lem-nat-1-BOX⟨0·23⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-13 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·23⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-23 ∷ []) (Bx0-13 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ23 ∷ []) (CZ13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-13 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;013): 8 steps
lem-nat-1-BOX⟨2·013⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-013 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-023 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·013⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-013 ∷ []) (Bx1-023 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·23⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·23⟩ c4) ▸
       at 0 6 (Bx1-023 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;2413): 8 steps
lem-nat-1-BOX⟨0·2413⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·2413⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-2413 ∷ []) (Bx0-1423 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 2 2 (Bx1-023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·013⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx1-023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·013⟩ c4) ▸
       at 0 6 (Bx0-1423 ∷ []) (refl) ▸ done


-- nat 1 TOFF014: 2 steps
lem-nat-1-TOFF014 : Complete 4 → ⟪ (Sw12 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF014 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Toff014 ∷ []) (Toff024 ∷ Sw12 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 TOFF034: 2 steps
lem-nat-2-TOFF034 : Complete 4 → ⟪ (Sw23 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF034 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Toff034 ∷ []) (Toff024 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 2 TOFF301: 2 steps
lem-nat-2-TOFF301 : Complete 4 → ⟪ (Sw23 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF301 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Toff301 ∷ []) (Toff201 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 2 BOX(0;32): 3 steps
lem-nat-2-BOX⟨0·32⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-23 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·32⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-32 ∷ []) (Bx0-23 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CZ23 ∷ []) (CZ23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-23 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;012): 8 steps
lem-nat-2-BOX⟨3·012⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-013 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·012⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-012 ∷ []) (Bx2-013 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 2 2 (Bx0-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·32⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx0-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·32⟩ c4) ▸
       at 0 6 (Bx2-013 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;3412): 8 steps
lem-nat-2-BOX⟨0·3412⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·3412⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-3412 ∷ []) (Bx0-2413 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 2 2 (Bx2-013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·012⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx2-013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·012⟩ c4) ▸
       at 0 6 (Bx0-2413 ∷ []) (refl) ▸ done


-- nat 2 TOFF024: 2 steps
lem-nat-2-TOFF024 : Complete 4 → ⟪ (Sw23 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF024 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Toff024 ∷ []) (Toff034 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 CCZ024: 2 steps
lem-nat-2-CCZ024 : Complete 4 → ⟪ (Sw23 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CCZ024 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 TOFF103: 2 steps
lem-nat-2-TOFF103 : Complete 4 → ⟪ (Sw23 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF103 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Toff103 ∷ []) (Toff102 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 2 BOX(1;034): 8 steps
lem-nat-2-BOX⟨1·034⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-024 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·034⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-034 ∷ []) (Bx1-024 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 2 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·14⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·14⟩ c4) ▸
       at 0 6 (Bx1-024 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;1234): 8 steps
lem-nat-2-BOX⟨0·1234⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-1234 ∷ []) (Bx0-1324 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 2 2 (Bx1-024 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·034⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx1-024 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·034⟩ c4) ▸
       at 0 6 (Bx0-1324 ∷ []) (refl) ▸ done


{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R017 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)

-- comm CX04 TOFF312: 13 steps
lem-comm-CX04-TOFF312 : Complete 4 → ⟪ (CX04 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CX04 ∷ []) ⟫ʷ
lem-comm-CX04-TOFF312 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX04 ∷ Toff312 ∷ []) (Sw34 ∷ Sw23 ∷ Toff413 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Toff423 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 2 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff413 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff312 ∷ CX04 ∷ [])
  b1 = at 2 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 1 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 1 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX30 CCZ124: 9 steps
lem-comm-CX30-CCZ124 : Complete 4 → ⟪ (CX30 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CX30 ∷ []) ⟫ʷ
lem-comm-CX30-CCZ124 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX30 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ124 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (CCZ124 ∷ CX30 ∷ [])
  b1 = at 1 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX30 TOFF214: 9 steps
lem-comm-CX30-TOFF214 : Complete 4 → ⟪ (CX30 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CX30 ∷ []) ⟫ʷ
lem-comm-CX30-TOFF214 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX30 ∷ Toff214 ∷ []) (Toff214 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff324 ∷ CX10 ∷ []) (c₂ (CX₁₀) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b1 : Chain (Toff214 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (Toff214 ∷ CX30 ∷ [])
  b1 = at 1 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ14 TOFF203: 7 steps
lem-comm-CZ14-TOFF203 : Complete 4 → ⟪ (CZ14 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CZ14 ∷ []) ⟫ʷ
lem-comm-CZ14-TOFF203 c4 = run b0
  where
  b0 : Chain (CZ14 ∷ Toff203 ∷ []) (Toff203 ∷ CZ14 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CZ24 ∷ []) (lw0 c4 (CZ14 ∷ Sw12 ∷ []) (Sw12 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CZ34 ∷ []) (lw0 c4 (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff102 ∷ CZ34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CZ))) ▸
       at 3 2 (Sw23 ∷ CZ24 ∷ []) (lw0 c4 (CZ34 ∷ Sw23 ∷ []) (Sw23 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ CZ14 ∷ []) (lw0 c4 (CZ24 ∷ Sw12 ∷ []) (Sw12 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (Toff203 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS12 TOFF304: 15 steps
lem-comm-CS12-TOFF304 : Complete 4 → ⟪ (CS12 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CS12 ∷ []) ⟫ʷ
lem-comm-CS12-TOFF304 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS12 ∷ Toff304 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23 ∷ []) (lw4 c4 (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CS34 ∷ []) (lw0 c4 (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff102 ∷ CS34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CS))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff304 ∷ CS12 ∷ [])
  b1 = at 5 2 (Sw23 ∷ CS24 ∷ []) (lw0 c4 (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ CS13 ∷ []) (lw4 c4 (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 9 (Toff304 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF314 CSd02: 23 steps
lem-comm-TOFF314-CSd02 : Complete 4 → ⟪ (Toff314 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Toff314 ∷ []) ⟫ʷ
lem-comm-TOFF314-CSd02 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff314 ∷ CS02⁻ ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Toff214 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Toff214 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ Toff324 ∷ []) (lw0 c4 (Toff314 ∷ Sw12 ∷ []) (Sw12 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS01⁻ ∷ Toff324 ∷ []) (sym (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 6 2 (Sw12 ∷ Toff314 ∷ []) (lw0 c4 (Toff324 ∷ Sw12 ∷ []) (Sw12 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CS02⁻ ∷ Toff314 ∷ [])
  b2 = at 10 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 2 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 1 5 (Toff314 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd14 TOFF302: 7 steps
lem-comm-CSd14-TOFF302 : Complete 4 → ⟪ (CS14⁻ ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS14⁻ ∷ []) ⟫ʷ
lem-comm-CSd14-TOFF302 c4 = run b0
  where
  b0 : Chain (CS14⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS14⁻ ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS24⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CS34⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff201 ∷ CS34⁻ ∷ []) (sym (c₃ (Toffᵗ) (CS • CS • CS))) ▸
       at 3 2 (Sw23 ∷ CS24⁻ ∷ []) (lw0 c4 (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ CS14⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 5 (Toff302 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CX30 at 2: 4 steps
lem-resp-CX30-at-2 : Complete 4 → ⟪ (CX30 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX31 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX30-at-2 c4 = run b0
  where
  b0 : Chain (CX30 ∷ []) (Sw12 ∷ Sw01 ∷ CX31 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw12 ∷ CX30 ∷ []) (lw4 c4 (CX30 ∷ Sw12 ∷ []) (Sw12 ∷ CX30 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CX31 ∷ []) (lw4 c4 (CX30 ∷ Sw01 ∷ []) (Sw01 ∷ CX31 ∷ []) tt tt Eq.refl) ▸ done


-- comm CSd02 CCZ134: 23 steps
lem-comm-CSd02-CCZ134 : Complete 4 → ⟪ (CS02⁻ ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-comm-CSd02-CCZ134 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02⁻ ∷ CCZ134 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CCZ134 ∷ CS02⁻ ∷ [])
  b2 = at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 3 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS02 CCZ134: 23 steps
lem-comm-CS02-CCZ134 : Complete 4 → ⟪ (CS02 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CS02 ∷ []) ⟫ʷ
lem-comm-CS02-CCZ134 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02 ∷ CCZ134 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CCZ134 ∷ CS02 ∷ [])
  b2 = at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 3 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ14 TOFF302: 7 steps
lem-comm-CZ14-TOFF302 : Complete 4 → ⟪ (CZ14 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CZ14 ∷ []) ⟫ʷ
lem-comm-CZ14-TOFF302 c4 = run b0
  where
  b0 : Chain (CZ14 ∷ Toff302 ∷ []) (Toff302 ∷ CZ14 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CZ24 ∷ []) (lw0 c4 (CZ14 ∷ Sw12 ∷ []) (Sw12 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CZ34 ∷ []) (lw0 c4 (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff201 ∷ CZ34 ∷ []) (sym (c₃ (Toffᵗ) (CZ))) ▸
       at 3 2 (Sw23 ∷ CZ24 ∷ []) (lw0 c4 (CZ34 ∷ Sw23 ∷ []) (Sw23 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ CZ14 ∷ []) (lw0 c4 (CZ24 ∷ Sw12 ∷ []) (Sw12 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (Toff302 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS03 TOFF214: 9 steps
lem-comm-CS03-TOFF214 : Complete 4 → ⟪ (CS03 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS03 ∷ []) ⟫ʷ
lem-comm-CS03-TOFF214 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ Toff214 ∷ []) (Toff214 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff324 ∷ CS01 ∷ []) (c₂ (CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b1 : Chain (Toff214 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (Toff214 ∷ CS03 ∷ [])
  b1 = at 1 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF214 CS03: 9 steps
lem-comm-TOFF214-CS03 : Complete 4 → ⟪ (Toff214 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff214 ∷ []) ⟫ʷ
lem-comm-TOFF214-CS03 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff214 ∷ CS03 ∷ []) (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ Toff324 ∷ []) (lw0 c4 (Toff314 ∷ Sw12 ∷ []) (Sw12 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS01 ∷ Toff324 ∷ []) (sym (c₂ (CS) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 3 2 (Sw12 ∷ Toff314 ∷ []) (lw0 c4 (Toff324 ∷ Sw12 ∷ []) (Sw12 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ []) (CS03 ∷ Toff214 ∷ [])
  b1 = at 0 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ23 TOFF014: 9 steps
lem-comm-CZ23-TOFF014 : Complete 4 → ⟪ (CZ23 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CZ23 ∷ []) ⟫ʷ
lem-comm-CZ23-TOFF014 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ23 ∷ Toff014 ∷ []) (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CZ23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CZ24 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ CZ34 ∷ []) (lw0 c4 (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ CZ34 ∷ []) (sym (c₃ (Toff) (CZ))) ▸
       at 3 2 (Sw23 ∷ CZ24 ∷ []) (lw0 c4 (CZ34 ∷ Sw23 ∷ []) (Sw23 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CZ23 ∷ []) (Toff014 ∷ CZ23 ∷ [])
  b1 = at 0 5 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ24 TOFF301: 5 steps
lem-comm-CZ24-TOFF301 : Complete 4 → ⟪ (CZ24 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CZ24 ∷ []) ⟫ʷ
lem-comm-CZ24-TOFF301 c4 = run b0
  where
  b0 : Chain (CZ24 ∷ Toff301 ∷ []) (Toff301 ∷ CZ24 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CZ34 ∷ []) (lw0 c4 (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ CZ34 ∷ []) (sym (c₃ (Toffᵗ) (CZ))) ▸
       at 2 2 (Sw23 ∷ CZ24 ∷ []) (lw0 c4 (CZ34 ∷ Sw23 ∷ []) (Sw23 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm SWAP14 BOX(3;20): 7 steps
lem-comm-SWAP14-BOX⟨3·20⟩ : Complete 4 → ⟪ (Sw14 ∷ Bx3-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-20 ∷ Sw14 ∷ []) ⟫ʷ
lem-comm-SWAP14-BOX⟨3·20⟩ c4 = run b0
  where
  b0 : Chain (Sw14 ∷ Bx3-20 ∷ []) (Bx3-20 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 1 1 (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ Sw24 ∷ []) (lw0 c4 (Sw14 ∷ Sw12 ∷ []) (Sw12 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CZ01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 2 2 (Sw12 ∷ Sw14 ∷ []) (lw0 c4 (Sw24 ∷ Sw12 ∷ []) (Sw12 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CZ02 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx3-20 ∷ []) (refl) ▸ done


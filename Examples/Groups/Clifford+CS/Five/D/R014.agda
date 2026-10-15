{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R014 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)

-- comm CS24 TOFF301: 5 steps
lem-comm-CS24-TOFF301 : Complete 4 → ⟪ (CS24 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS24 ∷ []) ⟫ʷ
lem-comm-CS24-TOFF301 c4 = run b0
  where
  b0 : Chain (CS24 ∷ Toff301 ∷ []) (Toff301 ∷ CS24 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CS34 ∷ []) (lw0 c4 (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ CS34 ∷ []) (sym (c₃ (Toffᵗ) (CS))) ▸
       at 2 2 (Sw23 ∷ CS24 ∷ []) (lw0 c4 (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm SWAP02 BOX(3;14): 11 steps
lem-comm-SWAP02-BOX⟨3·14⟩ : Complete 4 → ⟪ (Sw02 ∷ Bx3-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-14 ∷ Sw02 ∷ []) ⟫ʷ
lem-comm-SWAP02-BOX⟨3·14⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw02 ∷ Bx3-14 ∷ []) (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw02 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw02 ∷ []) (c₃ (Swap ↑ • Swap • Swap ↑) (Swap)) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Sw03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CZ12 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ CZ12 ∷ []) (CZ12 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ Sw02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw02 ∷ Sw34 ∷ []) (Bx3-14 ∷ Sw02 ∷ [])
  b1 = at 4 2 (Sw34 ∷ Sw02 ∷ []) (c₃ (Swap ↑ • Swap • Swap ↑) (Swap)) ▸
       at 0 5 (CZ14 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx3-14 ∷ []) (refl) ▸ done


-- comm CZ12 TOFF403: 15 steps
lem-comm-CZ12-TOFF403 : Complete 4 → ⟪ (CZ12 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CZ12 ∷ []) ⟫ʷ
lem-comm-CZ12-TOFF403 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ12 ∷ Toff403 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ CZ34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CZ23 ∷ []) (lw4 c4 (CZ13 ∷ Sw12 ∷ []) (Sw12 ∷ CZ23 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CZ24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CZ34 ∷ []) (lw0 c4 (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff201 ∷ CZ34 ∷ []) (sym (c₃ (Toffᵗ) (CZ))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ CZ34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff403 ∷ CZ12 ∷ [])
  b1 = at 5 2 (Sw23 ∷ CZ24 ∷ []) (lw0 c4 (CZ34 ∷ Sw23 ∷ []) (Sw23 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ CZ13 ∷ []) (lw4 c4 (CZ23 ∷ Sw12 ∷ []) (Sw12 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 9 (Toff403 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS04 TOFF312: 13 steps
lem-comm-CS04-TOFF312 : Complete 4 → ⟪ (CS04 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CS04 ∷ []) ⟫ʷ
lem-comm-CS04-TOFF312 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS04 ∷ Toff312 ∷ []) (Sw34 ∷ Sw23 ∷ Toff413 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Toff423 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff423 ∷ CS01 ∷ []) (c₂ (CS) (Toffᵗ)) ▸
       at 2 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff413 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff312 ∷ CS04 ∷ [])
  b1 = at 2 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 1 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 1 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF312 CS04: 13 steps
lem-comm-TOFF312-CS04 : Complete 4 → ⟪ (Toff312 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Toff312 ∷ []) ⟫ʷ
lem-comm-TOFF312-CS04 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff312 ∷ CS04 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Toff413 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Toff423 ∷ []) (lw0 c4 (Toff413 ∷ Sw12 ∷ []) (Sw12 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS01 ∷ Toff423 ∷ []) (sym (c₂ (CS) (Toffᵗ))) ▸
       at 4 2 (Sw12 ∷ Toff413 ∷ []) (lw0 c4 (Toff423 ∷ Sw12 ∷ []) (Sw12 ∷ Toff413 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Toff413 ∷ Sw23 ∷ Sw34 ∷ []) (CS04 ∷ Toff312 ∷ [])
  b1 = at 5 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CK41 at 2: 4 steps
lem-resp-CK41-at-2 : Complete 4 → ⟪ (CK41 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CK42 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CK41-at-2 c4 = run b0
  where
  b0 : Chain (CK41 ∷ []) (Sw12 ∷ Sw01 ∷ CK42 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw12 ∷ CK42 ∷ []) (lw0 c4 (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CK42 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))) ▸ done


-- comm CS04 TOFF213: 13 steps
lem-comm-CS04-TOFF213 : Complete 4 → ⟪ (CS04 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CS04 ∷ []) ⟫ʷ
lem-comm-CS04-TOFF213 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS04 ∷ Toff213 ∷ []) (Sw34 ∷ Sw23 ∷ Toff314 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff324 ∷ CS01 ∷ []) (c₂ (CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff314 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff213 ∷ CS04 ∷ [])
  b1 = at 2 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 1 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 1 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd14 CCZ023: 7 steps
lem-comm-CSd14-CCZ023 : Complete 4 → ⟪ (CS14⁻ ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CS14⁻ ∷ []) ⟫ʷ
lem-comm-CSd14-CCZ023 c4 = run b0
  where
  b0 : Chain (CS14⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS14⁻ ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS24⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CS34⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 3 2 (Sw23 ∷ CS24⁻ ∷ []) (lw0 c4 (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ CS14⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 5 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS14 CCZ023: 7 steps
lem-comm-CS14-CCZ023 : Complete 4 → ⟪ (CS14 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CS14 ∷ []) ⟫ʷ
lem-comm-CS14-CCZ023 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS14 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS24 ∷ []) (lw0 c4 (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CS34 ∷ []) (lw0 c4 (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 3 2 (Sw23 ∷ CS24 ∷ []) (lw0 c4 (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ CS14 ∷ []) (lw0 c4 (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CK40 at 2: 12 steps
lem-resp-CK40-at-2 : Complete 4 → ⟪ (CK40 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CK41 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CK40-at-2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK40 ∷ []) (Sw12 ∷ Sw34 ∷ CK30 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 2 (Sw12 ∷ CK30 ∷ []) (lw4 c4 (CK30 ∷ Sw12 ∷ []) (Sw12 ∷ CK30 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ CK30 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CK41 ∷ Sw01 ∷ Sw12 ∷ [])
  b1 = at 3 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CK31 ∷ []) (lw4 c4 (CK30 ∷ Sw01 ∷ []) (Sw01 ∷ CK31 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd04 CCZ123: 13 steps
lem-comm-CSd04-CCZ123 : Complete 4 → ⟪ (CS04⁻ ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-comm-CSd04-CCZ123 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS04⁻ ∷ CCZ123 ∷ []) (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 2 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (CCZ123 ∷ CS04⁻ ∷ [])
  b1 = at 2 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 1 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS04 CCZ123: 13 steps
lem-comm-CS04-CCZ123 : Complete 4 → ⟪ (CS04 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CS04 ∷ []) ⟫ʷ
lem-comm-CS04-CCZ123 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS04 ∷ CCZ123 ∷ []) (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 2 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (CCZ123 ∷ CS04 ∷ [])
  b1 = at 2 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 1 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK40 TOFF213: 13 steps
lem-comm-CK40-TOFF213 : Complete 4 → ⟪ (CK40 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CK40 ∷ []) ⟫ʷ
lem-comm-CK40-TOFF213 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK40 ∷ Toff213 ∷ []) (Sw34 ∷ Sw23 ∷ Toff314 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff324 ∷ CK10 ∷ []) (c₂ (CK₁₀) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff314 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff213 ∷ CK40 ∷ [])
  b1 = at 2 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 1 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 1 7 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CK40 at 3: 20 steps
lem-resp-CK40-at-3 : Complete 4 → ⟪ (CK40 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CK40-at-3 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK40 ∷ []) (Sw23 ∷ CK40 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 3 2 (Sw34 ∷ CK10 ∷ []) (c₂ (CK₁₀) (Swap ↑)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 7 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ CK40 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ CK30 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 2 2 (Sw12 ∷ CK30 ∷ []) (lw4 c4 (CK30 ∷ Sw12 ∷ []) (Sw12 ∷ CK30 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 2 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ CK30 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 4 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 3 2 (Sw01 ∷ CK31 ∷ []) (lw4 c4 (CK30 ∷ Sw01 ∷ []) (Sw01 ∷ CK31 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 3 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd13 TOFF204: 11 steps
lem-comm-CSd13-TOFF204 : Complete 4 → ⟪ (CS13⁻ ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-comm-CSd13-TOFF204 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS13⁻ ∷ Toff204 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS23⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CS34⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff102 ∷ CS34⁻ ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CS • CS • CS))) ▸
       at 4 2 (Sw23 ∷ CS24⁻ ∷ []) (lw0 c4 (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (Toff204 ∷ CS13⁻ ∷ [])
  b1 = at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (Sw12 ∷ CS13⁻ ∷ []) (lw4 c4 (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 7 (Toff204 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS13 TOFF204: 11 steps
lem-comm-CS13-TOFF204 : Complete 4 → ⟪ (CS13 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS13 ∷ []) ⟫ʷ
lem-comm-CS13-TOFF204 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS13 ∷ Toff204 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS23 ∷ []) (lw4 c4 (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CS34 ∷ []) (lw0 c4 (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff102 ∷ CS34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CS))) ▸
       at 4 2 (Sw23 ∷ CS24 ∷ []) (lw0 c4 (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (Toff204 ∷ CS13 ∷ [])
  b1 = at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (Sw12 ∷ CS13 ∷ []) (lw4 c4 (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 0 7 (Toff204 ∷ []) (by-assoc Eq.refl) ▸ done


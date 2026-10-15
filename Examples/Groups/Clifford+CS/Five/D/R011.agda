{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R011 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)

-- resp TOFF402 at 1: 71 steps
lem-resp-TOFF402-at-1 : Complete 4 → ⟪ (Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff412 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF402-at-1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (Toff402 ∷ []) (Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b1 = at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b2 = at 10 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (K4 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K3 ∷ []) (K4 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b3 = at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K4 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K3 ∷ []) (K4 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b4 = at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b5 : Chain (K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw01 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw01 ∷ [])
  b5 = at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 8 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ ι ∷ []) (lw4 c4 (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ K4 ∷ []) (sym (c₂ (Swap) (K ↑ ↑))) ▸
       at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸ done

  b6 : Chain (K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw01 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw01 ∷ []) (Sw01 ∷ K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ [])
  b6 = at 6 2 (Sw01 ∷ CS13 ∷ []) (lw4 c4 (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 6 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ CX12 ∷ []) (lw4 c4 (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CX12 ∷ []) (lw4 c4 (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 0 2 (Sw01 ∷ K4 ∷ []) (sym (c₂ (Swap) (K ↑ ↑))) ▸ done

  b7 : Chain (Sw01 ∷ K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ []) (Sw01 ∷ Sw34 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ [])
  b7 = at 1 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (K3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K4 ∷ []) (K3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸ done

  b8 : Chain (Sw01 ∷ Sw34 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ []) (Sw01 ∷ Toff412 ∷ Sw01 ∷ [])
  b8 = at 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (K3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K4 ∷ []) (K3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 2 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (lw4 c4 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) tt tt Eq.refl) ▸
       at 2 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd12 CCZ034: 15 steps
lem-comm-CSd12-CCZ034 : Complete 4 → ⟪ (CS12⁻ ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-comm-CSd12-CCZ034 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS12⁻ ∷ CCZ034 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ CS34⁻ ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CS34⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ CS34⁻ ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (CCZ034 ∷ CS12⁻ ∷ [])
  b1 = at 5 2 (Sw23 ∷ CS24⁻ ∷ []) (lw0 c4 (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ CS13⁻ ∷ []) (lw4 c4 (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 9 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS12 CCZ034: 15 steps
lem-comm-CS12-CCZ034 : Complete 4 → ⟪ (CS12 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CS12 ∷ []) ⟫ʷ
lem-comm-CS12-CCZ034 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS12 ∷ CCZ034 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23 ∷ []) (lw4 c4 (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CS34 ∷ []) (lw0 c4 (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (CCZ034 ∷ CS12 ∷ [])
  b1 = at 5 2 (Sw23 ∷ CS24 ∷ []) (lw0 c4 (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ CS13 ∷ []) (lw4 c4 (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 9 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CZ02 at 1: 2 steps
lem-resp-CZ02-at-1 : Complete 4 → ⟪ (CZ02 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ12 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CZ02-at-1 c4 = run b0
  where
  b0 : Chain (CZ02 ∷ []) (Sw01 ∷ CZ12 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ CZ12 ∷ []) (lw4 c4 (CZ02 ∷ Sw01 ∷ []) (Sw01 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸ done


-- resp CX20 at 1: 2 steps
lem-resp-CX20-at-1 : Complete 4 → ⟪ (CX20 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX21 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX20-at-1 c4 = run b0
  where
  b0 : Chain (CX20 ∷ []) (Sw01 ∷ CX21 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ CX21 ∷ []) (lw4 c4 (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) tt tt Eq.refl) ▸ done


-- resp CX03 at 1: 2 steps
lem-resp-CX03-at-1 : Complete 4 → ⟪ (CX03 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX13 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX03-at-1 c4 = run b0
  where
  b0 : Chain (CX03 ∷ []) (Sw01 ∷ CX13 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ CX13 ∷ []) (lw4 c4 (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) tt tt Eq.refl) ▸ done


-- resp CZ03 at 1: 2 steps
lem-resp-CZ03-at-1 : Complete 4 → ⟪ (CZ03 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ13 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CZ03-at-1 c4 = run b0
  where
  b0 : Chain (CZ03 ∷ []) (Sw01 ∷ CZ13 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ CZ13 ∷ []) (lw4 c4 (CZ03 ∷ Sw01 ∷ []) (Sw01 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸ done


-- comm CX12 TOFF034: 15 steps
lem-comm-CX12-TOFF034 : Complete 4 → ⟪ (CX12 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX12 ∷ []) ⟫ʷ
lem-comm-CX12-TOFF034 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX12 ∷ Toff034 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ CX34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CX23 ∷ []) (lw4 c4 (CX13 ∷ Sw12 ∷ []) (Sw12 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CX34 ∷ []) (lw0 c4 (CX24 ∷ Sw23 ∷ []) (Sw23 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ CX34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff034 ∷ CX12 ∷ [])
  b1 = at 5 2 (Sw23 ∷ CX24 ∷ []) (lw0 c4 (CX34 ∷ Sw23 ∷ []) (Sw23 ∷ CX24 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ CX13 ∷ []) (lw4 c4 (CX23 ∷ Sw12 ∷ []) (Sw12 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 9 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CX30 at 1: 2 steps
lem-resp-CX30-at-1 : Complete 4 → ⟪ (CX30 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX31 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX30-at-1 c4 = run b0
  where
  b0 : Chain (CX30 ∷ []) (Sw01 ∷ CX31 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ CX31 ∷ []) (lw4 c4 (CX30 ∷ Sw01 ∷ []) (Sw01 ∷ CX31 ∷ []) tt tt Eq.refl) ▸ done


-- resp CZ04 at 3: 20 steps
lem-resp-CZ04-at-3 : Complete 4 → ⟪ (CZ04 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CZ14 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CZ04-at-3 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CZ04 ∷ []) (Sw23 ∷ CZ04 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 3 2 (Sw34 ∷ CZ01 ∷ []) (c₂ (CZ) (Swap ↑)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 7 (CZ04 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ CZ04 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ CZ03 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 2 2 (Sw12 ∷ CZ03 ∷ []) (lw4 c4 (CZ03 ∷ Sw12 ∷ []) (Sw12 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 2 3 (CZ04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ CZ03 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CZ14 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 4 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 3 2 (Sw01 ∷ CZ13 ∷ []) (lw4 c4 (CZ03 ∷ Sw01 ∷ []) (Sw01 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 3 3 (CZ14 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CX40 at 3: 20 steps
lem-resp-CX40-at-3 : Complete 4 → ⟪ (CX40 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX40-at-3 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX40 ∷ []) (Sw23 ∷ CX40 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 3 2 (Sw34 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Swap ↑)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ CX40 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ CX30 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 2 2 (Sw12 ∷ CX30 ∷ []) (lw4 c4 (CX30 ∷ Sw12 ∷ []) (Sw12 ∷ CX30 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 2 3 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ CX30 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 4 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 3 2 (Sw01 ∷ CX31 ∷ []) (lw4 c4 (CX30 ∷ Sw01 ∷ []) (Sw01 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 3 3 (CX41 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CX40 at 1: 6 steps
lem-resp-CX40-at-1 : Complete 4 → ⟪ (CX40 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX41 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX40-at-1 c4 = run b0
  where
  b0 : Chain (CX40 ∷ []) (Sw01 ∷ CX41 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 2 (Sw01 ∷ CX31 ∷ []) (lw4 c4 (CX30 ∷ Sw01 ∷ []) (Sw01 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 3 (CX41 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CK40 at 1: 6 steps
lem-resp-CK40-at-1 : Complete 4 → ⟪ (CK40 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK41 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CK40-at-1 c4 = run b0
  where
  b0 : Chain (CK40 ∷ []) (Sw01 ∷ CK41 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 2 (Sw01 ∷ CK31 ∷ []) (lw4 c4 (CK30 ∷ Sw01 ∷ []) (Sw01 ∷ CK31 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CKd40 at 1: 6 steps
lem-resp-CKd40-at-1 : Complete 4 → ⟪ (CK40⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK41⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CKd40-at-1 c4 = run b0
  where
  b0 : Chain (CK40⁻ ∷ []) (Sw01 ∷ CK41⁻ ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sw34 ∷ CK30⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 2 (Sw01 ∷ CK31⁻ ∷ []) (lw4 c4 (CK30⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK31⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 3 (CK41⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CZ04 at 2: 12 steps
lem-resp-CZ04-at-2 : Complete 4 → ⟪ (CZ04 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CZ14 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CZ04-at-2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ04 ∷ []) (Sw12 ∷ Sw34 ∷ CZ03 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 2 (Sw12 ∷ CZ03 ∷ []) (lw4 c4 (CZ03 ∷ Sw12 ∷ []) (Sw12 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 3 (CZ04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ CZ03 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CZ14 ∷ Sw01 ∷ Sw12 ∷ [])
  b1 = at 3 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CZ13 ∷ []) (lw4 c4 (CZ03 ∷ Sw01 ∷ []) (Sw01 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 3 (CZ14 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX02 CCZ134: 23 steps
lem-comm-CX02-CCZ134 : Complete 4 → ⟪ (CX02 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CX02 ∷ []) ⟫ʷ
lem-comm-CX02-CCZ134 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX02 ∷ CCZ134 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CCZ134 ∷ CX02 ∷ [])
  b2 = at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 3 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done


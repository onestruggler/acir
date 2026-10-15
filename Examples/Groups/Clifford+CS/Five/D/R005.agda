{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R005 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)

-- resp TOFF023 at 1: 2 steps
lem-resp-TOFF023-at-1 : Complete 4 → ⟪ (Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF023-at-1 c4 = run b0
  where
  b0 : Chain (Toff023 ∷ []) (Sw01 ∷ Toff123 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ Toff123 ∷ []) (lw4 c4 (Toff023 ∷ Sw01 ∷ []) (Sw01 ∷ Toff123 ∷ []) tt tt Eq.refl) ▸ done


-- resp TOFF024 at 1: 71 steps
lem-resp-TOFF024-at-1 : Complete 4 → ⟪ (Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff124 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF024-at-1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (Toff024 ∷ []) (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b1 = at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b2 = at 10 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b3 = at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b4 = at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b5 : Chain (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw01 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw01 ∷ [])
  b5 = at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 8 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ ι ∷ []) (lw4 c4 (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ K1 ∷ []) (lw4 c4 (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸ done

  b6 : Chain (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw01 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ [])
  b6 = at 6 2 (Sw01 ∷ CS13 ∷ []) (lw4 c4 (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 6 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ CX12 ∷ []) (lw4 c4 (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CX12 ∷ []) (lw4 c4 (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 0 2 (Sw01 ∷ K1 ∷ []) (lw4 c4 (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (Sw01 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ []) (Sw01 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ [])
  b7 = at 1 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸ done

  b8 : Chain (Sw01 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ []) (Sw01 ∷ Toff124 ∷ Sw01 ∷ [])
  b8 = at 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 2 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (lw4 c4 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) tt tt Eq.refl) ▸
       at 2 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff124 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX14 TOFF023: 7 steps
lem-comm-CX14-TOFF023 : Complete 4 → ⟪ (CX14 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CX14 ∷ []) ⟫ʷ
lem-comm-CX14-TOFF023 c4 = run b0
  where
  b0 : Chain (CX14 ∷ Toff023 ∷ []) (Toff023 ∷ CX14 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CX24 ∷ []) (lw0 c4 (CX14 ∷ Sw12 ∷ []) (Sw12 ∷ CX24 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CX34 ∷ []) (lw0 c4 (CX24 ∷ Sw23 ∷ []) (Sw23 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸
       at 3 2 (Sw23 ∷ CX24 ∷ []) (lw0 c4 (CX34 ∷ Sw23 ∷ []) (Sw23 ∷ CX24 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ CX14 ∷ []) (lw0 c4 (CX24 ∷ Sw12 ∷ []) (Sw12 ∷ CX14 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (Toff023 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF024 at 3: 239 steps
lem-resp-TOFF024-at-3 : Complete 4 → ⟪ (Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff134 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF024-at-3 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (run b29)))))))))))))))))))))))))))))
  where
  b0 : Chain (Toff024 ∷ []) (Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b2 : Chain (Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 11 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 12 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw23 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b3 = at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸ done

  b4 : Chain (Sw23 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b4 = at 11 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 2 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw23 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b5 = at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done

  b6 : Chain (Sw23 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b6 = at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw23 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b7 = at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b8 : Chain (Sw23 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw12 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b8 = at 9 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap)) ▸
       at 7 2 (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap)) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 7 2 (Sw12 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (Sw23 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw12 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ Sw23 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b9 = at 5 2 (Sw12 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ CS34⁻ ∷ []) (sym (c₃ (Swap ↑) (CS • CS • CS))) ▸
       at 3 2 (Sw12 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 1 2 (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap)) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 4 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ Sw23 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b10 = at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 9 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b11 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ [])
  b11 = at 11 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 12 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 13 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ [])
  b12 = at 5 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (CS14⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24⁻ ∷ []) (CS14⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b13 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ [])
  b13 = at 10 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 9 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 11 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b14 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw34 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ [])
  b14 = at 6 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 11 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸ done

  b15 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw34 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ [])
  b15 = at 12 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b16 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Toff014 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ [])
  b16 = at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 6 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done

  b17 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Toff014 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b17 = at 3 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b18 = at 5 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b19 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b19 = at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 12 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 13 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b20 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b20 = at 9 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 11 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 9 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 11 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 12 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

  b21 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b21 = at 3 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 4 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b22 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b22 = at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 9 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 10 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 11 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b23 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b23 = at 3 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸ done

  b24 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b24 = at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 11 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 12 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b25 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ Sw01 ∷ CX13 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b25 = at 9 2 (Sw01 ∷ ι ∷ []) (lw4 c4 (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ K1 ∷ []) (lw4 c4 (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 8 2 (Sw01 ∷ CS13 ∷ []) (lw4 c4 (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 8 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ CX13 ∷ []) (lw4 c4 (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) tt tt Eq.refl) ▸ done

  b26 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ Sw01 ∷ CX13 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ K1 ∷ CS24 ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b26 = at 5 2 (Sw01 ∷ CS34⁻ ∷ []) (sym (c₂ (Swap) ((CS • CS • CS) ↑))) ▸
       at 4 2 (Sw01 ∷ CX13 ∷ []) (lw4 c4 (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ CS34 ∷ []) (sym (c₂ (Swap) (CS ↑))) ▸
       at 2 2 (Sw01 ∷ K1 ∷ []) (lw4 c4 (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 5 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b27 : Chain (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ K1 ∷ CS24 ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b27 = at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸ done

  b28 : Chain (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b28 = at 5 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 9 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 11 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b29 : Chain (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff134 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b29 = at 10 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 12 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 5 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (lw4 c4 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) tt tt Eq.refl) ▸
       at 5 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff124 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff134 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ14 CCZ023: 7 steps
lem-comm-CZ14-CCZ023 : Complete 4 → ⟪ (CZ14 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CZ14 ∷ []) ⟫ʷ
lem-comm-CZ14-CCZ023 c4 = run b0
  where
  b0 : Chain (CZ14 ∷ CCZ023 ∷ []) (CCZ023 ∷ CZ14 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CZ24 ∷ []) (lw0 c4 (CZ14 ∷ Sw12 ∷ []) (Sw12 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CZ34 ∷ []) (lw0 c4 (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 3 2 (Sw23 ∷ CZ24 ∷ []) (lw0 c4 (CZ34 ∷ Sw23 ∷ []) (Sw23 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ CZ14 ∷ []) (lw0 c4 (CZ24 ∷ Sw12 ∷ []) (Sw12 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ14 TOFF023: 7 steps
lem-comm-CZ14-TOFF023 : Complete 4 → ⟪ (CZ14 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CZ14 ∷ []) ⟫ʷ
lem-comm-CZ14-TOFF023 c4 = run b0
  where
  b0 : Chain (CZ14 ∷ Toff023 ∷ []) (Toff023 ∷ CZ14 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CZ24 ∷ []) (lw0 c4 (CZ14 ∷ Sw12 ∷ []) (Sw12 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CZ34 ∷ []) (lw0 c4 (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ CZ34 ∷ []) (sym (c₃ (Toff) (CZ))) ▸
       at 3 2 (Sw23 ∷ CZ24 ∷ []) (lw0 c4 (CZ34 ∷ Sw23 ∷ []) (Sw23 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ CZ14 ∷ []) (lw0 c4 (CZ24 ∷ Sw12 ∷ []) (Sw12 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (Toff023 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF024 CSd13: 11 steps
lem-comm-TOFF024-CSd13 : Complete 4 → ⟪ (Toff024 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Toff024 ∷ []) ⟫ʷ
lem-comm-TOFF024-CSd13 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff024 ∷ CS13⁻ ∷ []) (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS)) ▸
       at 2 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (CS13⁻ ∷ Toff024 ∷ [])
  b1 = at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (CS13⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 7 (Toff024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX24 CCZ013: 5 steps
lem-comm-CX24-CCZ013 : Complete 4 → ⟪ (CX24 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CX24 ∷ []) ⟫ʷ
lem-comm-CX24-CCZ013 c4 = run b0
  where
  b0 : Chain (CX24 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX24 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CX34 ∷ []) (lw0 c4 (CX24 ∷ Sw23 ∷ []) (Sw23 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 2 2 (Sw23 ∷ CX24 ∷ []) (lw0 c4 (CX34 ∷ Sw23 ∷ []) (Sw23 ∷ CX24 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd24 TOFF013: 5 steps
lem-comm-CSd24-TOFF013 : Complete 4 → ⟪ (CS24⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS24⁻ ∷ []) ⟫ʷ
lem-comm-CSd24-TOFF013 c4 = run b0
  where
  b0 : Chain (CS24⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS24⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CS34⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸
       at 2 2 (Sw23 ∷ CS24⁻ ∷ []) (lw0 c4 (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF134 at 2: 4 steps
lem-resp-TOFF134-at-2 : Complete 4 → ⟪ (Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff234 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF134-at-2 c4 = run b0
  where
  b0 : Chain (Toff134 ∷ []) (Sw12 ∷ Sw01 ∷ Toff234 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw12 ∷ Toff234 ∷ []) (lw0 c4 (Toff134 ∷ Sw12 ∷ []) (Sw12 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Toff234 ∷ []) (sym (c₂ (Swap) (Toff))) ▸ done


-- resp TOFF013 at 2: 5 steps
lem-resp-TOFF013-at-2 : Complete 4 → ⟪ (Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF013-at-2 c4 = run b0
  where
  b0 : Chain (Toff013 ∷ []) (Sw12 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Toff123 ∷ []) (lw4 c4 (Toff023 ∷ Sw01 ∷ []) (Sw01 ∷ Toff123 ∷ []) tt tt Eq.refl) ▸ done


-- comm CX24 TOFF013: 5 steps
lem-comm-CX24-TOFF013 : Complete 4 → ⟪ (CX24 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CX24 ∷ []) ⟫ʷ
lem-comm-CX24-TOFF013 c4 = run b0
  where
  b0 : Chain (CX24 ∷ Toff013 ∷ []) (Toff013 ∷ CX24 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CX34 ∷ []) (lw0 c4 (CX24 ∷ Sw23 ∷ []) (Sw23 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸
       at 2 2 (Sw23 ∷ CX24 ∷ []) (lw0 c4 (CX34 ∷ Sw23 ∷ []) (Sw23 ∷ CX24 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ24 CCZ013: 5 steps
lem-comm-CZ24-CCZ013 : Complete 4 → ⟪ (CZ24 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CZ24 ∷ []) ⟫ʷ
lem-comm-CZ24-CCZ013 c4 = run b0
  where
  b0 : Chain (CZ24 ∷ CCZ013 ∷ []) (CCZ013 ∷ CZ24 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CZ34 ∷ []) (lw0 c4 (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 2 2 (Sw23 ∷ CZ24 ∷ []) (lw0 c4 (CZ34 ∷ Sw23 ∷ []) (Sw23 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ24 TOFF013: 5 steps
lem-comm-CZ24-TOFF013 : Complete 4 → ⟪ (CZ24 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CZ24 ∷ []) ⟫ʷ
lem-comm-CZ24-TOFF013 c4 = run b0
  where
  b0 : Chain (CZ24 ∷ Toff013 ∷ []) (Toff013 ∷ CZ24 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CZ34 ∷ []) (lw0 c4 (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ CZ34 ∷ []) (sym (c₃ (Toff) (CZ))) ▸
       at 2 2 (Sw23 ∷ CZ24 ∷ []) (lw0 c4 (CZ34 ∷ Sw23 ∷ []) (Sw23 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸ done


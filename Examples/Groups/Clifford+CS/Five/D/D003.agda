{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D003 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-VPQ-at122441 ; lem-cQ-at122441 ; lem-tP-at122441)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd13-CCZ024 ; lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CX24-TOFF013 ; lem-comm-CZ24-CCZ013 ; lem-comm-CZ24-TOFF013)
-- QVQ @122441: 3 steps
lem-QVQ-at122441 : Complete 4 → ⟪ (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-QVQ-at122441 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ [])
  b0 = at 0 0 (Toff013 ∷ Toff013 ∷ []) (lw4 c4 [] (Toff013 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (sym (lem-VPQ-at122441 c4)) ▸
       at 4 2 [] (lw4 c4 (CCZ013 ∷ CCZ013 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @122441: 12 steps
lem-box-cP-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-box-cP-at122441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2431 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (lw4 c4 (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (lw4 c4 (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-QVQ-at122441 c4) ▸
       at 1 2 (Toff013 ∷ Toff024 ∷ []) (lem-tP-at122441 c4) ▸
       at 2 2 [] (pw1 c4 (Toff024 ∷ Toff024 ∷ []) [] tt tt Eq.refl) ▸ done


-- Xb-box @122441: 18 steps
lem-Xb-box-at122441 : Complete 4 → ⟪ (X4 ∷ Bx0-2431 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CCZ123 ∷ []) ⟫ʷ
lem-Xb-box-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx0-2431 ∷ X4 ∷ []) (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX23 ∷ CCZ024 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ Toff013 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) (lw4 c4 (CZ02 ∷ Toff013 ∷ []) (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 4 1 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX23 ∷ []) (pw1 c4 (CX23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX23 ∷ CCZ024 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ Toff013 ∷ X4 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CCZ123 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ024 ∷ CX23 ∷ []) (pw1 c4 (CX23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 c4) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CZ02 ∷ []) (pw3 c4 (CZ02 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (X4 ∷ []) (lw3 c4 (X4 ∷ CZ02 ∷ CZ02 ∷ []) (X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff013 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸ done

  b2 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @122441: 13 steps
lem-box-tQ-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at122441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2431 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (lw4 c4 (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (lw4 c4 (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff024 ∷ CCZ024 ∷ CZ24 ∷ []) (pw1 c4 (CCZ024 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ024 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ013 ∷ CZ24 ∷ []) (lem-comm-CZ24-CCZ013 c4) ▸
       at 1 2 (CCZ013 ∷ CCZ024 ∷ []) (lem-cQ-at122441 c4) ▸
       at 2 4 (Toff024 ∷ []) (pw1 c4 (CCZ024 ∷ CZ24 ∷ Toff024 ∷ CCZ024 ∷ []) (Toff024 ∷ []) tt tt Eq.refl) ▸ done


-- t-cP @122441: 5 steps
lem-t-cP-at122441 : Complete 4 → ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff024 ∷ []) ⟫ʷ
lem-t-cP-at122441 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff024 ∷ [])
  b0 = at 0 2 (CCZ024 ∷ Toff024 ∷ CZ24 ∷ []) (pw1 c4 (Toff024 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff024 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff013 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF013 c4) ▸
       at 1 2 (Toff013 ∷ Toff024 ∷ []) (lem-tP-at122441 c4) ▸
       at 2 3 (CCZ024 ∷ Toff024 ∷ []) (pw1 c4 (Toff024 ∷ CZ24 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ Toff024 ∷ []) (lem-tP-at122441 c4) ▸ done


-- box2 @122441: 11 steps
lem-box2-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at122441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2431 ∷ Bx0-2431 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ [])
  b0 = at 0 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 0 (Toff024 ∷ Toff024 ∷ []) (pw1 c4 [] (Toff024 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff024 ∷ []) (lem-t-cP-at122441 c4) ▸
       at 5 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 4 2 [] (pw1 c4 (Toff024 ∷ Toff024 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 [] (lw4 c4 (CCZ013 ∷ CCZ013 ∷ []) [] tt tt Eq.refl) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) []
  b1 = at 2 2 [] (pw1 c4 (Toff024 ∷ Toff024 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 [] (lw4 c4 (CCZ013 ∷ CCZ013 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 [] (pw1 c4 (Toff024 ∷ Toff024 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5-23: 112 steps
lem-F5-23 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ []) ⟫ʷ
lem-F5-23 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ X4 ∷ CX31 ∷ CS23 ∷ CCZ123 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 2 (X4 ∷ Sb⁻0-2-1-3 ∷ []) (c₃ ((CS • CS • CS) ↑) (X ↑)) ▸
       at 4 2 (X4 ∷ CX31 ∷ Toff134 ∷ []) (lw0 c4 (Toff134 ∷ X4 ∷ []) (X4 ∷ CX31 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (X4 ∷ Sb0-2-1-3 ∷ []) (c₃ (CS ↑) (X ↑)) ▸
       at 4 1 (CS12 ∷ []) (refl) ▸
       at 4 2 (CX31 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ CX31 ∷ []) (CX31 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ X4 ∷ CX31 ∷ CS23 ∷ CCZ123 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b1 = at 2 2 (X4 ∷ CX31 ∷ Toff134 ∷ []) (lw0 c4 (Toff134 ∷ X4 ∷ []) (X4 ∷ CX31 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CX31 ∷ Toff134 ∷ []) (lw0 c4 (Toff134 ∷ CX31 ∷ []) (CX31 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS23 ∷ Toff134 ∷ []) (lw0 c4 (Toff134 ∷ CS23 ∷ []) (CS23 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ123 ∷ CCZ234 ∷ Toff134 ∷ []) (lw0 c4 (Toff134 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ234 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 2 6 (X4 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ CX31 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ []) (X4 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-Xb-box-at122441 c4) ▸
       at 9 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 8 1 (CS12⁻ ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b2 = at 8 2 (CCZ024 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 13 2 (CCZ024 ∷ K1⁻ ∷ []) (pw3 c4 (K1⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 12 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 10 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 8 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b3 = at 7 2 (CCZ024 ∷ K1 ∷ []) (pw3 c4 (K1 ∷ CCZ024 ∷ []) (CCZ024 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 8 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS12 ∷ []) (refl) ▸
       at 6 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CCZ024 ∷ K1⁻ ∷ []) (pw3 c4 (K1⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸ done

  b4 : Chain (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CCZ024 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b4 = at 8 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 6 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ K1 ∷ []) (pw3 c4 (K1 ∷ CCZ024 ∷ []) (CCZ024 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ234 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CCZ024 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CCZ024 ∷ CS12 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b5 = at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 3 2 (CCZ024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 4 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (Bx0-2431 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CCZ024 ∷ CS12 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b6 = at 4 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 3 2 (CCZ024 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 1 2 (CCZ024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 2 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 6 (Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ []) (Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff013 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (pw2 c4 (Toff134 ∷ Toff013 ∷ []) (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff134 ∷ CS12 ∷ Toff013 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b7 = at 5 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff013 ∷ CS23 ∷ []) (lw4 c4 (CS23 ∷ Toff013 ∷ []) (Toff013 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 c4) ▸
       at 7 2 (Toff013 ∷ CS34⁻ ∷ []) (pw2 c4 (CS34⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 c4) ▸
       at 5 2 (Toff013 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ Toff013 ∷ []) (Toff013 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff013 ∷ CS23 ∷ []) (lw4 c4 (CS23 ∷ Toff013 ∷ []) (Toff013 ∷ CS23 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff134 ∷ CS12 ∷ Toff013 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12⁻ ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b8 = at 3 2 (Toff013 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ Toff013 ∷ []) (Toff013 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (pw2 c4 (Toff134 ∷ Toff013 ∷ []) (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ024 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 15 2 (CCZ024 ∷ K1⁻ ∷ []) (pw3 c4 (K1⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 12 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12⁻ ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CCZ024 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b9 = at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 10 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ K1 ∷ []) (pw3 c4 (K1 ∷ CCZ024 ∷ []) (CCZ024 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 10 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) (pw1 c4 (Toff034 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ234 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CCZ024 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b10 = at 4 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ024 ∷ K1⁻ ∷ []) (pw3 c4 (K1⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ K1 ∷ []) (pw3 c4 (K1 ∷ CCZ024 ∷ []) (CCZ024 ∷ K1 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ Toff013 ∷ CX24 ∷ CS23 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b11 = at 5 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) (pw1 c4 (Toff034 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (Toff134 ∷ CS12 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ []) (Toff134 ∷ CS12 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff013 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (pw2 c4 (Toff134 ∷ Toff013 ∷ []) (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (Toff013 ∷ CS23 ∷ []) (lw4 c4 (CS23 ∷ Toff013 ∷ []) (Toff013 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 c4) ▸ done

  b12 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ Toff013 ∷ CX24 ∷ CS23 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b12 = at 11 2 (Toff013 ∷ CS34⁻ ∷ []) (pw2 c4 (CS34⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 c4) ▸
       at 9 2 (Toff013 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ Toff013 ∷ []) (Toff013 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 10 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff013 ∷ Toff034 ∷ []) (pw2 c4 (Toff034 ∷ Toff013 ∷ []) (Toff013 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff013 ∷ CS23 ∷ []) (lw4 c4 (CS23 ∷ Toff013 ∷ []) (Toff013 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff013 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ Toff013 ∷ []) (Toff013 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (pw2 c4 (Toff134 ∷ Toff013 ∷ []) (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸ done

  b13 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (CS23 ∷ [])
  b13 = at 4 2 (Toff013 ∷ Toff034 ∷ []) (pw2 c4 (Toff034 ∷ Toff013 ∷ []) (Toff013 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 9 4 (CS23 ∷ CCZ234 ∷ []) (pw1 c4 (CS23 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ []) (CS23 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Toff134 ∷ []) (pw2 c4 (Toff034 ∷ Toff034 ∷ Toff134 ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 0 2 [] (lem-box2-at122441 c4) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 9 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 10 (CS23 ∷ []) (lw0 c4 (Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS23 ∷ []) tt tt Eq.refl) ▸ done


{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D034 where

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
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-box-cP-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-sym-ab-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D015 using (lem-cQ-at233442)
open import Examples.Groups.Clifford+CS.Five.D.D033 using (lem-pairs-at143143 ; lem-sym-bc-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-CSd13-TOFF024 ; lem-comm-TOFF013-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-comm-CK42-CCZ013 ; lem-comm-CK42-TOFF013)
-- box-perm-1423 @243243: 3 steps
lem-box-perm-1423-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-box-perm-1423-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-1342 ∷ [])
  b0 = at 0 1 (Bx0-4123 ∷ []) (lem-sym-ab-at243243 c4) ▸
       at 0 1 (Bx0-4213 ∷ []) (lem-sym-bc-at14213243 c4) ▸
       at 0 1 (Bx0-1342 ∷ []) (lem-pairs-at143143 c4) ▸ done


-- tP @233442: 7 steps
lem-tP-at233442 : Complete 4 → ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ
lem-tP-at233442 c4 = run b0
  where
  b0 : Chain (Toff013 ∷ Toff024 ∷ []) (Toff024 ∷ Toff013 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (pw1 c4 (Toff024 ∷ []) (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CCZ013 ∷ []) (lem-cQ-at233442 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff024 ∷ []) (pw1 c4 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (Toff024 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸ done


-- VPQ @233442: 14 steps
lem-VPQ-at233442 : Complete 4 → ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ
lem-VPQ-at233442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (CS24⁻ ∷ CS13⁻ ∷ S0 ∷ Toff024 ∷ Toff013 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (lw4 c4 (Toff013 ∷ CCZ013 ∷ []) (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (pw1 c4 (Toff024 ∷ CCZ024 ∷ []) (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS24⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)) ▸
       at 2 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 c4) ▸
       at 1 2 (CS24⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)) ▸
       at 0 2 (CS24⁻ ∷ CS13⁻ ∷ []) (lw0 c4 (CS13⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (S0⁻ ∷ S0 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff024 ∷ Toff013 ∷ []) (lem-tP-at233442 c4) ▸ done

  b1 : Chain (CS24⁻ ∷ CS13⁻ ∷ S0 ∷ Toff024 ∷ Toff013 ∷ S0⁻ ∷ []) (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (lw4 c4 [] (S0⁻ ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ CS13⁻ ∷ []) (sym (c₁ (S) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 2 2 (Toff024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF024 c4) ▸
       at 3 2 (S0⁻ ∷ CS13⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 0 4 (Toff024 ∷ CCZ024 ∷ []) (pw1 c4 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (Toff024 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff013 ∷ CCZ013 ∷ []) (lw4 c4 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (Toff013 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @233442: 3 steps
lem-QVQ-at233442 : Complete 4 → ⟪ (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-QVQ-at233442 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ [])
  b0 = at 0 0 (Toff024 ∷ Toff024 ∷ []) (pw1 c4 [] (Toff024 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at233442 c4)) ▸
       at 4 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @233442: 12 steps
lem-box-cP-at233442 : Complete 4 → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-box-cP-at233442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1342 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (pw3 c4 (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (pw3 c4 (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-QVQ-at233442 c4) ▸
       at 1 2 (Toff024 ∷ Toff013 ∷ []) (lem-tP-at233442 c4) ▸
       at 2 2 [] (lw4 c4 (Toff013 ∷ Toff013 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4-K2-CS1: 19 steps
lem-F4-K2-CS1 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-CS1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CCZ013 ∷ X4 ∷ CK42 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (Bx0-1342 ∷ []) (lem-box-perm-1423-at243243 c4) ▸
       at 3 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at233442 c4) ▸
       at 2 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 1 2 (CCZ013 ∷ CK42 ∷ []) (lem-comm-CK42-CCZ013 c4) ▸
       at 0 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸ done

  b1 : Chain (CCZ013 ∷ X4 ∷ CK42 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b1 = at 1 4 (Toff024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK42 ∷ X4 ∷ Toff024 ∷ []) (Toff024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 3 2 (CCZ013 ∷ CK42 ∷ []) (lem-comm-CK42-CCZ013 c4) ▸
       at 2 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 3 4 (Toff024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK42 ∷ X4 ∷ Toff024 ∷ []) (Toff024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-1342 ∷ []) (sym (lem-box-cP-at233442 c4)) ▸
       at 0 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1423-at243243 c4)) ▸
       at 1 7 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b2 = at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- F4-K2-CS2: 17 steps
lem-F4-K2-CS2 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-CS2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CCZ024 ∷ Toff013 ∷ X4 ∷ CK42 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 4 (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK42 ∷ X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 2 2 (Toff013 ∷ CK42 ∷ []) (lem-comm-CK42-TOFF013 c4) ▸
       at 1 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ X4 ∷ CK42 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b1 = at 2 4 (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK42 ∷ X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 4 2 (Toff013 ∷ CK42 ∷ []) (lem-comm-CK42-TOFF013 c4) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 7 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b2 = at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F4-K3-I: 1 steps
lem-F4-K3-I : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K3-S0: 1 steps
lem-F4-K3-S0 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K3-S1: 1 steps
lem-F4-K3-S1 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K3-S2: 1 steps
lem-F4-K3-S2 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K3-S3: 1 steps
lem-F4-K3-S3 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K3-K0: 1 steps
lem-F4-K3-K0 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K3-K1: 1 steps
lem-F4-K3-K1 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K3-K2: 1 steps
lem-F4-K3-K2 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K3-K3: 1 steps
lem-F4-K3-K3 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D052 where

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
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-sym-ab-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-box-tQ-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D031 using (lem-sym-bc-at122441 ; lem-tP-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D032 using (lem-box-cP-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D033 using (lem-box-tQ-at14213243 ; lem-cQ-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CSd14-TOFF023 ; lem-comm-CX23-CCZ014 ; lem-comm-TOFF014-CSd23)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CZ14-TOFF023)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-comm-CS14-TOFF023)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-comm-CZ23-TOFF014)
-- tP @14213243: 7 steps
lem-tP-at14213243 : Complete 4 → ⟪ (Toff014 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ []) ⟫ʷ
lem-tP-at14213243 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Toff023 ∷ []) (Toff023 ∷ Toff014 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (pw2 c4 (Toff014 ∷ []) (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (lw4 c4 (Toff023 ∷ []) (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ CCZ014 ∷ []) (lem-cQ-at14213243 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff023 ∷ []) (lw4 c4 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (Toff023 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff014 ∷ []) (pw2 c4 (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (Toff014 ∷ []) tt tt Eq.refl) ▸ done


-- P-box @14213243: 8 steps
lem-P-box-at14213243 : Complete 4 → ⟪ (Toff023 ∷ Bx0-4123 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-P-box-at14213243 c4 = run b0
  where
  b0 : Chain (Toff023 ∷ Bx0-4123 ∷ Toff023 ∷ []) (Bx0-4123 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at14213243 c4) ▸
       at 0 2 (Toff014 ∷ Toff023 ∷ []) (sym (lem-tP-at14213243 c4)) ▸
       at 1 2 (CCZ023 ∷ CZ23 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CCZ023 ∷ []) (CCZ023 ∷ CZ23 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff014 ∷ Toff023 ∷ []) (sym (lem-tP-at14213243 c4)) ▸
       at 4 3 (CCZ023 ∷ CZ23 ∷ []) (lw4 c4 (Toff023 ∷ CCZ023 ∷ Toff023 ∷ []) (CCZ023 ∷ CZ23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff014 ∷ CZ23 ∷ []) (lem-comm-CZ23-TOFF014 c4) ▸
       at 3 3 (CCZ023 ∷ []) (lw4 c4 (CZ23 ∷ CCZ023 ∷ CZ23 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-4123 ∷ []) (sym (lem-box-tQ-at14213243 c4)) ▸ done


-- VPQ @14213243: 14 steps
lem-VPQ-at14213243 : Complete 4 → ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ
lem-VPQ-at14213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (CS23⁻ ∷ CS14⁻ ∷ S0 ∷ Toff023 ∷ Toff014 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (pw2 c4 (Toff014 ∷ CCZ014 ∷ []) (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (lw4 c4 (Toff023 ∷ CCZ023 ∷ []) (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑)) ▸
       at 2 2 (CS23⁻ ∷ Toff014 ∷ []) (lem-comm-TOFF014-CSd23 c4) ▸
       at 1 2 (CS23⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑)) ▸
       at 0 2 (CS23⁻ ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (S0⁻ ∷ S0 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at14213243 c4) ▸ done

  b1 : Chain (CS23⁻ ∷ CS14⁻ ∷ S0 ∷ Toff023 ∷ Toff014 ∷ S0⁻ ∷ []) (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (lw4 c4 [] (S0⁻ ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ CS14⁻ ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))) ▸
       at 2 2 (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 c4) ▸
       at 3 2 (S0⁻ ∷ CS14⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))) ▸
       at 0 4 (Toff023 ∷ CCZ023 ∷ []) (lw4 c4 (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (Toff023 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff014 ∷ CCZ014 ∷ []) (pw2 c4 (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (Toff014 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @14213243: 3 steps
lem-QVQ-at14213243 : Complete 4 → ⟪ (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-QVQ-at14213243 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ [])
  b0 = at 0 0 (Toff023 ∷ Toff023 ∷ []) (lw4 c4 [] (Toff023 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at14213243 c4)) ▸
       at 4 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @14213243: 12 steps
lem-box-cP-at14213243 : Complete 4 → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-box-cP-at14213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4123 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (pw1 c4 (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (pw1 c4 (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-QVQ-at14213243 c4) ▸
       at 1 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at14213243 c4) ▸
       at 2 2 [] (pw2 c4 (Toff014 ∷ Toff014 ∷ []) [] tt tt Eq.refl) ▸ done


-- pairs @14213243: 4 steps
lem-pairs-at14213243 : Complete 4 → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-pairs-at14213243 c4 = run b0
  where
  b0 : Chain (Bx0-4123 ∷ []) (Bx0-2341 ∷ [])
  b0 = at 0 1 (Toff023 ∷ Bx0-4123 ∷ Toff023 ∷ []) (sym (lem-P-box-at14213243 c4)) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at14213243 c4) ▸
       at 4 2 [] (lw4 c4 (Toff023 ∷ Toff023 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx0-2341 ∷ []) (sym (lem-box-tQ-at12233441 c4)) ▸ done


-- CXbc-box @12233441: 17 steps
lem-CXbc-box-at12233441 : Complete 4 → ⟪ (CX34 ∷ Bx0-2341 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at12233441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX34 ∷ Bx0-2341 ∷ CX34 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CX34 ∷ CCZ013 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CCZ014 ∷ CX23 ∷ CS12 ∷ CX34 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at12233441 c4) ▸
       at 0 2 (Toff023 ∷ CX34 ∷ []) (pw1 c4 (CX34 ∷ Toff023 ∷ []) (Toff023 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ CX34 ∷ CCZ013 ∷ []) (pw2 c4 (CX34 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX34 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ CCZ013 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ013 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ CX34 ∷ []) (pw1 c4 (CX34 ∷ Toff023 ∷ []) (Toff023 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CX34 ∷ CCZ013 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CCZ014 ∷ CX23 ∷ CS12 ∷ CX34 ∷ []) (Bx0-2341 ∷ CX34 ∷ CCZ123 ∷ CX34 ∷ [])
  b1 = at 7 2 (CCZ014 ∷ CS13⁻ ∷ []) (pw2 c4 (CS13⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 5 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ123 ∷ []) (lw4 c4 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CX34 ∷ CCZ013 ∷ []) (pw2 c4 (CX34 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX34 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX34 ∷ []) (pw2 c4 (CX34 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX34 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-2341 ∷ []) (sym (lem-box-tQ-at12233441 c4)) ▸ done

  b2 : Chain (Bx0-2341 ∷ CX34 ∷ CCZ123 ∷ CX34 ∷ []) (Bx0-2341 ∷ CCZ123 ∷ [])
  b2 = at 1 3 (CCZ123 ∷ []) (lw0 c4 (CX34 ∷ CCZ123 ∷ CX34 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @12233441: 18 steps
lem-CXcb-box-at12233441 : Complete 4 → ⟪ (CX43 ∷ Bx0-2341 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at12233441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX43 ∷ Bx0-2341 ∷ CX43 ∷ []) (Toff023 ∷ CCZ014 ∷ CX43 ∷ Toff024 ∷ CS14 ∷ CX24 ∷ Toff023 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ CCZ014 ∷ CX43 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at12233441 c4) ▸
       at 0 2 (Toff023 ∷ CX43 ∷ Toff024 ∷ []) (pw1 c4 (CX43 ∷ Toff023 ∷ []) (Toff023 ∷ CX43 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (pw3 c4 (Toff024 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ CX43 ∷ []) (pw2 c4 (CX43 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX43 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff023 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ Toff023 ∷ []) (Toff023 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff023 ∷ CX24 ∷ []) (pw1 c4 (CX24 ∷ Toff023 ∷ []) (Toff023 ∷ CX24 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 c4) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ CX43 ∷ Toff024 ∷ CS14 ∷ CX24 ∷ Toff023 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ CCZ014 ∷ CX43 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX43 ∷ CCZ124 ∷ CX43 ∷ [])
  b1 = at 5 2 (Toff023 ∷ CX24 ∷ []) (pw1 c4 (CX24 ∷ Toff023 ∷ []) (Toff023 ∷ CX24 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff023 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF023 c4) ▸
       at 5 5 (CCZ124 ∷ []) (lw0 c4 (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ Toff024 ∷ []) (pw1 c4 (Toff024 ∷ Toff023 ∷ []) (Toff023 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ CX43 ∷ Toff024 ∷ []) (pw1 c4 (CX43 ∷ Toff023 ∷ []) (Toff023 ∷ CX43 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX43 ∷ []) (pw1 c4 (CX43 ∷ Toff024 ∷ Toff024 ∷ []) (CX43 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CX43 ∷ []) (pw2 c4 (CX43 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX43 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX43 ∷ CCZ124 ∷ CX43 ∷ []) (Bx0-2341 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx0-2341 ∷ []) (sym (lem-box-tQ-at12233441 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (lw0 c4 (CX43 ∷ CCZ124 ∷ CX43 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @12233441: 11 steps
lem-SWbc-box-at12233441 : Complete 4 → ⟪ (Sw34 ∷ Bx0-2341 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-SWbc-box-at12233441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Bx0-2341 ∷ Sw34 ∷ []) (CX34 ∷ Bx0-2341 ∷ CX34 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CX34 ∷ CX43 ∷ CX34 ∷ []) (lw0 c4 (Sw34 ∷ []) (CX34 ∷ CX43 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX34 ∷ CX43 ∷ CX34 ∷ []) (lw0 c4 (Sw34 ∷ []) (CX34 ∷ CX43 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-CXbc-box-at12233441 c4) ▸
       at 3 2 (CX43 ∷ CCZ124 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CX43 ∷ []) (CX43 ∷ CCZ124 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-2341 ∷ CCZ124 ∷ []) (lem-CXcb-box-at12233441 c4) ▸
       at 4 2 (CX34 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CX34 ∷ []) (CX34 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX34 ∷ CCZ123 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CX34 ∷ []) (CX34 ∷ CCZ123 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX34 ∷ CCZ123 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CX34 ∷ []) (CX34 ∷ CCZ123 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX34 ∷ Bx0-2341 ∷ CX34 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ []) (Bx0-2341 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-CXbc-box-at12233441 c4) ▸
       at 1 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @12233441: 23 steps
lem-nat-SWbc-at12233441 : Complete 4 → ⟪ (Sw34 ∷ Bx0-2341 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-nat-SWbc-at12233441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw34 ∷ Bx0-2341 ∷ Sw34 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ Sw34 ∷ CCZ024 ∷ Bx0-21 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff024 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ Toff023 ∷ []) (Toff024 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ CCZ024 ∷ []) (CCZ023 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff203 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ Toff204 ∷ []) (Toff203 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 5 2 (Toff203 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ Toff204 ∷ []) (Toff203 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ Sw34 ∷ CCZ024 ∷ Bx0-21 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ Sw34 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Sw34 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ Sw34 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ CCZ024 ∷ []) (CCZ023 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 8 2 (Toff024 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ Toff023 ∷ []) (Toff024 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ CCZ024 ∷ []) (CCZ023 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff203 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ Toff204 ∷ []) (Toff203 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸ done

  b2 : Chain (CCZ024 ∷ Toff024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Sw34 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ Sw34 ∷ []) (Bx0-2431 ∷ [])
  b2 = at 13 2 (Toff203 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ Toff204 ∷ []) (Toff203 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ023 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ CCZ024 ∷ []) (CCZ023 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 16 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx2-031 ∷ []) (refl) ▸
       at 5 6 (Bx2-031 ∷ []) (refl) ▸
       at 0 6 (Bx0-2431 ∷ []) (refl) ▸ done


-- sym-bc @12233441: 2 steps
lem-sym-bc-at12233441 : Complete 4 → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-sym-bc-at12233441 c4 = run b0
  where
  b0 : Chain (Bx0-2341 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Bx0-2341 ∷ Sw34 ∷ []) (sym (lem-SWbc-box-at12233441 c4)) ▸
       at 0 3 (Bx0-2431 ∷ []) (lem-nat-SWbc-at12233441 c4) ▸ done


-- box-perm-3241 @243243: 3 steps
lem-box-perm-3241-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-3241-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 1 (Bx0-4123 ∷ []) (lem-sym-ab-at243243 c4) ▸
       at 0 1 (Bx0-2341 ∷ []) (lem-pairs-at14213243 c4) ▸
       at 0 1 (Bx0-2431 ∷ []) (lem-sym-bc-at12233441 c4) ▸ done


-- P-box @12233441: 8 steps
lem-P-box-at12233441 : Complete 4 → ⟪ (Toff014 ∷ Bx0-2341 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-P-box-at12233441 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Bx0-2341 ∷ Toff014 ∷ []) (Bx0-2341 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at12233441 c4) ▸
       at 0 2 (Toff023 ∷ Toff014 ∷ []) (sym (lem-tP-at12233441 c4)) ▸
       at 1 2 (CCZ014 ∷ CZ14 ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ CCZ014 ∷ []) (CCZ014 ∷ CZ14 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ Toff014 ∷ []) (sym (lem-tP-at12233441 c4)) ▸
       at 4 3 (CCZ014 ∷ CZ14 ∷ []) (pw2 c4 (Toff014 ∷ CCZ014 ∷ Toff014 ∷ []) (CCZ014 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF023 c4) ▸
       at 3 3 (CCZ014 ∷ []) (pw2 c4 (CZ14 ∷ CCZ014 ∷ CZ14 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-2341 ∷ []) (sym (lem-box-tQ-at12233441 c4)) ▸ done


-- pairs @12233441: 4 steps
lem-pairs-at12233441 : Complete 4 → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-pairs-at12233441 c4 = run b0
  where
  b0 : Chain (Bx0-2341 ∷ []) (Bx0-4123 ∷ [])
  b0 = at 0 1 (Toff014 ∷ Bx0-2341 ∷ Toff014 ∷ []) (sym (lem-P-box-at12233441 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸
       at 4 2 [] (pw2 c4 (Toff014 ∷ Toff014 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx0-4123 ∷ []) (sym (lem-box-tQ-at14213243 c4)) ▸ done


-- sym-ab @14213243: 18 steps
lem-sym-ab-at14213243 : Complete 4 → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-sym-ab-at14213243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-4123 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (pw1 c4 (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-13 ∷ []) (refl) ▸
       at 7 1 (Bx0-13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ [])
  b1 = at 2 6 (Bx1-023 ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸
       at 5 6 (CCZ023 ∷ []) (pw1 c4 (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx0-13 ∷ []) (refl) ▸
       at 10 1 (Bx0-13 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (Bx0-1423 ∷ [])
  b2 = at 5 6 (Bx1-023 ∷ []) (refl) ▸
       at 0 6 (Bx0-1423 ∷ []) (refl) ▸ done


-- box-perm-4213 @122441: 3 steps
lem-box-perm-4213-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-4213-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 1 (Bx0-2341 ∷ []) (lem-sym-bc-at122441 c4) ▸
       at 0 1 (Bx0-4123 ∷ []) (lem-pairs-at12233441 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym-ab-at14213243 c4) ▸ done


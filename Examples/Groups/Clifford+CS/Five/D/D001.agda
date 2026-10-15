{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D001 where

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
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CSd12-TOFF034 ; lem-comm-CX12-CCZ034 ; lem-comm-CZ12-CCZ034 ; lem-comm-CZ12-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CX04-CCZ123 ; lem-comm-TOFF204-CSd13)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd04-TOFF213 ; lem-comm-CSd13-CCZ024 ; lem-comm-CZ04-CCZ123)
-- cQ: 7 steps
lem-cQ : Complete 4 → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 2 2 (CCZ034 ∷ CS02⁻ ∷ []) (pw1 c4 (CS02⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 0 2 (CCZ034 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ012 ∷ []) (lw4 c4 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- tP: 7 steps
lem-tP : Complete 4 → ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ
lem-tP c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Toff034 ∷ []) (Toff034 ∷ Toff012 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (pw1 c4 (Toff034 ∷ []) (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-cQ c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff034 ∷ []) (pw1 c4 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (Toff034 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸ done


-- VPQ: 14 steps
lem-VPQ : Complete 4 → ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (CS34⁻ ∷ CS12⁻ ∷ S0 ∷ Toff034 ∷ Toff012 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (lw4 c4 (Toff012 ∷ CCZ012 ∷ []) (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (pw1 c4 (Toff034 ∷ CCZ034 ∷ []) (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑ ↑)) ▸
       at 2 2 (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS)) ▸
       at 1 2 (CS34⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑ ↑)) ▸
       at 0 2 (CS34⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (CS • CS • CS)) ▸
       at 4 2 [] (lw4 c4 (S0⁻ ∷ S0 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP c4) ▸ done

  b1 : Chain (CS34⁻ ∷ CS12⁻ ∷ S0 ∷ Toff034 ∷ Toff012 ∷ S0⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (lw4 c4 [] (S0⁻ ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ CS12⁻ ∷ []) (sym (c₁ (S) (CS • CS • CS))) ▸
       at 2 2 (Toff034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF034 c4) ▸
       at 3 2 (S0⁻ ∷ CS12⁻ ∷ []) (sym (c₁ (S • S • S) (CS • CS • CS))) ▸
       at 0 4 (Toff034 ∷ CCZ034 ∷ []) (pw1 c4 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff012 ∷ CCZ012 ∷ []) (lw4 c4 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ: 3 steps
lem-QVQ : Complete 4 → ⟪ (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-QVQ c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ [])
  b0 = at 0 0 (Toff034 ∷ Toff034 ∷ []) (pw1 c4 [] (Toff034 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (sym (lem-VPQ c4)) ▸
       at 4 2 [] (pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-tQ: 13 steps
lem-box-tQ : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (pw2 c4 (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (pw2 c4 (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) (lw4 c4 (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-cQ c4) ▸
       at 2 4 (Toff012 ∷ []) (lw4 c4 (CCZ012 ∷ CZ12 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸ done


-- box-cP: 12 steps
lem-box-cP : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-box-cP c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (pw2 c4 (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (pw2 c4 (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-QVQ c4) ▸
       at 1 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP c4) ▸
       at 2 2 [] (lw4 c4 (Toff012 ∷ Toff012 ∷ []) [] tt tt Eq.refl) ▸ done


-- t-cP: 5 steps
lem-t-cP : Complete 4 → ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ Toff012 ∷ []) ⟫ʷ
lem-t-cP c4 = run b0
  where
  b0 : Chain (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ Toff012 ∷ [])
  b0 = at 0 2 (CCZ012 ∷ Toff012 ∷ CZ12 ∷ []) (lw4 c4 (Toff012 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff012 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff034 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF034 c4) ▸
       at 1 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP c4) ▸
       at 2 3 (CCZ012 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP c4) ▸ done


-- box2: 11 steps
lem-box2 : Complete 4 → ⟪ (Bx0-1234 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ [])
  b0 = at 0 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 4 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 4 0 (Toff012 ∷ Toff012 ∷ []) (lw4 c4 [] (Toff012 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ Toff012 ∷ []) (lem-t-cP c4) ▸
       at 5 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸
       at 5 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 4 2 [] (lw4 c4 (Toff012 ∷ Toff012 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 [] (pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) []
  b1 = at 2 2 [] (lw4 c4 (Toff012 ∷ Toff012 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 [] (pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Toff012 ∷ Toff012 ∷ []) [] tt tt Eq.refl) ▸ done


-- Xb-box: 18 steps
lem-Xb-box : Complete 4 → ⟪ (X2 ∷ Bx0-1234 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ134 ∷ []) ⟫ʷ
lem-Xb-box c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X2 ∷ Bx0-1234 ∷ X2 ∷ []) (CCZ012 ∷ Toff034 ∷ X2 ∷ CZ01 ∷ CS34 ∷ CX13 ∷ CCZ012 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff034 ∷ X2 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 0 2 (CCZ012 ∷ X2 ∷ CZ01 ∷ []) (lw4 c4 (X2 ∷ CCZ012 ∷ []) (CCZ012 ∷ X2 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff034 ∷ CZ01 ∷ CCZ134 ∷ []) (pw2 c4 (CZ01 ∷ Toff034 ∷ []) (Toff034 ∷ CZ01 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff034 ∷ X2 ∷ []) (pw1 c4 (X2 ∷ Toff034 ∷ []) (Toff034 ∷ X2 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ012 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ012 ∷ CX13 ∷ []) (lw4 c4 (CX13 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸ done

  b1 : Chain (CCZ012 ∷ Toff034 ∷ X2 ∷ CZ01 ∷ CS34 ∷ CX13 ∷ CCZ012 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff034 ∷ X2 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ X2 ∷ CCZ134 ∷ X2 ∷ [])
  b1 = at 5 2 (CCZ012 ∷ CX13 ∷ []) (lw4 c4 (CX13 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ134 ∷ []) (lw0 c4 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CZ01 ∷ []) (lw4 c4 (CZ01 ∷ CCZ012 ∷ []) (CCZ012 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ X2 ∷ CZ01 ∷ []) (lw4 c4 (X2 ∷ CCZ012 ∷ []) (CCZ012 ∷ X2 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (X2 ∷ []) (lw4 c4 (X2 ∷ CZ01 ∷ CZ01 ∷ []) (X2 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff034 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ X2 ∷ []) (pw1 c4 (X2 ∷ Toff034 ∷ []) (Toff034 ∷ X2 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ X2 ∷ CCZ134 ∷ X2 ∷ []) (Bx0-1234 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸
       at 1 3 (CCZ134 ∷ []) (lw0 c4 (X2 ∷ CCZ134 ∷ X2 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- cQ @0210243143: 7 steps
lem-cQ-at0210243143 : Complete 4 → ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at0210243143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 c4) ▸
       at 2 2 (CCZ123 ∷ CS24⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 c4) ▸
       at 0 2 (CCZ123 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ024 ∷ []) (pw1 c4 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸ done


-- tP @0210243143: 7 steps
lem-tP-at0210243143 : Complete 4 → ⟪ (Toff204 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ []) ⟫ʷ
lem-tP-at0210243143 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Toff213 ∷ []) (Toff213 ∷ Toff204 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (pw1 c4 (Toff204 ∷ []) (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) (lw4 c4 (Toff213 ∷ []) (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-cQ-at0210243143 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff213 ∷ []) (lw4 c4 (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) (Toff213 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff204 ∷ []) (pw1 c4 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (Toff204 ∷ []) tt tt Eq.refl) ▸ done


-- VPQ @0210243143: 14 steps
lem-VPQ-at0210243143 : Complete 4 → ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at0210243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (CS13⁻ ∷ CS04⁻ ∷ S2 ∷ Toff213 ∷ Toff204 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (pw1 c4 (Toff204 ∷ CCZ024 ∷ []) (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (lw4 c4 (Toff213 ∷ CCZ123 ∷ []) (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS13⁻ ∷ S2⁻ ∷ []) (lw4 c4 (S2⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS13⁻ ∷ Toff204 ∷ []) (lem-comm-TOFF204-CSd13 c4) ▸
       at 1 2 (CS13⁻ ∷ S2 ∷ []) (lw4 c4 (S2 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S2 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS13⁻ ∷ CS04⁻ ∷ []) (pw2 c4 (CS04⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (S2⁻ ∷ S2 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at0210243143 c4) ▸ done

  b1 : Chain (CS13⁻ ∷ CS04⁻ ∷ S2 ∷ Toff213 ∷ Toff204 ∷ S2⁻ ∷ []) (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (lw4 c4 [] (S2⁻ ∷ S2 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S2 ∷ CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ S2 ∷ []) (S2 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 c4) ▸
       at 3 2 (S2⁻ ∷ CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Toff213 ∷ CCZ123 ∷ []) (lw4 c4 (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (Toff213 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff204 ∷ CCZ024 ∷ []) (pw1 c4 (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (Toff204 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @0210243143: 3 steps
lem-QVQ-at0210243143 : Complete 4 → ⟪ (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-QVQ-at0210243143 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ [])
  b0 = at 0 0 (Toff213 ∷ Toff213 ∷ []) (lw4 c4 [] (Toff213 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (sym (lem-VPQ-at0210243143 c4)) ▸
       at 4 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @0210243143: 12 steps
lem-box-cP-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-box-cP-at0210243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0413 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (lw4 c4 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (lw4 c4 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-QVQ-at0210243143 c4) ▸
       at 1 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at0210243143 c4) ▸
       at 2 2 [] (pw1 c4 (Toff204 ∷ Toff204 ∷ []) [] tt tt Eq.refl) ▸ done


-- Xb-box @0210243143: 18 steps
lem-Xb-box-at0210243143 : Complete 4 → ⟪ (X4 ∷ Bx2-0413 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ013 ∷ []) ⟫ʷ
lem-Xb-box-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ []) (CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX01 ∷ CCZ024 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff213 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) (lw4 c4 (CZ02 ∷ Toff213 ∷ []) (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 4 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX01 ∷ CCZ024 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff213 ∷ X4 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CCZ013 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ024 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 c4) ▸
       at 5 5 (CCZ013 ∷ []) (lw4 c4 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CZ02 ∷ []) (pw3 c4 (CZ02 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (X4 ∷ []) (lw3 c4 (X4 ∷ CZ02 ∷ CZ02 ∷ []) (X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff213 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸ done

  b2 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (pw2 c4 (X4 ∷ CCZ013 ∷ X4 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @0210243143: 13 steps
lem-box-tQ-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at0210243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0413 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (lw4 c4 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (lw4 c4 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff204 ∷ CCZ024 ∷ CZ04 ∷ []) (pw1 c4 (CCZ024 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ024 ∷ CZ04 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ123 ∷ CZ04 ∷ []) (lem-comm-CZ04-CCZ123 c4) ▸
       at 1 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-cQ-at0210243143 c4) ▸
       at 2 4 (Toff204 ∷ []) (pw1 c4 (CCZ024 ∷ CZ04 ∷ Toff204 ∷ CCZ024 ∷ []) (Toff204 ∷ []) tt tt Eq.refl) ▸ done


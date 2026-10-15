{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D007 where

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
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-box-tQ-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-sym-ab)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym-bc-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-tQ-at13243241 ; lem-pairs-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-P-box-at122331 ; lem-tP-at122331)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CSd12-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-CZ13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-comm-CS12-TOFF034 ; lem-comm-CSd23-TOFF014 ; lem-comm-TOFF023-CSd14)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-comm-CX31-CCZ024 ; lem-comm-SWAP24-BOX⟨0·31⟩)
-- VPQ @122331: 14 steps
lem-VPQ-at122331 : Complete 4 → ⟪ (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at122331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (CS14⁻ ∷ CS23⁻ ∷ S0 ∷ Toff014 ∷ Toff023 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (lw4 c4 (Toff023 ∷ CCZ023 ∷ []) (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (pw2 c4 (Toff014 ∷ CCZ014 ∷ []) (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS14⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)) ▸
       at 2 2 (CS14⁻ ∷ Toff023 ∷ []) (lem-comm-TOFF023-CSd14 c4) ▸
       at 1 2 (CS14⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)) ▸
       at 0 2 (CS14⁻ ∷ CS23⁻ ∷ []) (lw0 c4 (CS23⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (S0⁻ ∷ S0 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff014 ∷ Toff023 ∷ []) (lem-tP-at122331 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS23⁻ ∷ S0 ∷ Toff014 ∷ Toff023 ∷ S0⁻ ∷ []) (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (lw4 c4 [] (S0⁻ ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ CS23⁻ ∷ []) (sym (c₁ (S) ((CS • CS • CS) ↑))) ▸
       at 2 2 (Toff014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF014 c4) ▸
       at 3 2 (S0⁻ ∷ CS23⁻ ∷ []) (sym (c₁ (S • S • S) ((CS • CS • CS) ↑))) ▸
       at 0 4 (Toff014 ∷ CCZ014 ∷ []) (pw2 c4 (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (Toff014 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff023 ∷ CCZ023 ∷ []) (lw4 c4 (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (Toff023 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @122331: 3 steps
lem-QVQ-at122331 : Complete 4 → ⟪ (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-QVQ-at122331 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ [])
  b0 = at 0 0 (Toff014 ∷ Toff014 ∷ []) (pw2 c4 [] (Toff014 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (sym (lem-VPQ-at122331 c4)) ▸
       at 4 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @122331: 12 steps
lem-box-cP-at122331 : Complete 4 → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-box-cP-at122331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2314 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (pw3 c4 (CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (pw3 c4 (CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-QVQ-at122331 c4) ▸
       at 1 2 (Toff014 ∷ Toff023 ∷ []) (lem-tP-at122331 c4) ▸
       at 2 2 [] (lw4 c4 (Toff023 ∷ Toff023 ∷ []) [] tt tt Eq.refl) ▸ done


-- pairs @122331: 4 steps
lem-pairs-at122331 : Complete 4 → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-pairs-at122331 c4 = run b0
  where
  b0 : Chain (Bx0-2314 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 1 (Toff014 ∷ Bx0-2314 ∷ Toff014 ∷ []) (sym (lem-P-box-at122331 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at122331 c4) ▸
       at 4 2 [] (pw2 c4 (Toff014 ∷ Toff014 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-tQ-at243243 c4)) ▸ done


-- box-perm-1423: 3 steps
lem-box-perm-1423 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-1423 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym-bc-at1221 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-pairs-at122331 c4) ▸ done


-- sym-ab @13243241: 18 steps
lem-sym-ab-at13243241 : Complete 4 → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-sym-ab-at13243241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-3421 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (lw4 c4 (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (pw3 c4 (CCZ012 ∷ []) (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-41 ∷ []) (refl) ▸
       at 7 1 (Bx0-41 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ [])
  b1 = at 2 6 (Bx4-021 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸
       at 5 6 (CCZ012 ∷ []) (lw4 c4 (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (pw3 c4 (CCZ012 ∷ []) (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx0-41 ∷ []) (refl) ▸
       at 10 1 (Bx0-41 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (Bx0-4321 ∷ [])
  b2 = at 5 6 (Bx4-021 ∷ []) (refl) ▸
       at 0 6 (Bx0-4321 ∷ []) (refl) ▸ done


-- box-perm-4321: 3 steps
lem-box-perm-4321 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-box-perm-4321 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-4321 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-3421 ∷ []) (lem-pairs-at1221 c4) ▸
       at 0 1 (Bx0-4321 ∷ []) (lem-sym-ab-at13243241 c4) ▸ done


-- CXbc-box @13243241: 17 steps
lem-CXbc-box-at13243241 : Complete 4 → ⟪ (CX42 ∷ Bx0-3421 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at13243241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX42 ∷ Bx0-3421 ∷ CX42 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CX42 ∷ CCZ014 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CCZ012 ∷ CX34 ∷ CS13 ∷ CX42 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at13243241 c4) ▸
       at 0 2 (Toff034 ∷ CX42 ∷ []) (pw1 c4 (CX42 ∷ Toff034 ∷ []) (Toff034 ∷ CX42 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CX42 ∷ CCZ014 ∷ []) (pw3 c4 (CX42 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX42 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ CCZ014 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ014 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ014 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff034 ∷ CX42 ∷ []) (pw1 c4 (CX42 ∷ Toff034 ∷ []) (Toff034 ∷ CX42 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ012 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸ done

  b1 : Chain (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CX42 ∷ CCZ014 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CCZ012 ∷ CX34 ∷ CS13 ∷ CX42 ∷ []) (Bx0-3421 ∷ CX42 ∷ CCZ134 ∷ CX42 ∷ [])
  b1 = at 7 2 (CCZ012 ∷ CS14⁻ ∷ []) (pw3 c4 (CS14⁻ ∷ CCZ012 ∷ []) (CCZ012 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 5 2 (CCZ012 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ134 ∷ []) (lw0 c4 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CX42 ∷ CCZ014 ∷ []) (pw3 c4 (CX42 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX42 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX42 ∷ []) (pw3 c4 (CX42 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX42 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-3421 ∷ []) (sym (lem-box-tQ-at13243241 c4)) ▸ done

  b2 : Chain (Bx0-3421 ∷ CX42 ∷ CCZ134 ∷ CX42 ∷ []) (Bx0-3421 ∷ CCZ134 ∷ [])
  b2 = at 1 3 (CCZ134 ∷ []) (lw0 c4 (CX42 ∷ CCZ134 ∷ CX42 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @13243241: 18 steps
lem-CXcb-box-at13243241 : Complete 4 → ⟪ (CX24 ∷ Bx0-3421 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at13243241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX24 ∷ Bx0-3421 ∷ CX24 ∷ []) (Toff034 ∷ CCZ012 ∷ CX24 ∷ Toff023 ∷ CS12 ∷ CX32 ∷ Toff034 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ CCZ012 ∷ CX24 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at13243241 c4) ▸
       at 0 2 (Toff034 ∷ CX24 ∷ Toff023 ∷ []) (pw1 c4 (CX24 ∷ Toff034 ∷ []) (Toff034 ∷ CX24 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ Toff023 ∷ CCZ123 ∷ []) (lw4 c4 (Toff023 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CX24 ∷ []) (pw3 c4 (CX24 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX24 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff034 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ Toff034 ∷ []) (Toff034 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff034 ∷ CX32 ∷ []) (pw1 c4 (CX32 ∷ Toff034 ∷ []) (Toff034 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF034 c4) ▸ done

  b1 : Chain (Toff034 ∷ CCZ012 ∷ CX24 ∷ Toff023 ∷ CS12 ∷ CX32 ∷ Toff034 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ CCZ012 ∷ CX24 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX24 ∷ CCZ123 ∷ CX24 ∷ [])
  b1 = at 5 2 (Toff034 ∷ CX32 ∷ []) (pw1 c4 (CX32 ∷ Toff034 ∷ []) (Toff034 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff034 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF034 c4) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ Toff034 ∷ []) (Toff034 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff034 ∷ CX24 ∷ Toff023 ∷ []) (pw1 c4 (CX24 ∷ Toff034 ∷ []) (Toff034 ∷ CX24 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX24 ∷ []) (pw1 c4 (CX24 ∷ Toff023 ∷ Toff023 ∷ []) (CX24 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CX24 ∷ []) (pw3 c4 (CX24 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX24 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX24 ∷ CCZ123 ∷ CX24 ∷ []) (Bx0-3421 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-3421 ∷ []) (sym (lem-box-tQ-at13243241 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (lw0 c4 (CX24 ∷ CCZ123 ∷ CX24 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @13243241: 11 steps
lem-SWbc-box-at13243241 : Complete 4 → ⟪ (Sw24 ∷ Bx0-3421 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-SWbc-box-at13243241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw24 ∷ Bx0-3421 ∷ Sw24 ∷ []) (CX42 ∷ Bx0-3421 ∷ CX42 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX42 ∷ CX24 ∷ CX42 ∷ []) (lw0 c4 (Sw24 ∷ []) (CX42 ∷ CX24 ∷ CX42 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX42 ∷ CX24 ∷ CX42 ∷ []) (lw0 c4 (Sw24 ∷ []) (CX42 ∷ CX24 ∷ CX42 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx0-3421 ∷ CCZ134 ∷ []) (lem-CXbc-box-at13243241 c4) ▸
       at 3 2 (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CX24 ∷ []) (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-3421 ∷ CCZ123 ∷ []) (lem-CXcb-box-at13243241 c4) ▸
       at 4 2 (CX42 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CX42 ∷ []) (CX42 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CX42 ∷ []) (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CX42 ∷ []) (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX42 ∷ Bx0-3421 ∷ CX42 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ []) (Bx0-3421 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx0-3421 ∷ CCZ134 ∷ []) (lem-CXbc-box-at13243241 c4) ▸
       at 1 2 [] (lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @13243241: 23 steps
lem-nat-SWbc-at13243241 : Complete 4 → ⟪ (Sw24 ∷ Bx0-3421 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-nat-SWbc-at13243241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw24 ∷ Bx0-3421 ∷ Sw24 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ Sw24 ∷ CCZ023 ∷ Bx0-31 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ Sw24 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ CCZ034 ∷ []) (CCZ023 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ Toff034 ∷ []) (Toff023 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 2 2 (CCZ034 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ CCZ023 ∷ []) (CCZ034 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff304 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ Toff302 ∷ []) (Toff304 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ c4) ▸
       at 5 2 (Toff304 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ Toff302 ∷ []) (Toff304 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ Sw24 ∷ CCZ023 ∷ Bx0-31 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ Sw24 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ Toff023 ∷ CCZ023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Sw24 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ Sw24 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ CCZ023 ∷ []) (CCZ034 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ c4) ▸
       at 8 2 (Toff023 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ Toff034 ∷ []) (Toff023 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ023 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ CCZ034 ∷ []) (CCZ023 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 10 2 (CCZ034 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ CCZ023 ∷ []) (CCZ034 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff304 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ Toff302 ∷ []) (Toff304 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ c4) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ Toff023 ∷ CCZ023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Sw24 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ Sw24 ∷ []) (Bx0-3241 ∷ [])
  b2 = at 13 2 (Toff304 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ Toff302 ∷ []) (Toff304 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ034 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ CCZ023 ∷ []) (CCZ034 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ c4) ▸
       at 16 2 [] (lw0 c4 (Sw24 ∷ Sw24 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx3-041 ∷ []) (refl) ▸
       at 5 6 (Bx3-041 ∷ []) (refl) ▸
       at 0 6 (Bx0-3241 ∷ []) (refl) ▸ done


-- sym-bc @13243241: 2 steps
lem-sym-bc-at13243241 : Complete 4 → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-sym-bc-at13243241 c4 = run b0
  where
  b0 : Chain (Bx0-3421 ∷ []) (Bx0-3241 ∷ [])
  b0 = at 0 1 (Sw24 ∷ Bx0-3421 ∷ Sw24 ∷ []) (sym (lem-SWbc-box-at13243241 c4)) ▸
       at 0 3 (Bx0-3241 ∷ []) (lem-nat-SWbc-at13243241 c4) ▸ done


-- box-perm-3241: 3 steps
lem-box-perm-3241 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-box-perm-3241 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-3241 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-3421 ∷ []) (lem-pairs-at1221 c4) ▸
       at 0 1 (Bx0-3241 ∷ []) (lem-sym-bc-at13243241 c4) ▸ done


-- cQ @132132: 7 steps
lem-cQ-at132132 : Complete 4 → ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at132132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 c4) ▸
       at 2 2 (CCZ024 ∷ CS01⁻ ∷ []) (pw3 c4 (CS01⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 c4) ▸
       at 0 2 (CCZ024 ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ013 ∷ []) (lw4 c4 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @132132: 13 steps
lem-box-tQ-at132132 : Complete 4 → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at132132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3124 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (pw1 c4 (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (pw1 c4 (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff013 ∷ CCZ013 ∷ CZ13 ∷ []) (lw4 c4 (CCZ013 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ013 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 c4) ▸
       at 1 2 (CCZ024 ∷ CCZ013 ∷ []) (lem-cQ-at132132 c4) ▸
       at 2 4 (Toff013 ∷ []) (lw4 c4 (CCZ013 ∷ CZ13 ∷ Toff013 ∷ CCZ013 ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸ done


-- tP @132132: 7 steps
lem-tP-at132132 : Complete 4 → ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ
lem-tP-at132132 c4 = run b0
  where
  b0 : Chain (Toff013 ∷ Toff024 ∷ []) (Toff024 ∷ Toff013 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (pw1 c4 (Toff024 ∷ []) (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CCZ013 ∷ []) (lem-cQ-at132132 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff024 ∷ []) (pw1 c4 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (Toff024 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸ done


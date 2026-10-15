{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D036 where

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
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-box-tQ-at1441)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-box-cP-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D035 using (lem-SWbc-box-at243243 ; lem-nat-SWbc-at243243)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CZ12-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-CSd13-TOFF024)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-comm-CS13-TOFF024)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-CX42-CCZ013 ; lem-comm-TOFF034-CSd12)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-comm-SWAP23-BOX⟨0·41⟩)
-- sym-bc @243243: 2 steps
lem-sym-bc-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-sym-bc-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-1243 ∷ [])
  b0 = at 0 1 (Sw24 ∷ Bx0-1423 ∷ Sw24 ∷ []) (sym (lem-SWbc-box-at243243 c4)) ▸
       at 0 3 (Bx0-1243 ∷ []) (lem-nat-SWbc-at243243 c4) ▸ done


-- box-perm-1324 @243243: 1 steps
lem-box-perm-1324-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-box-perm-1324-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-1243 ∷ [])
  b0 = at 0 1 (Bx0-1243 ∷ []) (lem-sym-bc-at243243 c4) ▸ done


-- F4-K3-CS1: 19 steps
lem-F4-K3-CS1 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-CS1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CCZ012 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4) ▸
       at 3 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at3443 c4) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 1 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 0 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸ done

  b1 : Chain (CCZ012 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b1 = at 1 4 (Toff034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK43 ∷ X4 ∷ Toff034 ∷ []) (Toff034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 4 (Toff034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK43 ∷ X4 ∷ Toff034 ∷ []) (Toff034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-1243 ∷ []) (sym (lem-box-cP-at3443 c4)) ▸
       at 0 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1324-at243243 c4)) ▸
       at 1 7 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b2 = at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- sym-ab @122441: 18 steps
lem-sym-ab-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-sym-ab-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-2431 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (lw4 c4 (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) (pw2 c4 (CCZ013 ∷ []) (CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-41 ∷ []) (refl) ▸
       at 7 1 (Bx0-41 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ [])
  b1 = at 2 6 (Bx4-031 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸
       at 5 6 (CCZ013 ∷ []) (lw4 c4 (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) (pw2 c4 (CCZ013 ∷ []) (CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx0-41 ∷ []) (refl) ▸
       at 10 1 (Bx0-41 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (Bx0-4231 ∷ [])
  b2 = at 5 6 (Bx4-031 ∷ []) (refl) ▸
       at 0 6 (Bx0-4231 ∷ []) (refl) ▸ done


-- CXbc-box @1441: 17 steps
lem-CXbc-box-at1441 : Complete 4 → ⟪ (CX23 ∷ Bx0-4231 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at1441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX23 ∷ Bx0-4231 ∷ CX23 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CX23 ∷ CCZ012 ∷ CS12 ∷ CX42 ∷ CS12⁻ ∷ CCZ013 ∷ CX42 ∷ CS14 ∷ CX23 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at1441 c4) ▸
       at 0 2 (Toff024 ∷ CX23 ∷ []) (pw1 c4 (CX23 ∷ Toff024 ∷ []) (Toff024 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ CX23 ∷ CCZ012 ∷ []) (lw4 c4 (CX23 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX23 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff024 ∷ CCZ012 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ012 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ012 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff024 ∷ CX23 ∷ []) (pw1 c4 (CX23 ∷ Toff024 ∷ []) (Toff024 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ013 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 c4) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CX23 ∷ CCZ012 ∷ CS12 ∷ CX42 ∷ CS12⁻ ∷ CCZ013 ∷ CX42 ∷ CS14 ∷ CX23 ∷ []) (Bx0-4231 ∷ CX23 ∷ CCZ124 ∷ CX23 ∷ [])
  b1 = at 7 2 (CCZ013 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 c4) ▸
       at 5 2 (CCZ013 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ124 ∷ []) (lw0 c4 (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ CX23 ∷ CCZ012 ∷ []) (lw4 c4 (CX23 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX23 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX23 ∷ []) (lw4 c4 (CX23 ∷ CCZ012 ∷ CCZ012 ∷ []) (CX23 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-4231 ∷ []) (sym (lem-box-tQ-at1441 c4)) ▸ done

  b2 : Chain (Bx0-4231 ∷ CX23 ∷ CCZ124 ∷ CX23 ∷ []) (Bx0-4231 ∷ CCZ124 ∷ [])
  b2 = at 1 3 (CCZ124 ∷ []) (lw0 c4 (CX23 ∷ CCZ124 ∷ CX23 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @1441: 18 steps
lem-CXcb-box-at1441 : Complete 4 → ⟪ (CX32 ∷ Bx0-4231 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at1441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX32 ∷ Bx0-4231 ∷ CX32 ∷ []) (Toff024 ∷ CCZ013 ∷ CX32 ∷ Toff034 ∷ CS13 ∷ CX43 ∷ Toff024 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ CCZ013 ∷ CX32 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at1441 c4) ▸
       at 0 2 (Toff024 ∷ CX32 ∷ Toff034 ∷ []) (pw1 c4 (CX32 ∷ Toff024 ∷ []) (Toff024 ∷ CX32 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ013 ∷ Toff034 ∷ CCZ134 ∷ []) (pw2 c4 (Toff034 ∷ CCZ013 ∷ []) (CCZ013 ∷ Toff034 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ Toff024 ∷ []) (Toff024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff024 ∷ CX43 ∷ []) (pw1 c4 (CX43 ∷ Toff024 ∷ []) (Toff024 ∷ CX43 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF024 c4) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ CX32 ∷ Toff034 ∷ CS13 ∷ CX43 ∷ Toff024 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ CCZ013 ∷ CX32 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CX32 ∷ CCZ134 ∷ CX32 ∷ [])
  b1 = at 5 2 (Toff024 ∷ CX43 ∷ []) (pw1 c4 (CX43 ∷ Toff024 ∷ []) (Toff024 ∷ CX43 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff024 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF024 c4) ▸
       at 5 5 (CCZ134 ∷ []) (lw0 c4 (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff024 ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ Toff024 ∷ []) (Toff024 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff024 ∷ CX32 ∷ Toff034 ∷ []) (pw1 c4 (CX32 ∷ Toff024 ∷ []) (Toff024 ∷ CX32 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX32 ∷ []) (pw1 c4 (CX32 ∷ Toff034 ∷ Toff034 ∷ []) (CX32 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX32 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CX32 ∷ CCZ134 ∷ CX32 ∷ []) (Bx0-4231 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx0-4231 ∷ []) (sym (lem-box-tQ-at1441 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (lw0 c4 (CX32 ∷ CCZ134 ∷ CX32 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @1441: 11 steps
lem-SWbc-box-at1441 : Complete 4 → ⟪ (Sw23 ∷ Bx0-4231 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-SWbc-box-at1441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx0-4231 ∷ Sw23 ∷ []) (CX23 ∷ Bx0-4231 ∷ CX23 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (lw4 c4 (Sw23 ∷ []) (CX23 ∷ CX32 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (lw4 c4 (Sw23 ∷ []) (CX23 ∷ CX32 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx0-4231 ∷ CCZ124 ∷ []) (lem-CXbc-box-at1441 c4) ▸
       at 3 2 (CX32 ∷ CCZ134 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CX32 ∷ []) (CX32 ∷ CCZ134 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-4231 ∷ CCZ134 ∷ []) (lem-CXcb-box-at1441 c4) ▸
       at 4 2 (CX23 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CX23 ∷ []) (CX23 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX23 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CX23 ∷ []) (CX23 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX23 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CX23 ∷ []) (CX23 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX23 ∷ Bx0-4231 ∷ CX23 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ []) (Bx0-4231 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx0-4231 ∷ CCZ124 ∷ []) (lem-CXbc-box-at1441 c4) ▸
       at 1 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @1441: 23 steps
lem-nat-SWbc-at1441 : Complete 4 → ⟪ (Sw23 ∷ Bx0-4231 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-nat-SWbc-at1441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw23 ∷ Bx0-4231 ∷ Sw23 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ Sw23 ∷ CCZ034 ∷ Bx0-41 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (pw1 c4 (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff034 ∷ Sw23 ∷ []) (pw1 c4 (Sw23 ∷ Toff024 ∷ []) (Toff034 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw23 ∷ []) (pw1 c4 (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff402 ∷ Sw23 ∷ []) (pw1 c4 (Sw23 ∷ Toff403 ∷ []) (Toff402 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-41 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·41⟩ c4) ▸
       at 5 2 (Toff402 ∷ Sw23 ∷ []) (pw1 c4 (Sw23 ∷ Toff403 ∷ []) (Toff402 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ Sw23 ∷ CCZ034 ∷ Bx0-41 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ Sw23 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Sw23 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw23 ∷ []) (pw1 c4 (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx0-41 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·41⟩ c4) ▸
       at 8 2 (Toff034 ∷ Sw23 ∷ []) (pw1 c4 (Sw23 ∷ Toff024 ∷ []) (Toff034 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ034 ∷ Sw23 ∷ []) (pw1 c4 (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw23 ∷ []) (pw1 c4 (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff402 ∷ Sw23 ∷ []) (pw1 c4 (Sw23 ∷ Toff403 ∷ []) (Toff402 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx0-41 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·41⟩ c4) ▸ done

  b2 : Chain (CCZ034 ∷ Toff034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Sw23 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ Sw23 ∷ []) (Bx0-4321 ∷ [])
  b2 = at 13 2 (Toff402 ∷ Sw23 ∷ []) (pw1 c4 (Sw23 ∷ Toff403 ∷ []) (Toff402 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ024 ∷ Sw23 ∷ []) (pw1 c4 (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx0-41 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·41⟩ c4) ▸
       at 16 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx4-021 ∷ []) (refl) ▸
       at 5 6 (Bx4-021 ∷ []) (refl) ▸
       at 0 6 (Bx0-4321 ∷ []) (refl) ▸ done


-- sym-bc @1441: 2 steps
lem-sym-bc-at1441 : Complete 4 → ⟪ (Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-sym-bc-at1441 c4 = run b0
  where
  b0 : Chain (Bx0-4231 ∷ []) (Bx0-4321 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Bx0-4231 ∷ Sw23 ∷ []) (sym (lem-SWbc-box-at1441 c4)) ▸
       at 0 3 (Bx0-4321 ∷ []) (lem-nat-SWbc-at1441 c4) ▸ done


-- cQ @14233241: 7 steps
lem-cQ-at14233241 : Complete 4 → ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at14233241 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS03 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 2 2 (CCZ012 ∷ CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ CCZ012 ∷ []) (CCZ012 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 0 2 (CCZ012 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ034 ∷ []) (pw1 c4 (CS03 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @14233241: 13 steps
lem-box-tQ-at14233241 : Complete 4 → ⟪ (Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at14233241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4321 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (pw3 c4 (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (pw3 c4 (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff034 ∷ CCZ034 ∷ CZ34 ∷ []) (pw1 c4 (CCZ034 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ034 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at14233241 c4) ▸
       at 2 4 (Toff034 ∷ []) (pw1 c4 (CCZ034 ∷ CZ34 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ []) tt tt Eq.refl) ▸ done


-- tP @14233241: 7 steps
lem-tP-at14233241 : Complete 4 → ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ
lem-tP-at14233241 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Toff012 ∷ []) (Toff012 ∷ Toff034 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (pw1 c4 (Toff034 ∷ []) (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at14233241 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff034 ∷ []) (pw1 c4 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (Toff034 ∷ []) tt tt Eq.refl) ▸ done


-- P-box @14233241: 8 steps
lem-P-box-at14233241 : Complete 4 → ⟪ (Toff012 ∷ Bx0-4321 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-P-box-at14233241 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Bx0-4321 ∷ Toff012 ∷ []) (Bx0-4321 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at14233241 c4) ▸
       at 0 2 (Toff034 ∷ Toff012 ∷ []) (sym (lem-tP-at14233241 c4)) ▸
       at 1 2 (CCZ012 ∷ CZ12 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ CCZ012 ∷ []) (CCZ012 ∷ CZ12 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ Toff012 ∷ []) (sym (lem-tP-at14233241 c4)) ▸
       at 4 3 (CCZ012 ∷ CZ12 ∷ []) (lw4 c4 (Toff012 ∷ CCZ012 ∷ Toff012 ∷ []) (CCZ012 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff034 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF034 c4) ▸
       at 3 3 (CCZ012 ∷ []) (lw4 c4 (CZ12 ∷ CCZ012 ∷ CZ12 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-4321 ∷ []) (sym (lem-box-tQ-at14233241 c4)) ▸ done


-- VPQ @14233241: 14 steps
lem-VPQ-at14233241 : Complete 4 → ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at14233241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (CS12⁻ ∷ CS34⁻ ∷ S0 ∷ Toff012 ∷ Toff034 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (pw1 c4 (Toff034 ∷ CCZ034 ∷ []) (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (lw4 c4 (Toff012 ∷ CCZ012 ∷ []) (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS12⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (CS • CS • CS)) ▸
       at 2 2 (CS12⁻ ∷ Toff034 ∷ []) (lem-comm-TOFF034-CSd12 c4) ▸
       at 1 2 (CS12⁻ ∷ S0 ∷ []) (c₁ (S) (CS • CS • CS)) ▸
       at 0 2 (CS12⁻ ∷ CS34⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (CS • CS • CS))) ▸
       at 4 2 [] (lw4 c4 (S0⁻ ∷ S0 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ Toff034 ∷ []) (lem-tP-at14233241 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS34⁻ ∷ S0 ∷ Toff012 ∷ Toff034 ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (lw4 c4 [] (S0⁻ ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ CS34⁻ ∷ []) (sym (c₁ (S) ((CS • CS • CS) ↑ ↑))) ▸
       at 2 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸
       at 3 2 (S0⁻ ∷ CS34⁻ ∷ []) (sym (c₁ (S • S • S) ((CS • CS • CS) ↑ ↑))) ▸
       at 0 4 (Toff012 ∷ CCZ012 ∷ []) (lw4 c4 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff034 ∷ CCZ034 ∷ []) (pw1 c4 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @14233241: 3 steps
lem-QVQ-at14233241 : Complete 4 → ⟪ (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-QVQ-at14233241 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ [])
  b0 = at 0 0 (Toff012 ∷ Toff012 ∷ []) (lw4 c4 [] (Toff012 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (sym (lem-VPQ-at14233241 c4)) ▸
       at 4 2 [] (lw4 c4 (CCZ012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @14233241: 12 steps
lem-box-cP-at14233241 : Complete 4 → ⟪ (Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-box-cP-at14233241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4321 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (pw3 c4 (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (pw3 c4 (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-QVQ-at14233241 c4) ▸
       at 1 2 (Toff012 ∷ Toff034 ∷ []) (lem-tP-at14233241 c4) ▸
       at 2 2 [] (pw1 c4 (Toff034 ∷ Toff034 ∷ []) [] tt tt Eq.refl) ▸ done


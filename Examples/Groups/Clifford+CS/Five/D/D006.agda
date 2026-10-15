{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D006 where

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
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-box-tQ-at13243142 ; lem-sym-ab ; lem-sym-bc)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-pairs ; lem-sym-bc-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-P-box-at2332 ; lem-box-cP-at2332 ; lem-box-tQ-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CSd12-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CX23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CZ14-TOFF023)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-comm-CS12-TOFF034 ; lem-comm-CZ23-CCZ014 ; lem-comm-SWAP14-BOX⟨0·32⟩)
-- pairs @2332: 4 steps
lem-pairs-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-pairs-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ []) (Bx0-2413 ∷ [])
  b0 = at 0 1 (Toff024 ∷ Bx0-1324 ∷ Toff024 ∷ []) (sym (lem-P-box-at2332 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at2332 c4) ▸
       at 4 2 [] (pw1 c4 (Toff024 ∷ Toff024 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx0-2413 ∷ []) (sym (lem-box-tQ-at12243143 c4)) ▸ done


-- box-perm-2413: 2 steps
lem-box-perm-2413 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-box-perm-2413 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-2413 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym-bc c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-pairs-at2332 c4) ▸ done


-- sym-ab @13243142: 18 steps
lem-sym-ab-at13243142 : Complete 4 → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-sym-ab-at13243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-3412 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (lw4 c4 (CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) (pw3 c4 (CCZ012 ∷ []) (CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-42 ∷ []) (refl) ▸
       at 7 1 (Bx0-42 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ [])
  b1 = at 2 6 (Bx4-012 ∷ []) (refl) ▸
       at 5 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸
       at 5 6 (CCZ012 ∷ []) (lw4 c4 (CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) (pw3 c4 (CCZ012 ∷ []) (CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx0-42 ∷ []) (refl) ▸
       at 10 1 (Bx0-42 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (Bx0-4312 ∷ [])
  b2 = at 5 6 (Bx4-012 ∷ []) (refl) ▸
       at 0 6 (Bx0-4312 ∷ []) (refl) ▸ done


-- box-perm-4312: 2 steps
lem-box-perm-4312 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-box-perm-4312 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-4312 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-pairs c4) ▸
       at 0 1 (Bx0-4312 ∷ []) (lem-sym-ab-at13243142 c4) ▸ done


-- CXbc-box @13243142: 17 steps
lem-CXbc-box-at13243142 : Complete 4 → ⟪ (CX41 ∷ Bx0-3412 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXbc-box-at13243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx0-3412 ∷ CX41 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CX41 ∷ CCZ024 ∷ CS24 ∷ CX34 ∷ CS24⁻ ∷ CCZ012 ∷ CX34 ∷ CS23 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at13243142 c4) ▸
       at 0 2 (Toff034 ∷ CX41 ∷ []) (pw2 c4 (CX41 ∷ Toff034 ∷ []) (Toff034 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CX41 ∷ CCZ024 ∷ []) (pw3 c4 (CX41 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX41 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ CCZ024 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ024 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ024 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff034 ∷ CX41 ∷ []) (pw2 c4 (CX41 ∷ Toff034 ∷ []) (Toff034 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ012 ∷ CS23 ∷ []) (lw4 c4 (CS23 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸ done

  b1 : Chain (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CX41 ∷ CCZ024 ∷ CS24 ∷ CX34 ∷ CS24⁻ ∷ CCZ012 ∷ CX34 ∷ CS23 ∷ CX41 ∷ []) (Bx0-3412 ∷ CX41 ∷ CCZ234 ∷ CX41 ∷ [])
  b1 = at 7 2 (CCZ012 ∷ CS24⁻ ∷ []) (pw3 c4 (CS24⁻ ∷ CCZ012 ∷ []) (CCZ012 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 5 2 (CCZ012 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ234 ∷ []) (lw0 c4 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CX41 ∷ CCZ024 ∷ []) (pw3 c4 (CX41 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX41 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX41 ∷ []) (pw3 c4 (CX41 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX41 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-3412 ∷ []) (sym (lem-box-tQ-at13243142 c4)) ▸ done

  b2 : Chain (Bx0-3412 ∷ CX41 ∷ CCZ234 ∷ CX41 ∷ []) (Bx0-3412 ∷ CCZ234 ∷ [])
  b2 = at 1 3 (CCZ234 ∷ []) (lw0 c4 (CX41 ∷ CCZ234 ∷ CX41 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @13243142: 18 steps
lem-CXcb-box-at13243142 : Complete 4 → ⟪ (CX14 ∷ Bx0-3412 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at13243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx0-3412 ∷ CX14 ∷ []) (Toff034 ∷ CCZ012 ∷ CX14 ∷ Toff013 ∷ CS12 ∷ CX31 ∷ Toff034 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ CCZ012 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at13243142 c4) ▸
       at 0 2 (Toff034 ∷ CX14 ∷ Toff013 ∷ []) (pw2 c4 (CX14 ∷ Toff034 ∷ []) (Toff034 ∷ CX14 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ Toff013 ∷ CCZ123 ∷ []) (lw4 c4 (Toff013 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CX14 ∷ []) (pw3 c4 (CX14 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX14 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff034 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ Toff034 ∷ []) (Toff034 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff034 ∷ CX31 ∷ []) (pw2 c4 (CX31 ∷ Toff034 ∷ []) (Toff034 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF034 c4) ▸ done

  b1 : Chain (Toff034 ∷ CCZ012 ∷ CX14 ∷ Toff013 ∷ CS12 ∷ CX31 ∷ Toff034 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ CCZ012 ∷ CX14 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX14 ∷ CCZ123 ∷ CX14 ∷ [])
  b1 = at 5 2 (Toff034 ∷ CX31 ∷ []) (pw2 c4 (CX31 ∷ Toff034 ∷ []) (Toff034 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff034 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF034 c4) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ Toff034 ∷ []) (Toff034 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff034 ∷ CX14 ∷ Toff013 ∷ []) (pw2 c4 (CX14 ∷ Toff034 ∷ []) (Toff034 ∷ CX14 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX14 ∷ []) (pw2 c4 (CX14 ∷ Toff013 ∷ Toff013 ∷ []) (CX14 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CX14 ∷ []) (pw3 c4 (CX14 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX14 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX14 ∷ CCZ123 ∷ CX14 ∷ []) (Bx0-3412 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-3412 ∷ []) (sym (lem-box-tQ-at13243142 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (lw0 c4 (CX14 ∷ CCZ123 ∷ CX14 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @13243142: 11 steps
lem-SWbc-box-at13243142 : Complete 4 → ⟪ (Sw14 ∷ Bx0-3412 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-SWbc-box-at13243142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx0-3412 ∷ Sw14 ∷ []) (CX41 ∷ Bx0-3412 ∷ CX41 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (lw0 c4 (Sw14 ∷ []) (CX41 ∷ CX14 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (lw0 c4 (Sw14 ∷ []) (CX41 ∷ CX14 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx0-3412 ∷ CCZ234 ∷ []) (lem-CXbc-box-at13243142 c4) ▸
       at 3 2 (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CX14 ∷ []) (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-3412 ∷ CCZ123 ∷ []) (lem-CXcb-box-at13243142 c4) ▸
       at 4 2 (CX41 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CX41 ∷ []) (CX41 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CX41 ∷ []) (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CX41 ∷ []) (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX41 ∷ Bx0-3412 ∷ CX41 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ []) (Bx0-3412 ∷ [])
  b1 = at 3 5 (CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx0-3412 ∷ CCZ234 ∷ []) (lem-CXbc-box-at13243142 c4) ▸
       at 1 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @13243142: 23 steps
lem-nat-SWbc-at13243142 : Complete 4 → ⟪ (Sw14 ∷ Bx0-3412 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-nat-SWbc-at13243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx0-3412 ∷ Sw14 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ Sw14 ∷ CCZ013 ∷ Bx0-32 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ CCZ034 ∷ []) (CCZ013 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff013 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ Toff034 ∷ []) (Toff013 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 2 2 (CCZ034 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ CCZ013 ∷ []) (CCZ034 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff304 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ Toff301 ∷ []) (Toff304 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ c4) ▸
       at 5 2 (Toff304 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ Toff301 ∷ []) (Toff304 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ Sw14 ∷ CCZ013 ∷ Bx0-32 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ Sw14 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Sw14 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ CCZ013 ∷ []) (CCZ034 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ c4) ▸
       at 8 2 (Toff013 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ Toff034 ∷ []) (Toff013 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ013 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ CCZ034 ∷ []) (CCZ013 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 10 2 (CCZ034 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ CCZ013 ∷ []) (CCZ034 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff304 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ Toff301 ∷ []) (Toff304 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ c4) ▸ done

  b2 : Chain (CCZ013 ∷ Toff013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Sw14 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ Sw14 ∷ []) (Bx0-3142 ∷ [])
  b2 = at 13 2 (Toff304 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ Toff301 ∷ []) (Toff304 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ034 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ CCZ013 ∷ []) (CCZ034 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ c4) ▸
       at 16 2 [] (lw0 c4 (Sw14 ∷ Sw14 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx3-042 ∷ []) (refl) ▸
       at 5 6 (Bx3-042 ∷ []) (refl) ▸
       at 0 6 (Bx0-3142 ∷ []) (refl) ▸ done


-- sym-bc @13243142: 2 steps
lem-sym-bc-at13243142 : Complete 4 → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-sym-bc-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ []) (Bx0-3142 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx0-3412 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at13243142 c4)) ▸
       at 0 3 (Bx0-3142 ∷ []) (lem-nat-SWbc-at13243142 c4) ▸ done


-- box-perm-3142: 2 steps
lem-box-perm-3142 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-box-perm-3142 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-3142 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-pairs c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym-bc-at13243142 c4) ▸ done


-- sym-ab @122331: 18 steps
lem-sym-ab-at122331 : Complete 4 → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-sym-ab-at122331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-2314 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (pw3 c4 (CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-34 ∷ []) (refl) ▸
       at 7 1 (Bx0-34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ [])
  b1 = at 2 6 (Bx3-014 ∷ []) (refl) ▸
       at 5 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸
       at 5 6 (CCZ014 ∷ []) (pw3 c4 (CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx0-34 ∷ []) (refl) ▸
       at 10 1 (Bx0-34 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (Bx0-3214 ∷ [])
  b2 = at 5 6 (Bx3-014 ∷ []) (refl) ▸
       at 0 6 (Bx0-3214 ∷ []) (refl) ▸ done


-- box-perm-3214: 3 steps
lem-box-perm-3214 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-box-perm-3214 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-3214 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym-bc-at1221 c4) ▸
       at 0 1 (Bx0-3214 ∷ []) (lem-sym-ab-at122331 c4) ▸ done


-- cQ @122331: 7 steps
lem-cQ-at122331 : Complete 4 → ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at122331 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CS02 ∷ []) (pw3 c4 (CS02 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 2 2 (CCZ014 ∷ CS03⁻ ∷ []) (pw2 c4 (CS03⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 0 2 (CCZ014 ∷ CS03 ∷ []) (pw2 c4 (CS03 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ023 ∷ []) (lw4 c4 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @122331: 13 steps
lem-box-tQ-at122331 : Complete 4 → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-box-tQ-at122331 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (pw3 c4 (CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff023 ∷ CCZ023 ∷ CZ23 ∷ []) (lw4 c4 (CCZ023 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ023 ∷ CZ23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ014 ∷ CZ23 ∷ []) (lem-comm-CZ23-CCZ014 c4) ▸
       at 1 2 (CCZ014 ∷ CCZ023 ∷ []) (lem-cQ-at122331 c4) ▸
       at 2 4 (Toff023 ∷ []) (lw4 c4 (CCZ023 ∷ CZ23 ∷ Toff023 ∷ CCZ023 ∷ []) (Toff023 ∷ []) tt tt Eq.refl) ▸ done


-- tP @122331: 7 steps
lem-tP-at122331 : Complete 4 → ⟪ (Toff023 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff023 ∷ []) ⟫ʷ
lem-tP-at122331 c4 = run b0
  where
  b0 : Chain (Toff023 ∷ Toff014 ∷ []) (Toff014 ∷ Toff023 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (lw4 c4 (Toff023 ∷ []) (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (pw2 c4 (Toff014 ∷ []) (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ CCZ023 ∷ []) (lem-cQ-at122331 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff014 ∷ []) (pw2 c4 (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (Toff014 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff023 ∷ []) (lw4 c4 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (Toff023 ∷ []) tt tt Eq.refl) ▸ done


-- P-box @122331: 8 steps
lem-P-box-at122331 : Complete 4 → ⟪ (Toff014 ∷ Bx0-2314 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-P-box-at122331 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Bx0-2314 ∷ Toff014 ∷ []) (Bx0-2314 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at122331 c4) ▸
       at 0 2 (Toff023 ∷ Toff014 ∷ []) (sym (lem-tP-at122331 c4)) ▸
       at 1 2 (CCZ014 ∷ CZ14 ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ CCZ014 ∷ []) (CCZ014 ∷ CZ14 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ Toff014 ∷ []) (sym (lem-tP-at122331 c4)) ▸
       at 4 3 (CCZ014 ∷ CZ14 ∷ []) (pw2 c4 (Toff014 ∷ CCZ014 ∷ Toff014 ∷ []) (CCZ014 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF023 c4) ▸
       at 3 3 (CCZ014 ∷ []) (pw2 c4 (CZ14 ∷ CCZ014 ∷ CZ14 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-2314 ∷ []) (sym (lem-box-tQ-at122331 c4)) ▸ done


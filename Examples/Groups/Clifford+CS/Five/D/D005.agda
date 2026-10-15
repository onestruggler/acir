{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D005 where

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
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-sym-ab ; lem-sym-bc)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-P-box-at1221 ; lem-QVQ-at1221 ; lem-tP-at1221)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CX24-CCZ013 ; lem-comm-CZ24-CCZ013 ; lem-comm-CZ24-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-CSd13-TOFF024 ; lem-comm-CZ13-CCZ024 ; lem-comm-TOFF013-CSd24)
-- box-cP @1221: 12 steps
lem-box-cP-at1221 : Complete 4 → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-box-cP-at1221 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2134 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (pw1 c4 (CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (pw1 c4 (CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-QVQ-at1221 c4) ▸
       at 1 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP-at1221 c4) ▸
       at 2 2 [] (lw4 c4 (Toff012 ∷ Toff012 ∷ []) [] tt tt Eq.refl) ▸ done


-- cQ @13243241: 7 steps
lem-cQ-at13243241 : Complete 4 → ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at13243241 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 2 2 (CCZ012 ∷ CS04⁻ ∷ []) (pw3 c4 (CS04⁻ ∷ CCZ012 ∷ []) (CCZ012 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 0 2 (CCZ012 ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ034 ∷ []) (pw1 c4 (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @13243241: 13 steps
lem-box-tQ-at13243241 : Complete 4 → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at13243241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3421 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (lw4 c4 (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (lw4 c4 (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff034 ∷ CCZ034 ∷ CZ34 ∷ []) (pw1 c4 (CCZ034 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ034 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at13243241 c4) ▸
       at 2 4 (Toff034 ∷ []) (pw1 c4 (CCZ034 ∷ CZ34 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ []) tt tt Eq.refl) ▸ done


-- pairs @1221: 4 steps
lem-pairs-at1221 : Complete 4 → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-pairs-at1221 c4 = run b0
  where
  b0 : Chain (Bx0-2134 ∷ []) (Bx0-3421 ∷ [])
  b0 = at 0 1 (Toff034 ∷ Bx0-2134 ∷ Toff034 ∷ []) (sym (lem-P-box-at1221 c4)) ▸
       at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at1221 c4) ▸
       at 4 2 [] (pw1 c4 (Toff034 ∷ Toff034 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx0-3421 ∷ []) (sym (lem-box-tQ-at13243241 c4)) ▸ done


-- box-perm-3421: 2 steps
lem-box-perm-3421 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-box-perm-3421 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-3421 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-3421 ∷ []) (lem-pairs-at1221 c4) ▸ done


-- sym-ab @2332: 18 steps
lem-sym-ab-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-sym-ab-at2332 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-1324 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (pw3 c4 (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-34 ∷ []) (refl) ▸
       at 7 1 (Bx0-34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ [])
  b1 = at 2 6 (Bx3-024 ∷ []) (refl) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (pw3 c4 (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx0-34 ∷ []) (refl) ▸
       at 10 1 (Bx0-34 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (Bx0-3124 ∷ [])
  b2 = at 5 6 (Bx3-024 ∷ []) (refl) ▸
       at 0 6 (Bx0-3124 ∷ []) (refl) ▸ done


-- box-perm-3124: 2 steps
lem-box-perm-3124 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-box-perm-3124 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-3124 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym-bc c4) ▸
       at 0 1 (Bx0-3124 ∷ []) (lem-sym-ab-at2332 c4) ▸ done


-- cQ @2332: 7 steps
lem-cQ-at2332 : Complete 4 → ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at2332 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 2 2 (CCZ024 ∷ CS03⁻ ∷ []) (pw1 c4 (CS03⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 0 2 (CCZ024 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @2332: 13 steps
lem-box-tQ-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at2332 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1324 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (pw3 c4 (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (pw3 c4 (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff013 ∷ CCZ013 ∷ CZ13 ∷ []) (lw4 c4 (CCZ013 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ013 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 c4) ▸
       at 1 2 (CCZ024 ∷ CCZ013 ∷ []) (lem-cQ-at2332 c4) ▸
       at 2 4 (Toff013 ∷ []) (lw4 c4 (CCZ013 ∷ CZ13 ∷ Toff013 ∷ CCZ013 ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸ done


-- tP @2332: 7 steps
lem-tP-at2332 : Complete 4 → ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ
lem-tP-at2332 c4 = run b0
  where
  b0 : Chain (Toff013 ∷ Toff024 ∷ []) (Toff024 ∷ Toff013 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (pw1 c4 (Toff024 ∷ []) (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CCZ013 ∷ []) (lem-cQ-at2332 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff024 ∷ []) (pw1 c4 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (Toff024 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸ done


-- P-box @2332: 8 steps
lem-P-box-at2332 : Complete 4 → ⟪ (Toff024 ∷ Bx0-1324 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-P-box-at2332 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ Bx0-1324 ∷ Toff024 ∷ []) (Bx0-1324 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at2332 c4) ▸
       at 0 2 (Toff013 ∷ Toff024 ∷ []) (sym (lem-tP-at2332 c4)) ▸
       at 1 2 (CCZ024 ∷ CZ24 ∷ Toff024 ∷ []) (pw1 c4 (Toff024 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ24 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ Toff024 ∷ []) (sym (lem-tP-at2332 c4)) ▸
       at 4 3 (CCZ024 ∷ CZ24 ∷ []) (pw1 c4 (Toff024 ∷ CCZ024 ∷ Toff024 ∷ []) (CCZ024 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff013 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF013 c4) ▸
       at 3 3 (CCZ024 ∷ []) (pw1 c4 (CZ24 ∷ CCZ024 ∷ CZ24 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-1324 ∷ []) (sym (lem-box-tQ-at2332 c4)) ▸ done


-- VPQ @2332: 14 steps
lem-VPQ-at2332 : Complete 4 → ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ
lem-VPQ-at2332 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (CS24⁻ ∷ CS13⁻ ∷ S0 ∷ Toff024 ∷ Toff013 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (lw4 c4 (Toff013 ∷ CCZ013 ∷ []) (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (pw1 c4 (Toff024 ∷ CCZ024 ∷ []) (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS24⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)) ▸
       at 2 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 c4) ▸
       at 1 2 (CS24⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)) ▸
       at 0 2 (CS24⁻ ∷ CS13⁻ ∷ []) (lw0 c4 (CS13⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (S0⁻ ∷ S0 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff024 ∷ Toff013 ∷ []) (lem-tP-at2332 c4) ▸ done

  b1 : Chain (CS24⁻ ∷ CS13⁻ ∷ S0 ∷ Toff024 ∷ Toff013 ∷ S0⁻ ∷ []) (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (lw4 c4 [] (S0⁻ ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ CS13⁻ ∷ []) (sym (c₁ (S) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 2 2 (Toff024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF024 c4) ▸
       at 3 2 (S0⁻ ∷ CS13⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 0 4 (Toff024 ∷ CCZ024 ∷ []) (pw1 c4 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (Toff024 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff013 ∷ CCZ013 ∷ []) (lw4 c4 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (Toff013 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @2332: 3 steps
lem-QVQ-at2332 : Complete 4 → ⟪ (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-QVQ-at2332 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ [])
  b0 = at 0 0 (Toff024 ∷ Toff024 ∷ []) (pw1 c4 [] (Toff024 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at2332 c4)) ▸
       at 4 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @2332: 12 steps
lem-box-cP-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-box-cP-at2332 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1324 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (pw3 c4 (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (pw3 c4 (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-QVQ-at2332 c4) ▸
       at 1 2 (Toff024 ∷ Toff013 ∷ []) (lem-tP-at2332 c4) ▸
       at 2 2 [] (lw4 c4 (Toff013 ∷ Toff013 ∷ []) [] tt tt Eq.refl) ▸ done


-- cQ @12243143: 7 steps
lem-cQ-at12243143 : Complete 4 → ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at12243143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 c4) ▸
       at 2 2 (CCZ013 ∷ CS04⁻ ∷ []) (pw2 c4 (CS04⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 c4) ▸
       at 0 2 (CCZ013 ∷ CS04 ∷ []) (pw2 c4 (CS04 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ024 ∷ []) (pw1 c4 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @12243143: 13 steps
lem-box-tQ-at12243143 : Complete 4 → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at12243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2413 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ012 ∷ Toff201 ∷ CZ23 ∷ Toff201 ∷ CCZ012 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (lw4 c4 (CCZ012 ∷ Toff201 ∷ CZ23 ∷ Toff201 ∷ CCZ012 ∷ CZ23 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ012 ∷ Toff201 ∷ CZ23 ∷ Toff201 ∷ CCZ012 ∷ CZ23 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (lw4 c4 (CCZ012 ∷ Toff201 ∷ CZ23 ∷ Toff201 ∷ CCZ012 ∷ CZ23 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff024 ∷ CCZ024 ∷ CZ24 ∷ []) (pw1 c4 (CCZ024 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ024 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ013 ∷ CZ24 ∷ []) (lem-comm-CZ24-CCZ013 c4) ▸
       at 1 2 (CCZ013 ∷ CCZ024 ∷ []) (lem-cQ-at12243143 c4) ▸
       at 2 4 (Toff024 ∷ []) (pw1 c4 (CCZ024 ∷ CZ24 ∷ Toff024 ∷ CCZ024 ∷ []) (Toff024 ∷ []) tt tt Eq.refl) ▸ done


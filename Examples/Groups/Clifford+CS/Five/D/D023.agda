{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D023 where

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
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-box-cP-at03102132)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-CSdu-box-3-at043043 ; lem-F0-R)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-box-cP-at04203243 ; lem-box-perm-1324-at043043)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-CSu-box-3-at043043 ; lem-F0-B ; lem-SWbc-box-at0330 ; lem-box-perm-2314-at03102132 ; lem-box2-at043043)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-comm-SWAP02-BOX⟨3·14⟩ ; lem-comm-TOFF312-CS04)
-- nat-SWbc @0330: 23 steps
lem-nat-SWbc-at0330 : Complete 4 → ⟪ (Sw02 ∷ Bx3-1204 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-nat-SWbc-at0330 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw02 ∷ Bx3-1204 ∷ Sw02 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ Sw02 ∷ CCZ013 ∷ Bx3-14 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ Sw02 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ CCZ123 ∷ []) (CCZ013 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff301 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ Toff312 ∷ []) (Toff301 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (refl) ▸
       at 2 2 (CCZ123 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ CCZ013 ∷ []) (CCZ123 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff123 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ Toff103 ∷ []) (Toff123 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ c4) ▸
       at 5 2 (Toff123 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ Toff103 ∷ []) (Toff123 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ Sw02 ∷ CCZ013 ∷ Bx3-14 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ Sw02 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Sw02 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ Sw02 ∷ [])
  b1 = at 6 2 (CCZ123 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ CCZ013 ∷ []) (CCZ123 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ c4) ▸
       at 8 2 (Toff301 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ Toff312 ∷ []) (Toff301 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ013 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ CCZ123 ∷ []) (CCZ013 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (refl) ▸
       at 10 2 (CCZ123 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ CCZ013 ∷ []) (CCZ123 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff123 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ Toff103 ∷ []) (Toff123 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ c4) ▸ done

  b2 : Chain (CCZ013 ∷ Toff301 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Sw02 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ Sw02 ∷ []) (Bx3-1024 ∷ [])
  b2 = at 13 2 (Toff123 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ Toff103 ∷ []) (Toff123 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ123 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ CCZ013 ∷ []) (CCZ123 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ c4) ▸
       at 16 2 [] (lw4 c4 (Sw02 ∷ Sw02 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx1-324 ∷ []) (refl) ▸
       at 5 6 (Bx1-324 ∷ []) (refl) ▸
       at 0 6 (Bx3-1024 ∷ []) (refl) ▸ done


-- sym-bc @0330: 2 steps
lem-sym-bc-at0330 : Complete 4 → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-sym-bc-at0330 c4 = run b0
  where
  b0 : Chain (Bx3-1204 ∷ []) (Bx3-1024 ∷ [])
  b0 = at 0 1 (Sw02 ∷ Bx3-1204 ∷ Sw02 ∷ []) (sym (lem-SWbc-box-at0330 c4)) ▸
       at 0 3 (Bx3-1024 ∷ []) (lem-nat-SWbc-at0330 c4) ▸ done


-- sym-ab @032032: 18 steps
lem-sym-ab-at032032 : Complete 4 → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-sym-ab-at032032 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-1024 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (lw0 c4 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (pw1 c4 (CCZ234 ∷ []) (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx3-04 ∷ []) (refl) ▸
       at 7 1 (Bx3-04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ [])
  b1 = at 2 6 (Bx0-324 ∷ []) (refl) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ234 ∷ []) (lw0 c4 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (pw1 c4 (CCZ234 ∷ []) (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx3-04 ∷ []) (refl) ▸
       at 10 1 (Bx3-04 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (Bx3-0124 ∷ [])
  b2 = at 5 6 (Bx0-324 ∷ []) (refl) ▸
       at 0 6 (Bx3-0124 ∷ []) (refl) ▸ done


-- box-perm-3124 @0330: 2 steps
lem-box-perm-3124-at0330 : Complete 4 → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-3124-at0330 c4 = run b0
  where
  b0 : Chain (Bx3-1204 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 1 (Bx3-1024 ∷ []) (lem-sym-bc-at0330 c4) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-sym-ab-at032032 c4) ▸ done


-- CXuA-S: 44 steps
lem-CXuA-S : Complete 4 → ⟪ (CX34 ∷ Sb3-0-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-12-4 ∷ CX34 ∷ []) ⟫ʷ
lem-CXuA-S c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CX34 ∷ Sb3-0-12-4 ∷ []) (Bx3-1204 ∷ Bx4-1203 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ Bx4-1203 ∷ CS04⁻ ∷ CX34 ∷ [])
  b0 = at 1 1 (Bx3-0124 ∷ Toff412 ∷ Sb3-0-4-2 ∷ Toff412 ∷ Sb⁻3-0-4-2 ∷ []) (refl) ▸
       at 3 1 (CS04 ∷ []) (refl) ▸
       at 5 1 (CS04⁻ ∷ []) (refl) ▸
       at 1 1 (Bx3-1204 ∷ []) (lem-box-perm-2314-at03102132 c4) ▸
       at 2 0 (CX34 ∷ CX34 ∷ []) (lw0 c4 [] (CX34 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx3-1204 ∷ Bx4-1203 ∷ []) (lem-F0-B c4) ▸
       at 2 5 (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Bx4-1203 ∷ CX34 ∷ []) (lem-F0-R c4) ▸
       at 5 2 (Bx4-1203 ∷ CS04⁻ ∷ []) (lem-CSdu-box-3-at043043 c4) ▸ done

  b1 : Chain (Bx3-1204 ∷ Bx4-1203 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ Bx4-1203 ∷ CS04⁻ ∷ CX34 ∷ []) (Bx3-1204 ∷ Bx4-1203 ∷ Toff412 ∷ CS04 ∷ CCZ014 ∷ Toff412 ∷ CS12 ∷ Toff423 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ014 ∷ Toff423 ∷ CS04⁻ ∷ CX34 ∷ [])
  b1 = at 5 1 (Bx4-1023 ∷ []) (lem-box-perm-1324-at043043 c4) ▸
       at 5 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 4 2 (CCZ014 ∷ Toff412 ∷ CCZ012 ∷ []) (pw3 c4 (Toff412 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff412 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Toff423 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ Toff423 ∷ []) (Toff423 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 8 2 (Toff423 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸ done

  b2 : Chain (Bx3-1204 ∷ Bx4-1203 ∷ Toff412 ∷ CS04 ∷ CCZ014 ∷ Toff412 ∷ CS12 ∷ Toff423 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ014 ∷ Toff423 ∷ CS04⁻ ∷ CX34 ∷ []) (Bx3-1204 ∷ Bx4-1203 ∷ Toff412 ∷ Bx4-1203 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ CX34 ∷ [])
  b2 = at 6 2 (Toff423 ∷ CS12 ∷ []) (lw0 c4 (CS12 ∷ Toff423 ∷ []) (Toff423 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 7 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff423 ∷ Toff412 ∷ []) (lw0 c4 (Toff412 ∷ Toff423 ∷ []) (Toff423 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CCZ014 ∷ Toff412 ∷ []) (pw3 c4 (Toff412 ∷ CCZ012 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff423 ∷ Toff412 ∷ []) (lw0 c4 (Toff412 ∷ Toff423 ∷ []) (Toff423 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 4 1 (Bx4-1203 ∷ []) (sym (lem-box-perm-1324-at043043 c4)) ▸
       at 3 2 (Bx4-1203 ∷ CS04 ∷ []) (lem-CSu-box-3-at043043 c4) ▸ done

  b3 : Chain (Bx3-1204 ∷ Bx4-1203 ∷ Toff412 ∷ Bx4-1203 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ CX34 ∷ []) (Bx3-1204 ∷ Bx4-1203 ∷ CCZ014 ∷ Toff412 ∷ CS12 ∷ Toff423 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ014 ∷ Toff423 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ CX34 ∷ [])
  b3 = at 3 1 (Bx4-1023 ∷ []) (lem-box-perm-1324-at043043 c4) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 2 2 (CCZ014 ∷ Toff412 ∷ CCZ012 ∷ []) (pw3 c4 (Toff412 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff412 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff423 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ Toff423 ∷ []) (Toff423 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 6 2 (Toff423 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸ done

  b4 : Chain (Bx3-1204 ∷ Bx4-1203 ∷ CCZ014 ∷ Toff412 ∷ CS12 ∷ Toff423 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ014 ∷ Toff423 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ CX34 ∷ []) (Bx3-1204 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ CX34 ∷ [])
  b4 = at 4 2 (Toff423 ∷ CS12 ∷ []) (lw0 c4 (CS12 ∷ Toff423 ∷ []) (Toff423 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff423 ∷ Toff412 ∷ []) (lw0 c4 (Toff412 ∷ Toff423 ∷ []) (Toff423 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CCZ014 ∷ Toff412 ∷ []) (pw3 c4 (Toff412 ∷ CCZ012 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff423 ∷ Toff412 ∷ []) (lw0 c4 (Toff412 ∷ Toff423 ∷ []) (Toff423 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 2 1 (Bx4-1203 ∷ []) (sym (lem-box-perm-1324-at043043 c4)) ▸
       at 1 2 [] (lem-box2-at043043 c4) ▸ done

  b5 : Chain (Bx3-1204 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ CX34 ∷ []) (Sb3-0-12-4 ∷ CX34 ∷ [])
  b5 = at 0 1 (Bx3-0124 ∷ []) (lem-box-perm-3124-at0330 c4) ▸
       at 2 1 (Sb3-0-4-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻3-0-4-2 ∷ []) (refl) ▸
       at 0 5 (Sb3-0-12-4 ∷ []) (refl) ▸ done


-- CXu-box-4 @03102132: 15 steps
lem-CXu-box-4-at03102132 : Complete 4 → ⟪ (CX43 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ CX43 ∷ []) ⟫ʷ
lem-CXu-box-4-at03102132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX43 ∷ Bx3-0124 ∷ []) (CCZ013 ∷ CX43 ∷ Toff324 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ013 ∷ Toff324 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at03102132 c4) ▸
       at 0 2 (CCZ013 ∷ CX43 ∷ CCZ014 ∷ []) (pw2 c4 (CX43 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX43 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff324 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ Toff324 ∷ []) (Toff324 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Toff324 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Toff324 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ Toff324 ∷ []) (Toff324 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ013 ∷ CX43 ∷ Toff324 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ013 ∷ Toff324 ∷ []) (Bx3-0124 ∷ CX43 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (pw2 c4 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ CX43 ∷ []) (lw0 c4 (CX43 ∷ Toff324 ∷ []) (Toff324 ∷ CX43 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ013 ∷ CX43 ∷ CCZ014 ∷ []) (pw2 c4 (CX43 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX43 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX43 ∷ []) (pw2 c4 (CX43 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX43 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff324 ∷ CX43 ∷ []) (lw0 c4 (CX43 ∷ Toff324 ∷ []) (Toff324 ∷ CX43 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx3-0124 ∷ []) (sym (lem-box-cP-at03102132 c4)) ▸ done


-- CXAu-S: 12 steps
lem-CXAu-S : Complete 4 → ⟪ (CX43 ∷ Sb3-0-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-12-4 ∷ CX43 ∷ []) ⟫ʷ
lem-CXAu-S c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX43 ∷ Sb3-0-12-4 ∷ []) (Bx3-0124 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CX43 ∷ CS04⁻ ∷ [])
  b0 = at 1 1 (Bx3-0124 ∷ Toff412 ∷ Sb3-0-4-2 ∷ Toff412 ∷ Sb⁻3-0-4-2 ∷ []) (refl) ▸
       at 3 1 (CS04 ∷ []) (refl) ▸
       at 5 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (Bx3-0124 ∷ CX43 ∷ []) (lem-CXu-box-4-at03102132 c4) ▸
       at 1 2 (Toff412 ∷ CX43 ∷ Toff312 ∷ []) (lw0 c4 (CX43 ∷ Toff412 ∷ []) (Toff412 ∷ CX43 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CS04 c4) ▸
       at 2 2 (CS04 ∷ CX43 ∷ []) (pw1 c4 (CX43 ∷ CS04 ∷ []) (CS04 ∷ CX43 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Toff412 ∷ CX43 ∷ []) (lw0 c4 (CX43 ∷ Toff312 ∷ Toff412 ∷ []) (Toff412 ∷ CX43 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx3-0124 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CX43 ∷ CS04⁻ ∷ []) (Sb3-0-12-4 ∷ CX43 ∷ [])
  b1 = at 4 2 (CS04⁻ ∷ CX43 ∷ []) (pw1 c4 (CX43 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CX43 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb3-0-4-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻3-0-4-2 ∷ []) (refl) ▸
       at 0 5 (Sb3-0-12-4 ∷ []) (refl) ▸ done


-- SW-S: 5 steps
lem-SW-S : Complete 4 → ⟪ (Sw34 ∷ Sb3-0-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-12-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-SW-S c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb3-0-12-4 ∷ []) (Sb3-0-12-4 ∷ Sw34 ∷ [])
  b0 = at 0 1 (CX34 ∷ CX43 ∷ CX34 ∷ []) (lw0 c4 (Sw34 ∷ []) (CX34 ∷ CX43 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb3-0-12-4 ∷ CX34 ∷ []) (lem-CXuA-S c4) ▸
       at 1 2 (Sb3-0-12-4 ∷ CX43 ∷ []) (lem-CXAu-S c4) ▸
       at 0 2 (Sb3-0-12-4 ∷ CX34 ∷ []) (lem-CXuA-S c4) ▸
       at 1 3 (Sw34 ∷ []) (lw0 c4 (CX34 ∷ CX43 ∷ CX34 ∷ []) (Sw34 ∷ []) tt tt Eq.refl) ▸ done


-- nat-S: 31 steps
lem-nat-S : Complete 4 → ⟪ (Sw34 ∷ Sb3-0-12-4 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-12-3 ∷ []) ⟫ʷ
lem-nat-S c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sw34 ∷ Sb3-0-12-4 ∷ Sw34 ∷ []) (CCZ014 ∷ Toff401 ∷ Sw34 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx3-0124 ∷ Toff412 ∷ Sb3-0-4-2 ∷ Toff412 ∷ Sb⁻3-0-4-2 ∷ []) (refl) ▸
       at 3 1 (CS04 ∷ []) (refl) ▸
       at 5 1 (CS04⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (pw2 c4 (Sw34 ∷ CCZ013 ∷ []) (CCZ014 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff401 ∷ Sw34 ∷ []) (pw2 c4 (Sw34 ∷ Toff301 ∷ []) (Toff401 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 5 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ Sw34 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Sw34 ∷ []) (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Sw34 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Sw34 ∷ [])
  b1 = at 8 1 (CZ04 ∷ []) (refl) ▸
       at 2 7 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx4-03 ∷ []) (refl) ▸
       at 7 1 (Bx4-03 ∷ []) (refl) ▸
       at 2 6 (Bx0-423 ∷ []) (refl) ▸
       at 3 2 (Toff401 ∷ Sw34 ∷ []) (pw2 c4 (Sw34 ∷ Toff301 ∷ []) (Toff401 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (pw2 c4 (Sw34 ∷ CCZ013 ∷ []) (CCZ014 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Sw34 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Sw34 ∷ []) (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ Toff312 ∷ CS03 ∷ Sw34 ∷ Toff412 ∷ CS04⁻ ∷ Sw34 ∷ [])
  b2 = at 8 1 (CZ04 ∷ []) (refl) ▸
       at 11 1 (CZ04 ∷ []) (refl) ▸
       at 5 7 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx4-03 ∷ []) (refl) ▸
       at 10 1 (Bx4-03 ∷ []) (refl) ▸
       at 5 6 (Bx0-423 ∷ []) (refl) ▸
       at 6 2 (Toff312 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff412 ∷ []) (Toff312 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS03 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ CS04 ∷ []) (CS03 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ Toff312 ∷ CS03 ∷ Sw34 ∷ Toff412 ∷ CS04⁻ ∷ Sw34 ∷ []) (Sb4-0-12-3 ∷ [])
  b3 = at 8 2 (Toff312 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff412 ∷ []) (Toff312 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CS03⁻ ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ CS04⁻ ∷ []) (CS03⁻ ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 6 (Bx4-0123 ∷ []) (refl) ▸
       at 2 1 (Sb4-0-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-0-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb4-0-12-3 ∷ []) (refl) ▸ done


-- F0: 3 steps
lem-F0 : Complete 4 → ⟪ (Sb3-0-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-12-3 ∷ []) ⟫ʷ
lem-F0 c4 = run b0
  where
  b0 : Chain (Sb3-0-12-4 ∷ []) (Sb4-0-12-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb3-0-12-4 ∷ Sw34 ∷ []) (lem-SW-S c4) ▸
       at 0 3 (Sb4-0-12-3 ∷ []) (lem-nat-S c4) ▸ done


-- F4-I-I: 1 steps
lem-F4-I-I : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-I c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-I-S0: 1 steps
lem-F4-I-S0 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-I-S1: 1 steps
lem-F4-I-S1 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-I-S2: 1 steps
lem-F4-I-S2 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-I-S3: 1 steps
lem-F4-I-S3 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-I-K0: 1 steps
lem-F4-I-K0 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


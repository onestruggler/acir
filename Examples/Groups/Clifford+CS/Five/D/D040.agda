{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D040 where

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
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-box-tQ-at0310243142 ; lem-cQ-at0314203142)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-sym-ab-at0314203142)
open import Examples.Groups.Clifford+CS.Five.D.D030 using (lem-box-tQ-at0210233441 ; lem-box-tQ-at0214213043 ; lem-pairs-at0214213043)
open import Examples.Groups.Clifford+CS.Five.D.D031 using (lem-box-cP-at0210233441 ; lem-tP-at0210233441)
open import Examples.Groups.Clifford+CS.Five.D.D039 using (lem-sym-bc-at0314213042)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CX04-CCZ123)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CZ04-CCZ123)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-comm-CX40-CCZ123)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-comm-CS14-CCZ023 ; lem-comm-CSd14-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-comm-CSd03-TOFF214 ; lem-comm-TOFF203-CSd14)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-comm-CX30-CCZ124 ; lem-comm-CX30-TOFF214 ; lem-comm-CZ14-TOFF203)
-- box-perm-1324 @0314213042: 1 steps
lem-box-perm-1324-at0314213042 : Complete 4 → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-box-perm-1324-at0314213042 c4 = run b0
  where
  b0 : Chain (Bx3-4102 ∷ []) (Bx3-4012 ∷ [])
  b0 = at 0 1 (Bx3-4012 ∷ []) (lem-sym-bc-at0314213042 c4) ▸ done


-- box-perm-3124 @0314213042: 2 steps
lem-box-perm-3124-at0314213042 : Complete 4 → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-box-perm-3124-at0314213042 c4 = run b0
  where
  b0 : Chain (Bx3-4102 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 1 (Bx3-4012 ∷ []) (lem-sym-bc-at0314213042 c4) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-sym-ab-at0314203142 c4) ▸ done


-- sym-ab @0210233441: 18 steps
lem-sym-ab-at0210233441 : Complete 4 → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ []) ⟫ʷ
lem-sym-ab-at0210233441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-0341 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (pw3 c4 (CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx2-31 ∷ []) (refl) ▸
       at 7 1 (Bx2-31 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) (CCZ023 ∷ Toff203 ∷ Bx3-241 ∷ Toff203 ∷ CCZ023 ∷ CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ [])
  b1 = at 2 6 (Bx3-241 ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸
       at 5 6 (CCZ124 ∷ []) (pw3 c4 (CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx2-31 ∷ []) (refl) ▸
       at 10 1 (Bx2-31 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff203 ∷ Bx3-241 ∷ Toff203 ∷ CCZ023 ∷ CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) (Bx2-3041 ∷ [])
  b2 = at 5 6 (Bx3-241 ∷ []) (refl) ▸
       at 0 6 (Bx2-3041 ∷ []) (refl) ▸ done


-- box-perm-4312 @0214213043: 2 steps
lem-box-perm-4312-at0214213043 : Complete 4 → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ []) ⟫ʷ
lem-box-perm-4312-at0214213043 c4 = run b0
  where
  b0 : Chain (Bx2-4103 ∷ []) (Bx2-3041 ∷ [])
  b0 = at 0 1 (Bx2-0341 ∷ []) (lem-pairs-at0214213043 c4) ▸
       at 0 1 (Bx2-3041 ∷ []) (lem-sym-ab-at0210233441 c4) ▸ done


-- cQ @0213203441: 7 steps
lem-cQ-at0213203441 : Complete 4 → ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at0213203441 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ124 ∷ CS23 ∷ []) (lw0 c4 (CS23 ∷ CCZ124 ∷ []) (CCZ124 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 c4) ▸
       at 2 2 (CCZ124 ∷ CS02⁻ ∷ []) (pw3 c4 (CS02⁻ ∷ CCZ124 ∷ []) (CCZ124 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 c4) ▸
       at 0 2 (CCZ124 ∷ CS02 ∷ []) (pw3 c4 (CS02 ∷ CCZ124 ∷ []) (CCZ124 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸ done


-- tP @0213203441: 7 steps
lem-tP-at0213203441 : Complete 4 → ⟪ (Toff203 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ []) ⟫ʷ
lem-tP-at0213203441 c4 = run b0
  where
  b0 : Chain (Toff203 ∷ Toff214 ∷ []) (Toff214 ∷ Toff203 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (lw4 c4 (Toff203 ∷ []) (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (lw0 c4 (Toff214 ∷ []) (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ124 ∷ CCZ023 ∷ []) (lem-cQ-at0213203441 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff214 ∷ []) (lw0 c4 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff203 ∷ []) (lw4 c4 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) tt tt Eq.refl) ▸ done


-- VPQ @0213203441: 14 steps
lem-VPQ-at0213203441 : Complete 4 → ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at0213203441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (CS14⁻ ∷ CS03⁻ ∷ S2 ∷ Toff214 ∷ Toff203 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (lw4 c4 (Toff203 ∷ CCZ023 ∷ []) (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (lw0 c4 (Toff214 ∷ CCZ124 ∷ []) (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS14⁻ ∷ S2⁻ ∷ []) (lw0 c4 (S2⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS14⁻ ∷ Toff203 ∷ []) (lem-comm-TOFF203-CSd14 c4) ▸
       at 1 2 (CS14⁻ ∷ S2 ∷ []) (lw0 c4 (S2 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ S2 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS14⁻ ∷ CS03⁻ ∷ []) (pw2 c4 (CS03⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (S2⁻ ∷ S2 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff214 ∷ Toff203 ∷ []) (lem-tP-at0213203441 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS03⁻ ∷ S2 ∷ Toff214 ∷ Toff203 ∷ S2⁻ ∷ []) (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (lw4 c4 [] (S2⁻ ∷ S2 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S2 ∷ CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ S2 ∷ []) (S2 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff214 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF214 c4) ▸
       at 3 2 (S2⁻ ∷ CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Toff214 ∷ CCZ124 ∷ []) (lw0 c4 (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (Toff214 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff203 ∷ CCZ023 ∷ []) (lw4 c4 (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (Toff203 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @0213203441: 3 steps
lem-QVQ-at0213203441 : Complete 4 → ⟪ (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-QVQ-at0213203441 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ [])
  b0 = at 0 0 (Toff214 ∷ Toff214 ∷ []) (lw0 c4 [] (Toff214 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (sym (lem-VPQ-at0213203441 c4)) ▸
       at 4 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @0213203441: 12 steps
lem-box-cP-at0213203441 : Complete 4 → ⟪ (Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-box-cP-at0213203441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-3041 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff203 ∷ Bx3-241 ∷ Toff203 ∷ CCZ023 ∷ Bx3-241 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (lw0 c4 (CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (lw0 c4 (CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-QVQ-at0213203441 c4) ▸
       at 1 2 (Toff214 ∷ Toff203 ∷ []) (lem-tP-at0213203441 c4) ▸
       at 2 2 [] (lw4 c4 (Toff203 ∷ Toff203 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-box-4 @0310243142: 103 steps
lem-box-box-4-at0310243142 : Complete 4 → ⟪ (Bx3-0412 ∷ Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-box-box-4-at0310243142 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (Bx3-0412 ∷ Bx2-3041 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ023 ∷ Toff214 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CCZ023 ∷ CX34 ∷ CS13 ∷ CCZ123 ∷ Toff214 ∷ [])
  b0 = at 0 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243142 c4) ▸
       at 4 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at0213203441 c4) ▸
       at 3 2 (CCZ023 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ023 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ023 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ023 ∷ CX34 ∷ []) (pw1 c4 (CX34 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX34 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ023 ∷ Toff214 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CCZ023 ∷ CX34 ∷ CS13 ∷ CCZ123 ∷ Toff214 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ023 ∷ Toff304 ∷ CCZ024 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ123 ∷ [])
  b1 = at 7 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 c4) ▸
       at 6 2 (CCZ023 ∷ CX34 ∷ []) (pw1 c4 (CX34 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 c4) ▸
       at 6 5 (CCZ134 ∷ []) (lw0 c4 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (Toff214 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ134 ∷ CCZ123 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx2-3041 ∷ []) (sym (lem-box-cP-at0213203441 c4)) ▸
       at 3 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at0213203441 c4) ▸
       at 2 2 (CCZ023 ∷ Toff304 ∷ CCZ024 ∷ []) (pw1 c4 (Toff304 ∷ CCZ023 ∷ []) (CCZ023 ∷ Toff304 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff304 ∷ CCZ123 ∷ CCZ023 ∷ Toff304 ∷ CCZ024 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ023 ∷ K3 ∷ Toff214 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ CCZ014 ∷ CCZ024 ∷ CCZ023 ∷ Toff214 ∷ CCZ123 ∷ [])
  b2 = at 4 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ []) (pw1 c4 (Toff304 ∷ []) (K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff214 ∷ K3⁻ ∷ []) (lw0 c4 (K3⁻ ∷ Toff214 ∷ []) (Toff214 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff214 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ Toff214 ∷ []) (Toff214 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 c4) ▸
       at 6 2 (Toff214 ∷ CS04⁻ ∷ []) (pw3 c4 (CS04⁻ ∷ Toff214 ∷ []) (Toff214 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 c4) ▸
       at 4 2 (Toff214 ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ Toff214 ∷ []) (Toff214 ∷ CS04 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Toff304 ∷ CCZ123 ∷ CCZ023 ∷ K3 ∷ Toff214 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ CCZ014 ∷ CCZ024 ∷ CCZ023 ∷ Toff214 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ023 ∷ Toff214 ∷ Toff304 ∷ CS14 ∷ CCZ023 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ024 ∷ Toff214 ∷ CCZ123 ∷ [])
  b3 = at 3 2 (Toff214 ∷ K3 ∷ []) (lw0 c4 (K3 ∷ Toff214 ∷ []) (Toff214 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 4 7 (Toff304 ∷ []) (pw1 c4 (K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ []) (Toff304 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ023 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ023 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ023 ∷ CX04 ∷ []) (pw1 c4 (CX04 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX04 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 c4) ▸
       at 6 2 (CCZ023 ∷ CX04 ∷ []) (pw1 c4 (CX04 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX04 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Toff304 ∷ CCZ123 ∷ CCZ023 ∷ Toff214 ∷ Toff304 ∷ CS14 ∷ CCZ023 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ024 ∷ Toff214 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ Toff214 ∷ CS34 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ [])
  b4 = at 5 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 c4) ▸
       at 6 5 (CCZ014 ∷ []) (pw2 c4 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Toff304 ∷ CCZ024 ∷ []) (pw1 c4 (Toff304 ∷ CCZ023 ∷ []) (CCZ023 ∷ Toff304 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CCZ014 ∷ []) (pw3 c4 (CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff214 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ []) (pw1 c4 (Toff304 ∷ []) (K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff214 ∷ K3⁻ ∷ []) (lw0 c4 (K3⁻ ∷ Toff214 ∷ []) (Toff214 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Toff214 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ Toff214 ∷ []) (Toff214 ∷ CS34 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (Toff304 ∷ CCZ123 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ Toff214 ∷ CS34 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b5 = at 9 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 c4) ▸
       at 8 2 (Toff214 ∷ CS04⁻ ∷ []) (pw3 c4 (CS04⁻ ∷ Toff214 ∷ []) (Toff214 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 c4) ▸
       at 6 2 (Toff214 ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ Toff214 ∷ []) (Toff214 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff214 ∷ K3 ∷ []) (lw0 c4 (K3 ∷ Toff214 ∷ []) (Toff214 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (Toff304 ∷ []) (pw1 c4 (K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ []) (Toff304 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx2-3041 ∷ []) (sym (lem-box-cP-at0213203441 c4)) ▸
       at 2 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at0213203441 c4) ▸ done

  b6 : Chain (Toff304 ∷ CCZ123 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ023 ∷ Toff214 ∷ CS14 ∷ CCZ023 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ CCZ123 ∷ Toff214 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b6 = at 1 2 (CCZ023 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ023 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ023 ∷ CX34 ∷ []) (pw1 c4 (CX34 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 c4) ▸
       at 4 2 (CCZ023 ∷ CX34 ∷ []) (pw1 c4 (CX34 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX34 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (Toff304 ∷ CCZ023 ∷ Toff214 ∷ CS14 ∷ CCZ023 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ CCZ123 ∷ Toff214 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ023 ∷ K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ023 ∷ Toff214 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b7 = at 3 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 c4) ▸
       at 4 5 (CCZ134 ∷ []) (lw0 c4 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (Toff214 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ134 ∷ CCZ123 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Bx2-3041 ∷ []) (sym (lem-box-cP-at0213203441 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at0213203441 c4) ▸
       at 0 2 (CCZ023 ∷ Toff304 ∷ CCZ024 ∷ []) (pw1 c4 (Toff304 ∷ CCZ023 ∷ []) (CCZ023 ∷ Toff304 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ []) (pw1 c4 (Toff304 ∷ []) (K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (CCZ023 ∷ K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ023 ∷ Toff214 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ023 ∷ Toff214 ∷ Toff304 ∷ CCZ014 ∷ CCZ024 ∷ CCZ023 ∷ Toff214 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b8 = at 7 2 (Toff214 ∷ K3⁻ ∷ []) (lw0 c4 (K3⁻ ∷ Toff214 ∷ []) (Toff214 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff214 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ Toff214 ∷ []) (Toff214 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 c4) ▸
       at 4 2 (Toff214 ∷ CS04⁻ ∷ []) (pw3 c4 (CS04⁻ ∷ Toff214 ∷ []) (Toff214 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 c4) ▸
       at 2 2 (Toff214 ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ Toff214 ∷ []) (Toff214 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff214 ∷ K3 ∷ []) (lw0 c4 (K3 ∷ Toff214 ∷ []) (Toff214 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 2 7 (Toff304 ∷ []) (pw1 c4 (K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ []) (Toff304 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (CCZ023 ∷ Toff214 ∷ Toff304 ∷ CCZ014 ∷ CCZ024 ∷ CCZ023 ∷ Toff214 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ023 ∷ Toff214 ∷ Toff304 ∷ CCZ023 ∷ CCZ014 ∷ CCZ024 ∷ Toff214 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b9 = at 4 2 (CCZ023 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ023 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ023 ∷ CX04 ∷ []) (pw1 c4 (CX04 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX04 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 c4) ▸
       at 4 2 (CCZ023 ∷ CX04 ∷ []) (pw1 c4 (CX04 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX04 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 c4) ▸
       at 4 5 (CCZ014 ∷ []) (pw2 c4 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (CCZ023 ∷ Toff214 ∷ Toff304 ∷ CCZ023 ∷ CCZ014 ∷ CCZ024 ∷ Toff214 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K3 ∷ CS04 ∷ CX30 ∷ Toff214 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b10 = at 2 2 (CCZ023 ∷ Toff304 ∷ CCZ024 ∷ []) (pw1 c4 (Toff304 ∷ CCZ023 ∷ []) (CCZ023 ∷ Toff304 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CCZ014 ∷ []) (pw3 c4 (CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff214 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ []) (pw1 c4 (Toff304 ∷ []) (K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff214 ∷ K3⁻ ∷ []) (lw0 c4 (K3⁻ ∷ Toff214 ∷ []) (Toff214 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff214 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ Toff214 ∷ []) (Toff214 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 c4) ▸
       at 6 2 (Toff214 ∷ CS04⁻ ∷ []) (pw3 c4 (CS04⁻ ∷ Toff214 ∷ []) (Toff214 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K3 ∷ CS04 ∷ CX30 ∷ Toff214 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (Bx2-3041 ∷ Toff304 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CCZ123 ∷ CX04 ∷ CS01 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b11 = at 5 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 c4) ▸
       at 4 2 (Toff214 ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ Toff214 ∷ []) (Toff214 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff214 ∷ K3 ∷ []) (lw0 c4 (K3 ∷ Toff214 ∷ []) (Toff214 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 4 7 (Toff304 ∷ []) (pw1 c4 (K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ []) (Toff304 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-3041 ∷ []) (sym (lem-box-cP-at0213203441 c4)) ▸
       at 2 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ123 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 c4) ▸ done

  b12 : Chain (Bx2-3041 ∷ Toff304 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CCZ123 ∷ CX04 ∷ CS01 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (Bx2-3041 ∷ Bx3-0412 ∷ [])
  b12 = at 4 2 (CCZ123 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 c4) ▸
       at 2 2 (CCZ123 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 5 (CCZ014 ∷ []) (pw2 c4 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff304 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Bx3-0412 ∷ []) (sym (lem-box-tQ-at0310243142 c4)) ▸ done


-- sym-ab @0213203441: 18 steps
lem-sym-ab-at0213203441 : Complete 4 → ⟪ (Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-sym-ab-at0213203441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-3041 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ Toff203 ∷ CCZ023 ∷ Bx3-241 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff203 ∷ Bx3-241 ∷ Toff203 ∷ CCZ023 ∷ Bx3-241 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (lw0 c4 (CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (pw3 c4 (CCZ124 ∷ []) (CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx2-01 ∷ []) (refl) ▸
       at 7 1 (Bx2-01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ Toff203 ∷ CCZ023 ∷ Bx3-241 ∷ []) (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ [])
  b1 = at 2 6 (Bx0-241 ∷ []) (refl) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸
       at 5 6 (CCZ124 ∷ []) (lw0 c4 (CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (pw3 c4 (CCZ124 ∷ []) (CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx2-01 ∷ []) (refl) ▸
       at 10 1 (Bx2-01 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (Bx2-0341 ∷ [])
  b2 = at 5 6 (Bx0-241 ∷ []) (refl) ▸
       at 0 6 (Bx2-0341 ∷ []) (refl) ▸ done


-- P-box @0210233441: 8 steps
lem-P-box-at0210233441 : Complete 4 → ⟪ (Toff214 ∷ Bx2-0341 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-P-box-at0210233441 c4 = run b0
  where
  b0 : Chain (Toff214 ∷ Bx2-0341 ∷ Toff214 ∷ []) (Bx2-0341 ∷ [])
  b0 = at 1 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-box-tQ-at0210233441 c4) ▸
       at 0 2 (Toff203 ∷ Toff214 ∷ []) (sym (lem-tP-at0210233441 c4)) ▸
       at 1 2 (CCZ124 ∷ CZ14 ∷ Toff214 ∷ []) (lw0 c4 (Toff214 ∷ CCZ124 ∷ []) (CCZ124 ∷ CZ14 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff203 ∷ Toff214 ∷ []) (sym (lem-tP-at0210233441 c4)) ▸
       at 4 3 (CCZ124 ∷ CZ14 ∷ []) (lw0 c4 (Toff214 ∷ CCZ124 ∷ Toff214 ∷ []) (CCZ124 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff203 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF203 c4) ▸
       at 3 3 (CCZ124 ∷ []) (lw0 c4 (CZ14 ∷ CCZ124 ∷ CZ14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-0341 ∷ []) (sym (lem-box-tQ-at0210233441 c4)) ▸ done


-- pairs @0210233441: 4 steps
lem-pairs-at0210233441 : Complete 4 → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-pairs-at0210233441 c4 = run b0
  where
  b0 : Chain (Bx2-0341 ∷ []) (Bx2-4103 ∷ [])
  b0 = at 0 1 (Toff214 ∷ Bx2-0341 ∷ Toff214 ∷ []) (sym (lem-P-box-at0210233441 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at0210233441 c4) ▸
       at 4 2 [] (lw0 c4 (Toff214 ∷ Toff214 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx2-4103 ∷ []) (sym (lem-box-tQ-at0214213043 c4)) ▸ done


-- box-perm-3421 @0213203441: 2 steps
lem-box-perm-3421-at0213203441 : Complete 4 → ⟪ (Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-box-perm-3421-at0213203441 c4 = run b0
  where
  b0 : Chain (Bx2-3041 ∷ []) (Bx2-4103 ∷ [])
  b0 = at 0 1 (Bx2-0341 ∷ []) (lem-sym-ab-at0213203441 c4) ▸
       at 0 1 (Bx2-4103 ∷ []) (lem-pairs-at0210233441 c4) ▸ done


-- box-tQ @0314203142: 13 steps
lem-box-tQ-at0314203142 : Complete 4 → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at0314203142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4012 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (lw0 c4 (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (lw0 c4 (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff304 ∷ CCZ034 ∷ CZ04 ∷ []) (pw1 c4 (CCZ034 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ034 ∷ CZ04 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ123 ∷ CZ04 ∷ []) (lem-comm-CZ04-CCZ123 c4) ▸
       at 1 2 (CCZ123 ∷ CCZ034 ∷ []) (lem-cQ-at0314203142 c4) ▸
       at 2 4 (Toff304 ∷ []) (pw1 c4 (CCZ034 ∷ CZ04 ∷ Toff304 ∷ CCZ034 ∷ []) (Toff304 ∷ []) tt tt Eq.refl) ▸ done


-- CXbc-box @0314203142: 17 steps
lem-CXbc-box-at0314203142 : Complete 4 → ⟪ (CX01 ∷ Bx3-4012 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXbc-box-at0314203142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX01 ∷ Bx3-4012 ∷ CX01 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CX01 ∷ CCZ023 ∷ CS02 ∷ CX40 ∷ CS02⁻ ∷ CCZ123 ∷ CX40 ∷ CS24 ∷ CX01 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203142 c4) ▸
       at 0 2 (Toff304 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ Toff304 ∷ []) (Toff304 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ CX01 ∷ CCZ023 ∷ []) (lw4 c4 (CX01 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX01 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff304 ∷ CCZ023 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ023 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ023 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff304 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ Toff304 ∷ []) (Toff304 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (pw3 c4 (CCZ024 ∷ []) (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ123 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 c4) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CX01 ∷ CCZ023 ∷ CS02 ∷ CX40 ∷ CS02⁻ ∷ CCZ123 ∷ CX40 ∷ CS24 ∷ CX01 ∷ []) (Bx3-4012 ∷ CX01 ∷ CCZ024 ∷ CX01 ∷ [])
  b1 = at 7 2 (CCZ123 ∷ CS02⁻ ∷ []) (lw4 c4 (CS02⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 c4) ▸
       at 5 2 (CCZ123 ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ024 ∷ []) (pw3 c4 (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ CX01 ∷ CCZ023 ∷ []) (lw4 c4 (CX01 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX01 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX01 ∷ []) (lw4 c4 (CX01 ∷ CCZ023 ∷ CCZ023 ∷ []) (CX01 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx3-4012 ∷ []) (sym (lem-box-tQ-at0314203142 c4)) ▸ done

  b2 : Chain (Bx3-4012 ∷ CX01 ∷ CCZ024 ∷ CX01 ∷ []) (Bx3-4012 ∷ CCZ024 ∷ [])
  b2 = at 1 3 (CCZ024 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ CX01 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸ done


{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D020 where

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
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-cQ-at0410213243)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-box-tQ-at0330 ; lem-tP-at0330)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CX04-CCZ123)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CZ04-CCZ123)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-CS12-CCZ034 ; lem-comm-CSd12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-comm-CSd04-TOFF312 ; lem-comm-CSd12-TOFF304 ; lem-comm-CX40-CCZ123 ; lem-comm-CX40-TOFF312 ; lem-comm-CZ04-TOFF312 ; lem-comm-TOFF304-CSd12 ; lem-comm-TOFF312-CSd04)
-- P-box @0330: 8 steps
lem-P-box-at0330 : Complete 4 → ⟪ (Toff304 ∷ Bx3-1204 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-P-box-at0330 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ Bx3-1204 ∷ Toff304 ∷ []) (Bx3-1204 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at0330 c4) ▸
       at 0 2 (Toff312 ∷ Toff304 ∷ []) (sym (lem-tP-at0330 c4)) ▸
       at 1 2 (CCZ034 ∷ CZ04 ∷ Toff304 ∷ []) (pw1 c4 (Toff304 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ04 ∷ Toff304 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff312 ∷ Toff304 ∷ []) (sym (lem-tP-at0330 c4)) ▸
       at 4 3 (CCZ034 ∷ CZ04 ∷ []) (pw1 c4 (Toff304 ∷ CCZ034 ∷ Toff304 ∷ []) (CCZ034 ∷ CZ04 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff312 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF312 c4) ▸
       at 3 3 (CCZ034 ∷ []) (pw1 c4 (CZ04 ∷ CCZ034 ∷ CZ04 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx3-1204 ∷ []) (sym (lem-box-tQ-at0330 c4)) ▸ done


-- VPQ @0330: 14 steps
lem-VPQ-at0330 : Complete 4 → ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) ⟫ʷ
lem-VPQ-at0330 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) (CS04⁻ ∷ CS12⁻ ∷ S3 ∷ Toff304 ∷ Toff312 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) (lw4 c4 (Toff312 ∷ CCZ123 ∷ []) (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) (pw1 c4 (Toff304 ∷ CCZ034 ∷ []) (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS04⁻ ∷ S3⁻ ∷ []) (pw1 c4 (S3⁻ ∷ CS04⁻ ∷ []) (CS04⁻ ∷ S3⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS04⁻ ∷ Toff312 ∷ []) (lem-comm-TOFF312-CSd04 c4) ▸
       at 1 2 (CS04⁻ ∷ S3 ∷ []) (pw1 c4 (S3 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ S3 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS04⁻ ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (S3⁻ ∷ S3 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff304 ∷ Toff312 ∷ []) (lem-tP-at0330 c4) ▸ done

  b1 : Chain (CS04⁻ ∷ CS12⁻ ∷ S3 ∷ Toff304 ∷ Toff312 ∷ S3⁻ ∷ []) (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (lw4 c4 [] (S3⁻ ∷ S3 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S3 ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S)) ▸
       at 2 2 (Toff304 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF304 c4) ▸
       at 3 2 (S3⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S • S • S)) ▸
       at 0 4 (Toff304 ∷ CCZ034 ∷ []) (pw1 c4 (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) (Toff304 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff312 ∷ CCZ123 ∷ []) (lw4 c4 (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) (Toff312 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @0330: 3 steps
lem-QVQ-at0330 : Complete 4 → ⟪ (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ
lem-QVQ-at0330 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ [])
  b0 = at 0 0 (Toff304 ∷ Toff304 ∷ []) (pw1 c4 [] (Toff304 ∷ Toff304 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at0330 c4)) ▸
       at 4 2 [] (pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @0330: 12 steps
lem-box-cP-at0330 : Complete 4 → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ
lem-box-cP-at0330 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1204 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (pw2 c4 (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (pw2 c4 (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-QVQ-at0330 c4) ▸
       at 1 2 (Toff304 ∷ Toff312 ∷ []) (lem-tP-at0330 c4) ▸
       at 2 2 [] (lw4 c4 (Toff312 ∷ Toff312 ∷ []) [] tt tt Eq.refl) ▸ done


-- cQ @0310243142: 7 steps
lem-cQ-at0310243142 : Complete 4 → ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0310243142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 c4) ▸
       at 2 2 (CCZ123 ∷ CS34⁻ ∷ []) (lw0 c4 (CS34⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 c4) ▸
       at 0 2 (CCZ123 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ034 ∷ []) (pw1 c4 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @0310243142: 13 steps
lem-box-tQ-at0310243142 : Complete 4 → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at0310243142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0412 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (lw4 c4 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (lw4 c4 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff304 ∷ CCZ034 ∷ CZ04 ∷ []) (pw1 c4 (CCZ034 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ034 ∷ CZ04 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ123 ∷ CZ04 ∷ []) (lem-comm-CZ04-CCZ123 c4) ▸
       at 1 2 (CCZ123 ∷ CCZ034 ∷ []) (lem-cQ-at0310243142 c4) ▸
       at 2 4 (Toff304 ∷ []) (pw1 c4 (CCZ034 ∷ CZ04 ∷ Toff304 ∷ CCZ034 ∷ []) (Toff304 ∷ []) tt tt Eq.refl) ▸ done


-- pairs @0330: 4 steps
lem-pairs-at0330 : Complete 4 → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-pairs-at0330 c4 = run b0
  where
  b0 : Chain (Bx3-1204 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 1 (Toff304 ∷ Bx3-1204 ∷ Toff304 ∷ []) (sym (lem-P-box-at0330 c4)) ▸
       at 1 1 (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-box-cP-at0330 c4) ▸
       at 4 2 [] (pw1 c4 (Toff304 ∷ Toff304 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx3-0412 ∷ []) (sym (lem-box-tQ-at0310243142 c4)) ▸ done


-- sym-ab @0310243142: 18 steps
lem-sym-ab-at0310243142 : Complete 4 → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-sym-ab-at0310243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-0412 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (lw4 c4 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) (lw0 c4 (CCZ123 ∷ []) (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx3-42 ∷ []) (refl) ▸
       at 7 1 (Bx3-42 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ [])
  b1 = at 2 6 (Bx4-312 ∷ []) (refl) ▸
       at 5 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸
       at 5 6 (CCZ123 ∷ []) (lw4 c4 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) (lw0 c4 (CCZ123 ∷ []) (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx3-42 ∷ []) (refl) ▸
       at 10 1 (Bx3-42 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (Bx3-4012 ∷ [])
  b2 = at 5 6 (Bx4-312 ∷ []) (refl) ▸
       at 0 6 (Bx3-4012 ∷ []) (refl) ▸ done


-- box-perm-4312 @0330: 2 steps
lem-box-perm-4312-at0330 : Complete 4 → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-box-perm-4312-at0330 c4 = run b0
  where
  b0 : Chain (Bx3-1204 ∷ []) (Bx3-4012 ∷ [])
  b0 = at 0 1 (Bx3-0412 ∷ []) (lem-pairs-at0330 c4) ▸
       at 0 1 (Bx3-4012 ∷ []) (lem-sym-ab-at0310243142 c4) ▸ done


-- box-tQ @0410213243: 13 steps
lem-box-tQ-at0410213243 : Complete 4 → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at0410213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-0123 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (pw1 c4 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (pw1 c4 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff401 ∷ CCZ014 ∷ CZ01 ∷ []) (pw2 c4 (CCZ014 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ014 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ014 ∷ []) (lem-cQ-at0410213243 c4) ▸
       at 2 4 (Toff401 ∷ []) (pw2 c4 (CCZ014 ∷ CZ01 ∷ Toff401 ∷ CCZ014 ∷ []) (Toff401 ∷ []) tt tt Eq.refl) ▸ done


-- cQ @0314203142: 7 steps
lem-cQ-at0314203142 : Complete 4 → ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0314203142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 c4) ▸
       at 2 2 (CCZ123 ∷ CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 c4) ▸
       at 0 2 (CCZ123 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ034 ∷ []) (pw1 c4 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- tP @0314203142: 7 steps
lem-tP-at0314203142 : Complete 4 → ⟪ (Toff304 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ []) ⟫ʷ
lem-tP-at0314203142 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ Toff312 ∷ []) (Toff312 ∷ Toff304 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (pw1 c4 (Toff304 ∷ []) (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) (lw4 c4 (Toff312 ∷ []) (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ CCZ034 ∷ []) (lem-cQ-at0314203142 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff312 ∷ []) (lw4 c4 (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff304 ∷ []) (pw1 c4 (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (Toff304 ∷ []) tt tt Eq.refl) ▸ done


-- VPQ @0314203142: 14 steps
lem-VPQ-at0314203142 : Complete 4 → ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at0314203142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (CS12⁻ ∷ CS04⁻ ∷ S3 ∷ Toff312 ∷ Toff304 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) (pw1 c4 (Toff304 ∷ CCZ034 ∷ []) (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) (lw4 c4 (Toff312 ∷ CCZ123 ∷ []) (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS12⁻ ∷ S3⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (S • S • S))) ▸
       at 2 2 (CS12⁻ ∷ Toff304 ∷ []) (lem-comm-TOFF304-CSd12 c4) ▸
       at 1 2 (CS12⁻ ∷ S3 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (S))) ▸
       at 0 2 (CS12⁻ ∷ CS04⁻ ∷ []) (pw3 c4 (CS04⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (S3⁻ ∷ S3 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0314203142 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS04⁻ ∷ S3 ∷ Toff312 ∷ Toff304 ∷ S3⁻ ∷ []) (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (lw4 c4 [] (S3⁻ ∷ S3 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S3 ∷ CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ S3 ∷ []) (S3 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff312 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF312 c4) ▸
       at 3 2 (S3⁻ ∷ CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Toff312 ∷ CCZ123 ∷ []) (lw4 c4 (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) (Toff312 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff304 ∷ CCZ034 ∷ []) (pw1 c4 (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) (Toff304 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @0314203142: 3 steps
lem-QVQ-at0314203142 : Complete 4 → ⟪ (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-QVQ-at0314203142 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ [])
  b0 = at 0 0 (Toff312 ∷ Toff312 ∷ []) (lw4 c4 [] (Toff312 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (sym (lem-VPQ-at0314203142 c4)) ▸
       at 4 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @0314203142: 12 steps
lem-box-cP-at0314203142 : Complete 4 → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-box-cP-at0314203142 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (lw0 c4 (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-QVQ-at0314203142 c4) ▸
       at 1 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0314203142 c4) ▸
       at 2 2 [] (pw1 c4 (Toff304 ∷ Toff304 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-box-4 @0410213243: 103 steps
lem-box-box-4-at0410213243 : Complete 4 → ⟪ (Bx4-0123 ∷ Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ Bx4-0123 ∷ []) ⟫ʷ
lem-box-box-4-at0410213243 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (Bx4-0123 ∷ Bx3-4012 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ034 ∷ Toff312 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CCZ034 ∷ CX41 ∷ CS24 ∷ CCZ234 ∷ Toff312 ∷ [])
  b0 = at 0 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at0410213243 c4) ▸
       at 4 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 3 2 (CCZ034 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ234 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff312 ∷ CCZ124 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ124 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ234 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ034 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ034 ∷ CX41 ∷ []) (pw2 c4 (CX41 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX41 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ034 ∷ Toff312 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CCZ034 ∷ CX41 ∷ CS24 ∷ CCZ234 ∷ Toff312 ∷ []) (Toff401 ∷ CCZ234 ∷ CCZ034 ∷ Toff401 ∷ CCZ013 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ234 ∷ [])
  b1 = at 7 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 c4) ▸
       at 6 2 (CCZ034 ∷ CX41 ∷ []) (pw2 c4 (CX41 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸
       at 6 5 (CCZ124 ∷ []) (lw0 c4 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (Toff312 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ124 ∷ CCZ234 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 2 2 (CCZ034 ∷ Toff401 ∷ CCZ013 ∷ []) (pw2 c4 (Toff401 ∷ CCZ034 ∷ []) (CCZ034 ∷ Toff401 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff401 ∷ CCZ234 ∷ CCZ034 ∷ Toff401 ∷ CCZ013 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ234 ∷ []) (Toff401 ∷ CCZ234 ∷ CCZ034 ∷ K4 ∷ Toff312 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ CCZ012 ∷ CCZ013 ∷ CCZ034 ∷ Toff312 ∷ CCZ234 ∷ [])
  b2 = at 4 2 (Toff312 ∷ CCZ012 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ012 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ []) (pw2 c4 (Toff401 ∷ []) (K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff312 ∷ K4⁻ ∷ []) (sym (c₄ (Toffᵗ ↑) (K • iI))) ▸
       at 8 2 (Toff312 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ Toff312 ∷ []) (Toff312 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 c4) ▸
       at 6 2 (Toff312 ∷ CS01⁻ ∷ []) (lw4 c4 (CS01⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 c4) ▸
       at 4 2 (Toff312 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ Toff312 ∷ []) (Toff312 ∷ CS01 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Toff401 ∷ CCZ234 ∷ CCZ034 ∷ K4 ∷ Toff312 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ CCZ012 ∷ CCZ013 ∷ CCZ034 ∷ Toff312 ∷ CCZ234 ∷ []) (Toff401 ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ Toff401 ∷ CS12 ∷ CCZ034 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ013 ∷ Toff312 ∷ CCZ234 ∷ [])
  b3 = at 3 2 (Toff312 ∷ K4 ∷ []) (sym (c₄ (Toffᵗ ↑) (K))) ▸
       at 4 7 (Toff401 ∷ []) (pw2 c4 (K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ []) (Toff401 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ034 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ034 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 c4) ▸
       at 6 2 (CCZ034 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Toff401 ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ Toff401 ∷ CS12 ∷ CCZ034 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ013 ∷ Toff312 ∷ CCZ234 ∷ []) (Toff401 ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ Toff312 ∷ CS14 ∷ K4⁻ ∷ CCZ012 ∷ CCZ234 ∷ [])
  b4 = at 5 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸
       at 6 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ Toff401 ∷ CCZ013 ∷ []) (pw2 c4 (Toff401 ∷ CCZ034 ∷ []) (CCZ034 ∷ Toff401 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CCZ012 ∷ []) (lw4 c4 (CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff312 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ []) (pw2 c4 (Toff401 ∷ []) (K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff312 ∷ K4⁻ ∷ []) (sym (c₄ (Toffᵗ ↑) (K • iI))) ▸
       at 10 2 (Toff312 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ Toff312 ∷ []) (Toff312 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (Toff401 ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ Toff312 ∷ CS14 ∷ K4⁻ ∷ CCZ012 ∷ CCZ234 ∷ []) (Toff401 ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ [])
  b5 = at 9 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 c4) ▸
       at 8 2 (Toff312 ∷ CS01⁻ ∷ []) (lw4 c4 (CS01⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 c4) ▸
       at 6 2 (Toff312 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ Toff312 ∷ []) (Toff312 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff312 ∷ K4 ∷ []) (sym (c₄ (Toffᵗ ↑) (K))) ▸
       at 6 7 (Toff401 ∷ []) (pw2 c4 (K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ []) (Toff401 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 2 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸ done

  b6 : Chain (Toff401 ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ []) (Toff401 ∷ CCZ034 ∷ Toff312 ∷ CS12 ∷ CCZ034 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ CCZ234 ∷ Toff312 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ [])
  b6 = at 1 2 (CCZ034 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ234 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff312 ∷ CCZ124 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ124 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ234 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ034 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CX41 ∷ []) (pw2 c4 (CX41 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 c4) ▸
       at 4 2 (CCZ034 ∷ CX41 ∷ []) (pw2 c4 (CX41 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX41 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (Toff401 ∷ CCZ034 ∷ Toff312 ∷ CS12 ∷ CCZ034 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ CCZ234 ∷ Toff312 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ []) (CCZ034 ∷ K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ Toff312 ∷ CCZ012 ∷ CCZ013 ∷ CCZ034 ∷ Toff312 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ [])
  b7 = at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸
       at 4 5 (CCZ124 ∷ []) (lw0 c4 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (Toff312 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ124 ∷ CCZ234 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 0 2 (CCZ034 ∷ Toff401 ∷ CCZ013 ∷ []) (pw2 c4 (Toff401 ∷ CCZ034 ∷ []) (CCZ034 ∷ Toff401 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff312 ∷ CCZ012 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ012 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ []) (pw2 c4 (Toff401 ∷ []) (K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (CCZ034 ∷ K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ Toff312 ∷ CCZ012 ∷ CCZ013 ∷ CCZ034 ∷ Toff312 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ []) (CCZ034 ∷ Toff312 ∷ Toff401 ∷ CCZ012 ∷ CCZ013 ∷ CCZ034 ∷ Toff312 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ [])
  b8 = at 7 2 (Toff312 ∷ K4⁻ ∷ []) (sym (c₄ (Toffᵗ ↑) (K • iI))) ▸
       at 6 2 (Toff312 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ Toff312 ∷ []) (Toff312 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 c4) ▸
       at 4 2 (Toff312 ∷ CS01⁻ ∷ []) (lw4 c4 (CS01⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 c4) ▸
       at 2 2 (Toff312 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ Toff312 ∷ []) (Toff312 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ K4 ∷ []) (sym (c₄ (Toffᵗ ↑) (K))) ▸
       at 2 7 (Toff401 ∷ []) (pw2 c4 (K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ []) (Toff401 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (CCZ034 ∷ Toff312 ∷ Toff401 ∷ CCZ012 ∷ CCZ013 ∷ CCZ034 ∷ Toff312 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ []) (CCZ034 ∷ Toff312 ∷ Toff401 ∷ CCZ034 ∷ CCZ012 ∷ CCZ013 ∷ Toff312 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ [])
  b9 = at 4 2 (CCZ034 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ034 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 c4) ▸
       at 4 2 (CCZ034 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸
       at 4 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (CCZ034 ∷ Toff312 ∷ Toff401 ∷ CCZ034 ∷ CCZ012 ∷ CCZ013 ∷ Toff312 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K4 ∷ CS01 ∷ CX40 ∷ Toff312 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ [])
  b10 = at 2 2 (CCZ034 ∷ Toff401 ∷ CCZ013 ∷ []) (pw2 c4 (Toff401 ∷ CCZ034 ∷ []) (CCZ034 ∷ Toff401 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CCZ012 ∷ []) (lw4 c4 (CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff312 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ []) (pw2 c4 (Toff401 ∷ []) (K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff312 ∷ K4⁻ ∷ []) (sym (c₄ (Toffᵗ ↑) (K • iI))) ▸
       at 8 2 (Toff312 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ Toff312 ∷ []) (Toff312 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 c4) ▸
       at 6 2 (Toff312 ∷ CS01⁻ ∷ []) (lw4 c4 (CS01⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K4 ∷ CS01 ∷ CX40 ∷ Toff312 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ []) (Bx3-4012 ∷ Toff401 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CCZ234 ∷ CX01 ∷ CS02 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ [])
  b11 = at 5 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 c4) ▸
       at 4 2 (Toff312 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ Toff312 ∷ []) (Toff312 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff312 ∷ K4 ∷ []) (sym (c₄ (Toffᵗ ↑) (K))) ▸
       at 4 7 (Toff401 ∷ []) (pw2 c4 (K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ []) (Toff401 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ234 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸ done

  b12 : Chain (Bx3-4012 ∷ Toff401 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CCZ234 ∷ CX01 ∷ CS02 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ []) (Bx3-4012 ∷ Bx4-0123 ∷ [])
  b12 = at 4 2 (CCZ234 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS12 ∷ []) (lw0 c4 (CS12 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 3 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff401 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Bx4-0123 ∷ []) (sym (lem-box-tQ-at0410213243 c4)) ▸ done


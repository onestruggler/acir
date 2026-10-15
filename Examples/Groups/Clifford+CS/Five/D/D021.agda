{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D021 where

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
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-box-tQ-at0330 ; lem-cQ-at04203243)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-box-tQ-at0310243142 ; lem-cQ-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-comm-CS23-TOFF401 ; lem-comm-CSd04-TOFF312 ; lem-comm-CSd23-TOFF401 ; lem-comm-CZ12-TOFF304 ; lem-comm-SWAP02-BOX⟨4·13⟩ ; lem-comm-TOFF304-CSd12)
-- sym-ab @0314203142: 18 steps
lem-sym-ab-at0314203142 : Complete 4 → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-sym-ab-at0314203142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-4012 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (lw0 c4 (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx3-02 ∷ []) (refl) ▸
       at 7 1 (Bx3-02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ []) (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ [])
  b1 = at 2 6 (Bx0-312 ∷ []) (refl) ▸
       at 5 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸
       at 5 6 (CCZ123 ∷ []) (lw0 c4 (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx3-02 ∷ []) (refl) ▸
       at 10 1 (Bx3-02 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (Bx3-0412 ∷ [])
  b2 = at 5 6 (Bx0-312 ∷ []) (refl) ▸
       at 0 6 (Bx3-0412 ∷ []) (refl) ▸ done


-- tP @0310243142: 7 steps
lem-tP-at0310243142 : Complete 4 → ⟪ (Toff304 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ []) ⟫ʷ
lem-tP-at0310243142 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ Toff312 ∷ []) (Toff312 ∷ Toff304 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (pw1 c4 (Toff304 ∷ []) (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) (lw4 c4 (Toff312 ∷ []) (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ CCZ034 ∷ []) (lem-cQ-at0310243142 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff312 ∷ []) (lw4 c4 (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff304 ∷ []) (pw1 c4 (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (Toff304 ∷ []) tt tt Eq.refl) ▸ done


-- P-box @0310243142: 8 steps
lem-P-box-at0310243142 : Complete 4 → ⟪ (Toff312 ∷ Bx3-0412 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-P-box-at0310243142 c4 = run b0
  where
  b0 : Chain (Toff312 ∷ Bx3-0412 ∷ Toff312 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243142 c4) ▸
       at 0 2 (Toff304 ∷ Toff312 ∷ []) (sym (lem-tP-at0310243142 c4)) ▸
       at 1 2 (CCZ123 ∷ CZ12 ∷ Toff312 ∷ []) (lw4 c4 (Toff312 ∷ CCZ123 ∷ []) (CCZ123 ∷ CZ12 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff304 ∷ Toff312 ∷ []) (sym (lem-tP-at0310243142 c4)) ▸
       at 4 3 (CCZ123 ∷ CZ12 ∷ []) (lw4 c4 (Toff312 ∷ CCZ123 ∷ Toff312 ∷ []) (CCZ123 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff304 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF304 c4) ▸
       at 3 3 (CCZ123 ∷ []) (lw4 c4 (CZ12 ∷ CCZ123 ∷ CZ12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx3-0412 ∷ []) (sym (lem-box-tQ-at0310243142 c4)) ▸ done


-- VPQ @0310243142: 14 steps
lem-VPQ-at0310243142 : Complete 4 → ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at0310243142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (CS12⁻ ∷ CS04⁻ ∷ S3 ∷ Toff312 ∷ Toff304 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) (pw1 c4 (Toff304 ∷ CCZ034 ∷ []) (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) (lw4 c4 (Toff312 ∷ CCZ123 ∷ []) (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS12⁻ ∷ S3⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (S • S • S))) ▸
       at 2 2 (CS12⁻ ∷ Toff304 ∷ []) (lem-comm-TOFF304-CSd12 c4) ▸
       at 1 2 (CS12⁻ ∷ S3 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (S))) ▸
       at 0 2 (CS12⁻ ∷ CS04⁻ ∷ []) (pw3 c4 (CS04⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (S3⁻ ∷ S3 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0310243142 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS04⁻ ∷ S3 ∷ Toff312 ∷ Toff304 ∷ S3⁻ ∷ []) (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (lw4 c4 [] (S3⁻ ∷ S3 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S3 ∷ CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ S3 ∷ []) (S3 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff312 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF312 c4) ▸
       at 3 2 (S3⁻ ∷ CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Toff312 ∷ CCZ123 ∷ []) (lw4 c4 (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) (Toff312 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff304 ∷ CCZ034 ∷ []) (pw1 c4 (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) (Toff304 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @0310243142: 3 steps
lem-QVQ-at0310243142 : Complete 4 → ⟪ (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-QVQ-at0310243142 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ [])
  b0 = at 0 0 (Toff312 ∷ Toff312 ∷ []) (lw4 c4 [] (Toff312 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (sym (lem-VPQ-at0310243142 c4)) ▸
       at 4 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @0310243142: 12 steps
lem-box-cP-at0310243142 : Complete 4 → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-box-cP-at0310243142 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (lw4 c4 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-QVQ-at0310243142 c4) ▸
       at 1 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0310243142 c4) ▸
       at 2 2 [] (pw1 c4 (Toff304 ∷ Toff304 ∷ []) [] tt tt Eq.refl) ▸ done


-- pairs @0310243142: 4 steps
lem-pairs-at0310243142 : Complete 4 → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-pairs-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Bx3-1204 ∷ [])
  b0 = at 0 1 (Toff312 ∷ Bx3-0412 ∷ Toff312 ∷ []) (sym (lem-P-box-at0310243142 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 4 2 [] (lw4 c4 (Toff312 ∷ Toff312 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx3-1204 ∷ []) (sym (lem-box-tQ-at0330 c4)) ▸ done


-- box-perm-3421 @0314203142: 2 steps
lem-box-perm-3421-at0314203142 : Complete 4 → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-box-perm-3421-at0314203142 c4 = run b0
  where
  b0 : Chain (Bx3-4012 ∷ []) (Bx3-1204 ∷ [])
  b0 = at 0 1 (Bx3-0412 ∷ []) (lem-sym-ab-at0314203142 c4) ▸
       at 0 1 (Bx3-1204 ∷ []) (lem-pairs-at0310243142 c4) ▸ done


-- sym-ab @0410213243: 18 steps
lem-sym-ab-at0410213243 : Complete 4 → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-sym-ab-at0410213243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-0123 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (pw1 c4 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx4-13 ∷ []) (refl) ▸
       at 7 1 (Bx4-13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ [])
  b1 = at 2 6 (Bx1-423 ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸
       at 5 6 (CCZ234 ∷ []) (pw1 c4 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx4-13 ∷ []) (refl) ▸
       at 10 1 (Bx4-13 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (Bx4-1023 ∷ [])
  b2 = at 5 6 (Bx1-423 ∷ []) (refl) ▸
       at 0 6 (Bx4-1023 ∷ []) (refl) ▸ done


-- box-tQ @04203243: 13 steps
lem-box-tQ-at04203243 : Complete 4 → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at04203243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-1023 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (lw0 c4 (CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (lw0 c4 (CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff401 ∷ CCZ014 ∷ CZ01 ∷ []) (pw2 c4 (CCZ014 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ014 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ014 ∷ []) (lem-cQ-at04203243 c4) ▸
       at 2 4 (Toff401 ∷ []) (pw2 c4 (CCZ014 ∷ CZ01 ∷ Toff401 ∷ CCZ014 ∷ []) (Toff401 ∷ []) tt tt Eq.refl) ▸ done


-- CXbc-box @04203243: 17 steps
lem-CXbc-box-at04203243 : Complete 4 → ⟪ (CX02 ∷ Bx4-1023 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at04203243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX02 ∷ Bx4-1023 ∷ CX02 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CX02 ∷ CCZ034 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CCZ234 ∷ CX10 ∷ CS13 ∷ CX02 ∷ [])
  b0 = at 1 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at04203243 c4) ▸
       at 0 2 (Toff401 ∷ CX02 ∷ []) (pw3 c4 (CX02 ∷ Toff401 ∷ []) (Toff401 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CX02 ∷ CCZ034 ∷ []) (pw1 c4 (CX02 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX02 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff401 ∷ CCZ034 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ034 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ034 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff401 ∷ CX02 ∷ []) (pw3 c4 (CX02 ∷ Toff401 ∷ []) (Toff401 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ234 ∷ CS13 ∷ []) (lw0 c4 (CS13 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸ done

  b1 : Chain (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CX02 ∷ CCZ034 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CCZ234 ∷ CX10 ∷ CS13 ∷ CX02 ∷ []) (Bx4-1023 ∷ CX02 ∷ CCZ013 ∷ CX02 ∷ [])
  b1 = at 7 2 (CCZ234 ∷ CS03⁻ ∷ []) (pw1 c4 (CS03⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ CX02 ∷ CCZ034 ∷ []) (pw1 c4 (CX02 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX02 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX02 ∷ []) (pw1 c4 (CX02 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX02 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-tQ-at04203243 c4)) ▸ done

  b2 : Chain (Bx4-1023 ∷ CX02 ∷ CCZ013 ∷ CX02 ∷ []) (Bx4-1023 ∷ CCZ013 ∷ [])
  b2 = at 1 3 (CCZ013 ∷ []) (lw4 c4 (CX02 ∷ CCZ013 ∷ CX02 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @04203243: 18 steps
lem-CXcb-box-at04203243 : Complete 4 → ⟪ (CX20 ∷ Bx4-1023 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at04203243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX20 ∷ Bx4-1023 ∷ CX20 ∷ []) (Toff401 ∷ CCZ234 ∷ CX20 ∷ Toff412 ∷ CS23 ∷ CX12 ∷ Toff401 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ234 ∷ CX20 ∷ [])
  b0 = at 1 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at04203243 c4) ▸
       at 0 2 (Toff401 ∷ CX20 ∷ Toff412 ∷ []) (pw3 c4 (CX20 ∷ Toff401 ∷ []) (Toff401 ∷ CX20 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ234 ∷ Toff412 ∷ CCZ123 ∷ []) (lw0 c4 (Toff412 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff412 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CX20 ∷ []) (pw1 c4 (CX20 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX20 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff401 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ Toff401 ∷ []) (Toff401 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff401 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ Toff401 ∷ []) (Toff401 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff401 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF401 c4) ▸ done

  b1 : Chain (Toff401 ∷ CCZ234 ∷ CX20 ∷ Toff412 ∷ CS23 ∷ CX12 ∷ Toff401 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ234 ∷ CX20 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ CX20 ∷ CCZ123 ∷ CX20 ∷ [])
  b1 = at 5 2 (Toff401 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ Toff401 ∷ []) (Toff401 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff401 ∷ CS23 ∷ []) (lem-comm-CS23-TOFF401 c4) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff401 ∷ Toff412 ∷ []) (pw3 c4 (Toff412 ∷ Toff401 ∷ []) (Toff401 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff401 ∷ CX20 ∷ Toff412 ∷ []) (pw3 c4 (CX20 ∷ Toff401 ∷ []) (Toff401 ∷ CX20 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX20 ∷ []) (pw3 c4 (CX20 ∷ Toff412 ∷ Toff412 ∷ []) (CX20 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ CX20 ∷ []) (pw1 c4 (CX20 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX20 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ CX20 ∷ CCZ123 ∷ CX20 ∷ []) (Bx4-1023 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-tQ-at04203243 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (lw4 c4 (CX20 ∷ CCZ123 ∷ CX20 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @04203243: 11 steps
lem-SWbc-box-at04203243 : Complete 4 → ⟪ (Sw02 ∷ Bx4-1023 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-SWbc-box-at04203243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw02 ∷ Bx4-1023 ∷ Sw02 ∷ []) (CX02 ∷ Bx4-1023 ∷ CX02 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CX02 ∷ CX20 ∷ CX02 ∷ []) (lw4 c4 (Sw02 ∷ []) (CX02 ∷ CX20 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX02 ∷ CX20 ∷ CX02 ∷ []) (lw4 c4 (Sw02 ∷ []) (CX02 ∷ CX20 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx4-1023 ∷ CCZ013 ∷ []) (lem-CXbc-box-at04203243 c4) ▸
       at 3 2 (CX20 ∷ CCZ123 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ CX20 ∷ []) (CX20 ∷ CCZ123 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx4-1023 ∷ CCZ123 ∷ []) (lem-CXcb-box-at04203243 c4) ▸
       at 4 2 (CX02 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ CX02 ∷ []) (CX02 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX02 ∷ CCZ013 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CX02 ∷ []) (CX02 ∷ CCZ013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX02 ∷ CCZ013 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CX02 ∷ []) (CX02 ∷ CCZ013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX02 ∷ Bx4-1023 ∷ CX02 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ []) (Bx4-1023 ∷ [])
  b1 = at 3 5 (CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx4-1023 ∷ CCZ013 ∷ []) (lem-CXbc-box-at04203243 c4) ▸
       at 1 2 [] (lw4 c4 (CCZ013 ∷ CCZ013 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @04203243: 23 steps
lem-nat-SWbc-at04203243 : Complete 4 → ⟪ (Sw02 ∷ Bx4-1023 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-nat-SWbc-at04203243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw02 ∷ Bx4-1023 ∷ Sw02 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ Sw02 ∷ CCZ124 ∷ Bx4-13 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ Sw02 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ CCZ014 ∷ []) (CCZ124 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff412 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ Toff401 ∷ []) (Toff412 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 2 2 (CCZ014 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ CCZ124 ∷ []) (CCZ014 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff104 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ Toff124 ∷ []) (Toff104 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ c4) ▸
       at 5 2 (Toff104 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ Toff124 ∷ []) (Toff104 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ Sw02 ∷ CCZ124 ∷ Bx4-13 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ Sw02 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ Toff412 ∷ CCZ124 ∷ CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Sw02 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ Sw02 ∷ [])
  b1 = at 6 2 (CCZ014 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ CCZ124 ∷ []) (CCZ014 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ c4) ▸
       at 8 2 (Toff412 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ Toff401 ∷ []) (Toff412 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ124 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ CCZ014 ∷ []) (CCZ124 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 10 2 (CCZ014 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ CCZ124 ∷ []) (CCZ014 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff104 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ Toff124 ∷ []) (Toff104 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ c4) ▸ done

  b2 : Chain (CCZ124 ∷ Toff412 ∷ CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ Toff412 ∷ CCZ124 ∷ CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Sw02 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ Sw02 ∷ []) (Bx4-1203 ∷ [])
  b2 = at 13 2 (Toff104 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ Toff124 ∷ []) (Toff104 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ014 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ CCZ124 ∷ []) (CCZ014 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ c4) ▸
       at 16 2 [] (lw4 c4 (Sw02 ∷ Sw02 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx1-403 ∷ []) (refl) ▸
       at 5 6 (Bx1-403 ∷ []) (refl) ▸
       at 0 6 (Bx4-1203 ∷ []) (refl) ▸ done


-- sym-bc @04203243: 2 steps
lem-sym-bc-at04203243 : Complete 4 → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-sym-bc-at04203243 c4 = run b0
  where
  b0 : Chain (Bx4-1023 ∷ []) (Bx4-1203 ∷ [])
  b0 = at 0 1 (Sw02 ∷ Bx4-1023 ∷ Sw02 ∷ []) (sym (lem-SWbc-box-at04203243 c4)) ▸
       at 0 3 (Bx4-1203 ∷ []) (lem-nat-SWbc-at04203243 c4) ▸ done


-- box-perm-2314 @0410213243: 2 steps
lem-box-perm-2314-at0410213243 : Complete 4 → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-box-perm-2314-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ []) (Bx4-1203 ∷ [])
  b0 = at 0 1 (Bx4-1023 ∷ []) (lem-sym-ab-at0410213243 c4) ▸
       at 0 1 (Bx4-1203 ∷ []) (lem-sym-bc-at04203243 c4) ▸ done


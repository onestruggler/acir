{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D045 where

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
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-box-tQ-at132132 ; lem-pairs-at122331)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-box-cP-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-pairs-at0330)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-box-tQ-at032032 ; lem-sym-ab-at03102132 ; lem-sym-bc-at032032)
open import Examples.Groups.Clifford+CS.Five.D.D023 using (lem-sym-ab-at032032)
open import Examples.Groups.Clifford+CS.Five.D.D043 using (lem-box-tQ-at0312243140 ; lem-cQ-at0312243140)
open import Examples.Groups.Clifford+CS.Five.D.D044 using (lem-box-perm-2341-at03102132 ; lem-box-tQ-at033440 ; lem-sym-ab-at033440 ; lem-sym-bc-at0312213440)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CSd24-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-comm-CX31-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-comm-CS24-CCZ013 ; lem-comm-CS24-TOFF013 ; lem-comm-CSd24-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-comm-CSd24-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-comm-CX31-TOFF024)
-- tP @0312243140: 7 steps
lem-tP-at0312243140 : Complete 4 → ⟪ (Toff324 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ []) ⟫ʷ
lem-tP-at0312243140 c4 = run b0
  where
  b0 : Chain (Toff324 ∷ Toff301 ∷ []) (Toff301 ∷ Toff324 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) (lw4 c4 (Toff301 ∷ []) (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ CCZ234 ∷ []) (lem-cQ-at0312243140 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff301 ∷ []) (lw4 c4 (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) (Toff301 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸ done


-- P-box @0312243140: 8 steps
lem-P-box-at0312243140 : Complete 4 → ⟪ (Toff301 ∷ Bx3-2410 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ []) ⟫ʷ
lem-P-box-at0312243140 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Bx3-2410 ∷ Toff301 ∷ []) (Bx3-2410 ∷ [])
  b0 = at 1 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at0312243140 c4) ▸
       at 0 2 (Toff324 ∷ Toff301 ∷ []) (sym (lem-tP-at0312243140 c4)) ▸
       at 1 2 (CCZ013 ∷ CZ01 ∷ Toff301 ∷ []) (lw4 c4 (Toff301 ∷ CCZ013 ∷ []) (CCZ013 ∷ CZ01 ∷ Toff301 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff324 ∷ Toff301 ∷ []) (sym (lem-tP-at0312243140 c4)) ▸
       at 4 3 (CCZ013 ∷ CZ01 ∷ []) (lw4 c4 (Toff301 ∷ CCZ013 ∷ Toff301 ∷ []) (CCZ013 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 3 3 (CCZ013 ∷ []) (lw4 c4 (CZ01 ∷ CCZ013 ∷ CZ01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx3-2410 ∷ []) (sym (lem-box-tQ-at0312243140 c4)) ▸ done


-- VPQ @0312243140: 14 steps
lem-VPQ-at0312243140 : Complete 4 → ⟪ (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at0312243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (CS01⁻ ∷ CS24⁻ ∷ S3 ∷ Toff301 ∷ Toff324 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) (lw0 c4 (Toff324 ∷ CCZ234 ∷ []) (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (lw4 c4 (Toff301 ∷ CCZ013 ∷ []) (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS01⁻ ∷ S3⁻ ∷ []) (sym (c₂ (CS • CS • CS) ((S • S • S) ↑))) ▸
       at 2 2 (CS01⁻ ∷ Toff324 ∷ []) (sym (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 1 2 (CS01⁻ ∷ S3 ∷ []) (sym (c₂ (CS • CS • CS) (S ↑))) ▸
       at 0 2 (CS01⁻ ∷ CS24⁻ ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 4 2 [] (lw4 c4 (S3⁻ ∷ S3 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff301 ∷ Toff324 ∷ []) (lem-tP-at0312243140 c4) ▸ done

  b1 : Chain (CS01⁻ ∷ CS24⁻ ∷ S3 ∷ Toff301 ∷ Toff324 ∷ S3⁻ ∷ []) (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (lw4 c4 [] (S3⁻ ∷ S3 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S3 ∷ CS24⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ S3 ∷ []) (S3 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff301 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF301 c4) ▸
       at 3 2 (S3⁻ ∷ CS24⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Toff301 ∷ CCZ013 ∷ []) (lw4 c4 (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (Toff301 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff324 ∷ CCZ234 ∷ []) (lw0 c4 (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) (Toff324 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @0312243140: 3 steps
lem-QVQ-at0312243140 : Complete 4 → ⟪ (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-QVQ-at0312243140 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ [])
  b0 = at 0 0 (Toff301 ∷ Toff301 ∷ []) (lw4 c4 [] (Toff301 ∷ Toff301 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (sym (lem-VPQ-at0312243140 c4)) ▸
       at 4 2 [] (lw4 c4 (CCZ013 ∷ CCZ013 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @0312243140: 12 steps
lem-box-cP-at0312243140 : Complete 4 → ⟪ (Bx3-2410 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-box-cP-at0312243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-2410 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ123 ∷ Toff213 ∷ CZ02 ∷ Toff213 ∷ CCZ123 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff324 ∷ Bx2-310 ∷ Toff324 ∷ CCZ234 ∷ Bx2-310 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (lw4 c4 (CCZ123 ∷ Toff213 ∷ CZ02 ∷ Toff213 ∷ CCZ123 ∷ CZ02 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ123 ∷ Toff213 ∷ CZ02 ∷ Toff213 ∷ CCZ123 ∷ CZ02 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (lw4 c4 (CCZ123 ∷ Toff213 ∷ CZ02 ∷ Toff213 ∷ CCZ123 ∷ CZ02 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-QVQ-at0312243140 c4) ▸
       at 1 2 (Toff301 ∷ Toff324 ∷ []) (lem-tP-at0312243140 c4) ▸
       at 2 2 [] (lw0 c4 (Toff324 ∷ Toff324 ∷ []) [] tt tt Eq.refl) ▸ done


-- pairs @0312243140: 4 steps
lem-pairs-at0312243140 : Complete 4 → ⟪ (Bx3-2410 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-pairs-at0312243140 c4 = run b0
  where
  b0 : Chain (Bx3-2410 ∷ []) (Bx3-1024 ∷ [])
  b0 = at 0 1 (Toff301 ∷ Bx3-2410 ∷ Toff301 ∷ []) (sym (lem-P-box-at0312243140 c4)) ▸
       at 1 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at0312243140 c4) ▸
       at 4 2 [] (lw4 c4 (Toff301 ∷ Toff301 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx3-1024 ∷ []) (sym (lem-box-tQ-at032032 c4)) ▸ done


-- box-perm-4123 @033440: 4 steps
lem-box-perm-4123-at033440 : Complete 4 → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-4123-at033440 c4 = run b0
  where
  b0 : Chain (Bx3-1240 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 1 (Bx3-2140 ∷ []) (lem-sym-ab-at033440 c4) ▸
       at 0 1 (Bx3-2410 ∷ []) (lem-sym-bc-at0312213440 c4) ▸
       at 0 1 (Bx3-1024 ∷ []) (lem-pairs-at0312243140 c4) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-sym-ab-at032032 c4) ▸ done


-- box-box-1 @03102132: 105 steps
lem-box-box-1-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-box-box-1-at03102132 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx3-0124 ∷ Bx0-3124 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CCZ013 ∷ CX32 ∷ CS34 ∷ Toff024 ∷ [])
  b0 = at 0 1 (Bx3-1240 ∷ []) (lem-box-perm-2341-at03102132 c4) ▸
       at 0 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at033440 c4) ▸
       at 4 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at132132 c4) ▸
       at 3 2 (CCZ013 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff024 ∷ CCZ034 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ034 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ034 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ013 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ013 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX32 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CCZ013 ∷ CX32 ∷ CS34 ∷ Toff024 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ [])
  b1 = at 8 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 c4) ▸
       at 7 2 (CCZ013 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 c4) ▸
       at 7 5 (CCZ234 ∷ []) (lw0 c4 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ013 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (Toff024 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ CCZ234 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx0-3124 ∷ []) (sym (lem-box-cP-at132132 c4)) ▸
       at 3 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at132132 c4) ▸ done

  b2 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ []) (Toff312 ∷ CCZ034 ∷ CCZ013 ∷ K3 ∷ CS12 ∷ Toff024 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ012 ∷ CCZ124 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ [])
  b2 = at 2 2 (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) (lw4 c4 (Toff312 ∷ CCZ013 ∷ []) (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff024 ∷ CCZ012 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ012 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ012 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) (lw4 c4 (Toff312 ∷ []) (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff024 ∷ K3⁻ ∷ []) (pw1 c4 (K3⁻ ∷ Toff024 ∷ []) (Toff024 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ Toff024 ∷ []) (Toff024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 c4) ▸
       at 6 2 (Toff024 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 c4) ▸ done

  b3 : Chain (Toff312 ∷ CCZ034 ∷ CCZ013 ∷ K3 ∷ CS12 ∷ Toff024 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ012 ∷ CCZ124 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ []) (Toff312 ∷ CCZ034 ∷ CCZ013 ∷ Toff024 ∷ Toff312 ∷ CCZ012 ∷ CS24 ∷ CCZ013 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff024 ∷ CCZ034 ∷ [])
  b3 = at 4 2 (Toff024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ Toff024 ∷ []) (Toff024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff024 ∷ K3 ∷ []) (pw1 c4 (K3 ∷ Toff024 ∷ []) (Toff024 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 4 7 (Toff312 ∷ []) (lw4 c4 (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ013 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ013 ∷ CX12 ∷ []) (lw4 c4 (CX12 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 c4) ▸
       at 7 2 (CCZ013 ∷ CX12 ∷ []) (lw4 c4 (CX12 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX12 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Toff312 ∷ CCZ034 ∷ CCZ013 ∷ Toff024 ∷ Toff312 ∷ CCZ012 ∷ CS24 ∷ CCZ013 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff024 ∷ CCZ034 ∷ []) (Toff312 ∷ CCZ034 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff024 ∷ K3⁻ ∷ CCZ124 ∷ CCZ034 ∷ [])
  b4 = at 6 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 c4) ▸
       at 7 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ013 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) (lw4 c4 (Toff312 ∷ CCZ013 ∷ []) (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Toff312 ∷ []) (lw4 c4 (Toff312 ∷ CCZ012 ∷ CCZ012 ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff024 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) (lw4 c4 (Toff312 ∷ []) (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff024 ∷ K3⁻ ∷ []) (pw1 c4 (K3⁻ ∷ Toff024 ∷ []) (Toff024 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (Toff312 ∷ CCZ034 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff024 ∷ K3⁻ ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff312 ∷ CCZ034 ∷ Bx0-3124 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b5 = at 10 2 (Toff024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ Toff024 ∷ []) (Toff024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 c4) ▸
       at 8 2 (Toff024 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 c4) ▸
       at 6 2 (Toff024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ Toff024 ∷ []) (Toff024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff024 ∷ K3 ∷ []) (pw1 c4 (K3 ∷ Toff024 ∷ []) (Toff024 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (Toff312 ∷ []) (lw4 c4 (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx0-3124 ∷ []) (sym (lem-box-cP-at132132 c4)) ▸ done

  b6 : Chain (Toff312 ∷ CCZ034 ∷ Bx0-3124 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff312 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ CS24 ∷ CCZ013 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ Toff024 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b6 = at 2 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at132132 c4) ▸
       at 1 2 (CCZ013 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff024 ∷ CCZ034 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ034 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ034 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ013 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ013 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 c4) ▸
       at 5 2 (CCZ013 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX32 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (Toff312 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ CS24 ∷ CCZ013 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ Toff024 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (CCZ013 ∷ Toff312 ∷ Toff024 ∷ CCZ012 ∷ CCZ124 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b7 = at 4 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 c4) ▸
       at 5 5 (CCZ234 ∷ []) (lw0 c4 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (Toff024 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ CCZ234 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Bx0-3124 ∷ []) (sym (lem-box-cP-at132132 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at132132 c4) ▸
       at 0 2 (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) (lw4 c4 (Toff312 ∷ CCZ013 ∷ []) (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff024 ∷ CCZ012 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ012 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ012 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (CCZ013 ∷ Toff312 ∷ Toff024 ∷ CCZ012 ∷ CCZ124 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (CCZ013 ∷ Toff024 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ012 ∷ CCZ124 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b8 = at 1 1 (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) (lw4 c4 (Toff312 ∷ []) (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff024 ∷ K3⁻ ∷ []) (pw1 c4 (K3⁻ ∷ Toff024 ∷ []) (Toff024 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ Toff024 ∷ []) (Toff024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 c4) ▸
       at 4 2 (Toff024 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 c4) ▸
       at 2 2 (Toff024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ Toff024 ∷ []) (Toff024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff024 ∷ K3 ∷ []) (pw1 c4 (K3 ∷ Toff024 ∷ []) (Toff024 ∷ K3 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (CCZ013 ∷ Toff024 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ012 ∷ CCZ124 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (CCZ013 ∷ Toff024 ∷ Toff312 ∷ CCZ012 ∷ CCZ013 ∷ CCZ124 ∷ Toff024 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b9 = at 2 7 (Toff312 ∷ []) (lw4 c4 (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ013 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ013 ∷ CX12 ∷ []) (lw4 c4 (CX12 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 c4) ▸
       at 5 2 (CCZ013 ∷ CX12 ∷ []) (lw4 c4 (CX12 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 c4) ▸
       at 5 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (CCZ013 ∷ Toff024 ∷ Toff312 ∷ CCZ012 ∷ CCZ013 ∷ CCZ124 ∷ Toff024 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ Toff024 ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b10 = at 3 2 (CCZ013 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) (lw4 c4 (Toff312 ∷ CCZ013 ∷ []) (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Toff312 ∷ []) (lw4 c4 (Toff312 ∷ CCZ012 ∷ CCZ012 ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff024 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) (lw4 c4 (Toff312 ∷ []) (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff024 ∷ K3⁻ ∷ []) (pw1 c4 (K3⁻ ∷ Toff024 ∷ []) (Toff024 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ Toff024 ∷ []) (Toff024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 c4) ▸ done

  b11 : Chain (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ Toff024 ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (Bx0-3124 ∷ Toff312 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b11 = at 6 2 (Toff024 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 c4) ▸
       at 4 2 (Toff024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ Toff024 ∷ []) (Toff024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff024 ∷ K3 ∷ []) (pw1 c4 (K3 ∷ Toff024 ∷ []) (Toff024 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 4 7 (Toff312 ∷ []) (lw4 c4 (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-3124 ∷ []) (sym (lem-box-cP-at132132 c4)) ▸
       at 2 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (Bx0-3124 ∷ Toff312 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (Bx0-3124 ∷ Bx3-1240 ∷ [])
  b12 = at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 4 2 (CCZ034 ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 2 2 (CCZ034 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 3 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff312 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Bx3-1240 ∷ []) (sym (lem-box-tQ-at033440 c4)) ▸ done

  b13 : Chain (Bx0-3124 ∷ Bx3-1240 ∷ []) (Bx0-3124 ∷ Bx3-0124 ∷ [])
  b13 = at 1 1 (Bx3-0124 ∷ []) (lem-box-perm-4123-at033440 c4) ▸ done


-- CXbc-box @132132: 17 steps
lem-CXbc-box-at132132 : Complete 4 → ⟪ (CX12 ∷ Bx0-3124 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at132132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX12 ∷ Bx0-3124 ∷ CX12 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX12 ∷ CCZ014 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CCZ024 ∷ CX31 ∷ CS34 ∷ CX12 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at132132 c4) ▸
       at 0 2 (Toff013 ∷ CX12 ∷ []) (lw4 c4 (CX12 ∷ Toff013 ∷ []) (Toff013 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CX12 ∷ CCZ014 ∷ []) (pw3 c4 (CX12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX12 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ CCZ014 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ014 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ014 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff013 ∷ CX12 ∷ []) (lw4 c4 (CX12 ∷ Toff013 ∷ []) (Toff013 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 c4) ▸ done

  b1 : Chain (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX12 ∷ CCZ014 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CCZ024 ∷ CX31 ∷ CS34 ∷ CX12 ∷ []) (Bx0-3124 ∷ CX12 ∷ CCZ134 ∷ CX12 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS14⁻ ∷ []) (pw3 c4 (CS14⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ134 ∷ []) (lw0 c4 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CX12 ∷ CCZ014 ∷ []) (pw3 c4 (CX12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX12 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX12 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-3124 ∷ []) (sym (lem-box-tQ-at132132 c4)) ▸ done

  b2 : Chain (Bx0-3124 ∷ CX12 ∷ CCZ134 ∷ CX12 ∷ []) (Bx0-3124 ∷ CCZ134 ∷ [])
  b2 = at 1 3 (CCZ134 ∷ []) (lw0 c4 (CX12 ∷ CCZ134 ∷ CX12 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @132132: 18 steps
lem-CXcb-box-at132132 : Complete 4 → ⟪ (CX21 ∷ Bx0-3124 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXcb-box-at132132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX21 ∷ Bx0-3124 ∷ CX21 ∷ []) (Toff013 ∷ CCZ024 ∷ CX21 ∷ Toff023 ∷ CS24 ∷ CX32 ∷ Toff013 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ CCZ024 ∷ CX21 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at132132 c4) ▸
       at 0 2 (Toff013 ∷ CX21 ∷ Toff023 ∷ []) (lw4 c4 (CX21 ∷ Toff013 ∷ []) (Toff013 ∷ CX21 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ Toff023 ∷ CCZ234 ∷ []) (pw1 c4 (Toff023 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff023 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CX21 ∷ []) (pw3 c4 (CX21 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff013 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ Toff013 ∷ []) (Toff013 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff013 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ Toff013 ∷ []) (Toff013 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 c4) ▸ done

  b1 : Chain (Toff013 ∷ CCZ024 ∷ CX21 ∷ Toff023 ∷ CS24 ∷ CX32 ∷ Toff013 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ CCZ024 ∷ CX21 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CX21 ∷ CCZ234 ∷ CX21 ∷ [])
  b1 = at 5 2 (Toff013 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ Toff013 ∷ []) (Toff013 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff013 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF013 c4) ▸
       at 5 5 (CCZ234 ∷ []) (lw0 c4 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ Toff013 ∷ []) (Toff013 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff013 ∷ CX21 ∷ Toff023 ∷ []) (lw4 c4 (CX21 ∷ Toff013 ∷ []) (Toff013 ∷ CX21 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX21 ∷ []) (lw4 c4 (CX21 ∷ Toff023 ∷ Toff023 ∷ []) (CX21 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ234 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CX21 ∷ []) (pw3 c4 (CX21 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX21 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CX21 ∷ CCZ234 ∷ CX21 ∷ []) (Bx0-3124 ∷ CCZ234 ∷ [])
  b2 = at 0 4 (Bx0-3124 ∷ []) (sym (lem-box-tQ-at132132 c4)) ▸
       at 1 3 (CCZ234 ∷ []) (lw0 c4 (CX21 ∷ CCZ234 ∷ CX21 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @132132: 11 steps
lem-SWbc-box-at132132 : Complete 4 → ⟪ (Sw12 ∷ Bx0-3124 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-SWbc-box-at132132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx0-3124 ∷ Sw12 ∷ []) (CX12 ∷ Bx0-3124 ∷ CX12 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (lw4 c4 (Sw12 ∷ []) (CX12 ∷ CX21 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (lw4 c4 (Sw12 ∷ []) (CX12 ∷ CX21 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx0-3124 ∷ CCZ134 ∷ []) (lem-CXbc-box-at132132 c4) ▸
       at 3 2 (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CX21 ∷ []) (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-3124 ∷ CCZ234 ∷ []) (lem-CXcb-box-at132132 c4) ▸
       at 4 2 (CX12 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CX12 ∷ []) (CX12 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CX12 ∷ []) (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CX12 ∷ []) (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX12 ∷ Bx0-3124 ∷ CX12 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ []) (Bx0-3124 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx0-3124 ∷ CCZ134 ∷ []) (lem-CXbc-box-at132132 c4) ▸
       at 1 2 [] (lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @132132: 23 steps
lem-nat-SWbc-at132132 : Complete 4 → ⟪ (Sw12 ∷ Bx0-3124 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-nat-SWbc-at132132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Bx0-3124 ∷ Sw12 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ Sw12 ∷ CCZ023 ∷ Bx0-34 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff013 ∷ []) (Toff023 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 2 2 (CCZ013 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff302 ∷ []) (Toff301 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 5 2 (Toff301 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff302 ∷ []) (Toff301 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ Sw12 ∷ CCZ023 ∷ Bx0-34 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ Sw12 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ Toff023 ∷ CCZ023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Sw12 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ Sw12 ∷ [])
  b1 = at 6 2 (CCZ013 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 8 2 (Toff023 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff013 ∷ []) (Toff023 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ023 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 10 2 (CCZ013 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff301 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff302 ∷ []) (Toff301 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ Toff023 ∷ CCZ023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Sw12 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ Sw12 ∷ []) (Bx0-3214 ∷ [])
  b2 = at 13 2 (Toff301 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff302 ∷ []) (Toff301 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ013 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 16 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx3-014 ∷ []) (refl) ▸
       at 5 6 (Bx3-014 ∷ []) (refl) ▸
       at 0 6 (Bx0-3214 ∷ []) (refl) ▸ done


-- sym-bc @132132: 2 steps
lem-sym-bc-at132132 : Complete 4 → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-sym-bc-at132132 c4 = run b0
  where
  b0 : Chain (Bx0-3124 ∷ []) (Bx0-3214 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx0-3124 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at132132 c4)) ▸
       at 0 3 (Bx0-3214 ∷ []) (lem-nat-SWbc-at132132 c4) ▸ done


-- sym-ab @1331: 18 steps
lem-sym-ab-at1331 : Complete 4 → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-sym-ab-at1331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-3214 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (pw2 c4 (CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) (pw3 c4 (CCZ014 ∷ []) (CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-24 ∷ []) (refl) ▸
       at 7 1 (Bx0-24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ [])
  b1 = at 2 6 (Bx2-014 ∷ []) (refl) ▸
       at 5 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸
       at 5 6 (CCZ014 ∷ []) (pw2 c4 (CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) (pw3 c4 (CCZ014 ∷ []) (CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx0-24 ∷ []) (refl) ▸
       at 10 1 (Bx0-24 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (Bx0-2314 ∷ [])
  b2 = at 5 6 (Bx2-014 ∷ []) (refl) ▸
       at 0 6 (Bx0-2314 ∷ []) (refl) ▸ done


-- box-perm-2431 @132132: 3 steps
lem-box-perm-2431-at132132 : Complete 4 → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-2431-at132132 c4 = run b0
  where
  b0 : Chain (Bx0-3124 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 1 (Bx0-3214 ∷ []) (lem-sym-bc-at132132 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym-ab-at1331 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-pairs-at122331 c4) ▸ done


-- box-perm-1423 @03102132: 3 steps
lem-box-perm-1423-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-box-perm-1423-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 1 (Bx3-1024 ∷ []) (lem-sym-ab-at03102132 c4) ▸
       at 0 1 (Bx3-1204 ∷ []) (lem-sym-bc-at032032 c4) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-pairs-at0330 c4) ▸ done


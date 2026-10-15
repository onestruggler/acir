{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D022 where

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
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-box-cP-at043043 ; lem-box-tQ-at043043 ; lem-tP-at043043)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-box-cP-at04203243 ; lem-box-perm-1324-at043043 ; lem-box-perm-3124-at043043 ; lem-box-tQ-at0330)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-box-box-4-at0410213243 ; lem-box-perm-4312-at0330)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-box-perm-2314-at0410213243 ; lem-box-perm-3421-at0314203142)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CS23-CCZ014 ; lem-comm-CSd23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-CS12-CCZ034 ; lem-comm-CSd12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-comm-CS03-CCZ124 ; lem-comm-CSd03-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-comm-CSd04-TOFF312 ; lem-comm-CSd24-TOFF301 ; lem-comm-CZ03-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-comm-CS04-TOFF312 ; lem-comm-CS24-TOFF301 ; lem-comm-CZ12-TOFF403 ; lem-comm-SWAP02-BOX⟨3·14⟩)
-- F0-B: 62 steps
lem-F0-B : Complete 4 → ⟪ (CX34 ∷ Bx3-1204 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ Bx4-1203 ∷ []) ⟫ʷ
lem-F0-B c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (CX34 ∷ Bx3-1204 ∷ CX34 ∷ []) (Toff312 ∷ Toff412 ∷ CCZ034 ∷ Toff312 ∷ Toff412 ∷ CZ03 ∷ CCZ012 ∷ CCZ034 ∷ CZ03 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at0330 c4) ▸
       at 0 2 (Toff312 ∷ Toff412 ∷ CX34 ∷ []) (lw0 c4 (CX34 ∷ Toff312 ∷ []) (Toff312 ∷ Toff412 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CZ03 ∷ CX34 ∷ []) (pw1 c4 (CX34 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ03 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff312 ∷ Toff412 ∷ CX34 ∷ []) (lw0 c4 (CX34 ∷ Toff312 ∷ []) (Toff312 ∷ Toff412 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CCZ034 ∷ CZ03 ∷ []) (pw1 c4 (CX34 ∷ CCZ034 ∷ CX34 ∷ []) (CCZ034 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff312 ∷ CZ03 ∷ CCZ012 ∷ []) (lw4 c4 (CZ03 ∷ Toff312 ∷ []) (Toff312 ∷ CZ03 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff412 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff412 ∷ CZ03 ∷ []) (lem-comm-CZ03-TOFF412 c4) ▸ done

  b1 : Chain (Toff312 ∷ Toff412 ∷ CCZ034 ∷ Toff312 ∷ Toff412 ∷ CZ03 ∷ CCZ012 ∷ CCZ034 ∷ CZ03 ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b1 = at 5 2 (CCZ012 ∷ CZ03 ∷ []) (lw4 c4 (CZ03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CCZ034 ∷ []) (pw1 c4 (CZ03 ∷ CCZ034 ∷ CZ03 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff412 ∷ Toff312 ∷ []) (lw0 c4 (Toff312 ∷ Toff412 ∷ []) (Toff412 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 4 0 (CCZ034 ∷ CCZ034 ∷ []) (pw1 c4 [] (CCZ034 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Bx4-1203 ∷ []) (sym (lem-box-tQ-at043043 c4)) ▸
       at 1 1 (Bx4-1023 ∷ []) (lem-box-perm-1324-at043043 c4) ▸
       at 1 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 0 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ []) (lw4 c4 (Toff312 ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ014 ∷ Toff312 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b2 = at 6 2 (CCZ014 ∷ K3⁻ ∷ []) (pw2 c4 (K3⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 2 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 0 2 (CCZ014 ∷ K3 ∷ []) (pw2 c4 (K3 ∷ CCZ014 ∷ []) (CCZ014 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 1 7 (Toff312 ∷ []) (lw4 c4 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (CCZ014 ∷ Toff312 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ014 ∷ Toff423 ∷ K3 ∷ CS23 ∷ CCZ014 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ Toff412 ∷ CCZ012 ∷ Toff423 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b3 = at 1 2 (Toff423 ∷ Toff312 ∷ Toff412 ∷ []) (lw0 c4 (Toff312 ∷ Toff423 ∷ []) (Toff423 ∷ Toff312 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ Toff412 ∷ CCZ012 ∷ []) (pw3 c4 (Toff412 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff412 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ []) (lw4 c4 (Toff312 ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ014 ∷ K3⁻ ∷ []) (pw2 c4 (K3⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 4 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (CCZ014 ∷ Toff423 ∷ K3 ∷ CS23 ∷ CCZ014 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ Toff412 ∷ CCZ012 ∷ Toff423 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff312 ∷ Toff412 ∷ CS12 ∷ Toff423 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b4 = at 3 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 2 2 (CCZ014 ∷ K3 ∷ []) (pw2 c4 (K3 ∷ CCZ014 ∷ []) (CCZ014 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 3 7 (Toff312 ∷ []) (lw4 c4 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff423 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ Toff423 ∷ []) (Toff423 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 7 2 (Toff423 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸ done

  b5 : Chain (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff312 ∷ Toff412 ∷ CS12 ∷ Toff423 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ []) (Bx4-1203 ∷ Toff312 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b5 = at 5 2 (Toff423 ∷ CS12 ∷ []) (lw0 c4 (CS12 ∷ Toff423 ∷ []) (Toff423 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff423 ∷ Toff412 ∷ []) (lw0 c4 (Toff412 ∷ Toff423 ∷ []) (Toff423 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff423 ∷ Toff312 ∷ Toff412 ∷ []) (lw0 c4 (Toff312 ∷ Toff423 ∷ []) (Toff423 ∷ Toff312 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (Toff312 ∷ []) (lw0 c4 (Toff312 ∷ Toff412 ∷ Toff412 ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 0 1 (Bx4-1203 ∷ []) (sym (lem-box-perm-1324-at043043 c4)) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (Bx4-1203 ∷ Toff312 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ []) (Bx4-1203 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ [])
  b6 = at 6 2 (CCZ034 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 c4) ▸
       at 3 2 (CCZ034 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸
       at 3 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff312 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸ done

  b7 : Chain (Bx4-1203 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (Bx3-1204 ∷ Bx4-1203 ∷ [])
  b7 = at 1 4 (Bx3-1204 ∷ []) (sym (lem-box-tQ-at0330 c4)) ▸
       at 0 1 (Bx4-0123 ∷ []) (lem-box-perm-3124-at043043 c4) ▸
       at 1 1 (Bx3-4012 ∷ []) (lem-box-perm-4312-at0330 c4) ▸
       at 0 2 (Bx3-4012 ∷ Bx4-0123 ∷ []) (lem-box-box-4-at0410213243 c4) ▸
       at 0 1 (Bx3-1204 ∷ []) (lem-box-perm-3421-at0314203142 c4) ▸
       at 1 1 (Bx4-1203 ∷ []) (lem-box-perm-2314-at0410213243 c4) ▸ done


-- sym-ab @03102132: 18 steps
lem-sym-ab-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-sym-ab-at03102132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-0124 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (pw1 c4 (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx3-14 ∷ []) (refl) ▸
       at 7 1 (Bx3-14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ [])
  b1 = at 2 6 (Bx1-324 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸
       at 5 6 (CCZ234 ∷ []) (pw1 c4 (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx3-14 ∷ []) (refl) ▸
       at 10 1 (Bx3-14 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (Bx3-1024 ∷ [])
  b2 = at 5 6 (Bx1-324 ∷ []) (refl) ▸
       at 0 6 (Bx3-1024 ∷ []) (refl) ▸ done


-- cQ @032032: 7 steps
lem-cQ-at032032 : Complete 4 → ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at032032 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ CS13 ∷ []) (lw0 c4 (CS13 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS03⁻ ∷ []) (pw1 c4 (CS03⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @032032: 13 steps
lem-box-tQ-at032032 : Complete 4 → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at032032 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1024 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (lw0 c4 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (lw0 c4 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff301 ∷ CCZ013 ∷ CZ01 ∷ []) (lw4 c4 (CCZ013 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ013 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ013 ∷ []) (lem-cQ-at032032 c4) ▸
       at 2 4 (Toff301 ∷ []) (lw4 c4 (CCZ013 ∷ CZ01 ∷ Toff301 ∷ CCZ013 ∷ []) (Toff301 ∷ []) tt tt Eq.refl) ▸ done


-- CXbc-box @032032: 17 steps
lem-CXbc-box-at032032 : Complete 4 → ⟪ (CX02 ∷ Bx3-1024 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at032032 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX02 ∷ Bx3-1024 ∷ CX02 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CX02 ∷ CCZ034 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CCZ234 ∷ CX10 ∷ CS14 ∷ CX02 ∷ [])
  b0 = at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at032032 c4) ▸
       at 0 2 (Toff301 ∷ CX02 ∷ []) (lw4 c4 (CX02 ∷ Toff301 ∷ []) (Toff301 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CX02 ∷ CCZ034 ∷ []) (pw1 c4 (CX02 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX02 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff301 ∷ CCZ034 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ034 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ034 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff301 ∷ CX02 ∷ []) (lw4 c4 (CX02 ∷ Toff301 ∷ []) (Toff301 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ234 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸ done

  b1 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CX02 ∷ CCZ034 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CCZ234 ∷ CX10 ∷ CS14 ∷ CX02 ∷ []) (Bx3-1024 ∷ CX02 ∷ CCZ014 ∷ CX02 ∷ [])
  b1 = at 7 2 (CCZ234 ∷ CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ014 ∷ []) (pw2 c4 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ CX02 ∷ CCZ034 ∷ []) (pw1 c4 (CX02 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX02 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX02 ∷ []) (pw1 c4 (CX02 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX02 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx3-1024 ∷ []) (sym (lem-box-tQ-at032032 c4)) ▸ done

  b2 : Chain (Bx3-1024 ∷ CX02 ∷ CCZ014 ∷ CX02 ∷ []) (Bx3-1024 ∷ CCZ014 ∷ [])
  b2 = at 1 3 (CCZ014 ∷ []) (pw3 c4 (CX02 ∷ CCZ014 ∷ CX02 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @032032: 18 steps
lem-CXcb-box-at032032 : Complete 4 → ⟪ (CX20 ∷ Bx3-1024 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at032032 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX20 ∷ Bx3-1024 ∷ CX20 ∷ []) (Toff301 ∷ CCZ234 ∷ CX20 ∷ Toff312 ∷ CS24 ∷ CX12 ∷ Toff301 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ234 ∷ CX20 ∷ [])
  b0 = at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at032032 c4) ▸
       at 0 2 (Toff301 ∷ CX20 ∷ Toff312 ∷ []) (lw4 c4 (CX20 ∷ Toff301 ∷ []) (Toff301 ∷ CX20 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ234 ∷ Toff312 ∷ CCZ124 ∷ []) (lw0 c4 (Toff312 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff312 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CX20 ∷ []) (pw1 c4 (CX20 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX20 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff301 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ Toff301 ∷ []) (Toff301 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff301 ∷ CX12 ∷ []) (lw4 c4 (CX12 ∷ Toff301 ∷ []) (Toff301 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff301 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF301 c4) ▸ done

  b1 : Chain (Toff301 ∷ CCZ234 ∷ CX20 ∷ Toff312 ∷ CS24 ∷ CX12 ∷ Toff301 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ234 ∷ CX20 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ [])
  b1 = at 5 2 (Toff301 ∷ CX12 ∷ []) (lw4 c4 (CX12 ∷ Toff301 ∷ []) (Toff301 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff301 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF301 c4) ▸
       at 5 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff301 ∷ Toff312 ∷ []) (lw4 c4 (Toff312 ∷ Toff301 ∷ []) (Toff301 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff301 ∷ CX20 ∷ Toff312 ∷ []) (lw4 c4 (CX20 ∷ Toff301 ∷ []) (Toff301 ∷ CX20 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX20 ∷ []) (lw4 c4 (CX20 ∷ Toff312 ∷ Toff312 ∷ []) (CX20 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ CX20 ∷ []) (pw1 c4 (CX20 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX20 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ []) (Bx3-1024 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx3-1024 ∷ []) (sym (lem-box-tQ-at032032 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (pw3 c4 (CX20 ∷ CCZ124 ∷ CX20 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @032032: 11 steps
lem-SWbc-box-at032032 : Complete 4 → ⟪ (Sw02 ∷ Bx3-1024 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-SWbc-box-at032032 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw02 ∷ Bx3-1024 ∷ Sw02 ∷ []) (CX02 ∷ Bx3-1024 ∷ CX02 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX02 ∷ CX20 ∷ CX02 ∷ []) (lw4 c4 (Sw02 ∷ []) (CX02 ∷ CX20 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX02 ∷ CX20 ∷ CX02 ∷ []) (lw4 c4 (Sw02 ∷ []) (CX02 ∷ CX20 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx3-1024 ∷ CCZ014 ∷ []) (lem-CXbc-box-at032032 c4) ▸
       at 3 2 (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CX20 ∷ []) (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx3-1024 ∷ CCZ124 ∷ []) (lem-CXcb-box-at032032 c4) ▸
       at 4 2 (CX02 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CX02 ∷ []) (CX02 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX02 ∷ CCZ014 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CX02 ∷ []) (CX02 ∷ CCZ014 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX02 ∷ CCZ014 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CX02 ∷ []) (CX02 ∷ CCZ014 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX02 ∷ Bx3-1024 ∷ CX02 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ []) (Bx3-1024 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx3-1024 ∷ CCZ014 ∷ []) (lem-CXbc-box-at032032 c4) ▸
       at 1 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @032032: 23 steps
lem-nat-SWbc-at032032 : Complete 4 → ⟪ (Sw02 ∷ Bx3-1024 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-nat-SWbc-at032032 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw02 ∷ Bx3-1024 ∷ Sw02 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ Sw02 ∷ CCZ123 ∷ Bx3-14 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ Sw02 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ CCZ013 ∷ []) (CCZ123 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ Toff301 ∷ []) (Toff312 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 2 2 (CCZ013 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ CCZ123 ∷ []) (CCZ013 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff103 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ Toff123 ∷ []) (Toff103 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ c4) ▸
       at 5 2 (Toff103 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ Toff123 ∷ []) (Toff103 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ Sw02 ∷ CCZ123 ∷ Bx3-14 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ Sw02 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ Toff312 ∷ CCZ123 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Sw02 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ Sw02 ∷ [])
  b1 = at 6 2 (CCZ013 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ CCZ123 ∷ []) (CCZ013 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ c4) ▸
       at 8 2 (Toff312 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ Toff301 ∷ []) (Toff312 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ123 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ CCZ013 ∷ []) (CCZ123 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 10 2 (CCZ013 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ CCZ123 ∷ []) (CCZ013 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff103 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ Toff123 ∷ []) (Toff103 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ c4) ▸ done

  b2 : Chain (CCZ123 ∷ Toff312 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ Toff312 ∷ CCZ123 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Sw02 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ Sw02 ∷ []) (Bx3-1204 ∷ [])
  b2 = at 13 2 (Toff103 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ Toff123 ∷ []) (Toff103 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ013 ∷ Sw02 ∷ []) (lw4 c4 (Sw02 ∷ CCZ123 ∷ []) (CCZ013 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ c4) ▸
       at 16 2 [] (lw4 c4 (Sw02 ∷ Sw02 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx1-304 ∷ []) (refl) ▸
       at 5 6 (Bx1-304 ∷ []) (refl) ▸
       at 0 6 (Bx3-1204 ∷ []) (refl) ▸ done


-- sym-bc @032032: 2 steps
lem-sym-bc-at032032 : Complete 4 → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-sym-bc-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Bx3-1204 ∷ [])
  b0 = at 0 1 (Sw02 ∷ Bx3-1024 ∷ Sw02 ∷ []) (sym (lem-SWbc-box-at032032 c4)) ▸
       at 0 3 (Bx3-1204 ∷ []) (lem-nat-SWbc-at032032 c4) ▸ done


-- box-perm-2314 @03102132: 2 steps
lem-box-perm-2314-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-box-perm-2314-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-1204 ∷ [])
  b0 = at 0 1 (Bx3-1024 ∷ []) (lem-sym-ab-at03102132 c4) ▸
       at 0 1 (Bx3-1204 ∷ []) (lem-sym-bc-at032032 c4) ▸ done


-- CSu-box-3 @043043: 17 steps
lem-CSu-box-3-at043043 : Complete 4 → ⟪ (CS04 ∷ Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ CS04 ∷ []) ⟫ʷ
lem-CSu-box-3-at043043 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS04 ∷ Bx4-1203 ∷ []) (CCZ124 ∷ Toff403 ∷ CS04 ∷ CS03 ∷ CS03 ∷ CCZ124 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ Toff403 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at043043 c4) ▸
       at 0 2 (CCZ124 ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ CCZ124 ∷ []) (CCZ124 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff403 ∷ CS04 ∷ CS03 ∷ CCZ034 ∷ []) (pw1 c4 (CS04 ∷ Toff403 ∷ []) (Toff403 ∷ CS04 ∷ CS03 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ124 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ CCZ124 ∷ []) (CCZ124 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ124 ∷ CX40 ∷ []) (pw3 c4 (CX40 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX40 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 c4) ▸
       at 5 2 (CCZ124 ∷ CX40 ∷ []) (pw3 c4 (CX40 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX40 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff403 ∷ CS04 ∷ CS03 ∷ CS03 ∷ CCZ124 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ Toff403 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CS04 ∷ [])
  b1 = at 4 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 c4) ▸
       at 5 5 (CCZ034 ∷ []) (pw1 c4 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 c4) ▸
       at 2 2 (CCZ124 ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ CCZ124 ∷ []) (CCZ124 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff403 ∷ CZ03 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ Toff403 ∷ []) (Toff403 ∷ CZ03 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff403 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ Toff403 ∷ []) (Toff403 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff403 ∷ CS04 ∷ CS03 ∷ CCZ034 ∷ []) (pw1 c4 (CS04 ∷ Toff403 ∷ []) (Toff403 ∷ CS04 ∷ CS03 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 6 (CS04 ∷ []) (pw1 c4 (CS04 ∷ CS03 ∷ CCZ034 ∷ CS03 ∷ CZ03 ∷ CCZ034 ∷ []) (CS04 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CS04 ∷ []) (Bx4-1203 ∷ CS04 ∷ [])
  b2 = at 0 4 (Bx4-1203 ∷ []) (sym (lem-box-cP-at043043 c4)) ▸ done


-- t-cP @043043: 5 steps
lem-t-cP-at043043 : Complete 4 → ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ Toff412 ∷ []) ⟫ʷ
lem-t-cP-at043043 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ Toff412 ∷ [])
  b0 = at 0 2 (CCZ124 ∷ Toff412 ∷ CZ12 ∷ []) (lw0 c4 (Toff412 ∷ CCZ124 ∷ []) (CCZ124 ∷ Toff412 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff403 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF403 c4) ▸
       at 1 2 (Toff403 ∷ Toff412 ∷ []) (lem-tP-at043043 c4) ▸
       at 2 3 (CCZ124 ∷ Toff412 ∷ []) (lw0 c4 (Toff412 ∷ CZ12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff403 ∷ Toff412 ∷ []) (lem-tP-at043043 c4) ▸ done


-- box2 @043043: 11 steps
lem-box2-at043043 : Complete 4 → ⟪ (Bx4-1203 ∷ Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at043043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-1203 ∷ Bx4-1203 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ [])
  b0 = at 0 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at043043 c4) ▸
       at 4 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at043043 c4) ▸
       at 4 0 (Toff412 ∷ Toff412 ∷ []) (lw0 c4 [] (Toff412 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ Toff412 ∷ []) (lem-t-cP-at043043 c4) ▸
       at 5 4 (Bx4-1203 ∷ []) (sym (lem-box-cP-at043043 c4)) ▸
       at 5 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at043043 c4) ▸
       at 4 2 [] (lw0 c4 (Toff412 ∷ Toff412 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 [] (pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl) ▸ done

  b1 : Chain (Toff412 ∷ CCZ034 ∷ Toff412 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) []
  b1 = at 2 2 [] (lw0 c4 (Toff412 ∷ Toff412 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 [] (pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Toff412 ∷ Toff412 ∷ []) [] tt tt Eq.refl) ▸ done


-- CXbc-box @0330: 17 steps
lem-CXbc-box-at0330 : Complete 4 → ⟪ (CX20 ∷ Bx3-1204 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at0330 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX20 ∷ Bx3-1204 ∷ CX20 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CX20 ∷ CCZ234 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ CX20 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at0330 c4) ▸
       at 0 2 (Toff312 ∷ CX20 ∷ []) (lw4 c4 (CX20 ∷ Toff312 ∷ []) (Toff312 ∷ CX20 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) (pw1 c4 (CX20 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff312 ∷ CCZ234 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ234 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ234 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff312 ∷ CX20 ∷ []) (lw4 c4 (CX20 ∷ Toff312 ∷ []) (Toff312 ∷ CX20 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ034 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸ done

  b1 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CX20 ∷ CCZ234 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ CX20 ∷ []) (Bx3-1204 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ [])
  b1 = at 7 2 (CCZ034 ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 5 2 (CCZ034 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ234 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) (pw1 c4 (CX20 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX20 ∷ []) (pw1 c4 (CX20 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX20 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx3-1204 ∷ []) (sym (lem-box-tQ-at0330 c4)) ▸ done

  b2 : Chain (Bx3-1204 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ []) (Bx3-1204 ∷ CCZ124 ∷ [])
  b2 = at 1 3 (CCZ124 ∷ []) (pw3 c4 (CX20 ∷ CCZ124 ∷ CX20 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @0330: 18 steps
lem-CXcb-box-at0330 : Complete 4 → ⟪ (CX02 ∷ Bx3-1204 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at0330 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX02 ∷ Bx3-1204 ∷ CX02 ∷ []) (Toff312 ∷ CCZ034 ∷ CX02 ∷ Toff301 ∷ CS04 ∷ CX10 ∷ Toff312 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ CCZ034 ∷ CX02 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at0330 c4) ▸
       at 0 2 (Toff312 ∷ CX02 ∷ Toff301 ∷ []) (lw4 c4 (CX02 ∷ Toff312 ∷ []) (Toff312 ∷ CX02 ∷ Toff301 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ Toff301 ∷ CCZ014 ∷ []) (pw2 c4 (Toff301 ∷ CCZ034 ∷ []) (CCZ034 ∷ Toff301 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CX02 ∷ []) (pw1 c4 (CX02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff312 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ Toff312 ∷ []) (Toff312 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff312 ∷ CX10 ∷ []) (lw4 c4 (CX10 ∷ Toff312 ∷ []) (Toff312 ∷ CX10 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff312 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF312 c4) ▸ done

  b1 : Chain (Toff312 ∷ CCZ034 ∷ CX02 ∷ Toff301 ∷ CS04 ∷ CX10 ∷ Toff312 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ CCZ034 ∷ CX02 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CX02 ∷ CCZ014 ∷ CX02 ∷ [])
  b1 = at 5 2 (Toff312 ∷ CX10 ∷ []) (lw4 c4 (CX10 ∷ Toff312 ∷ []) (Toff312 ∷ CX10 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff312 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF312 c4) ▸
       at 5 5 (CCZ014 ∷ []) (pw2 c4 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff312 ∷ Toff301 ∷ []) (lw4 c4 (Toff301 ∷ Toff312 ∷ []) (Toff312 ∷ Toff301 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff312 ∷ CX02 ∷ Toff301 ∷ []) (lw4 c4 (CX02 ∷ Toff312 ∷ []) (Toff312 ∷ CX02 ∷ Toff301 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX02 ∷ []) (lw4 c4 (CX02 ∷ Toff301 ∷ Toff301 ∷ []) (CX02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX02 ∷ []) (pw1 c4 (CX02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX02 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CX02 ∷ CCZ014 ∷ CX02 ∷ []) (Bx3-1204 ∷ CCZ014 ∷ [])
  b2 = at 0 4 (Bx3-1204 ∷ []) (sym (lem-box-tQ-at0330 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (pw3 c4 (CX02 ∷ CCZ014 ∷ CX02 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @0330: 11 steps
lem-SWbc-box-at0330 : Complete 4 → ⟪ (Sw02 ∷ Bx3-1204 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-SWbc-box-at0330 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw02 ∷ Bx3-1204 ∷ Sw02 ∷ []) (CX20 ∷ Bx3-1204 ∷ CX20 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX20 ∷ CX02 ∷ CX20 ∷ []) (lw4 c4 (Sw02 ∷ []) (CX20 ∷ CX02 ∷ CX20 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX20 ∷ CX02 ∷ CX20 ∷ []) (lw4 c4 (Sw02 ∷ []) (CX20 ∷ CX02 ∷ CX20 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx3-1204 ∷ CCZ124 ∷ []) (lem-CXbc-box-at0330 c4) ▸
       at 3 2 (CX02 ∷ CCZ014 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CX02 ∷ []) (CX02 ∷ CCZ014 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx3-1204 ∷ CCZ014 ∷ []) (lem-CXcb-box-at0330 c4) ▸
       at 4 2 (CX20 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CX20 ∷ []) (CX20 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CX20 ∷ []) (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CX20 ∷ []) (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX20 ∷ Bx3-1204 ∷ CX20 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ []) (Bx3-1204 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx3-1204 ∷ CCZ124 ∷ []) (lem-CXbc-box-at0330 c4) ▸
       at 1 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸ done


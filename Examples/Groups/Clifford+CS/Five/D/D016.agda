{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D016 where

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
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-box-tQ-at13243142 ; lem-cQ-at13243142)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-box-tQ-at13213442)
open import Examples.Groups.Clifford+CS.Five.D.D015 using (lem-cQ-at233442)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CZ12-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CSd24-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-CZ13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-comm-SWAP14-BOX⟨0·32⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-comm-CX31-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-TOFF034-CSd12)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-comm-CS24-TOFF013)
-- box-tQ @233442: 13 steps
lem-box-tQ-at233442 : Complete 4 → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at233442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1342 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (pw3 c4 (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (pw3 c4 (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff013 ∷ CCZ013 ∷ CZ13 ∷ []) (lw4 c4 (CCZ013 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ013 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 c4) ▸
       at 1 2 (CCZ024 ∷ CCZ013 ∷ []) (lem-cQ-at233442 c4) ▸
       at 2 4 (Toff013 ∷ []) (lw4 c4 (CCZ013 ∷ CZ13 ∷ Toff013 ∷ CCZ013 ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸ done


-- cQ @021021: 7 steps
lem-cQ-at021021 : Complete 4 → ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at021021 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS12 ∷ []) (lw0 c4 (CS12 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- tP @021021: 7 steps
lem-tP-at021021 : Complete 4 → ⟪ (Toff201 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ []) ⟫ʷ
lem-tP-at021021 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Toff234 ∷ []) (Toff234 ∷ Toff201 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (lw4 c4 (Toff201 ∷ []) (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (lw0 c4 (Toff234 ∷ []) (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-cQ-at021021 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff234 ∷ []) (lw0 c4 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (Toff234 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff201 ∷ []) (lw4 c4 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (Toff201 ∷ []) tt tt Eq.refl) ▸ done


-- VPQ @021021: 14 steps
lem-VPQ-at021021 : Complete 4 → ⟪ (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at021021 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (CS34⁻ ∷ CS01⁻ ∷ S2 ∷ Toff234 ∷ Toff201 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) (lw4 c4 (Toff201 ∷ CCZ012 ∷ []) (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) (lw0 c4 (Toff234 ∷ CCZ234 ∷ []) (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ S2⁻ ∷ []) (c₃ ((S • S • S) ↑ ↑) (CS • CS • CS)) ▸
       at 2 2 (CS34⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS • CS • CS)) ▸
       at 1 2 (CS34⁻ ∷ S2 ∷ []) (c₃ (S ↑ ↑) (CS • CS • CS)) ▸
       at 0 2 (CS34⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((CS • CS • CS) ↑)) ▸
       at 4 2 [] (lw4 c4 (S2⁻ ∷ S2 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff234 ∷ Toff201 ∷ []) (lem-tP-at021021 c4) ▸ done

  b1 : Chain (CS34⁻ ∷ CS01⁻ ∷ S2 ∷ Toff234 ∷ Toff201 ∷ S2⁻ ∷ []) (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (lw4 c4 [] (S2⁻ ∷ S2 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S2 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S)) ▸
       at 2 2 (Toff234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toff)) ▸
       at 3 2 (S2⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S • S • S)) ▸
       at 0 4 (Toff234 ∷ CCZ234 ∷ []) (lw0 c4 (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) (Toff234 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff201 ∷ CCZ012 ∷ []) (lw4 c4 (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) (Toff201 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @021021: 3 steps
lem-QVQ-at021021 : Complete 4 → ⟪ (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-QVQ-at021021 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ [])
  b0 = at 0 0 (Toff234 ∷ Toff234 ∷ []) (lw0 c4 [] (Toff234 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at021021 c4)) ▸
       at 4 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @021021: 12 steps
lem-box-cP-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-box-cP-at021021 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0134 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (pw1 c4 (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (pw1 c4 (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-QVQ-at021021 c4) ▸
       at 1 2 (Toff234 ∷ Toff201 ∷ []) (lem-tP-at021021 c4) ▸
       at 2 2 [] (lw4 c4 (Toff201 ∷ Toff201 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym-ab @233442: 18 steps
lem-sym-ab-at233442 : Complete 4 → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-sym-ab-at233442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-1342 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (pw3 c4 (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-32 ∷ []) (refl) ▸
       at 7 1 (Bx0-32 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ [])
  b1 = at 2 6 (Bx3-042 ∷ []) (refl) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (pw3 c4 (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx0-32 ∷ []) (refl) ▸
       at 10 1 (Bx0-32 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (Bx0-3142 ∷ [])
  b2 = at 5 6 (Bx3-042 ∷ []) (refl) ▸
       at 0 6 (Bx0-3142 ∷ []) (refl) ▸ done


-- CXbc-box @13213442: 17 steps
lem-CXbc-box-at13213442 : Complete 4 → ⟪ (CX14 ∷ Bx0-3142 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at13213442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx0-3142 ∷ CX14 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX14 ∷ CCZ012 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CCZ024 ∷ CX31 ∷ CS23 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at13213442 c4) ▸
       at 0 2 (Toff013 ∷ CX14 ∷ []) (pw2 c4 (CX14 ∷ Toff013 ∷ []) (Toff013 ∷ CX14 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CX14 ∷ CCZ012 ∷ []) (pw3 c4 (CX14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX14 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ CCZ012 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ012 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ012 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff013 ∷ CX14 ∷ []) (pw2 c4 (CX14 ∷ Toff013 ∷ []) (Toff013 ∷ CX14 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 c4) ▸ done

  b1 : Chain (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX14 ∷ CCZ012 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CCZ024 ∷ CX31 ∷ CS23 ∷ CX14 ∷ []) (Bx0-3142 ∷ CX14 ∷ CCZ123 ∷ CX14 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ123 ∷ []) (lw4 c4 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CX14 ∷ CCZ012 ∷ []) (pw3 c4 (CX14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX14 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX14 ∷ []) (pw3 c4 (CX14 ∷ CCZ012 ∷ CCZ012 ∷ []) (CX14 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-3142 ∷ []) (sym (lem-box-tQ-at13213442 c4)) ▸ done

  b2 : Chain (Bx0-3142 ∷ CX14 ∷ CCZ123 ∷ CX14 ∷ []) (Bx0-3142 ∷ CCZ123 ∷ [])
  b2 = at 1 3 (CCZ123 ∷ []) (lw0 c4 (CX14 ∷ CCZ123 ∷ CX14 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @13213442: 18 steps
lem-CXcb-box-at13213442 : Complete 4 → ⟪ (CX41 ∷ Bx0-3142 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXcb-box-at13213442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx0-3142 ∷ CX41 ∷ []) (Toff013 ∷ CCZ024 ∷ CX41 ∷ Toff034 ∷ CS24 ∷ CX34 ∷ Toff013 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ CCZ024 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at13213442 c4) ▸
       at 0 2 (Toff013 ∷ CX41 ∷ Toff034 ∷ []) (pw2 c4 (CX41 ∷ Toff013 ∷ []) (Toff013 ∷ CX41 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) (pw1 c4 (Toff034 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CX41 ∷ []) (pw3 c4 (CX41 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff013 ∷ CS23 ∷ []) (lw4 c4 (CS23 ∷ Toff013 ∷ []) (Toff013 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff013 ∷ CX34 ∷ []) (pw2 c4 (CX34 ∷ Toff013 ∷ []) (Toff013 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 c4) ▸ done

  b1 : Chain (Toff013 ∷ CCZ024 ∷ CX41 ∷ Toff034 ∷ CS24 ∷ CX34 ∷ Toff013 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ CCZ024 ∷ CX41 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CX41 ∷ CCZ234 ∷ CX41 ∷ [])
  b1 = at 5 2 (Toff013 ∷ CX34 ∷ []) (pw2 c4 (CX34 ∷ Toff013 ∷ []) (Toff013 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff013 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF013 c4) ▸
       at 5 5 (CCZ234 ∷ []) (lw0 c4 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ Toff034 ∷ []) (pw2 c4 (Toff034 ∷ Toff013 ∷ []) (Toff013 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff013 ∷ CX41 ∷ Toff034 ∷ []) (pw2 c4 (CX41 ∷ Toff013 ∷ []) (Toff013 ∷ CX41 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX41 ∷ []) (pw2 c4 (CX41 ∷ Toff034 ∷ Toff034 ∷ []) (CX41 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ234 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CX41 ∷ []) (pw3 c4 (CX41 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX41 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CX41 ∷ CCZ234 ∷ CX41 ∷ []) (Bx0-3142 ∷ CCZ234 ∷ [])
  b2 = at 0 4 (Bx0-3142 ∷ []) (sym (lem-box-tQ-at13213442 c4)) ▸
       at 1 3 (CCZ234 ∷ []) (lw0 c4 (CX41 ∷ CCZ234 ∷ CX41 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @13213442: 11 steps
lem-SWbc-box-at13213442 : Complete 4 → ⟪ (Sw14 ∷ Bx0-3142 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-SWbc-box-at13213442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx0-3142 ∷ Sw14 ∷ []) (CX14 ∷ Bx0-3142 ∷ CX14 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (lw0 c4 (Sw14 ∷ []) (CX14 ∷ CX41 ∷ CX14 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (lw0 c4 (Sw14 ∷ []) (CX14 ∷ CX41 ∷ CX14 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx0-3142 ∷ CCZ123 ∷ []) (lem-CXbc-box-at13213442 c4) ▸
       at 3 2 (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CX41 ∷ []) (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-3142 ∷ CCZ234 ∷ []) (lem-CXcb-box-at13213442 c4) ▸
       at 4 2 (CX14 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CX14 ∷ []) (CX14 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CX14 ∷ []) (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CX14 ∷ []) (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX14 ∷ Bx0-3142 ∷ CX14 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ []) (Bx0-3142 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx0-3142 ∷ CCZ123 ∷ []) (lem-CXbc-box-at13213442 c4) ▸
       at 1 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @13213442: 23 steps
lem-nat-SWbc-at13213442 : Complete 4 → ⟪ (Sw14 ∷ Bx0-3142 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-nat-SWbc-at13213442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx0-3142 ∷ Sw14 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ Sw14 ∷ CCZ034 ∷ Bx0-32 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ CCZ013 ∷ []) (CCZ034 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff034 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ Toff013 ∷ []) (Toff034 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 2 2 (CCZ013 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ CCZ034 ∷ []) (CCZ013 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff301 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ Toff304 ∷ []) (Toff301 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ c4) ▸
       at 5 2 (Toff301 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ Toff304 ∷ []) (Toff301 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ Sw14 ∷ CCZ034 ∷ Bx0-32 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ Sw14 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ Toff034 ∷ CCZ034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Sw14 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ013 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ CCZ034 ∷ []) (CCZ013 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ c4) ▸
       at 8 2 (Toff034 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ Toff013 ∷ []) (Toff034 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ034 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ CCZ013 ∷ []) (CCZ034 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 10 2 (CCZ013 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ CCZ034 ∷ []) (CCZ013 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff301 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ Toff304 ∷ []) (Toff301 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ c4) ▸ done

  b2 : Chain (CCZ034 ∷ Toff034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ Toff034 ∷ CCZ034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Sw14 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ Sw14 ∷ []) (Bx0-3412 ∷ [])
  b2 = at 13 2 (Toff301 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ Toff304 ∷ []) (Toff301 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ013 ∷ Sw14 ∷ []) (pw2 c4 (Sw14 ∷ CCZ034 ∷ []) (CCZ013 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ c4) ▸
       at 16 2 [] (lw0 c4 (Sw14 ∷ Sw14 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx3-012 ∷ []) (refl) ▸
       at 5 6 (Bx3-012 ∷ []) (refl) ▸
       at 0 6 (Bx0-3412 ∷ []) (refl) ▸ done


-- sym-bc @13213442: 2 steps
lem-sym-bc-at13213442 : Complete 4 → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-sym-bc-at13213442 c4 = run b0
  where
  b0 : Chain (Bx0-3142 ∷ []) (Bx0-3412 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx0-3142 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at13213442 c4)) ▸
       at 0 3 (Bx0-3412 ∷ []) (lem-nat-SWbc-at13213442 c4) ▸ done


-- tP @13243142: 7 steps
lem-tP-at13243142 : Complete 4 → ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ
lem-tP-at13243142 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Toff012 ∷ []) (Toff012 ∷ Toff034 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (pw1 c4 (Toff034 ∷ []) (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at13243142 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff034 ∷ []) (pw1 c4 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (Toff034 ∷ []) tt tt Eq.refl) ▸ done


-- P-box @13243142: 8 steps
lem-P-box-at13243142 : Complete 4 → ⟪ (Toff012 ∷ Bx0-3412 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-P-box-at13243142 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Bx0-3412 ∷ Toff012 ∷ []) (Bx0-3412 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at13243142 c4) ▸
       at 0 2 (Toff034 ∷ Toff012 ∷ []) (sym (lem-tP-at13243142 c4)) ▸
       at 1 2 (CCZ012 ∷ CZ12 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ CCZ012 ∷ []) (CCZ012 ∷ CZ12 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ Toff012 ∷ []) (sym (lem-tP-at13243142 c4)) ▸
       at 4 3 (CCZ012 ∷ CZ12 ∷ []) (lw4 c4 (Toff012 ∷ CCZ012 ∷ Toff012 ∷ []) (CCZ012 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff034 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF034 c4) ▸
       at 3 3 (CCZ012 ∷ []) (lw4 c4 (CZ12 ∷ CCZ012 ∷ CZ12 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-3412 ∷ []) (sym (lem-box-tQ-at13243142 c4)) ▸ done


-- VPQ @13243142: 14 steps
lem-VPQ-at13243142 : Complete 4 → ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at13243142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (CS12⁻ ∷ CS34⁻ ∷ S0 ∷ Toff012 ∷ Toff034 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (pw1 c4 (Toff034 ∷ CCZ034 ∷ []) (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (lw4 c4 (Toff012 ∷ CCZ012 ∷ []) (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS12⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (CS • CS • CS)) ▸
       at 2 2 (CS12⁻ ∷ Toff034 ∷ []) (lem-comm-TOFF034-CSd12 c4) ▸
       at 1 2 (CS12⁻ ∷ S0 ∷ []) (c₁ (S) (CS • CS • CS)) ▸
       at 0 2 (CS12⁻ ∷ CS34⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (CS • CS • CS))) ▸
       at 4 2 [] (lw4 c4 (S0⁻ ∷ S0 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ Toff034 ∷ []) (lem-tP-at13243142 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS34⁻ ∷ S0 ∷ Toff012 ∷ Toff034 ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (lw4 c4 [] (S0⁻ ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ CS34⁻ ∷ []) (sym (c₁ (S) ((CS • CS • CS) ↑ ↑))) ▸
       at 2 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸
       at 3 2 (S0⁻ ∷ CS34⁻ ∷ []) (sym (c₁ (S • S • S) ((CS • CS • CS) ↑ ↑))) ▸
       at 0 4 (Toff012 ∷ CCZ012 ∷ []) (lw4 c4 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff034 ∷ CCZ034 ∷ []) (pw1 c4 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @13243142: 3 steps
lem-QVQ-at13243142 : Complete 4 → ⟪ (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-QVQ-at13243142 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ [])
  b0 = at 0 0 (Toff012 ∷ Toff012 ∷ []) (lw4 c4 [] (Toff012 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (sym (lem-VPQ-at13243142 c4)) ▸
       at 4 2 [] (lw4 c4 (CCZ012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸ done


{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D017 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-tQ)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-box-tQ-at14233142)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-box-tQ-at3443 ; lem-cQ-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-box-perm-1342)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-P-box-at13243142 ; lem-QVQ-at13243142 ; lem-box-cP-at021021 ; lem-box-tQ-at233442 ; lem-sym-ab-at233442 ; lem-sym-bc-at13213442 ; lem-tP-at13243142)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CSd12-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-comm-TOFF301-CSd24)
-- box-cP @13243142: 12 steps
lem-box-cP-at13243142 : Complete 4 → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-box-cP-at13243142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3412 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (lw4 c4 (CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (lw4 c4 (CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-QVQ-at13243142 c4) ▸
       at 1 2 (Toff012 ∷ Toff034 ∷ []) (lem-tP-at13243142 c4) ▸
       at 2 2 [] (pw1 c4 (Toff034 ∷ Toff034 ∷ []) [] tt tt Eq.refl) ▸ done


-- pairs @13243142: 4 steps
lem-pairs-at13243142 : Complete 4 → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-pairs-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Toff012 ∷ Bx0-3412 ∷ Toff012 ∷ []) (sym (lem-P-box-at13243142 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-box-cP-at13243142 c4) ▸
       at 4 2 [] (lw4 c4 (Toff012 ∷ Toff012 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done


-- box-perm-1423 @233442: 3 steps
lem-box-perm-1423-at233442 : Complete 4 → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-1423-at233442 c4 = run b0
  where
  b0 : Chain (Bx0-1342 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-3142 ∷ []) (lem-sym-ab-at233442 c4) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-sym-bc-at13213442 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-pairs-at13243142 c4) ▸ done


-- box-box-2: 105 steps
lem-box-box-2 : Complete 4 → ⟪ (Bx0-1234 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-box-box-2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx0-1234 ∷ Bx2-0134 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CCZ012 ∷ CX03 ∷ CS04 ∷ Toff234 ∷ [])
  b0 = at 0 1 (Bx0-1342 ∷ []) (lem-box-perm-1342 c4) ▸
       at 0 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at233442 c4) ▸
       at 4 1 (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at021021 c4) ▸
       at 3 2 (CCZ012 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff234 ∷ CCZ024 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ024 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ024 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ012 ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ012 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX03 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CCZ012 ∷ CX03 ∷ CS04 ∷ Toff234 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ [])
  b1 = at 8 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 7 2 (CCZ012 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 7 5 (CCZ034 ∷ []) (pw1 c4 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (Toff234 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CCZ034 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx2-0134 ∷ []) (sym (lem-box-cP-at021021 c4)) ▸
       at 3 1 (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at021021 c4) ▸ done

  b2 : Chain (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ []) (Toff013 ∷ CCZ024 ∷ CCZ012 ∷ K0 ∷ CS13 ∷ Toff234 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ CCZ123 ∷ CCZ134 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ [])
  b2 = at 2 2 (CCZ012 ∷ Toff013 ∷ CCZ123 ∷ []) (lw4 c4 (Toff013 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff234 ∷ CCZ123 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ123 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ123 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff234 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toff ↑)) ▸
       at 8 2 (Toff234 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ Toff234 ∷ []) (Toff234 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toff)) ▸
       at 6 2 (Toff234 ∷ CS13⁻ ∷ []) (lw0 c4 (CS13⁻ ∷ Toff234 ∷ []) (Toff234 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toff)) ▸ done

  b3 : Chain (Toff013 ∷ CCZ024 ∷ CCZ012 ∷ K0 ∷ CS13 ∷ Toff234 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ CCZ123 ∷ CCZ134 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ []) (Toff013 ∷ CCZ024 ∷ CCZ012 ∷ Toff234 ∷ Toff013 ∷ CCZ123 ∷ CS34 ∷ CCZ012 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff234 ∷ CCZ024 ∷ [])
  b3 = at 4 2 (Toff234 ∷ CS13 ∷ []) (lw0 c4 (CS13 ∷ Toff234 ∷ []) (Toff234 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff234 ∷ K0 ∷ []) (c₁ (K) (Toff ↑)) ▸
       at 4 7 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ012 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ012 ∷ CX13 ∷ []) (lw4 c4 (CX13 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 7 2 (CCZ012 ∷ CX13 ∷ []) (lw4 c4 (CX13 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX13 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Toff013 ∷ CCZ024 ∷ CCZ012 ∷ Toff234 ∷ Toff013 ∷ CCZ123 ∷ CS34 ∷ CCZ012 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff234 ∷ CCZ024 ∷ []) (Toff013 ∷ CCZ024 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff234 ∷ K0⁻ ∷ CCZ134 ∷ CCZ024 ∷ [])
  b4 = at 6 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 7 5 (CCZ134 ∷ []) (lw0 c4 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Toff013 ∷ CCZ123 ∷ []) (lw4 c4 (Toff013 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CCZ123 ∷ CCZ123 ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff234 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff234 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toff ↑)) ▸ done

  b5 : Chain (Toff013 ∷ CCZ024 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff234 ∷ K0⁻ ∷ CCZ134 ∷ CCZ024 ∷ []) (Toff013 ∷ CCZ024 ∷ Bx2-0134 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b5 = at 10 2 (Toff234 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ Toff234 ∷ []) (Toff234 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toff)) ▸
       at 8 2 (Toff234 ∷ CS13⁻ ∷ []) (lw0 c4 (CS13⁻ ∷ Toff234 ∷ []) (Toff234 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toff)) ▸
       at 6 2 (Toff234 ∷ CS13 ∷ []) (lw0 c4 (CS13 ∷ Toff234 ∷ []) (Toff234 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff234 ∷ K0 ∷ []) (c₁ (K) (Toff ↑)) ▸
       at 6 7 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx2-0134 ∷ []) (sym (lem-box-cP-at021021 c4)) ▸ done

  b6 : Chain (Toff013 ∷ CCZ024 ∷ Bx2-0134 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ []) (Toff013 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff234 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b6 = at 2 1 (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at021021 c4) ▸
       at 1 2 (CCZ012 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff234 ∷ CCZ024 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ024 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ024 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ012 ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ012 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 5 2 (CCZ012 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX03 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (Toff013 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff234 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ []) (CCZ012 ∷ Toff013 ∷ Toff234 ∷ CCZ123 ∷ CCZ134 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b7 = at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ034 ∷ []) (pw1 c4 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (Toff234 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CCZ034 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Bx2-0134 ∷ []) (sym (lem-box-cP-at021021 c4)) ▸
       at 1 1 (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at021021 c4) ▸
       at 0 2 (CCZ012 ∷ Toff013 ∷ CCZ123 ∷ []) (lw4 c4 (Toff013 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff234 ∷ CCZ123 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ123 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ123 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (CCZ012 ∷ Toff013 ∷ Toff234 ∷ CCZ123 ∷ CCZ134 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ []) (CCZ012 ∷ Toff234 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ CCZ123 ∷ CCZ134 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b8 = at 1 1 (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff234 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toff ↑)) ▸
       at 6 2 (Toff234 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ Toff234 ∷ []) (Toff234 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toff)) ▸
       at 4 2 (Toff234 ∷ CS13⁻ ∷ []) (lw0 c4 (CS13⁻ ∷ Toff234 ∷ []) (Toff234 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toff)) ▸
       at 2 2 (Toff234 ∷ CS13 ∷ []) (lw0 c4 (CS13 ∷ Toff234 ∷ []) (Toff234 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ K0 ∷ []) (c₁ (K) (Toff ↑)) ▸ done

  b9 : Chain (CCZ012 ∷ Toff234 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ CCZ123 ∷ CCZ134 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ []) (CCZ012 ∷ Toff234 ∷ Toff013 ∷ CCZ123 ∷ CCZ012 ∷ CCZ134 ∷ Toff234 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b9 = at 2 7 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ012 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ012 ∷ CX13 ∷ []) (lw4 c4 (CX13 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 5 2 (CCZ012 ∷ CX13 ∷ []) (lw4 c4 (CX13 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ134 ∷ []) (lw0 c4 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (CCZ012 ∷ Toff234 ∷ Toff013 ∷ CCZ123 ∷ CCZ012 ∷ CCZ134 ∷ Toff234 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ []) (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Toff234 ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ CCZ134 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b10 = at 3 2 (CCZ012 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ Toff013 ∷ CCZ123 ∷ []) (lw4 c4 (Toff013 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CCZ123 ∷ CCZ123 ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff234 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff234 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toff ↑)) ▸
       at 8 2 (Toff234 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ Toff234 ∷ []) (Toff234 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toff)) ▸ done

  b11 : Chain (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Toff234 ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ CCZ134 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ []) (Bx2-0134 ∷ Toff013 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b11 = at 6 2 (Toff234 ∷ CS13⁻ ∷ []) (lw0 c4 (CS13⁻ ∷ Toff234 ∷ []) (Toff234 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toff)) ▸
       at 4 2 (Toff234 ∷ CS13 ∷ []) (lw0 c4 (CS13 ∷ Toff234 ∷ []) (Toff234 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff234 ∷ K0 ∷ []) (c₁ (K) (Toff ↑)) ▸
       at 4 7 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-0134 ∷ []) (sym (lem-box-cP-at021021 c4)) ▸
       at 2 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (Bx2-0134 ∷ Toff013 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ []) (Bx2-0134 ∷ Bx0-1342 ∷ [])
  b12 = at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 4 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 2 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 3 5 (CCZ134 ∷ []) (lw0 c4 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Bx0-1342 ∷ []) (sym (lem-box-tQ-at233442 c4)) ▸ done

  b13 : Chain (Bx2-0134 ∷ Bx0-1342 ∷ []) (Bx2-0134 ∷ Bx0-1234 ∷ [])
  b13 = at 1 1 (Bx0-1234 ∷ []) (lem-box-perm-1423-at233442 c4) ▸ done


-- cQ @03102132: 7 steps
lem-cQ-at03102132 : Complete 4 → ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at03102132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS13⁻ ∷ []) (lw0 c4 (CS13⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS13 ∷ []) (lw0 c4 (CS13 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ013 ∷ []) (lw4 c4 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- tP @03102132: 7 steps
lem-tP-at03102132 : Complete 4 → ⟪ (Toff301 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff301 ∷ []) ⟫ʷ
lem-tP-at03102132 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Toff324 ∷ []) (Toff324 ∷ Toff301 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) (lw4 c4 (Toff301 ∷ []) (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CCZ013 ∷ []) (lem-cQ-at03102132 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff301 ∷ []) (lw4 c4 (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) (Toff301 ∷ []) tt tt Eq.refl) ▸ done


-- VPQ @03102132: 14 steps
lem-VPQ-at03102132 : Complete 4 → ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) ⟫ʷ
lem-VPQ-at03102132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (CS24⁻ ∷ CS01⁻ ∷ S3 ∷ Toff324 ∷ Toff301 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (lw4 c4 (Toff301 ∷ CCZ013 ∷ []) (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) (lw0 c4 (Toff324 ∷ CCZ234 ∷ []) (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS24⁻ ∷ S3⁻ ∷ []) (lw0 c4 (S3⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ S3⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS24⁻ ∷ Toff301 ∷ []) (lem-comm-TOFF301-CSd24 c4) ▸
       at 1 2 (CS24⁻ ∷ S3 ∷ []) (lw0 c4 (S3 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ S3 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS24⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 4 2 [] (lw4 c4 (S3⁻ ∷ S3 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at03102132 c4) ▸ done

  b1 : Chain (CS24⁻ ∷ CS01⁻ ∷ S3 ∷ Toff324 ∷ Toff301 ∷ S3⁻ ∷ []) (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (lw4 c4 [] (S3⁻ ∷ S3 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S3 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S ↑)) ▸
       at 2 2 (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 3 2 (S3⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((S • S • S) ↑)) ▸
       at 0 4 (Toff324 ∷ CCZ234 ∷ []) (lw0 c4 (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) (Toff324 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff301 ∷ CCZ013 ∷ []) (lw4 c4 (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (Toff301 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @03102132: 3 steps
lem-QVQ-at03102132 : Complete 4 → ⟪ (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ
lem-QVQ-at03102132 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ [])
  b0 = at 0 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at03102132 c4)) ▸
       at 4 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @03102132: 12 steps
lem-box-cP-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ
lem-box-cP-at03102132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0124 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (pw1 c4 (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (pw1 c4 (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-QVQ-at03102132 c4) ▸
       at 1 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at03102132 c4) ▸
       at 2 2 [] (lw4 c4 (Toff301 ∷ Toff301 ∷ []) [] tt tt Eq.refl) ▸ done


-- tP @3443: 7 steps
lem-tP-at3443 : Complete 4 → ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ
lem-tP-at3443 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Toff034 ∷ []) (Toff034 ∷ Toff012 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (pw1 c4 (Toff034 ∷ []) (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-cQ-at3443 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff034 ∷ []) (pw1 c4 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (Toff034 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸ done


-- P-box @3443: 8 steps
lem-P-box-at3443 : Complete 4 → ⟪ (Toff034 ∷ Bx0-1243 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-P-box-at3443 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Bx0-1243 ∷ Toff034 ∷ []) (Bx0-1243 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at3443 c4) ▸
       at 0 2 (Toff012 ∷ Toff034 ∷ []) (sym (lem-tP-at3443 c4)) ▸
       at 1 2 (CCZ034 ∷ CZ34 ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ34 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ Toff034 ∷ []) (sym (lem-tP-at3443 c4)) ▸
       at 4 3 (CCZ034 ∷ CZ34 ∷ []) (pw1 c4 (Toff034 ∷ CCZ034 ∷ Toff034 ∷ []) (CCZ034 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ CZ34 ∷ []) (sym (c₃ (Toff) (CZ))) ▸
       at 3 3 (CCZ034 ∷ []) (pw1 c4 (CZ34 ∷ CCZ034 ∷ CZ34 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-1243 ∷ []) (sym (lem-box-tQ-at3443 c4)) ▸ done


-- VPQ @3443: 14 steps
lem-VPQ-at3443 : Complete 4 → ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at3443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (CS34⁻ ∷ CS12⁻ ∷ S0 ∷ Toff034 ∷ Toff012 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (lw4 c4 (Toff012 ∷ CCZ012 ∷ []) (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (pw1 c4 (Toff034 ∷ CCZ034 ∷ []) (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑ ↑)) ▸
       at 2 2 (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS)) ▸
       at 1 2 (CS34⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑ ↑)) ▸
       at 0 2 (CS34⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (CS • CS • CS)) ▸
       at 4 2 [] (lw4 c4 (S0⁻ ∷ S0 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP-at3443 c4) ▸ done

  b1 : Chain (CS34⁻ ∷ CS12⁻ ∷ S0 ∷ Toff034 ∷ Toff012 ∷ S0⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (lw4 c4 [] (S0⁻ ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ CS12⁻ ∷ []) (sym (c₁ (S) (CS • CS • CS))) ▸
       at 2 2 (Toff034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF034 c4) ▸
       at 3 2 (S0⁻ ∷ CS12⁻ ∷ []) (sym (c₁ (S • S • S) (CS • CS • CS))) ▸
       at 0 4 (Toff034 ∷ CCZ034 ∷ []) (pw1 c4 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff012 ∷ CCZ012 ∷ []) (lw4 c4 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @3443: 3 steps
lem-QVQ-at3443 : Complete 4 → ⟪ (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-QVQ-at3443 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ [])
  b0 = at 0 0 (Toff034 ∷ Toff034 ∷ []) (pw1 c4 [] (Toff034 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at3443 c4)) ▸
       at 4 2 [] (pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @3443: 12 steps
lem-box-cP-at3443 : Complete 4 → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-box-cP-at3443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1243 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx1-043 ∷ Toff012 ∷ CCZ012 ∷ Bx1-043 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (pw2 c4 (CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (pw2 c4 (CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-QVQ-at3443 c4) ▸
       at 1 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP-at3443 c4) ▸
       at 2 2 [] (lw4 c4 (Toff012 ∷ Toff012 ∷ []) [] tt tt Eq.refl) ▸ done


-- pairs @3443: 4 steps
lem-pairs-at3443 : Complete 4 → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-pairs-at3443 c4 = run b0
  where
  b0 : Chain (Bx0-1243 ∷ []) (Bx0-4312 ∷ [])
  b0 = at 0 1 (Toff034 ∷ Bx0-1243 ∷ Toff034 ∷ []) (sym (lem-P-box-at3443 c4)) ▸
       at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at3443 c4) ▸
       at 4 2 [] (pw1 c4 (Toff034 ∷ Toff034 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx0-4312 ∷ []) (sym (lem-box-tQ-at14233142 c4)) ▸ done


-- sym-ab @14233142: 18 steps
lem-sym-ab-at14233142 : Complete 4 → ⟪ (Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-sym-ab-at14233142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-4312 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (pw3 c4 (CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-32 ∷ []) (refl) ▸
       at 7 1 (Bx0-32 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ [])
  b1 = at 2 6 (Bx3-012 ∷ []) (refl) ▸
       at 5 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸
       at 5 6 (CCZ012 ∷ []) (pw3 c4 (CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx0-32 ∷ []) (refl) ▸
       at 10 1 (Bx0-32 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (Bx0-3412 ∷ [])
  b2 = at 5 6 (Bx3-012 ∷ []) (refl) ▸
       at 0 6 (Bx0-3412 ∷ []) (refl) ▸ done


{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D013 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-cP)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-Kdu-box ; lem-Ku-box ; lem-Sdu-box ; lem-Su-box)
open import Examples.Groups.Clifford+CS.Five.D.D012 using (lem-CKdu-box-2 ; lem-CKu-box-2 ; lem-CSu-box-2)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-CX12-TOFF034)
-- XCSdX-box-2: 4 steps
lem-XCSdX-box-2 : Complete 4 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-XCSdX-box-2 c4 = run b0
  where
  b0 : Chain (X2 ∷ CS02⁻ ∷ X2 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  b0 = at 0 3 (S0⁻ ∷ CS02 ∷ []) (lw4 c4 (X2 ∷ CS02⁻ ∷ X2 ∷ []) (S0⁻ ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CSu-box-2 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0⁻ ∷ []) (lem-Sdu-box c4) ▸
       at 1 2 (X2 ∷ CS02⁻ ∷ X2 ∷ []) (lw4 c4 (S0⁻ ∷ CS02 ∷ []) (X2 ∷ CS02⁻ ∷ X2 ∷ []) tt tt Eq.refl) ▸ done


-- XCKX-box-2: 4 steps
lem-XCKX-box-2 : Complete 4 → ⟪ (X2 ∷ CK20 ∷ X2 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-XCKX-box-2 c4 = run b0
  where
  b0 : Chain (X2 ∷ CK20 ∷ X2 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  b0 = at 0 3 (K0 ∷ CK20⁻ ∷ []) (lw4 c4 (X2 ∷ CK20 ∷ X2 ∷ []) (K0 ∷ CK20⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ CK20⁻ ∷ []) (lem-CKdu-box-2 c4) ▸
       at 0 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 1 2 (X2 ∷ CK20 ∷ X2 ∷ []) (lw4 c4 (K0 ∷ CK20⁻ ∷ []) (X2 ∷ CK20 ∷ X2 ∷ []) tt tt Eq.refl) ▸ done


-- XCKdX-box-2: 4 steps
lem-XCKdX-box-2 : Complete 4 → ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-XCKdX-box-2 c4 = run b0
  where
  b0 : Chain (X2 ∷ CK20⁻ ∷ X2 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  b0 = at 0 3 (K0⁻ ∷ CK20 ∷ []) (lw4 c4 (X2 ∷ CK20⁻ ∷ X2 ∷ []) (K0⁻ ∷ CK20 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ CK20 ∷ []) (lem-CKu-box-2 c4) ▸
       at 0 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 1 2 (X2 ∷ CK20⁻ ∷ X2 ∷ []) (lw4 c4 (K0⁻ ∷ CK20 ∷ []) (X2 ∷ CK20⁻ ∷ X2 ∷ []) tt tt Eq.refl) ▸ done


-- CSu-box-3: 17 steps
lem-CSu-box-3 : Complete 4 → ⟪ (CS03 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS03 ∷ []) ⟫ʷ
lem-CSu-box-3 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS03 ∷ Bx0-1234 ∷ []) (CCZ012 ∷ Toff034 ∷ CS03 ∷ CS34 ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 0 2 (CCZ012 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff034 ∷ CS03 ∷ CS34 ∷ CCZ034 ∷ []) (pw1 c4 (CS03 ∷ Toff034 ∷ []) (Toff034 ∷ CS03 ∷ CS34 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ012 ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ012 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 5 2 (CCZ012 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX03 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff034 ∷ CS03 ∷ CS34 ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff034 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CS03 ∷ [])
  b1 = at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ034 ∷ []) (pw1 c4 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 2 2 (CCZ012 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff034 ∷ CZ34 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ Toff034 ∷ []) (Toff034 ∷ CZ34 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff034 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ Toff034 ∷ []) (Toff034 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ CS03 ∷ CS34 ∷ CCZ034 ∷ []) (pw1 c4 (CS03 ∷ Toff034 ∷ []) (Toff034 ∷ CS03 ∷ CS34 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 6 (CS03 ∷ []) (pw1 c4 (CS03 ∷ CS34 ∷ CCZ034 ∷ CS34 ∷ CZ34 ∷ CCZ034 ∷ []) (CS03 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CS03 ∷ []) (Bx0-1234 ∷ CS03 ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸ done


-- CSdu-box-3: 17 steps
lem-CSdu-box-3 : Complete 4 → ⟪ (CS03⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS03⁻ ∷ Bx0-1234 ∷ []) (CCZ012 ∷ Toff034 ∷ CS03⁻ ∷ CS34⁻ ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 0 2 (CCZ012 ∷ CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ CCZ012 ∷ []) (CCZ012 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff034 ∷ CS03⁻ ∷ CS34⁻ ∷ CCZ034 ∷ []) (pw1 c4 (CS03⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS03⁻ ∷ CS34⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ012 ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ012 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 5 2 (CCZ012 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX03 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff034 ∷ CS03⁻ ∷ CS34⁻ ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff034 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CS03⁻ ∷ [])
  b1 = at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ034 ∷ []) (pw1 c4 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 2 2 (CCZ012 ∷ CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ CCZ012 ∷ []) (CCZ012 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff034 ∷ CZ34 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ Toff034 ∷ []) (Toff034 ∷ CZ34 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff034 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ CS03⁻ ∷ CS34⁻ ∷ CCZ034 ∷ []) (pw1 c4 (CS03⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS03⁻ ∷ CS34⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 6 (CS03⁻ ∷ []) (pw1 c4 (CS03⁻ ∷ CS34⁻ ∷ CCZ034 ∷ CS34⁻ ∷ CZ34 ∷ CCZ034 ∷ []) (CS03⁻ ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CS03⁻ ∷ []) (Bx0-1234 ∷ CS03⁻ ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸ done


-- CZu-box-3: 9 steps
lem-CZu-box-3 : Complete 4 → ⟪ (CZ03 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CZ03 ∷ []) ⟫ʷ
lem-CZu-box-3 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ03 ∷ Bx0-1234 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CZ03 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 0 2 (CCZ012 ∷ CZ03 ∷ []) (lw4 c4 (CZ03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff034 ∷ CZ03 ∷ CZ34 ∷ []) (pw1 c4 (CZ03 ∷ Toff034 ∷ []) (Toff034 ∷ CZ03 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 2 2 (CCZ012 ∷ CZ03 ∷ []) (lw4 c4 (CZ03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff034 ∷ CZ34 ∷ []) (pw1 c4 (CZ34 ∷ Toff034 ∷ []) (Toff034 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ CZ03 ∷ CZ34 ∷ []) (pw1 c4 (CZ03 ∷ Toff034 ∷ []) (Toff034 ∷ CZ03 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CZ03 ∷ []) (pw1 c4 (CZ03 ∷ CZ34 ∷ CZ34 ∷ []) (CZ03 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CZ03 ∷ []) (Bx0-1234 ∷ CZ03 ∷ [])
  b1 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸ done


-- CXu-box-3: 15 steps
lem-CXu-box-3 : Complete 4 → ⟪ (CX30 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CX30 ∷ []) ⟫ʷ
lem-CXu-box-3 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX30 ∷ Bx0-1234 ∷ []) (CCZ012 ∷ CX30 ∷ Toff034 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ012 ∷ Toff034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 0 2 (CCZ012 ∷ CX30 ∷ CCZ123 ∷ []) (lw4 c4 (CX30 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX30 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff034 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ Toff034 ∷ []) (Toff034 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 c4) ▸
       at 4 2 (Toff034 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 c4) ▸
       at 2 2 (Toff034 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ Toff034 ∷ []) (Toff034 ∷ CS23 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ012 ∷ CX30 ∷ Toff034 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ012 ∷ Toff034 ∷ []) (Bx0-1234 ∷ CX30 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff034 ∷ CX30 ∷ []) (pw1 c4 (CX30 ∷ Toff034 ∷ []) (Toff034 ∷ CX30 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ CX30 ∷ CCZ123 ∷ []) (lw4 c4 (CX30 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX30 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX30 ∷ []) (lw4 c4 (CX30 ∷ CCZ123 ∷ CCZ123 ∷ []) (CX30 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ CX30 ∷ []) (pw1 c4 (CX30 ∷ Toff034 ∷ []) (Toff034 ∷ CX30 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸ done


-- CKu-box-3: 7 steps
lem-CKu-box-3 : Complete 4 → ⟪ (CK30 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK30 ∷ []) ⟫ʷ
lem-CKu-box-3 c4 = run b0
  where
  b0 : Chain (CK30 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK30 ∷ [])
  b0 = at 0 1 (CS03⁻ ∷ K0⁻ ∷ CS03⁻ ∷ K0 ∷ CS03⁻ ∷ []) (lw4 c4 (CK30 ∷ []) (CS03⁻ ∷ K0⁻ ∷ CS03⁻ ∷ K0 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-1234 ∷ CS03⁻ ∷ []) (lem-CSdu-box-3 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS03⁻ ∷ []) (lem-CSdu-box-3 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS03⁻ ∷ []) (lem-CSdu-box-3 c4) ▸
       at 1 5 (CK30 ∷ []) (lw4 c4 (CS03⁻ ∷ K0⁻ ∷ CS03⁻ ∷ K0 ∷ CS03⁻ ∷ []) (CK30 ∷ []) tt tt Eq.refl) ▸ done


-- CKdu-box-3: 7 steps
lem-CKdu-box-3 : Complete 4 → ⟪ (CK30⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-CKdu-box-3 c4 = run b0
  where
  b0 : Chain (CK30⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK30⁻ ∷ [])
  b0 = at 0 1 (CS03 ∷ K0⁻ ∷ CS03 ∷ K0 ∷ CS03 ∷ []) (lw4 c4 (CK30⁻ ∷ []) (CS03 ∷ K0⁻ ∷ CS03 ∷ K0 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-1234 ∷ CS03 ∷ []) (lem-CSu-box-3 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS03 ∷ []) (lem-CSu-box-3 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS03 ∷ []) (lem-CSu-box-3 c4) ▸
       at 1 5 (CK30⁻ ∷ []) (lw4 c4 (CS03 ∷ K0⁻ ∷ CS03 ∷ K0 ∷ CS03 ∷ []) (CK30⁻ ∷ []) tt tt Eq.refl) ▸ done


-- XCSX-box-3: 4 steps
lem-XCSX-box-3 : Complete 4 → ⟪ (X3 ∷ CS03 ∷ X3 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-XCSX-box-3 c4 = run b0
  where
  b0 : Chain (X3 ∷ CS03 ∷ X3 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  b0 = at 0 3 (S0 ∷ CS03⁻ ∷ []) (lw4 c4 (X3 ∷ CS03 ∷ X3 ∷ []) (S0 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ CS03⁻ ∷ []) (lem-CSdu-box-3 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0 ∷ []) (lem-Su-box c4) ▸
       at 1 2 (X3 ∷ CS03 ∷ X3 ∷ []) (lw4 c4 (S0 ∷ CS03⁻ ∷ []) (X3 ∷ CS03 ∷ X3 ∷ []) tt tt Eq.refl) ▸ done


-- XCSdX-box-3: 4 steps
lem-XCSdX-box-3 : Complete 4 → ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-XCSdX-box-3 c4 = run b0
  where
  b0 : Chain (X3 ∷ CS03⁻ ∷ X3 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  b0 = at 0 3 (S0⁻ ∷ CS03 ∷ []) (lw4 c4 (X3 ∷ CS03⁻ ∷ X3 ∷ []) (S0⁻ ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ CS03 ∷ []) (lem-CSu-box-3 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0⁻ ∷ []) (lem-Sdu-box c4) ▸
       at 1 2 (X3 ∷ CS03⁻ ∷ X3 ∷ []) (lw4 c4 (S0⁻ ∷ CS03 ∷ []) (X3 ∷ CS03⁻ ∷ X3 ∷ []) tt tt Eq.refl) ▸ done


-- XCKX-box-3: 4 steps
lem-XCKX-box-3 : Complete 4 → ⟪ (X3 ∷ CK30 ∷ X3 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-XCKX-box-3 c4 = run b0
  where
  b0 : Chain (X3 ∷ CK30 ∷ X3 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  b0 = at 0 3 (K0 ∷ CK30⁻ ∷ []) (lw4 c4 (X3 ∷ CK30 ∷ X3 ∷ []) (K0 ∷ CK30⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ CK30⁻ ∷ []) (lem-CKdu-box-3 c4) ▸
       at 0 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 1 2 (X3 ∷ CK30 ∷ X3 ∷ []) (lw4 c4 (K0 ∷ CK30⁻ ∷ []) (X3 ∷ CK30 ∷ X3 ∷ []) tt tt Eq.refl) ▸ done


-- XCKdX-box-3: 4 steps
lem-XCKdX-box-3 : Complete 4 → ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-XCKdX-box-3 c4 = run b0
  where
  b0 : Chain (X3 ∷ CK30⁻ ∷ X3 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  b0 = at 0 3 (K0⁻ ∷ CK30 ∷ []) (lw4 c4 (X3 ∷ CK30⁻ ∷ X3 ∷ []) (K0⁻ ∷ CK30 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ CK30 ∷ []) (lem-CKu-box-3 c4) ▸
       at 0 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 1 2 (X3 ∷ CK30⁻ ∷ X3 ∷ []) (lw4 c4 (K0⁻ ∷ CK30 ∷ []) (X3 ∷ CK30⁻ ∷ X3 ∷ []) tt tt Eq.refl) ▸ done


-- CSu-box-4: 17 steps
lem-CSu-box-4 : Complete 4 → ⟪ (CS04 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS04 ∷ []) ⟫ʷ
lem-CSu-box-4 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS04 ∷ Bx0-1234 ∷ []) (CCZ012 ∷ Toff034 ∷ CS04 ∷ CS34 ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 0 2 (CCZ012 ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff034 ∷ CS04 ∷ CS34 ∷ CCZ034 ∷ []) (pw1 c4 (CS04 ∷ Toff034 ∷ []) (Toff034 ∷ CS04 ∷ CS34 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ012 ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ012 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 5 2 (CCZ012 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX03 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff034 ∷ CS04 ∷ CS34 ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff034 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CS04 ∷ [])
  b1 = at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ034 ∷ []) (pw1 c4 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 2 2 (CCZ012 ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff034 ∷ CZ34 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ Toff034 ∷ []) (Toff034 ∷ CZ34 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff034 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ Toff034 ∷ []) (Toff034 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ CS04 ∷ CS34 ∷ CCZ034 ∷ []) (pw1 c4 (CS04 ∷ Toff034 ∷ []) (Toff034 ∷ CS04 ∷ CS34 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 6 (CS04 ∷ []) (pw1 c4 (CS04 ∷ CS34 ∷ CCZ034 ∷ CS34 ∷ CZ34 ∷ CCZ034 ∷ []) (CS04 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CS04 ∷ []) (Bx0-1234 ∷ CS04 ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸ done


-- CSdu-box-4: 17 steps
lem-CSdu-box-4 : Complete 4 → ⟪ (CS04⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-CSdu-box-4 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS04⁻ ∷ Bx0-1234 ∷ []) (CCZ012 ∷ Toff034 ∷ CS04⁻ ∷ CS34⁻ ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 0 2 (CCZ012 ∷ CS04⁻ ∷ []) (pw3 c4 (CS04⁻ ∷ CCZ012 ∷ []) (CCZ012 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff034 ∷ CS04⁻ ∷ CS34⁻ ∷ CCZ034 ∷ []) (pw1 c4 (CS04⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS04⁻ ∷ CS34⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ012 ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ012 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 5 2 (CCZ012 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX03 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff034 ∷ CS04⁻ ∷ CS34⁻ ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff034 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CS04⁻ ∷ [])
  b1 = at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ034 ∷ []) (pw1 c4 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 2 2 (CCZ012 ∷ CS04⁻ ∷ []) (pw3 c4 (CS04⁻ ∷ CCZ012 ∷ []) (CCZ012 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff034 ∷ CZ34 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ Toff034 ∷ []) (Toff034 ∷ CZ34 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff034 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ CS04⁻ ∷ CS34⁻ ∷ CCZ034 ∷ []) (pw1 c4 (CS04⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS04⁻ ∷ CS34⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 6 (CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ CS34⁻ ∷ CCZ034 ∷ CS34⁻ ∷ CZ34 ∷ CCZ034 ∷ []) (CS04⁻ ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CS04⁻ ∷ []) (Bx0-1234 ∷ CS04⁻ ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸ done


-- CZu-box-4: 9 steps
lem-CZu-box-4 : Complete 4 → ⟪ (CZ04 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CZ04 ∷ []) ⟫ʷ
lem-CZu-box-4 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ04 ∷ Bx0-1234 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CZ04 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 0 2 (CCZ012 ∷ CZ04 ∷ []) (pw3 c4 (CZ04 ∷ CCZ012 ∷ []) (CCZ012 ∷ CZ04 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff034 ∷ CZ04 ∷ CZ34 ∷ []) (pw1 c4 (CZ04 ∷ Toff034 ∷ []) (Toff034 ∷ CZ04 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 2 2 (CCZ012 ∷ CZ04 ∷ []) (pw3 c4 (CZ04 ∷ CCZ012 ∷ []) (CCZ012 ∷ CZ04 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff034 ∷ CZ34 ∷ []) (pw1 c4 (CZ34 ∷ Toff034 ∷ []) (Toff034 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ CZ04 ∷ CZ34 ∷ []) (pw1 c4 (CZ04 ∷ Toff034 ∷ []) (Toff034 ∷ CZ04 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CZ04 ∷ []) (pw1 c4 (CZ04 ∷ CZ34 ∷ CZ34 ∷ []) (CZ04 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CZ04 ∷ []) (Bx0-1234 ∷ CZ04 ∷ [])
  b1 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸ done


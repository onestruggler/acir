{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D012 where

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
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-CSu-box-1 ; lem-Kdu-box ; lem-Ku-box ; lem-Sdu-box ; lem-Su-box)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CZ12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-CS12-CCZ034 ; lem-comm-CSd12-CCZ034)
-- CSdu-box-1: 17 steps
lem-CSdu-box-1 : Complete 4 → ⟪ (CS01⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CSdu-box-1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS01⁻ ∷ Bx0-1234 ∷ []) (Toff012 ∷ CS01⁻ ∷ CS12⁻ ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ CS01⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) (lw4 c4 (CS01⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS01⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ034 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 c4) ▸
       at 4 2 (CCZ034 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸ done

  b1 : Chain (Toff012 ∷ CS01⁻ ∷ CS12⁻ ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CS01⁻ ∷ [])
  b1 = at 4 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ CS01⁻ ∷ []) (pw2 c4 (CS01⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ CS01⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) (lw4 c4 (CS01⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS01⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 6 (CS01⁻ ∷ []) (lw4 c4 (CS01⁻ ∷ CS12⁻ ∷ CCZ012 ∷ CS12⁻ ∷ CZ12 ∷ CCZ012 ∷ []) (CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CS01⁻ ∷ []) (pw2 c4 (CS01⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CS01⁻ ∷ []) (Bx0-1234 ∷ CS01⁻ ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done


-- CZu-box-1: 9 steps
lem-CZu-box-1 : Complete 4 → ⟪ (CZ01 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CZ01 ∷ []) ⟫ʷ
lem-CZu-box-1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ01 ∷ Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CZ01 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ CZ01 ∷ CZ12 ∷ []) (lw4 c4 (CZ01 ∷ Toff012 ∷ []) (Toff012 ∷ CZ01 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ CZ01 ∷ []) (pw2 c4 (CZ01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ CZ12 ∷ []) (lw4 c4 (CZ12 ∷ Toff012 ∷ []) (Toff012 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ CZ01 ∷ CZ12 ∷ []) (lw4 c4 (CZ01 ∷ Toff012 ∷ []) (Toff012 ∷ CZ01 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CZ01 ∷ []) (lw4 c4 (CZ01 ∷ CZ12 ∷ CZ12 ∷ []) (CZ01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CZ01 ∷ []) (pw2 c4 (CZ01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CZ01 ∷ []) (Bx0-1234 ∷ CZ01 ∷ [])
  b1 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done


-- CXu-box-1: 15 steps
lem-CXu-box-1 : Complete 4 → ⟪ (CX10 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CX10 ∷ []) ⟫ʷ
lem-CXu-box-1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX10 ∷ Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ CX10 ∷ CS34 ∷ Toff012 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ CX10 ∷ []) (lw4 c4 (CX10 ∷ Toff012 ∷ []) (Toff012 ∷ CX10 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CX10 ∷ CCZ134 ∷ []) (pw2 c4 (CX10 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX10 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff012 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ Toff012 ∷ []) (Toff012 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff012 ∷ CX13 ∷ []) (lw4 c4 (CX13 ∷ Toff012 ∷ []) (Toff012 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸
       at 4 2 (Toff012 ∷ CX13 ∷ []) (lw4 c4 (CX13 ∷ Toff012 ∷ []) (Toff012 ∷ CX13 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ CX10 ∷ CS34 ∷ Toff012 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ034 ∷ []) (Bx0-1234 ∷ CX10 ∷ [])
  b1 = at 3 2 (Toff012 ∷ CS34 ∷ []) (sym (c₃ (Toff) (CS))) ▸
       at 4 5 (CCZ134 ∷ []) (lw0 c4 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ CX10 ∷ []) (lw4 c4 (CX10 ∷ Toff012 ∷ []) (Toff012 ∷ CX10 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX10 ∷ CCZ134 ∷ []) (pw2 c4 (CX10 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX10 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX10 ∷ []) (pw2 c4 (CX10 ∷ CCZ134 ∷ CCZ134 ∷ []) (CX10 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done


-- CKu-box-1: 7 steps
lem-CKu-box-1 : Complete 4 → ⟪ (CK10 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK10 ∷ []) ⟫ʷ
lem-CKu-box-1 c4 = run b0
  where
  b0 : Chain (CK10 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK10 ∷ [])
  b0 = at 0 1 (CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0 ∷ CS01⁻ ∷ []) (lw4 c4 (CK10 ∷ []) (CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-1234 ∷ CS01⁻ ∷ []) (lem-CSdu-box-1 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS01⁻ ∷ []) (lem-CSdu-box-1 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS01⁻ ∷ []) (lem-CSdu-box-1 c4) ▸
       at 1 5 (CK10 ∷ []) (lw4 c4 (CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0 ∷ CS01⁻ ∷ []) (CK10 ∷ []) tt tt Eq.refl) ▸ done


-- CKdu-box-1: 7 steps
lem-CKdu-box-1 : Complete 4 → ⟪ (CK10⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK10⁻ ∷ []) ⟫ʷ
lem-CKdu-box-1 c4 = run b0
  where
  b0 : Chain (CK10⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK10⁻ ∷ [])
  b0 = at 0 1 (CS01 ∷ K0⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ []) (lw4 c4 (CK10⁻ ∷ []) (CS01 ∷ K0⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-1234 ∷ CS01 ∷ []) (lem-CSu-box-1 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS01 ∷ []) (lem-CSu-box-1 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS01 ∷ []) (lem-CSu-box-1 c4) ▸
       at 1 5 (CK10⁻ ∷ []) (lw4 c4 (CS01 ∷ K0⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ []) (CK10⁻ ∷ []) tt tt Eq.refl) ▸ done


-- XCSX-box-1: 4 steps
lem-XCSX-box-1 : Complete 4 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-XCSX-box-1 c4 = run b0
  where
  b0 : Chain (X1 ∷ CS01 ∷ X1 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  b0 = at 0 3 (S0 ∷ CS01⁻ ∷ []) (lw4 c4 (X1 ∷ CS01 ∷ X1 ∷ []) (S0 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ CS01⁻ ∷ []) (lem-CSdu-box-1 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0 ∷ []) (lem-Su-box c4) ▸
       at 1 2 (X1 ∷ CS01 ∷ X1 ∷ []) (lw4 c4 (S0 ∷ CS01⁻ ∷ []) (X1 ∷ CS01 ∷ X1 ∷ []) tt tt Eq.refl) ▸ done


-- XCSdX-box-1: 4 steps
lem-XCSdX-box-1 : Complete 4 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-XCSdX-box-1 c4 = run b0
  where
  b0 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  b0 = at 0 3 (S0⁻ ∷ CS01 ∷ []) (lw4 c4 (X1 ∷ CS01⁻ ∷ X1 ∷ []) (S0⁻ ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ CS01 ∷ []) (lem-CSu-box-1 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0⁻ ∷ []) (lem-Sdu-box c4) ▸
       at 1 2 (X1 ∷ CS01⁻ ∷ X1 ∷ []) (lw4 c4 (S0⁻ ∷ CS01 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ []) tt tt Eq.refl) ▸ done


-- XCKX-box-1: 4 steps
lem-XCKX-box-1 : Complete 4 → ⟪ (X1 ∷ CK10 ∷ X1 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
lem-XCKX-box-1 c4 = run b0
  where
  b0 : Chain (X1 ∷ CK10 ∷ X1 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X1 ∷ CK10 ∷ X1 ∷ [])
  b0 = at 0 3 (K0 ∷ CK10⁻ ∷ []) (lw4 c4 (X1 ∷ CK10 ∷ X1 ∷ []) (K0 ∷ CK10⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ CK10⁻ ∷ []) (lem-CKdu-box-1 c4) ▸
       at 0 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 1 2 (X1 ∷ CK10 ∷ X1 ∷ []) (lw4 c4 (K0 ∷ CK10⁻ ∷ []) (X1 ∷ CK10 ∷ X1 ∷ []) tt tt Eq.refl) ▸ done


-- XCKdX-box-1: 4 steps
lem-XCKdX-box-1 : Complete 4 → ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
lem-XCKdX-box-1 c4 = run b0
  where
  b0 : Chain (X1 ∷ CK10⁻ ∷ X1 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ [])
  b0 = at 0 3 (K0⁻ ∷ CK10 ∷ []) (lw4 c4 (X1 ∷ CK10⁻ ∷ X1 ∷ []) (K0⁻ ∷ CK10 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ CK10 ∷ []) (lem-CKu-box-1 c4) ▸
       at 0 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 1 2 (X1 ∷ CK10⁻ ∷ X1 ∷ []) (lw4 c4 (K0⁻ ∷ CK10 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ []) tt tt Eq.refl) ▸ done


-- CSu-box-2: 17 steps
lem-CSu-box-2 : Complete 4 → ⟪ (CS02 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS02 ∷ []) ⟫ʷ
lem-CSu-box-2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02 ∷ Bx0-1234 ∷ []) (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) (lw4 c4 (CS02 ∷ Toff012 ∷ []) (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ034 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 c4) ▸
       at 4 2 (CCZ034 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸ done

  b1 : Chain (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CS02 ∷ [])
  b1 = at 4 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ Toff012 ∷ []) (Toff012 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) (lw4 c4 (CS02 ∷ Toff012 ∷ []) (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 6 (CS02 ∷ []) (lw4 c4 (CS02 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CZ12 ∷ CCZ012 ∷ []) (CS02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CS02 ∷ []) (Bx0-1234 ∷ CS02 ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done


-- CSdu-box-2: 17 steps
lem-CSdu-box-2 : Complete 4 → ⟪ (CS02⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-CSdu-box-2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02⁻ ∷ Bx0-1234 ∷ []) (Toff012 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) (lw4 c4 (CS02⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ034 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 c4) ▸
       at 4 2 (CCZ034 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸ done

  b1 : Chain (Toff012 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CS02⁻ ∷ [])
  b1 = at 4 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ CS02⁻ ∷ []) (pw1 c4 (CS02⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) (lw4 c4 (CS02⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 6 (CS02⁻ ∷ []) (lw4 c4 (CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ CS12⁻ ∷ CZ12 ∷ CCZ012 ∷ []) (CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CS02⁻ ∷ []) (pw1 c4 (CS02⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CS02⁻ ∷ []) (Bx0-1234 ∷ CS02⁻ ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done


-- CZu-box-2: 9 steps
lem-CZu-box-2 : Complete 4 → ⟪ (CZ02 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CZ02 ∷ []) ⟫ʷ
lem-CZu-box-2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ02 ∷ Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CZ02 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ CZ02 ∷ CZ12 ∷ []) (lw4 c4 (CZ02 ∷ Toff012 ∷ []) (Toff012 ∷ CZ02 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ CZ02 ∷ []) (pw1 c4 (CZ02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ CZ12 ∷ []) (lw4 c4 (CZ12 ∷ Toff012 ∷ []) (Toff012 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ CZ02 ∷ CZ12 ∷ []) (lw4 c4 (CZ02 ∷ Toff012 ∷ []) (Toff012 ∷ CZ02 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CZ02 ∷ []) (lw4 c4 (CZ02 ∷ CZ12 ∷ CZ12 ∷ []) (CZ02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CZ02 ∷ []) (pw1 c4 (CZ02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CZ02 ∷ []) (Bx0-1234 ∷ CZ02 ∷ [])
  b1 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done


-- CXu-box-2: 15 steps
lem-CXu-box-2 : Complete 4 → ⟪ (CX20 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CX20 ∷ []) ⟫ʷ
lem-CXu-box-2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX20 ∷ Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ CX20 ∷ CS34 ∷ Toff012 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ CX20 ∷ []) (lw4 c4 (CX20 ∷ Toff012 ∷ []) (Toff012 ∷ CX20 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) (pw1 c4 (CX20 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff012 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ Toff012 ∷ []) (Toff012 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff012 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ Toff012 ∷ []) (Toff012 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸
       at 4 2 (Toff012 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ Toff012 ∷ []) (Toff012 ∷ CX23 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ CX20 ∷ CS34 ∷ Toff012 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ034 ∷ []) (Bx0-1234 ∷ CX20 ∷ [])
  b1 = at 3 2 (Toff012 ∷ CS34 ∷ []) (sym (c₃ (Toff) (CS))) ▸
       at 4 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ CX20 ∷ []) (lw4 c4 (CX20 ∷ Toff012 ∷ []) (Toff012 ∷ CX20 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ234 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) (pw1 c4 (CX20 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX20 ∷ []) (pw1 c4 (CX20 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX20 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done


-- CKu-box-2: 7 steps
lem-CKu-box-2 : Complete 4 → ⟪ (CK20 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK20 ∷ []) ⟫ʷ
lem-CKu-box-2 c4 = run b0
  where
  b0 : Chain (CK20 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK20 ∷ [])
  b0 = at 0 1 (CS02⁻ ∷ K0⁻ ∷ CS02⁻ ∷ K0 ∷ CS02⁻ ∷ []) (lw4 c4 (CK20 ∷ []) (CS02⁻ ∷ K0⁻ ∷ CS02⁻ ∷ K0 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CSdu-box-2 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CSdu-box-2 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CSdu-box-2 c4) ▸
       at 1 5 (CK20 ∷ []) (lw4 c4 (CS02⁻ ∷ K0⁻ ∷ CS02⁻ ∷ K0 ∷ CS02⁻ ∷ []) (CK20 ∷ []) tt tt Eq.refl) ▸ done


-- CKdu-box-2: 7 steps
lem-CKdu-box-2 : Complete 4 → ⟪ (CK20⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK20⁻ ∷ []) ⟫ʷ
lem-CKdu-box-2 c4 = run b0
  where
  b0 : Chain (CK20⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK20⁻ ∷ [])
  b0 = at 0 1 (CS02 ∷ K0⁻ ∷ CS02 ∷ K0 ∷ CS02 ∷ []) (lw4 c4 (CK20⁻ ∷ []) (CS02 ∷ K0⁻ ∷ CS02 ∷ K0 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CSu-box-2 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CSu-box-2 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CSu-box-2 c4) ▸
       at 1 5 (CK20⁻ ∷ []) (lw4 c4 (CS02 ∷ K0⁻ ∷ CS02 ∷ K0 ∷ CS02 ∷ []) (CK20⁻ ∷ []) tt tt Eq.refl) ▸ done


-- XCSX-box-2: 4 steps
lem-XCSX-box-2 : Complete 4 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-XCSX-box-2 c4 = run b0
  where
  b0 : Chain (X2 ∷ CS02 ∷ X2 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X2 ∷ CS02 ∷ X2 ∷ [])
  b0 = at 0 3 (S0 ∷ CS02⁻ ∷ []) (lw4 c4 (X2 ∷ CS02 ∷ X2 ∷ []) (S0 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CSdu-box-2 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0 ∷ []) (lem-Su-box c4) ▸
       at 1 2 (X2 ∷ CS02 ∷ X2 ∷ []) (lw4 c4 (S0 ∷ CS02⁻ ∷ []) (X2 ∷ CS02 ∷ X2 ∷ []) tt tt Eq.refl) ▸ done


{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D001 where

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
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CCZ034-CS12 ; lem-comm-CS12-CCZ034 ; lem-comm-CZ12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-1-CCZ023 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF014 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-BOX⟨0·3412⟩ ; lem-nat-2-BOX⟨1·034⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF301 ; lem-nat-3-BOX⟨0·1243⟩ ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-CCZ024 ; lem-nat-3-CCZ034 ; lem-nat-3-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX12-CCZ034 ; lem-nat-1-BOX⟨0·1423⟩ ; lem-nat-1-CCZ013 ; lem-nat-2-BOX⟨0·2413⟩ ; lem-nat-2-TOFF201 ; lem-nat-3-BOX⟨0·1324⟩ ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
-- beta-form: 9 steps
lem-beta-form : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-form c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (pw2 c4 (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (pw2 c4 (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- CCZ012-CCZ034: 7 steps
lem-CCZ012-CCZ034 : Complete 4 → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CCZ012-CCZ034 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS04 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CS04 ∷ []) (CS04 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁)) ▸
       at 2 2 (CS04⁻ ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁)) ▸
       at 4 2 (CS03 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CS03 ∷ []) (CS03 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (CCZ034 ∷ []) (pw1 c4 (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- P12-P34: 4 steps
lem-P12-P34 : Complete 4 → ⟪ (CS12 ∷ CCZ012 ∷ CCZ034 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CS34⁻ ∷ CS12 ∷ CCZ012 ∷ []) ⟫ʷ
lem-P12-P34 c4 = run b0
  where
  b0 : Chain (CS12 ∷ CCZ012 ∷ CCZ034 ∷ CS34⁻ ∷ []) (CCZ034 ∷ CS34⁻ ∷ CS12 ∷ CCZ012 ∷ [])
  b0 = at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-CCZ012-CCZ034 c4) ▸
       at 0 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸
       at 2 2 (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS)) ▸
       at 1 2 (CS34⁻ ∷ CS12 ∷ []) (c₃ (CS ↑) (CS • CS • CS)) ▸ done


-- Z0-beta: 8 steps
lem-Z0-beta : Complete 4 → ⟪ (Z0 ∷ Bx0-1234 ∷ Z0 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-Z0-beta c4 = run b0
  where
  b0 : Chain (Z0 ∷ Bx0-1234 ∷ Z0 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 3 (CCZ012 ∷ Toff012 ∷ CZ12 ∷ Z0 ∷ []) (lw4 c4 (Z0 ∷ CCZ012 ∷ Toff012 ∷ []) (CCZ012 ∷ Toff012 ∷ CZ12 ∷ Z0 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ Z0 ∷ []) (pw1 c4 (Z0 ∷ CCZ034 ∷ []) (CCZ034 ∷ Z0 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (Toff012 ∷ CCZ012 ∷ CZ12 ∷ Z0 ∷ []) (lw4 c4 (Z0 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ CCZ012 ∷ CZ12 ∷ Z0 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CCZ034 ∷ []) (pw1 c4 (Z0 ∷ CCZ034 ∷ Z0 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 c4) ▸
       at 3 4 (Toff012 ∷ CCZ012 ∷ []) (lw4 c4 (CZ12 ∷ Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) (Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx0-1234 ∷ []) (sym (lem-beta-form c4)) ▸ done


-- beta-mirror: 6 steps
lem-beta-mirror : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ CCZ034 ∷ CCZ012 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-mirror c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Toff012 ∷ CCZ012 ∷ CCZ034 ∷ CCZ012 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (Z0 ∷ Bx0-1234 ∷ Z0 ∷ []) (sym (lem-Z0-beta c4)) ▸
       at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 3 (Toff012 ∷ CCZ012 ∷ Z0 ∷ []) (lw4 c4 (Z0 ∷ CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ012 ∷ Z0 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ Z0 ∷ []) (pw1 c4 (Z0 ∷ CCZ034 ∷ []) (CCZ034 ∷ Z0 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CCZ012 ∷ Toff012 ∷ Z0 ∷ []) (lw4 c4 (Z0 ∷ Toff012 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff012 ∷ Z0 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CCZ034 ∷ []) (pw1 c4 (Z0 ∷ CCZ034 ∷ Z0 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- W-Q: 7 steps
lem-W-Q : Complete 4 → ⟪ (CCZ012 ∷ Toff012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ CCZ012 ∷ Toff012 ∷ []) ⟫ʷ
lem-W-Q c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff012 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ CCZ034 ∷ CCZ012 ∷ Toff012 ∷ [])
  b0 = at 0 0 (S0 ∷ K0 ∷ K0⁻ ∷ S0⁻ ∷ []) (lw4 c4 [] (S0 ∷ K0 ∷ K0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CS12 ∷ CCZ012 ∷ K0⁻ ∷ S0⁻ ∷ []) (lw4 c4 (K0⁻ ∷ S0⁻ ∷ CCZ012 ∷ Toff012 ∷ []) (CS12 ∷ CCZ012 ∷ K0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CCZ034 ∷ CS34⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (pw1 c4 (K0⁻ ∷ S0⁻ ∷ Toff034 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS34⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ034 ∷ CS34⁻ ∷ CS12 ∷ CCZ012 ∷ []) (lem-P12-P34 c4) ▸
       at 0 4 (Toff034 ∷ CCZ034 ∷ S0 ∷ K0 ∷ []) (pw1 c4 (S0 ∷ K0 ∷ CCZ034 ∷ CS34⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ S0 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ012 ∷ Toff012 ∷ S0 ∷ K0 ∷ []) (lw4 c4 (S0 ∷ K0 ∷ CS12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff012 ∷ S0 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 4 4 [] (lw4 c4 (S0 ∷ K0 ∷ K0⁻ ∷ S0⁻ ∷ []) [] tt tt Eq.refl) ▸ done


-- V-Q: 3 steps
lem-V-Q : Complete 4 → ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-V-Q c4 = run b0
  where
  b0 : Chain (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ [])
  b0 = at 4 0 (CCZ012 ∷ Toff012 ∷ Toff012 ∷ CCZ012 ∷ []) (lw4 c4 [] (CCZ012 ∷ Toff012 ∷ Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ012 ∷ Toff012 ∷ Toff034 ∷ CCZ034 ∷ []) (sym (lem-W-Q c4)) ▸
       at 0 4 [] (lw4 c4 (Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T34: 4 steps
lem-beta-T34 : Complete 4 → ⟪ (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff012 ∷ Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-beta-T34 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ012 ∷ Toff012 ∷ Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ [])
  b0 = at 2 1 (Toff034 ∷ Toff034 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ []) (Toff034 ∷ Toff034 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Toff034 ∷ Toff034 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ []) (Toff034 ∷ Toff034 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (sym (lem-V-Q c4)) ▸
       at 5 5 (Toff034 ∷ []) (pw1 c4 (Toff034 ∷ CCZ034 ∷ Toff034 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ []) tt tt Eq.refl) ▸ done


-- K0-beta: 16 steps
lem-K0-beta : Complete 4 → ⟪ (K0 ∷ Bx0-1234 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-K0-beta c4 = trans (run b0) (run b1)
  where
  b0 : Chain (K0 ∷ Bx0-1234 ∷ K0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ Toff034 ∷ Z0 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ CZ34 ∷ Z0 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 3 (Toff012 ∷ CCZ012 ∷ K0 ∷ []) (lw4 c4 (K0 ∷ CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ012 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff034 ∷ K0 ∷ []) (pw1 c4 (K0 ∷ CCZ034 ∷ []) (Toff034 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CCZ012 ∷ Toff012 ∷ K0 ∷ []) (lw4 c4 (K0 ∷ Toff012 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff012 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Toff034 ∷ []) (pw1 c4 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (Toff034 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Z0 ∷ Z0 ∷ []) (lw4 c4 [] (Z0 ∷ Z0 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Z0 ∷ Toff034 ∷ CZ34 ∷ []) (pw1 c4 (Toff034 ∷ Z0 ∷ []) (Z0 ∷ Toff034 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Z0 ∷ Toff012 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ Toff012 ∷ Z0 ∷ []) (Z0 ∷ Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff012 ∷ CCZ012 ∷ Toff034 ∷ Z0 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ CZ34 ∷ Z0 ∷ []) (Bx0-1234 ∷ [])
  b1 = at 2 2 (Z0 ∷ Toff034 ∷ CZ34 ∷ []) (pw1 c4 (Toff034 ∷ Z0 ∷ []) (Z0 ∷ Toff034 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Z0 ∷ CCZ012 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ CCZ012 ∷ Z0 ∷ []) (Z0 ∷ CCZ012 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff012 ∷ CZ34 ∷ []) (sym (c₃ (Toff) (CZ))) ▸
       at 5 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 6 3 (Toff034 ∷ []) (pw1 c4 (CZ34 ∷ Toff034 ∷ CZ34 ∷ []) (Toff034 ∷ []) tt tt Eq.refl) ▸
       at 1 6 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (sym (lem-beta-T34 c4)) ▸
       at 1 6 (Bx0-1234 ∷ []) (sym (lem-beta-form c4)) ▸
       at 0 3 (Bx0-1234 ∷ []) (lem-Z0-beta c4) ▸ done


-- beta-T: 8 steps
lem-beta-T : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-T c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 4 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-CCZ012-CCZ034 c4) ▸
       at 0 2 (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) (lw4 c4 (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-CCZ012-CCZ034 c4) ▸
       at 2 3 (Toff012 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CZ12 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-CCZ012-CCZ034 c4) ▸
       at 4 2 [] (lw4 c4 (CCZ012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸ done


-- S0-beta: 10 steps
lem-S0-beta : Complete 4 → ⟪ (S0 ∷ Bx0-1234 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-S0-beta c4 = trans (run b0) (run b1)
  where
  b0 : Chain (S0 ∷ Bx0-1234 ∷ S0⁻ ∷ []) (CS12⁻ ∷ CS12 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 3 (CS12⁻ ∷ Toff012 ∷ S0 ∷ []) (lw4 c4 (S0 ∷ CCZ012 ∷ Toff012 ∷ []) (CS12⁻ ∷ Toff012 ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ S0 ∷ []) (pw1 c4 (S0 ∷ CCZ034 ∷ []) (CCZ034 ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Toff012 ∷ CS12 ∷ S0 ∷ []) (lw4 c4 (S0 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ CS12 ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CCZ034 ∷ []) (pw1 c4 (S0 ∷ CCZ034 ∷ S0⁻ ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS12 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ CS12 ∷ []) (CS12 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 c4) ▸
       at 1 2 (CS12 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ CS12 ∷ []) (CS12 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS12⁻ ∷ CS12 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (Bx0-1234 ∷ [])
  b1 = at 0 2 [] (lw4 c4 (CS12⁻ ∷ CS12 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-beta-T c4)) ▸ done


-- S0-beta-c: 2 steps
lem-S0-beta-c : Complete 4 → ⟪ (S0 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ S0 ∷ []) ⟫ʷ
lem-S0-beta-c c4 = run b0
  where
  b0 : Chain (S0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ S0 ∷ [])
  b0 = at 2 0 (S0⁻ ∷ S0 ∷ []) (lw4 c4 [] (S0⁻ ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx0-1234 ∷ []) (lem-S0-beta c4) ▸ done


-- S0-beta-ci: 2 steps
lem-S0-beta-ci : Complete 4 → ⟪ (S0⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ S0⁻ ∷ []) ⟫ʷ
lem-S0-beta-ci c4 = run b0
  where
  b0 : Chain (S0⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ S0⁻ ∷ [])
  b0 = at 1 1 (S0 ∷ Bx0-1234 ∷ S0⁻ ∷ []) (sym (lem-S0-beta c4)) ▸
       at 0 2 [] (lw4 c4 (S0⁻ ∷ S0 ∷ []) [] tt tt Eq.refl) ▸ done


-- K0-pass: 1 steps
lem-K0-pass : Complete 4 → ⟪ (K0 ∷ Bx0-1234 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-K0-pass c4 = run b0
  where
  b0 : Chain (K0 ∷ Bx0-1234 ∷ K0⁻ ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 3 (Bx0-1234 ∷ []) (lem-K0-beta c4) ▸ done


-- K0-pass-c: 2 steps
lem-K0-pass-c : Complete 4 → ⟪ (K0 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ K0 ∷ []) ⟫ʷ
lem-K0-pass-c c4 = run b0
  where
  b0 : Chain (K0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0 ∷ [])
  b0 = at 2 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx0-1234 ∷ []) (lem-K0-pass c4) ▸ done


-- K0-pass-ci: 2 steps
lem-K0-pass-ci : Complete 4 → ⟪ (K0⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ K0⁻ ∷ []) ⟫ʷ
lem-K0-pass-ci c4 = run b0
  where
  b0 : Chain (K0⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0⁻ ∷ [])
  b0 = at 1 1 (K0 ∷ Bx0-1234 ∷ K0⁻ ∷ []) (sym (lem-K0-pass c4)) ▸
       at 0 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸ done


-- CCZ134-W: 9 steps
lem-CCZ134-W : Complete 4 → ⟪ (CCZ134 ∷ CCZ012 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff012 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CCZ134-W c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ134 ∷ CCZ012 ∷ Toff012 ∷ []) (CCZ012 ∷ Toff012 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ [])
  b0 = at 0 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CCZ012 ∷ Toff012 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ CCZ012 ∷ Toff012 ∷ []) (CCZ012 ∷ Toff012 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 4 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸
       at 2 3 (CCZ012 ∷ Toff012 ∷ CS14⁻ ∷ []) (pw3 c4 (CS14⁻ ∷ CCZ012 ∷ Toff012 ∷ []) (CCZ012 ∷ Toff012 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 2 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸
       at 0 3 (CCZ012 ∷ Toff012 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ012 ∷ Toff012 ∷ []) (CCZ012 ∷ Toff012 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ134 ∷ [])
  b1 = at 2 5 (CCZ134 ∷ []) (lw0 c4 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- CX10-beta: 8 steps
lem-CX10-beta : Complete 4 → ⟪ (CX10 ∷ Bx0-1234 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-CX10-beta c4 = run b0
  where
  b0 : Chain (CX10 ∷ Bx0-1234 ∷ CX10 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 3 (Toff012 ∷ CCZ012 ∷ CX10 ∷ []) (lw4 c4 (CX10 ∷ CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ012 ∷ CX10 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CCZ134 ∷ CX10 ∷ []) (pw2 c4 (CX10 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ134 ∷ CX10 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CCZ012 ∷ Toff012 ∷ CX10 ∷ []) (lw4 c4 (CX10 ∷ Toff012 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff012 ∷ CX10 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CCZ034 ∷ CCZ134 ∷ []) (pw2 c4 (CX10 ∷ CCZ034 ∷ CX10 ∷ []) (CCZ034 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CCZ012 ∷ Toff012 ∷ CCZ134 ∷ []) (lem-CCZ134-W c4) ▸
       at 5 3 (CCZ034 ∷ []) (pw2 c4 (CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx0-1234 ∷ []) (sym (lem-beta-mirror c4)) ▸ done


-- CX10-beta-c: 2 steps
lem-CX10-beta-c : Complete 4 → ⟪ (CX10 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CX10 ∷ []) ⟫ʷ
lem-CX10-beta-c c4 = run b0
  where
  b0 : Chain (CX10 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CX10 ∷ [])
  b0 = at 2 0 (CX10 ∷ CX10 ∷ []) (lw4 c4 [] (CX10 ∷ CX10 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx0-1234 ∷ []) (lem-CX10-beta c4) ▸ done


-- CX10-beta-ci: 2 steps
lem-CX10-beta-ci : Complete 4 → ⟪ (CX10 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CX10 ∷ []) ⟫ʷ
lem-CX10-beta-ci c4 = run b0
  where
  b0 : Chain (CX10 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CX10 ∷ [])
  b0 = at 1 1 (CX10 ∷ Bx0-1234 ∷ CX10 ∷ []) (sym (lem-CX10-beta c4)) ▸
       at 0 2 [] (lw4 c4 (CX10 ∷ CX10 ∷ []) [] tt tt Eq.refl) ▸ done


-- CS20-beta: 10 steps
lem-CS20-beta : Complete 4 → ⟪ (CS02 ∷ Bx0-1234 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-CS20-beta c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS02 ∷ Bx0-1234 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ CS12 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 3 (CS12⁻ ∷ Toff012 ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ CCZ012 ∷ Toff012 ∷ []) (CS12⁻ ∷ Toff012 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Toff012 ∷ CS12 ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ CS12 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CCZ034 ∷ []) (pw1 c4 (CS02 ∷ CCZ034 ∷ CS02⁻ ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS12 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ CS12 ∷ []) (CS12 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 c4) ▸
       at 1 2 (CS12 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ CS12 ∷ []) (CS12 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS12⁻ ∷ CS12 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (Bx0-1234 ∷ [])
  b1 = at 0 2 [] (lw4 c4 (CS12⁻ ∷ CS12 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-beta-T c4)) ▸ done


-- CS20-beta-c: 2 steps
lem-CS20-beta-c : Complete 4 → ⟪ (CS02 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS02 ∷ []) ⟫ʷ
lem-CS20-beta-c c4 = run b0
  where
  b0 : Chain (CS02 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02 ∷ [])
  b0 = at 2 0 (CS02⁻ ∷ CS02 ∷ []) (lw4 c4 [] (CS02⁻ ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx0-1234 ∷ []) (lem-CS20-beta c4) ▸ done


-- CS20-beta-ci: 2 steps
lem-CS20-beta-ci : Complete 4 → ⟪ (CS02⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-CS20-beta-ci c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02⁻ ∷ [])
  b0 = at 1 1 (CS02 ∷ Bx0-1234 ∷ CS02⁻ ∷ []) (sym (lem-CS20-beta c4)) ▸
       at 0 2 [] (lw4 c4 (CS02⁻ ∷ CS02 ∷ []) [] tt tt Eq.refl) ▸ done


-- V-beta: 10 steps
lem-V-beta : Complete 4 → ⟪ (Toff012 ∷ CCZ012 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-V-beta c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff012 ∷ CCZ012 ∷ Bx0-1234 ∷ []) (S0 ∷ Bx0-1234 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ K0⁻ ∷ S0⁻ ∷ [])
  b0 = at 0 2 (S0 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ K0⁻ ∷ S0⁻ ∷ []) (lw4 c4 (Toff012 ∷ CCZ012 ∷ []) (S0 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ K0⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx0-1234 ∷ S0⁻ ∷ []) (lem-S0-beta-ci c4) ▸
       at 6 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-K0-pass-ci c4) ▸
       at 5 2 (Bx0-1234 ∷ CX10 ∷ []) (lem-CX10-beta-c c4) ▸
       at 4 2 (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CS20-beta-ci c4) ▸
       at 3 2 (Bx0-1234 ∷ CX10 ∷ []) (lem-CX10-beta-c c4) ▸
       at 2 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CS20-beta-c c4) ▸
       at 1 2 (Bx0-1234 ∷ K0 ∷ []) (lem-K0-pass-c c4) ▸ done

  b1 : Chain (S0 ∷ Bx0-1234 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ K0⁻ ∷ S0⁻ ∷ []) (Bx0-1234 ∷ Toff012 ∷ CCZ012 ∷ [])
  b1 = at 0 2 (Bx0-1234 ∷ S0 ∷ []) (lem-S0-beta-c c4) ▸
       at 1 8 (Toff012 ∷ CCZ012 ∷ []) (lw4 c4 (S0 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ K0⁻ ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- beta-inv: 7 steps
lem-beta-inv : Complete 4 → ⟪ (Bx0-1234 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Bx0-1234 ∷ []) []
  b0 = at 1 1 (Toff012 ∷ CCZ012 ∷ CCZ034 ∷ CCZ012 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-mirror c4) ▸
       at 0 3 (Toff012 ∷ CCZ012 ∷ Bx0-1234 ∷ []) (sym (lem-V-beta c4)) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 7 2 [] (pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 [] (lw4 c4 (Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 [] (lw4 c4 (Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 [] (pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-form @1221: 10 steps
lem-beta-form-at1221 : Complete 4 → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-form-at1221 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2134 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ Sw12 ∷ CCZ034 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 3 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ Sw12 ∷ CCZ034 ∷ Sw12 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b1 = at 5 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 6 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12: 4 steps
lem-sym12 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-sym12 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-2134 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 2 (CCZ012 ∷ Toff012 ∷ []) (lw4 c4 (CCZ012 ∷ Toff012 ∷ []) (CCZ012 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ CCZ012 ∷ []) (lw4 c4 (Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx0-2134 ∷ []) (sym (lem-beta-form-at1221 c4)) ▸ done


-- beta-form @3443: 10 steps
lem-beta-form-at3443 : Complete 4 → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-form-at3443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1243 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ Sw34 ∷ CCZ034 ∷ Sw34 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ c4) ▸
       at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 2 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 3 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ Sw34 ∷ CCZ034 ∷ Sw34 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b1 = at 5 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 6 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34: 4 steps
lem-sym34 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-sym34 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-1243 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 2 1 (CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx0-1243 ∷ []) (sym (lem-beta-form-at3443 c4)) ▸ done


-- CS12-beta: 6 steps
lem-CS12-beta : Complete 4 → ⟪ (CS12 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS12 ∷ []) ⟫ʷ
lem-CS12-beta c4 = run b0
  where
  b0 : Chain (CS12 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 3 (CCZ012 ∷ Toff012 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ CCZ012 ∷ Toff012 ∷ []) (CCZ012 ∷ Toff012 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸
       at 3 3 (Toff012 ∷ CCZ012 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ CCZ012 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸
       at 0 6 (Bx0-1234 ∷ []) (sym (lem-beta-form c4)) ▸ done


-- CSd12-beta: 5 steps
lem-CSd12-beta : Complete 4 → ⟪ (CS12⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-CSd12-beta c4 = run b0
  where
  b0 : Chain (CS12⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS12⁻ ∷ [])
  b0 = at 0 1 (CS12 ∷ CS12 ∷ CS12 ∷ []) (lw4 c4 (CS12⁻ ∷ []) (CS12 ∷ CS12 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1234 ∷ CS12 ∷ []) (lem-CS12-beta c4) ▸
       at 1 2 (Bx0-1234 ∷ CS12 ∷ []) (lem-CS12-beta c4) ▸
       at 0 2 (Bx0-1234 ∷ CS12 ∷ []) (lem-CS12-beta c4) ▸
       at 1 3 (CS12⁻ ∷ []) (lw4 c4 (CS12 ∷ CS12 ∷ CS12 ∷ []) (CS12⁻ ∷ []) tt tt Eq.refl) ▸ done


-- Cz-beta: 7 steps
lem-Cz-beta : Complete 4 → ⟪ (CCZ012 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-Cz-beta c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CX10 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CS12⁻ ∷ []) (lw4 c4 (CCZ012 ∷ []) (CX10 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-1234 ∷ CS12⁻ ∷ []) (lem-CSd12-beta c4) ▸
       at 3 2 (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CS20-beta-ci c4) ▸
       at 2 2 (Bx0-1234 ∷ CX10 ∷ []) (lem-CX10-beta-c c4) ▸
       at 1 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CS20-beta-c c4) ▸
       at 0 2 (Bx0-1234 ∷ CX10 ∷ []) (lem-CX10-beta-c c4) ▸
       at 1 5 (CCZ012 ∷ []) (lw4 c4 (CX10 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CS12⁻ ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- W-beta: 3 steps
lem-W-beta : Complete 4 → ⟪ (CCZ012 ∷ Toff012 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ012 ∷ Toff012 ∷ []) ⟫ʷ
lem-W-beta c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ012 ∷ Toff012 ∷ [])
  b0 = at 3 0 (Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ []) (lw4 c4 [] (Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Toff012 ∷ CCZ012 ∷ Bx0-1234 ∷ []) (sym (lem-V-beta c4)) ▸
       at 0 4 [] (lw4 c4 (CCZ012 ∷ Toff012 ∷ Toff012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸ done


-- T-beta: 4 steps
lem-T-beta : Complete 4 → ⟪ (Toff012 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Toff012 ∷ []) ⟫ʷ
lem-T-beta c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Toff012 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ CCZ012 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ []) (CCZ012 ∷ CCZ012 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-1234 ∷ CCZ012 ∷ Toff012 ∷ []) (lem-W-beta c4) ▸
       at 0 2 (Bx0-1234 ∷ CCZ012 ∷ []) (lem-Cz-beta c4) ▸
       at 1 3 (Toff012 ∷ []) (lw4 c4 (CCZ012 ∷ CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸ done


-- beta-invword: 6 steps
lem-beta-invword : Complete 4 → ⟪ (CCZ034 ∷ CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-beta-invword c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 6 0 (Bx0-1234 ∷ Bx0-1234 ∷ []) (sym (lem-beta-inv c4)) ▸
       at 6 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 4 4 [] (lw4 c4 (Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 [] (pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 [] (lw4 c4 (CCZ012 ∷ Toff012 ∷ Toff012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 [] (pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl) ▸ done


-- d-beta: 2 steps
lem-d-beta : Complete 4 → ⟪ (CCZ034 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ034 ∷ []) ⟫ʷ
lem-d-beta c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 6 (Bx0-1234 ∷ []) (lem-beta-invword c4) ▸ done


-- beta-T @2332: 8 steps
lem-beta-T-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-beta-T-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T c4) ▸
       at 0 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 2 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 3 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @243243: 8 steps
lem-beta-T-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-beta-T-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at2332 c4) ▸
       at 0 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 1 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 2 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 3 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @12243143: 8 steps
lem-beta-T-at12243143 : Complete 4 → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-beta-T-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ c4) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 0 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 3 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @13243142: 8 steps
lem-beta-T-at13243142 : Complete 4 → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-beta-T-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ c4) ▸
       at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at12243143 c4) ▸
       at 0 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 3 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- d-beta @2332: 7 steps
lem-d-beta-at2332 : Complete 4 → ⟪ (CCZ024 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ024 ∷ []) ⟫ʷ
lem-d-beta-at2332 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ CCZ034 ∷ []) (lem-d-beta c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- d-beta @243243: 7 steps
lem-d-beta-at243243 : Complete 4 → ⟪ (CCZ023 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ023 ∷ []) ⟫ʷ
lem-d-beta-at243243 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Bx0-1324 ∷ CCZ024 ∷ []) (lem-d-beta-at2332 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- d-beta @12243143: 7 steps
lem-d-beta-at12243143 : Complete 4 → ⟪ (CCZ013 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ CCZ013 ∷ []) ⟫ʷ
lem-d-beta-at12243143 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 2 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ c4) ▸
       at 1 2 (Bx0-1423 ∷ CCZ023 ∷ []) (lem-d-beta-at243243 c4) ▸
       at 0 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- d-beta @13243142: 7 steps
lem-d-beta-at13243142 : Complete 4 → ⟪ (CCZ012 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ CCZ012 ∷ []) ⟫ʷ
lem-d-beta-at13243142 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ c4) ▸
       at 1 2 (Bx0-2413 ∷ CCZ013 ∷ []) (lem-d-beta-at12243143 c4) ▸
       at 0 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- symP: 10 steps
lem-symP : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-symP c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ []) (CCZ012 ∷ Bx0-3412 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (K0 ∷ Bx0-1234 ∷ K0⁻ ∷ []) (sym (lem-K0-pass c4)) ▸
       at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T c4) ▸
       at 0 2 (CCZ012 ∷ K0 ∷ []) (lw4 c4 (K0 ∷ Toff012 ∷ []) (CCZ012 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff034 ∷ K0 ∷ []) (pw1 c4 (K0 ∷ CCZ034 ∷ []) (Toff034 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ K0 ∷ []) (lw4 c4 (K0 ∷ Toff012 ∷ []) (CCZ012 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Toff034 ∷ []) (pw1 c4 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (Toff034 ∷ []) tt tt Eq.refl) ▸
       at 4 0 (CCZ012 ∷ CCZ012 ∷ []) (lw4 c4 [] (CCZ012 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Bx0-3412 ∷ []) (sym (lem-beta-T-at13243142 c4)) ▸ done

  b1 : Chain (CCZ012 ∷ Bx0-3412 ∷ CCZ012 ∷ []) (Bx0-3412 ∷ [])
  b1 = at 0 2 (Bx0-3412 ∷ CCZ012 ∷ []) (lem-d-beta-at13243142 c4) ▸
       at 1 2 [] (lw4 c4 (CCZ012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸ done


-- CX23-beta: 17 steps
lem-CX23-beta : Complete 4 → ⟪ (CX23 ∷ Bx0-1234 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CX23-beta c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX23 ∷ Bx0-1234 ∷ CX23 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ CCZ024 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 3 (CCZ012 ∷ Toff012 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ CCZ012 ∷ Toff012 ∷ []) (CCZ012 ∷ Toff012 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CCZ024 ∷ CX23 ∷ []) (pw1 c4 (CX23 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ024 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (Toff012 ∷ CCZ012 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ CCZ012 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CCZ034 ∷ CCZ024 ∷ []) (pw1 c4 (CX23 ∷ CCZ034 ∷ CX23 ∷ []) (CCZ034 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Toff012 ∷ CCZ012 ∷ CCZ024 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ024 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ CCZ012 ∷ CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ034 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ CCZ024 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ CCZ124 ∷ [])
  b1 = at 9 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 8 2 (CCZ034 ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 6 2 (CCZ034 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 7 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 6 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ CCZ124 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ [])
  b2 = at 0 6 (Bx0-1234 ∷ []) (sym (lem-beta-form c4)) ▸ done


-- CX32-beta: 16 steps
lem-CX32-beta : Complete 4 → ⟪ (CX32 ∷ Bx0-1234 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-CX32-beta c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX32 ∷ Bx0-1234 ∷ CX32 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff013 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ034 ∷ CX12 ∷ CS13 ∷ CCZ123 ∷ Toff013 ∷ CCZ013 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 3 (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff013 ∷ CCZ123 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ CCZ012 ∷ Toff012 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff013 ∷ CCZ123 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CX32 ∷ []) (pw1 c4 (CX32 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CCZ123 ∷ Toff013 ∷ CCZ013 ∷ Toff012 ∷ CCZ012 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ Toff012 ∷ CCZ012 ∷ []) (CCZ123 ∷ Toff013 ∷ CCZ013 ∷ Toff012 ∷ CCZ012 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 11 3 (CCZ034 ∷ []) (pw1 c4 (CX32 ∷ CCZ034 ∷ CX32 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ034 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff013 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ034 ∷ CX12 ∷ CS13 ∷ CCZ123 ∷ Toff013 ∷ CCZ013 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ134 ∷ Bx0-1234 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 4 2 (CCZ034 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 2 5 (CCZ134 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ013 ∷ Toff013 ∷ CCZ034 ∷ Toff013 ∷ CCZ013 ∷ []) (CCZ134 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CCZ134 ∷ CCZ012 ∷ Toff012 ∷ []) (sym (lem-CCZ134-W c4)) ▸
       at 1 6 (Bx0-1234 ∷ []) (sym (lem-beta-form c4)) ▸ done


-- c124-beta: 20 steps
lem-c124-beta : Complete 4 → ⟪ (CCZ124 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ124 ∷ []) ⟫ʷ
lem-c124-beta c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CCZ124 ∷ Bx0-1234 ∷ []) (CCZ012 ∷ Toff012 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 2 (CCZ012 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 4 2 (CCZ034 ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CS24 ∷ CX12 ∷ CCZ034 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ [])
  b1 = at 2 2 (CCZ034 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 3 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ034 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 7 2 (CCZ034 ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CS24 ∷ CX12 ∷ CCZ034 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ [])
  b2 = at 6 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 5 2 (CCZ034 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx0-1234 ∷ []) (sym (lem-beta-form c4)) ▸ done


-- c134-beta: 32 steps
lem-c134-beta : Complete 4 → ⟪ (CCZ134 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ134 ∷ []) ⟫ʷ
lem-c134-beta c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CCZ134 ∷ Bx0-1234 ∷ []) (CCZ012 ∷ CCZ134 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 2 2 (CCZ012 ∷ CS14⁻ ∷ []) (pw3 c4 (CS14⁻ ∷ CCZ012 ∷ []) (CCZ012 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 0 2 (CCZ012 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ134 ∷ []) (lw0 c4 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ012 ∷ CCZ134 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ CCZ134 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b1 = at 1 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff012 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ Toff012 ∷ []) (Toff012 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸
       at 3 2 (Toff012 ∷ CS14⁻ ∷ []) (pw3 c4 (CS14⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸
       at 1 2 (Toff012 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ Toff012 ∷ []) (Toff012 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 2 5 (CCZ134 ∷ []) (lw0 c4 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ CCZ134 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b2 = at 3 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff012 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ Toff012 ∷ []) (Toff012 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸
       at 5 2 (Toff012 ∷ CS14⁻ ∷ []) (pw3 c4 (CS14⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸
       at 3 2 (Toff012 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ Toff012 ∷ []) (Toff012 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 4 5 (CCZ134 ∷ []) (lw0 c4 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ CCZ012 ∷ CCZ034 ∷ []) (Bx0-1234 ∷ CCZ134 ∷ [])
  b3 = at 8 2 (CCZ012 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 6 2 (CCZ012 ∷ CS14⁻ ∷ []) (pw3 c4 (CS14⁻ ∷ CCZ012 ∷ []) (CCZ012 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 4 2 (CCZ012 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (CCZ134 ∷ []) (lw0 c4 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx0-1234 ∷ []) (sym (lem-beta-form c4)) ▸ done


-- SW23-beta: 14 steps
lem-SW23-beta : Complete 4 → ⟪ (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-SW23-beta c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) (CCZ134 ∷ CCZ124 ∷ CX23 ∷ Bx0-1234 ∷ CCZ124 ∷ CCZ134 ∷ CX23 ∷ [])
  b0 = at 0 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (lw4 c4 (Sw23 ∷ []) (CX23 ∷ CX32 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (lw4 c4 (Sw23 ∷ []) (CX23 ∷ CX32 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CX23-beta c4) ▸
       at 3 0 (CX32 ∷ CX32 ∷ []) (lw4 c4 [] (CX32 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CCZ134 ∷ Bx0-1234 ∷ []) (lem-CX32-beta c4) ▸
       at 3 3 (CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CX32 ∷ CCZ124 ∷ CX32 ∷ []) (CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (CX23 ∷ CX23 ∷ []) (lw4 c4 [] (CX23 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CCZ134 ∷ CCZ124 ∷ []) (lw0 c4 (CX23 ∷ CCZ134 ∷ CX23 ∷ []) (CCZ134 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ134 ∷ CCZ124 ∷ CX23 ∷ Bx0-1234 ∷ CCZ124 ∷ CCZ134 ∷ CX23 ∷ []) (Bx0-1234 ∷ [])
  b1 = at 4 0 (CX23 ∷ CX23 ∷ []) (lw4 c4 [] (CX23 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CX23-beta c4) ▸
       at 4 4 (CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ []) (lw0 c4 (CX23 ∷ CCZ124 ∷ CCZ134 ∷ CX23 ∷ []) (CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-c124-beta c4) ▸
       at 0 2 (Bx0-1234 ∷ CCZ134 ∷ []) (lem-c134-beta c4) ▸
       at 1 6 [] (lw0 c4 (CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23: 10 steps
lem-sym23 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-sym23 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ []) (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) (sym (lem-SW23-beta c4)) ▸
       at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 2 2 (Bx1-024 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·034⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx1-024 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·034⟩ c4) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ Sw23 ∷ Sw23 ∷ []) (Bx0-1324 ∷ [])
  b1 = at 0 6 (Bx0-1324 ∷ []) (refl) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- Z0-beta-c: 4 steps
lem-Z0-beta-c : Complete 4 → ⟪ (Z0 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Z0 ∷ []) ⟫ʷ
lem-Z0-beta-c c4 = run b0
  where
  b0 : Chain (Z0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Z0 ∷ [])
  b0 = at 0 1 (S0 ∷ S0 ∷ []) (lw4 c4 (Z0 ∷ []) (S0 ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ S0 ∷ []) (lem-S0-beta-c c4) ▸
       at 0 2 (Bx0-1234 ∷ S0 ∷ []) (lem-S0-beta-c c4) ▸
       at 1 2 (Z0 ∷ []) (lw4 c4 (S0 ∷ S0 ∷ []) (Z0 ∷ []) tt tt Eq.refl) ▸ done


-- CZ10-beta-c: 4 steps
lem-CZ10-beta-c : Complete 4 → ⟪ (CZ02 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CZ02 ∷ []) ⟫ʷ
lem-CZ10-beta-c c4 = run b0
  where
  b0 : Chain (CZ02 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CS02 ∷ CS02 ∷ []) (lw4 c4 (CZ02 ∷ []) (CS02 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CS20-beta-c c4) ▸
       at 0 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CS20-beta-c c4) ▸
       at 1 2 (CZ02 ∷ []) (lw4 c4 (CS02 ∷ CS02 ∷ []) (CZ02 ∷ []) tt tt Eq.refl) ▸ done


-- BOXd-BOX: 22 steps
lem-BOXd-BOX : Complete 4 → ⟪ (Bx⁻0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-BOXd-BOX c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx⁻0-1234 ∷ []) (Bx⁻1-034 ∷ CCZ012 ∷ Toff012 ∷ CZ14 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ Bx0-1234 ∷ [])
  b0 = at 1 0 [] (lw4 c4 [] [] tt tt Eq.refl) ▸
       at 1 0 (Bx0-1234 ∷ Bx0-1234 ∷ []) (sym (lem-beta-inv c4)) ▸
       at 0 1 (Bx⁻1-034 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-034 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 6 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (refl) ▸
       at 5 2 [] (lw4 c4 (CCZ012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Toff012 ∷ Toff012 ∷ []) [] tt tt Eq.refl) ▸
       at 3 1 (Bx⁻0-14 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-14 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 3 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (Bx⁻1-034 ∷ CCZ012 ∷ Toff012 ∷ CZ14 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ Bx0-1234 ∷ []) (Bx⁻0-14 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx1-034 ∷ Bx0-1234 ∷ [])
  b1 = at 6 1 (CZ14 ∷ []) (refl) ▸
       at 9 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 11 1 (CZ14 ∷ []) (refl) ▸
       at 14 1 (CZ14 ∷ []) (refl) ▸
       at 3 12 [] (pw2 c4 (CZ14 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) [] tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Toff012 ∷ Toff012 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 [] (lw4 c4 (CCZ012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸
       at 0 1 (Bx⁻0-14 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-14 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸ done

  b2 : Chain (Bx⁻0-14 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx1-034 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ [])
  b2 = at 0 1 (CZ14 ∷ []) (refl) ▸
       at 3 1 (CZ14 ∷ []) (refl) ▸
       at 6 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 8 1 (CZ14 ∷ []) (refl) ▸
       at 11 1 (CZ14 ∷ []) (refl) ▸
       at 0 12 [] (pw2 c4 (CZ14 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CCZ324: 7 steps
lem-auto-TOFF012-∣-CCZ324 : Complete 4 → ⟪ (Toff012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ324 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff012 ∷ [])
  b0 = at 1 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS34 ∷ Toff012 ∷ []) (c₃ (Toff) (CS)) ▸
       at 1 2 (CX24 ∷ Toff012 ∷ []) (pw3 c4 (Toff012 ∷ CX24 ∷ []) (CX24 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS)) ▸
       at 3 2 (CX24 ∷ Toff012 ∷ []) (pw3 c4 (Toff012 ∷ CX24 ∷ []) (CX24 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS23 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ CS23 ∷ []) (CS23 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ314: 7 steps
lem-auto-CCZ012-∣-CCZ314 : Complete 4 → ⟪ (CCZ012 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ314 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸
       at 1 2 (CX14 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CX14 ∷ []) (CX14 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS)) ▸
       at 3 2 (CX14 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CX14 ∷ []) (CX14 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS13 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CS13 ∷ []) (CS13 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (CCZ134 ∷ []) (lw0 c4 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ304: 7 steps
lem-auto-CCZ012-∣-CCZ304 : Complete 4 → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ304 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸
       at 1 2 (CX04 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CX04 ∷ []) (CX04 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS)) ▸
       at 3 2 (CX04 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CX04 ∷ []) (CX04 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS03 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CS03 ∷ []) (CS03 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (CCZ034 ∷ []) (pw1 c4 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF304: 5 steps
lem-auto-CCZ012-∣-TOFF304 : Complete 4 → ⟪ (CCZ012 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF304 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (pw1 c4 (Toff304 ∷ []) (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 2 (K3 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ K3 ∷ []) (K3 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ304 c4) ▸
       at 2 2 (K3⁻ ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff304 ∷ []) (pw1 c4 (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (Toff304 ∷ []) tt tt Eq.refl) ▸ done


-- beta-form @2332: 10 steps
lem-beta-form-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-beta-form-at2332 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1324 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ Sw23 ∷ CCZ034 ∷ Sw23 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 2 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 3 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ Sw23 ∷ CCZ034 ∷ Sw23 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b1 = at 5 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CCZ324 @0110: 7 steps
lem-auto-TOFF012-∣-CCZ324-at0110 : Complete 4 → ⟪ (Toff102 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff102 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ324-at0110 c4 = run b0
  where
  b0 : Chain (Toff102 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff102 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-CCZ324 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CCZ324 @021021: 7 steps
lem-auto-TOFF012-∣-CCZ324-at021021 : Complete 4 → ⟪ (Toff201 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff201 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ324-at021021 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ CCZ134 ∷ []) (CCZ134 ∷ Toff201 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Toff102 ∷ []) (lem-auto-TOFF012-∣-CCZ324-at0110 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CCZ324 @03102132: 7 steps
lem-auto-TOFF012-∣-CCZ324-at03102132 : Complete 4 → ⟪ (Toff301 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff301 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ324-at03102132 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ CCZ124 ∷ []) (CCZ124 ∷ Toff301 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (CCZ134 ∷ Toff201 ∷ []) (lem-auto-TOFF012-∣-CCZ324-at021021 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CCZ324 @031031: 7 steps
lem-auto-TOFF012-∣-CCZ324-at031031 : Complete 4 → ⟪ (Toff302 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff302 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ324-at031031 c4 = run b0
  where
  b0 : Chain (Toff302 ∷ CCZ124 ∷ []) (CCZ124 ∷ Toff302 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 2 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ124 ∷ Toff301 ∷ []) (lem-auto-TOFF012-∣-CCZ324-at03102132 c4) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CCZ324 @0330: 7 steps
lem-auto-TOFF012-∣-CCZ324-at0330 : Complete 4 → ⟪ (Toff312 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff312 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ324-at0330 c4 = run b0
  where
  b0 : Chain (Toff312 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff312 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (CCZ124 ∷ Toff302 ∷ []) (lem-auto-TOFF012-∣-CCZ324-at031031 c4) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


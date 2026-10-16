{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R011 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·23⟩ ; lem-nat-1-BOX⟨0·24⟩ ; lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-2-BOX⟨0·32⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-3-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-2-TOFF304 ; lem-nat-3-TOFF203 ; lem-nat-3-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-2-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-TOFF023)
-- nat 3 CZ03: 2 steps
lem-nat-3-CZ03 : Complete 4 → ⟪ (Sw34 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CZ04 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CZ03 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CZ03 ∷ []) (CZ04 ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CZ04 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(2;03): 3 steps
lem-nat-3-BOX⟨2·03⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-04 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·03⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-03 ∷ []) (Bx2-04 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw34 ∷ []) (lem-nat-3-CZ03 c4) ▸
       at 0 1 (Bx2-04 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;213): 8 steps
lem-nat-3-BOX⟨0·213⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-214 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·213⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-213 ∷ []) (Bx0-214 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 2 2 (Bx2-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·03⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx2-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·03⟩ c4) ▸
       at 0 6 (Bx0-214 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;0413): 8 steps
lem-nat-3-BOX⟨2·0413⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·0413⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-0413 ∷ []) (Bx2-0314 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4) ▸
       at 2 2 (Bx0-214 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·213⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx0-214 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·213⟩ c4) ▸
       at 0 6 (Bx2-0314 ∷ []) (refl) ▸ done


-- nat 3 CZ04: 2 steps
lem-nat-3-CZ04 : Complete 4 → ⟪ (Sw34 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CZ04 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CZ04 ∷ []) (CZ03 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 3 BOX(2;04): 3 steps
lem-nat-3-BOX⟨2·04⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-03 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·04⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-04 ∷ []) (Bx2-03 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw34 ∷ []) (lem-nat-3-CZ04 c4) ▸
       at 0 1 (Bx2-03 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;214): 8 steps
lem-nat-3-BOX⟨0·214⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-213 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·214⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-214 ∷ []) (Bx0-213 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 2 2 (Bx2-03 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·04⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx2-03 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·04⟩ c4) ▸
       at 0 6 (Bx0-213 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;0314): 8 steps
lem-nat-3-BOX⟨2·0314⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·0314⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-0314 ∷ []) (Bx2-0413 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 2 2 (Bx0-213 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·214⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx0-213 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·214⟩ c4) ▸
       at 0 6 (Bx2-0413 ∷ []) (refl) ▸ done


-- nat 2 CCZ014: 53 steps
lem-nat-2-CCZ014 : Complete 4 → ⟪ (Sw23 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CCZ014 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (Sw23 ∷ CCZ014 ∷ []) (Sw23 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw23 ∷ CX01 ∷ CS04 ∷ [])
  b2 = at 3 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 2 2 (CS14⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw23 ∷ CX01 ∷ CS04 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw23 ∷ [])
  b3 = at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 5 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 7 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw23 ∷ []) (Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw23 ∷ [])
  b4 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 4 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Sw34 ∷ Sw23 ∷ [])
  b5 = at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b6 : Chain (Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Sw34 ∷ Sw23 ∷ []) (CCZ014 ∷ Sw23 ∷ [])
  b6 = at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 2 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CCZ014 at 3: 112 steps
lem-resp-CCZ014-at-3 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CCZ014-at-3 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (CCZ014 ∷ []) (Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ []) (CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ [])
  b1 = at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b2 : Chain (CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ [])
  b2 = at 4 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (CS14 ∷ Sw23 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw23 ∷ [])
  b3 = at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑)) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 4 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap)) ▸
       at 2 2 (Sw23 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap)) ▸ done

  b4 : Chain (CS14 ∷ Sw23 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ CS04 ∷ Sw23 ∷ [])
  b4 = at 0 2 (Sw23 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 5 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b5 : Chain (Sw23 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ CS04 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw23 ∷ [])
  b5 = at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b6 : Chain (Sw23 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw12 ∷ CCZ014 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b6 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (Sw23 ∷ Sw12 ∷ Sw12 ∷ CCZ014 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b7 = at 2 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b8 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b9 = at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

  b10 : Chain (Sw23 ∷ Sw12 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b10 = at 2 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b11 : Chain (Sw23 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw01 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b11 = at 7 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 7 2 (Sw01 ∷ CS13 ∷ []) (lw4 c4 (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw01 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b12 = at 7 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) (lw4 c4 (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 3 2 (Sw01 ∷ CX12 ∷ []) (lw4 c4 (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

  b13 : Chain (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b13 = at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 9 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF214 at 3: 7 steps
lem-resp-TOFF214-at-3 : Complete 4 → ⟪ (Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff324 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF214-at-3 c4 = run b0
  where
  b0 : Chain (Toff214 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff324 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw12 ∷ Toff324 ∷ []) (lw0 c4 (Toff314 ∷ Sw12 ∷ []) (Sw12 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸ done


-- resp TOFF204 at 1: 71 steps
lem-resp-TOFF204-at-1 : Complete 4 → ⟪ (Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff214 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF204-at-1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (Toff204 ∷ []) (Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b1 = at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b2 = at 10 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b3 = at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (K2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b4 = at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b5 : Chain (K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw01 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw01 ∷ [])
  b5 = at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 8 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ ι ∷ []) (lw4 c4 (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ K2 ∷ []) (sym (c₂ (Swap) (K))) ▸
       at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸ done

  b6 : Chain (K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw01 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw01 ∷ []) (Sw01 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ Sw01 ∷ [])
  b6 = at 6 2 (Sw01 ∷ CS13 ∷ []) (lw4 c4 (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 6 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ CX12 ∷ []) (lw4 c4 (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CX12 ∷ []) (lw4 c4 (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 0 2 (Sw01 ∷ K2 ∷ []) (sym (c₂ (Swap) (K))) ▸ done

  b7 : Chain (Sw01 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ Sw01 ∷ []) (Sw01 ∷ Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ CS14 ∷ K2 ∷ ι ∷ Sw01 ∷ [])
  b7 = at 1 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸ done

  b8 : Chain (Sw01 ∷ Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ CS14 ∷ K2 ∷ ι ∷ Sw01 ∷ []) (Sw01 ∷ Toff214 ∷ Sw01 ∷ [])
  b8 = at 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 2 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (lw4 c4 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) tt tt Eq.refl) ▸
       at 2 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(1;24): 2 steps
lem-nat-0-BOX⟨1·24⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-24 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·24⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-24 ∷ []) (Bx0-24 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Bx1-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 0 1 (Bx0-24 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(2;134): 8 steps
lem-nat-0-BOX⟨2·134⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-034 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·134⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-134 ∷ []) (Bx2-034 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-24 ∷ Toff213 ∷ CCZ123 ∷ Bx1-24 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff203 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-24 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·24⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-24 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·24⟩ c4) ▸
       at 0 6 (Bx2-034 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;2034): 8 steps
lem-nat-0-BOX⟨1·2034⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·2034⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-2034 ∷ []) (Bx0-2134 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-134 ∷ Toff102 ∷ CCZ012 ∷ Bx2-134 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·134⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·134⟩ c4) ▸
       at 0 6 (Bx0-2134 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;24): 2 steps
lem-nat-0-BOX⟨0·24⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-24 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·24⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-24 ∷ []) (Bx1-24 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Bx0-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 0 1 (Bx1-24 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(2;034): 8 steps
lem-nat-0-BOX⟨2·034⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-134 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·034⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-034 ∷ []) (Bx2-134 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-24 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·24⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-24 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·24⟩ c4) ▸
       at 0 6 (Bx2-134 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;2134): 8 steps
lem-nat-0-BOX⟨0·2134⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·2134⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-2134 ∷ []) (Bx1-2034 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·034⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·034⟩ c4) ▸
       at 0 6 (Bx1-2034 ∷ []) (refl) ▸ done


-- nat 1 CZ01: 2 steps
lem-nat-1-CZ01 : Complete 4 → ⟪ (Sw12 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CZ01 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CZ01 ∷ []) (CZ02 ∷ Sw12 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CZ02 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 CZ02: 2 steps
lem-nat-1-CZ02 : Complete 4 → ⟪ (Sw12 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CZ02 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CZ02 ∷ []) (CZ01 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 1 BOX(2;014): 8 steps
lem-nat-1-BOX⟨2·014⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-014 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-024 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·014⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-014 ∷ []) (Bx1-024 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·24⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·24⟩ c4) ▸
       at 0 6 (Bx1-024 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;2314): 8 steps
lem-nat-1-BOX⟨0·2314⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·2314⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-2314 ∷ []) (Bx0-1324 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 2 2 (Bx1-024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·014⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx1-024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·014⟩ c4) ▸
       at 0 6 (Bx0-1324 ∷ []) (refl) ▸ done


-- nat 1 CX20: 2 steps
lem-nat-1-CX20 : Complete 4 → ⟪ (Sw12 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CX20 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CX20 ∷ []) (CX10 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CX10 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 1 CX10: 2 steps
lem-nat-1-CX10 : Complete 4 → ⟪ (Sw12 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CX10 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CX10 ∷ []) (CX20 ∷ Sw12 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CX20 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CZ02 at 1: 2 steps
lem-resp-CZ02-at-1 : Complete 4 → ⟪ (CZ02 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ12 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CZ02-at-1 c4 = run b0
  where
  b0 : Chain (CZ02 ∷ []) (Sw01 ∷ CZ12 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ CZ12 ∷ []) (lw4 c4 (CZ02 ∷ Sw01 ∷ []) (Sw01 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸ done


-- resp CX20 at 1: 2 steps
lem-resp-CX20-at-1 : Complete 4 → ⟪ (CX20 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX21 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX20-at-1 c4 = run b0
  where
  b0 : Chain (CX20 ∷ []) (Sw01 ∷ CX21 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ CX21 ∷ []) (lw4 c4 (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) tt tt Eq.refl) ▸ done


-- nat 2 CZ13: 2 steps
lem-nat-2-CZ13 : Complete 4 → ⟪ (Sw23 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CZ13 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CZ13 ∷ []) (CZ12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 2 BOX(0;13): 3 steps
lem-nat-2-BOX⟨0·13⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-12 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·13⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-13 ∷ []) (Bx0-12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw23 ∷ []) (lem-nat-2-CZ13 c4) ▸
       at 0 1 (Bx0-12 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;043): 8 steps
lem-nat-2-BOX⟨1·043⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-042 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·043⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-043 ∷ []) (Bx1-042 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 2 2 (Bx0-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·13⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx0-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·13⟩ c4) ▸
       at 0 6 (Bx1-042 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;1243): 8 steps
lem-nat-2-BOX⟨0·1243⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·1243⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-1243 ∷ []) (Bx0-1342 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-043 ∷ Toff012 ∷ CCZ012 ∷ Bx1-043 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 2 2 (Bx1-042 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·043⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx1-042 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·043⟩ c4) ▸
       at 0 6 (Bx0-1342 ∷ []) (refl) ▸ done


-- nat 3 CZ24: 2 steps
lem-nat-3-CZ24 : Complete 4 → ⟪ (Sw34 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CZ24 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CZ24 ∷ []) (CZ23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 3 BOX(0;24): 3 steps
lem-nat-3-BOX⟨0·24⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-23 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·24⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-24 ∷ []) (Bx0-23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw34 ∷ []) (lem-nat-3-CZ24 c4) ▸
       at 0 1 (Bx0-23 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;034): 8 steps
lem-nat-3-BOX⟨2·034⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-043 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·034⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-034 ∷ []) (Bx2-043 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 2 2 (Bx0-23 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·24⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx0-23 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·24⟩ c4) ▸
       at 0 6 (Bx2-043 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;2134): 8 steps
lem-nat-3-BOX⟨0·2134⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·2134⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-2134 ∷ []) (Bx0-2143 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 2 2 (Bx2-043 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·034⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx2-043 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·034⟩ c4) ▸
       at 0 6 (Bx0-2143 ∷ []) (refl) ▸ done


-- nat 2 CZ12: 2 steps
lem-nat-2-CZ12 : Complete 4 → ⟪ (Sw23 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CZ12 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CZ12 ∷ []) (CZ13 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(0;12): 3 steps
lem-nat-2-BOX⟨0·12⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-13 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·12⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-12 ∷ []) (Bx0-13 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw23 ∷ []) (lem-nat-2-CZ12 c4) ▸
       at 0 1 (Bx0-13 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;042): 8 steps
lem-nat-2-BOX⟨1·042⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-043 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·042⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-042 ∷ []) (Bx1-043 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 2 2 (Bx0-13 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·12⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx0-13 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·12⟩ c4) ▸
       at 0 6 (Bx1-043 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;1342): 8 steps
lem-nat-2-BOX⟨0·1342⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·1342⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-1342 ∷ []) (Bx0-1243 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 2 2 (Bx1-043 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·042⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx1-043 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·042⟩ c4) ▸
       at 0 6 (Bx0-1243 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;043): 8 steps
lem-nat-1-BOX⟨2·043⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-043 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·043⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-043 ∷ []) (Bx1-043 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 2 2 (Bx0-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·23⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx0-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·23⟩ c4) ▸
       at 0 6 (Bx1-043 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;2143): 8 steps
lem-nat-1-BOX⟨0·2143⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·2143⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-2143 ∷ []) (Bx0-1243 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-043 ∷ Toff012 ∷ CCZ012 ∷ Bx2-043 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-043 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·043⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-043 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·043⟩ c4) ▸
       at 0 6 (Bx0-1243 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;042): 8 steps
lem-nat-2-BOX⟨3·042⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-043 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·042⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-042 ∷ []) (Bx2-043 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 2 2 (Bx0-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·32⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx0-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·32⟩ c4) ▸
       at 0 6 (Bx2-043 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;3142): 8 steps
lem-nat-2-BOX⟨0·3142⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·3142⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-3142 ∷ []) (Bx0-2143 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 2 2 (Bx2-043 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·042⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx2-043 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·042⟩ c4) ▸
       at 0 6 (Bx0-2143 ∷ []) (refl) ▸ done


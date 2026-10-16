{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R010 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF034 ; lem-nat-2-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-2-TOFF201 ; lem-nat-3-BOX⟨0·14⟩ ; lem-nat-3-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-2-TOFF204 ; lem-nat-2-TOFF304)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-CCZ014 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF104 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-CZ14)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-CZ04 ; lem-nat-0-TOFF214 ; lem-nat-0-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨0·13⟩ ; lem-nat-1-BOX⟨1·03⟩ ; lem-nat-1-TOFF013 ; lem-nat-2-BOX⟨0·213⟩ ; lem-nat-2-BOX⟨2·03⟩)
-- nat 2 BOX(2;0413): 8 steps
lem-nat-2-BOX⟨2·0413⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·0413⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-0413 ∷ []) (Bx3-0412 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 2 2 (Bx0-312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·213⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx0-312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·213⟩ c4) ▸
       at 0 6 (Bx3-0412 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;03): 3 steps
lem-nat-0-BOX⟨1·03⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-13 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·03⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-03 ∷ []) (Bx0-13 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ03 ∷ []) (CZ13 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-13 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;123): 8 steps
lem-nat-0-BOX⟨0·123⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-023 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·123⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-123 ∷ []) (Bx1-023 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-03 ∷ Toff012 ∷ CCZ012 ∷ Bx1-03 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·03⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·03⟩ c4) ▸
       at 0 6 (Bx1-023 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;0423): 8 steps
lem-nat-0-BOX⟨1·0423⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·0423⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-0423 ∷ []) (Bx0-1423 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 2 2 (Bx1-023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·123⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx1-023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·123⟩ c4) ▸
       at 0 6 (Bx0-1423 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;03): 3 steps
lem-nat-1-BOX⟨2·03⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·03⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-03 ∷ []) (Bx1-03 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ03 ∷ []) (CZ03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx1-03 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;213): 8 steps
lem-nat-1-BOX⟨0·213⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-123 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·213⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-213 ∷ []) (Bx0-123 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·03⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·03⟩ c4) ▸
       at 0 6 (Bx0-123 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;0413): 8 steps
lem-nat-1-BOX⟨2·0413⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·0413⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-0413 ∷ []) (Bx1-0423 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 2 2 (Bx0-123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·213⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx0-123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·213⟩ c4) ▸
       at 0 6 (Bx1-0423 ∷ []) (refl) ▸ done


-- nat 2 CZ02: 2 steps
lem-nat-2-CZ02 : Complete 4 → ⟪ (Sw23 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CZ02 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CZ02 ∷ []) (CZ03 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(3;02): 3 steps
lem-nat-2-BOX⟨3·02⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-03 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·02⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-02 ∷ []) (Bx2-03 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4) ▸
       at 0 1 (Bx2-03 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;312): 8 steps
lem-nat-2-BOX⟨0·312⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-213 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·312⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-312 ∷ []) (Bx0-213 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 2 2 (Bx2-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·02⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx2-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·02⟩ c4) ▸
       at 0 6 (Bx0-213 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;0412): 8 steps
lem-nat-2-BOX⟨3·0412⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·0412⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-0412 ∷ []) (Bx2-0413 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 2 2 (Bx0-213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·312⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx0-213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·312⟩ c4) ▸
       at 0 6 (Bx2-0413 ∷ []) (refl) ▸ done


-- resp CCZ014 at 2: 58 steps
lem-resp-CCZ014-at-2 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CCZ014-at-2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (CCZ014 ∷ []) (Sw12 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b1 = at 5 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw12 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b2 = at 8 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Sw12 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b3 = at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw01 ∷ Sw34 ∷ Sw01 ∷ Sw12 ∷ [])
  b4 = at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸ done

  b5 : Chain (Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw01 ∷ Sw34 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw34 ∷ Sw34 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ [])
  b5 = at 6 2 (Sw01 ∷ CS13 ∷ []) (lw4 c4 (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 6 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ CX12 ∷ []) (lw4 c4 (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CX12 ∷ []) (lw4 c4 (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (Sw12 ∷ Sw01 ∷ Sw34 ∷ Sw34 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw34 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw34 ∷ Sw01 ∷ Sw12 ∷ [])
  b6 = at 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

  b7 : Chain (Sw12 ∷ Sw01 ∷ Sw34 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw34 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ [])
  b7 = at 3 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(4;203): 8 steps
lem-nat-0-BOX⟨4·203⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-213 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·203⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-203 ∷ []) (Bx4-213 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 2 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 3 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 0 6 (Bx4-213 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;4103): 8 steps
lem-nat-0-BOX⟨2·4103⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·4103⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-4103 ∷ []) (Bx2-4013 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-203 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 2 2 (Bx4-213 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·203⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx4-213 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·203⟩ c4) ▸
       at 0 6 (Bx2-4013 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;04): 3 steps
lem-nat-0-BOX⟨1·04⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-14 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·04⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-04 ∷ []) (Bx0-14 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw01 ∷ []) (lem-nat-0-CZ04 c4) ▸
       at 0 1 (Bx0-14 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;134): 8 steps
lem-nat-0-BOX⟨0·134⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-034 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·134⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-134 ∷ []) (Bx1-034 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-04 ∷ Toff013 ∷ CCZ013 ∷ Bx1-04 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·04⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·04⟩ c4) ▸
       at 0 6 (Bx1-034 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;0234): 8 steps
lem-nat-0-BOX⟨1·0234⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·0234⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-0234 ∷ []) (Bx0-1234 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-134 ∷ Toff102 ∷ CCZ012 ∷ Bx0-134 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·134⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·134⟩ c4) ▸
       at 0 6 (Bx0-1234 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;043): 8 steps
lem-nat-0-BOX⟨1·043⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-043 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-143 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·043⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-043 ∷ []) (Bx0-143 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 2 2 (Bx1-03 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·13⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx1-03 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·13⟩ c4) ▸
       at 0 6 (Bx0-143 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;1243): 8 steps
lem-nat-0-BOX⟨0·1243⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·1243⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-1243 ∷ []) (Bx1-0243 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-043 ∷ Toff012 ∷ CCZ012 ∷ Bx1-043 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-143 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·043⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-143 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·043⟩ c4) ▸
       at 0 6 (Bx1-0243 ∷ []) (refl) ▸ done


-- nat 1 TOFF023: 2 steps
lem-nat-1-TOFF023 : Complete 4 → ⟪ (Sw12 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF023 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Toff023 ∷ []) (Toff013 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Toff013 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 1 CZ04: 5 steps
lem-nat-1-CZ04 : Complete 4 → ⟪ (Sw12 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (CZ04 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CZ04 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CZ04 ∷ []) (CZ04 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 1 2 (CZ03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ03 ∷ []) (CZ03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (CZ04 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOX(2;04): 3 steps
lem-nat-1-BOX⟨2·04⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-04 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·04⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-04 ∷ []) (Bx1-04 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw12 ∷ []) (lem-nat-1-CZ04 c4) ▸
       at 0 1 (Bx1-04 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;234): 8 steps
lem-nat-1-BOX⟨0·234⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-134 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·234⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-234 ∷ []) (Bx0-134 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 2 2 (Bx1-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·04⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx1-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·04⟩ c4) ▸
       at 0 6 (Bx0-134 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;0134): 8 steps
lem-nat-1-BOX⟨2·0134⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·0134⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-0134 ∷ []) (Bx1-0234 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·234⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·234⟩ c4) ▸
       at 0 6 (Bx1-0234 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;143): 8 steps
lem-nat-1-BOX⟨0·143⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-243 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·143⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-143 ∷ []) (Bx0-243 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-03 ∷ Toff014 ∷ CCZ014 ∷ Bx1-03 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 2 2 (Bx2-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·03⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx2-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·03⟩ c4) ▸
       at 0 6 (Bx0-243 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;0243): 8 steps
lem-nat-1-BOX⟨1·0243⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·0243⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-0243 ∷ []) (Bx2-0143 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-143 ∷ Toff102 ∷ CCZ012 ∷ Bx0-143 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·143⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·143⟩ c4) ▸
       at 0 6 (Bx2-0143 ∷ []) (refl) ▸ done


-- nat 2 CZ04: 7 steps
lem-nat-2-CZ04 : Complete 4 → ⟪ (Sw23 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (CZ04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CZ04 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CZ04 ∷ []) (CZ04 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 3 2 (CZ01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 4 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 5 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 7 (CZ04 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(3;04): 3 steps
lem-nat-2-BOX⟨3·04⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·04⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-04 ∷ []) (Bx2-04 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw23 ∷ []) (lem-nat-2-CZ04 c4) ▸
       at 0 1 (Bx2-04 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;324): 8 steps
lem-nat-2-BOX⟨0·324⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-234 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·324⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-324 ∷ []) (Bx0-234 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·04⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·04⟩ c4) ▸
       at 0 6 (Bx0-234 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;0124): 8 steps
lem-nat-2-BOX⟨3·0124⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·0124⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-0124 ∷ []) (Bx2-0134 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 2 2 (Bx0-234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·324⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx0-234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·324⟩ c4) ▸
       at 0 6 (Bx2-0134 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;243): 8 steps
lem-nat-2-BOX⟨0·243⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-342 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·243⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-243 ∷ []) (Bx0-342 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 2 2 (Bx3-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·03⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx3-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·03⟩ c4) ▸
       at 0 6 (Bx0-342 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;0143): 8 steps
lem-nat-2-BOX⟨2·0143⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·0143⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-0143 ∷ []) (Bx3-0142 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 2 2 (Bx0-342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·243⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx0-342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·243⟩ c4) ▸
       at 0 6 (Bx3-0142 ∷ []) (refl) ▸ done


-- nat 3 CCZ123: 2 steps
lem-nat-3-CCZ123 : Complete 4 → ⟪ (Sw34 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CCZ123 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CCZ123 ∷ []) (CCZ124 ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 TOFF103: 2 steps
lem-nat-3-TOFF103 : Complete 4 → ⟪ (Sw34 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF103 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Toff103 ∷ []) (Toff104 ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff104 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(1;034): 8 steps
lem-nat-3-BOX⟨1·034⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-043 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·034⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-034 ∷ []) (Bx1-043 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 2 2 (Bx0-13 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·14⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx0-13 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·14⟩ c4) ▸
       at 0 6 (Bx1-043 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;1234): 8 steps
lem-nat-3-BOX⟨0·1234⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-1234 ∷ []) (Bx0-1243 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 2 2 (Bx1-043 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·034⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx1-043 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·034⟩ c4) ▸
       at 0 6 (Bx0-1243 ∷ []) (refl) ▸ done


-- nat 3 CCZ124: 2 steps
lem-nat-3-CCZ124 : Complete 4 → ⟪ (Sw34 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CCZ124 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CCZ124 ∷ []) (CCZ123 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 0 BOX(0;143): 8 steps
lem-nat-0-BOX⟨0·143⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-043 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·143⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-143 ∷ []) (Bx1-043 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-03 ∷ Toff014 ∷ CCZ014 ∷ Bx1-03 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 2 2 (Bx0-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·03⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx0-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·03⟩ c4) ▸
       at 0 6 (Bx1-043 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;0243): 8 steps
lem-nat-0-BOX⟨1·0243⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·0243⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-0243 ∷ []) (Bx0-1243 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-143 ∷ Toff102 ∷ CCZ012 ∷ Bx0-143 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-043 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·143⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-043 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·143⟩ c4) ▸
       at 0 6 (Bx0-1243 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;243): 8 steps
lem-nat-1-BOX⟨0·243⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-143 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·243⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-243 ∷ []) (Bx0-143 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 2 2 (Bx1-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·03⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx1-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·03⟩ c4) ▸
       at 0 6 (Bx0-143 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;0143): 8 steps
lem-nat-1-BOX⟨2·0143⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·0143⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-0143 ∷ []) (Bx1-0243 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·243⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·243⟩ c4) ▸
       at 0 6 (Bx1-0243 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;342): 8 steps
lem-nat-2-BOX⟨0·342⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-243 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·342⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-342 ∷ []) (Bx0-243 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 2 2 (Bx2-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·02⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx2-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·02⟩ c4) ▸
       at 0 6 (Bx0-243 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;0142): 8 steps
lem-nat-2-BOX⟨3·0142⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·0142⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-0142 ∷ []) (Bx2-0143 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 2 2 (Bx0-243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·342⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx0-243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·342⟩ c4) ▸
       at 0 6 (Bx2-0143 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;14): 3 steps
lem-nat-0-BOX⟨0·14⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-04 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·14⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-14 ∷ []) (Bx1-04 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw01 ∷ []) (lem-nat-0-CZ14 c4) ▸
       at 0 1 (Bx1-04 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;034): 8 steps
lem-nat-0-BOX⟨1·034⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-134 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·034⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-034 ∷ []) (Bx0-134 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·14⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·14⟩ c4) ▸
       at 0 6 (Bx0-134 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;1234): 8 steps
lem-nat-0-BOX⟨0·1234⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-1234 ∷ []) (Bx1-0234 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·034⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·034⟩ c4) ▸
       at 0 6 (Bx1-0234 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;04): 3 steps
lem-nat-1-BOX⟨1·04⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-04 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·04⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-04 ∷ []) (Bx2-04 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw12 ∷ []) (lem-nat-1-CZ04 c4) ▸
       at 0 1 (Bx2-04 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;134): 8 steps
lem-nat-1-BOX⟨0·134⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-234 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·134⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-134 ∷ []) (Bx0-234 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-04 ∷ Toff013 ∷ CCZ013 ∷ Bx1-04 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 2 2 (Bx2-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·04⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx2-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·04⟩ c4) ▸
       at 0 6 (Bx0-234 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;0234): 8 steps
lem-nat-1-BOX⟨1·0234⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·0234⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-0234 ∷ []) (Bx2-0134 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-134 ∷ Toff102 ∷ CCZ012 ∷ Bx0-134 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·134⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·134⟩ c4) ▸
       at 0 6 (Bx2-0134 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;04): 3 steps
lem-nat-2-BOX⟨2·04⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·04⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-04 ∷ []) (Bx3-04 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw23 ∷ []) (lem-nat-2-CZ04 c4) ▸
       at 0 1 (Bx3-04 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;234): 8 steps
lem-nat-2-BOX⟨0·234⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-324 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·234⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-234 ∷ []) (Bx0-324 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·04⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·04⟩ c4) ▸
       at 0 6 (Bx0-324 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;0134): 8 steps
lem-nat-2-BOX⟨2·0134⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·0134⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-0134 ∷ []) (Bx3-0124 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 2 2 (Bx0-324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·234⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx0-324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·234⟩ c4) ▸
       at 0 6 (Bx3-0124 ∷ []) (refl) ▸ done


-- resp TOFF314 at 2: 4 steps
lem-resp-TOFF314-at-2 : Complete 4 → ⟪ (Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff324 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF314-at-2 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ []) (Sw12 ∷ Sw01 ∷ Toff324 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw12 ∷ Toff324 ∷ []) (lw0 c4 (Toff314 ∷ Sw12 ∷ []) (Sw12 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸ done


-- resp CS03 at 2: 4 steps
lem-resp-CS03-at-2 : Complete 4 → ⟪ (CS03 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CS03-at-2 c4 = run b0
  where
  b0 : Chain (CS03 ∷ []) (Sw12 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS13 ∷ []) (lw4 c4 (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) tt tt Eq.refl) ▸ done


-- resp CSd03 at 2: 4 steps
lem-resp-CSd03-at-2 : Complete 4 → ⟪ (CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CSd03-at-2 c4 = run b0
  where
  b0 : Chain (CS03⁻ ∷ []) (Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS13⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸ done


-- nat 1 BOX(3;04): 3 steps
lem-nat-1-BOX⟨3·04⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-04 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·04⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-04 ∷ []) (Bx3-04 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw12 ∷ []) (lem-nat-1-CZ04 c4) ▸
       at 0 1 (Bx3-04 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;314): 8 steps
lem-nat-1-BOX⟨0·314⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-324 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·314⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-314 ∷ []) (Bx0-324 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 2 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·04⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·04⟩ c4) ▸
       at 0 6 (Bx0-324 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;0214): 8 steps
lem-nat-1-BOX⟨3·0214⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·0214⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-0214 ∷ []) (Bx3-0124 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 2 2 (Bx0-324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·314⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx0-324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·314⟩ c4) ▸
       at 0 6 (Bx3-0124 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;324): 8 steps
lem-nat-1-BOX⟨0·324⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-314 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·324⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-324 ∷ []) (Bx0-314 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 2 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·04⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·04⟩ c4) ▸
       at 0 6 (Bx0-314 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;0124): 8 steps
lem-nat-1-BOX⟨3·0124⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·0124⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-0124 ∷ []) (Bx3-0214 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 2 2 (Bx0-314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·324⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx0-314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·324⟩ c4) ▸
       at 0 6 (Bx3-0214 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;214): 8 steps
lem-nat-2-BOX⟨0·214⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-314 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·214⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-214 ∷ []) (Bx0-314 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 2 2 (Bx3-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·04⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx3-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·04⟩ c4) ▸
       at 0 6 (Bx0-314 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;0314): 8 steps
lem-nat-2-BOX⟨2·0314⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·0314⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-0314 ∷ []) (Bx3-0214 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff302 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-314 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·214⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-314 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·214⟩ c4) ▸
       at 0 6 (Bx3-0214 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;314): 8 steps
lem-nat-2-BOX⟨0·314⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-214 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·314⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-314 ∷ []) (Bx0-214 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 2 2 (Bx2-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·04⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx2-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·04⟩ c4) ▸
       at 0 6 (Bx0-214 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;0214): 8 steps
lem-nat-2-BOX⟨3·0214⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·0214⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-0214 ∷ []) (Bx2-0314 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff203 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·314⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·314⟩ c4) ▸
       at 0 6 (Bx2-0314 ∷ []) (refl) ▸ done


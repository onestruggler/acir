{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R013 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-TOFF203 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF013 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013 ; lem-nat-2-TOFF201)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-TOFF103)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-CCZ014 ; lem-nat-0-TOFF104 ; lem-nat-0-TOFF412 ; lem-nat-1-TOFF204 ; lem-nat-3-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-CZ14 ; lem-nat-0-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-CZ04)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-TOFF413 ; lem-nat-2-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨0·14⟩ ; lem-nat-1-BOX⟨1·04⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-BOXd⟨0·213⟩)
-- nat 1 BOXd(2;0413): 8 steps
lem-nat-1-BOXd⟨2·0413⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0423 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·0413⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-0413 ∷ []) (Bx⁻1-0423 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-123 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·213⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 3 2 (Bx⁻0-123 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·213⟩ c4) ▸
       at 4 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 5 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 0 6 (Bx⁻1-0423 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;24): 3 steps
lem-nat-1-BOXd⟨0·24⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-14 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·24⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-24 ∷ []) (Bx⁻0-14 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CZ24 ∷ []) (CZ14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻0-14 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;034): 8 steps
lem-nat-1-BOXd⟨2·034⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻2-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-034 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·034⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-034 ∷ []) (Bx⁻1-034 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-24 ∷ CCZ023 ∷ Toff203 ∷ Bx⁻0-24 ∷ Toff203 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-14 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·24⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 3 2 (Bx⁻0-14 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·24⟩ c4) ▸
       at 4 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 5 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 0 6 (Bx⁻1-034 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;2134): 8 steps
lem-nat-1-BOXd⟨0·2134⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1234 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·2134⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-2134 ∷ []) (Bx⁻0-1234 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻2-034 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-034 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-034 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·034⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻1-034 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·034⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻0-1234 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;34): 3 steps
lem-nat-2-BOXd⟨0·34⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻0-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-24 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·34⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-34 ∷ []) (Bx⁻0-24 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ34 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ34 ∷ []) (CZ24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻0-24 ∷ []) (refl) ▸ done


-- nat 2 BOXd(3;024): 8 steps
lem-nat-2-BOXd⟨3·024⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻3-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-034 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨3·024⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻3-024 ∷ []) (Bx⁻2-034 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-34 ∷ CCZ023 ∷ Toff302 ∷ Bx⁻0-34 ∷ Toff302 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-24 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·34⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff203 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻0-24 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·34⟩ c4) ▸
       at 4 2 (Toff203 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻2-034 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;3124): 8 steps
lem-nat-2-BOXd⟨0·3124⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-2134 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·3124⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-3124 ∷ []) (Bx⁻0-2134 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻3-024 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻3-024 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-034 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·024⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 3 2 (Bx⁻2-034 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·024⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 5 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 0 6 (Bx⁻0-2134 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;43): 3 steps
lem-nat-3-BOXd⟨0·43⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻0-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-34 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·43⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-43 ∷ []) (Bx⁻0-34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ34 ∷ []) (refl) ▸
       at 0 2 (CZ34 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CZ34 ∷ []) (CZ34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻0-34 ∷ []) (refl) ▸ done


-- nat 3 BOXd(4;023): 8 steps
lem-nat-3-BOXd⟨4·023⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻4-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-024 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨4·023⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻4-023 ∷ []) (Bx⁻3-024 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-43 ∷ CCZ024 ∷ Toff402 ∷ Bx⁻0-43 ∷ Toff402 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-34 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·43⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 2 2 (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4) ▸
       at 3 2 (Bx⁻0-34 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·43⟩ c4) ▸
       at 4 2 (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4) ▸
       at 5 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 0 6 (Bx⁻3-024 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;4123): 8 steps
lem-nat-3-BOXd⟨0·4123⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-3124 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·4123⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-4123 ∷ []) (Bx⁻0-3124 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻4-023 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻4-023 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻3-024 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·023⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 3 2 (Bx⁻3-024 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·023⟩ c4) ▸
       at 4 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 5 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-3124 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;43): 2 steps
lem-nat-0-BOXd⟨1·43⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-43 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·43⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-43 ∷ []) (Bx⁻0-43 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Bx⁻1-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 0 1 (Bx⁻0-43 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOXd(4;123): 8 steps
lem-nat-0-BOXd⟨4·123⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻4-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-023 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·123⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻4-123 ∷ []) (Bx⁻4-023 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-43 ∷ CCZ124 ∷ Toff412 ∷ Bx⁻1-43 ∷ Toff412 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-43 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·43⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 3 2 (Bx⁻0-43 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·43⟩ c4) ▸
       at 4 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 5 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 0 6 (Bx⁻4-023 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;4023): 8 steps
lem-nat-0-BOXd⟨1·4023⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-4023 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-4123 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·4023⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-4023 ∷ []) (Bx⁻0-4123 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻4-123 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻4-123 ∷ Toff104 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-023 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·123⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 2 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 3 2 (Bx⁻4-023 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·123⟩ c4) ▸
       at 4 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 5 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-4123 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;43): 2 steps
lem-nat-1-BOXd⟨2·43⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻2-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-43 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·43⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-43 ∷ []) (Bx⁻1-43 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Bx⁻2-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 0 1 (Bx⁻1-43 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOXd(4;213): 8 steps
lem-nat-1-BOXd⟨4·213⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻4-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-123 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·213⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻4-213 ∷ []) (Bx⁻4-123 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻2-43 ∷ CCZ124 ∷ Toff412 ∷ Bx⁻2-43 ∷ Toff412 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-43 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·43⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff412 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻1-43 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·43⟩ c4) ▸
       at 4 2 (Toff412 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻4-123 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;4013): 8 steps
lem-nat-1-BOXd⟨2·4013⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-4023 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·4013⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-4013 ∷ []) (Bx⁻1-4023 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻4-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻4-213 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-123 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·213⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 3 2 (Bx⁻4-123 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·213⟩ c4) ▸
       at 4 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 5 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 0 6 (Bx⁻1-4023 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;24): 3 steps
lem-nat-1-BOX⟨1·24⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-14 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·24⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-24 ∷ []) (Bx2-14 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CZ24 ∷ []) (CZ14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx2-14 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;134): 8 steps
lem-nat-1-BOX⟨2·134⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-234 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·134⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-134 ∷ []) (Bx1-234 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-24 ∷ Toff213 ∷ CCZ123 ∷ Bx1-24 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·24⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·24⟩ c4) ▸
       at 0 6 (Bx1-234 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;2034): 8 steps
lem-nat-1-BOX⟨1·2034⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·2034⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-2034 ∷ []) (Bx2-1034 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-134 ∷ Toff102 ∷ CCZ012 ∷ Bx2-134 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·134⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·134⟩ c4) ▸
       at 0 6 (Bx2-1034 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;14): 3 steps
lem-nat-2-BOX⟨2·14⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-14 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·14⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-14 ∷ []) (Bx3-14 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ14 ∷ []) (CZ14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx3-14 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;234): 8 steps
lem-nat-2-BOX⟨1·234⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-324 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·234⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-234 ∷ []) (Bx1-324 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-14 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·14⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-14 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·14⟩ c4) ▸
       at 0 6 (Bx1-324 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;1034): 8 steps
lem-nat-2-BOX⟨2·1034⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·1034⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-1034 ∷ []) (Bx3-1024 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 2 2 (Bx1-324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·234⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx1-324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·234⟩ c4) ▸
       at 0 6 (Bx3-1024 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;024): 8 steps
lem-nat-0-BOX⟨1·024⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-124 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·024⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-024 ∷ []) (Bx0-124 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·14⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·14⟩ c4) ▸
       at 0 6 (Bx0-124 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;1324): 8 steps
lem-nat-0-BOX⟨0·1324⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·1324⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-1324 ∷ []) (Bx1-0324 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·024⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·024⟩ c4) ▸
       at 0 6 (Bx1-0324 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;124): 8 steps
lem-nat-1-BOX⟨0·124⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-214 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·124⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-124 ∷ []) (Bx0-214 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-04 ∷ Toff012 ∷ CCZ012 ∷ Bx1-04 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·04⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·04⟩ c4) ▸
       at 0 6 (Bx0-214 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;0324): 8 steps
lem-nat-1-BOX⟨1·0324⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·0324⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-0324 ∷ []) (Bx2-0314 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-124 ∷ Toff103 ∷ CCZ013 ∷ Bx0-124 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 2 2 (Bx0-214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·124⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx0-214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·124⟩ c4) ▸
       at 0 6 (Bx2-0314 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;14): 3 steps
lem-nat-0-BOX⟨3·14⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-04 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·14⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-14 ∷ []) (Bx3-04 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw01 ∷ []) (lem-nat-0-CZ14 c4) ▸
       at 0 1 (Bx3-04 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;324): 8 steps
lem-nat-0-BOX⟨1·324⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-324 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·324⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-324 ∷ []) (Bx0-324 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·14⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·14⟩ c4) ▸
       at 0 6 (Bx0-324 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;1024): 8 steps
lem-nat-0-BOX⟨3·1024⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·1024⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-1024 ∷ []) (Bx3-0124 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·324⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·324⟩ c4) ▸
       at 0 6 (Bx3-0124 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;04): 3 steps
lem-nat-0-BOX⟨3·04⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-14 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·04⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-04 ∷ []) (Bx3-14 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw01 ∷ []) (lem-nat-0-CZ04 c4) ▸
       at 0 1 (Bx3-14 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;314): 8 steps
lem-nat-0-BOX⟨0·314⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-314 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-304 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·314⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-314 ∷ []) (Bx1-304 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·04⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·04⟩ c4) ▸
       at 0 6 (Bx1-304 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;0214): 8 steps
lem-nat-0-BOX⟨3·0214⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·0214⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-0214 ∷ []) (Bx3-1204 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·314⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·314⟩ c4) ▸
       at 0 6 (Bx3-1204 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;304): 8 steps
lem-nat-0-BOX⟨1·304⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-304 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-314 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·304⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-304 ∷ []) (Bx0-314 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·14⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·14⟩ c4) ▸
       at 0 6 (Bx0-314 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;1204): 8 steps
lem-nat-0-BOX⟨3·1204⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·1204⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-1204 ∷ []) (Bx3-0214 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·304⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·304⟩ c4) ▸
       at 0 6 (Bx3-0214 ∷ []) (refl) ▸ done


-- resp CK40 at 1: 6 steps
lem-resp-CK40-at-1 : Complete 4 → ⟪ (CK40 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK41 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CK40-at-1 c4 = run b0
  where
  b0 : Chain (CK40 ∷ []) (Sw01 ∷ CK41 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 2 (Sw01 ∷ CK31 ∷ []) (lw4 c4 (CK30 ∷ Sw01 ∷ []) (Sw01 ∷ CK31 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CKd40 at 1: 6 steps
lem-resp-CKd40-at-1 : Complete 4 → ⟪ (CK40⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK41⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CKd40-at-1 c4 = run b0
  where
  b0 : Chain (CK40⁻ ∷ []) (Sw01 ∷ CK41⁻ ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sw34 ∷ CK30⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 2 (Sw01 ∷ CK31⁻ ∷ []) (lw4 c4 (CK30⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK31⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 3 (CK41⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CKd40 CCZ123: 13 steps
lem-comm-CKd40-CCZ123 : Complete 4 → ⟪ (CK40⁻ ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK40⁻ ∷ []) ⟫ʷ
lem-comm-CKd40-CCZ123 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK40⁻ ∷ CCZ123 ∷ []) (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ CK10⁻ ∷ []) (c₂ (S ↑ • CK₁₀) (CCZ)) ▸
       at 2 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (CCZ123 ∷ CK40⁻ ∷ [])
  b1 = at 2 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 1 7 (CK40⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 CS13: 2 steps
lem-nat-2-CS13 : Complete 4 → ⟪ (Sw23 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CS13 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CS13 ∷ []) (CS12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 2 CS12: 2 steps
lem-nat-2-CS12 : Complete 4 → ⟪ (Sw23 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CS12 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CS12 ∷ []) (CS13 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 CS14: 2 steps
lem-nat-3-CS14 : Complete 4 → ⟪ (Sw34 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CS14 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CS14 ∷ []) (CS13 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 3 CS13: 2 steps
lem-nat-3-CS13 : Complete 4 → ⟪ (Sw34 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CS13 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CS13 ∷ []) (CS14 ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 CSd13: 2 steps
lem-nat-2-CSd13 : Complete 4 → ⟪ (Sw23 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CSd13 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CS13⁻ ∷ []) (CS12⁻ ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 2 CSd12: 2 steps
lem-nat-2-CSd12 : Complete 4 → ⟪ (Sw23 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CSd12 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CS12⁻ ∷ []) (CS13⁻ ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 CSd14: 2 steps
lem-nat-3-CSd14 : Complete 4 → ⟪ (Sw34 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CSd14 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CS14⁻ ∷ []) (CS13⁻ ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 3 CSd13: 2 steps
lem-nat-3-CSd13 : Complete 4 → ⟪ (Sw34 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CSd13 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CS13⁻ ∷ []) (CS14⁻ ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(2;41): 3 steps
lem-nat-0-BOX⟨2·41⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-40 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·41⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-41 ∷ []) (Bx2-40 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw01 ∷ []) (lem-nat-0-CZ14 c4) ▸
       at 0 1 (Bx2-40 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;231): 8 steps
lem-nat-0-BOX⟨4·231⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-230 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·231⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-231 ∷ []) (Bx4-230 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (Bx2-40 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·41⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx2-40 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·41⟩ c4) ▸
       at 0 6 (Bx4-230 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;4031): 8 steps
lem-nat-0-BOX⟨2·4031⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4130 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·4031⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-4031 ∷ []) (Bx2-4130 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 2 2 (Bx4-230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·231⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx4-230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·231⟩ c4) ▸
       at 0 6 (Bx2-4130 ∷ []) (refl) ▸ done


-- nat 2 TOFF314: 2 steps
lem-nat-2-TOFF314 : Complete 4 → ⟪ (Sw23 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF314 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Toff314 ∷ []) (Toff214 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 2 TOFF014: 68 steps
lem-nat-2-TOFF014 : Complete 4 → ⟪ (Sw23 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF014 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (Sw23 ∷ Toff014 ∷ []) (Sw23 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ K0 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b1 = at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸ done

  b2 : Chain (Sw23 ∷ K0 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b2 = at 4 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw23 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw23 ∷ CS04 ∷ K0 ∷ ι ∷ [])
  b3 = at 7 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 1 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 3 2 (CS14⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b4 : Chain (K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw23 ∷ CS04 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ Sw23 ∷ ι ∷ [])
  b4 = at 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b5 : Chain (K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ Sw23 ∷ ι ∷ []) (Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b5 = at 7 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 3 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 5 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

  b6 : Chain (Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b6 = at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b7 = at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b8 : Chain (Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (Toff014 ∷ Sw23 ∷ [])
  b8 = at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 TOFF403: 2 steps
lem-nat-2-TOFF403 : Complete 4 → ⟪ (Sw23 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF403 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Toff403 ∷ []) (Toff402 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 2 BOX(0;42): 3 steps
lem-nat-2-BOX⟨0·42⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-43 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·42⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-42 ∷ []) (Bx0-43 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ24 ∷ []) (CZ34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-43 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;032): 8 steps
lem-nat-2-BOX⟨4·032⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-032 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-023 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·032⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-032 ∷ []) (Bx4-023 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 2 2 (Bx0-43 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·42⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx0-43 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·42⟩ c4) ▸
       at 0 6 (Bx4-023 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;4132): 8 steps
lem-nat-2-BOX⟨0·4132⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·4132⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-4132 ∷ []) (Bx0-4123 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 2 2 (Bx4-023 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·032⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx4-023 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·032⟩ c4) ▸
       at 0 6 (Bx0-4123 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;43): 3 steps
lem-nat-2-BOX⟨0·43⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-42 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·43⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-43 ∷ []) (Bx0-42 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ34 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ34 ∷ []) (CZ24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-42 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;023): 8 steps
lem-nat-2-BOX⟨4·023⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-032 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·023⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-023 ∷ []) (Bx4-032 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 2 2 (Bx0-42 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·43⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx0-42 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·43⟩ c4) ▸
       at 0 6 (Bx4-032 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;4123): 8 steps
lem-nat-2-BOX⟨0·4123⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·4123⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-4123 ∷ []) (Bx0-4132 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 2 2 (Bx4-032 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·023⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx4-032 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·023⟩ c4) ▸
       at 0 6 (Bx0-4132 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;42): 2 steps
lem-nat-0-BOX⟨1·42⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-42 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·42⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-42 ∷ []) (Bx0-42 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Bx1-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 0 1 (Bx0-42 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(4;132): 8 steps
lem-nat-0-BOX⟨4·132⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-132 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-032 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·132⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-132 ∷ []) (Bx4-032 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx1-42 ∷ Toff413 ∷ CCZ134 ∷ Bx1-42 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 2 2 (Bx0-42 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·42⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx0-42 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·42⟩ c4) ▸
       at 0 6 (Bx4-032 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;4032): 8 steps
lem-nat-0-BOX⟨1·4032⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-4032 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·4032⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-4032 ∷ []) (Bx0-4132 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx4-132 ∷ Toff104 ∷ CCZ014 ∷ Bx4-132 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 2 2 (Bx4-032 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·132⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx4-032 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·132⟩ c4) ▸
       at 0 6 (Bx0-4132 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;41): 3 steps
lem-nat-1-BOX⟨2·41⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-42 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·41⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-41 ∷ []) (Bx1-42 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CZ14 ∷ []) (CZ24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx1-42 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;231): 8 steps
lem-nat-1-BOX⟨4·231⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-132 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·231⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-231 ∷ []) (Bx4-132 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·41⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·41⟩ c4) ▸
       at 0 6 (Bx4-132 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;4031): 8 steps
lem-nat-1-BOX⟨2·4031⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4032 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·4031⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-4031 ∷ []) (Bx1-4032 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 2 2 (Bx4-132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·231⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx4-132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·231⟩ c4) ▸
       at 0 6 (Bx1-4032 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;40): 3 steps
lem-nat-0-BOX⟨2·40⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-40 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-41 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·40⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-40 ∷ []) (Bx2-41 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw01 ∷ []) (lem-nat-0-CZ04 c4) ▸
       at 0 1 (Bx2-41 ∷ []) (refl) ▸ done


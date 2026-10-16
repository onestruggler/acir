{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R019 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF203 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF034 ; lem-nat-2-TOFF102)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013 ; lem-nat-1-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-TOFF103)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-CZ14 ; lem-nat-0-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-CZ04)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-1-TOFF401 ; lem-nat-2-CZ03)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-CZ01 ; lem-nat-2-BOX⟨0·13⟩ ; lem-nat-2-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-CS12 ; lem-nat-2-CS13 ; lem-nat-2-CSd12 ; lem-nat-2-CSd13 ; lem-nat-2-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-TOFF134 ; lem-nat-1-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-1-TOFF402 ; lem-nat-2-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-nat-1-BOXd⟨4·02⟩ ; lem-nat-2-BOXd⟨4·02⟩)
-- nat 2 BOXd(0;432): 8 steps
lem-nat-2-BOXd⟨0·432⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻0-432 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-423 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·432⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-432 ∷ []) (Bx⁻0-423 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻4-02 ∷ CCZ034 ∷ Toff034 ∷ Bx⁻4-02 ∷ Toff034 ∷ CCZ034 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-03 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·02⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 2 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 3 2 (Bx⁻4-03 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·02⟩ c4) ▸
       at 4 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 5 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 0 6 (Bx⁻0-423 ∷ []) (refl) ▸ done


-- nat 2 BOXd(4;0132): 8 steps
lem-nat-2-BOXd⟨4·0132⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻4-0132 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0123 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨4·0132⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻4-0132 ∷ []) (Bx⁻4-0123 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-432 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻0-432 ∷ Toff401 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-423 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·432⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 3 2 (Bx⁻0-423 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·432⟩ c4) ▸
       at 4 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 5 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 0 6 (Bx⁻4-0123 ∷ []) (refl) ▸ done


-- nat 2 BOXd(4;03): 3 steps
lem-nat-2-BOXd⟨4·03⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-02 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨4·03⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻4-03 ∷ []) (Bx⁻4-02 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw23 ∷ []) (lem-nat-2-CZ03 c4) ▸
       at 0 1 (Bx⁻4-02 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;423): 8 steps
lem-nat-2-BOXd⟨0·423⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻0-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-432 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·423⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-423 ∷ []) (Bx⁻0-432 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻4-03 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻4-03 ∷ Toff024 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-02 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·03⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 2 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 3 2 (Bx⁻4-02 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·03⟩ c4) ▸
       at 4 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 5 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 0 6 (Bx⁻0-432 ∷ []) (refl) ▸ done


-- nat 2 BOXd(4;0123): 8 steps
lem-nat-2-BOXd⟨4·0123⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0132 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨4·0123⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻4-0123 ∷ []) (Bx⁻4-0132 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-423 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻0-423 ∷ Toff401 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-432 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·423⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 3 2 (Bx⁻0-432 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·423⟩ c4) ▸
       at 4 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 5 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 0 6 (Bx⁻4-0132 ∷ []) (refl) ▸ done


-- nat 1 BOXd(4;01): 3 steps
lem-nat-1-BOXd⟨4·01⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻4-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-02 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·01⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻4-01 ∷ []) (Bx⁻4-02 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 c4) ▸
       at 0 1 (Bx⁻4-02 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;431): 8 steps
lem-nat-1-BOXd⟨0·431⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-431 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-432 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·431⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-431 ∷ []) (Bx⁻0-432 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻4-01 ∷ CCZ034 ∷ Toff034 ∷ Bx⁻4-01 ∷ Toff034 ∷ CCZ034 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-02 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·01⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 2 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 3 2 (Bx⁻4-02 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·01⟩ c4) ▸
       at 4 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 5 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 0 6 (Bx⁻0-432 ∷ []) (refl) ▸ done


-- nat 1 BOXd(4;0231): 8 steps
lem-nat-1-BOXd⟨4·0231⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0132 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·0231⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻4-0231 ∷ []) (Bx⁻4-0132 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-431 ∷ CCZ024 ∷ Toff402 ∷ Bx⁻0-431 ∷ Toff402 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-432 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·431⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 3 2 (Bx⁻0-432 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·431⟩ c4) ▸
       at 4 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 5 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 0 6 (Bx⁻4-0132 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;432): 8 steps
lem-nat-1-BOXd⟨0·432⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-432 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-431 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·432⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-432 ∷ []) (Bx⁻0-431 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻4-02 ∷ CCZ034 ∷ Toff034 ∷ Bx⁻4-02 ∷ Toff034 ∷ CCZ034 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-01 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·02⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 2 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 3 2 (Bx⁻4-01 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·02⟩ c4) ▸
       at 4 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 5 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 0 6 (Bx⁻0-431 ∷ []) (refl) ▸ done


-- nat 1 BOXd(4;0132): 8 steps
lem-nat-1-BOXd⟨4·0132⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻4-0132 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0231 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·0132⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻4-0132 ∷ []) (Bx⁻4-0231 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-432 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻0-432 ∷ Toff401 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-431 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·432⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 3 2 (Bx⁻0-431 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·432⟩ c4) ▸
       at 4 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 5 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 0 6 (Bx⁻4-0231 ∷ []) (refl) ▸ done


-- nat 0 BOXd(4;10): 3 steps
lem-nat-0-BOXd⟨4·10⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻4-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-01 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·10⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻4-10 ∷ []) (Bx⁻4-01 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ01 ∷ []) (CZ01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻4-01 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;430): 8 steps
lem-nat-0-BOXd⟨1·430⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-430 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-431 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·430⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-430 ∷ []) (Bx⁻0-431 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻4-10 ∷ CCZ134 ∷ Toff134 ∷ Bx⁻4-10 ∷ Toff134 ∷ CCZ134 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-01 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·10⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 2 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 3 2 (Bx⁻4-01 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·10⟩ c4) ▸
       at 4 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 5 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 0 6 (Bx⁻0-431 ∷ []) (refl) ▸ done


-- nat 0 BOXd(4;1230): 8 steps
lem-nat-0-BOXd⟨4·1230⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0231 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·1230⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻4-1230 ∷ []) (Bx⁻4-0231 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-430 ∷ CCZ124 ∷ Toff412 ∷ Bx⁻1-430 ∷ Toff412 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-431 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·430⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 3 2 (Bx⁻0-431 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·430⟩ c4) ▸
       at 4 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 5 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 0 6 (Bx⁻4-0231 ∷ []) (refl) ▸ done


-- resp CSd14 at 2: 4 steps
lem-resp-CSd14-at-2 : Complete 4 → ⟪ (CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS24⁻ ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CSd14-at-2 c4 = run b0
  where
  b0 : Chain (CS14⁻ ∷ []) (Sw12 ∷ Sw01 ∷ CS24⁻ ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS24⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸ done


-- nat 2 CS03: 2 steps
lem-nat-2-CS03 : Complete 4 → ⟪ (Sw23 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CS03 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CS03 ∷ []) (CS02 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- comm CCZ024 CX13: 11 steps
lem-comm-CCZ024-CX13 : Complete 4 → ⟪ (CCZ024 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CCZ024 ∷ []) ⟫ʷ
lem-comm-CCZ024-CX13 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ024 ∷ CX13 ∷ []) (Sw12 ∷ Sw34 ∷ Sw34 ∷ CX23 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CX13 ∷ []) (CX23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX24 ∷ []) (CX34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁)) ▸
       at 2 2 (CX24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX34 ∷ []) (CX24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw34 ∷ CX23 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (CX13 ∷ CCZ024 ∷ [])
  b1 = at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (CX13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CX23 ∷ []) (CX13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 7 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CSd03 at 1: 2 steps
lem-resp-CSd03-at-1 : Complete 4 → ⟪ (CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS13⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CSd03-at-1 c4 = run b0
  where
  b0 : Chain (CS03⁻ ∷ []) (Sw01 ∷ CS13⁻ ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ CS13⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸ done


-- resp CX13 at 2: 4 steps
lem-resp-CX13-at-2 : Complete 4 → ⟪ (CX13 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX23 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX13-at-2 c4 = run b0
  where
  b0 : Chain (CX13 ∷ []) (Sw12 ∷ Sw01 ∷ CX23 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw12 ∷ CX23 ∷ []) (lw4 c4 (CX13 ∷ Sw12 ∷ []) (Sw12 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CX23 ∷ []) (sym (c₂ (Swap) (CX₀₁))) ▸ done


-- nat 2 CX30: 2 steps
lem-nat-2-CX30 : Complete 4 → ⟪ (Sw23 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CX30 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CX30 ∷ []) (CX20 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 2 CX20: 2 steps
lem-nat-2-CX20 : Complete 4 → ⟪ (Sw23 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CX20 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CX20 ∷ []) (CX30 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 CX40: 2 steps
lem-nat-3-CX40 : Complete 4 → ⟪ (Sw34 ∷ CX40 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CX40 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CX40 ∷ []) (CX30 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 3 CX30: 2 steps
lem-nat-3-CX30 : Complete 4 → ⟪ (Sw34 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (CX40 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CX30 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CX30 ∷ []) (CX40 ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CX40 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 CSd03: 2 steps
lem-nat-2-CSd03 : Complete 4 → ⟪ (Sw23 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CSd03 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CS03⁻ ∷ []) (CS02⁻ ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- resp CS24 at 3: 6 steps
lem-resp-CS24-at-3 : Complete 4 → ⟪ (CS24 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CS24-at-3 c4 = run b0
  where
  b0 : Chain (CS24 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw23 ∷ CS34 ∷ []) (lw0 c4 (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ CS34 ∷ []) (sym (c₂ (Swap) (CS ↑))) ▸ done


-- nat 2 CX12: 2 steps
lem-nat-2-CX12 : Complete 4 → ⟪ (Sw23 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CX12 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CX12 ∷ []) (CX13 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd02 CCZ134: 23 steps
lem-comm-CSd02-CCZ134 : Complete 4 → ⟪ (CS02⁻ ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-comm-CSd02-CCZ134 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02⁻ ∷ CCZ134 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CCZ134 ∷ CS02⁻ ∷ [])
  b2 = at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 3 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd03 CCZ124: 9 steps
lem-comm-CSd03-CCZ124 : Complete 4 → ⟪ (CS03⁻ ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-comm-CSd03-CCZ124 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03⁻ ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ124 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (CCZ124 ∷ CS03⁻ ∷ [])
  b1 = at 1 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOXd(0;1;3;2): 3 steps
lem-nat-2-SBOXd⟨0·1·3·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·1·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-2-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 c4) ▸
       at 0 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;023): 8 steps
lem-nat-2-BOX⟨1·023⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-032 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·023⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-023 ∷ []) (Bx1-032 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 2 2 (Bx0-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·13⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx0-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·13⟩ c4) ▸
       at 0 6 (Bx1-032 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;1423): 8 steps
lem-nat-2-BOX⟨0·1423⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·1423⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-1423 ∷ []) (Bx0-1432 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 2 2 (Bx1-032 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·023⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx1-032 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·023⟩ c4) ▸
       at 0 6 (Bx0-1432 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;1;2;3): 3 steps
lem-nat-2-SBOXd⟨0·1·2·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·1·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-3-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4) ▸
       at 0 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;1;3;2): 3 steps
lem-nat-2-SBOX⟨0·1·3·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·1·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-2-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 c4) ▸
       at 0 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;1;2;3): 3 steps
lem-nat-2-SBOX⟨0·1·2·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·1·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-3-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4) ▸
       at 0 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;34): 2 steps
lem-nat-0-BOX⟨1·34⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-34 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·34⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-34 ∷ []) (Bx0-34 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Bx1-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 0 1 (Bx0-34 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(3;124): 8 steps
lem-nat-0-BOX⟨3·124⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-024 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·124⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-124 ∷ []) (Bx3-024 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-34 ∷ Toff312 ∷ CCZ123 ∷ Bx1-34 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-34 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·34⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-34 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·34⟩ c4) ▸
       at 0 6 (Bx3-024 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;3024): 8 steps
lem-nat-0-BOX⟨1·3024⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-3024 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·3024⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-3024 ∷ []) (Bx0-3124 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-124 ∷ Toff103 ∷ CCZ013 ∷ Bx3-124 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·124⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·124⟩ c4) ▸
       at 0 6 (Bx0-3124 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;34): 2 steps
lem-nat-1-BOX⟨2·34⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-34 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·34⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-34 ∷ []) (Bx1-34 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Bx2-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 0 1 (Bx1-34 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOX(3;214): 8 steps
lem-nat-1-BOX⟨3·214⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-124 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·214⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-214 ∷ []) (Bx3-124 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-34 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·34⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-34 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·34⟩ c4) ▸
       at 0 6 (Bx3-124 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;3014): 8 steps
lem-nat-1-BOX⟨2·3014⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3024 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·3014⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-3014 ∷ []) (Bx1-3024 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-214 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 2 2 (Bx3-124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·214⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx3-124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·214⟩ c4) ▸
       at 0 6 (Bx1-3024 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;204): 8 steps
lem-nat-0-BOX⟨3·204⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-214 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·204⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-204 ∷ []) (Bx3-214 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 3 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 0 6 (Bx3-214 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;3104): 8 steps
lem-nat-0-BOX⟨2·3104⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·3104⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-3104 ∷ []) (Bx2-3014 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-204 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff203 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-214 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·204⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-214 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·204⟩ c4) ▸
       at 0 6 (Bx2-3014 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;04): 3 steps
lem-nat-0-BOX⟨2·04⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-14 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·04⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-04 ∷ []) (Bx2-14 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw01 ∷ []) (lem-nat-0-CZ04 c4) ▸
       at 0 1 (Bx2-14 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;214): 8 steps
lem-nat-0-BOX⟨0·214⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-204 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·214⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-214 ∷ []) (Bx1-204 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·04⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·04⟩ c4) ▸
       at 0 6 (Bx1-204 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;0314): 8 steps
lem-nat-0-BOX⟨2·0314⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·0314⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-0314 ∷ []) (Bx2-1304 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-204 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·214⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-204 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·214⟩ c4) ▸
       at 0 6 (Bx2-1304 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;14): 3 steps
lem-nat-0-BOX⟨2·14⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-04 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·14⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-14 ∷ []) (Bx2-04 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw01 ∷ []) (lem-nat-0-CZ14 c4) ▸
       at 0 1 (Bx2-04 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;204): 8 steps
lem-nat-0-BOX⟨1·204⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-204 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-214 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·204⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-204 ∷ []) (Bx0-214 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·14⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·14⟩ c4) ▸
       at 0 6 (Bx0-214 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;1304): 8 steps
lem-nat-0-BOX⟨2·1304⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·1304⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-1304 ∷ []) (Bx2-0314 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff203 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-214 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·204⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-214 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·204⟩ c4) ▸
       at 0 6 (Bx2-0314 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;234): 8 steps
lem-nat-0-BOX⟨0·234⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-234 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·234⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-234 ∷ []) (Bx1-234 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff023 ∷ []) (Toff123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·04⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff023 ∷ []) (Toff123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·04⟩ c4) ▸
       at 0 6 (Bx1-234 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;0134): 8 steps
lem-nat-0-BOX⟨2·0134⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·0134⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-0134 ∷ []) (Bx2-1034 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff201 ∷ []) (Toff201 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·234⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff201 ∷ []) (Toff201 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·234⟩ c4) ▸
       at 0 6 (Bx2-1034 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;234): 8 steps
lem-nat-0-BOX⟨1·234⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-234 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·234⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-234 ∷ []) (Bx0-234 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·14⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·14⟩ c4) ▸
       at 0 6 (Bx0-234 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;1034): 8 steps
lem-nat-0-BOX⟨2·1034⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·1034⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-1034 ∷ []) (Bx2-0134 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff201 ∷ []) (Toff201 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·234⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff201 ∷ []) (Toff201 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·234⟩ c4) ▸
       at 0 6 (Bx2-0134 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;34): 2 steps
lem-nat-0-BOX⟨0·34⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-34 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·34⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-34 ∷ []) (Bx1-34 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Bx0-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 0 1 (Bx1-34 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(3;024): 8 steps
lem-nat-0-BOX⟨3·024⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-124 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·024⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-024 ∷ []) (Bx3-124 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-34 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·34⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-34 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·34⟩ c4) ▸
       at 0 6 (Bx3-124 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;3124): 8 steps
lem-nat-0-BOX⟨0·3124⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3024 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·3124⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-3124 ∷ []) (Bx1-3024 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·024⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·024⟩ c4) ▸
       at 0 6 (Bx1-3024 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;34): 2 steps
lem-nat-1-BOX⟨1·34⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-34 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·34⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-34 ∷ []) (Bx2-34 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Bx1-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 0 1 (Bx2-34 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOX(3;124): 8 steps
lem-nat-1-BOX⟨3·124⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-214 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·124⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-124 ∷ []) (Bx3-214 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-34 ∷ Toff312 ∷ CCZ123 ∷ Bx1-34 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-34 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·34⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-34 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·34⟩ c4) ▸
       at 0 6 (Bx3-214 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;3024): 8 steps
lem-nat-1-BOX⟨1·3024⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-3024 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·3024⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-3024 ∷ []) (Bx2-3014 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-124 ∷ Toff103 ∷ CCZ013 ∷ Bx3-124 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 2 2 (Bx3-214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·124⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx3-214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·124⟩ c4) ▸
       at 0 6 (Bx2-3014 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;214): 8 steps
lem-nat-0-BOX⟨3·214⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-204 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·214⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-214 ∷ []) (Bx3-204 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 0 6 (Bx3-204 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;3014): 8 steps
lem-nat-0-BOX⟨2·3014⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·3014⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-3014 ∷ []) (Bx2-3104 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-214 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-204 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·214⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-204 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·214⟩ c4) ▸
       at 0 6 (Bx2-3104 ∷ []) (refl) ▸ done


-- resp TOFF403 at 1: 101 steps
lem-resp-TOFF403-at-1 : Complete 4 → ⟪ (Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff413 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF403-at-1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (Toff403 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b1 = at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw34 ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b2 = at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 11 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 2 2 (K4 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K3 ∷ []) (K4 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw34 ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b3 = at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K4 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K3 ∷ []) (K4 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b4 = at 5 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (K4 ∷ CS34 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b5 = at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (K4 ∷ CS34 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b6 = at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸ done

  b7 : Chain (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw01 ∷ K4 ∷ ι ∷ Sw01 ∷ [])
  b7 = at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 8 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ ι ∷ []) (lw4 c4 (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ K4 ∷ []) (sym (c₂ (Swap) (K ↑ ↑))) ▸ done

  b8 : Chain (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw01 ∷ K4 ∷ ι ∷ Sw01 ∷ []) (K4 ∷ CS34 ∷ Sw01 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ [])
  b8 = at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 6 2 (Sw01 ∷ CS13 ∷ []) (lw4 c4 (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 6 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ CX13 ∷ []) (lw4 c4 (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ CS34⁻ ∷ []) (sym (c₂ (Swap) ((CS • CS • CS) ↑))) ▸
       at 2 2 (Sw01 ∷ CX13 ∷ []) (lw4 c4 (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (K4 ∷ CS34 ∷ Sw01 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ []) (Sw01 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ CX13 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ [])
  b9 = at 1 2 (Sw01 ∷ CS34 ∷ []) (sym (c₂ (Swap) (CS ↑))) ▸
       at 0 2 (Sw01 ∷ K4 ∷ []) (sym (c₂ (Swap) (K ↑ ↑))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 3 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (Sw01 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ CX13 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ []) (Sw01 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ Sw34 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ [])
  b10 = at 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K4 ∷ []) (K3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (Sw01 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ Sw34 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ []) (Sw01 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ Sw34 ∷ ι ∷ Sw23 ∷ Sw01 ∷ [])
  b11 = at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 9 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 (K3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K4 ∷ []) (K3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (Sw01 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ Sw34 ∷ ι ∷ Sw23 ∷ Sw01 ∷ []) (Sw01 ∷ Toff413 ∷ Sw01 ∷ [])
  b12 = at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (lw4 c4 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) tt tt Eq.refl) ▸
       at 3 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(0;21): 3 steps
lem-nat-0-BOX⟨0·21⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-20 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·21⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-21 ∷ []) (Bx1-20 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ12 ∷ []) (CZ02 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx1-20 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;041): 8 steps
lem-nat-0-BOX⟨2·041⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-140 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·041⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-041 ∷ []) (Bx2-140 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 2 2 (Bx1-20 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·21⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx1-20 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·21⟩ c4) ▸
       at 0 6 (Bx2-140 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;2341): 8 steps
lem-nat-0-BOX⟨0·2341⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·2341⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-2341 ∷ []) (Bx1-2340 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff023 ∷ []) (Toff123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-140 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·041⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff023 ∷ []) (Toff123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-140 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·041⟩ c4) ▸
       at 0 6 (Bx1-2340 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;03): 3 steps
lem-nat-2-BOX⟨1·03⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-02 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·03⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-03 ∷ []) (Bx1-02 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw23 ∷ []) (lem-nat-2-CZ03 c4) ▸
       at 0 1 (Bx1-02 ∷ []) (refl) ▸ done


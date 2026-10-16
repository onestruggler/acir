{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R030 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ014 ; lem-nat-3-CCZ013 ; lem-nat-3-CZ14)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-CCZ014 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF104 ; lem-nat-0-TOFF412 ; lem-nat-1-TOFF104 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF304 ; lem-nat-0-TOFF314 ; lem-nat-0-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-TOFF402 ; lem-nat-2-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-TOFF024 ; lem-nat-0-TOFF401 ; lem-nat-0-TOFF413 ; lem-nat-1-TOFF401 ; lem-nat-2-TOFF214 ; lem-nat-2-TOFF402 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-3-CCZ123)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-CCZ014 ; lem-nat-2-CZ12)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-TOFF014 ; lem-nat-2-TOFF314 ; lem-nat-2-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-TOFF034 ; lem-nat-1-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-1-TOFF402 ; lem-nat-2-BOX⟨4·03⟩)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-3-TOFF123)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-TOFF124)
open import Examples.Groups.Clifford+CS.Five.D.R029 using (lem-nat-1-BOX⟨0·423⟩)
-- nat 1 BOX(4;0123): 8 steps
lem-nat-1-BOX⟨4·0123⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·0123⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-0123 ∷ []) (Bx4-0213 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 2 2 (Bx0-413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·423⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx0-413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·423⟩ c4) ▸
       at 0 6 (Bx4-0213 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;03): 3 steps
lem-nat-0-BOX⟨4·03⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-13 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·03⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-03 ∷ []) (Bx4-13 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ03 ∷ []) (CZ13 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx4-13 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;413): 8 steps
lem-nat-0-BOX⟨0·413⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-413 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-403 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·413⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-413 ∷ []) (Bx1-403 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 2 2 (Bx4-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·03⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx4-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·03⟩ c4) ▸
       at 0 6 (Bx1-403 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;0213): 8 steps
lem-nat-0-BOX⟨4·0213⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·0213⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-0213 ∷ []) (Bx4-1203 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-413 ∷ Toff402 ∷ CCZ024 ∷ Bx0-413 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 2 2 (Bx1-403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·413⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx1-403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·413⟩ c4) ▸
       at 0 6 (Bx4-1203 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;13): 3 steps
lem-nat-0-BOX⟨4·13⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-03 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·13⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-13 ∷ []) (Bx4-03 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ13 ∷ []) (CZ03 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx4-03 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;403): 8 steps
lem-nat-0-BOX⟨1·403⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-403 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-413 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·403⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-403 ∷ []) (Bx0-413 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 2 2 (Bx4-03 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·13⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx4-03 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·13⟩ c4) ▸
       at 0 6 (Bx0-413 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;1203): 8 steps
lem-nat-0-BOX⟨4·1203⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·1203⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-1203 ∷ []) (Bx4-0213 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-403 ∷ Toff412 ∷ CCZ124 ∷ Bx1-403 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 2 2 (Bx0-413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·403⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx0-413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·403⟩ c4) ▸
       at 0 6 (Bx4-0213 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;423): 8 steps
lem-nat-0-BOX⟨0·423⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-423 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·423⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-423 ∷ []) (Bx1-423 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 2 2 (Bx4-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·03⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx4-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·03⟩ c4) ▸
       at 0 6 (Bx1-423 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;0123): 8 steps
lem-nat-0-BOX⟨4·0123⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·0123⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-0123 ∷ []) (Bx4-1023 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 2 2 (Bx1-423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·423⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx1-423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·423⟩ c4) ▸
       at 0 6 (Bx4-1023 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;423): 8 steps
lem-nat-0-BOX⟨1·423⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-423 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·423⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-423 ∷ []) (Bx0-423 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 2 2 (Bx4-03 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·13⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx4-03 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·13⟩ c4) ▸
       at 0 6 (Bx0-423 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;1023): 8 steps
lem-nat-0-BOX⟨4·1023⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·1023⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-1023 ∷ []) (Bx4-0123 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 2 2 (Bx0-423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·423⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx0-423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·423⟩ c4) ▸
       at 0 6 (Bx4-0123 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;413): 8 steps
lem-nat-2-BOX⟨0·413⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-412 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·413⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-413 ∷ []) (Bx0-412 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 2 2 (Bx4-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·03⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx4-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·03⟩ c4) ▸
       at 0 6 (Bx0-412 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;0213): 8 steps
lem-nat-2-BOX⟨4·0213⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·0213⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-0213 ∷ []) (Bx4-0312 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-413 ∷ Toff402 ∷ CCZ024 ∷ Bx0-413 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 2 2 (Bx0-412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·413⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx0-412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·413⟩ c4) ▸
       at 0 6 (Bx4-0312 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;14): 3 steps
lem-nat-3-BOX⟨3·14⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx3-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-13 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·14⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-14 ∷ []) (Bx4-13 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw34 ∷ []) (lem-nat-3-CZ14 c4) ▸
       at 0 1 (Bx4-13 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;324): 8 steps
lem-nat-3-BOX⟨1·324⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-423 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·324⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-324 ∷ []) (Bx1-423 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (Toff124 ∷ Sw34 ∷ []) (lem-nat-3-TOFF123 c4) ▸
       at 2 2 (Bx4-13 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·14⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw34 ∷ []) (lem-nat-3-TOFF123 c4) ▸
       at 4 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 5 2 (Bx4-13 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·14⟩ c4) ▸
       at 0 6 (Bx1-423 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;1024): 8 steps
lem-nat-3-BOX⟨3·1024⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·1024⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-1024 ∷ []) (Bx4-1023 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 2 2 (Bx1-423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·324⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx1-423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·324⟩ c4) ▸
       at 0 6 (Bx4-1023 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;13): 3 steps
lem-nat-1-BOX⟨4·13⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-23 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·13⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-13 ∷ []) (Bx4-23 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ13 ∷ []) (CZ23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx4-23 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;423): 8 steps
lem-nat-1-BOX⟨1·423⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-413 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·423⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-423 ∷ []) (Bx2-413 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff214 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-23 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·13⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-23 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·13⟩ c4) ▸
       at 0 6 (Bx2-413 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;1023): 8 steps
lem-nat-1-BOX⟨4·1023⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2013 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·1023⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-1023 ∷ []) (Bx4-2013 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 2 2 (Bx2-413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·423⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx2-413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·423⟩ c4) ▸
       at 0 6 (Bx4-2013 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;23): 3 steps
lem-nat-2-BOX⟨4·23⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-32 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·23⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-23 ∷ []) (Bx4-32 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CZ23 ∷ []) (CZ23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx4-32 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;413): 8 steps
lem-nat-2-BOX⟨2·413⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-413 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-412 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·413⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-413 ∷ []) (Bx3-412 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-23 ∷ Toff214 ∷ CCZ124 ∷ Bx4-23 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 2 2 (Bx4-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·23⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx4-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·23⟩ c4) ▸
       at 0 6 (Bx3-412 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;2013): 8 steps
lem-nat-2-BOX⟨4·2013⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-2013 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·2013⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-2013 ∷ []) (Bx4-3012 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-413 ∷ Toff402 ∷ CCZ024 ∷ Bx2-413 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 2 2 (Bx3-412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·413⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx3-412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·413⟩ c4) ▸
       at 0 6 (Bx4-3012 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;32): 3 steps
lem-nat-1-BOX⟨4·32⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-31 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·32⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-32 ∷ []) (Bx4-31 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ23 ∷ []) (CZ13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx4-31 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;412): 8 steps
lem-nat-1-BOX⟨3·412⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-421 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·412⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-412 ∷ []) (Bx3-421 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-31 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·32⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-31 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·32⟩ c4) ▸
       at 0 6 (Bx3-421 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;3012): 8 steps
lem-nat-1-BOX⟨4·3012⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3021 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·3012⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-3012 ∷ []) (Bx4-3021 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-412 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 2 2 (Bx3-421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·412⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx3-421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·412⟩ c4) ▸
       at 0 6 (Bx4-3021 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;31): 3 steps
lem-nat-0-BOX⟨4·31⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-30 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·31⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-31 ∷ []) (Bx4-30 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ13 ∷ []) (CZ03 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx4-30 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;421): 8 steps
lem-nat-0-BOX⟨3·421⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-420 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·421⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-421 ∷ []) (Bx3-420 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-31 ∷ Toff324 ∷ CCZ234 ∷ Bx4-31 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Bx4-30 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·31⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx4-30 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·31⟩ c4) ▸
       at 0 6 (Bx3-420 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;3021): 8 steps
lem-nat-0-BOX⟨4·3021⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-3021 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·3021⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-3021 ∷ []) (Bx4-3120 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-421 ∷ Toff403 ∷ CCZ034 ∷ Bx3-421 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 2 2 (Bx3-420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·421⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx3-420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·421⟩ c4) ▸
       at 0 6 (Bx4-3120 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;02): 3 steps
lem-nat-0-BOX⟨4·02⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-12 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·02⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-02 ∷ []) (Bx4-12 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ02 ∷ []) (CZ12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx4-12 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;432): 8 steps
lem-nat-0-BOX⟨0·432⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-432 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·432⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-432 ∷ []) (Bx1-432 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-02 ∷ Toff034 ∷ CCZ034 ∷ Bx4-02 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 2 2 (Bx4-12 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·02⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx4-12 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·02⟩ c4) ▸
       at 0 6 (Bx1-432 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;0132): 8 steps
lem-nat-0-BOX⟨4·0132⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-0132 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1032 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·0132⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-0132 ∷ []) (Bx4-1032 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-432 ∷ Toff401 ∷ CCZ014 ∷ Bx0-432 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 2 2 (Bx1-432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·432⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx1-432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·432⟩ c4) ▸
       at 0 6 (Bx4-1032 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;23): 3 steps
lem-nat-1-BOX⟨4·23⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-13 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·23⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-23 ∷ []) (Bx4-13 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ23 ∷ []) (CZ13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx4-13 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;413): 8 steps
lem-nat-1-BOX⟨2·413⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-413 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-423 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·413⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-413 ∷ []) (Bx1-423 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-23 ∷ Toff214 ∷ CCZ124 ∷ Bx4-23 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff214 ∷ []) (Toff124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·23⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff214 ∷ []) (Toff124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·23⟩ c4) ▸
       at 0 6 (Bx1-423 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;2013): 8 steps
lem-nat-1-BOX⟨4·2013⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-2013 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·2013⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-2013 ∷ []) (Bx4-1023 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-413 ∷ Toff402 ∷ CCZ024 ∷ Bx2-413 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 2 2 (Bx1-423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·413⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx1-423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·413⟩ c4) ▸
       at 0 6 (Bx4-1023 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;12): 3 steps
lem-nat-1-BOX⟨4·12⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-21 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·12⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-12 ∷ []) (Bx4-21 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ12 ∷ []) (CZ12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx4-21 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;432): 8 steps
lem-nat-1-BOX⟨1·432⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-432 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-431 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·432⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-432 ∷ []) (Bx2-431 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-12 ∷ Toff134 ∷ CCZ134 ∷ Bx4-12 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·12⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·12⟩ c4) ▸
       at 0 6 (Bx2-431 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;1032): 8 steps
lem-nat-1-BOX⟨4·1032⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-1032 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·1032⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-1032 ∷ []) (Bx4-2031 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-432 ∷ Toff401 ∷ CCZ014 ∷ Bx1-432 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 2 2 (Bx2-431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·432⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx2-431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·432⟩ c4) ▸
       at 0 6 (Bx4-2031 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;32): 3 steps
lem-nat-2-BOX⟨4·32⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-23 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·32⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-32 ∷ []) (Bx4-23 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CZ23 ∷ []) (CZ23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx4-23 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;412): 8 steps
lem-nat-2-BOX⟨3·412⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-412 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-413 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·412⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-412 ∷ []) (Bx2-413 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 2 2 (Bx4-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·32⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx4-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·32⟩ c4) ▸
       at 0 6 (Bx2-413 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;3012): 8 steps
lem-nat-2-BOX⟨4·3012⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2013 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·3012⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-3012 ∷ []) (Bx4-2013 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-412 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 2 2 (Bx2-413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·412⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx2-413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·412⟩ c4) ▸
       at 0 6 (Bx4-2013 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;21): 3 steps
lem-nat-2-BOX⟨4·21⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-31 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·21⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-21 ∷ []) (Bx4-31 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw23 ∷ []) (lem-nat-2-CZ12 c4) ▸
       at 0 1 (Bx4-31 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;431): 8 steps
lem-nat-2-BOX⟨2·431⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-431 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-421 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·431⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-431 ∷ []) (Bx3-421 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-31 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·21⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-31 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·21⟩ c4) ▸
       at 0 6 (Bx3-421 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;2031): 8 steps
lem-nat-2-BOX⟨4·2031⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3021 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·2031⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-2031 ∷ []) (Bx4-3021 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-431 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 2 2 (Bx3-421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·431⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx3-421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·431⟩ c4) ▸
       at 0 6 (Bx4-3021 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;31): 3 steps
lem-nat-1-BOX⟨4·31⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-32 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·31⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-31 ∷ []) (Bx4-32 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ13 ∷ []) (CZ23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx4-32 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;421): 8 steps
lem-nat-1-BOX⟨3·421⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-412 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·421⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-421 ∷ []) (Bx3-412 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-31 ∷ Toff324 ∷ CCZ234 ∷ Bx4-31 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-32 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·31⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-32 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·31⟩ c4) ▸
       at 0 6 (Bx3-412 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;3021): 8 steps
lem-nat-1-BOX⟨4·3021⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-3021 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·3021⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-3021 ∷ []) (Bx4-3012 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-421 ∷ Toff403 ∷ CCZ034 ∷ Bx3-421 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 2 2 (Bx3-412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·421⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx3-412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·421⟩ c4) ▸
       at 0 6 (Bx4-3012 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;30): 3 steps
lem-nat-0-BOX⟨4·30⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-31 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·30⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-30 ∷ []) (Bx4-31 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ03 ∷ []) (CZ13 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx4-31 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;420): 8 steps
lem-nat-0-BOX⟨3·420⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-421 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·420⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-420 ∷ []) (Bx3-421 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Bx4-31 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·30⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx4-31 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·30⟩ c4) ▸
       at 0 6 (Bx3-421 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;3120): 8 steps
lem-nat-0-BOX⟨4·3120⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-3120 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3021 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·3120⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-3120 ∷ []) (Bx4-3021 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-420 ∷ Toff413 ∷ CCZ134 ∷ Bx3-420 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 2 2 (Bx3-421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·420⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx3-421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·420⟩ c4) ▸
       at 0 6 (Bx4-3021 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;412): 8 steps
lem-nat-0-BOX⟨3·412⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-402 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·412⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-412 ∷ []) (Bx3-402 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 2 2 (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 3 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 0 6 (Bx3-402 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;3012): 8 steps
lem-nat-0-BOX⟨4·3012⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·3012⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-3012 ∷ []) (Bx4-3102 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-412 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 2 2 (Bx3-402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·412⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx3-402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·412⟩ c4) ▸
       at 0 6 (Bx4-3102 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;403): 8 steps
lem-nat-1-BOX⟨1·403⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-403 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·403⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-403 ∷ []) (Bx2-403 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 2 2 (Bx4-23 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·13⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx4-23 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·13⟩ c4) ▸
       at 0 6 (Bx2-403 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;1203): 8 steps
lem-nat-1-BOX⟨4·1203⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2103 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·1203⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-1203 ∷ []) (Bx4-2103 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-403 ∷ Toff412 ∷ CCZ124 ∷ Bx1-403 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff412 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·403⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·403⟩ c4) ▸
       at 0 6 (Bx4-2103 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;403): 8 steps
lem-nat-2-BOX⟨2·403⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-403 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-402 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·403⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-403 ∷ []) (Bx3-402 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-23 ∷ Toff204 ∷ CCZ024 ∷ Bx4-23 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 2 2 (Bx4-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·23⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx4-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·23⟩ c4) ▸
       at 0 6 (Bx3-402 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;2103): 8 steps
lem-nat-2-BOX⟨4·2103⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-2103 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·2103⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-2103 ∷ []) (Bx4-3102 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-403 ∷ Toff412 ∷ CCZ124 ∷ Bx2-403 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 2 2 (Bx3-402 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·403⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx3-402 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·403⟩ c4) ▸
       at 0 6 (Bx4-3102 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;402): 8 steps
lem-nat-0-BOX⟨3·402⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-412 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·402⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-402 ∷ []) (Bx3-412 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 2 2 (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 3 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 0 6 (Bx3-412 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;3102): 8 steps
lem-nat-0-BOX⟨4·3102⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-3102 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·3102⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-3102 ∷ []) (Bx4-3012 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-402 ∷ Toff413 ∷ CCZ134 ∷ Bx3-402 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 2 2 (Bx3-412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·402⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx3-412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·402⟩ c4) ▸
       at 0 6 (Bx4-3012 ∷ []) (refl) ▸ done


-- nat 1 CX01: 2 steps
lem-nat-1-CX01 : Complete 4 → ⟪ (Sw12 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CX01 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CX01 ∷ []) (CX02 ∷ Sw12 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm SBOXd(0;1;2;3) TOFF403: 17 steps
lem-comm-SBOXd⟨0·1·2·3⟩-TOFF403 : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-comm-SBOXd⟨0·1·2·3⟩-TOFF403 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Toff403 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CS34⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff403 ∷ CS12⁻ ∷ [])
  b1 = at 4 2 (Toff201 ∷ CS34⁻ ∷ []) (sym (c₃ (Toffᵗ) (CS • CS • CS))) ▸
       at 5 2 (Sw23 ∷ CS24⁻ ∷ []) (lw0 c4 (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ CS13⁻ ∷ []) (lw4 c4 (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 9 (Toff403 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Toff403 ∷ CS12⁻ ∷ []) (Toff403 ∷ Sb⁻0-1-2-3 ∷ [])
  b2 = at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;12): 3 steps
lem-nat-0-BOX⟨4·12⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-02 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·12⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-12 ∷ []) (Bx4-02 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ12 ∷ []) (CZ02 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx4-02 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;402): 8 steps
lem-nat-0-BOX⟨1·402⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-402 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-412 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·402⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-402 ∷ []) (Bx0-412 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 2 2 (Bx4-02 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·12⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx4-02 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·12⟩ c4) ▸
       at 0 6 (Bx0-412 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;1302): 8 steps
lem-nat-0-BOX⟨4·1302⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-1302 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·1302⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-1302 ∷ []) (Bx4-0312 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx1-402 ∷ Toff413 ∷ CCZ134 ∷ Bx1-402 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 2 2 (Bx0-412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·402⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx0-412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·402⟩ c4) ▸
       at 0 6 (Bx4-0312 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;21): 3 steps
lem-nat-1-BOX⟨4·21⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-12 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·21⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-21 ∷ []) (Bx4-12 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ12 ∷ []) (CZ12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx4-12 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;401): 8 steps
lem-nat-1-BOX⟨2·401⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-401 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-402 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·401⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-401 ∷ []) (Bx1-402 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Toff204 ∷ CCZ024 ∷ Bx4-21 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 2 2 (Bx4-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·21⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx4-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·21⟩ c4) ▸
       at 0 6 (Bx1-402 ∷ []) (refl) ▸ done


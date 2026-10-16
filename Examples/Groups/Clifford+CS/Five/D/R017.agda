{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R017 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF034 ; lem-nat-2-TOFF102 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ014 ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-1-TOFF401 ; lem-nat-2-CZ03 ; lem-nat-3-TOFF023 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-2-CZ02 ; lem-nat-2-CZ04)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-CZ01 ; lem-nat-2-CCZ014 ; lem-nat-3-BOX⟨2·03⟩ ; lem-nat-3-CZ03 ; lem-nat-3-CZ04)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-CS04 ; lem-nat-0-CS14 ; lem-nat-1-CS04 ; lem-nat-1-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-TOFF134 ; lem-nat-1-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-BOX⟨1·0324⟩ ; lem-nat-0-TOFF034 ; lem-nat-1-BOX⟨4·02⟩ ; lem-nat-1-BOX⟨4·0312⟩ ; lem-nat-1-CSd04)
-- nat 1 SBOX(4;0;2;1): 3 steps
lem-nat-1-SBOX⟨4·0·2·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-1-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨4·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb4-0-2-1 ∷ []) (Sb4-0-1-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 0 1 (Sb4-0-1-2 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(4;0;2;1): 3 steps
lem-nat-1-SBOXd⟨4·0·2·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-1-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨4·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻4-0-1-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 0 1 (Sb⁻4-0-1-2 ∷ []) (refl) ▸ done


-- nat 1 SBOX(4;0;31;2): 7 steps
lem-nat-1-SBOX⟨4·0·31·2⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb4-0-31-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-32-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨4·0·31·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb4-0-31-2 ∷ []) (Sb4-0-32-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx4-0312 ∷ Toff213 ∷ Sb4-0-2-1 ∷ Toff213 ∷ Sb⁻4-0-2-1 ∷ []) (refl) ▸
       at 0 2 (Bx4-0321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0312⟩ c4) ▸
       at 1 2 (Toff123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb4-0-1-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨4·0·2·1⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻4-0-1-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨4·0·2·1⟩ c4) ▸
       at 0 5 (Sb4-0-32-1 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;04): 3 steps
lem-nat-2-BOX⟨1·04⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·04⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-04 ∷ []) (Bx1-04 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw23 ∷ []) (lem-nat-2-CZ04 c4) ▸
       at 0 1 (Bx1-04 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;134): 8 steps
lem-nat-2-BOX⟨0·134⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-124 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·134⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-134 ∷ []) (Bx0-124 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-04 ∷ Toff013 ∷ CCZ013 ∷ Bx1-04 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 2 2 (Bx1-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·04⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx1-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·04⟩ c4) ▸
       at 0 6 (Bx0-124 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;0234): 8 steps
lem-nat-2-BOX⟨1·0234⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·0234⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-0234 ∷ []) (Bx1-0324 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-134 ∷ Toff102 ∷ CCZ012 ∷ Bx0-134 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 2 2 (Bx0-124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·134⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx0-124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·134⟩ c4) ▸
       at 0 6 (Bx1-0324 ∷ []) (refl) ▸ done


-- nat 2 CS04: 7 steps
lem-nat-2-CS04 : Complete 4 → ⟪ (Sw23 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CS04 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CS04 ∷ []) (CS04 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 3 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 4 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 5 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOX(1;0;4;3): 3 steps
lem-nat-2-SBOX⟨1·0·4·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb1-0-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-4-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-0-4-3 ∷ []) (Sb1-0-4-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 c4) ▸
       at 0 1 (Sb1-0-4-2 ∷ []) (refl) ▸ done


-- nat 2 CSd04: 7 steps
lem-nat-2-CSd04 : Complete 4 → ⟪ (Sw23 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CSd04 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 3 2 (CS01⁻ ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 4 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 5 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOXd(1;0;4;3): 3 steps
lem-nat-2-SBOXd⟨1·0·4·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻1-0-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-4-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-0-4-3 ∷ []) (Sb⁻1-0-4-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 c4) ▸
       at 0 1 (Sb⁻1-0-4-2 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;0;23;4): 7 steps
lem-nat-2-SBOX⟨1·0·23·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb1-0-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-32-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·23·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-0-23-4 ∷ []) (Sb1-0-32-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx1-0234 ∷ Toff423 ∷ Sb1-0-4-3 ∷ Toff423 ∷ Sb⁻1-0-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff423 ∷ []) (Toff423 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-0-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·4·3⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff423 ∷ []) (Toff423 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻1-0-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·4·3⟩ c4) ▸
       at 0 5 (Sb1-0-32-4 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;421): 8 steps
lem-nat-2-BOX⟨0·421⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-431 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·421⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-421 ∷ []) (Bx0-431 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 2 2 (Bx4-01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 3 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx4-01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 0 6 (Bx0-431 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;0321): 8 steps
lem-nat-2-BOX⟨4·0321⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·0321⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-0321 ∷ []) (Bx4-0231 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-421 ∷ Toff403 ∷ CCZ034 ∷ Bx0-421 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 2 2 (Bx0-431 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·421⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx0-431 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·421⟩ c4) ▸
       at 0 6 (Bx4-0231 ∷ []) (refl) ▸ done


-- nat 2 SBOX(4;0;1;2): 2 steps
lem-nat-2-SBOX⟨4·0·1·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb4-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-1-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·0·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb4-0-1-2 ∷ []) (Sb4-0-1-3 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb4-0-1-2 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 0 1 (Sb4-0-1-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOXd(4;0;1;2): 2 steps
lem-nat-2-SBOXd⟨4·0·1·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻4-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-1-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨4·0·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻4-0-1-2 ∷ []) (Sb⁻4-0-1-3 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb⁻4-0-1-2 ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 0 1 (Sb⁻4-0-1-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOX(4;0;32;1): 7 steps
lem-nat-2-SBOX⟨4·0·32·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb4-0-32-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-23-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·0·32·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb4-0-32-1 ∷ []) (Sb4-0-23-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx4-0321 ∷ Toff123 ∷ Sb4-0-1-2 ∷ Toff123 ∷ Sb⁻4-0-1-2 ∷ []) (refl) ▸
       at 0 2 (Bx4-0231 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0321⟩ c4) ▸
       at 1 2 (Toff123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb4-0-1-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·0·1·2⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻4-0-1-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·0·1·2⟩ c4) ▸
       at 0 5 (Sb4-0-23-1 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;1;4;3): 3 steps
lem-nat-0-SBOX⟨0·1·4·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-4-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-1-4-3 ∷ []) (Sb1-0-4-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 c4) ▸
       at 0 1 (Sb1-0-4-3 ∷ []) (refl) ▸ done


-- nat 0 CSd14: 5 steps
lem-nat-0-CSd14 : Complete 4 → ⟪ (Sw01 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CSd14 c4 = run b0
  where
  b0 : Chain (Sw01 ∷ CS14⁻ ∷ []) (CS04⁻ ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CS03⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS13⁻ ∷ []) (CS03⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(0;1;4;3): 3 steps
lem-nat-0-SBOXd⟨0·1·4·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-4-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·1·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻1-0-4-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw01 ∷ []) (lem-nat-0-CSd14 c4) ▸
       at 0 1 (Sb⁻1-0-4-3 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;1;23;4): 7 steps
lem-nat-0-SBOX⟨0·1·23·4⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-23-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·23·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-1-23-4 ∷ []) (Sb1-0-23-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (Sb1-0-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·4·3⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 4 2 (Sb⁻1-0-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 0 5 (Sb1-0-23-4 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;01): 3 steps
lem-nat-0-BOX⟨4·01⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-10 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·01⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-01 ∷ []) (Bx4-10 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ01 ∷ []) (CZ01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx4-10 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;431): 8 steps
lem-nat-0-BOX⟨0·431⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-431 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-430 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·431⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-431 ∷ []) (Bx1-430 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 2 2 (Bx4-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·01⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx4-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·01⟩ c4) ▸
       at 0 6 (Bx1-430 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;0231): 8 steps
lem-nat-0-BOX⟨4·0231⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·0231⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-0231 ∷ []) (Bx4-1230 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-431 ∷ Toff402 ∷ CCZ024 ∷ Bx0-431 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 2 2 (Bx1-430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·431⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx1-430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·431⟩ c4) ▸
       at 0 6 (Bx4-1230 ∷ []) (refl) ▸ done


-- nat 0 SBOX(4;0;1;3): 3 steps
lem-nat-0-SBOX⟨4·0·1·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb4-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨4·0·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb4-0-1-3 ∷ []) (Sb4-1-0-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb4-1-0-3 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(4;0;1;3): 3 steps
lem-nat-0-SBOXd⟨4·0·1·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻4-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-1-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨4·0·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻4-0-1-3 ∷ []) (Sb⁻4-1-0-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 2 (CS01⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻4-1-0-3 ∷ []) (refl) ▸ done


-- nat 0 SBOX(4;0;23;1): 7 steps
lem-nat-0-SBOX⟨4·0·23·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb4-0-23-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-23-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨4·0·23·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb4-0-23-1 ∷ []) (Sb4-1-23-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx4-0231 ∷ Toff123 ∷ Sb4-0-1-3 ∷ Toff123 ∷ Sb⁻4-0-1-3 ∷ []) (refl) ▸
       at 0 2 (Bx4-1230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0231⟩ c4) ▸
       at 1 2 (Toff023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb4-1-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨4·0·1·3⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻4-1-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨4·0·1·3⟩ c4) ▸
       at 0 5 (Sb4-1-23-0 ∷ []) (refl) ▸ done


-- nat 3 TOFF401: 2 steps
lem-nat-3-TOFF401 : Complete 4 → ⟪ (Sw34 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF401 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Toff401 ∷ []) (Toff301 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 3 TOFF024: 80 steps
lem-nat-3-TOFF024 : Complete 4 → ⟪ (Sw34 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF024 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (Sw34 ∷ Toff024 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ [])
  b1 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 11 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b2 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ []) (Sw34 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ [])
  b2 = at 2 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Sw34 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ []) (Sw34 ∷ K0 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b3 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Sw34 ∷ K0 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (Sw34 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b4 = at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw34 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (K0 ∷ CS23 ∷ CX02 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ [])
  b5 = at 7 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 2 2 (CX02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))) ▸
       at 4 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (K0 ∷ CS23 ∷ CX02 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ []) (Sw12 ∷ K0 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b6 = at 3 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CX02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 7 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸ done

  b7 : Chain (Sw12 ∷ K0 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw12 ∷ ι ∷ Sw34 ∷ [])
  b7 = at 2 2 (CS13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CS13⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸ done

  b8 : Chain (Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw12 ∷ ι ∷ Sw34 ∷ []) (Sw12 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b8 = at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b9 : Chain (Sw12 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (Toff023 ∷ Sw34 ∷ [])
  b9 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(4;03): 3 steps
lem-nat-3-BOX⟨4·03⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-04 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·03⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-03 ∷ []) (Bx3-04 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw34 ∷ []) (lem-nat-3-CZ03 c4) ▸
       at 0 1 (Bx3-04 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;423): 8 steps
lem-nat-3-BOX⟨0·423⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-324 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·423⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-423 ∷ []) (Bx0-324 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 2 2 (Bx3-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·03⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx3-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·03⟩ c4) ▸
       at 0 6 (Bx0-324 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;0123): 8 steps
lem-nat-3-BOX⟨4·0123⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·0123⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-0123 ∷ []) (Bx3-0124 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 1 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 2 2 (Bx0-324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·423⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 4 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 5 2 (Bx0-324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·423⟩ c4) ▸
       at 0 6 (Bx3-0124 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;04): 3 steps
lem-nat-3-BOX⟨3·04⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx3-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-03 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·04⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-04 ∷ []) (Bx4-03 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw34 ∷ []) (lem-nat-3-CZ04 c4) ▸
       at 0 1 (Bx4-03 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;324): 8 steps
lem-nat-3-BOX⟨0·324⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-423 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·324⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-324 ∷ []) (Bx0-423 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 2 2 (Bx4-03 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·04⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx4-03 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·04⟩ c4) ▸
       at 0 6 (Bx0-423 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;0124): 8 steps
lem-nat-3-BOX⟨3·0124⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·0124⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-0124 ∷ []) (Bx4-0123 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 2 2 (Bx0-423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·324⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx0-423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·324⟩ c4) ▸
       at 0 6 (Bx4-0123 ∷ []) (refl) ▸ done


-- nat 2 TOFF401: 68 steps
lem-nat-2-TOFF401 : Complete 4 → ⟪ (Sw23 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF401 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (Sw23 ∷ Toff401 ∷ []) (Sw23 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ K4 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ [])
  b1 = at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (K4 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K3 ∷ []) (K4 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ K4 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw34 ∷ [])
  b2 = at 4 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw23 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw34 ∷ []) (K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw23 ∷ CS04 ∷ K4 ∷ ι ∷ [])
  b3 = at 7 2 (K4 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K3 ∷ []) (K4 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 3 2 (CS14⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b4 : Chain (K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw23 ∷ CS04 ∷ K4 ∷ ι ∷ []) (K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ Sw23 ∷ ι ∷ [])
  b4 = at 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸ done

  b5 : Chain (K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ Sw23 ∷ ι ∷ []) (Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ [])
  b5 = at 7 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K4 ∷ []) (K3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 5 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

  b6 : Chain (Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b6 = at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (K3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K4 ∷ []) (K3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (K2 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K3 ∷ []) (K2 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b7 = at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (K2 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K3 ∷ []) (K2 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (Toff401 ∷ Sw23 ∷ [])
  b8 = at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(4;02): 3 steps
lem-nat-2-BOX⟨4·02⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-03 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·02⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-02 ∷ []) (Bx4-03 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4) ▸
       at 0 1 (Bx4-03 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;432): 8 steps
lem-nat-2-BOX⟨0·432⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-423 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·432⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-432 ∷ []) (Bx0-423 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-02 ∷ Toff034 ∷ CCZ034 ∷ Bx4-02 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 2 2 (Bx4-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·02⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx4-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·02⟩ c4) ▸
       at 0 6 (Bx0-423 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;0132): 8 steps
lem-nat-2-BOX⟨4·0132⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-0132 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·0132⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-0132 ∷ []) (Bx4-0123 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-432 ∷ Toff401 ∷ CCZ014 ∷ Bx0-432 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 2 2 (Bx0-423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·432⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx0-423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·432⟩ c4) ▸
       at 0 6 (Bx4-0123 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;03): 3 steps
lem-nat-2-BOX⟨4·03⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-02 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·03⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-03 ∷ []) (Bx4-02 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw23 ∷ []) (lem-nat-2-CZ03 c4) ▸
       at 0 1 (Bx4-02 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;423): 8 steps
lem-nat-2-BOX⟨0·423⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-432 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·423⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-423 ∷ []) (Bx0-432 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 2 2 (Bx4-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·03⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx4-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·03⟩ c4) ▸
       at 0 6 (Bx0-432 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;0123): 8 steps
lem-nat-2-BOX⟨4·0123⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0132 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·0123⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-0123 ∷ []) (Bx4-0132 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 2 2 (Bx0-432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·423⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx0-432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·423⟩ c4) ▸
       at 0 6 (Bx4-0132 ∷ []) (refl) ▸ done


-- nat 1 TOFF402: 2 steps
lem-nat-1-TOFF402 : Complete 4 → ⟪ (Sw12 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF402 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Toff402 ∷ []) (Toff401 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 1 BOX(4;01): 3 steps
lem-nat-1-BOX⟨4·01⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-02 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·01⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-01 ∷ []) (Bx4-02 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 c4) ▸
       at 0 1 (Bx4-02 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;431): 8 steps
lem-nat-1-BOX⟨0·431⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-432 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·431⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-431 ∷ []) (Bx0-432 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Bx4-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·01⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx4-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·01⟩ c4) ▸
       at 0 6 (Bx0-432 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;0231): 8 steps
lem-nat-1-BOX⟨4·0231⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0132 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·0231⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-0231 ∷ []) (Bx4-0132 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-431 ∷ Toff402 ∷ CCZ024 ∷ Bx0-431 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 2 2 (Bx0-432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·431⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx0-432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·431⟩ c4) ▸
       at 0 6 (Bx4-0132 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;432): 8 steps
lem-nat-1-BOX⟨0·432⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-431 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·432⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-432 ∷ []) (Bx0-431 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-02 ∷ Toff034 ∷ CCZ034 ∷ Bx4-02 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Bx4-01 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·02⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx4-01 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·02⟩ c4) ▸
       at 0 6 (Bx0-431 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;0132): 8 steps
lem-nat-1-BOX⟨4·0132⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-0132 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·0132⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-0132 ∷ []) (Bx4-0231 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-432 ∷ Toff401 ∷ CCZ014 ∷ Bx0-432 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 2 2 (Bx0-431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·432⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx0-431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·432⟩ c4) ▸
       at 0 6 (Bx4-0231 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;10): 3 steps
lem-nat-0-BOX⟨4·10⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-01 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·10⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-10 ∷ []) (Bx4-01 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ01 ∷ []) (CZ01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx4-01 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;430): 8 steps
lem-nat-0-BOX⟨1·430⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-430 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-431 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·430⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-430 ∷ []) (Bx0-431 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 2 2 (Bx4-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·10⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx4-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·10⟩ c4) ▸
       at 0 6 (Bx0-431 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;1230): 8 steps
lem-nat-0-BOX⟨4·1230⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·1230⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-1230 ∷ []) (Bx4-0231 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 2 2 (Bx0-431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·430⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx0-431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·430⟩ c4) ▸
       at 0 6 (Bx4-0231 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;243): 8 steps
lem-nat-3-BOX⟨0·243⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-234 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·243⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-243 ∷ []) (Bx0-234 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 2 2 (Bx2-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·03⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx2-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·03⟩ c4) ▸
       at 0 6 (Bx0-234 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;0143): 8 steps
lem-nat-3-BOX⟨2·0143⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·0143⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-0143 ∷ []) (Bx2-0134 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 2 2 (Bx0-234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·243⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx0-234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·243⟩ c4) ▸
       at 0 6 (Bx2-0134 ∷ []) (refl) ▸ done


-- nat 3 CS03: 2 steps
lem-nat-3-CS03 : Complete 4 → ⟪ (Sw34 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CS03 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CS03 ∷ []) (CS04 ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOX(2;0;3;4): 3 steps
lem-nat-3-SBOX⟨2·0·3·4⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb2-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-4-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-0-3-4 ∷ []) (Sb2-0-4-3 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 c4) ▸
       at 0 1 (Sb2-0-4-3 ∷ []) (refl) ▸ done


-- nat 3 CSd03: 2 steps
lem-nat-3-CSd03 : Complete 4 → ⟪ (Sw34 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CSd03 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CS03⁻ ∷ []) (CS04⁻ ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(2;0;3;4): 3 steps
lem-nat-3-SBOXd⟨2·0·3·4⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻2-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-4-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·0·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-0-3-4 ∷ []) (Sb⁻2-0-4-3 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd03 c4) ▸
       at 0 1 (Sb⁻2-0-4-3 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;0;14;3): 7 steps
lem-nat-3-SBOX⟨2·0·14·3⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb2-0-14-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-13-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·14·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-0-14-3 ∷ []) (Sb2-0-13-4 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx2-0143 ∷ Toff314 ∷ Sb2-0-3-4 ∷ Toff314 ∷ Sb⁻2-0-3-4 ∷ []) (refl) ▸
       at 0 2 (Bx2-0134 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·0143⟩ c4) ▸
       at 1 2 (Toff413 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff314 ∷ []) (Toff413 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb2-0-4-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·3·4⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff314 ∷ []) (Toff413 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻2-0-4-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·3·4⟩ c4) ▸
       at 0 5 (Sb2-0-13-4 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;0;4;3): 3 steps
lem-nat-1-SBOX⟨2·0·4·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb2-0-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-4-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·0·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-0-4-3 ∷ []) (Sb1-0-4-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 c4) ▸
       at 0 1 (Sb1-0-4-3 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;0;4;3): 3 steps
lem-nat-1-SBOXd⟨2·0·4·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻2-0-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-4-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·0·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-0-4-3 ∷ []) (Sb⁻1-0-4-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd04 c4) ▸
       at 0 1 (Sb⁻1-0-4-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;0;13;4): 7 steps
lem-nat-1-SBOX⟨2·0·13·4⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb2-0-13-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-23-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·0·13·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-0-13-4 ∷ []) (Sb1-0-23-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx2-0134 ∷ Toff413 ∷ Sb2-0-4-3 ∷ Toff413 ∷ Sb⁻2-0-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-0-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·4·3⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻1-0-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·4·3⟩ c4) ▸
       at 0 5 (Sb1-0-23-4 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;0;4;2): 3 steps
lem-nat-0-SBOX⟨1·0·4·2⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb1-0-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·0·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-0-4-2 ∷ []) (Sb0-1-4-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 c4) ▸
       at 0 1 (Sb0-1-4-2 ∷ []) (refl) ▸ done


-- nat 0 CSd04: 5 steps
lem-nat-0-CSd04 : Complete 4 → ⟪ (Sw01 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CSd04 c4 = run b0
  where
  b0 : Chain (Sw01 ∷ CS04⁻ ∷ []) (CS14⁻ ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CS13⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS03⁻ ∷ []) (CS13⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(1;0;4;2): 3 steps
lem-nat-0-SBOXd⟨1·0·4·2⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻1-0-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·0·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻1-0-4-2 ∷ []) (Sb⁻0-1-4-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw01 ∷ []) (lem-nat-0-CSd04 c4) ▸
       at 0 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;0;32;4): 7 steps
lem-nat-0-SBOX⟨1·0·32·4⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·0·32·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-0-32-4 ∷ []) (Sb0-1-32-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx1-0324 ∷ Toff423 ∷ Sb1-0-4-2 ∷ Toff423 ∷ Sb⁻1-0-4-2 ∷ []) (refl) ▸
       at 0 2 (Bx0-1324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (Sb0-1-4-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·4·2⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 4 2 (Sb⁻0-1-4-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·4·2⟩ c4) ▸
       at 0 5 (Sb0-1-32-4 ∷ []) (refl) ▸ done


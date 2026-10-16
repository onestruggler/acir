{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R018 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF014 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF102 ; lem-nat-2-TOFF103 ; lem-nat-2-TOFF301 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-CCZ034 ; lem-nat-3-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-2-TOFF201 ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-1-TOFF103 ; lem-nat-3-TOFF203)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-CZ14 ; lem-nat-3-TOFF214 ; lem-nat-3-TOFF304)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-CZ04 ; lem-nat-0-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-1-TOFF013 ; lem-nat-3-TOFF023 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-CZ04 ; lem-nat-1-TOFF023 ; lem-nat-2-CZ02 ; lem-nat-2-CZ04)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-CZ02 ; lem-nat-3-CZ03 ; lem-nat-3-CZ04)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-2-BOXd⟨0·1324⟩ ; lem-nat-2-BOXd⟨0·14⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-TOFF034 ; lem-nat-1-SBOX⟨1·0·4·2⟩ ; lem-nat-1-SBOXd⟨1·0·4·2⟩ ; lem-nat-1-TOFF403 ; lem-nat-3-SBOX⟨2·0·4·1⟩ ; lem-nat-3-SBOX⟨3·0·2·1⟩ ; lem-nat-3-SBOXd⟨2·0·4·1⟩ ; lem-nat-3-SBOXd⟨3·0·2·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-0-SBOX⟨0·1·4·3⟩ ; lem-nat-0-SBOX⟨1·0·4·2⟩ ; lem-nat-0-SBOX⟨4·0·1·3⟩ ; lem-nat-0-SBOXd⟨0·1·4·3⟩ ; lem-nat-0-SBOXd⟨1·0·4·2⟩ ; lem-nat-0-SBOXd⟨4·0·1·3⟩ ; lem-nat-1-SBOX⟨2·0·4·3⟩ ; lem-nat-1-SBOX⟨4·0·2·1⟩ ; lem-nat-1-SBOXd⟨2·0·4·3⟩ ; lem-nat-1-SBOXd⟨4·0·2·1⟩ ; lem-nat-2-SBOX⟨1·0·4·3⟩ ; lem-nat-2-SBOX⟨4·0·1·2⟩ ; lem-nat-2-SBOXd⟨1·0·4·3⟩ ; lem-nat-2-SBOXd⟨4·0·1·2⟩ ; lem-nat-3-SBOX⟨2·0·3·4⟩ ; lem-nat-3-SBOXd⟨2·0·3·4⟩ ; lem-nat-3-TOFF024 ; lem-nat-3-TOFF401)
-- nat 3 BOXd(2;04): 3 steps
lem-nat-3-BOXd⟨2·04⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-03 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨2·04⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻2-04 ∷ []) (Bx⁻2-03 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw34 ∷ []) (lem-nat-3-CZ04 c4) ▸
       at 0 1 (Bx⁻2-03 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;214): 8 steps
lem-nat-3-BOXd⟨0·214⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻0-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-213 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·214⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-214 ∷ []) (Bx⁻0-213 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻2-04 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-04 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-03 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·04⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 3 2 (Bx⁻2-03 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·04⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 5 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 0 6 (Bx⁻0-213 ∷ []) (refl) ▸ done


-- nat 3 BOXd(2;0314): 8 steps
lem-nat-3-BOXd⟨2·0314⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0413 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨2·0314⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻2-0314 ∷ []) (Bx⁻2-0413 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-214 ∷ CCZ023 ∷ Toff203 ∷ Bx⁻0-214 ∷ Toff203 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-213 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·214⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 2 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 3 2 (Bx⁻0-213 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·214⟩ c4) ▸
       at 4 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 5 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 0 6 (Bx⁻2-0413 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(2;0;31;4): 7 steps
lem-nat-3-SBOXd⟨2·0·31·4⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-41-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·0·31·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-0-31-4 ∷ []) (Sb⁻2-0-41-3 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sb2-0-4-1 ∷ Toff413 ∷ Sb⁻2-0-4-1 ∷ Toff413 ∷ Bx⁻2-0314 ∷ []) (refl) ▸
       at 0 2 (Sb2-0-3-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·4·1⟩ c4) ▸
       at 1 2 (Toff314 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff413 ∷ []) (Toff314 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻2-0-3-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·4·1⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff413 ∷ []) (Toff314 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻2-0413 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·0314⟩ c4) ▸
       at 0 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸ done


-- nat 3 BOXd(2;03): 3 steps
lem-nat-3-BOXd⟨2·03⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-04 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨2·03⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻2-03 ∷ []) (Bx⁻2-04 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw34 ∷ []) (lem-nat-3-CZ03 c4) ▸
       at 0 1 (Bx⁻2-04 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;243): 8 steps
lem-nat-3-BOXd⟨0·243⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻0-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-234 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·243⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-243 ∷ []) (Bx⁻0-234 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻2-03 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-03 ∷ Toff024 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-04 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·03⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 2 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 3 2 (Bx⁻2-04 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·03⟩ c4) ▸
       at 4 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 5 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 0 6 (Bx⁻0-234 ∷ []) (refl) ▸ done


-- nat 3 BOXd(2;0143): 8 steps
lem-nat-3-BOXd⟨2·0143⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0134 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨2·0143⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻2-0143 ∷ []) (Bx⁻2-0134 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-243 ∷ CCZ012 ∷ Toff201 ∷ Bx⁻0-243 ∷ Toff201 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-234 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·243⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 3 2 (Bx⁻0-234 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·243⟩ c4) ▸
       at 4 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 5 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 0 6 (Bx⁻2-0134 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(2;0;14;3): 7 steps
lem-nat-3-SBOXd⟨2·0·14·3⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻2-0-14-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-13-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·0·14·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-0-14-3 ∷ []) (Sb⁻2-0-13-4 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sb2-0-3-4 ∷ Toff314 ∷ Sb⁻2-0-3-4 ∷ Toff314 ∷ Bx⁻2-0143 ∷ []) (refl) ▸
       at 0 2 (Sb2-0-4-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·3·4⟩ c4) ▸
       at 1 2 (Toff413 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff314 ∷ []) (Toff413 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻2-0-4-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·3·4⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff314 ∷ []) (Toff413 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻2-0134 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·0143⟩ c4) ▸
       at 0 5 (Sb⁻2-0-13-4 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;04): 3 steps
lem-nat-1-BOXd⟨1·04⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻1-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-04 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·04⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-04 ∷ []) (Bx⁻2-04 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw12 ∷ []) (lem-nat-1-CZ04 c4) ▸
       at 0 1 (Bx⁻2-04 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;124): 8 steps
lem-nat-1-BOXd⟨0·124⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-214 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·124⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-124 ∷ []) (Bx⁻0-214 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻1-04 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-04 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-04 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·04⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻2-04 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·04⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻0-214 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;0324): 8 steps
lem-nat-1-BOXd⟨1·0324⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0314 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·0324⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-0324 ∷ []) (Bx⁻2-0314 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-124 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-124 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-214 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·124⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 2 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 3 2 (Bx⁻0-214 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·124⟩ c4) ▸
       at 4 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 5 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 0 6 (Bx⁻2-0314 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;0;32;4): 7 steps
lem-nat-1-SBOXd⟨1·0·32·4⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-31-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·0·32·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-0-32-4 ∷ []) (Sb⁻2-0-31-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb1-0-4-2 ∷ Toff423 ∷ Sb⁻1-0-4-2 ∷ Toff423 ∷ Bx⁻1-0324 ∷ []) (refl) ▸
       at 0 2 (Sb2-0-4-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·4·2⟩ c4) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻2-0-4-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·4·2⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻2-0314 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·0324⟩ c4) ▸
       at 0 5 (Sb⁻2-0-31-4 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;04): 3 steps
lem-nat-1-BOXd⟨2·04⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-04 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·04⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-04 ∷ []) (Bx⁻1-04 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw12 ∷ []) (lem-nat-1-CZ04 c4) ▸
       at 0 1 (Bx⁻1-04 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;234): 8 steps
lem-nat-1-BOXd⟨0·234⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-134 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·234⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-234 ∷ []) (Bx⁻0-134 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻2-04 ∷ CCZ023 ∷ Toff023 ∷ Bx⁻2-04 ∷ Toff023 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-04 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·04⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 3 2 (Bx⁻1-04 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·04⟩ c4) ▸
       at 4 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 5 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 0 6 (Bx⁻0-134 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;0134): 8 steps
lem-nat-1-BOXd⟨2·0134⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0234 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·0134⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-0134 ∷ []) (Bx⁻1-0234 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-234 ∷ CCZ012 ∷ Toff201 ∷ Bx⁻0-234 ∷ Toff201 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-134 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·234⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻0-134 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·234⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻1-0234 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;0;13;4): 7 steps
lem-nat-1-SBOXd⟨2·0·13·4⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻2-0-13-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-23-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·0·13·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-0-13-4 ∷ []) (Sb⁻1-0-23-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb2-0-4-3 ∷ Toff413 ∷ Sb⁻2-0-4-3 ∷ Toff413 ∷ Bx⁻2-0134 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·4·3⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻1-0-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·4·3⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0134⟩ c4) ▸
       at 0 5 (Sb⁻1-0-23-4 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;04): 3 steps
lem-nat-2-BOXd⟨1·04⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·04⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-04 ∷ []) (Bx⁻1-04 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw23 ∷ []) (lem-nat-2-CZ04 c4) ▸
       at 0 1 (Bx⁻1-04 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;134): 8 steps
lem-nat-2-BOXd⟨0·134⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻0-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-124 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·134⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-134 ∷ []) (Bx⁻0-124 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-04 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-04 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-04 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·04⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 3 2 (Bx⁻1-04 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·04⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 5 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 0 6 (Bx⁻0-124 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;0234): 8 steps
lem-nat-2-BOXd⟨1·0234⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0324 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·0234⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-0234 ∷ []) (Bx⁻1-0324 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-134 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-134 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-124 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·134⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 3 2 (Bx⁻0-124 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·134⟩ c4) ▸
       at 4 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 5 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 0 6 (Bx⁻1-0324 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;0;23;4): 7 steps
lem-nat-2-SBOXd⟨1·0·23·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻1-0-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-32-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·23·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-0-23-4 ∷ []) (Sb⁻1-0-32-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb1-0-4-3 ∷ Toff423 ∷ Sb⁻1-0-4-3 ∷ Toff423 ∷ Bx⁻1-0234 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·4·3⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff423 ∷ []) (Toff423 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻1-0-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·4·3⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff423 ∷ []) (Toff423 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·0234⟩ c4) ▸
       at 0 5 (Sb⁻1-0-32-4 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;14): 3 steps
lem-nat-0-BOXd⟨0·14⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻0-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-04 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·14⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-14 ∷ []) (Bx⁻1-04 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw01 ∷ []) (lem-nat-0-CZ14 c4) ▸
       at 0 1 (Bx⁻1-04 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;034): 8 steps
lem-nat-0-BOXd⟨1·034⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-134 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·034⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-034 ∷ []) (Bx⁻0-134 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻0-14 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-14 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-04 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·14⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻1-04 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·14⟩ c4) ▸
       at 4 2 (Toff013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻0-134 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;1234): 8 steps
lem-nat-0-BOXd⟨0·1234⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0234 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-1234 ∷ []) (Bx⁻1-0234 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-034 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-034 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-134 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·034⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻0-134 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·034⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻1-0234 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(0;1;23;4): 7 steps
lem-nat-0-SBOXd⟨0·1·23·4⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-23-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·1·23·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-1-23-4 ∷ []) (Sb⁻1-0-23-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·4·3⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (Sb⁻1-0-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 4 2 (Bx⁻1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·1234⟩ c4) ▸
       at 0 5 (Sb⁻1-0-23-4 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;04): 3 steps
lem-nat-0-BOXd⟨1·04⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-14 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·04⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-04 ∷ []) (Bx⁻0-14 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw01 ∷ []) (lem-nat-0-CZ04 c4) ▸
       at 0 1 (Bx⁻0-14 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;124): 8 steps
lem-nat-0-BOXd⟨0·124⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻0-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-024 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·124⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-124 ∷ []) (Bx⁻1-024 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-04 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-04 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-14 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·04⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻0-14 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·04⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻1-024 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;0324): 8 steps
lem-nat-0-BOXd⟨1·0324⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1324 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·0324⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-0324 ∷ []) (Bx⁻0-1324 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻0-124 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-124 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-024 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·124⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻1-024 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·124⟩ c4) ▸
       at 4 2 (Toff013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻0-1324 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(1;0;32;4): 7 steps
lem-nat-0-SBOXd⟨1·0·32·4⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-32-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·0·32·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻1-0-32-4 ∷ []) (Sb⁻0-1-32-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb1-0-4-2 ∷ Toff423 ∷ Sb⁻1-0-4-2 ∷ Toff423 ∷ Bx⁻1-0324 ∷ []) (refl) ▸
       at 0 2 (Sb0-1-4-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·4·2⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (Sb⁻0-1-4-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·4·2⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 4 2 (Bx⁻0-1324 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0324⟩ c4) ▸
       at 0 5 (Sb⁻0-1-32-4 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;1;32;4): 7 steps
lem-nat-2-SBOXd⟨0·1·32·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·1·32·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-1-32-4 ∷ []) (Sb⁻0-1-23-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ []) (refl) ▸
       at 0 2 (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff423 ∷ []) (Toff423 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff423 ∷ []) (Toff423 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1324⟩ c4) ▸
       at 0 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;034): 8 steps
lem-nat-2-BOXd⟨1·034⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-024 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·034⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-034 ∷ []) (Bx⁻1-024 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-14 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-14 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-14 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·14⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 3 2 (Bx⁻0-14 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·14⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 5 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 0 6 (Bx⁻1-024 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;1234): 8 steps
lem-nat-2-BOXd⟨0·1234⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1324 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-1234 ∷ []) (Bx⁻0-1324 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-034 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-034 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-024 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·034⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 3 2 (Bx⁻1-024 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·034⟩ c4) ▸
       at 4 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 5 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 0 6 (Bx⁻0-1324 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;1;23;4): 7 steps
lem-nat-2-SBOXd⟨0·1·23·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·1·23·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-1-23-4 ∷ []) (Sb⁻0-1-32-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 0 2 (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff423 ∷ []) (Toff423 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff423 ∷ []) (Toff423 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1234⟩ c4) ▸
       at 0 5 (Sb⁻0-1-32-4 ∷ []) (refl) ▸ done


-- nat 3 BOXd(3;02): 2 steps
lem-nat-3-BOXd⟨3·02⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻3-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-02 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨3·02⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻3-02 ∷ []) (Bx⁻4-02 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Bx⁻3-02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 0 1 (Bx⁻4-02 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOXd(0;312): 8 steps
lem-nat-3-BOXd⟨0·312⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻0-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-412 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·312⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-312 ∷ []) (Bx⁻0-412 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻3-02 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻3-02 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-02 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·02⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 3 2 (Bx⁻4-02 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·02⟩ c4) ▸
       at 4 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 5 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 0 6 (Bx⁻0-412 ∷ []) (refl) ▸ done


-- nat 3 BOXd(3;0412): 8 steps
lem-nat-3-BOXd⟨3·0412⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0312 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨3·0412⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻3-0412 ∷ []) (Bx⁻4-0312 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-312 ∷ CCZ034 ∷ Toff304 ∷ Bx⁻0-312 ∷ Toff304 ∷ CCZ034 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-412 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·312⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 2 2 (Toff403 ∷ Sw34 ∷ []) (lem-nat-3-TOFF304 c4) ▸
       at 3 2 (Bx⁻0-412 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·312⟩ c4) ▸
       at 4 2 (Toff403 ∷ Sw34 ∷ []) (lem-nat-3-TOFF304 c4) ▸
       at 5 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 0 6 (Bx⁻4-0312 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(3;0;41;2): 7 steps
lem-nat-3-SBOXd⟨3·0·41·2⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-31-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨3·0·41·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻3-0-41-2 ∷ []) (Sb⁻4-0-31-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ Toff214 ∷ Bx⁻3-0412 ∷ []) (refl) ▸
       at 0 2 (Sb4-0-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨3·0·2·1⟩ c4) ▸
       at 1 2 (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 c4) ▸
       at 2 2 (Sb⁻4-0-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨3·0·2·1⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 c4) ▸
       at 4 2 (Bx⁻4-0312 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·0412⟩ c4) ▸
       at 0 5 (Sb⁻4-0-31-2 ∷ []) (refl) ▸ done


-- nat 1 BOXd(4;02): 3 steps
lem-nat-1-BOXd⟨4·02⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻4-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-01 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·02⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻4-02 ∷ []) (Bx⁻4-01 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw12 ∷ []) (lem-nat-1-CZ02 c4) ▸
       at 0 1 (Bx⁻4-01 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;412): 8 steps
lem-nat-1-BOXd⟨0·412⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-412 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-421 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·412⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-412 ∷ []) (Bx⁻0-421 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻4-02 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻4-02 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-01 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·02⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 3 2 (Bx⁻4-01 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·02⟩ c4) ▸
       at 4 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 5 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-421 ∷ []) (refl) ▸ done


-- nat 1 BOXd(4;0312): 8 steps
lem-nat-1-BOXd⟨4·0312⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0321 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·0312⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻4-0312 ∷ []) (Bx⁻4-0321 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-412 ∷ CCZ034 ∷ Toff403 ∷ Bx⁻0-412 ∷ Toff403 ∷ CCZ034 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-421 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·412⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 2 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 3 2 (Bx⁻0-421 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·412⟩ c4) ▸
       at 4 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 5 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 0 6 (Bx⁻4-0321 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(4;0;31;2): 7 steps
lem-nat-1-SBOXd⟨4·0·31·2⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻4-0-31-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-32-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨4·0·31·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻4-0-31-2 ∷ []) (Sb⁻4-0-32-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb4-0-2-1 ∷ Toff213 ∷ Sb⁻4-0-2-1 ∷ Toff213 ∷ Bx⁻4-0312 ∷ []) (refl) ▸
       at 0 2 (Sb4-0-1-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨4·0·2·1⟩ c4) ▸
       at 1 2 (Toff123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻4-0-1-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨4·0·2·1⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻4-0321 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·0312⟩ c4) ▸
       at 0 5 (Sb⁻4-0-32-1 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;421): 8 steps
lem-nat-2-BOXd⟨0·421⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻0-421 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-431 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·421⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-421 ∷ []) (Bx⁻0-431 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻4-01 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻4-01 ∷ Toff024 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 1 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 2 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 3 2 (Bx⁻4-01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 4 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 5 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 0 6 (Bx⁻0-431 ∷ []) (refl) ▸ done


-- nat 2 BOXd(4;0321): 8 steps
lem-nat-2-BOXd⟨4·0321⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0231 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨4·0321⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻4-0321 ∷ []) (Bx⁻4-0231 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-421 ∷ CCZ034 ∷ Toff403 ∷ Bx⁻0-421 ∷ Toff403 ∷ CCZ034 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-431 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·421⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 2 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 3 2 (Bx⁻0-431 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·421⟩ c4) ▸
       at 4 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 5 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 0 6 (Bx⁻4-0231 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(4;0;32;1): 7 steps
lem-nat-2-SBOXd⟨4·0·32·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻4-0-32-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-23-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨4·0·32·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻4-0-32-1 ∷ []) (Sb⁻4-0-23-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb4-0-1-2 ∷ Toff123 ∷ Sb⁻4-0-1-2 ∷ Toff123 ∷ Bx⁻4-0321 ∷ []) (refl) ▸
       at 0 2 (Sb4-0-1-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·0·1·2⟩ c4) ▸
       at 1 2 (Toff123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻4-0-1-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·0·1·2⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻4-0231 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·0321⟩ c4) ▸
       at 0 5 (Sb⁻4-0-23-1 ∷ []) (refl) ▸ done


-- nat 0 BOXd(4;01): 3 steps
lem-nat-0-BOXd⟨4·01⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻4-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-10 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·01⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻4-01 ∷ []) (Bx⁻4-10 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ01 ∷ []) (CZ01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻4-10 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;431): 8 steps
lem-nat-0-BOXd⟨0·431⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻0-431 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-430 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·431⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-431 ∷ []) (Bx⁻1-430 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻4-01 ∷ CCZ034 ∷ Toff034 ∷ Bx⁻4-01 ∷ Toff034 ∷ CCZ034 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-10 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·01⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 2 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 3 2 (Bx⁻4-10 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·01⟩ c4) ▸
       at 4 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 5 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 0 6 (Bx⁻1-430 ∷ []) (refl) ▸ done


-- nat 0 BOXd(4;0231): 8 steps
lem-nat-0-BOXd⟨4·0231⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-1230 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·0231⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻4-0231 ∷ []) (Bx⁻4-1230 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻0-431 ∷ CCZ024 ∷ Toff402 ∷ Bx⁻0-431 ∷ Toff402 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-430 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·431⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 2 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 3 2 (Bx⁻1-430 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·431⟩ c4) ▸
       at 4 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 5 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 0 6 (Bx⁻4-1230 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(4;0;23;1): 7 steps
lem-nat-0-SBOXd⟨4·0·23·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻4-0-23-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-1-23-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨4·0·23·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻4-0-23-1 ∷ []) (Sb⁻4-1-23-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb4-0-1-3 ∷ Toff123 ∷ Sb⁻4-0-1-3 ∷ Toff123 ∷ Bx⁻4-0231 ∷ []) (refl) ▸
       at 0 2 (Sb4-1-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨4·0·1·3⟩ c4) ▸
       at 1 2 (Toff023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻4-1-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨4·0·1·3⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻4-1230 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·0231⟩ c4) ▸
       at 0 5 (Sb⁻4-1-23-0 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;134): 8 steps
lem-nat-0-BOXd⟨0·134⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻0-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-034 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·134⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-134 ∷ []) (Bx⁻1-034 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-04 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-04 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-14 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·04⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻0-14 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·04⟩ c4) ▸
       at 4 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻1-034 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;0234): 8 steps
lem-nat-0-BOXd⟨1·0234⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1234 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·0234⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-0234 ∷ []) (Bx⁻0-1234 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻0-134 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-134 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-034 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·134⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻1-034 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·134⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻0-1234 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;134): 8 steps
lem-nat-1-BOXd⟨0·134⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-234 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·134⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-134 ∷ []) (Bx⁻0-234 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻1-04 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-04 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-04 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·04⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 2 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 3 2 (Bx⁻2-04 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·04⟩ c4) ▸
       at 4 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 5 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 0 6 (Bx⁻0-234 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;0234): 8 steps
lem-nat-1-BOXd⟨1·0234⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0134 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·0234⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-0234 ∷ []) (Bx⁻2-0134 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-134 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-134 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-234 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·134⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻0-234 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·134⟩ c4) ▸
       at 4 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻2-0134 ∷ []) (refl) ▸ done


-- nat 2 BOXd(3;04): 3 steps
lem-nat-2-BOXd⟨3·04⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻3-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨3·04⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻3-04 ∷ []) (Bx⁻2-04 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw23 ∷ []) (lem-nat-2-CZ04 c4) ▸
       at 0 1 (Bx⁻2-04 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;324): 8 steps
lem-nat-2-BOXd⟨0·324⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻0-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-234 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·324⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-324 ∷ []) (Bx⁻0-234 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻3-04 ∷ CCZ023 ∷ Toff023 ∷ Bx⁻3-04 ∷ Toff023 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-04 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·04⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻2-04 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·04⟩ c4) ▸
       at 4 2 (Toff023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻0-234 ∷ []) (refl) ▸ done


-- nat 2 BOXd(3;0124): 8 steps
lem-nat-2-BOXd⟨3·0124⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0134 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨3·0124⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻3-0124 ∷ []) (Bx⁻2-0134 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-324 ∷ CCZ013 ∷ Toff301 ∷ Bx⁻0-324 ∷ Toff301 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-234 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·324⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 3 2 (Bx⁻0-234 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·324⟩ c4) ▸
       at 4 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 5 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 0 6 (Bx⁻2-0134 ∷ []) (refl) ▸ done


-- nat 2 BOXd(2;04): 3 steps
lem-nat-2-BOXd⟨2·04⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨2·04⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻2-04 ∷ []) (Bx⁻3-04 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw23 ∷ []) (lem-nat-2-CZ04 c4) ▸
       at 0 1 (Bx⁻3-04 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;234): 8 steps
lem-nat-2-BOXd⟨0·234⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻0-234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-324 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·234⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-234 ∷ []) (Bx⁻0-324 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻2-04 ∷ CCZ023 ∷ Toff023 ∷ Bx⁻2-04 ∷ Toff023 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻3-04 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨2·04⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻3-04 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨2·04⟩ c4) ▸
       at 4 2 (Toff023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻0-324 ∷ []) (refl) ▸ done


-- nat 2 BOXd(2;0134): 8 steps
lem-nat-2-BOXd⟨2·0134⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-0124 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨2·0134⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻2-0134 ∷ []) (Bx⁻3-0124 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-234 ∷ CCZ012 ∷ Toff201 ∷ Bx⁻0-234 ∷ Toff201 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-324 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·234⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 3 2 (Bx⁻0-324 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·234⟩ c4) ▸
       at 4 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 5 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 0 6 (Bx⁻3-0124 ∷ []) (refl) ▸ done


-- nat 3 BOXd(4;03): 3 steps
lem-nat-3-BOXd⟨4·03⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-04 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨4·03⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻4-03 ∷ []) (Bx⁻3-04 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw34 ∷ []) (lem-nat-3-CZ03 c4) ▸
       at 0 1 (Bx⁻3-04 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;423): 8 steps
lem-nat-3-BOXd⟨0·423⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻0-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-324 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·423⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-423 ∷ []) (Bx⁻0-324 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻4-03 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻4-03 ∷ Toff024 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻3-04 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·03⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 2 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 3 2 (Bx⁻3-04 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·03⟩ c4) ▸
       at 4 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 5 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 0 6 (Bx⁻0-324 ∷ []) (refl) ▸ done


-- nat 3 BOXd(4;0123): 8 steps
lem-nat-3-BOXd⟨4·0123⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-0124 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨4·0123⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻4-0123 ∷ []) (Bx⁻3-0124 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-423 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻0-423 ∷ Toff401 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-324 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·423⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 3 2 (Bx⁻0-324 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·423⟩ c4) ▸
       at 4 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 5 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 0 6 (Bx⁻3-0124 ∷ []) (refl) ▸ done


-- nat 3 BOXd(3;04): 3 steps
lem-nat-3-BOXd⟨3·04⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻3-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-03 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨3·04⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻3-04 ∷ []) (Bx⁻4-03 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw34 ∷ []) (lem-nat-3-CZ04 c4) ▸
       at 0 1 (Bx⁻4-03 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;324): 8 steps
lem-nat-3-BOXd⟨0·324⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻0-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-423 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·324⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-324 ∷ []) (Bx⁻0-423 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻3-04 ∷ CCZ023 ∷ Toff023 ∷ Bx⁻3-04 ∷ Toff023 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-03 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·04⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 2 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 3 2 (Bx⁻4-03 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·04⟩ c4) ▸
       at 4 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 5 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 0 6 (Bx⁻0-423 ∷ []) (refl) ▸ done


-- nat 3 BOXd(3;0124): 8 steps
lem-nat-3-BOXd⟨3·0124⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0123 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨3·0124⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻3-0124 ∷ []) (Bx⁻4-0123 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-324 ∷ CCZ013 ∷ Toff301 ∷ Bx⁻0-324 ∷ Toff301 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-423 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·324⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 3 2 (Bx⁻0-423 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·324⟩ c4) ▸
       at 4 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 5 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 0 6 (Bx⁻4-0123 ∷ []) (refl) ▸ done


-- nat 2 BOXd(4;02): 3 steps
lem-nat-2-BOXd⟨4·02⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻4-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-03 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨4·02⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻4-02 ∷ []) (Bx⁻4-03 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4) ▸
       at 0 1 (Bx⁻4-03 ∷ []) (refl) ▸ done


{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R027 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-2-CCZ012 ; lem-nat-3-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ014 ; lem-nat-2-TOFF201 ; lem-nat-3-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-TOFF302 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF304 ; lem-nat-3-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF014 ; lem-nat-0-TOFF104 ; lem-nat-0-TOFF412 ; lem-nat-1-TOFF104 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-TOFF304 ; lem-nat-0-TOFF314)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-TOFF204 ; lem-nat-3-CZ23)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-TOFF214 ; lem-nat-0-TOFF402 ; lem-nat-1-TOFF304)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-1-TOFF401 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-BOX⟨2·0413⟩ ; lem-nat-3-CS23)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-2-TOFF124)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-2-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-2-TOFF134)
open import Examples.Groups.Clifford+CS.Five.D.R024 using (lem-nat-0-SBOX⟨2·1·3·0⟩ ; lem-nat-0-SBOXd⟨2·1·3·0⟩ ; lem-nat-1-BOX⟨2·1403⟩)
open import Examples.Groups.Clifford+CS.Five.D.R025 using (lem-nat-0-BOX⟨2·3401⟩ ; lem-nat-0-BOX⟨2·3410⟩ ; lem-nat-1-BOX⟨1·3402⟩ ; lem-nat-1-BOX⟨2·3401⟩ ; lem-nat-2-SBOX⟨1·4·2·0⟩ ; lem-nat-2-SBOXd⟨1·4·2·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R026 using (lem-nat-3-BOX⟨2·4310⟩ ; lem-nat-3-SBOX⟨2·4·0·1⟩ ; lem-nat-3-SBOXd⟨2·4·0·1⟩)
-- nat 3 SBOX(2;4;31;0): 7 steps
lem-nat-3-SBOX⟨2·4·31·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb2-4-31-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-41-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·4·31·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-4-31-0 ∷ []) (Sb2-3-41-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx2-4310 ∷ Toff013 ∷ Sb2-4-0-1 ∷ Toff013 ∷ Sb⁻2-4-0-1 ∷ []) (refl) ▸
       at 0 2 (Bx2-3410 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·4310⟩ c4) ▸
       at 1 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 2 2 (Sb2-3-0-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·4·0·1⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 4 2 (Sb⁻2-3-0-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·4·0·1⟩ c4) ▸
       at 0 5 (Sb2-3-41-0 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;3;1;0): 3 steps
lem-nat-0-SBOX⟨2·3·1·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb2-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-0-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-3-1-0 ∷ []) (Sb2-3-0-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS13 ∷ []) (CS03 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb2-3-0-1 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;3;1;0): 3 steps
lem-nat-0-SBOXd⟨2·3·1·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻2-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-0-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·3·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-3-1-0 ∷ []) (Sb⁻2-3-0-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS13⁻ ∷ []) (CS03⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻2-3-0-1 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;3;40;1): 7 steps
lem-nat-0-SBOX⟨2·3·40·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb2-3-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-41-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·40·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-3-40-1 ∷ []) (Sb2-3-41-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx2-3401 ∷ Toff104 ∷ Sb2-3-1-0 ∷ Toff104 ∷ Sb⁻2-3-1-0 ∷ []) (refl) ▸
       at 0 2 (Bx2-3410 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3401⟩ c4) ▸
       at 1 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 2 2 (Sb2-3-0-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·1·0⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 4 2 (Sb⁻2-3-0-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·3·1·0⟩ c4) ▸
       at 0 5 (Sb2-3-41-0 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;3;0;1): 3 steps
lem-nat-0-SBOX⟨2·3·0·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb2-3-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-1-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-3-0-1 ∷ []) (Sb2-3-1-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS03 ∷ []) (CS13 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb2-3-1-0 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;3;0;1): 3 steps
lem-nat-0-SBOXd⟨2·3·0·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻2-3-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-1-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·3·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-3-0-1 ∷ []) (Sb⁻2-3-1-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS03⁻ ∷ []) (CS13⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻2-3-1-0 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;3;41;0): 7 steps
lem-nat-0-SBOX⟨2·3·41·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb2-3-41-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-40-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·41·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-3-41-0 ∷ []) (Sb2-3-40-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx2-3410 ∷ Toff014 ∷ Sb2-3-0-1 ∷ Toff014 ∷ Sb⁻2-3-0-1 ∷ []) (refl) ▸
       at 0 2 (Bx2-3401 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3410⟩ c4) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 2 2 (Sb2-3-1-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·0·1⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 4 2 (Sb⁻2-3-1-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·3·0·1⟩ c4) ▸
       at 0 5 (Sb2-3-40-1 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;3;2;0): 3 steps
lem-nat-1-SBOX⟨1·3·2·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb1-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·3·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-3-2-0 ∷ []) (Sb2-3-1-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb2-3-1-0 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;3;2;0): 3 steps
lem-nat-1-SBOXd⟨1·3·2·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻1-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·3·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-3-2-0 ∷ []) (Sb⁻2-3-1-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS23⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻2-3-1-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;3;40;2): 7 steps
lem-nat-1-SBOX⟨1·3·40·2⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-40-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·3·40·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-3-40-2 ∷ []) (Sb2-3-40-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx1-3402 ∷ Toff204 ∷ Sb1-3-2-0 ∷ Toff204 ∷ Sb⁻1-3-2-0 ∷ []) (refl) ▸
       at 0 2 (Bx2-3401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3402⟩ c4) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 2 2 (Sb2-3-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·3·2·0⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 4 2 (Sb⁻2-3-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·3·2·0⟩ c4) ▸
       at 0 5 (Sb2-3-40-1 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;3;1;0): 3 steps
lem-nat-1-SBOX⟨2·3·1·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb2-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·3·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-3-1-0 ∷ []) (Sb1-3-2-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb1-3-2-0 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;3;1;0): 3 steps
lem-nat-1-SBOXd⟨2·3·1·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻2-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·3·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-3-1-0 ∷ []) (Sb⁻1-3-2-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻1-3-2-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;3;40;1): 7 steps
lem-nat-1-SBOX⟨2·3·40·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb2-3-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-40-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·3·40·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-3-40-1 ∷ []) (Sb1-3-40-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx2-3401 ∷ Toff104 ∷ Sb2-3-1-0 ∷ Toff104 ∷ Sb⁻2-3-1-0 ∷ []) (refl) ▸
       at 0 2 (Bx1-3402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3401⟩ c4) ▸
       at 1 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 2 2 (Sb1-3-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·3·1·0⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 4 2 (Sb⁻1-3-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·3·1·0⟩ c4) ▸
       at 0 5 (Sb1-3-40-2 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;23): 3 steps
lem-nat-2-BOX⟨1·23⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-32 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·23⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-23 ∷ []) (Bx1-32 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CZ23 ∷ []) (CZ23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx1-32 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;103): 8 steps
lem-nat-2-BOX⟨2·103⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-102 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·103⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-103 ∷ []) (Bx3-102 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-23 ∷ Toff201 ∷ CCZ012 ∷ Bx1-23 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 2 2 (Bx1-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·23⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx1-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·23⟩ c4) ▸
       at 0 6 (Bx3-102 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;2403): 8 steps
lem-nat-2-BOX⟨1·2403⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·2403⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-2403 ∷ []) (Bx1-3402 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-103 ∷ Toff124 ∷ CCZ124 ∷ Bx2-103 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 2 2 (Bx3-102 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·103⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx3-102 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·103⟩ c4) ▸
       at 0 6 (Bx1-3402 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;2;3;0): 3 steps
lem-nat-2-SBOX⟨1·2·3·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·2·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-2-3-0 ∷ []) (Sb1-3-2-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CS23 ∷ []) (CS23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb1-3-2-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;2;3;0): 3 steps
lem-nat-2-SBOXd⟨1·2·3·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·2·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-2-3-0 ∷ []) (Sb⁻1-3-2-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS23⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻1-3-2-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;2;40;3): 7 steps
lem-nat-2-SBOX⟨1·2·40·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-40-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·2·40·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-2-40-3 ∷ []) (Sb1-3-40-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx1-2403 ∷ Toff304 ∷ Sb1-2-3-0 ∷ Toff304 ∷ Sb⁻1-2-3-0 ∷ []) (refl) ▸
       at 0 2 (Bx1-3402 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·2403⟩ c4) ▸
       at 1 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 2 2 (Sb1-3-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·2·3·0⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 4 2 (Sb⁻1-3-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·2·3·0⟩ c4) ▸
       at 0 5 (Sb1-3-40-2 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;1;3;0): 3 steps
lem-nat-1-SBOX⟨2·1·3·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·1·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-1-3-0 ∷ []) (Sb1-2-3-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb1-2-3-0 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;1;3;0): 3 steps
lem-nat-1-SBOXd⟨2·1·3·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·1·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-1-3-0 ∷ []) (Sb⁻1-2-3-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻1-2-3-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;1;40;3): 7 steps
lem-nat-1-SBOX⟨2·1·40·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-40-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·1·40·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-1-40-3 ∷ []) (Sb1-2-40-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx2-1403 ∷ Toff304 ∷ Sb2-1-3-0 ∷ Toff304 ∷ Sb⁻2-1-3-0 ∷ []) (refl) ▸
       at 0 2 (Bx1-2403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1403⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 2 2 (Sb1-2-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·3·0⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 4 2 (Sb⁻1-2-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·1·3·0⟩ c4) ▸
       at 0 5 (Sb1-2-40-3 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;0;3;1): 3 steps
lem-nat-0-SBOX⟨2·0·3·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-3-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·0·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-0-3-1 ∷ []) (Sb2-1-3-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS03 ∷ []) (CS13 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb2-1-3-0 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;0;3;1): 3 steps
lem-nat-0-SBOXd⟨2·0·3·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-3-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·0·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻2-1-3-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS03⁻ ∷ []) (CS13⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻2-1-3-0 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;0;41;3): 7 steps
lem-nat-0-SBOX⟨2·0·41·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-40-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·0·41·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-0-41-3 ∷ []) (Sb2-1-40-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 2 (Bx2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 2 2 (Sb2-1-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·3·1⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 4 2 (Sb⁻2-1-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·0·3·1⟩ c4) ▸
       at 0 5 (Sb2-1-40-3 ∷ []) (refl) ▸ done


-- nat 0 BOXd(2;03): 3 steps
lem-nat-0-BOXd⟨2·03⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-13 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·03⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻2-03 ∷ []) (Bx⁻2-13 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ03 ∷ []) (CZ13 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻2-13 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;213): 8 steps
lem-nat-0-BOXd⟨0·213⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻0-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-203 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·213⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-213 ∷ []) (Bx⁻1-203 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-13 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·03⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻2-13 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·03⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻1-203 ∷ []) (refl) ▸ done


-- nat 0 BOXd(2;0413): 8 steps
lem-nat-0-BOXd⟨2·0413⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-1403 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·0413⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻2-0413 ∷ []) (Bx⁻2-1403 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-203 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·213⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 2 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 3 2 (Bx⁻1-203 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·213⟩ c4) ▸
       at 4 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 5 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 0 6 (Bx⁻2-1403 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;0;41;3): 7 steps
lem-nat-0-SBOXd⟨2·0·41·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-40-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·0·41·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-0-41-3 ∷ []) (Sb⁻2-1-40-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 0 2 (Sb2-1-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·3·1⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 2 2 (Sb⁻2-1-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·0·3·1⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 4 2 (Bx⁻2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·0413⟩ c4) ▸
       at 0 5 (Sb⁻2-1-40-3 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;13): 3 steps
lem-nat-1-BOXd⟨2·13⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻2-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-23 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·13⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-13 ∷ []) (Bx⁻1-23 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ13 ∷ []) (CZ23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻1-23 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;203): 8 steps
lem-nat-1-BOXd⟨1·203⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻1-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-103 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·203⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-203 ∷ []) (Bx⁻2-103 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻2-13 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻2-13 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-23 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·13⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻1-23 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·13⟩ c4) ▸
       at 4 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻2-103 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;1403): 8 steps
lem-nat-1-BOXd⟨2·1403⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-2403 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·1403⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-1403 ∷ []) (Bx⁻1-2403 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻1-203 ∷ CCZ124 ∷ Toff214 ∷ Bx⁻1-203 ∷ Toff214 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-103 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·203⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff214 ∷ []) (Toff124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻2-103 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·203⟩ c4) ▸
       at 4 2 (Toff124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff214 ∷ []) (Toff124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻1-2403 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;1;40;3): 7 steps
lem-nat-1-SBOXd⟨2·1·40·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-40-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·1·40·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-1-40-3 ∷ []) (Sb⁻1-2-40-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb2-1-3-0 ∷ Toff304 ∷ Sb⁻2-1-3-0 ∷ Toff304 ∷ Bx⁻2-1403 ∷ []) (refl) ▸
       at 0 2 (Sb1-2-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·3·0⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 2 2 (Sb⁻1-2-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·1·3·0⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 4 2 (Bx⁻1-2403 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·1403⟩ c4) ▸
       at 0 5 (Sb⁻1-2-40-3 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;23): 3 steps
lem-nat-2-BOXd⟨1·23⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-32 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·23⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-23 ∷ []) (Bx⁻1-32 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CZ23 ∷ []) (CZ23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻1-32 ∷ []) (refl) ▸ done


-- nat 2 BOXd(2;103): 8 steps
lem-nat-2-BOXd⟨2·103⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻2-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-102 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨2·103⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻2-103 ∷ []) (Bx⁻3-102 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-23 ∷ CCZ012 ∷ Toff201 ∷ Bx⁻1-23 ∷ Toff201 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-32 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·23⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 3 2 (Bx⁻1-32 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·23⟩ c4) ▸
       at 4 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 5 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 0 6 (Bx⁻3-102 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;2403): 8 steps
lem-nat-2-BOXd⟨1·2403⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-3402 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·2403⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-2403 ∷ []) (Bx⁻1-3402 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻2-103 ∷ CCZ124 ∷ Toff124 ∷ Bx⁻2-103 ∷ Toff124 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻3-102 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨2·103⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 2 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 3 2 (Bx⁻3-102 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨2·103⟩ c4) ▸
       at 4 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 5 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 0 6 (Bx⁻1-3402 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;2;40;3): 7 steps
lem-nat-2-SBOXd⟨1·2·40·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-40-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·2·40·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-2-40-3 ∷ []) (Sb⁻1-3-40-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb1-2-3-0 ∷ Toff304 ∷ Sb⁻1-2-3-0 ∷ Toff304 ∷ Bx⁻1-2403 ∷ []) (refl) ▸
       at 0 2 (Sb1-3-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·2·3·0⟩ c4) ▸
       at 1 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 2 2 (Sb⁻1-3-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·2·3·0⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 4 2 (Bx⁻1-3402 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·2403⟩ c4) ▸
       at 0 5 (Sb⁻1-3-40-2 ∷ []) (refl) ▸ done


-- nat 3 SBOX(1;3;2;0): 3 steps
lem-nat-3-SBOX⟨1·3·2·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb1-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-2-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·3·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb1-3-2-0 ∷ []) (Sb1-4-2-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw34 ∷ []) (lem-nat-3-CS23 c4) ▸
       at 0 1 (Sb1-4-2-0 ∷ []) (refl) ▸ done


-- nat 3 CSd23: 2 steps
lem-nat-3-CSd23 : Complete 4 → ⟪ (Sw34 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CSd23 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CS23⁻ ∷ []) (CS24⁻ ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(1;3;2;0): 3 steps
lem-nat-3-SBOXd⟨1·3·2·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻1-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-2-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·3·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-3-2-0 ∷ []) (Sb⁻1-4-2-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS23⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd23 c4) ▸
       at 0 1 (Sb⁻1-4-2-0 ∷ []) (refl) ▸ done


-- nat 3 BOXd(1;32): 3 steps
lem-nat-3-BOXd⟨1·32⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻1-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-42 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·32⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻1-32 ∷ []) (Bx⁻1-42 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw34 ∷ []) (lem-nat-3-CZ23 c4) ▸
       at 0 1 (Bx⁻1-42 ∷ []) (refl) ▸ done


-- nat 3 BOXd(3;102): 8 steps
lem-nat-3-BOXd⟨3·102⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻3-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-102 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨3·102⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻3-102 ∷ []) (Bx⁻4-102 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻1-32 ∷ CCZ013 ∷ Toff301 ∷ Bx⁻1-32 ∷ Toff301 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-42 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·32⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 3 2 (Bx⁻1-42 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·32⟩ c4) ▸
       at 4 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 5 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 0 6 (Bx⁻4-102 ∷ []) (refl) ▸ done


-- nat 3 BOXd(1;3402): 8 steps
lem-nat-3-BOXd⟨1·3402⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-4302 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·3402⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻1-3402 ∷ []) (Bx⁻1-4302 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻3-102 ∷ CCZ134 ∷ Toff134 ∷ Bx⁻3-102 ∷ Toff134 ∷ CCZ134 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-102 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·102⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻4-102 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·102⟩ c4) ▸
       at 4 2 (Toff134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻1-4302 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(1;3;40;2): 7 steps
lem-nat-3-SBOXd⟨1·3·40·2⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-30-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·3·40·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-3-40-2 ∷ []) (Sb⁻1-4-30-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sb1-3-2-0 ∷ Toff204 ∷ Sb⁻1-3-2-0 ∷ Toff204 ∷ Bx⁻1-3402 ∷ []) (refl) ▸
       at 0 2 (Sb1-4-2-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·3·2·0⟩ c4) ▸
       at 1 2 (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4) ▸
       at 2 2 (Sb⁻1-4-2-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·3·2·0⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4) ▸
       at 4 2 (Bx⁻1-4302 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·3402⟩ c4) ▸
       at 0 5 (Sb⁻1-4-30-2 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;42): 3 steps
lem-nat-2-BOXd⟨1·42⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-43 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·42⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-42 ∷ []) (Bx⁻1-43 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ24 ∷ []) (CZ34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻1-43 ∷ []) (refl) ▸ done


-- nat 2 BOXd(4;102): 8 steps
lem-nat-2-BOXd⟨4·102⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻4-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-103 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨4·102⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻4-102 ∷ []) (Bx⁻4-103 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-42 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻1-42 ∷ Toff401 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-43 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·42⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 3 2 (Bx⁻1-43 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·42⟩ c4) ▸
       at 4 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 5 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 0 6 (Bx⁻4-103 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;4302): 8 steps
lem-nat-2-BOXd⟨1·4302⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-4302 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-4203 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·4302⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-4302 ∷ []) (Bx⁻1-4203 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻4-102 ∷ CCZ134 ∷ Toff134 ∷ Bx⁻4-102 ∷ Toff134 ∷ CCZ134 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-103 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·102⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 2 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 3 2 (Bx⁻4-103 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·102⟩ c4) ▸
       at 4 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 5 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 0 6 (Bx⁻1-4203 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;4;30;2): 7 steps
lem-nat-2-SBOXd⟨1·4·30·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻1-4-30-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-20-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·4·30·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-4-30-2 ∷ []) (Sb⁻1-4-20-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb1-4-2-0 ∷ Toff203 ∷ Sb⁻1-4-2-0 ∷ Toff203 ∷ Bx⁻1-4302 ∷ []) (refl) ▸
       at 0 2 (Sb1-4-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·4·2·0⟩ c4) ▸
       at 1 2 (Toff302 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻1-4-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·4·2·0⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻1-4203 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·4302⟩ c4) ▸
       at 0 5 (Sb⁻1-4-20-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;4;3;0): 2 steps
lem-nat-1-SBOX⟨1·4·3·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb1-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·4·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-4-3-0 ∷ []) (Sb2-4-3-0 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Sb1-4-3-0 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 0 1 (Sb2-4-3-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOXd(1;4;3;0): 2 steps
lem-nat-1-SBOXd⟨1·4·3·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻1-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·4·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-4-3-0 ∷ []) (Sb⁻2-4-3-0 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Sb⁻1-4-3-0 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS)) ▸
       at 0 1 (Sb⁻2-4-3-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOXd(1;43): 2 steps
lem-nat-1-BOXd⟨1·43⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻1-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-43 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·43⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-43 ∷ []) (Bx⁻2-43 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Bx⁻1-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 0 1 (Bx⁻2-43 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOXd(4;103): 8 steps
lem-nat-1-BOXd⟨4·103⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻4-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-203 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·103⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻4-103 ∷ []) (Bx⁻4-203 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻1-43 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻1-43 ∷ Toff401 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-43 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·43⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 3 2 (Bx⁻2-43 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·43⟩ c4) ▸
       at 4 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 5 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 0 6 (Bx⁻4-203 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;4203): 8 steps
lem-nat-1-BOXd⟨1·4203⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻1-4203 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-4103 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·4203⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-4203 ∷ []) (Bx⁻2-4103 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻4-103 ∷ CCZ124 ∷ Toff124 ∷ Bx⁻4-103 ∷ Toff124 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-203 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·103⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff214 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻4-203 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·103⟩ c4) ▸
       at 4 2 (Toff214 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻2-4103 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;4;20;3): 7 steps
lem-nat-1-SBOXd⟨1·4·20·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-10-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·4·20·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-4-20-3 ∷ []) (Sb⁻2-4-10-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb1-4-3-0 ∷ Toff302 ∷ Sb⁻1-4-3-0 ∷ Toff302 ∷ Bx⁻1-4203 ∷ []) (refl) ▸
       at 0 2 (Sb2-4-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·4·3·0⟩ c4) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 2 2 (Sb⁻2-4-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·4·3·0⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 4 2 (Bx⁻2-4103 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·4203⟩ c4) ▸
       at 0 5 (Sb⁻2-4-10-3 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;4;3;0): 2 steps
lem-nat-0-SBOX⟨2·4·3·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb2-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·4·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-4-3-0 ∷ []) (Sb2-4-3-1 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb2-4-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 0 1 (Sb2-4-3-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(2;4;3;0): 2 steps
lem-nat-0-SBOXd⟨2·4·3·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻2-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·4·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-4-3-0 ∷ []) (Sb⁻2-4-3-1 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb⁻2-4-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 0 1 (Sb⁻2-4-3-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOXd(4;203): 8 steps
lem-nat-0-BOXd⟨4·203⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻4-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-213 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·203⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻4-203 ∷ []) (Bx⁻4-213 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻2-43 ∷ CCZ024 ∷ Toff402 ∷ Bx⁻2-43 ∷ Toff402 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 2 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 3 2 (Bx⁻2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 4 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 5 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 0 6 (Bx⁻4-213 ∷ []) (refl) ▸ done


-- nat 0 BOXd(2;4103): 8 steps
lem-nat-0-BOXd⟨2·4103⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-4013 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·4103⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻2-4103 ∷ []) (Bx⁻2-4013 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻4-203 ∷ CCZ124 ∷ Toff214 ∷ Bx⁻4-203 ∷ Toff214 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-213 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·203⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 3 2 (Bx⁻4-213 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·203⟩ c4) ▸
       at 4 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 5 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 0 6 (Bx⁻2-4013 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;4;10;3): 7 steps
lem-nat-0-SBOXd⟨2·4·10·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻2-4-10-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-01-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·4·10·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-4-10-3 ∷ []) (Sb⁻2-4-01-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb2-4-3-0 ∷ Toff301 ∷ Sb⁻2-4-3-0 ∷ Toff301 ∷ Bx⁻2-4103 ∷ []) (refl) ▸
       at 0 2 (Sb2-4-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·4·3·0⟩ c4) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻2-4-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·4·3·0⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻2-4013 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·4103⟩ c4) ▸
       at 0 5 (Sb⁻2-4-01-3 ∷ []) (refl) ▸ done


-- nat 0 BOXd(2;13): 3 steps
lem-nat-0-BOXd⟨2·13⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻2-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-03 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·13⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻2-13 ∷ []) (Bx⁻2-03 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ13 ∷ []) (CZ03 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻2-03 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;203): 8 steps
lem-nat-0-BOXd⟨1·203⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-213 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·203⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-203 ∷ []) (Bx⁻0-213 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻2-13 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻2-13 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-03 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·13⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻2-03 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·13⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻0-213 ∷ []) (refl) ▸ done


-- nat 0 BOXd(2;1403): 8 steps
lem-nat-0-BOXd⟨2·1403⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0413 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·1403⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻2-1403 ∷ []) (Bx⁻2-0413 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-203 ∷ CCZ124 ∷ Toff214 ∷ Bx⁻1-203 ∷ Toff214 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-213 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·203⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 3 2 (Bx⁻0-213 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·203⟩ c4) ▸
       at 4 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 5 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 0 6 (Bx⁻2-0413 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;1;40;3): 7 steps
lem-nat-0-SBOXd⟨2·1·40·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-41-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·1·40·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-1-40-3 ∷ []) (Sb⁻2-0-41-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb2-1-3-0 ∷ Toff304 ∷ Sb⁻2-1-3-0 ∷ Toff304 ∷ Bx⁻2-1403 ∷ []) (refl) ▸
       at 0 2 (Sb2-0-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·3·0⟩ c4) ▸
       at 1 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 2 2 (Sb⁻2-0-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·1·3·0⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 4 2 (Bx⁻2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·1403⟩ c4) ▸
       at 0 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸ done


-- nat 0 BOXd(4;213): 8 steps
lem-nat-0-BOXd⟨4·213⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻4-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-203 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·213⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻4-213 ∷ []) (Bx⁻4-203 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻2-43 ∷ CCZ124 ∷ Toff412 ∷ Bx⁻2-43 ∷ Toff412 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 3 2 (Bx⁻2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 4 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 5 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 0 6 (Bx⁻4-203 ∷ []) (refl) ▸ done


{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R041 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-2-CCZ024 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ034 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-3-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-2-TOFF204 ; lem-nat-2-TOFF304)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF412 ; lem-nat-1-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-TOFF204 ; lem-nat-3-BOX⟨0·32⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-TOFF024 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-3-CZ24)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-CS12 ; lem-nat-2-CS13 ; lem-nat-2-CSd12 ; lem-nat-2-CSd13 ; lem-nat-3-CS14 ; lem-nat-3-CSd13 ; lem-nat-3-CSd14)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-CSd02 ; lem-nat-3-CS23 ; lem-nat-3-CS24)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-TOFF134 ; lem-nat-1-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-nat-0-BOXd⟨0·14⟩ ; lem-nat-0-BOXd⟨4·01⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-CS03)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-3-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R024 using (lem-nat-3-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R027 using (lem-nat-3-CSd23)
open import Examples.Groups.Clifford+CS.Five.D.R029 using (lem-nat-0-SBOX⟨0·1·4·2⟩ ; lem-nat-0-SBOX⟨4·0·1·2⟩ ; lem-nat-0-SBOXd⟨0·1·4·2⟩ ; lem-nat-0-SBOXd⟨4·0·1·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R032 using (lem-nat-0-BOX⟨3·01⟩ ; lem-nat-0-BOX⟨3·10⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-1-BOX⟨3·2401⟩)
open import Examples.Groups.Clifford+CS.Five.D.R034 using (lem-nat-2-BOX⟨0·21⟩)
open import Examples.Groups.Clifford+CS.Five.D.R035 using (lem-nat-1-BOX⟨1·2430⟩)
open import Examples.Groups.Clifford+CS.Five.D.R038 using (lem-nat-3-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R039 using (lem-nat-2-BOX⟨2·1403⟩ ; lem-nat-2-BOX⟨3·1402⟩ ; lem-nat-2-SBOX⟨2·1·3·0⟩ ; lem-nat-2-SBOX⟨3·1·2·0⟩ ; lem-nat-2-SBOXd⟨2·1·3·0⟩ ; lem-nat-2-SBOXd⟨3·1·2·0⟩)
-- nat 3 SBOX(0;4;1;2): 3 steps
lem-nat-3-SBOX⟨0·4·1·2⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb0-4-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-1-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·4·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-4-1-2 ∷ []) (Sb0-3-1-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw34 ∷ []) (lem-nat-3-CS14 c4) ▸
       at 0 1 (Sb0-3-1-2 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;2;1;3): 3 steps
lem-nat-2-SBOX⟨0·2·1·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-1-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·2·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-2-1-3 ∷ []) (Sb0-3-1-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4) ▸
       at 0 1 (Sb0-3-1-2 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;3;1;2): 3 steps
lem-nat-2-SBOX⟨0·3·1·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb0-3-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·3·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-3-1-2 ∷ []) (Sb0-2-1-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 c4) ▸
       at 0 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;4;1;2): 3 steps
lem-nat-2-SBOXd⟨0·4·1·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻0-4-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-1-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·4·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-4-1-2 ∷ []) (Sb⁻0-4-1-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-4-1-3 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;4;1;3): 3 steps
lem-nat-2-SBOXd⟨0·4·1·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻0-4-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-1-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·4·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-4-1-3 ∷ []) (Sb⁻0-4-1-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-4-1-2 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;3;1;2): 3 steps
lem-nat-3-SBOXd⟨0·3·1·2⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻0-3-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-1-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·3·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-3-1-2 ∷ []) (Sb⁻0-4-1-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd13 c4) ▸
       at 0 1 (Sb⁻0-4-1-2 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;4;1;2): 3 steps
lem-nat-3-SBOXd⟨0·4·1·2⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻0-4-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-1-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·4·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-4-1-2 ∷ []) (Sb⁻0-3-1-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd14 c4) ▸
       at 0 1 (Sb⁻0-3-1-2 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;2;1;3): 3 steps
lem-nat-2-SBOXd⟨0·2·1·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-1-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·2·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-3-1-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4) ▸
       at 0 1 (Sb⁻0-3-1-2 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;3;1;2): 3 steps
lem-nat-2-SBOXd⟨0·3·1·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻0-3-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·3·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-3-1-2 ∷ []) (Sb⁻0-2-1-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 c4) ▸
       at 0 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;403): 8 steps
lem-nat-0-BOX⟨2·403⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-413 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·403⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-403 ∷ []) (Bx2-413 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-23 ∷ Toff204 ∷ CCZ024 ∷ Bx4-23 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 2 2 (Bx4-23 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 3 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx4-23 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 0 6 (Bx2-413 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;2103): 8 steps
lem-nat-0-BOX⟨4·2103⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-2103 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2013 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·2103⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-2103 ∷ []) (Bx4-2013 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-403 ∷ Toff412 ∷ CCZ124 ∷ Bx2-403 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 2 2 (Bx2-413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·403⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx2-413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·403⟩ c4) ▸
       at 0 6 (Bx4-2013 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;02): 2 steps
lem-nat-3-BOX⟨4·02⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx4-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-02 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·02⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-02 ∷ []) (Bx3-02 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Bx4-02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 0 1 (Bx3-02 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(0;412): 8 steps
lem-nat-3-BOX⟨0·412⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-312 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·412⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-412 ∷ []) (Bx0-312 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 1 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 2 2 (Bx3-02 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·02⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 4 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 5 2 (Bx3-02 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·02⟩ c4) ▸
       at 0 6 (Bx0-312 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;0312): 8 steps
lem-nat-3-BOX⟨4·0312⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·0312⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-0312 ∷ []) (Bx3-0412 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-412 ∷ Toff403 ∷ CCZ034 ∷ Bx0-412 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 1 2 (Toff304 ∷ Sw34 ∷ []) (lem-nat-3-TOFF403 c4) ▸
       at 2 2 (Bx0-312 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·412⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw34 ∷ []) (lem-nat-3-TOFF403 c4) ▸
       at 4 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 5 2 (Bx0-312 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·412⟩ c4) ▸
       at 0 6 (Bx3-0412 ∷ []) (refl) ▸ done


-- nat 2 SBOX(4;0;3;1): 3 steps
lem-nat-2-SBOX⟨4·0·3·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·0·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb4-0-3-1 ∷ []) (Sb4-0-2-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 0 1 (Sb4-0-2-1 ∷ []) (refl) ▸ done


-- nat 3 SBOX(4;0;2;1): 2 steps
lem-nat-3-SBOX⟨4·0·2·1⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-2-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨4·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb4-0-2-1 ∷ []) (Sb3-0-2-1 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb4-0-2-1 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (Swap))) ▸
       at 0 1 (Sb3-0-2-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(4;0;2;1): 2 steps
lem-nat-3-SBOXd⟨4·0·2·1⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-2-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨4·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻3-0-2-1 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻4-0-2-1 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (Swap))) ▸
       at 0 1 (Sb⁻3-0-2-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm SBOXd(0;1;2;3) TOFF034: 17 steps
lem-comm-SBOXd⟨0·1·2·3⟩-TOFF034 : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-comm-SBOXd⟨0·1·2·3⟩-TOFF034 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Toff034 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CS34⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff034 ∷ CS12⁻ ∷ [])
  b1 = at 4 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸
       at 5 2 (Sw23 ∷ CS24⁻ ∷ []) (lw0 c4 (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ CS13⁻ ∷ []) (lw4 c4 (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 9 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Toff034 ∷ CS12⁻ ∷ []) (Toff034 ∷ Sb⁻0-1-2-3 ∷ [])
  b2 = at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


-- comm SBOX(0;1;2;3) TOFF034: 17 steps
lem-comm-SBOX⟨0·1·2·3⟩-TOFF034 : Complete 4 → ⟪ (Sb0-1-2-3 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-comm-SBOX⟨0·1·2·3⟩-TOFF034 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sb0-1-2-3 ∷ Toff034 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (CS12 ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23 ∷ []) (lw4 c4 (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CS34 ∷ []) (lw0 c4 (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff034 ∷ CS12 ∷ [])
  b1 = at 4 2 (Toff012 ∷ CS34 ∷ []) (sym (c₃ (Toff) (CS))) ▸
       at 5 2 (Sw23 ∷ CS24 ∷ []) (lw0 c4 (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ CS13 ∷ []) (lw4 c4 (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 9 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Toff034 ∷ CS12 ∷ []) (Toff034 ∷ Sb0-1-2-3 ∷ [])
  b2 = at 1 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;041): 8 steps
lem-nat-2-BOX⟨2·041⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-041 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·041⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-041 ∷ []) (Bx3-041 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 2 2 (Bx0-31 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·21⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx0-31 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·21⟩ c4) ▸
       at 0 6 (Bx3-041 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;2341): 8 steps
lem-nat-2-BOX⟨0·2341⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·2341⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-2341 ∷ []) (Bx0-3241 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-041 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·041⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-041 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·041⟩ c4) ▸
       at 0 6 (Bx0-3241 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;2;1;0): 3 steps
lem-nat-1-SBOX⟨3·2·1·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb3-2-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·2·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-2-1-0 ∷ []) (Sb3-1-2-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS12 ∷ []) (CS12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb3-1-2-0 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(3;2;1;0): 3 steps
lem-nat-1-SBOXd⟨3·2·1·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻3-2-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-1-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·2·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻3-2-1-0 ∷ []) (Sb⁻3-1-2-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻3-1-2-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;2;40;1): 7 steps
lem-nat-1-SBOX⟨3·2·40·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb3-2-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-40-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·2·40·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-2-40-1 ∷ []) (Sb3-1-40-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx3-2401 ∷ Toff104 ∷ Sb3-2-1-0 ∷ Toff104 ∷ Sb⁻3-2-1-0 ∷ []) (refl) ▸
       at 0 2 (Bx3-1402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2401⟩ c4) ▸
       at 1 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 2 2 (Sb3-1-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·2·1·0⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 4 2 (Sb⁻3-1-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·2·1·0⟩ c4) ▸
       at 0 5 (Sb3-1-40-2 ∷ []) (refl) ▸ done


-- nat 2 SBOX(2;1;40;3): 7 steps
lem-nat-2-SBOX⟨2·1·40·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-40-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·1·40·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-1-40-3 ∷ []) (Sb3-1-40-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx2-1403 ∷ Toff304 ∷ Sb2-1-3-0 ∷ Toff304 ∷ Sb⁻2-1-3-0 ∷ []) (refl) ▸
       at 0 2 (Bx3-1402 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·1403⟩ c4) ▸
       at 1 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 2 2 (Sb3-1-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·1·3·0⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 4 2 (Sb⁻3-1-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·1·3·0⟩ c4) ▸
       at 0 5 (Sb3-1-40-2 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;1;40;2): 7 steps
lem-nat-2-SBOX⟨3·1·40·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb3-1-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-40-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·1·40·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-1-40-2 ∷ []) (Sb2-1-40-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx3-1402 ∷ Toff204 ∷ Sb3-1-2-0 ∷ Toff204 ∷ Sb⁻3-1-2-0 ∷ []) (refl) ▸
       at 0 2 (Bx2-1403 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·1402⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 2 2 (Sb2-1-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·1·2·0⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 4 2 (Sb⁻2-1-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·1·2·0⟩ c4) ▸
       at 0 5 (Sb2-1-40-3 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;2;1;4): 3 steps
lem-nat-2-SBOX⟨0·2·1·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb0-2-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·2·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-2-1-4 ∷ []) (Sb0-3-1-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4) ▸
       at 0 1 (Sb0-3-1-4 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;2;1;3): 2 steps
lem-nat-3-SBOX⟨0·2·1·3⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·2·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-2-1-3 ∷ []) (Sb0-2-1-4 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb0-2-1-3 ∷ Sw34 ∷ []) (sym (c₃ (CS ↑) (Swap))) ▸
       at 0 1 (Sb0-2-1-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOX(0;2;1;4): 2 steps
lem-nat-3-SBOX⟨0·2·1·4⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb0-2-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·2·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-2-1-4 ∷ []) (Sb0-2-1-3 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb0-2-1-4 ∷ Sw34 ∷ []) (sym (c₃ (CS ↑) (Swap))) ▸
       at 0 1 (Sb0-2-1-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOXd(0;2;1;4): 3 steps
lem-nat-2-SBOXd⟨0·2·1·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻0-2-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·2·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-2-1-4 ∷ []) (Sb⁻0-3-1-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4) ▸
       at 0 1 (Sb⁻0-3-1-4 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;2;1;3): 2 steps
lem-nat-3-SBOXd⟨0·2·1·3⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·2·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-2-1-4 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻0-2-1-3 ∷ Sw34 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (Swap))) ▸
       at 0 1 (Sb⁻0-2-1-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(0;2;1;4): 2 steps
lem-nat-3-SBOXd⟨0·2·1·4⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻0-2-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·2·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-2-1-4 ∷ []) (Sb⁻0-2-1-3 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻0-2-1-4 ∷ Sw34 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (Swap))) ▸
       at 0 1 (Sb⁻0-2-1-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CX30 at 1: 2 steps
lem-resp-CX30-at-1 : Complete 4 → ⟪ (CX30 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX31 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX30-at-1 c4 = run b0
  where
  b0 : Chain (CX30 ∷ []) (Sw01 ∷ CX31 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ CX31 ∷ []) (lw4 c4 (CX30 ∷ Sw01 ∷ []) (Sw01 ∷ CX31 ∷ []) tt tt Eq.refl) ▸ done


-- nat 3 BOX(0;42): 3 steps
lem-nat-3-BOX⟨0·42⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-32 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·42⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-42 ∷ []) (Bx0-32 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw34 ∷ []) (lem-nat-3-CZ24 c4) ▸
       at 0 1 (Bx0-32 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;012): 8 steps
lem-nat-3-BOX⟨4·012⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx4-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-012 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·012⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-012 ∷ []) (Bx3-012 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 1 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 2 2 (Bx0-32 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·42⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 4 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 5 2 (Bx0-32 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·42⟩ c4) ▸
       at 0 6 (Bx3-012 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;4312): 8 steps
lem-nat-3-BOX⟨0·4312⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·4312⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-4312 ∷ []) (Bx0-3412 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw34 ∷ []) (lem-nat-3-TOFF034 c4) ▸
       at 2 2 (Bx3-012 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·012⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw34 ∷ []) (lem-nat-3-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 5 2 (Bx3-012 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·012⟩ c4) ▸
       at 0 6 (Bx0-3412 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;012): 8 steps
lem-nat-3-BOX⟨3·012⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx3-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-012 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·012⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-012 ∷ []) (Bx4-012 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 2 2 (Bx0-42 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·32⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx0-42 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·32⟩ c4) ▸
       at 0 6 (Bx4-012 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;3412): 8 steps
lem-nat-3-BOX⟨0·3412⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·3412⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-3412 ∷ []) (Bx0-4312 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw34 ∷ []) (lem-nat-3-TOFF034 c4) ▸
       at 2 2 (Bx4-012 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·012⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw34 ∷ []) (lem-nat-3-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 5 2 (Bx4-012 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·012⟩ c4) ▸
       at 0 6 (Bx0-4312 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;341): 8 steps
lem-nat-0-BOX⟨0·341⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-341 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-340 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·341⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-341 ∷ []) (Bx1-340 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 2 2 (Bx3-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·01⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx3-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·01⟩ c4) ▸
       at 0 6 (Bx1-340 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;0241): 8 steps
lem-nat-0-BOX⟨3·0241⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·0241⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-0241 ∷ []) (Bx3-1240 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-341 ∷ Toff302 ∷ CCZ023 ∷ Bx0-341 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-340 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·341⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-340 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·341⟩ c4) ▸
       at 0 6 (Bx3-1240 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;340): 8 steps
lem-nat-0-BOX⟨1·340⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-340 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-341 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·340⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-340 ∷ []) (Bx0-341 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 2 2 (Bx3-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·10⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx3-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·10⟩ c4) ▸
       at 0 6 (Bx0-341 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;1240): 8 steps
lem-nat-0-BOX⟨3·1240⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·1240⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-1240 ∷ []) (Bx3-0241 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-340 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-341 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·340⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-341 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·340⟩ c4) ▸
       at 0 6 (Bx3-0241 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;2;0;3): 3 steps
lem-nat-1-SBOX⟨1·2·0·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb1-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-0-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·2·0·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-2-0-3 ∷ []) (Sb2-1-0-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 0 1 (Sb2-1-0-3 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;2;0;3): 3 steps
lem-nat-1-SBOXd⟨1·2·0·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻1-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-0-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·2·0·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-2-0-3 ∷ []) (Sb⁻2-1-0-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 0 1 (Sb⁻2-1-0-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;2;43;0): 7 steps
lem-nat-1-SBOX⟨1·2·43·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-43-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·2·43·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-2-43-0 ∷ []) (Sb2-1-43-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx1-2430 ∷ Toff034 ∷ Sb1-2-0-3 ∷ Toff034 ∷ Sb⁻1-2-0-3 ∷ []) (refl) ▸
       at 0 2 (Bx2-1430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2430⟩ c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Sb2-1-0-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·0·3⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 4 2 (Sb⁻2-1-0-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·2·0·3⟩ c4) ▸
       at 0 5 (Sb2-1-43-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;4;2;1): 3 steps
lem-nat-2-SBOX⟨0·4·2·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·4·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-4-2-1 ∷ []) (Sb0-4-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-4-3-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;4;3;1): 3 steps
lem-nat-2-SBOX⟨0·4·3·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb0-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·4·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-4-3-1 ∷ []) (Sb0-4-2-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS34 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-4-2-1 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;3;2;1): 3 steps
lem-nat-3-SBOX⟨0·3·2·1⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb0-3-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-2-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·3·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-3-2-1 ∷ []) (Sb0-4-2-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw34 ∷ []) (lem-nat-3-CS23 c4) ▸
       at 0 1 (Sb0-4-2-1 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;4;2;1): 3 steps
lem-nat-3-SBOX⟨0·4·2·1⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-2-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·4·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-4-2-1 ∷ []) (Sb0-3-2-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw34 ∷ []) (lem-nat-3-CS24 c4) ▸
       at 0 1 (Sb0-3-2-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;2;3;1): 3 steps
lem-nat-2-SBOX⟨0·2·3·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·2·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-2-3-1 ∷ []) (Sb0-3-2-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CS23 ∷ []) (CS23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-3-2-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;3;2;1): 3 steps
lem-nat-2-SBOX⟨0·3·2·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb0-3-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·3·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-3-2-1 ∷ []) (Sb0-2-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CS23 ∷ []) (CS23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-2-3-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;4;2;1): 3 steps
lem-nat-2-SBOXd⟨0·4·2·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·4·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-4-2-1 ∷ []) (Sb⁻0-4-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-4-3-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;4;3;1): 3 steps
lem-nat-2-SBOXd⟨0·4·3·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻0-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·4·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-4-3-1 ∷ []) (Sb⁻0-4-2-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-4-2-1 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;3;2;1): 3 steps
lem-nat-3-SBOXd⟨0·3·2·1⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻0-3-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-2-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·3·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-3-2-1 ∷ []) (Sb⁻0-4-2-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS23⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd23 c4) ▸
       at 0 1 (Sb⁻0-4-2-1 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;4;2;1): 3 steps
lem-nat-3-SBOXd⟨0·4·2·1⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-2-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·4·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-4-2-1 ∷ []) (Sb⁻0-3-2-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd24 c4) ▸
       at 0 1 (Sb⁻0-3-2-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;2;3;1): 3 steps
lem-nat-2-SBOXd⟨0·2·3·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·2·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻0-3-2-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS23⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-3-2-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;3;2;1): 3 steps
lem-nat-2-SBOXd⟨0·3·2·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻0-3-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·3·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-3-2-1 ∷ []) (Sb⁻0-2-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS23⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-2-3-1 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;024): 8 steps
lem-nat-0-BOXd⟨1·024⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-124 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·024⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-024 ∷ []) (Bx⁻0-124 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻0-14 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-14 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-04 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·14⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻1-04 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·14⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻0-124 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;1324): 8 steps
lem-nat-0-BOXd⟨0·1324⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0324 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·1324⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-1324 ∷ []) (Bx⁻1-0324 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-024 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-024 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-124 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·024⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻0-124 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·024⟩ c4) ▸
       at 4 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻1-0324 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(0;1;32;4): 7 steps
lem-nat-0-SBOXd⟨0·1·32·4⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-32-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·1·32·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-1-32-4 ∷ []) (Sb⁻1-0-32-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-4-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·4·2⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (Sb⁻1-0-4-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 4 2 (Bx⁻1-0324 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·1324⟩ c4) ▸
       at 0 5 (Sb⁻1-0-32-4 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;421): 8 steps
lem-nat-0-BOXd⟨0·421⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻0-421 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-420 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·421⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-421 ∷ []) (Bx⁻1-420 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻4-01 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻4-01 ∷ Toff024 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-10 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·01⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 2 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 3 2 (Bx⁻4-10 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·01⟩ c4) ▸
       at 4 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 5 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 0 6 (Bx⁻1-420 ∷ []) (refl) ▸ done


-- nat 0 BOXd(4;0321): 8 steps
lem-nat-0-BOXd⟨4·0321⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-1320 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·0321⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻4-0321 ∷ []) (Bx⁻4-1320 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻0-421 ∷ CCZ034 ∷ Toff403 ∷ Bx⁻0-421 ∷ Toff403 ∷ CCZ034 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-420 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·421⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 2 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 3 2 (Bx⁻1-420 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·421⟩ c4) ▸
       at 4 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 5 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 0 6 (Bx⁻4-1320 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(4;0;32;1): 7 steps
lem-nat-0-SBOXd⟨4·0·32·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻4-0-32-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-1-32-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨4·0·32·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻4-0-32-1 ∷ []) (Sb⁻4-1-32-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb4-0-1-2 ∷ Toff123 ∷ Sb⁻4-0-1-2 ∷ Toff123 ∷ Bx⁻4-0321 ∷ []) (refl) ▸
       at 0 2 (Sb4-1-0-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨4·0·1·2⟩ c4) ▸
       at 1 2 (Toff023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻4-1-0-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨4·0·1·2⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻4-1320 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·0321⟩ c4) ▸
       at 0 5 (Sb⁻4-1-32-0 ∷ []) (refl) ▸ done


-- nat 1 BOXd(4;03): 3 steps
lem-nat-1-BOXd⟨4·03⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·03⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻4-03 ∷ []) (Bx⁻4-03 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ03 ∷ []) (CZ03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻4-03 ∷ []) (refl) ▸ done


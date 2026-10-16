{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R043 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF102 ; lem-nat-2-TOFF103)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-3-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-CCZ014 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF104 ; lem-nat-1-TOFF104 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-TOFF214 ; lem-nat-1-TOFF304 ; lem-nat-2-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-TOFF024 ; lem-nat-1-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-TOFF023 ; lem-nat-3-TOFF103)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-CZ01 ; lem-nat-2-CCZ014 ; lem-nat-2-CZ12 ; lem-nat-2-CZ13)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-SBOX⟨0·1·2·4⟩ ; lem-nat-0-SBOX⟨2·0·1·4⟩ ; lem-nat-0-SBOXd⟨0·1·2·4⟩ ; lem-nat-0-SBOXd⟨2·0·1·4⟩ ; lem-nat-0-TOFF134 ; lem-nat-1-SBOX⟨0·2·1·4⟩ ; lem-nat-1-SBOX⟨2·1·0·4⟩ ; lem-nat-1-SBOXd⟨0·2·1·4⟩ ; lem-nat-1-SBOXd⟨2·1·0·4⟩ ; lem-nat-1-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-SBOX⟨1·2·0·4⟩ ; lem-nat-0-SBOXd⟨1·2·0·4⟩ ; lem-nat-0-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-TOFF124)
open import Examples.Groups.Clifford+CS.Five.D.R022 using (lem-nat-3-BOXd⟨0·14⟩)
open import Examples.Groups.Clifford+CS.Five.D.R032 using (lem-nat-0-BOX⟨3·1420⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-0-SBOX⟨0·1·2·3⟩ ; lem-nat-0-SBOX⟨1·0·2·3⟩ ; lem-nat-0-SBOXd⟨0·1·2·3⟩ ; lem-nat-0-SBOXd⟨1·0·2·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R037 using (lem-nat-3-BOX⟨0·2341⟩ ; lem-nat-3-BOX⟨0·2431⟩)
open import Examples.Groups.Clifford+CS.Five.D.R038 using (lem-nat-0-SBOX⟨3·1·0·2⟩ ; lem-nat-0-SBOXd⟨3·1·0·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R041 using (lem-nat-3-SBOX⟨0·2·1·3⟩ ; lem-nat-3-SBOX⟨0·2·1·4⟩ ; lem-nat-3-SBOXd⟨0·2·1·3⟩ ; lem-nat-3-SBOXd⟨0·2·1·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R042 using (lem-nat-1-BOXd⟨2·01⟩ ; lem-nat-3-BOXd⟨1·043⟩)
-- nat 3 BOXd(0;1243): 8 steps
lem-nat-3-BOXd⟨0·1243⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1234 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·1243⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-1243 ∷ []) (Bx⁻0-1234 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻1-043 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-043 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-034 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·043⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 3 2 (Bx⁻1-034 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·043⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 5 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 0 6 (Bx⁻0-1234 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;12): 3 steps
lem-nat-2-BOXd⟨0·12⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻0-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-13 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·12⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-12 ∷ []) (Bx⁻0-13 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw23 ∷ []) (lem-nat-2-CZ12 c4) ▸
       at 0 1 (Bx⁻0-13 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;042): 8 steps
lem-nat-2-BOXd⟨1·042⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-043 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·042⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-042 ∷ []) (Bx⁻1-043 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-12 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-12 ∷ Toff104 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-13 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·12⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 3 2 (Bx⁻0-13 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·12⟩ c4) ▸
       at 4 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 5 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 0 6 (Bx⁻1-043 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;1342): 8 steps
lem-nat-2-BOXd⟨0·1342⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1243 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·1342⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-1342 ∷ []) (Bx⁻0-1243 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-042 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-042 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-043 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·042⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 3 2 (Bx⁻1-043 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·042⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 5 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 0 6 (Bx⁻0-1243 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;02): 3 steps
lem-nat-0-BOXd⟨1·02⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-12 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·02⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-02 ∷ []) (Bx⁻0-12 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ02 ∷ []) (CZ12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻0-12 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;142): 8 steps
lem-nat-0-BOXd⟨0·142⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻0-142 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-042 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·142⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-142 ∷ []) (Bx⁻1-042 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-02 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-02 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-12 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·02⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 2 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 3 2 (Bx⁻0-12 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·02⟩ c4) ▸
       at 4 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 5 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 0 6 (Bx⁻1-042 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;0342): 8 steps
lem-nat-0-BOXd⟨1·0342⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1342 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·0342⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-0342 ∷ []) (Bx⁻0-1342 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻0-142 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-142 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-042 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·142⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻1-042 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·142⟩ c4) ▸
       at 4 2 (Toff013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻0-1342 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;12): 3 steps
lem-nat-0-BOXd⟨0·12⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻0-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-02 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·12⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-12 ∷ []) (Bx⁻1-02 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ12 ∷ []) (CZ02 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻1-02 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;042): 8 steps
lem-nat-0-BOXd⟨1·042⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-142 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·042⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-042 ∷ []) (Bx⁻0-142 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻0-12 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-12 ∷ Toff104 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-02 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·12⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 2 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 3 2 (Bx⁻1-02 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·12⟩ c4) ▸
       at 4 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 5 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-142 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;1342): 8 steps
lem-nat-0-BOXd⟨0·1342⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0342 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·1342⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-1342 ∷ []) (Bx⁻1-0342 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-042 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-042 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-142 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·042⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻0-142 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·042⟩ c4) ▸
       at 4 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻1-0342 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(0;1;34;2): 7 steps
lem-nat-0-SBOXd⟨0·1·34·2⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻0-1-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-34-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·1·34·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-1-34-2 ∷ []) (Sb⁻1-0-34-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb0-1-2-4 ∷ Toff234 ∷ Sb⁻0-1-2-4 ∷ Toff234 ∷ Bx⁻0-1342 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-2-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·2·4⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 2 2 (Sb⁻1-0-2-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·2·4⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 4 2 (Bx⁻1-0342 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·1342⟩ c4) ▸
       at 0 5 (Sb⁻1-0-34-2 ∷ []) (refl) ▸ done


-- nat 0 BOXd(2;01): 3 steps
lem-nat-0-BOXd⟨2·01⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻2-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-10 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·01⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻2-01 ∷ []) (Bx⁻2-10 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ01 ∷ []) (CZ01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻2-10 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;241): 8 steps
lem-nat-0-BOXd⟨0·241⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻0-241 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-240 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·241⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-241 ∷ []) (Bx⁻1-240 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻2-01 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-01 ∷ Toff024 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-10 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·01⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 2 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 3 2 (Bx⁻2-10 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·01⟩ c4) ▸
       at 4 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 5 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 0 6 (Bx⁻1-240 ∷ []) (refl) ▸ done


-- nat 0 BOXd(2;0341): 8 steps
lem-nat-0-BOXd⟨2·0341⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-1340 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·0341⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻2-0341 ∷ []) (Bx⁻2-1340 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻0-241 ∷ CCZ023 ∷ Toff203 ∷ Bx⁻0-241 ∷ Toff203 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-240 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·241⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff213 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻1-240 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·241⟩ c4) ▸
       at 4 2 (Toff213 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻2-1340 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;0;34;1): 7 steps
lem-nat-0-SBOXd⟨2·0·34·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻2-0-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-34-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·0·34·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-0-34-1 ∷ []) (Sb⁻2-1-34-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb2-0-1-4 ∷ Toff134 ∷ Sb⁻2-0-1-4 ∷ Toff134 ∷ Bx⁻2-0341 ∷ []) (refl) ▸
       at 0 2 (Sb2-1-0-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·1·4⟩ c4) ▸
       at 1 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 2 2 (Sb⁻2-1-0-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·0·1·4⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 4 2 (Bx⁻2-1340 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·0341⟩ c4) ▸
       at 0 5 (Sb⁻2-1-34-0 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;21): 3 steps
lem-nat-1-BOXd⟨0·21⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-12 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·21⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-21 ∷ []) (Bx⁻0-12 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ12 ∷ []) (CZ12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻0-12 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;041): 8 steps
lem-nat-1-BOXd⟨2·041⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻2-041 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-042 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·041⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-041 ∷ []) (Bx⁻1-042 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-21 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-21 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-12 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·21⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 3 2 (Bx⁻0-12 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·21⟩ c4) ▸
       at 4 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 5 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 0 6 (Bx⁻1-042 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;2341): 8 steps
lem-nat-1-BOXd⟨0·2341⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1342 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·2341⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-2341 ∷ []) (Bx⁻0-1342 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻2-041 ∷ CCZ023 ∷ Toff023 ∷ Bx⁻2-041 ∷ Toff023 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-042 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·041⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 3 2 (Bx⁻1-042 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·041⟩ c4) ▸
       at 4 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 5 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 0 6 (Bx⁻0-1342 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(0;2;34;1): 7 steps
lem-nat-1-SBOXd⟨0·2·34·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻0-2-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-34-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·2·34·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-2-34-1 ∷ []) (Sb⁻0-1-34-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb0-2-1-4 ∷ Toff134 ∷ Sb⁻0-2-1-4 ∷ Toff134 ∷ Bx⁻0-2341 ∷ []) (refl) ▸
       at 0 2 (Sb0-1-2-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·1·4⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻0-1-2-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·1·4⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻0-1342 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·2341⟩ c4) ▸
       at 0 5 (Sb⁻0-1-34-2 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;10): 3 steps
lem-nat-1-BOXd⟨2·10⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻2-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-20 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·10⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-10 ∷ []) (Bx⁻1-20 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 c4) ▸
       at 0 1 (Bx⁻1-20 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;240): 8 steps
lem-nat-1-BOXd⟨1·240⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻1-240 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-140 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·240⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-240 ∷ []) (Bx⁻2-140 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻2-10 ∷ CCZ124 ∷ Toff124 ∷ Bx⁻2-10 ∷ Toff124 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-20 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·10⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff214 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻1-20 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·10⟩ c4) ▸
       at 4 2 (Toff214 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻2-140 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;1340): 8 steps
lem-nat-1-BOXd⟨2·1340⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-2340 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·1340⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-1340 ∷ []) (Bx⁻1-2340 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻1-240 ∷ CCZ123 ∷ Toff213 ∷ Bx⁻1-240 ∷ Toff213 ∷ CCZ123 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-140 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·240⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻2-140 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·240⟩ c4) ▸
       at 4 2 (Toff123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻1-2340 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;1;34;0): 7 steps
lem-nat-1-SBOXd⟨2·1·34·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻2-1-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-34-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·1·34·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-1-34-0 ∷ []) (Sb⁻1-2-34-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb2-1-0-4 ∷ Toff034 ∷ Sb⁻2-1-0-4 ∷ Toff034 ∷ Bx⁻2-1340 ∷ []) (refl) ▸
       at 0 2 (Sb1-2-0-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·0·4⟩ c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Sb⁻1-2-0-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·1·0·4⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 4 2 (Bx⁻1-2340 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·1340⟩ c4) ▸
       at 0 5 (Sb⁻1-2-34-0 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;20): 3 steps
lem-nat-0-BOXd⟨1·20⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-21 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·20⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-20 ∷ []) (Bx⁻0-21 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ02 ∷ []) (CZ12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻0-21 ∷ []) (refl) ▸ done


-- nat 0 BOXd(2;140): 8 steps
lem-nat-0-BOXd⟨2·140⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻2-140 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-041 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·140⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻2-140 ∷ []) (Bx⁻2-041 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-20 ∷ CCZ124 ∷ Toff214 ∷ Bx⁻1-20 ∷ Toff214 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-21 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·20⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 3 2 (Bx⁻0-21 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·20⟩ c4) ▸
       at 4 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 5 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 0 6 (Bx⁻2-041 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;2340): 8 steps
lem-nat-0-BOXd⟨1·2340⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-2341 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·2340⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-2340 ∷ []) (Bx⁻0-2341 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻2-140 ∷ CCZ123 ∷ Toff123 ∷ Bx⁻2-140 ∷ Toff123 ∷ CCZ123 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-041 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·140⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻2-041 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·140⟩ c4) ▸
       at 4 2 (Toff023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻0-2341 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(1;2;34;0): 7 steps
lem-nat-0-SBOXd⟨1·2·34·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-34-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·2·34·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻1-2-34-0 ∷ []) (Sb⁻0-2-34-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb1-2-0-4 ∷ Toff034 ∷ Sb⁻1-2-0-4 ∷ Toff034 ∷ Bx⁻1-2340 ∷ []) (refl) ▸
       at 0 2 (Sb0-2-1-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·0·4⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 2 2 (Sb⁻0-2-1-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·2·0·4⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 4 2 (Bx⁻0-2341 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·2340⟩ c4) ▸
       at 0 5 (Sb⁻0-2-34-1 ∷ []) (refl) ▸ done


-- nat 3 BOXd(1;034): 8 steps
lem-nat-3-BOXd⟨1·034⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻1-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-043 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·034⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻1-034 ∷ []) (Bx⁻1-043 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-14 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-14 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-13 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·14⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 3 2 (Bx⁻0-13 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·14⟩ c4) ▸
       at 4 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 5 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 0 6 (Bx⁻1-043 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;1234): 8 steps
lem-nat-3-BOXd⟨0·1234⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1243 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-1234 ∷ []) (Bx⁻0-1243 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻1-034 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-034 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-043 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·034⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 3 2 (Bx⁻1-043 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·034⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 5 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 0 6 (Bx⁻0-1243 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;13): 3 steps
lem-nat-2-BOXd⟨0·13⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻0-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-12 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·13⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-13 ∷ []) (Bx⁻0-12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw23 ∷ []) (lem-nat-2-CZ13 c4) ▸
       at 0 1 (Bx⁻0-12 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;043): 8 steps
lem-nat-2-BOXd⟨1·043⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-043 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-042 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·043⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-043 ∷ []) (Bx⁻1-042 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-13 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-13 ∷ Toff104 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-12 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·13⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 3 2 (Bx⁻0-12 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·13⟩ c4) ▸
       at 4 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 5 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 0 6 (Bx⁻1-042 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;1243): 8 steps
lem-nat-2-BOXd⟨0·1243⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1342 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·1243⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-1243 ∷ []) (Bx⁻0-1342 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-043 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-043 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-042 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·043⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 3 2 (Bx⁻1-042 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·043⟩ c4) ▸
       at 4 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 5 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 0 6 (Bx⁻0-1342 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;12): 3 steps
lem-nat-1-BOXd⟨0·12⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-21 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·12⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-12 ∷ []) (Bx⁻0-21 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ12 ∷ []) (CZ12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻0-21 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;042): 8 steps
lem-nat-1-BOXd⟨1·042⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻1-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-041 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·042⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-042 ∷ []) (Bx⁻2-041 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-12 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-12 ∷ Toff104 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-21 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·12⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 3 2 (Bx⁻0-21 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·12⟩ c4) ▸
       at 4 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 5 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 0 6 (Bx⁻2-041 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;1342): 8 steps
lem-nat-1-BOXd⟨0·1342⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-2341 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·1342⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-1342 ∷ []) (Bx⁻0-2341 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻1-042 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-042 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-041 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·042⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 2 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 3 2 (Bx⁻2-041 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·042⟩ c4) ▸
       at 4 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 5 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 0 6 (Bx⁻0-2341 ∷ []) (refl) ▸ done


-- nat 0 BOXd(2;10): 3 steps
lem-nat-0-BOXd⟨2·10⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻2-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-01 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·10⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻2-10 ∷ []) (Bx⁻2-01 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ01 ∷ []) (CZ01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻2-01 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;240): 8 steps
lem-nat-0-BOXd⟨1·240⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-240 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-241 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·240⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-240 ∷ []) (Bx⁻0-241 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻2-10 ∷ CCZ124 ∷ Toff124 ∷ Bx⁻2-10 ∷ Toff124 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-01 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·10⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 3 2 (Bx⁻2-01 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·10⟩ c4) ▸
       at 4 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 5 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 0 6 (Bx⁻0-241 ∷ []) (refl) ▸ done


-- nat 0 BOXd(2;1340): 8 steps
lem-nat-0-BOXd⟨2·1340⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0341 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·1340⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻2-1340 ∷ []) (Bx⁻2-0341 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-240 ∷ CCZ123 ∷ Toff213 ∷ Bx⁻1-240 ∷ Toff213 ∷ CCZ123 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-241 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·240⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff203 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻0-241 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·240⟩ c4) ▸
       at 4 2 (Toff203 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻2-0341 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;2;43;1): 7 steps
lem-nat-3-SBOX⟨0·2·43·1⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-34-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·2·43·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-34-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-2341 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2431⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-2-1-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·1·3⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻0-2-1-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·2·1·3⟩ c4) ▸
       at 0 5 (Sb0-2-34-1 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;2;34;1): 7 steps
lem-nat-3-SBOX⟨0·2·34·1⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb0-2-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·2·34·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-2-34-1 ∷ []) (Sb0-2-43-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx0-2341 ∷ Toff134 ∷ Sb0-2-1-4 ∷ Toff134 ∷ Sb⁻0-2-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx0-2431 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2341⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-2-1-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·1·4⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻0-2-1-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·2·1·4⟩ c4) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- nat 1 BOXd(3;01): 3 steps
lem-nat-1-BOXd⟨3·01⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻3-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-02 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨3·01⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻3-01 ∷ []) (Bx⁻3-02 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 c4) ▸
       at 0 1 (Bx⁻3-02 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;321): 8 steps
lem-nat-1-BOXd⟨0·321⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-321 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-312 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·321⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-321 ∷ []) (Bx⁻0-312 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻3-01 ∷ CCZ023 ∷ Toff023 ∷ Bx⁻3-01 ∷ Toff023 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻3-02 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨3·01⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 3 2 (Bx⁻3-02 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨3·01⟩ c4) ▸
       at 4 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 5 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 0 6 (Bx⁻0-312 ∷ []) (refl) ▸ done


-- nat 1 BOXd(3;0421): 8 steps
lem-nat-1-BOXd⟨3·0421⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-0412 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨3·0421⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻3-0421 ∷ []) (Bx⁻3-0412 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-321 ∷ CCZ034 ∷ Toff304 ∷ Bx⁻0-321 ∷ Toff304 ∷ CCZ034 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-312 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·321⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 2 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 3 2 (Bx⁻0-312 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·321⟩ c4) ▸
       at 4 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 5 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 0 6 (Bx⁻3-0412 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;032): 8 steps
lem-nat-2-BOXd⟨1·032⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-032 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-023 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·032⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-032 ∷ []) (Bx⁻1-023 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-12 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-12 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-13 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·12⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 3 2 (Bx⁻0-13 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·12⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 5 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 0 6 (Bx⁻1-023 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;1432): 8 steps
lem-nat-2-BOXd⟨0·1432⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1423 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·1432⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-1432 ∷ []) (Bx⁻0-1423 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-032 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-032 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-023 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·032⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 3 2 (Bx⁻1-023 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·032⟩ c4) ▸
       at 4 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 5 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-1423 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;132): 8 steps
lem-nat-0-BOXd⟨0·132⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻0-132 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-032 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·132⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-132 ∷ []) (Bx⁻1-032 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-02 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-02 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-12 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·02⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻0-12 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·02⟩ c4) ▸
       at 4 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻1-032 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;0432): 8 steps
lem-nat-0-BOXd⟨1·0432⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1432 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·0432⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-0432 ∷ []) (Bx⁻0-1432 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻0-132 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-132 ∷ Toff104 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-032 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·132⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 2 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 3 2 (Bx⁻1-032 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·132⟩ c4) ▸
       at 4 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 5 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-1432 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;231): 8 steps
lem-nat-1-BOXd⟨0·231⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-231 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-132 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·231⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-231 ∷ []) (Bx⁻0-132 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻2-01 ∷ CCZ023 ∷ Toff023 ∷ Bx⁻2-01 ∷ Toff023 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-02 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·01⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 3 2 (Bx⁻1-02 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·01⟩ c4) ▸
       at 4 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 5 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 0 6 (Bx⁻0-132 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;0431): 8 steps
lem-nat-1-BOXd⟨2·0431⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0432 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·0431⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-0431 ∷ []) (Bx⁻1-0432 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-231 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-231 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-132 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·231⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 3 2 (Bx⁻0-132 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·231⟩ c4) ▸
       at 4 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 5 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 0 6 (Bx⁻1-0432 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;1;43;2): 7 steps
lem-nat-2-SBOXd⟨0·1·43·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-42-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·1·43·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-1-43-2 ∷ []) (Sb⁻0-1-42-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ Toff234 ∷ Bx⁻0-1432 ∷ []) (refl) ▸
       at 0 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1432⟩ c4) ▸
       at 0 5 (Sb⁻0-1-42-3 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;023): 8 steps
lem-nat-2-BOXd⟨1·023⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-032 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·023⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-023 ∷ []) (Bx⁻1-032 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-13 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-13 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-12 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·13⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 3 2 (Bx⁻0-12 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·13⟩ c4) ▸
       at 4 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 5 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 0 6 (Bx⁻1-032 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;1423): 8 steps
lem-nat-2-BOXd⟨0·1423⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1432 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·1423⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-1423 ∷ []) (Bx⁻0-1432 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-023 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-023 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-032 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·023⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 3 2 (Bx⁻1-032 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·023⟩ c4) ▸
       at 4 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 5 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-1432 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;1;42;3): 7 steps
lem-nat-2-SBOXd⟨0·1·42·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-43-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·1·42·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-1-42-3 ∷ []) (Sb⁻0-1-43-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Toff324 ∷ Bx⁻0-1423 ∷ []) (refl) ▸
       at 0 2 (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1423⟩ c4) ▸
       at 0 5 (Sb⁻0-1-43-2 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(1;0;43;2): 7 steps
lem-nat-0-SBOXd⟨1·0·43·2⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-43-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·0·43·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻1-0-43-2 ∷ []) (Sb⁻0-1-43-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ Toff234 ∷ Bx⁻1-0432 ∷ []) (refl) ▸
       at 0 2 (Sb0-1-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 2 2 (Sb⁻0-1-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·2·3⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 4 2 (Bx⁻0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0432⟩ c4) ▸
       at 0 5 (Sb⁻0-1-43-2 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;032): 8 steps
lem-nat-0-BOXd⟨1·032⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-032 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-132 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·032⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-032 ∷ []) (Bx⁻0-132 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻0-12 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-12 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-02 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·12⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻1-02 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·12⟩ c4) ▸
       at 4 2 (Toff013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻0-132 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;1432): 8 steps
lem-nat-0-BOXd⟨0·1432⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0432 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·1432⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-1432 ∷ []) (Bx⁻1-0432 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-032 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-032 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-132 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·032⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 2 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 3 2 (Bx⁻0-132 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·032⟩ c4) ▸
       at 4 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 5 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 0 6 (Bx⁻1-0432 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(0;1;43;2): 7 steps
lem-nat-0-SBOXd⟨0·1·43·2⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-43-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·1·43·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-1-43-2 ∷ []) (Sb⁻1-0-43-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ Toff234 ∷ Bx⁻0-1432 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·2·3⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 2 2 (Sb⁻1-0-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 4 2 (Bx⁻1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·1432⟩ c4) ▸
       at 0 5 (Sb⁻1-0-43-2 ∷ []) (refl) ▸ done


-- nat 0 SBOX(3;1;42;0): 7 steps
lem-nat-0-SBOX⟨3·1·42·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-42-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·1·42·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb3-1-42-0 ∷ []) (Sb3-0-42-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 0 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 2 2 (Sb3-0-1-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·0·2⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 4 2 (Sb⁻3-0-1-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨3·1·0·2⟩ c4) ▸
       at 0 5 (Sb3-0-42-1 ∷ []) (refl) ▸ done


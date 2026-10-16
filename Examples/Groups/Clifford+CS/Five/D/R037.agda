{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R037 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-2-CCZ034 ; lem-nat-2-TOFF034 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF014 ; lem-nat-3-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-3-CCZ013 ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-3-TOFF203 ; lem-nat-3-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-CZ14)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-CZ04)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-TOFF024 ; lem-nat-0-TOFF413 ; lem-nat-2-TOFF214 ; lem-nat-3-TOFF023)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0412⟩ ; lem-nat-3-TOFF103)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-CZ13)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-CS01)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-CS12 ; lem-nat-2-CS13 ; lem-nat-2-CSd12 ; lem-nat-2-CSd13 ; lem-nat-2-TOFF314)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-2-CS02 ; lem-nat-2-CSd02 ; lem-nat-3-CS23 ; lem-nat-3-CS24)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-1-CSd01 ; lem-nat-2-TOFF124)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-3-TOFF024)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-0-BOX⟨0·34⟩ ; lem-nat-0-BOX⟨1·34⟩ ; lem-nat-2-CS03 ; lem-nat-2-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-TOFF124 ; lem-nat-2-BOX⟨1·20⟩ ; lem-nat-2-BOX⟨1·30⟩)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-2-TOFF134)
open import Examples.Groups.Clifford+CS.Five.D.R024 using (lem-nat-3-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R027 using (lem-nat-3-CSd23)
open import Examples.Groups.Clifford+CS.Five.D.R028 using (lem-nat-1-BOX⟨3·0421⟩)
open import Examples.Groups.Clifford+CS.Five.D.R034 using (lem-nat-2-BOX⟨0·31⟩)
-- nat 2 SBOXd(3;1;0;4): 2 steps
lem-nat-2-SBOXd⟨3·1·0·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻3-1-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-0-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·1·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻3-1-0-4 ∷ []) (Sb⁻2-1-0-4 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb⁻3-1-0-4 ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 0 1 (Sb⁻2-1-0-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(2;1;0;3): 2 steps
lem-nat-3-SBOXd⟨2·1·0·3⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻2-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-0-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·1·0·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-1-0-3 ∷ []) (Sb⁻2-1-0-4 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻2-1-0-3 ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 0 1 (Sb⁻2-1-0-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(2;1;0;4): 2 steps
lem-nat-3-SBOXd⟨2·1·0·4⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻2-1-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-0-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·1·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-1-0-4 ∷ []) (Sb⁻2-1-0-3 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻2-1-0-4 ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 0 1 (Sb⁻2-1-0-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(2;0;1;3): 3 steps
lem-nat-0-SBOXd⟨2·0·1·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻2-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·0·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-0-1-3 ∷ []) (Sb⁻2-1-0-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 2 (CS01⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻2-1-0-3 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;1;0;3): 3 steps
lem-nat-0-SBOXd⟨2·1·0·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻2-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-1-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·1·0·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-1-0-3 ∷ []) (Sb⁻2-0-1-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 2 (CS01⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻2-0-1-3 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;031): 8 steps
lem-nat-3-BOX⟨2·031⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-041 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·031⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-031 ∷ []) (Bx2-041 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 2 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 3 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 0 6 (Bx2-041 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;2431): 8 steps
lem-nat-3-BOX⟨0·2431⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·2431⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-2431 ∷ []) (Bx0-2341 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 2 2 (Bx2-041 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·031⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx2-041 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·031⟩ c4) ▸
       at 0 6 (Bx0-2341 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;041): 8 steps
lem-nat-3-BOX⟨2·041⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-031 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·041⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-041 ∷ []) (Bx2-031 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4) ▸
       at 2 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 3 2 (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 0 6 (Bx2-031 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;2341): 8 steps
lem-nat-3-BOX⟨0·2341⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·2341⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-2341 ∷ []) (Bx0-2431 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 2 2 (Bx2-031 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·041⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx2-031 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·041⟩ c4) ▸
       at 0 6 (Bx0-2431 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;021): 8 steps
lem-nat-2-BOX⟨3·021⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-021 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-031 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·021⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-021 ∷ []) (Bx2-031 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff203 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-21 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·31⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-21 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·31⟩ c4) ▸
       at 0 6 (Bx2-031 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;3421): 8 steps
lem-nat-2-BOX⟨0·3421⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·3421⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-3421 ∷ []) (Bx0-2431 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 2 2 (Bx2-031 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·021⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx2-031 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·021⟩ c4) ▸
       at 0 6 (Bx0-2431 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;104): 8 steps
lem-nat-0-BOX⟨3·104⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-014 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·104⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-104 ∷ []) (Bx3-014 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-34 ∷ Toff301 ∷ CCZ013 ∷ Bx1-34 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-34 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·34⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-34 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·34⟩ c4) ▸
       at 0 6 (Bx3-014 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;3204): 8 steps
lem-nat-0-BOX⟨1·3204⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-3204 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·3204⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-3204 ∷ []) (Bx0-3214 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-104 ∷ Toff123 ∷ CCZ123 ∷ Bx3-104 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·104⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·104⟩ c4) ▸
       at 0 6 (Bx0-3214 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;014): 8 steps
lem-nat-0-BOX⟨3·014⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-104 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·014⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-014 ∷ []) (Bx3-104 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-34 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·34⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-34 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·34⟩ c4) ▸
       at 0 6 (Bx3-104 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;3214): 8 steps
lem-nat-0-BOX⟨0·3214⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3204 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·3214⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-3214 ∷ []) (Bx1-3204 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff023 ∷ []) (Toff123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-104 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·014⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff023 ∷ []) (Toff123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-104 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·014⟩ c4) ▸
       at 0 6 (Bx1-3204 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;2;4;0): 3 steps
lem-nat-2-SBOX⟨1·2·4·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb1-2-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-4-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·2·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-2-4-0 ∷ []) (Sb1-3-4-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb1-3-4-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;3;4;0): 3 steps
lem-nat-2-SBOX⟨1·3·4·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb1-3-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-4-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·3·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-3-4-0 ∷ []) (Sb1-2-4-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS34 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb1-2-4-0 ∷ []) (refl) ▸ done


-- nat 3 SBOX(1;2;3;0): 3 steps
lem-nat-3-SBOX⟨1·2·3·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-4-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·2·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb1-2-3-0 ∷ []) (Sb1-2-4-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw34 ∷ []) (lem-nat-3-CS23 c4) ▸
       at 0 1 (Sb1-2-4-0 ∷ []) (refl) ▸ done


-- nat 3 SBOX(1;2;4;0): 3 steps
lem-nat-3-SBOX⟨1·2·4·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb1-2-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-3-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·2·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb1-2-4-0 ∷ []) (Sb1-2-3-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw34 ∷ []) (lem-nat-3-CS24 c4) ▸
       at 0 1 (Sb1-2-3-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;1;3;2): 3 steps
lem-nat-1-SBOX⟨0·1·3·2⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-3-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·1·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-1-3-2 ∷ []) (Sb0-2-3-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-2-3-1 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;2;3;1): 3 steps
lem-nat-1-SBOX⟨0·2·3·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·2·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-2-3-1 ∷ []) (Sb0-1-3-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;2;4;0): 3 steps
lem-nat-2-SBOXd⟨1·2·4·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻1-2-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-4-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·2·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-2-4-0 ∷ []) (Sb⁻1-3-4-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻1-3-4-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;3;4;0): 3 steps
lem-nat-2-SBOXd⟨1·3·4·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻1-3-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-4-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·3·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-3-4-0 ∷ []) (Sb⁻1-2-4-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻1-2-4-0 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(1;2;3;0): 3 steps
lem-nat-3-SBOXd⟨1·2·3·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-4-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·2·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-2-3-0 ∷ []) (Sb⁻1-2-4-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS23⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd23 c4) ▸
       at 0 1 (Sb⁻1-2-4-0 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(1;2;4;0): 3 steps
lem-nat-3-SBOXd⟨1·2·4·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻1-2-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-3-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·2·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-2-4-0 ∷ []) (Sb⁻1-2-3-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd24 c4) ▸
       at 0 1 (Sb⁻1-2-3-0 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(0;1;3;2): 3 steps
lem-nat-1-SBOXd⟨0·1·3·2⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-3-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·1·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-2-3-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-2-3-1 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(0;2;3;1): 3 steps
lem-nat-1-SBOXd⟨0·2·3·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·2·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻0-1-3-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS23⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;130): 8 steps
lem-nat-2-BOX⟨2·130⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-130 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-120 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·130⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-130 ∷ []) (Bx3-120 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-20 ∷ Toff213 ∷ CCZ123 ∷ Bx1-20 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff213 ∷ []) (Toff312 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-30 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·20⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff213 ∷ []) (Toff312 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-30 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·20⟩ c4) ▸
       at 0 6 (Bx3-120 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;2430): 8 steps
lem-nat-2-BOX⟨1·2430⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3420 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·2430⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-2430 ∷ []) (Bx1-3420 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-130 ∷ Toff124 ∷ CCZ124 ∷ Bx2-130 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 2 2 (Bx3-120 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·130⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx3-120 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·130⟩ c4) ▸
       at 0 6 (Bx1-3420 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;120): 8 steps
lem-nat-2-BOX⟨3·120⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-120 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-130 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·120⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-120 ∷ []) (Bx2-130 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-30 ∷ Toff312 ∷ CCZ123 ∷ Bx1-30 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff312 ∷ []) (Toff213 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-20 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·30⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff312 ∷ []) (Toff213 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-20 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·30⟩ c4) ▸
       at 0 6 (Bx2-130 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;3420): 8 steps
lem-nat-2-BOX⟨1·3420⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-3420 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2430 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·3420⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-3420 ∷ []) (Bx1-2430 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-120 ∷ Toff134 ∷ CCZ134 ∷ Bx3-120 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 2 2 (Bx2-130 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·120⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx2-130 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·120⟩ c4) ▸
       at 0 6 (Bx1-2430 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;132): 8 steps
lem-nat-3-BOX⟨0·132⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-142 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·132⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-132 ∷ []) (Bx0-142 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-02 ∷ Toff013 ∷ CCZ013 ∷ Bx1-02 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 2 2 (Bx1-02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 3 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx1-02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 0 6 (Bx0-142 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;0432): 8 steps
lem-nat-3-BOX⟨1·0432⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·0432⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-0432 ∷ []) (Bx1-0342 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-132 ∷ Toff104 ∷ CCZ014 ∷ Bx0-132 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 1 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 2 2 (Bx0-142 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·132⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 4 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 5 2 (Bx0-142 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·132⟩ c4) ▸
       at 0 6 (Bx1-0342 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(2;3;4;1): 3 steps
lem-nat-3-SBOXd⟨2·3·4·1⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻2-3-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-3-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·3·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-3-4-1 ∷ []) (Sb⁻2-4-3-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 2 (CS34⁻ ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(2;4;3;1): 3 steps
lem-nat-3-SBOXd⟨2·4·3·1⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻2-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-4-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·4·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-4-3-1 ∷ []) (Sb⁻2-3-4-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 2 (CS34⁻ ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻2-3-4-1 ∷ []) (refl) ▸ done


-- resp TOFF203 at 1: 2 steps
lem-resp-TOFF203-at-1 : Complete 4 → ⟪ (Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF203-at-1 c4 = run b0
  where
  b0 : Chain (Toff203 ∷ []) (Sw01 ∷ Toff213 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ Toff213 ∷ []) (lw4 c4 (Toff203 ∷ Sw01 ∷ []) (Sw01 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸ done


-- resp CX14 at 2: 4 steps
lem-resp-CX14-at-2 : Complete 4 → ⟪ (CX14 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX24 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX14-at-2 c4 = run b0
  where
  b0 : Chain (CX14 ∷ []) (Sw12 ∷ Sw01 ∷ CX24 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw12 ∷ CX24 ∷ []) (lw0 c4 (CX14 ∷ Sw12 ∷ []) (Sw12 ∷ CX24 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CX24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CX₀₁ • Swap ↑))) ▸ done


-- nat 0 BOX(0;41): 3 steps
lem-nat-0-BOX⟨0·41⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-40 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·41⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-41 ∷ []) (Bx1-40 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw01 ∷ []) (lem-nat-0-CZ14 c4) ▸
       at 0 1 (Bx1-40 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;031): 8 steps
lem-nat-0-BOX⟨4·031⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-130 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·031⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-031 ∷ []) (Bx4-130 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 2 2 (Bx1-40 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·41⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx1-40 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·41⟩ c4) ▸
       at 0 6 (Bx4-130 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;4231): 8 steps
lem-nat-0-BOX⟨0·4231⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4230 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·4231⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-4231 ∷ []) (Bx1-4230 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 2 2 (Bx4-130 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·031⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx4-130 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·031⟩ c4) ▸
       at 0 6 (Bx1-4230 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;40): 3 steps
lem-nat-0-BOX⟨1·40⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-40 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-41 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·40⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-40 ∷ []) (Bx0-41 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw01 ∷ []) (lem-nat-0-CZ04 c4) ▸
       at 0 1 (Bx0-41 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;130): 8 steps
lem-nat-0-BOX⟨4·130⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-130 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-031 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·130⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-130 ∷ []) (Bx4-031 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx1-40 ∷ Toff413 ∷ CCZ134 ∷ Bx1-40 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 2 2 (Bx0-41 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·40⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx0-41 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·40⟩ c4) ▸
       at 0 6 (Bx4-031 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;4230): 8 steps
lem-nat-0-BOX⟨1·4230⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-4230 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·4230⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-4230 ∷ []) (Bx0-4231 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-130 ∷ Toff124 ∷ CCZ124 ∷ Bx4-130 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 2 2 (Bx4-031 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·130⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx4-031 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·130⟩ c4) ▸
       at 0 6 (Bx0-4231 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;032): 8 steps
lem-nat-3-BOX⟨1·032⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-032 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-042 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·032⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-032 ∷ []) (Bx1-042 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 2 2 (Bx0-12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 3 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx0-12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 0 6 (Bx1-042 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;1432): 8 steps
lem-nat-3-BOX⟨0·1432⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·1432⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-1432 ∷ []) (Bx0-1342 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 1 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 2 2 (Bx1-042 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·032⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 4 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 5 2 (Bx1-042 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·032⟩ c4) ▸
       at 0 6 (Bx0-1342 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;0;1;2): 3 steps
lem-nat-1-SBOX⟨3·0·1·2⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb3-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-2-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·0·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-0-1-2 ∷ []) (Sb3-0-2-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 0 1 (Sb3-0-2-1 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(3;0;1;2): 3 steps
lem-nat-1-SBOXd⟨3·0·1·2⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻3-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-2-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·0·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻3-0-1-2 ∷ []) (Sb⁻3-0-2-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 0 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;0;42;1): 7 steps
lem-nat-1-SBOX⟨3·0·42·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb3-0-42-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·0·42·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-0-42-1 ∷ []) (Sb3-0-41-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx3-0421 ∷ Toff124 ∷ Sb3-0-1-2 ∷ Toff124 ∷ Sb⁻3-0-1-2 ∷ []) (refl) ▸
       at 0 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ c4) ▸
       at 1 2 (Toff214 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb3-0-2-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·1·2⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻3-0-2-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·0·1·2⟩ c4) ▸
       at 0 5 (Sb3-0-41-2 ∷ []) (refl) ▸ done


-- nat 2 SBOX(2;0;3;1): 3 steps
lem-nat-2-SBOX⟨2·0·3·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·0·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-0-3-1 ∷ []) (Sb3-0-2-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 0 1 (Sb3-0-2-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(2;0;3;1): 3 steps
lem-nat-2-SBOXd⟨2·0·3·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·0·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻3-0-2-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4) ▸
       at 0 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(2;0;41;3): 7 steps
lem-nat-2-SBOX⟨2·0·41·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·0·41·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 2 2 (Sb3-0-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·3·1⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 4 2 (Sb⁻3-0-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·0·3·1⟩ c4) ▸
       at 0 5 (Sb3-0-41-2 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;0;2;1): 3 steps
lem-nat-2-SBOX⟨3·0·2·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-0-2-1 ∷ []) (Sb2-0-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 0 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(3;0;2;1): 3 steps
lem-nat-2-SBOXd⟨3·0·2·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻3-0-2-1 ∷ []) (Sb⁻2-0-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4) ▸
       at 0 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;0;41;2): 7 steps
lem-nat-2-SBOX⟨3·0·41·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·0·41·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-0-41-2 ∷ []) (Sb2-0-41-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 0 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ c4) ▸
       at 1 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 2 2 (Sb2-0-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·2·1⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 4 2 (Sb⁻2-0-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·0·2·1⟩ c4) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;1;2;4): 3 steps
lem-nat-2-SBOX⟨0·1·2·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb0-1-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·1·2·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-1-2-4 ∷ []) (Sb0-1-3-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4) ▸
       at 0 1 (Sb0-1-3-4 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;1;3;4): 3 steps
lem-nat-2-SBOX⟨0·1·3·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb0-1-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·1·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-1-3-4 ∷ []) (Sb0-1-2-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 c4) ▸
       at 0 1 (Sb0-1-2-4 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;1;2;3): 2 steps
lem-nat-3-SBOX⟨0·1·2·3⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·1·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-2-4 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb0-1-2-3 ∷ Sw34 ∷ []) (sym (c₃ (CS ↑) (Swap))) ▸
       at 0 1 (Sb0-1-2-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOX(0;1;2;4): 2 steps
lem-nat-3-SBOX⟨0·1·2·4⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb0-1-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·1·2·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-1-2-4 ∷ []) (Sb0-1-2-3 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb0-1-2-4 ∷ Sw34 ∷ []) (sym (c₃ (CS ↑) (Swap))) ▸
       at 0 1 (Sb0-1-2-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOXd(0;1;2;4): 3 steps
lem-nat-2-SBOXd⟨0·1·2·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻0-1-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·1·2·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-1-2-4 ∷ []) (Sb⁻0-1-3-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4) ▸
       at 0 1 (Sb⁻0-1-3-4 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;1;3;4): 3 steps
lem-nat-2-SBOXd⟨0·1·3·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻0-1-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·1·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-1-3-4 ∷ []) (Sb⁻0-1-2-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 c4) ▸
       at 0 1 (Sb⁻0-1-2-4 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;1;2;3): 2 steps
lem-nat-3-SBOXd⟨0·1·2·3⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·1·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-2-4 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻0-1-2-3 ∷ Sw34 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (Swap))) ▸
       at 0 1 (Sb⁻0-1-2-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(0;1;2;4): 2 steps
lem-nat-3-SBOXd⟨0·1·2·4⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻0-1-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·1·2·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-1-2-4 ∷ []) (Sb⁻0-1-2-3 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻0-1-2-4 ∷ Sw34 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (Swap))) ▸
       at 0 1 (Sb⁻0-1-2-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(4;13): 3 steps
lem-nat-2-BOX⟨4·13⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-12 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·13⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-13 ∷ []) (Bx4-12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw23 ∷ []) (lem-nat-2-CZ13 c4) ▸
       at 0 1 (Bx4-12 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;423): 8 steps
lem-nat-2-BOX⟨1·423⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-432 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·423⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-423 ∷ []) (Bx1-432 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 2 2 (Bx4-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·13⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx4-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·13⟩ c4) ▸
       at 0 6 (Bx1-432 ∷ []) (refl) ▸ done


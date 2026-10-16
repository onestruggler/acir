{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R029 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF301 ; lem-nat-3-CCZ024 ; lem-nat-3-CCZ034 ; lem-nat-3-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-TOFF302 ; lem-nat-2-BOX⟨0·34⟩)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-2-TOFF413)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF304 ; lem-nat-0-TOFF314 ; lem-nat-0-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-3-CZ23 ; lem-nat-3-TOFF302)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-2-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-TOFF024 ; lem-nat-0-TOFF413 ; lem-nat-1-TOFF013 ; lem-nat-2-BOX⟨0·2314⟩ ; lem-nat-3-TOFF023 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-3-TOFF103)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-CCZ014 ; lem-nat-3-BOX⟨0·24⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-BOX⟨0·23⟩ ; lem-nat-0-BOX⟨1·23⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-0-BOX⟨0·1324⟩ ; lem-nat-2-TOFF014 ; lem-nat-2-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-CS14 ; lem-nat-3-CS23 ; lem-nat-3-CS24)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-1-TOFF403 ; lem-nat-3-BOX⟨3·02⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-0-BOX⟨4·01⟩ ; lem-nat-0-BOX⟨4·10⟩ ; lem-nat-0-CSd14 ; lem-nat-1-BOX⟨4·01⟩ ; lem-nat-1-TOFF402 ; lem-nat-2-BOX⟨4·02⟩ ; lem-nat-3-BOX⟨3·04⟩ ; lem-nat-3-TOFF024)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-3-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-TOFF124)
open import Examples.Groups.Clifford+CS.Five.D.R024 using (lem-nat-3-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R025 using (lem-nat-1-BOX⟨0·3214⟩)
open import Examples.Groups.Clifford+CS.Five.D.R027 using (lem-nat-3-CSd23)
open import Examples.Groups.Clifford+CS.Five.D.R028 using (lem-nat-3-BOX⟨0·124⟩)
-- nat 3 BOX(1;0324): 8 steps
lem-nat-3-BOX⟨1·0324⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·0324⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-0324 ∷ []) (Bx1-0423 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-124 ∷ Toff103 ∷ CCZ013 ∷ Bx0-124 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 2 2 (Bx0-123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·124⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx0-123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·124⟩ c4) ▸
       at 0 6 (Bx1-0423 ∷ []) (refl) ▸ done


-- comm CCZ134 CX20: 23 steps
lem-comm-CCZ134-CX20 : Complete 4 → ⟪ (CCZ134 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CCZ134 ∷ []) ⟫ʷ
lem-comm-CCZ134-CX20 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CCZ134 ∷ CX20 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ CCZ124 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ CCZ124 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸
       at 6 2 (Sw12 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CX20 ∷ CCZ134 ∷ [])
  b2 = at 10 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 2 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 1 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd04 CCZ123: 13 steps
lem-comm-CSd04-CCZ123 : Complete 4 → ⟪ (CS04⁻ ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-comm-CSd04-CCZ123 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS04⁻ ∷ CCZ123 ∷ []) (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 2 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (CCZ123 ∷ CS04⁻ ∷ [])
  b1 = at 2 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 1 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOX(0;3;4;1): 2 steps
lem-nat-1-SBOX⟨0·3·4·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb0-3-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-4-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·3·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-3-4-1 ∷ []) (Sb0-3-4-2 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Sb0-3-4-1 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 0 1 (Sb0-3-4-2 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOXd(0;3;4;1): 2 steps
lem-nat-1-SBOXd⟨0·3·4·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻0-3-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-4-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·3·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-3-4-1 ∷ []) (Sb⁻0-3-4-2 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Sb⁻0-3-4-1 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS)) ▸
       at 0 1 (Sb⁻0-3-4-2 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOX(0;3;21;4): 7 steps
lem-nat-1-SBOX⟨0·3·21·4⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb0-3-21-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-12-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·3·21·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-3-21-4 ∷ []) (Sb0-3-12-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx0-3214 ∷ Toff412 ∷ Sb0-3-4-1 ∷ Toff412 ∷ Sb⁻0-3-4-1 ∷ []) (refl) ▸
       at 0 2 (Bx0-3124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3214⟩ c4) ▸
       at 1 2 (Toff412 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-3-4-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·3·4·1⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻0-3-4-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·3·4·1⟩ c4) ▸
       at 0 5 (Sb0-3-12-4 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;024): 8 steps
lem-nat-1-BOX⟨3·024⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-014 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·024⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-024 ∷ []) (Bx3-014 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 2 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 0 6 (Bx3-014 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;3124): 8 steps
lem-nat-1-BOX⟨0·3124⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·3124⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-3124 ∷ []) (Bx0-3214 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 2 2 (Bx3-014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·024⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx3-014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·024⟩ c4) ▸
       at 0 6 (Bx0-3214 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;3;4;2): 2 steps
lem-nat-1-SBOX⟨0·3·4·2⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb0-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-4-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·3·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-3-4-2 ∷ []) (Sb0-3-4-1 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Sb0-3-4-2 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 0 1 (Sb0-3-4-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOXd(0;3;4;2): 2 steps
lem-nat-1-SBOXd⟨0·3·4·2⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻0-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-4-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·3·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-3-4-2 ∷ []) (Sb⁻0-3-4-1 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Sb⁻0-3-4-2 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS)) ▸
       at 0 1 (Sb⁻0-3-4-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOX(0;3;12;4): 7 steps
lem-nat-1-SBOX⟨0·3·12·4⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb0-3-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-21-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·3·12·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-3-12-4 ∷ []) (Sb0-3-21-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx0-3124 ∷ Toff412 ∷ Sb0-3-4-2 ∷ Toff412 ∷ Sb⁻0-3-4-2 ∷ []) (refl) ▸
       at 0 2 (Bx0-3214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3124⟩ c4) ▸
       at 1 2 (Toff412 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-3-4-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·3·4·2⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻0-3-4-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·3·4·2⟩ c4) ▸
       at 0 5 (Sb0-3-21-4 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;2;4;1): 3 steps
lem-nat-2-SBOX⟨0·2·4·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb0-2-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-4-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·2·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-2-4-1 ∷ []) (Sb0-3-4-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-3-4-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;2;4;1): 3 steps
lem-nat-2-SBOXd⟨0·2·4·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻0-2-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-4-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·2·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-2-4-1 ∷ []) (Sb⁻0-3-4-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-3-4-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;2;31;4): 7 steps
lem-nat-2-SBOX⟨0·2·31·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb0-2-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-21-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·2·31·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-2-31-4 ∷ []) (Sb0-3-21-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx0-2314 ∷ Toff413 ∷ Sb0-2-4-1 ∷ Toff413 ∷ Sb⁻0-2-4-1 ∷ []) (refl) ▸
       at 0 2 (Bx0-3214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2314⟩ c4) ▸
       at 1 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 2 2 (Sb0-3-4-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·2·4·1⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 4 2 (Sb⁻0-3-4-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·2·4·1⟩ c4) ▸
       at 0 5 (Sb0-3-21-4 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;014): 8 steps
lem-nat-2-BOX⟨3·014⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-014 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·014⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-014 ∷ []) (Bx2-014 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 2 2 (Bx0-24 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·34⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx0-24 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·34⟩ c4) ▸
       at 0 6 (Bx2-014 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;3214): 8 steps
lem-nat-2-BOX⟨0·3214⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·3214⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-3214 ∷ []) (Bx0-2314 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-014 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·014⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-014 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·014⟩ c4) ▸
       at 0 6 (Bx0-2314 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;3;4;1): 3 steps
lem-nat-2-SBOX⟨0·3·4·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb0-3-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-4-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·3·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-3-4-1 ∷ []) (Sb0-2-4-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS34 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-2-4-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;3;4;1): 3 steps
lem-nat-2-SBOXd⟨0·3·4·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻0-3-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-4-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·3·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-3-4-1 ∷ []) (Sb⁻0-2-4-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-2-4-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;3;21;4): 7 steps
lem-nat-2-SBOX⟨0·3·21·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb0-3-21-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-31-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·3·21·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-3-21-4 ∷ []) (Sb0-2-31-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx0-3214 ∷ Toff412 ∷ Sb0-3-4-1 ∷ Toff412 ∷ Sb⁻0-3-4-1 ∷ []) (refl) ▸
       at 0 2 (Bx0-2314 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3214⟩ c4) ▸
       at 1 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 2 2 (Sb0-2-4-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·3·4·1⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 4 2 (Sb⁻0-2-4-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·3·4·1⟩ c4) ▸
       at 0 5 (Sb0-2-31-4 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;23): 3 steps
lem-nat-3-BOX⟨0·23⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-24 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·23⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-23 ∷ []) (Bx0-24 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw34 ∷ []) (lem-nat-3-CZ23 c4) ▸
       at 0 1 (Bx0-24 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;013): 8 steps
lem-nat-3-BOX⟨2·013⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-014 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·013⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-013 ∷ []) (Bx2-014 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 2 2 (Bx0-24 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·23⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx0-24 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·23⟩ c4) ▸
       at 0 6 (Bx2-014 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;2413): 8 steps
lem-nat-3-BOX⟨0·2413⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·2413⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-2413 ∷ []) (Bx0-2314 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 2 2 (Bx2-014 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·013⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx2-014 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·013⟩ c4) ▸
       at 0 6 (Bx0-2314 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;2;3;1): 3 steps
lem-nat-3-SBOX⟨0·2·3·1⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-4-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·2·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-2-3-1 ∷ []) (Sb0-2-4-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw34 ∷ []) (lem-nat-3-CS23 c4) ▸
       at 0 1 (Sb0-2-4-1 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;2;3;1): 3 steps
lem-nat-3-SBOXd⟨0·2·3·1⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-4-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·2·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻0-2-4-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS23⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd23 c4) ▸
       at 0 1 (Sb⁻0-2-4-1 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;2;41;3): 7 steps
lem-nat-3-SBOX⟨0·2·41·3⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb0-2-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-31-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·2·41·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-2-41-3 ∷ []) (Sb0-2-31-4 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx0-2413 ∷ Toff314 ∷ Sb0-2-3-1 ∷ Toff314 ∷ Sb⁻0-2-3-1 ∷ []) (refl) ▸
       at 0 2 (Bx0-2314 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2413⟩ c4) ▸
       at 1 2 (Toff413 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff314 ∷ []) (Toff413 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-2-4-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·3·1⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff314 ∷ []) (Toff413 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻0-2-4-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·2·3·1⟩ c4) ▸
       at 0 5 (Sb0-2-31-4 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;014): 8 steps
lem-nat-3-BOX⟨2·014⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-013 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·014⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-014 ∷ []) (Bx2-013 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 2 2 (Bx0-23 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·24⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx0-23 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·24⟩ c4) ▸
       at 0 6 (Bx2-013 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;2314): 8 steps
lem-nat-3-BOX⟨0·2314⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·2314⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-2314 ∷ []) (Bx0-2413 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 2 2 (Bx2-013 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·014⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx2-013 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·014⟩ c4) ▸
       at 0 6 (Bx0-2413 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;2;4;1): 3 steps
lem-nat-3-SBOX⟨0·2·4·1⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb0-2-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-3-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·2·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-2-4-1 ∷ []) (Sb0-2-3-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw34 ∷ []) (lem-nat-3-CS24 c4) ▸
       at 0 1 (Sb0-2-3-1 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;2;4;1): 3 steps
lem-nat-3-SBOXd⟨0·2·4·1⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻0-2-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-3-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·2·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-2-4-1 ∷ []) (Sb⁻0-2-3-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd24 c4) ▸
       at 0 1 (Sb⁻0-2-3-1 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;2;31;4): 7 steps
lem-nat-3-SBOX⟨0·2·31·4⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb0-2-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-41-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·2·31·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-2-31-4 ∷ []) (Sb0-2-41-3 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx0-2314 ∷ Toff413 ∷ Sb0-2-4-1 ∷ Toff413 ∷ Sb⁻0-2-4-1 ∷ []) (refl) ▸
       at 0 2 (Bx0-2413 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2314⟩ c4) ▸
       at 1 2 (Toff314 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff413 ∷ []) (Toff314 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-2-3-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·4·1⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff413 ∷ []) (Toff314 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻0-2-3-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·2·4·1⟩ c4) ▸
       at 0 5 (Sb0-2-41-3 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;103): 8 steps
lem-nat-0-BOX⟨2·103⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-013 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·103⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-103 ∷ []) (Bx2-013 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-23 ∷ Toff201 ∷ CCZ012 ∷ Bx1-23 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff201 ∷ []) (Toff201 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-23 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·23⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff201 ∷ []) (Toff201 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-23 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·23⟩ c4) ▸
       at 0 6 (Bx2-013 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;2403): 8 steps
lem-nat-0-BOX⟨1·2403⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·2403⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-2403 ∷ []) (Bx0-2413 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-103 ∷ Toff124 ∷ CCZ124 ∷ Bx2-103 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 2 2 (Bx2-013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·103⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx2-013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·103⟩ c4) ▸
       at 0 6 (Bx0-2413 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;2;3;0): 2 steps
lem-nat-0-SBOX⟨1·2·3·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·2·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-2-3-0 ∷ []) (Sb0-2-3-1 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb1-2-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) (CS)) ▸
       at 0 1 (Sb0-2-3-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(1;2;3;0): 2 steps
lem-nat-0-SBOXd⟨1·2·3·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·2·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻1-2-3-0 ∷ []) (Sb⁻0-2-3-1 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb⁻1-2-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) (CS • CS • CS)) ▸
       at 0 1 (Sb⁻0-2-3-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(1;2;40;3): 7 steps
lem-nat-0-SBOX⟨1·2·40·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-41-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·2·40·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-2-40-3 ∷ []) (Sb0-2-41-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx1-2403 ∷ Toff304 ∷ Sb1-2-3-0 ∷ Toff304 ∷ Sb⁻1-2-3-0 ∷ []) (refl) ▸
       at 0 2 (Bx0-2413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2403⟩ c4) ▸
       at 1 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 2 2 (Sb0-2-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·3·0⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 4 2 (Sb⁻0-2-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·2·3·0⟩ c4) ▸
       at 0 5 (Sb0-2-41-3 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;013): 8 steps
lem-nat-0-BOX⟨2·013⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-103 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·013⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-013 ∷ []) (Bx2-103 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff201 ∷ []) (Toff201 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-23 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·23⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff201 ∷ []) (Toff201 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-23 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·23⟩ c4) ▸
       at 0 6 (Bx2-103 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;2413): 8 steps
lem-nat-0-BOX⟨0·2413⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·2413⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-2413 ∷ []) (Bx1-2403 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 2 2 (Bx2-103 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·013⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx2-103 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·013⟩ c4) ▸
       at 0 6 (Bx1-2403 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;2;3;1): 2 steps
lem-nat-0-SBOX⟨0·2·3·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-3-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·2·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-2-3-1 ∷ []) (Sb1-2-3-0 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb0-2-3-1 ∷ Sw01 ∷ []) (c₂ (Swap) (CS)) ▸
       at 0 1 (Sb1-2-3-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(0;2;3;1): 2 steps
lem-nat-0-SBOXd⟨0·2·3·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-3-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·2·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻1-2-3-0 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb⁻0-2-3-1 ∷ Sw01 ∷ []) (c₂ (Swap) (CS • CS • CS)) ▸
       at 0 1 (Sb⁻1-2-3-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(0;2;41;3): 7 steps
lem-nat-0-SBOX⟨0·2·41·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb0-2-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-40-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·2·41·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-2-41-3 ∷ []) (Sb1-2-40-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx0-2413 ∷ Toff314 ∷ Sb0-2-3-1 ∷ Toff314 ∷ Sb⁻0-2-3-1 ∷ []) (refl) ▸
       at 0 2 (Bx1-2403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2413⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 2 2 (Sb1-2-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·3·1⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 4 2 (Sb⁻1-2-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·2·3·1⟩ c4) ▸
       at 0 5 (Sb1-2-40-3 ∷ []) (refl) ▸ done


-- comm CX20 CCZ134: 23 steps
lem-comm-CX20-CCZ134 : Complete 4 → ⟪ (CX20 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CX20 ∷ []) ⟫ʷ
lem-comm-CX20-CCZ134 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX20 ∷ CCZ134 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CCZ134 ∷ CX20 ∷ [])
  b2 = at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 3 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm SBOXd(0;1;2;3) TOFF304: 17 steps
lem-comm-SBOXd⟨0·1·2·3⟩-TOFF304 : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-comm-SBOXd⟨0·1·2·3⟩-TOFF304 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Toff304 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CS34⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff304 ∷ CS12⁻ ∷ [])
  b1 = at 4 2 (Toff102 ∷ CS34⁻ ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CS • CS • CS))) ▸
       at 5 2 (Sw23 ∷ CS24⁻ ∷ []) (lw0 c4 (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ CS13⁻ ∷ []) (lw4 c4 (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 9 (Toff304 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Toff304 ∷ CS12⁻ ∷ []) (Toff304 ∷ Sb⁻0-1-2-3 ∷ [])
  b2 = at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;1;4;2): 3 steps
lem-nat-0-SBOX⟨0·1·4·2⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-4-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-1-4-2 ∷ []) (Sb1-0-4-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 c4) ▸
       at 0 1 (Sb1-0-4-2 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(0;1;4;2): 3 steps
lem-nat-0-SBOXd⟨0·1·4·2⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-4-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·1·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻1-0-4-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw01 ∷ []) (lem-nat-0-CSd14 c4) ▸
       at 0 1 (Sb⁻1-0-4-2 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;1;32;4): 7 steps
lem-nat-0-SBOX⟨0·1·32·4⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-32-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·32·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-1-32-4 ∷ []) (Sb1-0-32-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 0 2 (Bx1-0324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (Sb1-0-4-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·4·2⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 4 2 (Sb⁻1-0-4-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 0 5 (Sb1-0-32-4 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;421): 8 steps
lem-nat-0-BOX⟨0·421⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-421 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-420 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·421⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-421 ∷ []) (Bx1-420 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 2 2 (Bx4-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·01⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx4-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·01⟩ c4) ▸
       at 0 6 (Bx1-420 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;0321): 8 steps
lem-nat-0-BOX⟨4·0321⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·0321⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-0321 ∷ []) (Bx4-1320 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-421 ∷ Toff403 ∷ CCZ034 ∷ Bx0-421 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 2 2 (Bx1-420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·421⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx1-420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·421⟩ c4) ▸
       at 0 6 (Bx4-1320 ∷ []) (refl) ▸ done


-- nat 0 SBOX(4;0;1;2): 3 steps
lem-nat-0-SBOX⟨4·0·1·2⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb4-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-0-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨4·0·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb4-0-1-2 ∷ []) (Sb4-1-0-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb4-1-0-2 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(4;0;1;2): 3 steps
lem-nat-0-SBOXd⟨4·0·1·2⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻4-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-1-0-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨4·0·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻4-0-1-2 ∷ []) (Sb⁻4-1-0-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 2 (CS01⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻4-1-0-2 ∷ []) (refl) ▸ done


-- nat 0 SBOX(4;0;32;1): 7 steps
lem-nat-0-SBOX⟨4·0·32·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb4-0-32-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-32-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨4·0·32·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb4-0-32-1 ∷ []) (Sb4-1-32-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx4-0321 ∷ Toff123 ∷ Sb4-0-1-2 ∷ Toff123 ∷ Sb⁻4-0-1-2 ∷ []) (refl) ▸
       at 0 2 (Bx4-1320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0321⟩ c4) ▸
       at 1 2 (Toff023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb4-1-0-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨4·0·1·2⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻4-1-0-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨4·0·1·2⟩ c4) ▸
       at 0 5 (Sb4-1-32-0 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;314): 8 steps
lem-nat-3-BOX⟨0·314⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-413 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·314⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-314 ∷ []) (Bx0-413 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 2 2 (Bx4-03 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·04⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx4-03 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·04⟩ c4) ▸
       at 0 6 (Bx0-413 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;0214): 8 steps
lem-nat-3-BOX⟨3·0214⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·0214⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-0214 ∷ []) (Bx4-0213 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff402 ∷ Sw34 ∷ []) (lem-nat-3-TOFF302 c4) ▸
       at 2 2 (Bx0-413 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·314⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw34 ∷ []) (lem-nat-3-TOFF302 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx0-413 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·314⟩ c4) ▸
       at 0 6 (Bx4-0213 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;03): 3 steps
lem-nat-1-BOX⟨4·03⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·03⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-03 ∷ []) (Bx4-03 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ03 ∷ []) (CZ03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx4-03 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;413): 8 steps
lem-nat-1-BOX⟨0·413⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-423 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·413⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-413 ∷ []) (Bx0-423 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 2 2 (Bx4-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·03⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx4-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·03⟩ c4) ▸
       at 0 6 (Bx0-423 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;0213): 8 steps
lem-nat-1-BOX⟨4·0213⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·0213⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-0213 ∷ []) (Bx4-0123 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-413 ∷ Toff402 ∷ CCZ024 ∷ Bx0-413 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 2 2 (Bx0-423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·413⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx0-423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·413⟩ c4) ▸
       at 0 6 (Bx4-0123 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;412): 8 steps
lem-nat-2-BOX⟨0·412⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-413 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·412⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-412 ∷ []) (Bx0-413 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 2 2 (Bx4-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·02⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx4-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·02⟩ c4) ▸
       at 0 6 (Bx0-413 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;0312): 8 steps
lem-nat-2-BOX⟨4·0312⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·0312⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-0312 ∷ []) (Bx4-0213 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-412 ∷ Toff403 ∷ CCZ034 ∷ Bx0-412 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 2 2 (Bx0-413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·412⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx0-413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·412⟩ c4) ▸
       at 0 6 (Bx4-0213 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;421): 8 steps
lem-nat-1-BOX⟨0·421⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-412 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·421⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-421 ∷ []) (Bx0-412 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 2 2 (Bx4-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·01⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx4-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·01⟩ c4) ▸
       at 0 6 (Bx0-412 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;0321): 8 steps
lem-nat-1-BOX⟨4·0321⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·0321⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-0321 ∷ []) (Bx4-0312 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-421 ∷ Toff403 ∷ CCZ034 ∷ Bx0-421 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 2 2 (Bx0-412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·421⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx0-412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·421⟩ c4) ▸
       at 0 6 (Bx4-0312 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;420): 8 steps
lem-nat-0-BOX⟨1·420⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-420 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-421 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·420⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-420 ∷ []) (Bx0-421 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 2 2 (Bx4-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·10⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx4-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·10⟩ c4) ▸
       at 0 6 (Bx0-421 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;1320): 8 steps
lem-nat-0-BOX⟨4·1320⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·1320⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-1320 ∷ []) (Bx4-0321 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx1-420 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 2 2 (Bx0-421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·420⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx0-421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·420⟩ c4) ▸
       at 0 6 (Bx4-0321 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;342): 8 steps
lem-nat-3-BOX⟨0·342⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-432 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·342⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-342 ∷ []) (Bx0-432 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw34 ∷ []) (lem-nat-3-TOFF034 c4) ▸
       at 2 2 (Bx4-02 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·02⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw34 ∷ []) (lem-nat-3-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 5 2 (Bx4-02 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·02⟩ c4) ▸
       at 0 6 (Bx0-432 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;0142): 8 steps
lem-nat-3-BOX⟨3·0142⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0132 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·0142⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-0142 ∷ []) (Bx4-0132 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 2 2 (Bx0-432 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·342⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx0-432 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·342⟩ c4) ▸
       at 0 6 (Bx4-0132 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;423): 8 steps
lem-nat-1-BOX⟨0·423⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-413 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·423⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-423 ∷ []) (Bx0-413 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 2 2 (Bx4-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·03⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx4-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·03⟩ c4) ▸
       at 0 6 (Bx0-413 ∷ []) (refl) ▸ done


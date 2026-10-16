{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R024 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-CCZ024 ; lem-nat-2-CCZ013 ; lem-nat-2-TOFF301 ; lem-nat-3-CCZ014 ; lem-nat-3-CZ13 ; lem-nat-3-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013 ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-1-TOFF103 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF204 ; lem-nat-3-TOFF203)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034 ; lem-nat-0-TOFF304 ; lem-nat-0-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-1-BOX⟨0·1234⟩ ; lem-nat-3-TOFF302)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-TOFF214 ; lem-nat-1-TOFF304 ; lem-nat-2-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-TOFF413)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-0-BOX⟨0·2134⟩ ; lem-nat-0-BOX⟨1·2034⟩ ; lem-nat-2-CZ12 ; lem-nat-3-CZ24)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-1-BOX⟨2·41⟩ ; lem-nat-2-CS12 ; lem-nat-2-CSd12 ; lem-nat-3-CS13 ; lem-nat-3-CSd13)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-BOX⟨2·1403⟩ ; lem-nat-3-CS24)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-1-TOFF402 ; lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R022 using (lem-nat-1-BOX⟨1·23⟩)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-1-BOX⟨1·203⟩ ; lem-nat-2-TOFF134)
-- nat 1 BOX(2;1403): 8 steps
lem-nat-1-BOX⟨2·1403⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·1403⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-1403 ∷ []) (Bx1-2403 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-203 ∷ Toff214 ∷ CCZ124 ∷ Bx1-203 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff214 ∷ []) (Toff124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-103 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·203⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff214 ∷ []) (Toff124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-103 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·203⟩ c4) ▸
       at 0 6 (Bx1-2403 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;103): 8 steps
lem-nat-1-BOX⟨2·103⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-203 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·103⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-103 ∷ []) (Bx1-203 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-23 ∷ Toff201 ∷ CCZ012 ∷ Bx1-23 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·23⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·23⟩ c4) ▸
       at 0 6 (Bx1-203 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;2403): 8 steps
lem-nat-1-BOX⟨1·2403⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·2403⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-2403 ∷ []) (Bx2-1403 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-103 ∷ Toff124 ∷ CCZ124 ∷ Bx2-103 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff214 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-203 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·103⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-203 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·103⟩ c4) ▸
       at 0 6 (Bx2-1403 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;2;4;3): 2 steps
lem-nat-0-SBOX⟨0·2·4·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb0-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-4-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·2·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-2-4-3 ∷ []) (Sb1-2-4-3 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb0-2-4-3 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 0 1 (Sb1-2-4-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(0;2;4;3): 2 steps
lem-nat-0-SBOXd⟨0·2·4·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻0-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-4-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·2·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-2-4-3 ∷ []) (Sb⁻1-2-4-3 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb⁻0-2-4-3 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 0 1 (Sb⁻1-2-4-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(0;2;13;4): 7 steps
lem-nat-0-SBOX⟨0·2·13·4⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb0-2-13-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-03-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·2·13·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-2-13-4 ∷ []) (Sb1-2-03-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx0-2134 ∷ Toff413 ∷ Sb0-2-4-3 ∷ Toff413 ∷ Sb⁻0-2-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 2 2 (Sb1-2-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·4·3⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 4 2 (Sb⁻1-2-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·2·4·3⟩ c4) ▸
       at 0 5 (Sb1-2-03-4 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;2;4;3): 2 steps
lem-nat-0-SBOX⟨1·2·4·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb1-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-4-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·2·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-2-4-3 ∷ []) (Sb0-2-4-3 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb1-2-4-3 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 0 1 (Sb0-2-4-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(1;2;4;3): 2 steps
lem-nat-0-SBOXd⟨1·2·4·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻1-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-4-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·2·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻1-2-4-3 ∷ []) (Sb⁻0-2-4-3 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb⁻1-2-4-3 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 0 1 (Sb⁻0-2-4-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(1;2;03;4): 7 steps
lem-nat-0-SBOX⟨1·2·03·4⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb1-2-03-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-13-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·2·03·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-2-03-4 ∷ []) (Sb0-2-13-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ Sb⁻1-2-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 2 2 (Sb0-2-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·4·3⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 4 2 (Sb⁻0-2-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·2·4·3⟩ c4) ▸
       at 0 5 (Sb0-2-13-4 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;1;4;3): 3 steps
lem-nat-1-SBOX⟨0·1·4·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-4-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·1·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-1-4-3 ∷ []) (Sb0-2-4-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-2-4-3 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(0;1;4;3): 3 steps
lem-nat-1-SBOXd⟨0·1·4·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-4-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·1·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-2-4-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-2-4-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;1;23;4): 7 steps
lem-nat-1-SBOX⟨0·1·23·4⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-13-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·1·23·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-1-23-4 ∷ []) (Sb0-2-13-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-2-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·4·3⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻0-2-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 0 5 (Sb0-2-13-4 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;2;4;3): 3 steps
lem-nat-1-SBOX⟨0·2·4·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb0-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·2·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-2-4-3 ∷ []) (Sb0-1-4-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(0;2;4;3): 3 steps
lem-nat-1-SBOXd⟨0·2·4·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻0-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·2·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-2-4-3 ∷ []) (Sb⁻0-1-4-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24⁻ ∷ []) (CS14⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;2;13;4): 7 steps
lem-nat-1-SBOX⟨0·2·13·4⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb0-2-13-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·2·13·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-2-13-4 ∷ []) (Sb0-1-23-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx0-2134 ∷ Toff413 ∷ Sb0-2-4-3 ∷ Toff413 ∷ Sb⁻0-2-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-1-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·4·3⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻0-1-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·4·3⟩ c4) ▸
       at 0 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;1;3;0): 3 steps
lem-nat-0-SBOX⟨2·1·3·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·1·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-1-3-0 ∷ []) (Sb2-0-3-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS13 ∷ []) (CS03 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;1;3;0): 3 steps
lem-nat-0-SBOXd⟨2·1·3·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·1·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-1-3-0 ∷ []) (Sb⁻2-0-3-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS13⁻ ∷ []) (CS03⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;1;40;3): 7 steps
lem-nat-0-SBOX⟨2·1·40·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·1·40·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-1-40-3 ∷ []) (Sb2-0-41-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx2-1403 ∷ Toff304 ∷ Sb2-1-3-0 ∷ Toff304 ∷ Sb⁻2-1-3-0 ∷ []) (refl) ▸
       at 0 2 (Bx2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1403⟩ c4) ▸
       at 1 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 2 2 (Sb2-0-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·3·0⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 4 2 (Sb⁻2-0-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·1·3·0⟩ c4) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;02): 3 steps
lem-nat-0-BOX⟨3·02⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-12 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·02⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-02 ∷ []) (Bx3-12 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ02 ∷ []) (CZ12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx3-12 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;312): 8 steps
lem-nat-0-BOX⟨0·312⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-302 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·312⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-312 ∷ []) (Bx1-302 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-12 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·02⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-12 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·02⟩ c4) ▸
       at 0 6 (Bx1-302 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;0412): 8 steps
lem-nat-0-BOX⟨3·0412⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·0412⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-0412 ∷ []) (Bx3-1402 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 2 2 (Bx1-302 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·312⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx1-302 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·312⟩ c4) ▸
       at 0 6 (Bx3-1402 ∷ []) (refl) ▸ done


-- nat 0 SBOX(3;0;2;1): 3 steps
lem-nat-0-SBOX⟨3·0·2·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-2-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb3-0-2-1 ∷ []) (Sb3-1-2-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb3-1-2-0 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(3;0;2;1): 3 steps
lem-nat-0-SBOXd⟨3·0·2·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-1-2-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨3·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻3-0-2-1 ∷ []) (Sb⁻3-1-2-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻3-1-2-0 ∷ []) (refl) ▸ done


-- nat 0 SBOX(3;0;41;2): 7 steps
lem-nat-0-SBOX⟨3·0·41·2⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-40-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·0·41·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb3-0-41-2 ∷ []) (Sb3-1-40-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 0 2 (Bx3-1402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0412⟩ c4) ▸
       at 1 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 2 2 (Sb3-1-2-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·2·1⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 4 2 (Sb⁻3-1-2-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨3·0·2·1⟩ c4) ▸
       at 0 5 (Sb3-1-40-2 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;2;3;0): 3 steps
lem-nat-1-SBOX⟨1·2·3·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·2·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-2-3-0 ∷ []) (Sb2-1-3-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb2-1-3-0 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;2;3;0): 3 steps
lem-nat-1-SBOXd⟨1·2·3·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·2·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-2-3-0 ∷ []) (Sb⁻2-1-3-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS23⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻2-1-3-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;2;40;3): 7 steps
lem-nat-1-SBOX⟨1·2·40·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-40-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·2·40·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-2-40-3 ∷ []) (Sb2-1-40-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx1-2403 ∷ Toff304 ∷ Sb1-2-3-0 ∷ Toff304 ∷ Sb⁻1-2-3-0 ∷ []) (refl) ▸
       at 0 2 (Bx2-1403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2403⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 2 2 (Sb2-1-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·3·0⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 4 2 (Sb⁻2-1-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·2·3·0⟩ c4) ▸
       at 0 5 (Sb2-1-40-3 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;12): 3 steps
lem-nat-1-BOX⟨3·12⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-21 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·12⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-12 ∷ []) (Bx3-21 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ12 ∷ []) (CZ12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx3-21 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;302): 8 steps
lem-nat-1-BOX⟨1·302⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-302 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-301 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·302⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-302 ∷ []) (Bx2-301 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 2 2 (Bx3-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·12⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx3-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·12⟩ c4) ▸
       at 0 6 (Bx2-301 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;1402): 8 steps
lem-nat-1-BOX⟨3·1402⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·1402⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-1402 ∷ []) (Bx3-2401 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-302 ∷ Toff314 ∷ CCZ134 ∷ Bx1-302 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-301 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·302⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-301 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·302⟩ c4) ▸
       at 0 6 (Bx3-2401 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;1;2;0): 3 steps
lem-nat-1-SBOX⟨3·1·2·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb3-1-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-2-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·1·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-1-2-0 ∷ []) (Sb3-2-1-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS12 ∷ []) (CS12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb3-2-1-0 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(3;1;2;0): 3 steps
lem-nat-1-SBOXd⟨3·1·2·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻3-1-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-2-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·1·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻3-1-2-0 ∷ []) (Sb⁻3-2-1-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻3-2-1-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;1;40;2): 7 steps
lem-nat-1-SBOX⟨3·1·40·2⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb3-1-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-2-40-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·1·40·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-1-40-2 ∷ []) (Sb3-2-40-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx3-1402 ∷ Toff204 ∷ Sb3-1-2-0 ∷ Toff204 ∷ Sb⁻3-1-2-0 ∷ []) (refl) ▸
       at 0 2 (Bx3-2401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1402⟩ c4) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 2 2 (Sb3-2-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·1·2·0⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 4 2 (Sb⁻3-2-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·1·2·0⟩ c4) ▸
       at 0 5 (Sb3-2-40-1 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;32): 3 steps
lem-nat-2-BOX⟨1·32⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-23 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·32⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-32 ∷ []) (Bx1-23 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CZ23 ∷ []) (CZ23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx1-23 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;102): 8 steps
lem-nat-2-BOX⟨3·102⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-103 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·102⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-102 ∷ []) (Bx2-103 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-32 ∷ Toff301 ∷ CCZ013 ∷ Bx1-32 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 2 2 (Bx1-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·32⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx1-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·32⟩ c4) ▸
       at 0 6 (Bx2-103 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;3402): 8 steps
lem-nat-2-BOX⟨1·3402⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·3402⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-3402 ∷ []) (Bx1-2403 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-102 ∷ Toff134 ∷ CCZ134 ∷ Bx3-102 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 2 2 (Bx2-103 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·102⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx2-103 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·102⟩ c4) ▸
       at 0 6 (Bx1-2403 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;3;2;0): 3 steps
lem-nat-2-SBOX⟨1·3·2·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb1-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·3·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-3-2-0 ∷ []) (Sb1-2-3-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CS23 ∷ []) (CS23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb1-2-3-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;3;2;0): 3 steps
lem-nat-2-SBOXd⟨1·3·2·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻1-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·3·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-3-2-0 ∷ []) (Sb⁻1-2-3-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS23⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻1-2-3-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;3;40;2): 7 steps
lem-nat-2-SBOX⟨1·3·40·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-40-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·3·40·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-3-40-2 ∷ []) (Sb1-2-40-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx1-3402 ∷ Toff204 ∷ Sb1-3-2-0 ∷ Toff204 ∷ Sb⁻1-3-2-0 ∷ []) (refl) ▸
       at 0 2 (Bx1-2403 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·3402⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 2 2 (Sb1-2-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·2·0⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 4 2 (Sb⁻1-2-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·3·2·0⟩ c4) ▸
       at 0 5 (Sb1-2-40-3 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;21): 3 steps
lem-nat-2-BOX⟨3·21⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-31 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·21⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-21 ∷ []) (Bx2-31 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw23 ∷ []) (lem-nat-2-CZ12 c4) ▸
       at 0 1 (Bx2-31 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;301): 8 steps
lem-nat-2-BOX⟨2·301⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-301 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-201 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·301⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-301 ∷ []) (Bx3-201 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff302 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-31 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·21⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-31 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·21⟩ c4) ▸
       at 0 6 (Bx3-201 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;2401): 8 steps
lem-nat-2-BOX⟨3·2401⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·2401⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-2401 ∷ []) (Bx2-3401 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-301 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-201 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·301⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-201 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·301⟩ c4) ▸
       at 0 6 (Bx2-3401 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;2;1;0): 3 steps
lem-nat-2-SBOX⟨3·2·1·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb3-2-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-1-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·2·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-2-1-0 ∷ []) (Sb2-3-1-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4) ▸
       at 0 1 (Sb2-3-1-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(3;2;1;0): 3 steps
lem-nat-2-SBOXd⟨3·2·1·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻3-2-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-1-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·2·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻3-2-1-0 ∷ []) (Sb⁻2-3-1-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4) ▸
       at 0 1 (Sb⁻2-3-1-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;2;40;1): 7 steps
lem-nat-2-SBOX⟨3·2·40·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb3-2-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-40-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·2·40·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-2-40-1 ∷ []) (Sb2-3-40-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx3-2401 ∷ Toff104 ∷ Sb3-2-1-0 ∷ Toff104 ∷ Sb⁻3-2-1-0 ∷ []) (refl) ▸
       at 0 2 (Bx2-3401 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·2401⟩ c4) ▸
       at 1 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 2 2 (Sb2-3-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·2·1·0⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 4 2 (Sb⁻2-3-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·2·1·0⟩ c4) ▸
       at 0 5 (Sb2-3-40-1 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;42): 3 steps
lem-nat-3-BOX⟨1·42⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-32 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·42⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-42 ∷ []) (Bx1-32 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw34 ∷ []) (lem-nat-3-CZ24 c4) ▸
       at 0 1 (Bx1-32 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;102): 8 steps
lem-nat-3-BOX⟨4·102⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx4-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-102 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·102⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-102 ∷ []) (Bx3-102 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-42 ∷ Toff401 ∷ CCZ014 ∷ Bx1-42 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 1 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 2 2 (Bx1-32 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·42⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 4 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 5 2 (Bx1-32 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·42⟩ c4) ▸
       at 0 6 (Bx3-102 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;4302): 8 steps
lem-nat-3-BOX⟨1·4302⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-4302 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·4302⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-4302 ∷ []) (Bx1-3402 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-102 ∷ Toff134 ∷ CCZ134 ∷ Bx4-102 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-102 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·102⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-102 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·102⟩ c4) ▸
       at 0 6 (Bx1-3402 ∷ []) (refl) ▸ done


-- nat 3 SBOX(1;4;2;0): 3 steps
lem-nat-3-SBOX⟨1·4·2·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb1-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-2-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·4·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb1-4-2-0 ∷ []) (Sb1-3-2-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw34 ∷ []) (lem-nat-3-CS24 c4) ▸
       at 0 1 (Sb1-3-2-0 ∷ []) (refl) ▸ done


-- nat 3 CSd24: 2 steps
lem-nat-3-CSd24 : Complete 4 → ⟪ (Sw34 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CSd24 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CS24⁻ ∷ []) (CS23⁻ ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 3 SBOXd(1;4;2;0): 3 steps
lem-nat-3-SBOXd⟨1·4·2·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻1-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-2-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·4·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-4-2-0 ∷ []) (Sb⁻1-3-2-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd24 c4) ▸
       at 0 1 (Sb⁻1-3-2-0 ∷ []) (refl) ▸ done


-- nat 3 SBOX(1;4;30;2): 7 steps
lem-nat-3-SBOX⟨1·4·30·2⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb1-4-30-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-40-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·4·30·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb1-4-30-2 ∷ []) (Sb1-3-40-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx1-4302 ∷ Toff203 ∷ Sb1-4-2-0 ∷ Toff203 ∷ Sb⁻1-4-2-0 ∷ []) (refl) ▸
       at 0 2 (Bx1-3402 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·4302⟩ c4) ▸
       at 1 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 2 2 (Sb1-3-2-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·4·2·0⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 4 2 (Sb⁻1-3-2-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·4·2·0⟩ c4) ▸
       at 0 5 (Sb1-3-40-2 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;31): 3 steps
lem-nat-3-BOX⟨2·31⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-41 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·31⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-31 ∷ []) (Bx2-41 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw34 ∷ []) (lem-nat-3-CZ13 c4) ▸
       at 0 1 (Bx2-41 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;201): 8 steps
lem-nat-3-BOX⟨3·201⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx3-201 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-201 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·201⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-201 ∷ []) (Bx4-201 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff402 ∷ Sw34 ∷ []) (lem-nat-3-TOFF302 c4) ▸
       at 2 2 (Bx2-41 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·31⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw34 ∷ []) (lem-nat-3-TOFF302 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx2-41 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·31⟩ c4) ▸
       at 0 6 (Bx4-201 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;3401): 8 steps
lem-nat-3-BOX⟨2·3401⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·3401⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-3401 ∷ []) (Bx2-4301 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-201 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·201⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-201 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·201⟩ c4) ▸
       at 0 6 (Bx2-4301 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;3;1;0): 3 steps
lem-nat-3-SBOX⟨2·3·1·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb2-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-1-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·3·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-3-1-0 ∷ []) (Sb2-4-1-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw34 ∷ []) (lem-nat-3-CS13 c4) ▸
       at 0 1 (Sb2-4-1-0 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(2;3;1;0): 3 steps
lem-nat-3-SBOXd⟨2·3·1·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻2-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-1-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·3·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-3-1-0 ∷ []) (Sb⁻2-4-1-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd13 c4) ▸
       at 0 1 (Sb⁻2-4-1-0 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;3;40;1): 7 steps
lem-nat-3-SBOX⟨2·3·40·1⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb2-3-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-30-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·3·40·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-3-40-1 ∷ []) (Sb2-4-30-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx2-3401 ∷ Toff104 ∷ Sb2-3-1-0 ∷ Toff104 ∷ Sb⁻2-3-1-0 ∷ []) (refl) ▸
       at 0 2 (Bx2-4301 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·3401⟩ c4) ▸
       at 1 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 2 2 (Sb2-4-1-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·3·1·0⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 4 2 (Sb⁻2-4-1-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·3·1·0⟩ c4) ▸
       at 0 5 (Sb2-4-30-1 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;201): 8 steps
lem-nat-1-BOX⟨4·201⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-201 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-102 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·201⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-201 ∷ []) (Bx4-102 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 2 2 (Bx1-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·41⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx1-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·41⟩ c4) ▸
       at 0 6 (Bx4-102 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;4301): 8 steps
lem-nat-1-BOX⟨2·4301⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4302 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·4301⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-4301 ∷ []) (Bx1-4302 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·201⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·201⟩ c4) ▸
       at 0 6 (Bx1-4302 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;4;1;0): 3 steps
lem-nat-1-SBOX⟨2·4·1·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb2-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·4·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-4-1-0 ∷ []) (Sb1-4-2-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb1-4-2-0 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;4;1;0): 3 steps
lem-nat-1-SBOXd⟨2·4·1·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻2-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·4·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-4-1-0 ∷ []) (Sb⁻1-4-2-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻1-4-2-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;4;30;1): 7 steps
lem-nat-1-SBOX⟨2·4·30·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb2-4-30-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-30-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·4·30·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-4-30-1 ∷ []) (Sb1-4-30-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx2-4301 ∷ Toff103 ∷ Sb2-4-1-0 ∷ Toff103 ∷ Sb⁻2-4-1-0 ∷ []) (refl) ▸
       at 0 2 (Bx1-4302 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4301⟩ c4) ▸
       at 1 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 2 2 (Sb1-4-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·4·1·0⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 4 2 (Sb⁻1-4-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·4·1·0⟩ c4) ▸
       at 0 5 (Sb1-4-30-2 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;41): 3 steps
lem-nat-2-BOX⟨3·41⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-41 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·41⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-41 ∷ []) (Bx2-41 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ14 ∷ []) (CZ14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx2-41 ∷ []) (refl) ▸ done


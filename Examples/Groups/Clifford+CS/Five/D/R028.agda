{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R028 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF103 ; lem-nat-2-TOFF301 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-3-CZ14)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-1-TOFF301 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF204 ; lem-nat-2-TOFF304 ; lem-nat-3-TOFF203)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-3-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨3·4102⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-TOFF204 ; lem-nat-2-BOX⟨2·41⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-1-BOX⟨3·41⟩ ; lem-nat-1-BOX⟨3·42⟩ ; lem-nat-1-TOFF304)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨3·4012⟩ ; lem-nat-2-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-TOFF023 ; lem-nat-2-CZ02 ; lem-nat-3-TOFF103)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-CCZ014 ; lem-nat-3-CZ24)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-1-BOXd⟨2·43⟩ ; lem-nat-3-CS14 ; lem-nat-3-CSd14)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-2-TOFF124)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-1-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-1-TOFF402 ; lem-nat-2-BOX⟨1·04⟩ ; lem-nat-2-TOFF401 ; lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-1-BOX⟨3·01⟩ ; lem-nat-2-BOX⟨2·01⟩ ; lem-nat-2-TOFF134)
open import Examples.Groups.Clifford+CS.Five.D.R024 using (lem-nat-1-SBOX⟨1·2·3·0⟩ ; lem-nat-1-SBOXd⟨1·2·3·0⟩ ; lem-nat-2-SBOX⟨1·3·2·0⟩ ; lem-nat-2-SBOXd⟨1·3·2·0⟩ ; lem-nat-3-SBOX⟨1·4·2·0⟩ ; lem-nat-3-SBOXd⟨1·4·2·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R025 using (lem-nat-3-BOX⟨1·03⟩ ; lem-nat-3-BOX⟨1·04⟩)
open import Examples.Groups.Clifford+CS.Five.D.R026 using (lem-nat-0-SBOX⟨2·4·3·1⟩ ; lem-nat-0-SBOXd⟨2·4·3·1⟩ ; lem-nat-1-SBOX⟨2·4·3·0⟩ ; lem-nat-1-SBOXd⟨2·4·3·0⟩ ; lem-nat-2-SBOX⟨1·4·3·0⟩ ; lem-nat-2-SBOXd⟨1·4·3·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R027 using (lem-nat-0-BOXd⟨4·213⟩)
-- nat 0 BOXd(2;4013): 8 steps
lem-nat-0-BOXd⟨2·4013⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-4103 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·4013⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻2-4013 ∷ []) (Bx⁻2-4103 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻4-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻4-213 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-203 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·213⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 2 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 3 2 (Bx⁻4-203 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·213⟩ c4) ▸
       at 4 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 5 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 0 6 (Bx⁻2-4103 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;4;01;3): 7 steps
lem-nat-0-SBOXd⟨2·4·01·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-10-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·4·01·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-4-01-3 ∷ []) (Sb⁻2-4-10-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ Toff301 ∷ Bx⁻2-4013 ∷ []) (refl) ▸
       at 0 2 (Sb2-4-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·4·3·1⟩ c4) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻2-4-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·4·3·1⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻2-4103 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·4013⟩ c4) ▸
       at 0 5 (Sb⁻2-4-10-3 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;23): 3 steps
lem-nat-1-BOXd⟨1·23⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻1-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-13 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·23⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-23 ∷ []) (Bx⁻2-13 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ23 ∷ []) (CZ13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻2-13 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;103): 8 steps
lem-nat-1-BOXd⟨2·103⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻2-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-203 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·103⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-103 ∷ []) (Bx⁻1-203 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻1-23 ∷ CCZ012 ∷ Toff201 ∷ Bx⁻1-23 ∷ Toff201 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-13 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·23⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻2-13 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·23⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻1-203 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;2403): 8 steps
lem-nat-1-BOXd⟨1·2403⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-1403 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·2403⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-2403 ∷ []) (Bx⁻2-1403 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻2-103 ∷ CCZ124 ∷ Toff124 ∷ Bx⁻2-103 ∷ Toff124 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-203 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·103⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff214 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻1-203 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·103⟩ c4) ▸
       at 4 2 (Toff214 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻2-1403 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;2;40;3): 7 steps
lem-nat-1-SBOXd⟨1·2·40·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-40-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·2·40·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-2-40-3 ∷ []) (Sb⁻2-1-40-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb1-2-3-0 ∷ Toff304 ∷ Sb⁻1-2-3-0 ∷ Toff304 ∷ Bx⁻1-2403 ∷ []) (refl) ▸
       at 0 2 (Sb2-1-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·3·0⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 2 2 (Sb⁻2-1-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·2·3·0⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 4 2 (Bx⁻2-1403 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·2403⟩ c4) ▸
       at 0 5 (Sb⁻2-1-40-3 ∷ []) (refl) ▸ done


-- nat 1 BOXd(4;203): 8 steps
lem-nat-1-BOXd⟨4·203⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻4-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-103 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·203⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻4-203 ∷ []) (Bx⁻4-103 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻2-43 ∷ CCZ024 ∷ Toff402 ∷ Bx⁻2-43 ∷ Toff402 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-43 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·43⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 3 2 (Bx⁻1-43 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·43⟩ c4) ▸
       at 4 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 5 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 0 6 (Bx⁻4-103 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;4103): 8 steps
lem-nat-1-BOXd⟨2·4103⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-4203 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·4103⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-4103 ∷ []) (Bx⁻1-4203 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻4-203 ∷ CCZ124 ∷ Toff214 ∷ Bx⁻4-203 ∷ Toff214 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-103 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·203⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff214 ∷ []) (Toff124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻4-103 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·203⟩ c4) ▸
       at 4 2 (Toff124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff214 ∷ []) (Toff124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻1-4203 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;4;10;3): 7 steps
lem-nat-1-SBOXd⟨2·4·10·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻2-4-10-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-20-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·4·10·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-4-10-3 ∷ []) (Sb⁻1-4-20-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb2-4-3-0 ∷ Toff301 ∷ Sb⁻2-4-3-0 ∷ Toff301 ∷ Bx⁻2-4103 ∷ []) (refl) ▸
       at 0 2 (Sb1-4-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·4·3·0⟩ c4) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 2 2 (Sb⁻1-4-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·4·3·0⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 4 2 (Bx⁻1-4203 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·4103⟩ c4) ▸
       at 0 5 (Sb⁻1-4-20-3 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;32): 3 steps
lem-nat-2-BOXd⟨1·32⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-23 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·32⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-32 ∷ []) (Bx⁻1-23 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CZ23 ∷ []) (CZ23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻1-23 ∷ []) (refl) ▸ done


-- nat 2 BOXd(3;102): 8 steps
lem-nat-2-BOXd⟨3·102⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻3-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-103 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨3·102⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻3-102 ∷ []) (Bx⁻2-103 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-32 ∷ CCZ013 ∷ Toff301 ∷ Bx⁻1-32 ∷ Toff301 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-23 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·32⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 3 2 (Bx⁻1-23 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·32⟩ c4) ▸
       at 4 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 5 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 0 6 (Bx⁻2-103 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;3402): 8 steps
lem-nat-2-BOXd⟨1·3402⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-2403 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·3402⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-3402 ∷ []) (Bx⁻1-2403 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻3-102 ∷ CCZ134 ∷ Toff134 ∷ Bx⁻3-102 ∷ Toff134 ∷ CCZ134 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-103 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·102⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 2 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 3 2 (Bx⁻2-103 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·102⟩ c4) ▸
       at 4 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 5 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 0 6 (Bx⁻1-2403 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;3;40;2): 7 steps
lem-nat-2-SBOXd⟨1·3·40·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-40-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·3·40·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-3-40-2 ∷ []) (Sb⁻1-2-40-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb1-3-2-0 ∷ Toff204 ∷ Sb⁻1-3-2-0 ∷ Toff204 ∷ Bx⁻1-3402 ∷ []) (refl) ▸
       at 0 2 (Sb1-2-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·2·0⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 2 2 (Sb⁻1-2-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·3·2·0⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 4 2 (Bx⁻1-2403 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·3402⟩ c4) ▸
       at 0 5 (Sb⁻1-2-40-3 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;43): 3 steps
lem-nat-2-BOXd⟨1·43⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-42 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·43⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-43 ∷ []) (Bx⁻1-42 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ34 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ34 ∷ []) (CZ24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻1-42 ∷ []) (refl) ▸ done


-- nat 2 BOXd(4;103): 8 steps
lem-nat-2-BOXd⟨4·103⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻4-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-102 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨4·103⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻4-103 ∷ []) (Bx⁻4-102 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-43 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻1-43 ∷ Toff401 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-42 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·43⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 3 2 (Bx⁻1-42 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·43⟩ c4) ▸
       at 4 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 5 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 0 6 (Bx⁻4-102 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;4203): 8 steps
lem-nat-2-BOXd⟨1·4203⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-4203 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-4302 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·4203⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-4203 ∷ []) (Bx⁻1-4302 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻4-103 ∷ CCZ124 ∷ Toff124 ∷ Bx⁻4-103 ∷ Toff124 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-102 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·103⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 2 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 3 2 (Bx⁻4-102 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·103⟩ c4) ▸
       at 4 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 5 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 0 6 (Bx⁻1-4302 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;4;20;3): 7 steps
lem-nat-2-SBOXd⟨1·4·20·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-30-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·4·20·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-4-20-3 ∷ []) (Sb⁻1-4-30-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb1-4-3-0 ∷ Toff302 ∷ Sb⁻1-4-3-0 ∷ Toff302 ∷ Bx⁻1-4203 ∷ []) (refl) ▸
       at 0 2 (Sb1-4-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·4·3·0⟩ c4) ▸
       at 1 2 (Toff203 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻1-4-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·4·3·0⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻1-4302 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·4203⟩ c4) ▸
       at 0 5 (Sb⁻1-4-30-2 ∷ []) (refl) ▸ done


-- nat 3 BOXd(1;42): 3 steps
lem-nat-3-BOXd⟨1·42⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻1-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-32 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·42⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻1-42 ∷ []) (Bx⁻1-32 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw34 ∷ []) (lem-nat-3-CZ24 c4) ▸
       at 0 1 (Bx⁻1-32 ∷ []) (refl) ▸ done


-- nat 3 BOXd(4;102): 8 steps
lem-nat-3-BOXd⟨4·102⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻4-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-102 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨4·102⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻4-102 ∷ []) (Bx⁻3-102 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻1-42 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻1-42 ∷ Toff401 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-32 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·42⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 3 2 (Bx⁻1-32 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·42⟩ c4) ▸
       at 4 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 5 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 0 6 (Bx⁻3-102 ∷ []) (refl) ▸ done


-- nat 3 BOXd(1;4302): 8 steps
lem-nat-3-BOXd⟨1·4302⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻1-4302 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-3402 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·4302⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻1-4302 ∷ []) (Bx⁻1-3402 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻4-102 ∷ CCZ134 ∷ Toff134 ∷ Bx⁻4-102 ∷ Toff134 ∷ CCZ134 ∷ []) (refl) ▸
       at 0 2 (Bx⁻3-102 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·102⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻3-102 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·102⟩ c4) ▸
       at 4 2 (Toff134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻1-3402 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(1;4;30;2): 7 steps
lem-nat-3-SBOXd⟨1·4·30·2⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻1-4-30-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-40-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·4·30·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-4-30-2 ∷ []) (Sb⁻1-3-40-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sb1-4-2-0 ∷ Toff203 ∷ Sb⁻1-4-2-0 ∷ Toff203 ∷ Bx⁻1-4302 ∷ []) (refl) ▸
       at 0 2 (Sb1-3-2-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·4·2·0⟩ c4) ▸
       at 1 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 2 2 (Sb⁻1-3-2-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·4·2·0⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 4 2 (Bx⁻1-3402 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·4302⟩ c4) ▸
       at 0 5 (Sb⁻1-3-40-2 ∷ []) (refl) ▸ done


-- nat 2 BOXd(3;02): 3 steps
lem-nat-2-BOXd⟨3·02⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻3-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-03 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨3·02⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻3-02 ∷ []) (Bx⁻2-03 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4) ▸
       at 0 1 (Bx⁻2-03 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;312): 8 steps
lem-nat-2-BOXd⟨0·312⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻0-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-213 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·312⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-312 ∷ []) (Bx⁻0-213 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻3-02 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻3-02 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-03 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·02⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 3 2 (Bx⁻2-03 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·02⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 5 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 0 6 (Bx⁻0-213 ∷ []) (refl) ▸ done


-- nat 2 BOXd(3;0412): 8 steps
lem-nat-2-BOXd⟨3·0412⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0413 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨3·0412⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻3-0412 ∷ []) (Bx⁻2-0413 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-312 ∷ CCZ034 ∷ Toff304 ∷ Bx⁻0-312 ∷ Toff304 ∷ CCZ034 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-213 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·312⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 2 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 3 2 (Bx⁻0-213 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·312⟩ c4) ▸
       at 4 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 5 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 0 6 (Bx⁻2-0413 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;231): 8 steps
lem-nat-2-BOX⟨0·231⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-321 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·231⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-231 ∷ []) (Bx0-321 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-01 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·01⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-01 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·01⟩ c4) ▸
       at 0 6 (Bx0-321 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;0431): 8 steps
lem-nat-2-BOX⟨2·0431⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·0431⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-0431 ∷ []) (Bx3-0421 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 2 2 (Bx0-321 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·231⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx0-321 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·231⟩ c4) ▸
       at 0 6 (Bx3-0421 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;321): 8 steps
lem-nat-1-BOX⟨0·321⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-312 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·321⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-321 ∷ []) (Bx0-312 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 2 2 (Bx3-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·01⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx3-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·01⟩ c4) ▸
       at 0 6 (Bx0-312 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;0421): 8 steps
lem-nat-1-BOX⟨3·0421⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·0421⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-0421 ∷ []) (Bx3-0412 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 2 2 (Bx0-312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·321⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx0-312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·321⟩ c4) ▸
       at 0 6 (Bx3-0412 ∷ []) (refl) ▸ done


-- resp CX41 at 3: 6 steps
lem-resp-CX41-at-3 : Complete 4 → ⟪ (CX41 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX42 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX41-at-3 c4 = run b0
  where
  b0 : Chain (CX41 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX42 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw23 ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ Sw23 ∷ []) (Sw23 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw12 ∷ CX42 ∷ []) (lw0 c4 (CX41 ∷ Sw12 ∷ []) (Sw12 ∷ CX42 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ CX42 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CX₁₀ • Swap ↑))) ▸ done


-- resp CX30 at 2: 4 steps
lem-resp-CX30-at-2 : Complete 4 → ⟪ (CX30 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX31 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX30-at-2 c4 = run b0
  where
  b0 : Chain (CX30 ∷ []) (Sw12 ∷ Sw01 ∷ CX31 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw12 ∷ CX30 ∷ []) (lw4 c4 (CX30 ∷ Sw12 ∷ []) (Sw12 ∷ CX30 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CX31 ∷ []) (lw4 c4 (CX30 ∷ Sw01 ∷ []) (Sw01 ∷ CX31 ∷ []) tt tt Eq.refl) ▸ done


-- resp CX03 at 1: 2 steps
lem-resp-CX03-at-1 : Complete 4 → ⟪ (CX03 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX13 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX03-at-1 c4 = run b0
  where
  b0 : Chain (CX03 ∷ []) (Sw01 ∷ CX13 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ CX13 ∷ []) (lw4 c4 (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) tt tt Eq.refl) ▸ done


-- resp CX03 at 2: 4 steps
lem-resp-CX03-at-2 : Complete 4 → ⟪ (CX03 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX13 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX03-at-2 c4 = run b0
  where
  b0 : Chain (CX03 ∷ []) (Sw12 ∷ Sw01 ∷ CX13 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw12 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CX13 ∷ []) (lw4 c4 (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) tt tt Eq.refl) ▸ done


-- nat 1 BOX(4;301): 8 steps
lem-nat-1-BOX⟨4·301⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-301 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-302 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·301⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-301 ∷ []) (Bx4-302 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 2 2 (Bx3-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·41⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx3-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·41⟩ c4) ▸
       at 0 6 (Bx4-302 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;4201): 8 steps
lem-nat-1-BOX⟨3·4201⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·4201⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-4201 ∷ []) (Bx3-4102 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-301 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-302 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·301⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-302 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·301⟩ c4) ▸
       at 0 6 (Bx3-4102 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;302): 8 steps
lem-nat-1-BOX⟨4·302⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-302 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-301 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·302⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-302 ∷ []) (Bx4-301 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 2 2 (Bx3-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·42⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx3-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·42⟩ c4) ▸
       at 0 6 (Bx4-301 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;4102): 8 steps
lem-nat-1-BOX⟨3·4102⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·4102⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-4102 ∷ []) (Bx3-4201 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx4-302 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-301 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·302⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-301 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·302⟩ c4) ▸
       at 0 6 (Bx3-4201 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;201): 8 steps
lem-nat-2-BOX⟨4·201⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-201 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-301 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·201⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-201 ∷ []) (Bx4-301 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 2 2 (Bx3-41 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·41⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx3-41 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·41⟩ c4) ▸
       at 0 6 (Bx4-301 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;4301): 8 steps
lem-nat-2-BOX⟨2·4301⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·4301⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-4301 ∷ []) (Bx3-4201 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-301 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·201⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-301 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·201⟩ c4) ▸
       at 0 6 (Bx3-4201 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;41): 3 steps
lem-nat-3-BOX⟨2·41⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-31 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·41⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-41 ∷ []) (Bx2-31 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw34 ∷ []) (lem-nat-3-CZ14 c4) ▸
       at 0 1 (Bx2-31 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;201): 8 steps
lem-nat-3-BOX⟨4·201⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx4-201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-201 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·201⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-201 ∷ []) (Bx3-201 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4) ▸
       at 2 2 (Bx2-31 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·41⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx2-31 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·41⟩ c4) ▸
       at 0 6 (Bx3-201 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;4301): 8 steps
lem-nat-3-BOX⟨2·4301⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·4301⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-4301 ∷ []) (Bx2-3401 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-201 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·201⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-201 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·201⟩ c4) ▸
       at 0 6 (Bx2-3401 ∷ []) (refl) ▸ done


-- nat 0 SBOX(3;4;2;0): 2 steps
lem-nat-0-SBOX⟨3·4·2·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb3-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-2-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·4·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb3-4-2-0 ∷ []) (Sb3-4-2-1 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb3-4-2-0 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 0 1 (Sb3-4-2-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(3;4;2;0): 2 steps
lem-nat-0-SBOXd⟨3·4·2·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻3-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-2-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨3·4·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻3-4-2-0 ∷ []) (Sb⁻3-4-2-1 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb⁻3-4-2-0 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 0 1 (Sb⁻3-4-2-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(3;4;10;2): 7 steps
lem-nat-0-SBOX⟨3·4·10·2⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb3-4-10-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-01-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·4·10·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb3-4-10-2 ∷ []) (Sb3-4-01-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx3-4102 ∷ Toff201 ∷ Sb3-4-2-0 ∷ Toff201 ∷ Sb⁻3-4-2-0 ∷ []) (refl) ▸
       at 0 2 (Bx3-4012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4102⟩ c4) ▸
       at 1 2 (Toff201 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff201 ∷ []) (Toff201 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb3-4-2-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·4·2·0⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff201 ∷ []) (Toff201 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻3-4-2-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨3·4·2·0⟩ c4) ▸
       at 0 5 (Sb3-4-01-2 ∷ []) (refl) ▸ done


-- nat 0 SBOX(3;4;2;1): 2 steps
lem-nat-0-SBOX⟨3·4·2·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb3-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-2-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·4·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb3-4-2-1 ∷ []) (Sb3-4-2-0 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb3-4-2-1 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 0 1 (Sb3-4-2-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(3;4;2;1): 2 steps
lem-nat-0-SBOXd⟨3·4·2·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻3-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-2-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨3·4·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻3-4-2-1 ∷ []) (Sb⁻3-4-2-0 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb⁻3-4-2-1 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 0 1 (Sb⁻3-4-2-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(3;4;01;2): 7 steps
lem-nat-0-SBOX⟨3·4·01·2⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb3-4-01-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-10-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·4·01·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb3-4-01-2 ∷ []) (Sb3-4-10-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 0 2 (Bx3-4102 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4012⟩ c4) ▸
       at 1 2 (Toff201 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff201 ∷ []) (Toff201 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb3-4-2-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·4·2·1⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff201 ∷ []) (Toff201 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻3-4-2-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨3·4·2·1⟩ c4) ▸
       at 0 5 (Sb3-4-10-2 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;4;1;0): 3 steps
lem-nat-1-SBOX⟨3·4·1·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb3-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-4-1-0 ∷ []) (Sb3-4-2-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb3-4-2-0 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(3;4;1;0): 3 steps
lem-nat-1-SBOXd⟨3·4·1·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻3-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·4·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻3-4-1-0 ∷ []) (Sb⁻3-4-2-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻3-4-2-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;4;20;1): 7 steps
lem-nat-1-SBOX⟨3·4·20·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb3-4-20-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-10-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·20·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-4-20-1 ∷ []) (Sb3-4-10-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx3-4201 ∷ Toff102 ∷ Sb3-4-1-0 ∷ Toff102 ∷ Sb⁻3-4-1-0 ∷ []) (refl) ▸
       at 0 2 (Bx3-4102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4201⟩ c4) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb3-4-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·1·0⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻3-4-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·4·1·0⟩ c4) ▸
       at 0 5 (Sb3-4-10-2 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;4;2;0): 3 steps
lem-nat-1-SBOX⟨3·4·2·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb3-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-4-2-0 ∷ []) (Sb3-4-1-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb3-4-1-0 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(3;4;2;0): 3 steps
lem-nat-1-SBOXd⟨3·4·2·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻3-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·4·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻3-4-2-0 ∷ []) (Sb⁻3-4-1-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24⁻ ∷ []) (CS14⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻3-4-1-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;4;10;2): 7 steps
lem-nat-1-SBOX⟨3·4·10·2⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb3-4-10-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-20-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·10·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-4-10-2 ∷ []) (Sb3-4-20-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx3-4102 ∷ Toff201 ∷ Sb3-4-2-0 ∷ Toff201 ∷ Sb⁻3-4-2-0 ∷ []) (refl) ▸
       at 0 2 (Bx3-4201 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4102⟩ c4) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb3-4-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·2·0⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻3-4-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·4·2·0⟩ c4) ▸
       at 0 5 (Sb3-4-20-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(2;4;1;0): 3 steps
lem-nat-2-SBOX⟨2·4·1·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb2-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-1-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·4·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-4-1-0 ∷ []) (Sb3-4-1-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb3-4-1-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(2;4;1;0): 3 steps
lem-nat-2-SBOXd⟨2·4·1·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻2-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-1-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·4·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻2-4-1-0 ∷ []) (Sb⁻3-4-1-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻3-4-1-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(2;4;30;1): 7 steps
lem-nat-2-SBOX⟨2·4·30·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb2-4-30-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-20-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·4·30·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-4-30-1 ∷ []) (Sb3-4-20-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx2-4301 ∷ Toff103 ∷ Sb2-4-1-0 ∷ Toff103 ∷ Sb⁻2-4-1-0 ∷ []) (refl) ▸
       at 0 2 (Bx3-4201 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4301⟩ c4) ▸
       at 1 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 2 2 (Sb3-4-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·4·1·0⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 4 2 (Sb⁻3-4-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·4·1·0⟩ c4) ▸
       at 0 5 (Sb3-4-20-1 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;4;1;0): 3 steps
lem-nat-3-SBOX⟨2·4·1·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb2-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-1-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·4·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-4-1-0 ∷ []) (Sb2-3-1-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw34 ∷ []) (lem-nat-3-CS14 c4) ▸
       at 0 1 (Sb2-3-1-0 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(2;4;1;0): 3 steps
lem-nat-3-SBOXd⟨2·4·1·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻2-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-1-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·4·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-4-1-0 ∷ []) (Sb⁻2-3-1-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd14 c4) ▸
       at 0 1 (Sb⁻2-3-1-0 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;4;30;1): 7 steps
lem-nat-3-SBOX⟨2·4·30·1⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb2-4-30-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-40-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·4·30·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-4-30-1 ∷ []) (Sb2-3-40-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx2-4301 ∷ Toff103 ∷ Sb2-4-1-0 ∷ Toff103 ∷ Sb⁻2-4-1-0 ∷ []) (refl) ▸
       at 0 2 (Bx2-3401 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·4301⟩ c4) ▸
       at 1 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 2 2 (Sb2-3-1-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·4·1·0⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 4 2 (Sb⁻2-3-1-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·4·1·0⟩ c4) ▸
       at 0 5 (Sb2-3-40-1 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;124): 8 steps
lem-nat-2-BOX⟨0·124⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-134 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·124⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-124 ∷ []) (Bx0-134 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-04 ∷ Toff012 ∷ CCZ012 ∷ Bx1-04 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 2 2 (Bx1-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·04⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx1-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·04⟩ c4) ▸
       at 0 6 (Bx0-134 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;0324): 8 steps
lem-nat-2-BOX⟨1·0324⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·0324⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-0324 ∷ []) (Bx1-0234 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-124 ∷ Toff103 ∷ CCZ013 ∷ Bx0-124 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 2 2 (Bx0-134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·124⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx0-134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·124⟩ c4) ▸
       at 0 6 (Bx1-0234 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;123): 8 steps
lem-nat-3-BOX⟨0·123⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-124 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·123⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-123 ∷ []) (Bx0-124 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-03 ∷ Toff012 ∷ CCZ012 ∷ Bx1-03 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 2 2 (Bx1-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·03⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx1-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·03⟩ c4) ▸
       at 0 6 (Bx0-124 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;0423): 8 steps
lem-nat-3-BOX⟨1·0423⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·0423⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-0423 ∷ []) (Bx1-0324 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 1 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 2 2 (Bx0-124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·123⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 4 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 5 2 (Bx0-124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·123⟩ c4) ▸
       at 0 6 (Bx1-0324 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;124): 8 steps
lem-nat-3-BOX⟨0·124⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-123 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·124⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-124 ∷ []) (Bx0-123 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-04 ∷ Toff012 ∷ CCZ012 ∷ Bx1-04 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 2 2 (Bx1-03 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·04⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx1-03 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·04⟩ c4) ▸
       at 0 6 (Bx0-123 ∷ []) (refl) ▸ done


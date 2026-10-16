{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R025 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-TOFF024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF102 ; lem-nat-3-CCZ014 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013 ; lem-nat-1-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ124 ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨1·43⟩ ; lem-nat-0-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨3·40⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-TOFF401 ; lem-nat-0-TOFF413 ; lem-nat-1-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-CZ04 ; lem-nat-1-TOFF023)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-CCZ014 ; lem-nat-3-CZ03 ; lem-nat-3-CZ04)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-CS01)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-CS04 ; lem-nat-1-CS04)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-TOFF134 ; lem-nat-1-CSd01)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-BOX⟨0·32⟩ ; lem-nat-0-BOX⟨1·32⟩ ; lem-nat-0-TOFF034 ; lem-nat-1-BOX⟨1·32⟩ ; lem-nat-1-BOX⟨2·0341⟩ ; lem-nat-1-BOX⟨2·31⟩ ; lem-nat-1-CSd04)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-0-CSd04 ; lem-nat-2-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-BOX⟨2·30⟩ ; lem-nat-0-BOX⟨2·31⟩ ; lem-nat-0-TOFF124)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-2-TOFF134)
open import Examples.Groups.Clifford+CS.Five.D.R024 using (lem-nat-2-BOX⟨3·41⟩)
-- nat 2 BOX(4;301): 8 steps
lem-nat-2-BOX⟨4·301⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-301 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-201 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·301⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-301 ∷ []) (Bx4-201 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 2 2 (Bx2-41 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·41⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx2-41 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·41⟩ c4) ▸
       at 0 6 (Bx4-201 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;4201): 8 steps
lem-nat-2-BOX⟨3·4201⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·4201⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-4201 ∷ []) (Bx2-4301 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-301 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-201 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·301⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-201 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·301⟩ c4) ▸
       at 0 6 (Bx2-4301 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;4;1;0): 3 steps
lem-nat-2-SBOX⟨3·4·1·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb3-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-1-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·4·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-4-1-0 ∷ []) (Sb2-4-1-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb2-4-1-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(3;4;1;0): 3 steps
lem-nat-2-SBOXd⟨3·4·1·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻3-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-1-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·4·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻3-4-1-0 ∷ []) (Sb⁻2-4-1-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻2-4-1-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;4;20;1): 7 steps
lem-nat-2-SBOX⟨3·4·20·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb3-4-20-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-30-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·4·20·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-4-20-1 ∷ []) (Sb2-4-30-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx3-4201 ∷ Toff102 ∷ Sb3-4-1-0 ∷ Toff102 ∷ Sb⁻3-4-1-0 ∷ []) (refl) ▸
       at 0 2 (Bx2-4301 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4201⟩ c4) ▸
       at 1 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 2 2 (Sb2-4-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·4·1·0⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 4 2 (Sb⁻2-4-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·4·1·0⟩ c4) ▸
       at 0 5 (Sb2-4-30-1 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;42): 3 steps
lem-nat-2-BOX⟨1·42⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-43 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·42⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-42 ∷ []) (Bx1-43 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ24 ∷ []) (CZ34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx1-43 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;102): 8 steps
lem-nat-2-BOX⟨4·102⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-103 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·102⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-102 ∷ []) (Bx4-103 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-42 ∷ Toff401 ∷ CCZ014 ∷ Bx1-42 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 2 2 (Bx1-43 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·42⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx1-43 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·42⟩ c4) ▸
       at 0 6 (Bx4-103 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;4302): 8 steps
lem-nat-2-BOX⟨1·4302⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-4302 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4203 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·4302⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-4302 ∷ []) (Bx1-4203 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-102 ∷ Toff134 ∷ CCZ134 ∷ Bx4-102 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 2 2 (Bx4-103 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·102⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx4-103 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·102⟩ c4) ▸
       at 0 6 (Bx1-4203 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;4;2;0): 3 steps
lem-nat-2-SBOX⟨1·4·2·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb1-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·4·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-4-2-0 ∷ []) (Sb1-4-3-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb1-4-3-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;4;2;0): 3 steps
lem-nat-2-SBOXd⟨1·4·2·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻1-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·4·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-4-2-0 ∷ []) (Sb⁻1-4-3-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻1-4-3-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;4;30;2): 7 steps
lem-nat-2-SBOX⟨1·4·30·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb1-4-30-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-20-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·4·30·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-4-30-2 ∷ []) (Sb1-4-20-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx1-4302 ∷ Toff203 ∷ Sb1-4-2-0 ∷ Toff203 ∷ Sb⁻1-4-2-0 ∷ []) (refl) ▸
       at 0 2 (Bx1-4203 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·4302⟩ c4) ▸
       at 1 2 (Toff302 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-4-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·4·2·0⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻1-4-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·4·2·0⟩ c4) ▸
       at 0 5 (Sb1-4-20-3 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;310): 8 steps
lem-nat-0-BOX⟨4·310⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-310 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-301 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·310⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-310 ∷ []) (Bx4-301 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 2 2 (Bx3-41 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·40⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx3-41 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·40⟩ c4) ▸
       at 0 6 (Bx4-301 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;4210): 8 steps
lem-nat-0-BOX⟨3·4210⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·4210⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-4210 ∷ []) (Bx3-4201 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-310 ∷ Toff324 ∷ CCZ234 ∷ Bx4-310 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Bx4-301 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·310⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx4-301 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·310⟩ c4) ▸
       at 0 6 (Bx3-4201 ∷ []) (refl) ▸ done


-- nat 0 SBOX(3;4;0;1): 3 steps
lem-nat-0-SBOX⟨3·4·0·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb3-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-1-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·4·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb3-4-0-1 ∷ []) (Sb3-4-1-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 c4) ▸
       at 0 1 (Sb3-4-1-0 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(3;4;0;1): 3 steps
lem-nat-0-SBOXd⟨3·4·0·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻3-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-1-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨3·4·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻3-4-0-1 ∷ []) (Sb⁻3-4-1-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw01 ∷ []) (lem-nat-0-CSd04 c4) ▸
       at 0 1 (Sb⁻3-4-1-0 ∷ []) (refl) ▸ done


-- nat 0 SBOX(3;4;21;0): 7 steps
lem-nat-0-SBOX⟨3·4·21·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb3-4-21-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-20-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·4·21·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb3-4-21-0 ∷ []) (Sb3-4-20-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx3-4210 ∷ Toff012 ∷ Sb3-4-0-1 ∷ Toff012 ∷ Sb⁻3-4-0-1 ∷ []) (refl) ▸
       at 0 2 (Bx3-4201 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4210⟩ c4) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb3-4-1-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·4·0·1⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻3-4-1-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨3·4·0·1⟩ c4) ▸
       at 0 5 (Sb3-4-20-1 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;103): 8 steps
lem-nat-0-BOX⟨4·103⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-013 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·103⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-103 ∷ []) (Bx4-013 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-43 ∷ Toff401 ∷ CCZ014 ∷ Bx1-43 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 2 2 (Bx0-43 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·43⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx0-43 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·43⟩ c4) ▸
       at 0 6 (Bx4-013 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;4203): 8 steps
lem-nat-0-BOX⟨1·4203⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-4203 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·4203⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-4203 ∷ []) (Bx0-4213 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-103 ∷ Toff124 ∷ CCZ124 ∷ Bx4-103 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 2 2 (Bx4-013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·103⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx4-013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·103⟩ c4) ▸
       at 0 6 (Bx0-4213 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;4;3;0): 2 steps
lem-nat-0-SBOX⟨1·4·3·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb1-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·4·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-4-3-0 ∷ []) (Sb0-4-3-1 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb1-4-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 0 1 (Sb0-4-3-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(1;4;3;0): 2 steps
lem-nat-0-SBOXd⟨1·4·3·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻1-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·4·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻1-4-3-0 ∷ []) (Sb⁻0-4-3-1 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb⁻1-4-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 0 1 (Sb⁻0-4-3-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(1;4;20;3): 7 steps
lem-nat-0-SBOX⟨1·4·20·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-21-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·4·20·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-4-20-3 ∷ []) (Sb0-4-21-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx1-4203 ∷ Toff302 ∷ Sb1-4-3-0 ∷ Toff302 ∷ Sb⁻1-4-3-0 ∷ []) (refl) ▸
       at 0 2 (Bx0-4213 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4203⟩ c4) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-4-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·4·3·0⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻0-4-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·4·3·0⟩ c4) ▸
       at 0 5 (Sb0-4-21-3 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;40): 3 steps
lem-nat-1-BOX⟨3·40⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-40 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-40 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·40⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-40 ∷ []) (Bx3-40 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw12 ∷ []) (lem-nat-1-CZ04 c4) ▸
       at 0 1 (Bx3-40 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;320): 8 steps
lem-nat-1-BOX⟨4·320⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-310 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·320⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-320 ∷ []) (Bx4-310 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-40 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·40⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-40 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·40⟩ c4) ▸
       at 0 6 (Bx4-310 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;4120): 8 steps
lem-nat-1-BOX⟨3·4120⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·4120⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-4120 ∷ []) (Bx3-4210 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx4-320 ∷ Toff314 ∷ CCZ134 ∷ Bx4-320 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-310 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·320⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-310 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·320⟩ c4) ▸
       at 0 6 (Bx3-4210 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;4;0;2): 3 steps
lem-nat-1-SBOX⟨3·4·0·2⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb3-4-0-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-0-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·0·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-4-0-2 ∷ []) (Sb3-4-0-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 c4) ▸
       at 0 1 (Sb3-4-0-1 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(3;4;0;2): 3 steps
lem-nat-1-SBOXd⟨3·4·0·2⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻3-4-0-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-0-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·4·0·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻3-4-0-2 ∷ []) (Sb⁻3-4-0-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd04 c4) ▸
       at 0 1 (Sb⁻3-4-0-1 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;4;12;0): 7 steps
lem-nat-1-SBOX⟨3·4·12·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb3-4-12-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-21-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·12·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-4-12-0 ∷ []) (Sb3-4-21-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx3-4120 ∷ Toff012 ∷ Sb3-4-0-2 ∷ Toff012 ∷ Sb⁻3-4-0-2 ∷ []) (refl) ▸
       at 0 2 (Bx3-4210 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4120⟩ c4) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb3-4-0-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·0·2⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻3-4-0-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·4·0·2⟩ c4) ▸
       at 0 5 (Sb3-4-21-0 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;013): 8 steps
lem-nat-1-BOX⟨4·013⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-013 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-023 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·013⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-013 ∷ []) (Bx4-023 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 2 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 3 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 0 6 (Bx4-023 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;4213): 8 steps
lem-nat-1-BOX⟨0·4213⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·4213⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-4213 ∷ []) (Bx0-4123 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 2 2 (Bx4-023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·013⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx4-023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·013⟩ c4) ▸
       at 0 6 (Bx0-4123 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;4;3;1): 2 steps
lem-nat-1-SBOX⟨0·4·3·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb0-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-3-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·4·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-4-3-1 ∷ []) (Sb0-4-3-2 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Sb0-4-3-1 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 0 1 (Sb0-4-3-2 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOXd(0;4;3;1): 2 steps
lem-nat-1-SBOXd⟨0·4·3·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻0-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-3-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·4·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-4-3-1 ∷ []) (Sb⁻0-4-3-2 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Sb⁻0-4-3-1 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS)) ▸
       at 0 1 (Sb⁻0-4-3-2 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOX(0;4;21;3): 7 steps
lem-nat-1-SBOX⟨0·4·21·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb0-4-21-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-12-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·4·21·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-4-21-3 ∷ []) (Sb0-4-12-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx0-4213 ∷ Toff312 ∷ Sb0-4-3-1 ∷ Toff312 ∷ Sb⁻0-4-3-1 ∷ []) (refl) ▸
       at 0 2 (Bx0-4123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·4213⟩ c4) ▸
       at 1 2 (Toff312 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-4-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·4·3·1⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻0-4-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·4·3·1⟩ c4) ▸
       at 0 5 (Sb0-4-12-3 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;4;3;2): 3 steps
lem-nat-3-SBOX⟨0·4·3·2⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb0-4-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-4-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·4·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-4-3-2 ∷ []) (Sb0-3-4-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS34 ∷ []) (refl) ▸
       at 0 2 (CS34 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CS34 ∷ []) (CS34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-3-4-2 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;3;4;2): 3 steps
lem-nat-3-SBOX⟨0·3·4·2⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb0-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-3-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·3·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-3-4-2 ∷ []) (Sb0-4-3-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS34 ∷ []) (refl) ▸
       at 0 2 (CS34 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CS34 ∷ []) (CS34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-4-3-2 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;4;3;2): 3 steps
lem-nat-3-SBOXd⟨0·4·3·2⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻0-4-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-4-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·4·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-4-3-2 ∷ []) (Sb⁻0-3-4-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 2 (CS34⁻ ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-3-4-2 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;3;4;2): 3 steps
lem-nat-3-SBOXd⟨0·3·4·2⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻0-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-3-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·3·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-3-4-2 ∷ []) (Sb⁻0-4-3-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 2 (CS34⁻ ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-4-3-2 ∷ []) (refl) ▸ done


-- comm TOFF013 CSd24: 15 steps
lem-comm-TOFF013-CSd24 : Complete 4 → ⟪ (Toff013 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Toff013 ∷ []) ⟫ʷ
lem-comm-TOFF013-CSd24 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff013 ∷ CS24⁻ ∷ []) (Sw34 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS)) ▸ done

  b1 : Chain (Sw34 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (CS24⁻ ∷ Toff013 ∷ [])
  b1 = at 2 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 2 5 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOX(3;014): 8 steps
lem-nat-1-BOX⟨3·014⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-024 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·014⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-014 ∷ []) (Bx3-024 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 2 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 0 6 (Bx3-024 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;3214): 8 steps
lem-nat-1-BOX⟨0·3214⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·3214⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-3214 ∷ []) (Bx0-3124 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 2 2 (Bx3-024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·014⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx3-024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·014⟩ c4) ▸
       at 0 6 (Bx0-3124 ∷ []) (refl) ▸ done


-- comm CCZ014 CX23: 9 steps
lem-comm-CCZ014-CX23 : Complete 4 → ⟪ (CCZ014 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ014 ∷ []) ⟫ʷ
lem-comm-CCZ014-CX23 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ014 ∷ CX23 ∷ []) (CX23 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX24 ∷ []) (CX34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁)) ▸
       at 1 2 (CX24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX34 ∷ []) (CX24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

  b1 : Chain (CX23 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (CX23 ∷ CCZ014 ∷ [])
  b1 = at 1 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CSd24 at 3: 6 steps
lem-resp-CSd24-at-3 : Complete 4 → ⟪ (CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS34⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CSd24-at-3 c4 = run b0
  where
  b0 : Chain (CS24⁻ ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS34⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw23 ∷ CS34⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS34⁻ ∷ []) (sym (c₃ (Swap ↑) (CS • CS • CS))) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ CS34⁻ ∷ []) (sym (c₂ (Swap) ((CS • CS • CS) ↑))) ▸ done


-- nat 0 BOX(3;102): 8 steps
lem-nat-0-BOX⟨3·102⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-012 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·102⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-102 ∷ []) (Bx3-012 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-32 ∷ Toff301 ∷ CCZ013 ∷ Bx1-32 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-32 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·32⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-32 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·32⟩ c4) ▸
       at 0 6 (Bx3-012 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;3402): 8 steps
lem-nat-0-BOX⟨1·3402⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·3402⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-3402 ∷ []) (Bx0-3412 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-102 ∷ Toff134 ∷ CCZ134 ∷ Bx3-102 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 2 2 (Bx3-012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·102⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx3-012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·102⟩ c4) ▸
       at 0 6 (Bx0-3412 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;201): 8 steps
lem-nat-1-BOX⟨3·201⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-102 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·201⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-201 ∷ []) (Bx3-102 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 2 2 (Bx1-32 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·31⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx1-32 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·31⟩ c4) ▸
       at 0 6 (Bx3-102 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;3401): 8 steps
lem-nat-1-BOX⟨2·3401⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·3401⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-3401 ∷ []) (Bx1-3402 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·201⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·201⟩ c4) ▸
       at 0 6 (Bx1-3402 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;210): 8 steps
lem-nat-0-BOX⟨3·210⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-201 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·210⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-210 ∷ []) (Bx3-201 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-31 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·30⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-31 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·30⟩ c4) ▸
       at 0 6 (Bx3-201 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;3410): 8 steps
lem-nat-0-BOX⟨2·3410⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·3410⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-3410 ∷ []) (Bx2-3401 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-210 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 2 2 (Bx3-201 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·210⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx3-201 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·210⟩ c4) ▸
       at 0 6 (Bx2-3401 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;10): 3 steps
lem-nat-0-BOX⟨2·10⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-01 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·10⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-10 ∷ []) (Bx2-01 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ01 ∷ []) (CZ01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx2-01 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;240): 8 steps
lem-nat-0-BOX⟨1·240⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-240 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-241 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·240⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-240 ∷ []) (Bx0-241 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 2 2 (Bx2-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·10⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx2-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·10⟩ c4) ▸
       at 0 6 (Bx0-241 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;1340): 8 steps
lem-nat-0-BOX⟨2·1340⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·1340⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-1340 ∷ []) (Bx2-0341 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff203 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-241 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·240⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-241 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·240⟩ c4) ▸
       at 0 6 (Bx2-0341 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;012): 8 steps
lem-nat-0-BOX⟨3·012⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-102 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·012⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-012 ∷ []) (Bx3-102 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-32 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·32⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-32 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·32⟩ c4) ▸
       at 0 6 (Bx3-102 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;3412): 8 steps
lem-nat-0-BOX⟨0·3412⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·3412⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-3412 ∷ []) (Bx1-3402 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 2 2 (Bx3-102 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·012⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx3-102 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·012⟩ c4) ▸
       at 0 6 (Bx1-3402 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;102): 8 steps
lem-nat-1-BOX⟨3·102⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-201 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·102⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-102 ∷ []) (Bx3-201 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-32 ∷ Toff301 ∷ CCZ013 ∷ Bx1-32 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 2 2 (Bx2-31 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·32⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx2-31 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·32⟩ c4) ▸
       at 0 6 (Bx3-201 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;3402): 8 steps
lem-nat-1-BOX⟨1·3402⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·3402⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-3402 ∷ []) (Bx2-3401 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-102 ∷ Toff134 ∷ CCZ134 ∷ Bx3-102 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-201 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·102⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-201 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·102⟩ c4) ▸
       at 0 6 (Bx2-3401 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;201): 8 steps
lem-nat-0-BOX⟨3·201⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-210 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·201⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-201 ∷ []) (Bx3-210 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-30 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·31⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-30 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·31⟩ c4) ▸
       at 0 6 (Bx3-210 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;3401): 8 steps
lem-nat-0-BOX⟨2·3401⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·3401⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-3401 ∷ []) (Bx2-3410 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 2 2 (Bx3-210 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·201⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx3-210 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·201⟩ c4) ▸
       at 0 6 (Bx2-3410 ∷ []) (refl) ▸ done


-- resp CSd04 at 2: 12 steps
lem-resp-CSd04-at-2 : Complete 4 → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS14⁻ ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CSd04-at-2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS04⁻ ∷ []) (Sw12 ∷ Sw34 ∷ CS03⁻ ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 2 (Sw12 ∷ CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ CS03⁻ ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CS14⁻ ∷ Sw01 ∷ Sw12 ∷ [])
  b1 = at 3 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CS13⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOX(2;0;1;4): 3 steps
lem-nat-1-SBOX⟨2·0·1·4⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb2-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·0·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-0-1-4 ∷ []) (Sb1-0-2-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 0 1 (Sb1-0-2-4 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;0;1;4): 3 steps
lem-nat-1-SBOXd⟨2·0·1·4⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻2-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·0·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-0-1-4 ∷ []) (Sb⁻1-0-2-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 0 1 (Sb⁻1-0-2-4 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;0;34;1): 7 steps
lem-nat-1-SBOX⟨2·0·34·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb2-0-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-34-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·0·34·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-0-34-1 ∷ []) (Sb1-0-34-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx2-0341 ∷ Toff134 ∷ Sb2-0-1-4 ∷ Toff134 ∷ Sb⁻2-0-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx1-0342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0341⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-0-2-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·1·4⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻1-0-2-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·1·4⟩ c4) ▸
       at 0 5 (Sb1-0-34-2 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;03): 3 steps
lem-nat-3-BOX⟨1·03⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-04 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·03⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-03 ∷ []) (Bx1-04 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw34 ∷ []) (lem-nat-3-CZ03 c4) ▸
       at 0 1 (Bx1-04 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;143): 8 steps
lem-nat-3-BOX⟨0·143⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-134 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·143⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-143 ∷ []) (Bx0-134 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-03 ∷ Toff014 ∷ CCZ014 ∷ Bx1-03 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 1 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 2 2 (Bx1-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·03⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 4 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 5 2 (Bx1-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·03⟩ c4) ▸
       at 0 6 (Bx0-134 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;0243): 8 steps
lem-nat-3-BOX⟨1·0243⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·0243⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-0243 ∷ []) (Bx1-0234 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-143 ∷ Toff102 ∷ CCZ012 ∷ Bx0-143 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 2 2 (Bx0-134 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·143⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx0-134 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·143⟩ c4) ▸
       at 0 6 (Bx1-0234 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;04): 3 steps
lem-nat-3-BOX⟨1·04⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-03 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·04⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-04 ∷ []) (Bx1-03 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw34 ∷ []) (lem-nat-3-CZ04 c4) ▸
       at 0 1 (Bx1-03 ∷ []) (refl) ▸ done


{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R040 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF034 ; lem-nat-3-CCZ024 ; lem-nat-3-CCZ034 ; lem-nat-3-CZ13)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-3-CCZ023 ; lem-nat-3-CZ14)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ124 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF412 ; lem-nat-2-TOFF413 ; lem-nat-3-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-3-TOFF302)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-2-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-2-TOFF214 ; lem-nat-2-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-2-CZ04 ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-CZ01 ; lem-nat-1-CZ02 ; lem-nat-3-CZ03 ; lem-nat-3-CZ04)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-TOFF314 ; lem-nat-3-CS13)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-TOFF134 ; lem-nat-1-CSd01 ; lem-nat-1-TOFF034 ; lem-nat-2-TOFF124)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-TOFF034 ; lem-nat-3-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-3-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-2-TOFF134)
open import Examples.Groups.Clifford+CS.Five.D.R026 using (lem-nat-3-TOFF312)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-2-BOX⟨0·41⟩)
open import Examples.Groups.Clifford+CS.Five.D.R035 using (lem-nat-0-BOX⟨2·0431⟩ ; lem-nat-0-BOX⟨2·1430⟩ ; lem-nat-1-BOX⟨2·1430⟩)
open import Examples.Groups.Clifford+CS.Five.D.R036 using (lem-nat-0-SBOX⟨2·0·1·3⟩ ; lem-nat-0-SBOX⟨2·1·0·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R037 using (lem-nat-0-BOX⟨1·40⟩ ; lem-nat-0-SBOXd⟨2·0·1·3⟩ ; lem-nat-0-SBOXd⟨2·1·0·3⟩)
-- nat 0 BOX(4;120): 8 steps
lem-nat-0-BOX⟨4·120⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-120 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-021 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·120⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-120 ∷ []) (Bx4-021 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-40 ∷ Toff412 ∷ CCZ124 ∷ Bx1-40 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 2 2 (Bx0-41 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·40⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx0-41 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·40⟩ c4) ▸
       at 0 6 (Bx4-021 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;4320): 8 steps
lem-nat-0-BOX⟨1·4320⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-4320 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·4320⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-4320 ∷ []) (Bx0-4321 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-120 ∷ Toff134 ∷ CCZ134 ∷ Bx4-120 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 2 2 (Bx4-021 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·120⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx4-021 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·120⟩ c4) ▸
       at 0 6 (Bx0-4321 ∷ []) (refl) ▸ done


-- resp CX31 at 2: 4 steps
lem-resp-CX31-at-2 : Complete 4 → ⟪ (CX31 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX32 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX31-at-2 c4 = run b0
  where
  b0 : Chain (CX31 ∷ []) (Sw12 ∷ Sw01 ∷ CX32 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw12 ∷ CX32 ∷ []) (lw4 c4 (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CX32 ∷ []) (sym (c₂ (Swap) (CX₁₀))) ▸ done


-- nat 0 SBOX(2;0;43;1): 7 steps
lem-nat-0-SBOX⟨2·0·43·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb2-0-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-43-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·0·43·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-0-43-1 ∷ []) (Sb2-1-43-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (refl) ▸
       at 0 2 (Bx2-1430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0431⟩ c4) ▸
       at 1 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 2 2 (Sb2-1-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·1·3⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 4 2 (Sb⁻2-1-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·0·1·3⟩ c4) ▸
       at 0 5 (Sb2-1-43-0 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;40): 3 steps
lem-nat-3-BOX⟨1·40⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-40 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-30 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·40⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-40 ∷ []) (Bx1-30 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw34 ∷ []) (lem-nat-3-CZ04 c4) ▸
       at 0 1 (Bx1-30 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;120): 8 steps
lem-nat-3-BOX⟨4·120⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx4-120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-120 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·120⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-120 ∷ []) (Bx3-120 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-40 ∷ Toff412 ∷ CCZ124 ∷ Bx1-40 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (Toff312 ∷ Sw34 ∷ []) (lem-nat-3-TOFF412 c4) ▸
       at 2 2 (Bx1-30 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·40⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw34 ∷ []) (lem-nat-3-TOFF412 c4) ▸
       at 4 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 5 2 (Bx1-30 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·40⟩ c4) ▸
       at 0 6 (Bx3-120 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;4320): 8 steps
lem-nat-3-BOX⟨1·4320⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-4320 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3420 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·4320⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-4320 ∷ []) (Bx1-3420 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-120 ∷ Toff134 ∷ CCZ134 ∷ Bx4-120 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-120 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·120⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-120 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·120⟩ c4) ▸
       at 0 6 (Bx1-3420 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;30): 3 steps
lem-nat-3-BOX⟨1·30⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-40 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·30⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-30 ∷ []) (Bx1-40 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw34 ∷ []) (lem-nat-3-CZ03 c4) ▸
       at 0 1 (Bx1-40 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;120): 8 steps
lem-nat-3-BOX⟨3·120⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx3-120 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-120 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·120⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-120 ∷ []) (Bx4-120 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-30 ∷ Toff312 ∷ CCZ123 ∷ Bx1-30 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (Toff412 ∷ Sw34 ∷ []) (lem-nat-3-TOFF312 c4) ▸
       at 2 2 (Bx1-40 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·30⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw34 ∷ []) (lem-nat-3-TOFF312 c4) ▸
       at 4 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 5 2 (Bx1-40 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·30⟩ c4) ▸
       at 0 6 (Bx4-120 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;3420): 8 steps
lem-nat-3-BOX⟨1·3420⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-3420 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4320 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·3420⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-3420 ∷ []) (Bx1-4320 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-120 ∷ Toff134 ∷ CCZ134 ∷ Bx3-120 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-120 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·120⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-120 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·120⟩ c4) ▸
       at 0 6 (Bx1-4320 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;40): 3 steps
lem-nat-2-BOX⟨1·40⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-40 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-40 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·40⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-40 ∷ []) (Bx1-40 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw23 ∷ []) (lem-nat-2-CZ04 c4) ▸
       at 0 1 (Bx1-40 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;130): 8 steps
lem-nat-2-BOX⟨4·130⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-130 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-120 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·130⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-130 ∷ []) (Bx4-120 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx1-40 ∷ Toff413 ∷ CCZ134 ∷ Bx1-40 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 2 2 (Bx1-40 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·40⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx1-40 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·40⟩ c4) ▸
       at 0 6 (Bx4-120 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;4230): 8 steps
lem-nat-2-BOX⟨1·4230⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-4230 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4320 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·4230⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-4230 ∷ []) (Bx1-4320 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-130 ∷ Toff124 ∷ CCZ124 ∷ Bx4-130 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 2 2 (Bx4-120 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·130⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx4-120 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·130⟩ c4) ▸
       at 0 6 (Bx1-4320 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;120): 8 steps
lem-nat-2-BOX⟨4·120⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-120 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-130 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·120⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-120 ∷ []) (Bx4-130 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-40 ∷ Toff412 ∷ CCZ124 ∷ Bx1-40 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 2 2 (Bx1-40 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·40⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx1-40 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·40⟩ c4) ▸
       at 0 6 (Bx4-130 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;4320): 8 steps
lem-nat-2-BOX⟨1·4320⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-4320 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4230 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·4320⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-4320 ∷ []) (Bx1-4230 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-120 ∷ Toff134 ∷ CCZ134 ∷ Bx4-120 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 2 2 (Bx4-130 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·120⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx4-130 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·120⟩ c4) ▸
       at 0 6 (Bx1-4230 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;41): 3 steps
lem-nat-3-BOX⟨0·41⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-31 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·41⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-41 ∷ []) (Bx0-31 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw34 ∷ []) (lem-nat-3-CZ14 c4) ▸
       at 0 1 (Bx0-31 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;021): 8 steps
lem-nat-3-BOX⟨4·021⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx4-021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-021 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·021⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-021 ∷ []) (Bx3-021 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4) ▸
       at 2 2 (Bx0-31 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·41⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx0-31 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·41⟩ c4) ▸
       at 0 6 (Bx3-021 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;4321): 8 steps
lem-nat-3-BOX⟨0·4321⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·4321⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-4321 ∷ []) (Bx0-3421 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw34 ∷ []) (lem-nat-3-TOFF034 c4) ▸
       at 2 2 (Bx3-021 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·021⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw34 ∷ []) (lem-nat-3-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 5 2 (Bx3-021 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·021⟩ c4) ▸
       at 0 6 (Bx0-3421 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;31): 3 steps
lem-nat-3-BOX⟨0·31⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-41 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·31⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-31 ∷ []) (Bx0-41 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw34 ∷ []) (lem-nat-3-CZ13 c4) ▸
       at 0 1 (Bx0-41 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;021): 8 steps
lem-nat-3-BOX⟨3·021⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx3-021 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-021 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·021⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-021 ∷ []) (Bx4-021 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff402 ∷ Sw34 ∷ []) (lem-nat-3-TOFF302 c4) ▸
       at 2 2 (Bx0-41 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·31⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw34 ∷ []) (lem-nat-3-TOFF302 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx0-41 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·31⟩ c4) ▸
       at 0 6 (Bx4-021 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;3421): 8 steps
lem-nat-3-BOX⟨0·3421⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·3421⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-3421 ∷ []) (Bx0-4321 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw34 ∷ []) (lem-nat-3-TOFF034 c4) ▸
       at 2 2 (Bx4-021 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·021⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw34 ∷ []) (lem-nat-3-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 5 2 (Bx4-021 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·021⟩ c4) ▸
       at 0 6 (Bx0-4321 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;021): 8 steps
lem-nat-2-BOX⟨4·021⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-021 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-031 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·021⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-021 ∷ []) (Bx4-031 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 2 2 (Bx0-41 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·41⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx0-41 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·41⟩ c4) ▸
       at 0 6 (Bx4-031 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;4321): 8 steps
lem-nat-2-BOX⟨0·4321⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·4321⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-4321 ∷ []) (Bx0-4231 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 2 2 (Bx4-031 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·021⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx4-031 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·021⟩ c4) ▸
       at 0 6 (Bx0-4231 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;20): 3 steps
lem-nat-0-BOX⟨3·20⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-21 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·20⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-20 ∷ []) (Bx3-21 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ02 ∷ []) (CZ12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx3-21 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;310): 8 steps
lem-nat-0-BOX⟨2·310⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-310 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-301 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·310⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-310 ∷ []) (Bx2-301 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff203 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-21 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·20⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-21 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·20⟩ c4) ▸
       at 0 6 (Bx2-301 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;2410): 8 steps
lem-nat-0-BOX⟨3·2410⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-2410 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·2410⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-2410 ∷ []) (Bx3-2401 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-310 ∷ Toff324 ∷ CCZ234 ∷ Bx2-310 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Bx2-301 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·310⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx2-301 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·310⟩ c4) ▸
       at 0 6 (Bx3-2401 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;21): 3 steps
lem-nat-0-BOX⟨3·21⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-20 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·21⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-21 ∷ []) (Bx3-20 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ12 ∷ []) (CZ02 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx3-20 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;341): 8 steps
lem-nat-0-BOX⟨2·341⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-340 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·341⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-341 ∷ []) (Bx2-340 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 2 2 (Bx3-20 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·21⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx3-20 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·21⟩ c4) ▸
       at 0 6 (Bx2-340 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;2041): 8 steps
lem-nat-0-BOX⟨3·2041⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·2041⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-2041 ∷ []) (Bx3-2140 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-341 ∷ Toff302 ∷ CCZ023 ∷ Bx2-341 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-340 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·341⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-340 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·341⟩ c4) ▸
       at 0 6 (Bx3-2140 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;340): 8 steps
lem-nat-0-BOX⟨2·340⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-341 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·340⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-340 ∷ []) (Bx2-341 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 2 2 (Bx3-21 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·20⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx3-21 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·20⟩ c4) ▸
       at 0 6 (Bx2-341 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;2140): 8 steps
lem-nat-0-BOX⟨3·2140⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·2140⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-2140 ∷ []) (Bx3-2041 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-340 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-341 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·340⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-341 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·340⟩ c4) ▸
       at 0 6 (Bx3-2041 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;301): 8 steps
lem-nat-0-BOX⟨2·301⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-301 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-310 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·301⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-301 ∷ []) (Bx2-310 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-20 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·21⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-20 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·21⟩ c4) ▸
       at 0 6 (Bx2-310 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;2401): 8 steps
lem-nat-0-BOX⟨3·2401⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·2401⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-2401 ∷ []) (Bx3-2410 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-301 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Bx2-310 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·301⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx2-310 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·301⟩ c4) ▸
       at 0 6 (Bx3-2410 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;1;0;3): 3 steps
lem-nat-1-SBOX⟨2·1·0·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb2-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-0-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·1·0·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-1-0-3 ∷ []) (Sb1-2-0-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 0 1 (Sb1-2-0-3 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;1;0;3): 3 steps
lem-nat-1-SBOXd⟨2·1·0·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻2-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-0-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·1·0·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-1-0-3 ∷ []) (Sb⁻1-2-0-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 0 1 (Sb⁻1-2-0-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;1;43;0): 7 steps
lem-nat-1-SBOX⟨2·1·43·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb2-1-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·1·43·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-1-43-0 ∷ []) (Sb1-2-43-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx2-1430 ∷ Toff034 ∷ Sb2-1-0-3 ∷ Toff034 ∷ Sb⁻2-1-0-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-2430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1430⟩ c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Sb1-2-0-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·0·3⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 4 2 (Sb⁻1-2-0-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·1·0·3⟩ c4) ▸
       at 0 5 (Sb1-2-43-0 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;10): 3 steps
lem-nat-1-BOX⟨3·10⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-20 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·10⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-10 ∷ []) (Bx3-20 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 c4) ▸
       at 0 1 (Bx3-20 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;320): 8 steps
lem-nat-1-BOX⟨1·320⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-320 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-310 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·320⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-320 ∷ []) (Bx2-310 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff123 ∷ []) (Toff213 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-20 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·10⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff123 ∷ []) (Toff213 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-20 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·10⟩ c4) ▸
       at 0 6 (Bx2-310 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;1420): 8 steps
lem-nat-1-BOX⟨3·1420⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·1420⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-1420 ∷ []) (Bx3-2410 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-310 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·320⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-310 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·320⟩ c4) ▸
       at 0 6 (Bx3-2410 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;1;0;2): 3 steps
lem-nat-1-SBOX⟨3·1·0·2⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb3-1-0-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-2-0-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·1·0·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-1-0-2 ∷ []) (Sb3-2-0-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 0 1 (Sb3-2-0-1 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(3;1;0;2): 3 steps
lem-nat-1-SBOXd⟨3·1·0·2⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻3-1-0-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-2-0-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·1·0·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻3-1-0-2 ∷ []) (Sb⁻3-2-0-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 0 1 (Sb⁻3-2-0-1 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;1;42;0): 7 steps
lem-nat-1-SBOX⟨3·1·42·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-2-41-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·1·42·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-1-42-0 ∷ []) (Sb3-2-41-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 0 2 (Bx3-2410 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1420⟩ c4) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 2 2 (Sb3-2-0-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·1·0·2⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 4 2 (Sb⁻3-2-0-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·1·0·2⟩ c4) ▸
       at 0 5 (Sb3-2-41-0 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;20): 3 steps
lem-nat-1-BOX⟨3·20⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-10 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·20⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-20 ∷ []) (Bx3-10 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw12 ∷ []) (lem-nat-1-CZ02 c4) ▸
       at 0 1 (Bx3-10 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;310): 8 steps
lem-nat-1-BOX⟨2·310⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-310 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-320 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·310⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-310 ∷ []) (Bx1-320 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-10 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·20⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-10 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·20⟩ c4) ▸
       at 0 6 (Bx1-320 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;2410): 8 steps
lem-nat-1-BOX⟨3·2410⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-2410 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·2410⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-2410 ∷ []) (Bx3-1420 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-310 ∷ Toff324 ∷ CCZ234 ∷ Bx2-310 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-320 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·310⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-320 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·310⟩ c4) ▸
       at 0 6 (Bx3-1420 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;2;0;1): 3 steps
lem-nat-1-SBOX⟨3·2·0·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb3-2-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-0-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·2·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-2-0-1 ∷ []) (Sb3-1-0-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 0 1 (Sb3-1-0-2 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(3;2;0;1): 3 steps
lem-nat-1-SBOXd⟨3·2·0·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻3-2-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-1-0-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·2·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻3-2-0-1 ∷ []) (Sb⁻3-1-0-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 0 1 (Sb⁻3-1-0-2 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;2;41;0): 7 steps
lem-nat-1-SBOX⟨3·2·41·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb3-2-41-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·2·41·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-2-41-0 ∷ []) (Sb3-1-42-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx3-2410 ∷ Toff014 ∷ Sb3-2-0-1 ∷ Toff014 ∷ Sb⁻3-2-0-1 ∷ []) (refl) ▸
       at 0 2 (Bx3-1420 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2410⟩ c4) ▸
       at 1 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 2 2 (Sb3-1-0-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·2·0·1⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 4 2 (Sb⁻3-1-0-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·2·0·1⟩ c4) ▸
       at 0 5 (Sb3-1-42-0 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;10): 2 steps
lem-nat-2-BOX⟨2·10⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-10 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·10⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-10 ∷ []) (Bx3-10 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Bx2-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 0 1 (Bx3-10 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(1;230): 8 steps
lem-nat-2-BOX⟨1·230⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-230 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-320 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·230⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-230 ∷ []) (Bx1-320 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-10 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·10⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-10 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·10⟩ c4) ▸
       at 0 6 (Bx1-320 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;1430): 8 steps
lem-nat-2-BOX⟨2·1430⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·1430⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-1430 ∷ []) (Bx3-1420 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 2 2 (Bx1-320 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·230⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx1-320 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·230⟩ c4) ▸
       at 0 6 (Bx3-1420 ∷ []) (refl) ▸ done


-- nat 2 SBOX(2;1;0;3): 2 steps
lem-nat-2-SBOX⟨2·1·0·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb2-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-0-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·1·0·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-1-0-3 ∷ []) (Sb3-1-0-2 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb2-1-0-3 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 0 1 (Sb3-1-0-2 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOXd(2;1;0;3): 2 steps
lem-nat-2-SBOXd⟨2·1·0·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻2-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-1-0-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·1·0·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻2-1-0-3 ∷ []) (Sb⁻3-1-0-2 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb⁻2-1-0-3 ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 0 1 (Sb⁻3-1-0-2 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOX(2;1;43;0): 7 steps
lem-nat-2-SBOX⟨2·1·43·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb2-1-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·1·43·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-1-43-0 ∷ []) (Sb3-1-42-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx2-1430 ∷ Toff034 ∷ Sb2-1-0-3 ∷ Toff034 ∷ Sb⁻2-1-0-3 ∷ []) (refl) ▸
       at 0 2 (Bx3-1420 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·1430⟩ c4) ▸
       at 1 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 2 2 (Sb3-1-0-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·1·0·3⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 4 2 (Sb⁻3-1-0-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·1·0·3⟩ c4) ▸
       at 0 5 (Sb3-1-42-0 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;10): 2 steps
lem-nat-2-BOX⟨3·10⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-10 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·10⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-10 ∷ []) (Bx2-10 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Bx3-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 0 1 (Bx2-10 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(1;320): 8 steps
lem-nat-2-BOX⟨1·320⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-320 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-230 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·320⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-320 ∷ []) (Bx1-230 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-10 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·10⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-10 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·10⟩ c4) ▸
       at 0 6 (Bx1-230 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;1420): 8 steps
lem-nat-2-BOX⟨3·1420⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·1420⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-1420 ∷ []) (Bx2-1430 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 2 2 (Bx1-230 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·320⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx1-230 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·320⟩ c4) ▸
       at 0 6 (Bx2-1430 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;1;0;2): 2 steps
lem-nat-2-SBOX⟨3·1·0·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb3-1-0-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-0-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·1·0·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-1-0-2 ∷ []) (Sb2-1-0-3 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb3-1-0-2 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 0 1 (Sb2-1-0-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOXd(3;1;0;2): 2 steps
lem-nat-2-SBOXd⟨3·1·0·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻3-1-0-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-0-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·1·0·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻3-1-0-2 ∷ []) (Sb⁻2-1-0-3 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb⁻3-1-0-2 ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 0 1 (Sb⁻2-1-0-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOX(3;1;42;0): 7 steps
lem-nat-2-SBOX⟨3·1·42·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-43-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·1·42·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-1-42-0 ∷ []) (Sb2-1-43-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 0 2 (Bx2-1430 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·1420⟩ c4) ▸
       at 1 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 2 2 (Sb2-1-0-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·1·0·2⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 4 2 (Sb⁻2-1-0-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·1·0·2⟩ c4) ▸
       at 0 5 (Sb2-1-43-0 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;1;43;0): 7 steps
lem-nat-0-SBOX⟨2·1·43·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb2-1-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-43-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·1·43·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-1-43-0 ∷ []) (Sb2-0-43-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx2-1430 ∷ Toff034 ∷ Sb2-1-0-3 ∷ Toff034 ∷ Sb⁻2-1-0-3 ∷ []) (refl) ▸
       at 0 2 (Bx2-0431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1430⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 2 2 (Sb2-0-1-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·0·3⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 4 2 (Sb⁻2-0-1-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·1·0·3⟩ c4) ▸
       at 0 5 (Sb2-0-43-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;4;1;2): 3 steps
lem-nat-2-SBOX⟨0·4·1·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb0-4-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-1-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·4·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-4-1-2 ∷ []) (Sb0-4-1-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-4-1-3 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;4;1;3): 3 steps
lem-nat-2-SBOX⟨0·4·1·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb0-4-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-1-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·4·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-4-1-3 ∷ []) (Sb0-4-1-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-4-1-2 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;3;1;2): 3 steps
lem-nat-3-SBOX⟨0·3·1·2⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb0-3-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-1-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·3·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-3-1-2 ∷ []) (Sb0-4-1-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw34 ∷ []) (lem-nat-3-CS13 c4) ▸
       at 0 1 (Sb0-4-1-2 ∷ []) (refl) ▸ done


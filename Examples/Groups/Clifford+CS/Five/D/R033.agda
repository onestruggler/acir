{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R033 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-1-TOFF203 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013 ; lem-nat-1-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-1-TOFF103 ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-1-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-CCZ014 ; lem-nat-2-CZ13)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-0-BOX⟨3·04⟩ ; lem-nat-2-BOX⟨0·42⟩ ; lem-nat-2-BOX⟨0·43⟩ ; lem-nat-2-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-TOFF134 ; lem-nat-1-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-TOFF034 ; lem-nat-1-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-1-TOFF402 ; lem-nat-2-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-BOX⟨0·1432⟩ ; lem-nat-1-BOX⟨1·30⟩ ; lem-nat-1-BOX⟨2·30⟩)
open import Examples.Groups.Clifford+CS.Five.D.R024 using (lem-nat-0-BOX⟨3·02⟩)
open import Examples.Groups.Clifford+CS.Five.D.R031 using (lem-nat-0-BOX⟨0·31⟩ ; lem-nat-0-BOX⟨1·30⟩ ; lem-nat-1-BOX⟨0·31⟩ ; lem-nat-1-BOX⟨0·32⟩)
open import Examples.Groups.Clifford+CS.Five.D.R032 using (lem-nat-0-BOX⟨1·342⟩)
-- nat 0 BOX(3;1042): 8 steps
lem-nat-0-BOX⟨3·1042⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·1042⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-1042 ∷ []) (Bx3-0142 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-342 ∷ Toff301 ∷ CCZ013 ∷ Bx1-342 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·342⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·342⟩ c4) ▸
       at 0 6 (Bx3-0142 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;21): 3 steps
lem-nat-1-BOX⟨3·21⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-12 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·21⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-21 ∷ []) (Bx3-12 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ12 ∷ []) (CZ12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx3-12 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;341): 8 steps
lem-nat-1-BOX⟨2·341⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-341 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-342 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·341⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-341 ∷ []) (Bx1-342 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·21⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·21⟩ c4) ▸
       at 0 6 (Bx1-342 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;2041): 8 steps
lem-nat-1-BOX⟨3·2041⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·2041⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-2041 ∷ []) (Bx3-1042 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-341 ∷ Toff302 ∷ CCZ023 ∷ Bx2-341 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 2 2 (Bx1-342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·341⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx1-342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·341⟩ c4) ▸
       at 0 6 (Bx3-1042 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;301): 8 steps
lem-nat-1-BOX⟨2·301⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-301 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-302 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·301⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-301 ∷ []) (Bx1-302 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 2 2 (Bx3-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·21⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx3-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·21⟩ c4) ▸
       at 0 6 (Bx1-302 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;2401): 8 steps
lem-nat-1-BOX⟨3·2401⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·2401⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-2401 ∷ []) (Bx3-1402 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-301 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-302 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·301⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-302 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·301⟩ c4) ▸
       at 0 6 (Bx3-1402 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;342): 8 steps
lem-nat-0-BOX⟨0·342⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-342 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·342⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-342 ∷ []) (Bx1-342 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 2 2 (Bx3-12 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·02⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx3-12 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·02⟩ c4) ▸
       at 0 6 (Bx1-342 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;0142): 8 steps
lem-nat-0-BOX⟨3·0142⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·0142⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-0142 ∷ []) (Bx3-1042 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·342⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·342⟩ c4) ▸
       at 0 6 (Bx3-1042 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;324): 8 steps
lem-nat-0-BOX⟨0·324⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-324 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·324⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-324 ∷ []) (Bx1-324 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff023 ∷ []) (Toff123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·04⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff023 ∷ []) (Toff123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·04⟩ c4) ▸
       at 0 6 (Bx1-324 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;0124): 8 steps
lem-nat-0-BOX⟨3·0124⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·0124⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-0124 ∷ []) (Bx3-1024 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·324⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·324⟩ c4) ▸
       at 0 6 (Bx3-1024 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;14): 3 steps
lem-nat-1-BOX⟨3·14⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-24 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·14⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-14 ∷ []) (Bx3-24 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CZ14 ∷ []) (CZ24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx3-24 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;324): 8 steps
lem-nat-1-BOX⟨1·324⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-314 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·324⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-324 ∷ []) (Bx2-314 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff123 ∷ []) (Toff213 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-24 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·14⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff123 ∷ []) (Toff213 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-24 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·14⟩ c4) ▸
       at 0 6 (Bx2-314 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;1024): 8 steps
lem-nat-1-BOX⟨3·1024⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·1024⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-1024 ∷ []) (Bx3-2014 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 2 2 (Bx2-314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·324⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx2-314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·324⟩ c4) ▸
       at 0 6 (Bx3-2014 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;24): 3 steps
lem-nat-1-BOX⟨3·24⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-14 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·24⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-24 ∷ []) (Bx3-14 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CZ24 ∷ []) (CZ14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx3-14 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;314): 8 steps
lem-nat-1-BOX⟨2·314⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-314 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-324 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·314⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-314 ∷ []) (Bx1-324 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·24⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·24⟩ c4) ▸
       at 0 6 (Bx1-324 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;2014): 8 steps
lem-nat-1-BOX⟨3·2014⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·2014⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-2014 ∷ []) (Bx3-1024 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 2 2 (Bx1-324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·314⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx1-324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·314⟩ c4) ▸
       at 0 6 (Bx3-1024 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;31): 3 steps
lem-nat-2-BOX⟨2·31⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-21 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·31⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-31 ∷ []) (Bx3-21 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw23 ∷ []) (lem-nat-2-CZ13 c4) ▸
       at 0 1 (Bx3-21 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;201): 8 steps
lem-nat-2-BOX⟨3·201⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-201 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-301 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·201⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-201 ∷ []) (Bx2-301 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff203 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-21 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·31⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-21 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·31⟩ c4) ▸
       at 0 6 (Bx2-301 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;3401): 8 steps
lem-nat-2-BOX⟨2·3401⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·3401⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-3401 ∷ []) (Bx3-2401 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-301 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·201⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-301 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·201⟩ c4) ▸
       at 0 6 (Bx3-2401 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;1;2;3): 3 steps
lem-nat-0-SBOX⟨0·1·2·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-1-2-3 ∷ []) (Sb1-0-2-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb1-0-2-3 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(0;1;2;3): 3 steps
lem-nat-0-SBOXd⟨0·1·2·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·1·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻1-0-2-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;1;43;2): 7 steps
lem-nat-0-SBOX⟨0·1·43·2⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·43·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-1-43-2 ∷ []) (Sb1-0-43-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 2 2 (Sb1-0-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·2·3⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 4 2 (Sb⁻1-0-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 0 5 (Sb1-0-43-2 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;42): 3 steps
lem-nat-1-BOX⟨0·42⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-41 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·42⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-42 ∷ []) (Bx0-41 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CZ24 ∷ []) (CZ14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-41 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;032): 8 steps
lem-nat-1-BOX⟨4·032⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-032 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-031 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·032⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-032 ∷ []) (Bx4-031 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 2 2 (Bx0-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·42⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx0-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·42⟩ c4) ▸
       at 0 6 (Bx4-031 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;4132): 8 steps
lem-nat-1-BOX⟨0·4132⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·4132⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-4132 ∷ []) (Bx0-4231 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 2 2 (Bx4-031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·032⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx4-031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·032⟩ c4) ▸
       at 0 6 (Bx0-4231 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;41): 3 steps
lem-nat-1-BOX⟨0·41⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-42 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·41⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-41 ∷ []) (Bx0-42 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CZ14 ∷ []) (CZ24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-42 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;031): 8 steps
lem-nat-1-BOX⟨4·031⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-032 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·031⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-031 ∷ []) (Bx4-032 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 2 2 (Bx0-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·41⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx0-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·41⟩ c4) ▸
       at 0 6 (Bx4-032 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;4231): 8 steps
lem-nat-1-BOX⟨0·4231⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·4231⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-4231 ∷ []) (Bx0-4132 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 2 2 (Bx4-032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·031⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx4-032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·031⟩ c4) ▸
       at 0 6 (Bx0-4132 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;023): 8 steps
lem-nat-1-BOX⟨4·023⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-013 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·023⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-023 ∷ []) (Bx4-013 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 2 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 3 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 0 6 (Bx4-013 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;4123): 8 steps
lem-nat-1-BOX⟨0·4123⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·4123⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-4123 ∷ []) (Bx0-4213 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 2 2 (Bx4-013 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·023⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx4-013 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·023⟩ c4) ▸
       at 0 6 (Bx0-4213 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;013): 8 steps
lem-nat-2-BOX⟨4·013⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-013 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-012 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·013⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-013 ∷ []) (Bx4-012 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 2 2 (Bx0-42 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·43⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx0-42 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·43⟩ c4) ▸
       at 0 6 (Bx4-012 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;4213): 8 steps
lem-nat-2-BOX⟨0·4213⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·4213⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-4213 ∷ []) (Bx0-4312 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 2 2 (Bx4-012 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·013⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx4-012 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·013⟩ c4) ▸
       at 0 6 (Bx0-4312 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;012): 8 steps
lem-nat-1-BOX⟨4·012⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-021 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·012⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-012 ∷ []) (Bx4-021 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 2 2 (Bx0-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·42⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx0-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·42⟩ c4) ▸
       at 0 6 (Bx4-021 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;4312): 8 steps
lem-nat-1-BOX⟨0·4312⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·4312⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-4312 ∷ []) (Bx0-4321 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Bx4-021 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·012⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx4-021 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·012⟩ c4) ▸
       at 0 6 (Bx0-4321 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;012): 8 steps
lem-nat-2-BOX⟨4·012⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-013 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·012⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-012 ∷ []) (Bx4-013 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 2 2 (Bx0-43 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·42⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx0-43 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·42⟩ c4) ▸
       at 0 6 (Bx4-013 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;4312): 8 steps
lem-nat-2-BOX⟨0·4312⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·4312⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-4312 ∷ []) (Bx0-4213 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 2 2 (Bx4-013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·012⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx4-013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·012⟩ c4) ▸
       at 0 6 (Bx0-4213 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;021): 8 steps
lem-nat-1-BOX⟨4·021⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-021 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-012 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·021⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-021 ∷ []) (Bx4-012 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 2 2 (Bx0-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·41⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx0-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·41⟩ c4) ▸
       at 0 6 (Bx4-012 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;4321): 8 steps
lem-nat-1-BOX⟨0·4321⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·4321⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-4321 ∷ []) (Bx0-4312 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Bx4-012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·021⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx4-012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·021⟩ c4) ▸
       at 0 6 (Bx0-4312 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;41): 3 steps
lem-nat-2-BOX⟨0·41⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-41 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·41⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-41 ∷ []) (Bx0-41 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ14 ∷ []) (CZ14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-41 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;031): 8 steps
lem-nat-2-BOX⟨4·031⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-021 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·031⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-031 ∷ []) (Bx4-021 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 2 2 (Bx0-41 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·41⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx0-41 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·41⟩ c4) ▸
       at 0 6 (Bx4-021 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;4231): 8 steps
lem-nat-2-BOX⟨0·4231⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·4231⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-4231 ∷ []) (Bx0-4321 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 2 2 (Bx4-021 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·031⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx4-021 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·031⟩ c4) ▸
       at 0 6 (Bx0-4321 ∷ []) (refl) ▸ done


-- resp CX40 at 3: 20 steps
lem-resp-CX40-at-3 : Complete 4 → ⟪ (CX40 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX40-at-3 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX40 ∷ []) (Sw23 ∷ CX40 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 3 2 (Sw34 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Swap ↑)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ CX40 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ CX30 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 2 2 (Sw12 ∷ CX30 ∷ []) (lw4 c4 (CX30 ∷ Sw12 ∷ []) (Sw12 ∷ CX30 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 2 3 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ CX30 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 4 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 3 2 (Sw01 ∷ CX31 ∷ []) (lw4 c4 (CX30 ∷ Sw01 ∷ []) (Sw01 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 3 3 (CX41 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOX(1;304): 8 steps
lem-nat-1-BOX⟨1·304⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-304 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·304⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-304 ∷ []) (Bx2-304 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 2 2 (Bx3-24 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·14⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx3-24 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·14⟩ c4) ▸
       at 0 6 (Bx2-304 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;1204): 8 steps
lem-nat-1-BOX⟨3·1204⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·1204⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-1204 ∷ []) (Bx3-2104 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-304 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·304⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-304 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·304⟩ c4) ▸
       at 0 6 (Bx3-2104 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;304): 8 steps
lem-nat-0-BOX⟨2·304⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-314 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·304⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-304 ∷ []) (Bx2-314 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 3 2 (Toff213 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 0 6 (Bx2-314 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;2104): 8 steps
lem-nat-0-BOX⟨3·2104⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·2104⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-2104 ∷ []) (Bx3-2014 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-304 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·304⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·304⟩ c4) ▸
       at 0 6 (Bx3-2014 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;314): 8 steps
lem-nat-0-BOX⟨2·314⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-304 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·314⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-314 ∷ []) (Bx2-304 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff203 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 3 2 (Toff203 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 0 6 (Bx2-304 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;2014): 8 steps
lem-nat-0-BOX⟨3·2014⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·2014⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-2014 ∷ []) (Bx3-2104 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·314⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·314⟩ c4) ▸
       at 0 6 (Bx3-2104 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;304): 8 steps
lem-nat-1-BOX⟨2·304⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-304 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·304⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-304 ∷ []) (Bx1-304 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 2 2 (Bx3-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·24⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx3-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·24⟩ c4) ▸
       at 0 6 (Bx1-304 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;2104): 8 steps
lem-nat-1-BOX⟨3·2104⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·2104⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-2104 ∷ []) (Bx3-1204 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-304 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-304 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·304⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-304 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·304⟩ c4) ▸
       at 0 6 (Bx3-1204 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;012): 8 steps
lem-nat-1-BOX⟨3·012⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-021 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·012⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-012 ∷ []) (Bx3-021 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 2 2 (Bx0-31 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·32⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx0-31 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·32⟩ c4) ▸
       at 0 6 (Bx3-021 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;3412): 8 steps
lem-nat-1-BOX⟨0·3412⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·3412⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-3412 ∷ []) (Bx0-3421 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Bx3-021 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·012⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx3-021 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·012⟩ c4) ▸
       at 0 6 (Bx0-3421 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;120): 8 steps
lem-nat-1-BOX⟨3·120⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-210 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·120⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-120 ∷ []) (Bx3-210 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-30 ∷ Toff312 ∷ CCZ123 ∷ Bx1-30 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-30 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·30⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-30 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·30⟩ c4) ▸
       at 0 6 (Bx3-210 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;3420): 8 steps
lem-nat-1-BOX⟨1·3420⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-3420 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·3420⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-3420 ∷ []) (Bx2-3410 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-120 ∷ Toff134 ∷ CCZ134 ∷ Bx3-120 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-210 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·120⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-210 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·120⟩ c4) ▸
       at 0 6 (Bx2-3410 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;210): 8 steps
lem-nat-1-BOX⟨3·210⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-120 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·210⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-210 ∷ []) (Bx3-120 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-30 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·30⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-30 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·30⟩ c4) ▸
       at 0 6 (Bx3-120 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;3410): 8 steps
lem-nat-1-BOX⟨2·3410⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3420 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·3410⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-3410 ∷ []) (Bx1-3420 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-210 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-120 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·210⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-120 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·210⟩ c4) ▸
       at 0 6 (Bx1-3420 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;021): 8 steps
lem-nat-0-BOX⟨3·021⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-120 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·021⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-021 ∷ []) (Bx3-120 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-30 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·31⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-30 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·31⟩ c4) ▸
       at 0 6 (Bx3-120 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;3421): 8 steps
lem-nat-0-BOX⟨0·3421⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3420 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·3421⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-3421 ∷ []) (Bx1-3420 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 2 2 (Bx3-120 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·021⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx3-120 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·021⟩ c4) ▸
       at 0 6 (Bx1-3420 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;120): 8 steps
lem-nat-0-BOX⟨3·120⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-021 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·120⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-120 ∷ []) (Bx3-021 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-30 ∷ Toff312 ∷ CCZ123 ∷ Bx1-30 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-31 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·30⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-31 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·30⟩ c4) ▸
       at 0 6 (Bx3-021 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;3420): 8 steps
lem-nat-0-BOX⟨1·3420⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-3420 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·3420⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-3420 ∷ []) (Bx0-3421 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-120 ∷ Toff134 ∷ CCZ134 ∷ Bx3-120 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 2 2 (Bx3-021 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·120⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx3-021 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·120⟩ c4) ▸
       at 0 6 (Bx0-3421 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;021): 8 steps
lem-nat-1-BOX⟨3·021⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-012 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·021⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-021 ∷ []) (Bx3-012 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 2 2 (Bx0-32 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·31⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx0-32 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·31⟩ c4) ▸
       at 0 6 (Bx3-012 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;3421): 8 steps
lem-nat-1-BOX⟨0·3421⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·3421⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-3421 ∷ []) (Bx0-3412 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Bx3-012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·021⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx3-012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·021⟩ c4) ▸
       at 0 6 (Bx0-3412 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;0;2;3): 3 steps
lem-nat-0-SBOX⟨1·0·2·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·0·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-0-2-3 ∷ []) (Sb0-1-2-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(1;0;2;3): 3 steps
lem-nat-0-SBOXd⟨1·0·2·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·0·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


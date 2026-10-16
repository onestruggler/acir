{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D219 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym12-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym12-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-SBsym-at0113203442 ; lem-T312-beta-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D081 using (lem-sym23-at0310243241)
open import Examples.Groups.Clifford+CS.Five.D.D082 using (lem-sym23-at03103441)
open import Examples.Groups.Clifford+CS.Five.D.D136 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D153 using (lem-sym34-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D157 using (lem-sym23-at12233441 ; lem-sym23-at122441 ; lem-sym34-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D174 using (lem-c124-beta-at03103441)
open import Examples.Groups.Clifford+CS.Five.D.D218 using (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·4213⟩ ; lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩ ; lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at243243)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-1-CCZ023 ; lem-nat-2-BOX⟨0·3412⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-BOX⟨0·1423⟩ ; lem-nat-1-CCZ013 ; lem-nat-2-BOX⟨0·2413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-2-SBOX⟨0·1·42·3⟩ ; lem-nat-2-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-SBOX⟨0·2·43·1⟩ ; lem-nat-0-SBOX⟨1·2·43·0⟩ ; lem-nat-1-SBOX⟨0·1·43·2⟩ ; lem-nat-1-SBOX⟨0·2·43·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R025 using (lem-nat-1-BOX⟨0·4213⟩)
open import Examples.Groups.Clifford+CS.Five.D.R032 using (lem-nat-0-BOX⟨3·0421⟩ ; lem-nat-0-BOX⟨3·1420⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-1-BOX⟨0·4123⟩ ; lem-nat-2-BOX⟨0·4213⟩ ; lem-nat-2-BOX⟨0·4312⟩)
open import Examples.Groups.Clifford+CS.Five.D.R037 using (lem-nat-1-SBOX⟨0·1·3·2⟩ ; lem-nat-1-SBOX⟨0·2·3·1⟩ ; lem-nat-1-SBOXd⟨0·1·3·2⟩ ; lem-nat-1-SBOXd⟨0·2·3·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R040 using (lem-nat-1-SBOX⟨2·1·43·0⟩ ; lem-nat-2-SBOX⟨2·1·43·0⟩ ; lem-nat-2-SBOX⟨3·1·42·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R041 using (lem-nat-0-BOX⟨3·0241⟩ ; lem-nat-0-BOX⟨3·1240⟩ ; lem-nat-1-SBOX⟨1·2·43·0⟩ ; lem-nat-2-SBOX⟨0·2·3·1⟩ ; lem-nat-2-SBOX⟨0·3·2·1⟩ ; lem-nat-2-SBOX⟨0·4·2·1⟩ ; lem-nat-2-SBOX⟨0·4·3·1⟩ ; lem-nat-2-SBOXd⟨0·2·3·1⟩ ; lem-nat-2-SBOXd⟨0·3·2·1⟩ ; lem-nat-2-SBOXd⟨0·4·2·1⟩ ; lem-nat-2-SBOXd⟨0·4·3·1⟩ ; lem-nat-3-BOX⟨0·3412⟩ ; lem-nat-3-BOX⟨0·4312⟩ ; lem-nat-3-SBOX⟨0·3·2·1⟩ ; lem-nat-3-SBOX⟨0·4·2·1⟩ ; lem-nat-3-SBOXd⟨0·3·2·1⟩ ; lem-nat-3-SBOXd⟨0·4·2·1⟩)
-- auto SBOXd(0;1;2;3) | BOX(0;2413) @2442: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2442 : Complete 4 → ⟪ (Sb⁻0-1-4-3 ∷ Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-3 ∷ Bx0-4213 ∷ []) (Bx0-4213 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx0-4312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4213⟩ c4) ▸
       at 1 2 (Bx0-4312 ∷ Sb⁻0-1-4-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at243243 c4) ▸
       at 0 2 (Bx0-4213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4312⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @143143: 5 steps
lem-sym12-at143143 : Complete 4 → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-sym12-at143143 c4 = run b0
  where
  b0 : Chain (Bx0-4213 ∷ []) (Bx0-2413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·4213⟩ c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 0 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @12243143: 5 steps
lem-sym12-at12243143 : Complete 4 → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-sym12-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ []) (Bx0-4213 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ c4) ▸
       at 1 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 0 2 (Bx0-4213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·4123⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;2413) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2332 : Complete 4 → ⟪ (Sb0-1-3-2 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-3-2 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ Sb0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ c4) ▸
       at 1 2 (Bx0-2413 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩ c4) ▸
       at 0 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ c4) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;2413) @243243: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at243243 : Complete 4 → ⟪ (Sb0-1-4-2 ∷ Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-2 ∷ Bx0-4312 ∷ []) (Bx0-4312 ∷ Sb0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx0-3412 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4312⟩ c4) ▸
       at 1 2 (Bx0-3412 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2332 c4) ▸
       at 0 2 (Bx0-4312 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3412⟩ c4) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;2413) @2442: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2442 : Complete 4 → ⟪ (Sb0-1-4-3 ∷ Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-3 ∷ Bx0-4213 ∷ []) (Bx0-4213 ∷ Sb0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx0-4312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4213⟩ c4) ▸
       at 1 2 (Bx0-4312 ∷ Sb0-1-4-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at243243 c4) ▸
       at 0 2 (Bx0-4213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4312⟩ c4) ▸
       at 1 2 (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;4213): 30 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb0-1-23-4 ∷ Bx0-4213 ∷ []) (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Bx0-2431 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 2 (Bx0-4213 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2442 c4) ▸
       at 5 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-2413 ∷ []) (lem-sym12-at143143 c4) ▸
       at 4 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸
       at 4 1 (Bx0-2341 ∷ []) (lem-sym23-at122441 c4) ▸
       at 3 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-T312-beta-at12233441 c4) ▸
       at 3 1 (Bx0-2431 ∷ []) (lem-sym23-at12233441 c4) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Bx0-2431 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx0-1234 ∷ Bx0-2341 ∷ CCZ123 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b1 = at 3 1 (Bx0-2413 ∷ []) (lem-sym34-at122441 c4) ▸
       at 3 1 (Bx0-4213 ∷ []) (lem-sym12-at12243143 c4) ▸
       at 2 2 (Bx0-4213 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2442 c4) ▸
       at 3 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-2413 ∷ []) (lem-sym12-at143143 c4) ▸
       at 2 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸
       at 2 1 (Bx0-2341 ∷ []) (lem-sym23-at122441 c4) ▸
       at 1 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-T312-beta-at12233441 c4) ▸ done

  b2 : Chain (Bx0-1234 ∷ Bx0-2341 ∷ CCZ123 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx0-4213 ∷ Bx0-1234 ∷ CCZ123 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ123 ∷ [])
  b2 = at 1 1 (Bx0-2431 ∷ []) (lem-sym23-at12233441 c4) ▸
       at 1 1 (Bx0-2413 ∷ []) (lem-sym34-at122441 c4) ▸
       at 1 1 (Bx0-4213 ∷ []) (lem-sym12-at12243143 c4) ▸
       at 0 2 (Bx0-4213 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·4213⟩ c4) ▸
       at 7 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 3 (Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ Toff423 ∷ CS14⁻ ∷ []) (Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14 ∷ []) (refl) ▸ done

  b3 : Chain (Bx0-4213 ∷ Bx0-1234 ∷ CCZ123 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ123 ∷ []) (Bx0-4213 ∷ Sb0-1-23-4 ∷ [])
  b3 = at 6 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 5 (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 6 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- sym23 @03243240: 5 steps
lem-sym23-at03243240 : Complete 4 → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-sym23-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ []) (Bx3-1240 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ c4) ▸
       at 1 1 (Bx3-0241 ∷ []) (lem-sym23-at0310243241 c4) ▸
       at 0 2 (Bx3-1240 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0241⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- c124-beta @033440: 7 steps
lem-c124-beta-at033440 : Complete 4 → ⟪ (CCZ012 ∷ Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ CCZ012 ∷ []) ⟫ʷ
lem-c124-beta-at033440 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-1240 ∷ []) (Bx3-1240 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-0241 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1240⟩ c4) ▸
       at 1 2 (Bx3-0241 ∷ CCZ012 ∷ []) (lem-c124-beta-at03103441 c4) ▸
       at 0 2 (Bx3-1240 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0241⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @033440: 5 steps
lem-sym23-at033440 : Complete 4 → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-sym23-at033440 c4 = run b0
  where
  b0 : Chain (Bx3-1240 ∷ []) (Bx3-1420 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0241 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1240⟩ c4) ▸
       at 1 1 (Bx3-0421 ∷ []) (lem-sym23-at03103441 c4) ▸
       at 0 2 (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;1420): 5 steps
lem-auto-CCZ012-∣-BOX⟨3·1420⟩ : Complete 4 → ⟪ (CCZ012 ∷ Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·1420⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-1420 ∷ []) (Bx3-1420 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx3-1240 ∷ []) (lem-sym23-at03243240 c4) ▸
       at 0 2 (Bx3-1240 ∷ CCZ012 ∷ []) (lem-c124-beta-at033440 c4) ▸
       at 0 1 (Bx3-1420 ∷ []) (lem-sym23-at033440 c4) ▸
       at 1 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;1;42;0): 9 steps
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩ : Complete 4 → ⟪ (CCZ012 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Sb3-1-42-0 ∷ []) (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 0 2 (Bx3-1420 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·1420⟩ c4) ▸
       at 3 1 (CS01 ∷ []) (refl) ▸
       at 1 4 (Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ []) (Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb3-1-0-2 ∷ []) (refl) ▸
       at 5 1 (CS01⁻ ∷ []) (refl) ▸
       at 4 2 (CS01⁻ ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻3-1-0-2 ∷ []) (refl) ▸ done

  b1 : Chain (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ CCZ012 ∷ []) (Sb3-1-42-0 ∷ CCZ012 ∷ [])
  b1 = at 0 5 (Sb3-1-42-0 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;4;3;1): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Sb0-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-3-1 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb0-4-3-1 ∷ []) (Sb0-4-3-1 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS34 ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb0-4-3-1 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;4;3;1): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Sb⁻0-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-3-1 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb⁻0-4-3-1 ∷ []) (Sb⁻0-4-3-1 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS34⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb⁻0-4-3-1 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;4213) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Bx0-4312 ∷ []) (Bx0-4312 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Bx0-4213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4312⟩ c4) ▸
       at 1 2 (Bx0-4213 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩ c4) ▸
       at 0 2 (Bx0-4312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4213⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;4213) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Bx0-4312 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3412⟩ c4) ▸
       at 1 2 (Bx0-4312 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at2332 c4) ▸
       at 0 2 (Bx0-3412 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4312⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;4213) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at2442 : Complete 4 → ⟪ (Sb0-1-43-2 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ c4) ▸
       at 1 2 (Bx0-3412 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at243243 c4) ▸
       at 0 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;4213) @122441: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at122441 : Complete 4 → ⟪ (Sb0-2-43-1 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at122441 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 2 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Bx0-2413 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at2442 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ c4) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;1;42;0) @2332: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at2332 : Complete 4 → ⟪ (CCZ013 ∷ Sb2-1-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-43-0 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at2332 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Sb2-1-43-0 ∷ []) (Sb2-1-43-0 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Sb3-1-42-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·1·43·0⟩ c4) ▸
       at 1 2 (Sb3-1-42-0 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩ c4) ▸
       at 0 2 (Sb2-1-43-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·1·42·0⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;1;42;0) @122331: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at122331 : Complete 4 → ⟪ (CCZ023 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at122331 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Sb1-2-43-0 ∷ []) (Sb1-2-43-0 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Sb2-1-43-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·43·0⟩ c4) ▸
       at 1 2 (Sb2-1-43-0 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at2332 c4) ▸
       at 0 2 (Sb1-2-43-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·43·0⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;1;42;0) @01122330: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at01122330 : Complete 4 → ⟪ (CCZ123 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CCZ123 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at01122330 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ c4) ▸
       at 1 2 (Sb1-2-43-0 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at122331 c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;4;3;1) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Sb0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-2-1 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb0-4-2-1 ∷ []) (Sb0-4-2-1 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Sb0-4-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·4·2·1⟩ c4) ▸
       at 1 2 (Sb0-4-3-1 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩ c4) ▸
       at 0 2 (Sb0-4-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·4·3·1⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;4;3;1) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Sb0-3-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-2-1 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb0-3-2-1 ∷ []) (Sb0-3-2-1 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Sb0-4-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·3·2·1⟩ c4) ▸
       at 1 2 (Sb0-4-2-1 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at2332 c4) ▸
       at 0 2 (Sb0-3-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·4·2·1⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;4;3;1) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at2442 : Complete 4 → ⟪ (Sb0-1-43-2 ∷ Sb0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-3-1 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Sb0-2-3-1 ∷ []) (Sb0-2-3-1 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 (Sb0-3-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·2·3·1⟩ c4) ▸
       at 1 2 (Sb0-3-2-1 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at243243 c4) ▸
       at 0 2 (Sb0-2-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·3·2·1⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;4;3;1) @122441: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at122441 : Complete 4 → ⟪ (Sb0-2-43-1 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at122441 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-3-2 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 2 2 (Sb0-2-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·3·2⟩ c4) ▸
       at 1 2 (Sb0-2-3-1 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at2442 c4) ▸
       at 0 2 (Sb0-1-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·3·1⟩ c4) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;4;3;1) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Sb⁻0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-2-1 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb⁻0-4-2-1 ∷ []) (Sb⁻0-4-2-1 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Sb⁻0-4-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·4·2·1⟩ c4) ▸
       at 1 2 (Sb⁻0-4-3-1 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩ c4) ▸
       at 0 2 (Sb⁻0-4-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·4·3·1⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;4;3;1) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Sb⁻0-3-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-2-1 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb⁻0-3-2-1 ∷ []) (Sb⁻0-3-2-1 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Sb⁻0-4-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·3·2·1⟩ c4) ▸
       at 1 2 (Sb⁻0-4-2-1 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at2332 c4) ▸
       at 0 2 (Sb⁻0-3-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·4·2·1⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;4;3;1) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at2442 : Complete 4 → ⟪ (Sb0-1-43-2 ∷ Sb⁻0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-3-1 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻0-2-3-1 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 (Sb⁻0-3-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·2·3·1⟩ c4) ▸
       at 1 2 (Sb⁻0-3-2-1 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at243243 c4) ▸
       at 0 2 (Sb⁻0-2-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·3·2·1⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;4;3;1) @122441: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at122441 : Complete 4 → ⟪ (Sb0-2-43-1 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at122441 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 2 2 (Sb⁻0-2-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 1 2 (Sb⁻0-2-3-1 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at2442 c4) ▸
       at 0 2 (Sb⁻0-1-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·3·1⟩ c4) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D185 where

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
open import Examples.Groups.Clifford+CS.Five.D.D174 using (lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩ ; lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1243⟩-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·3·4⟩-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·3·4⟩-at243243)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-SBOX⟨0·1·3·2⟩ ; lem-nat-0-SBOX⟨1·0·3·2⟩ ; lem-nat-0-SBOXd⟨0·1·3·2⟩ ; lem-nat-0-SBOXd⟨1·0·3·2⟩ ; lem-nat-2-BOX⟨0·1432⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-2-SBOX⟨3·0·42·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-BOX⟨0·1423⟩ ; lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-2-SBOX⟨0·1·42·3⟩ ; lem-nat-2-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-1-SBOX⟨1·0·43·2⟩ ; lem-nat-1-SBOX⟨2·0·43·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-0-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R034 using (lem-nat-0-SBOX⟨1·0·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R039 using (lem-nat-2-SBOX⟨2·0·43·1⟩)
-- auto SBOX(0;1;23;4) | BOX(0;1243) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1243⟩-at2442 : Complete 4 → ⟪ (Sb0-1-43-2 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1243⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Bx0-1432 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1243⟩-at243243 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;1243) @01102442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1243⟩-at01102442 : Complete 4 → ⟪ (Sb1-0-43-2 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1243⟩-at01102442 c4 = run b0
  where
  b0 : Chain (Sb1-0-43-2 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ Sb1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Bx0-1423 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1243⟩-at2442 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;0;42;1) @2332: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩-at2332 : Complete 4 → ⟪ (CCZ013 ∷ Sb2-0-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-43-1 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩-at2332 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Sb2-0-43-1 ∷ []) (Sb2-0-43-1 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Sb3-0-42-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·43·1⟩ c4) ▸
       at 1 2 (Sb3-0-42-1 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩ c4) ▸
       at 0 2 (Sb2-0-43-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·42·1⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;0;42;1) @122331: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩-at122331 : Complete 4 → ⟪ (CCZ023 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩-at122331 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Sb2-0-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·43·2⟩ c4) ▸
       at 1 2 (Sb2-0-43-1 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩-at2332 c4) ▸
       at 0 2 (Sb1-0-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·43·1⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;1;3;4) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·3·4⟩-at2442 : Complete 4 → ⟪ (Sb0-1-43-2 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·3·4⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-3-2 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ c4) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·3·4⟩-at243243 c4) ▸
       at 0 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;1;3;4) @01102442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·3·4⟩-at01102442 : Complete 4 → ⟪ (Sb1-0-43-2 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-2 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·3·4⟩-at01102442 c4 = run b0
  where
  b0 : Chain (Sb1-0-43-2 ∷ Sb1-0-3-2 ∷ []) (Sb1-0-3-2 ∷ Sb1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 2 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ c4) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·3·4⟩-at2442 c4) ▸
       at 0 2 (Sb1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·3·2⟩ c4) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;1;3;4) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·3·4⟩-at2442 : Complete 4 → ⟪ (Sb0-1-43-2 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·3·4⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·3·4⟩-at243243 c4) ▸
       at 0 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;1;3;4) @01102442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·3·4⟩-at01102442 : Complete 4 → ⟪ (Sb1-0-43-2 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-2 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·3·4⟩-at01102442 c4 = run b0
  where
  b0 : Chain (Sb1-0-43-2 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻1-0-3-2 ∷ Sb1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 2 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ c4) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·3·4⟩-at2442 c4) ▸
       at 0 2 (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


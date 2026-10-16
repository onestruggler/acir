{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D228 where

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
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-BOXd-BOX-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D224 using (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at243243 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D226 using (lem-AX-SB-at12213443)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-SBOX⟨0·1·3·2⟩ ; lem-nat-0-SBOX⟨1·0·3·2⟩ ; lem-nat-0-SBOXd⟨0·1·3·2⟩ ; lem-nat-0-SBOXd⟨1·0·3·2⟩ ; lem-nat-2-CS02 ; lem-nat-2-SBOX⟨1·0·2·3⟩ ; lem-nat-2-SBOXd⟨1·0·2·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-BOX⟨0·1423⟩ ; lem-nat-2-CS03)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-2-SBOX⟨0·1·42·3⟩ ; lem-nat-2-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-BOX⟨0·1432⟩ ; lem-nat-1-BOX⟨1·0432⟩)
open import Examples.Groups.Clifford+CS.Five.D.R022 using (lem-nat-2-SBOX⟨1·0·3·2⟩ ; lem-nat-2-SBOXd⟨1·0·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R043 using (lem-nat-0-BOXd⟨1·0432⟩ ; lem-nat-0-SBOXd⟨0·1·43·2⟩ ; lem-nat-0-SBOXd⟨1·0·43·2⟩ ; lem-nat-1-BOXd⟨2·0431⟩ ; lem-nat-2-BOXd⟨0·1432⟩ ; lem-nat-2-SBOXd⟨0·1·42·3⟩ ; lem-nat-2-SBOXd⟨0·1·43·2⟩)
-- AX-SB @13213442: 7 steps
lem-AX-SB-at13213442 : Complete 4 → ⟪ (CS03 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS03 ∷ []) ⟫ʷ
lem-AX-SB-at13213442 c4 = run b0
  where
  b0 : Chain (CS03 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS03 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ CS02 ∷ []) (lem-AX-SB-at12213443 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @2442: 5 steps
lem-BOXd-BOX-at2442 : Complete 4 → ⟪ (Bx⁻0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-BOXd-BOX-at2442 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1432 ∷ []) (Bx0-1432 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1432⟩ c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-BOXd-BOX-at243243 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @01102442: 5 steps
lem-BOXd-BOX-at01102442 : Complete 4 → ⟪ (Bx⁻1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ []) ⟫ʷ
lem-BOXd-BOX-at01102442 c4 = run b0
  where
  b0 : Chain (Bx⁻1-0432 ∷ []) (Bx1-0432 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0432⟩ c4) ▸
       at 1 1 (Bx0-1432 ∷ []) (lem-BOXd-BOX-at2442 c4) ▸
       at 0 2 (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @02102441: 5 steps
lem-BOXd-BOX-at02102441 : Complete 4 → ⟪ (Bx⁻2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-BOXd-BOX-at02102441 c4 = run b0
  where
  b0 : Chain (Bx⁻2-0431 ∷ []) (Bx2-0431 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻1-0432 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0431⟩ c4) ▸
       at 1 1 (Bx1-0432 ∷ []) (lem-BOXd-BOX-at01102442 c4) ▸
       at 0 2 (Bx2-0431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0432⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ143 @2442: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at2442 : Complete 4 → ⟪ (Sb⁻0-1-43-2 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sb⁻0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at2442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-43-2 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sb⁻0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·43·2⟩ c4) ▸
       at 2 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at243243 c4) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ143 @01102442: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at01102442 : Complete 4 → ⟪ (Sb⁻1-0-43-2 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb⁻1-0-43-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at01102442 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-43-2 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb⁻1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·43·2⟩ c4) ▸
       at 2 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ Sb⁻0-1-43-2 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at2442 c4) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOX(1;0;3;4) @2442: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2442 : Complete 4 → ⟪ (Sb⁻0-1-43-2 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-2 ∷ Sb⁻0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-43-2 ∷ Sb1-0-3-2 ∷ []) (Sb1-0-3-2 ∷ Sb⁻0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·43·2⟩ c4) ▸
       at 2 2 (Sb1-0-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·3·2⟩ c4) ▸
       at 1 2 (Sb1-0-2-3 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 c4) ▸
       at 0 2 (Sb1-0-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Sb⁻0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOX(1;0;3;4) @01102442: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at01102442 : Complete 4 → ⟪ (Sb⁻1-0-43-2 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sb⁻1-0-43-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at01102442 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-43-2 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-3-2 ∷ Sb⁻1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·43·2⟩ c4) ▸
       at 2 2 (Sb1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·3·2⟩ c4) ▸
       at 1 2 (Sb1-0-3-2 ∷ Sb⁻0-1-43-2 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2442 c4) ▸
       at 0 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ c4) ▸
       at 1 2 (Sb⁻1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOXd(1;0;3;4) @2442: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2442 : Complete 4 → ⟪ (Sb⁻0-1-43-2 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-2 ∷ Sb⁻0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-43-2 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻1-0-3-2 ∷ Sb⁻0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·43·2⟩ c4) ▸
       at 2 2 (Sb⁻1-0-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·3·2⟩ c4) ▸
       at 1 2 (Sb⁻1-0-2-3 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 c4) ▸
       at 0 2 (Sb⁻1-0-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Sb⁻0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOXd(1;0;3;4) @01102442: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at01102442 : Complete 4 → ⟪ (Sb⁻1-0-43-2 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sb⁻1-0-43-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at01102442 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-43-2 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sb⁻1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·43·2⟩ c4) ▸
       at 2 2 (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 1 2 (Sb⁻1-0-3-2 ∷ Sb⁻0-1-43-2 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2442 c4) ▸
       at 0 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ c4) ▸
       at 1 2 (Sb⁻1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


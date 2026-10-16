{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D189 where

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
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-F0-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D154 using (lem-X1-beta-at01142042 ; lem-sym12-at01102442 ; lem-sym12-at01142042)
open import Examples.Groups.Clifford+CS.Five.D.D176 using (lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩-at12213443 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·1·3⟩-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·1·3⟩-at243243)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-1-BOX⟨1·4032⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-0-BOX⟨2·4031⟩ ; lem-nat-1-BOX⟨2·4031⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-BOX⟨2·4130⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-2-BOX⟨3·0421⟩ ; lem-nat-2-SBOX⟨3·0·1·2⟩ ; lem-nat-2-SBOXd⟨3·0·1·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-2-SBOX⟨0·1·42·3⟩ ; lem-nat-2-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-1-BOX⟨1·0432⟩)
open import Examples.Groups.Clifford+CS.Five.D.R022 using (lem-nat-1-BOX⟨2·0431⟩)
open import Examples.Groups.Clifford+CS.Five.D.R028 using (lem-nat-2-BOX⟨2·0431⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-0-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R034 using (lem-nat-0-SBOX⟨1·0·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R035 using (lem-nat-0-BOX⟨2·0431⟩ ; lem-nat-0-BOX⟨2·1430⟩)
open import Examples.Groups.Clifford+CS.Five.D.R036 using (lem-nat-0-SBOX⟨2·0·1·3⟩ ; lem-nat-0-SBOX⟨2·1·0·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R037 using (lem-nat-0-SBOXd⟨2·0·1·3⟩ ; lem-nat-0-SBOXd⟨2·1·0·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R039 using (lem-nat-2-SBOX⟨2·0·1·3⟩ ; lem-nat-2-SBOXd⟨2·0·1·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R040 using (lem-nat-0-SBOX⟨2·0·43·1⟩)
-- F0 @01132032: 5 steps
lem-F0-at01132032 : Complete 4 → ⟪ (Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-43-0 ∷ []) ⟫ʷ
lem-F0-at01132032 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ []) (Sb2-1-43-0 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 1 (Sb2-0-43-1 ∷ []) (lem-F0-at132132 c4) ▸
       at 0 2 (Sb2-1-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·43·1⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @02102441: 5 steps
lem-sym12-at02102441 : Complete 4 → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-sym12-at02102441 c4 = run b0
  where
  b0 : Chain (Bx2-0431 ∷ []) (Bx2-4031 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0431⟩ c4) ▸
       at 1 1 (Bx1-4032 ∷ []) (lem-sym12-at01102442 c4) ▸
       at 0 2 (Bx2-4031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4032⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @022440: 5 steps
lem-sym12-at022440 : Complete 4 → ⟪ (Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4130 ∷ []) ⟫ʷ
lem-sym12-at022440 c4 = run b0
  where
  b0 : Chain (Bx2-1430 ∷ []) (Bx2-4130 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1430⟩ c4) ▸
       at 1 1 (Bx2-4031 ∷ []) (lem-sym12-at02102441 c4) ▸
       at 0 2 (Bx2-4130 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4031⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- X1-beta @02142041: 8 steps
lem-X1-beta-at02142041 : Complete 4 → ⟪ (X4 ∷ Bx2-4031 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Bx2-4031 ∷ []) ⟫ʷ
lem-X1-beta-at02142041 c4 = run b0
  where
  b0 : Chain (X4 ∷ Bx2-4031 ∷ X4 ∷ []) (CCZ013 ∷ Bx2-4031 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 2 2 (Bx1-4032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4031⟩ c4) ▸
       at 3 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 1 3 (CCZ023 ∷ Bx1-4032 ∷ []) (lem-X1-beta-at01142042 c4) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Bx2-4031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4032⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- X1-beta @02142140: 8 steps
lem-X1-beta-at02142140 : Complete 4 → ⟪ (X4 ∷ Bx2-4130 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Bx2-4130 ∷ []) ⟫ʷ
lem-X1-beta-at02142140 c4 = run b0
  where
  b0 : Chain (X4 ∷ Bx2-4130 ∷ X4 ∷ []) (CCZ013 ∷ Bx2-4130 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑)) ▸
       at 2 2 (Bx2-4031 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4130⟩ c4) ▸
       at 3 2 (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑)) ▸
       at 1 3 (CCZ013 ∷ Bx2-4031 ∷ []) (lem-X1-beta-at02142041 c4) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-4130 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4031⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @02142041: 5 steps
lem-sym12-at02142041 : Complete 4 → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-sym12-at02142041 c4 = run b0
  where
  b0 : Chain (Bx2-4031 ∷ []) (Bx2-0431 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-4032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4031⟩ c4) ▸
       at 1 1 (Bx1-0432 ∷ []) (lem-sym12-at01142042 c4) ▸
       at 0 2 (Bx2-0431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0432⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @02142140: 5 steps
lem-sym12-at02142140 : Complete 4 → ⟪ (Bx2-4130 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ []) ⟫ʷ
lem-sym12-at02142140 c4 = run b0
  where
  b0 : Chain (Bx2-4130 ∷ []) (Bx2-1430 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-4031 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4130⟩ c4) ▸
       at 1 1 (Bx2-0431 ∷ []) (lem-sym12-at02142041 c4) ▸
       at 0 2 (Bx2-1430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0431⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(4;0231) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩-at2442 : Complete 4 → ⟪ (Sb0-1-43-2 ∷ Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Bx2-0431 ∷ []) (Bx2-0431 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 (Bx3-0421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0431⟩ c4) ▸
       at 1 2 (Bx3-0421 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩-at243243 c4) ▸
       at 0 2 (Bx2-0431 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0421⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(4;0231) @01102442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩-at01102442 : Complete 4 → ⟪ (Sb1-0-43-2 ∷ Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩-at01102442 c4 = run b0
  where
  b0 : Chain (Sb1-0-43-2 ∷ Bx2-1430 ∷ []) (Bx2-1430 ∷ Sb1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 2 2 (Bx2-0431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1430⟩ c4) ▸
       at 1 2 (Bx2-0431 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩-at2442 c4) ▸
       at 0 2 (Bx2-1430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0431⟩ c4) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(0;2;31;4) @13213442: 7 steps
lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩-at13213442 : Complete 4 → ⟪ (CCZ013 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩-at13213442 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩-at12213443 c4) ▸
       at 0 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(0;2;31;4) @0113203442: 7 steps
lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩-at0113203442 : Complete 4 → ⟪ (CCZ013 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩-at0113203442 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩-at13213442 c4) ▸
       at 0 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(4;0;1;3) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·1·3⟩-at2442 : Complete 4 → ⟪ (Sb0-1-43-2 ∷ Sb2-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-1-3 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·1·3⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Sb2-0-1-3 ∷ []) (Sb2-0-1-3 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 (Sb3-0-1-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·1·3⟩ c4) ▸
       at 1 2 (Sb3-0-1-2 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·1·3⟩-at243243 c4) ▸
       at 0 2 (Sb2-0-1-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·1·2⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(4;0;1;3) @01102442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·1·3⟩-at01102442 : Complete 4 → ⟪ (Sb1-0-43-2 ∷ Sb2-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-0-3 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·1·3⟩-at01102442 c4 = run b0
  where
  b0 : Chain (Sb1-0-43-2 ∷ Sb2-1-0-3 ∷ []) (Sb2-1-0-3 ∷ Sb1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 2 2 (Sb2-0-1-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·0·3⟩ c4) ▸
       at 1 2 (Sb2-0-1-3 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·1·3⟩-at2442 c4) ▸
       at 0 2 (Sb2-1-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·1·3⟩ c4) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(4;0;1;3) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·1·3⟩-at2442 : Complete 4 → ⟪ (Sb0-1-43-2 ∷ Sb⁻2-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-1-3 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·1·3⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Sb⁻2-0-1-3 ∷ []) (Sb⁻2-0-1-3 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 (Sb⁻3-0-1-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·0·1·3⟩ c4) ▸
       at 1 2 (Sb⁻3-0-1-2 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·1·3⟩-at243243 c4) ▸
       at 0 2 (Sb⁻2-0-1-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·0·1·2⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(4;0;1;3) @01102442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·1·3⟩-at01102442 : Complete 4 → ⟪ (Sb1-0-43-2 ∷ Sb⁻2-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-0-3 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·1·3⟩-at01102442 c4 = run b0
  where
  b0 : Chain (Sb1-0-43-2 ∷ Sb⁻2-1-0-3 ∷ []) (Sb⁻2-1-0-3 ∷ Sb1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 2 2 (Sb⁻2-0-1-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·1·0·3⟩ c4) ▸
       at 1 2 (Sb⁻2-0-1-3 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·1·3⟩-at2442 c4) ▸
       at 0 2 (Sb⁻2-1-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·0·1·3⟩ c4) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


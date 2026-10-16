{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D218 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-beta-T-at12243143 ; lem-sym23)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-Cz-beta-at2332 ; lem-sym23-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D154 using (lem-X1-beta-at01142042 ; lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1331 ; lem-sym12-at01102442 ; lem-sym12-at01142042)
open import Examples.Groups.Clifford+CS.Five.D.D157 using (lem-beta-T-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D160 using (lem-beta-T-at143143)
open import Examples.Groups.Clifford+CS.Five.D.D189 using (lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩-at13213442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩-at2442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·1·3⟩-at2442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·1·3⟩-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D191 using (lem-auto-BOX⟨0·1234⟩-∣-TOFF042)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-2-BOX⟨0·3412⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013 ; lem-nat-2-BOX⟨0·2413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-1-BOX⟨1·0432⟩ ; lem-nat-1-SBOX⟨0·1·43·2⟩ ; lem-nat-1-SBOX⟨0·2·43·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R022 using (lem-nat-1-BOX⟨2·0431⟩)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-1-SBOX⟨1·0·2·3⟩ ; lem-nat-1-SBOX⟨2·0·1·3⟩ ; lem-nat-1-SBOXd⟨1·0·2·3⟩ ; lem-nat-1-SBOXd⟨2·0·1·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R041 using (lem-nat-3-BOX⟨0·3412⟩ ; lem-nat-3-BOX⟨0·4312⟩)
-- auto SBOX(0;1;23;4) | BOX(4;0231) @122441: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩-at122441 : Complete 4 → ⟪ (Sb0-2-43-1 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩-at122441 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ Bx1-0432 ∷ []) (Bx1-0432 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 2 2 (Bx2-0431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0432⟩ c4) ▸
       at 1 2 (Bx2-0431 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩-at2442 c4) ▸
       at 0 2 (Bx1-0432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0431⟩ c4) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(0;2;31;4) @133441: 7 steps
lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩-at133441 : Complete 4 → ⟪ (CCZ023 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩-at133441 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩-at13213442 c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(4;0;1;3) @122441: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·1·3⟩-at122441 : Complete 4 → ⟪ (Sb0-2-43-1 ∷ Sb1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-3 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·1·3⟩-at122441 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-2-3 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 2 2 (Sb2-0-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Sb2-0-1-3 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·1·3⟩-at2442 c4) ▸
       at 0 2 (Sb1-0-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·1·3⟩ c4) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(4;0;1;3) @122441: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·1·3⟩-at122441 : Complete 4 → ⟪ (Sb0-2-43-1 ∷ Sb⁻1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-3 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·1·3⟩-at122441 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-2-3 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 2 2 (Sb⁻2-0-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Sb⁻2-0-1-3 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·1·3⟩-at2442 c4) ▸
       at 0 2 (Sb⁻1-0-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·1·3⟩ c4) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 CS23^0|CS03^1: 420 steps
lem-F4-CS23ᵖ0∣CS03ᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣CS03ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (run b52))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb1-0-43-2 ∷ []) (X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ CCZ023 ∷ X4 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b0 = at 3 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx1-4032 ∷ []) (lem-sym12-at01102442 c4) ▸
       at 2 3 (CCZ023 ∷ Bx1-4032 ∷ []) (lem-X1-beta-at01142042 c4) ▸
       at 3 1 (Bx1-0432 ∷ []) (lem-sym12-at01142042 c4) ▸
       at 2 2 (Bx1-0432 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1331 c4) ▸
       at 1 2 (Bx1-0432 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩-at122441 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ CCZ023 ∷ X4 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CCZ023 ∷ CCZ023 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b1 = at 1 1 (Bx1-4032 ∷ []) (lem-sym12-at01102442 c4) ▸
       at 0 3 (CCZ023 ∷ Bx1-4032 ∷ []) (lem-X1-beta-at01142042 c4) ▸
       at 1 1 (Bx1-0432 ∷ []) (lem-sym12-at01142042 c4) ▸
       at 0 2 (Bx1-0432 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1331 c4) ▸
       at 4 2 (X4 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-2-43-1 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩-at133441 c4) ▸
       at 3 2 (X4 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx1-0432 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CCZ023 ∷ CCZ023 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b2 = at 4 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (lw0 c4 (Toff234 ∷ []) (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b3 : Chain (Bx1-0432 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b3 = at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (CS12 ∷ []) (refl) ▸
       at 14 1 (CS12⁻ ∷ []) (refl) ▸
       at 7 12 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b4 : Chain (Bx1-0432 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ K2 ∷ CCZ013 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b4 = at 17 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 11 2 (K2 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (Bx1-0432 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ K2 ∷ CCZ013 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b5 = at 10 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 12 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (Bx1-0432 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b6 = at 17 4 (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 13 5 (CCZ013 ∷ []) (lw4 c4 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (Bx1-0432 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b7 = at 14 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 13 2 (K2⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 7 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 5 2 (K2 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 6 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (Bx1-0432 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b8 = at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (Bx1-0432 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ K2⁻ ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b9 = at 5 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 5 (CCZ013 ∷ []) (lw4 c4 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 7 2 (K2⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (Bx1-0432 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ K2⁻ ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b10 = at 6 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 1 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b11 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b11 = at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b12 = at 11 1 (CS12 ∷ []) (refl) ▸
       at 17 1 (CS12⁻ ∷ []) (refl) ▸
       at 10 21 (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 29 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 7 15 (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b13 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ X4 ∷ K2⁻ ∷ CCZ013 ∷ X4 ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b13 = at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 14 2 (K2 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 14 4 (CX34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CCZ013 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 16 2 (K2⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸ done

  b14 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ X4 ∷ K2⁻ ∷ CCZ013 ∷ X4 ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ CS03 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b14 = at 15 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 18 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 17 2 (K2 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 18 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b15 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ CS03 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b15 = at 28 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 29 4 (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 4 (CS24⁻ ∷ X4 ∷ CX31 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX31 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (CS24⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01⁻ ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CS24⁻ ∷ X4 ∷ CX31 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX31 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b16 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ X4 ∷ K2 ∷ CCZ013 ∷ X4 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b16 = at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 5 (CCZ013 ∷ []) (lw4 c4 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 19 2 (K2⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 21 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 20 2 (K2 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸ done

  b17 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ X4 ∷ K2 ∷ CCZ013 ∷ X4 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CCZ013 ∷ X4 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b17 = at 19 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 20 4 (CX34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CCZ013 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 22 2 (K2⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 21 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 24 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 23 2 (K2 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b18 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CCZ013 ∷ X4 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ K2 ∷ X4 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b18 = at 25 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 24 2 (CS23 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ CS23 ∷ []) (CS23 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 26 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 25 2 (K2⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 24 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 10 15 (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b19 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ K2 ∷ X4 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CCZ013 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b19 = at 8 2 (K2 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 8 4 (CX34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CCZ013 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 10 2 (K2⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 12 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 11 2 (K2 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸ done

  b20 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CCZ013 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b20 = at 10 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 12 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CS24⁻ ∷ X4 ∷ CX31 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX31 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b21 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b21 = at 17 4 (CS24⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01⁻ ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS24⁻ ∷ X4 ∷ CX31 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX31 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 13 5 (CCZ013 ∷ []) (lw4 c4 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done

  b22 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ X4 ∷ CCZ013 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b22 = at 14 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 13 2 (K2⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 15 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 14 2 (K2 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 14 4 (CX34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CCZ013 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸ done

  b23 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ X4 ∷ CCZ013 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ X4 ∷ CCZ013 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b23 = at 16 2 (K2⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 18 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 17 2 (K2 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 19 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 18 2 (CS23 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ CS23 ∷ []) (CS23 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸ done

  b24 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ X4 ∷ CCZ013 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b24 = at 20 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 19 2 (K2⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 4 15 (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸ done

  b25 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b25 = at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 3 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸ done

  b26 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ X4 ∷ CS02 ∷ Sb0-2-43-1 ∷ X4 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b26 = at 6 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 2 5 (CCZ234 ∷ []) (lw0 c4 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff234 ∷ []) (lw0 c4 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (Toff234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS02 ∷ []) (refl) ▸
       at 4 2 (CS02 ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02 ∷ []) (CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 3 2 (Sb1-0-2-3 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·1·3⟩-at122441 c4) ▸
       at 3 1 (CS02 ∷ []) (refl) ▸ done

  b27 : Chain (Bx1-0432 ∷ Toff234 ∷ X4 ∷ CS02 ∷ Sb0-2-43-1 ∷ X4 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b27 = at 2 2 (CS02 ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02 ∷ []) (CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 6 1 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (lw0 c4 (Toff234 ∷ []) (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸ done

  b28 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b28 = at 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (CS12 ∷ []) (refl) ▸
       at 16 1 (CS12⁻ ∷ []) (refl) ▸
       at 9 12 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b29 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ K2 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b29 = at 13 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 19 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b30 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ K2 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b30 = at 13 2 (K2 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 14 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b31 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b31 = at 22 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b32 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CCZ013 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b32 = at 15 5 (CCZ013 ∷ []) (lw4 c4 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 15 2 (K2⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 9 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 7 2 (K2 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b33 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CCZ013 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b33 = at 8 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b34 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ K2⁻ ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b34 = at 10 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 5 (CCZ013 ∷ []) (lw4 c4 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸ done

  b35 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ K2⁻ ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b35 = at 9 2 (K2⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 3 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b36 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b36 = at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 7 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b37 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b37 = at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (CS12 ∷ []) (refl) ▸
       at 19 1 (CS12⁻ ∷ []) (refl) ▸
       at 12 21 (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 31 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 9 15 (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸ done

  b38 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ X4 ∷ CCZ013 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b38 = at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 16 2 (K2 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 16 4 (CX34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CCZ013 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸ done

  b39 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ X4 ∷ CCZ013 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b39 = at 18 2 (K2⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 20 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 19 2 (K2 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 20 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b40 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ CS01 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b40 = at 27 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 30 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 31 4 (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 4 (CS24⁻ ∷ X4 ∷ CX31 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX31 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS24⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01⁻ ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS24⁻ ∷ X4 ∷ CX31 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX31 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b41 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ CS01 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ X4 ∷ CCZ013 ∷ K2 ∷ X4 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b41 = at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 24 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 25 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 5 (CCZ013 ∷ []) (lw4 c4 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 21 2 (K2⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 23 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b42 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ X4 ∷ CCZ013 ∷ K2 ∷ X4 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CCZ013 ∷ X4 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b42 = at 22 2 (K2 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 21 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 22 4 (CX34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CCZ013 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 24 2 (K2⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 26 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 25 2 (K2 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸ done

  b43 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CCZ013 ∷ X4 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b43 = at 24 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 27 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 26 2 (CS23 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ CS23 ∷ []) (CS23 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 25 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 28 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 27 2 (K2⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 26 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 12 15 (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b44 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ X4 ∷ CCZ013 ∷ K2 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b44 = at 11 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 10 2 (K2 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 10 4 (CX34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CCZ013 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 12 2 (K2⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 14 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b45 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ X4 ∷ CCZ013 ∷ K2 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b45 = at 13 2 (K2 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 14 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b46 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b46 = at 22 4 (CS24⁻ ∷ X4 ∷ CX31 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX31 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS24⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01⁻ ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS24⁻ ∷ X4 ∷ CX31 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX31 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b47 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b47 = at 15 5 (CCZ013 ∷ []) (lw4 c4 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 15 2 (K2⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 17 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 16 2 (K2 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 16 4 (CX34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CCZ013 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b48 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS23 ∷ CCZ013 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b48 = at 19 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 18 2 (K2⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 20 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 19 2 (K2 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 21 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 20 2 (CS23 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ CS23 ∷ []) (CS23 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸ done

  b49 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS23 ∷ CCZ013 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b49 = at 19 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 22 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 21 2 (K2⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 6 15 (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b50 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ CX34 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b50 = at 19 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 5 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸ done

  b51 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ CX34 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b51 = at 7 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (CCZ234 ∷ []) (lw0 c4 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Toff234 ∷ []) (lw0 c4 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (Toff234 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS02⁻ ∷ []) (refl) ▸
       at 6 2 (CS02⁻ ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 5 2 (Sb⁻1-0-2-3 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·1·3⟩-at122441 c4) ▸ done

  b52 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (Sb1-0-43-2 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b52 = at 5 1 (CS02⁻ ∷ []) (refl) ▸
       at 4 2 (CS02⁻ ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-43-2 ∷ []) (refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;2413): 14 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx0-2413 ∷ []) (Toff024 ∷ CCZ013 ∷ CS12⁻ ∷ Toff024 ∷ CCZ013 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at12243143 c4) ▸
       at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Toff024 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 2 (CCZ013 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 2 1 (CS12⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ CS12⁻ ∷ Toff024 ∷ CCZ013 ∷ []) (Bx0-2413 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 2 2 (Toff024 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 3 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 2 (CCZ013 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx0-2413 ∷ []) (sym (lem-beta-T-at12243143 c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;2413): 14 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩ : Complete 4 → ⟪ (Sb0-1-2-3 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-2-3 ∷ Bx0-2413 ∷ []) (Toff024 ∷ CCZ013 ∷ CS12 ∷ Toff024 ∷ CCZ013 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at12243143 c4) ▸
       at 0 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (Toff024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ Toff024 ∷ []) (Toff024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 1 1 (CS12 ∷ []) (refl) ▸
       at 1 2 (CCZ013 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 2 1 (CS12 ∷ []) (refl) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ CS12 ∷ Toff024 ∷ CCZ013 ∷ []) (Bx0-2413 ∷ Sb0-1-2-3 ∷ [])
  b1 = at 2 2 (Toff024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ Toff024 ∷ []) (Toff024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 3 2 (CCZ013 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx0-2413 ∷ []) (sym (lem-beta-T-at12243143 c4)) ▸ done


-- auto BOX(0;1234) | CCZ013: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ013 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ013 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ013 ∷ []) (CCZ013 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CCZ013 ∷ Bx0-1324 ∷ []) (sym (lem-Cz-beta-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸ done


-- auto BOX(0;1234) | BOX(0;4213): 6 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·4213⟩ : Complete 4 → ⟪ (Bx0-1234 ∷ Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·4213⟩ c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Bx0-4213 ∷ []) (Bx0-4213 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at143143 c4) ▸
       at 0 2 (Toff024 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF042 c4) ▸
       at 1 2 (CCZ013 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ013 c4) ▸
       at 2 2 (Toff024 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF042 c4) ▸
       at 3 2 (CCZ013 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ013 c4) ▸
       at 0 4 (Bx0-4213 ∷ []) (sym (lem-beta-T-at143143 c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;2413) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2332 : Complete 4 → ⟪ (Sb⁻0-1-3-2 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-3-2 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ c4) ▸
       at 1 2 (Bx0-2413 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩ c4) ▸
       at 0 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ c4) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;2413) @243243: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at243243 : Complete 4 → ⟪ (Sb⁻0-1-4-2 ∷ Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-2 ∷ Bx0-4312 ∷ []) (Bx0-4312 ∷ Sb⁻0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx0-3412 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4312⟩ c4) ▸
       at 1 2 (Bx0-3412 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2332 c4) ▸
       at 0 2 (Bx0-4312 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3412⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D199 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-beta-T-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-beta-T-at233442 ; lem-sym23-at233442 ; lem-sym23-at2442 ; lem-sym34-at243243 ; lem-sym34-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D138 using (lem-F0-at011220)
open import Examples.Groups.Clifford+CS.Five.D.D156 using (lem-beta-T-at01102442)
open import Examples.Groups.Clifford+CS.Five.D.D160 using (lem-beta-T-at03243240)
open import Examples.Groups.Clifford+CS.Five.D.D169 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243)
-- F4 CS12^0|CS03^1: 892 steps
lem-F4-CS12ᵖ0∣CS03ᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣CS03ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (trans (run b62) (trans (run b63) (trans (run b64) (trans (run b65) (trans (run b66) (trans (run b67) (trans (run b68) (trans (run b69) (trans (run b70) (trans (run b71) (trans (run b72) (trans (run b73) (trans (run b74) (trans (run b75) (trans (run b76) (trans (run b77) (trans (run b78) (trans (run b79) (trans (run b80) (trans (run b81) (trans (run b82) (trans (run b83) (trans (run b84) (trans (run b85) (trans (run b86) (trans (run b87) (trans (run b88) (trans (run b89) (trans (run b90) (trans (run b91) (trans (run b92) (trans (run b93) (trans (run b94) (trans (run b95) (trans (run b96) (trans (run b97) (trans (run b98) (trans (run b99) (trans (run b100) (trans (run b101) (trans (run b102) (trans (run b103) (trans (run b104) (trans (run b105) (trans (run b106) (trans (run b107) (trans (run b108) (trans (run b109) (trans (run b110) (run b111)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb1-0-43-2 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b0 = at 3 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 3 1 (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) (lem-beta-T-at01102442 c4) ▸
       at 3 1 (K1 ∷ CCZ014 ∷ K1⁻ ∷ []) (pw2 c4 (Toff104 ∷ []) (K1 ∷ CCZ014 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b1 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸
       at 13 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 12 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b2 = at 10 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 16 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b3 : Chain (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b3 = at 10 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 11 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b4 = at 19 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b5 : Chain (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b5 = at 12 5 (CCZ023 ∷ []) (lw4 c4 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 12 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 6 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 4 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b6 : Chain (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b6 = at 5 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ K1⁻ ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b7 = at 7 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 5 (CCZ023 ∷ []) (lw4 c4 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b8 : Chain (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ K1⁻ ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b8 = at 6 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 0 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b9 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx3-1420 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b9 = at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 4 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 4 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx3-1420 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx3-1420 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b10 = at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (CS01 ∷ []) (refl) ▸
       at 16 1 (CS01⁻ ∷ []) (refl) ▸
       at 9 21 (K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ []) (K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 1 (Sb3-1-0-2 ∷ []) (refl) ▸
       at 28 1 (Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 6 15 (K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ Toff024 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ []) (K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx3-1420 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b11 = at 4 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-beta-T-at03243240 c4) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 13 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 13 4 (CX04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX04 ∷ []) (CX04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b12 = at 16 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 15 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 17 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 16 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 17 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b13 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX20 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX20 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b13 = at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 4 (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS14⁻ ∷ X4 ∷ CX20 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CX20 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX20 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS14⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS14⁻ ∷ X4 ∷ CX20 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CX20 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX20 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b14 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX20 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX20 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b14 = at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 5 (CCZ023 ∷ []) (lw4 c4 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 19 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 18 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b15 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b15 = at 20 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 19 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 19 4 (CX04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX04 ∷ []) (CX04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 21 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 23 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b16 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b16 = at 22 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 21 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 24 2 (CS01 ∷ X4 ∷ []) (sym (c₂ (CS) (X ↑ ↑))) ▸
       at 23 2 (CS01 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ CS01 ∷ []) (CS01 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (CS01 ∷ X4 ∷ []) (sym (c₂ (CS) (X ↑ ↑))) ▸
       at 25 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 24 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b17 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b17 = at 9 15 (K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ []) (K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 7 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 7 4 (CX04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX04 ∷ []) (CX04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 9 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b18 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX20 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX20 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b18 = at 11 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 10 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 11 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b19 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX20 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX20 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b19 = at 22 4 (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS14⁻ ∷ X4 ∷ CX20 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CX20 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX20 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS14⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS14⁻ ∷ X4 ∷ CX20 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CX20 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX20 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b20 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ X4 ∷ CCZ023 ∷ X4 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b20 = at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 5 (CCZ023 ∷ []) (lw4 c4 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 12 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 14 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 13 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b21 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ X4 ∷ CCZ023 ∷ X4 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CCZ023 ∷ CS01 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b21 = at 13 4 (CX04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX04 ∷ []) (CX04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 15 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 17 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 16 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 18 2 (CS01 ∷ X4 ∷ []) (sym (c₂ (CS) (X ↑ ↑))) ▸ done

  b22 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CCZ023 ∷ CS01 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b22 = at 17 2 (CS01 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ CS01 ∷ []) (CS01 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (CS01 ∷ X4 ∷ []) (sym (c₂ (CS) (X ↑ ↑))) ▸
       at 19 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 18 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 3 15 (K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ []) (K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b23 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b23 = at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 4 (Bx3-1420 ∷ []) (sym (lem-beta-T-at03243240 c4)) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 5 (Sb3-1-42-0 ∷ []) (refl) ▸
       at 16 1 (Sb0-1-42-3 ∷ []) (sym (lem-F0-at011220 c4)) ▸ done

  b24 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ X4 ∷ CCZ123 ∷ Sb0-1-42-3 ∷ X4 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b24 = at 2 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 1 5 (CCZ014 ∷ []) (pw2 c4 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff104 ∷ []) (pw2 c4 (K1 ∷ CCZ014 ∷ K1⁻ ∷ []) (Toff104 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ []) (CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ123 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at243243 c4) ▸ done

  b25 : Chain (Toff104 ∷ X4 ∷ CCZ123 ∷ Sb0-1-42-3 ∷ X4 ∷ Toff104 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b25 = at 1 2 (CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ []) (CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K1 ∷ CCZ014 ∷ K1⁻ ∷ []) (pw2 c4 (Toff104 ∷ []) (K1 ∷ CCZ014 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b26 : Chain (Toff104 ∷ CCZ123 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b26 = at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (CS13 ∷ []) (refl) ▸
       at 15 1 (CS13⁻ ∷ []) (refl) ▸
       at 8 12 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b27 : Chain (Toff104 ∷ CCZ123 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b27 = at 18 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 12 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b28 : Chain (Toff104 ∷ CCZ123 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b28 = at 11 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 13 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b29 : Chain (Toff104 ∷ CCZ123 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b29 = at 18 4 (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 14 5 (CCZ023 ∷ []) (lw4 c4 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b30 : Chain (Toff104 ∷ CCZ123 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b30 = at 15 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 14 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 8 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 6 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 7 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) tt tt Eq.refl) ▸ done

  b31 : Chain (Toff104 ∷ CCZ123 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b31 = at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 4 (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b32 : Chain (Toff104 ∷ CCZ123 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ K1⁻ ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b32 = at 6 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 5 (CCZ023 ∷ []) (lw4 c4 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 8 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b33 : Chain (Toff104 ∷ CCZ123 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ K1⁻ ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b33 = at 7 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 2 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b34 : Chain (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx3-1420 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b34 = at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 6 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 6 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b35 : Chain (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx3-1420 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b35 = at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (CS01 ∷ []) (refl) ▸
       at 18 1 (CS01⁻ ∷ []) (refl) ▸
       at 11 21 (K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ []) (K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 1 (Sb3-1-0-2 ∷ []) (refl) ▸
       at 30 1 (Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 8 15 (K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ Toff024 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ []) (K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-beta-T-at03243240 c4) ▸ done

  b36 : Chain (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ X4 ∷ CCZ023 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b36 = at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 15 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 15 4 (CX04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX04 ∷ []) (CX04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b37 : Chain (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ X4 ∷ CCZ023 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX20 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b37 = at 17 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 19 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 18 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 19 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b38 : Chain (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX20 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS03 ∷ CX20 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX20 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b38 = at 26 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 29 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 30 4 (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 4 (CS14⁻ ∷ X4 ∷ CX20 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CX20 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX20 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 4 (CS14⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 4 (CS14⁻ ∷ X4 ∷ CX20 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CX20 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX20 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 4 (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b39 : Chain (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS03 ∷ CX20 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX20 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b39 = at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 24 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 5 (CCZ023 ∷ []) (lw4 c4 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 21 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 20 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 19 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 22 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b40 : Chain (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b40 = at 21 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 21 4 (CX04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX04 ∷ []) (CX04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 23 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 25 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 24 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b41 : Chain (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b41 = at 23 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 26 2 (CS01 ∷ X4 ∷ []) (sym (c₂ (CS) (X ↑ ↑))) ▸
       at 25 2 (CS01 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ CS01 ∷ []) (CS01 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 24 2 (CS01 ∷ X4 ∷ []) (sym (c₂ (CS) (X ↑ ↑))) ▸
       at 27 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 26 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 25 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 11 15 (K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ []) (K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b42 : Chain (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b42 = at 10 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 9 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 9 4 (CX04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX04 ∷ []) (CX04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 11 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 13 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b43 : Chain (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX20 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX20 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b43 = at 12 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 13 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 4 (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b44 : Chain (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX20 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX20 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b44 = at 21 4 (CS14⁻ ∷ X4 ∷ CX20 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CX20 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX20 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 4 (CS14⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (CS14⁻ ∷ X4 ∷ CX20 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CX20 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX20 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 4 (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b45 : Chain (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b45 = at 14 5 (CCZ023 ∷ []) (lw4 c4 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 14 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 16 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 15 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 15 4 (CX04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX04 ∷ []) (CX04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b46 : Chain (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS01 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b46 = at 18 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 17 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 19 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 18 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 20 2 (CS01 ∷ X4 ∷ []) (sym (c₂ (CS) (X ↑ ↑))) ▸
       at 19 2 (CS01 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ CS01 ∷ []) (CS01 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b47 : Chain (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS01 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b47 = at 18 2 (CS01 ∷ X4 ∷ []) (sym (c₂ (CS) (X ↑ ↑))) ▸
       at 21 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 20 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 19 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 5 15 (K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ []) (K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b48 : Chain (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb3-1-0-2 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ Sb⁻3-1-0-2 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b48 = at 18 4 (Bx3-1420 ∷ []) (sym (lem-beta-T-at03243240 c4)) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 5 (Sb3-1-42-0 ∷ []) (refl) ▸
       at 18 1 (Sb0-1-42-3 ∷ []) (sym (lem-F0-at011220 c4)) ▸
       at 4 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸ done

  b49 : Chain (Toff104 ∷ CCZ123 ∷ K1 ∷ CS14 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX04 ∷ K1⁻ ∷ K1 ∷ CS01 ∷ K1⁻ ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CCZ123 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b49 = at 5 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 3 5 (CCZ014 ∷ []) (pw2 c4 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Toff104 ∷ []) (pw2 c4 (K1 ∷ CCZ014 ∷ K1⁻ ∷ []) (Toff104 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ []) (CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at243243 c4) ▸
       at 3 2 (CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ []) (CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b50 : Chain (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b50 = at 0 4 (Bx1-0432 ∷ []) (sym (lem-beta-T-at01102442 c4)) ▸
       at 4 1 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (lw0 c4 (Toff234 ∷ []) (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b51 : Chain (Bx1-0432 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b51 = at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (CS13⁻ ∷ []) (refl) ▸
       at 13 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13⁻ ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 10 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b52 : Chain (Bx1-0432 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b52 = at 8 1 (CS13 ∷ []) (refl) ▸
       at 7 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-1432 ∷ []) (lem-sym34-at243243 c4) ▸
       at 2 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 2 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b53 : Chain (Bx1-0432 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b53 = at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 8 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 9 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b54 : Chain (Bx1-0432 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b54 = at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b55 : Chain (Bx1-0432 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b55 = at 20 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b56 : Chain (Bx1-0432 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b56 = at 13 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 10 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸ done

  b57 : Chain (Bx1-0432 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b57 = at 4 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 2 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 3 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b58 : Chain (Bx1-0432 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b58 = at 6 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b59 : Chain (Bx1-0432 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b59 = at 8 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b60 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b60 = at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 4 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b61 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b61 = at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 4 (Bx0-1342 ∷ []) (sym (lem-beta-T-at233442 c4)) ▸
       at 5 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 5 1 (Bx0-1423 ∷ []) (lem-sym34-at2442 c4) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b62 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b62 = at 5 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 1 (CS13⁻ ∷ []) (refl) ▸
       at 16 15 (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13⁻ ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b63 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1342 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b63 = at 29 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 13 15 (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CS13 ∷ []) (refl) ▸
       at 10 15 (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 15 (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx0-1432 ∷ []) (lem-sym34-at243243 c4) ▸
       at 5 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸ done

  b64 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1342 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ Toff013 ∷ X4 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b64 = at 5 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 15 (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 11 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b65 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ Toff013 ∷ X4 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ CCZ013 ∷ K0⁻ ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b65 = at 11 4 (CX34 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff013 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 13 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 15 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 14 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 15 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸ done

  b66 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ CCZ013 ∷ K0⁻ ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b66 = at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b67 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b67 = at 29 4 (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b68 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ K2⁻ ∷ Toff013 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b68 = at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 16 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸ done

  b69 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ K2⁻ ∷ Toff013 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b69 = at 15 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 18 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 17 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 17 4 (CX34 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff013 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 19 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸ done

  b70 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ X4 ∷ K2⁻ ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b70 = at 21 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 20 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 19 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 22 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 21 2 (CS23 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CS23 ∷ []) (CS23 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 23 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 22 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸ done

  b71 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ X4 ∷ K2⁻ ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ X4 ∷ K2⁻ ∷ Toff013 ∷ X4 ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b71 = at 21 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 7 15 (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 5 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 5 4 (CX34 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff013 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 7 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸ done

  b72 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ X4 ∷ K2⁻ ∷ Toff013 ∷ X4 ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b72 = at 6 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 9 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 8 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 9 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b73 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b73 = at 12 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b74 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b74 = at 14 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 13 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b75 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ X4 ∷ K2 ∷ Toff013 ∷ X4 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b75 = at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 10 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 12 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 11 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸ done

  b76 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ X4 ∷ K2 ∷ Toff013 ∷ X4 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ Toff013 ∷ X4 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b76 = at 10 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 11 4 (CX34 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff013 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 13 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 15 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 14 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b77 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ Toff013 ∷ X4 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b77 = at 16 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 15 2 (CS23 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CS23 ∷ []) (CS23 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 17 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 16 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b78 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b78 = at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 4 (Bx0-1342 ∷ []) (sym (lem-beta-T-at233442 c4)) ▸
       at 17 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 17 1 (Bx0-1423 ∷ []) (lem-sym34-at2442 c4) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b79 : Chain (Bx1-0432 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS02 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b79 = at 17 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 2 5 (CCZ234 ∷ []) (lw0 c4 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff234 ∷ []) (lw0 c4 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (Toff234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS02 ∷ []) (refl) ▸ done

  b80 : Chain (Bx1-0432 ∷ Toff234 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS02 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ K2 ∷ CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b80 = at 4 2 (CS02 ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02 ∷ []) (CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 3 2 (Sb1-0-2-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 c4) ▸
       at 3 1 (CS02 ∷ []) (refl) ▸
       at 2 2 (CS02 ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02 ∷ []) (CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 6 1 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (lw0 c4 (Toff234 ∷ []) (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) tt tt Eq.refl) ▸ done

  b81 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ K2 ∷ CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b81 = at 8 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b82 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b82 = at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (CS13⁻ ∷ []) (refl) ▸
       at 15 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13⁻ ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 12 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (CS13 ∷ []) (refl) ▸
       at 9 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b83 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b83 = at 6 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-1432 ∷ []) (lem-sym34-at243243 c4) ▸
       at 4 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 4 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b84 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ X4 ∷ CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b84 = at 11 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 10 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 11 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) tt tt Eq.refl) ▸ done

  b85 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ X4 ∷ CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b85 = at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b86 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ K0 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b86 = at 13 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b87 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ K0 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ K2 ∷ Toff013 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b87 = at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 12 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 6 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 4 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸ done

  b88 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ K2 ∷ Toff013 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ X4 ∷ CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b88 = at 3 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 5 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b89 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ X4 ∷ CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b89 = at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b90 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ X4 ∷ Toff013 ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b90 = at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸ done

  b91 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ X4 ∷ Toff013 ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b91 = at 7 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 6 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 4 (Bx0-1342 ∷ []) (sym (lem-beta-T-at233442 c4)) ▸
       at 7 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸ done

  b92 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b92 = at 7 1 (Bx0-1423 ∷ []) (lem-sym34-at2442 c4) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 7 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b93 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b93 = at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (CS13⁻ ∷ []) (refl) ▸
       at 18 15 (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13⁻ ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 31 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 15 15 (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (CS13 ∷ []) (refl) ▸ done

  b94 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b94 = at 12 15 (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 9 15 (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx0-1432 ∷ []) (lem-sym34-at243243 c4) ▸
       at 7 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 7 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b95 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ X4 ∷ K2⁻ ∷ Toff013 ∷ X4 ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b95 = at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 15 (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 13 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 13 4 (CX34 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff013 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 15 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸ done

  b96 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ X4 ∷ K2⁻ ∷ Toff013 ∷ X4 ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b96 = at 14 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 17 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 16 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 17 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b97 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b97 = at 20 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 30 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 31 4 (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b98 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b98 = at 22 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 24 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 25 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b99 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ X4 ∷ K2 ∷ Toff013 ∷ X4 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b99 = at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸
       at 19 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 18 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 20 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 19 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸ done

  b100 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ X4 ∷ K2 ∷ Toff013 ∷ X4 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ Toff013 ∷ X4 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b100 = at 18 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 19 4 (CX34 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff013 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 21 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 23 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 22 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 21 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b101 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ Toff013 ∷ X4 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ K2 ∷ X4 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b101 = at 24 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 23 2 (CS23 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CS23 ∷ []) (CS23 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 25 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 24 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 9 15 (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ []) (K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b102 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ K2 ∷ X4 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ X4 ∷ K2 ∷ Toff013 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b102 = at 7 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 7 4 (CX34 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff013 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 9 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 11 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 10 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸ done

  b103 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ X4 ∷ K2 ∷ Toff013 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b103 = at 9 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 11 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b104 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CS03 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b104 = at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b105 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CS03 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b105 = at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸ done

  b106 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ X4 ∷ Toff013 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b106 = at 13 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 12 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 14 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 13 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 13 4 (CX34 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff013 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸ done

  b107 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ X4 ∷ Toff013 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ X4 ∷ Toff013 ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b107 = at 15 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 17 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 16 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 18 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 17 2 (CS23 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CS23 ∷ []) (CS23 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸ done

  b108 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ X4 ∷ Toff013 ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b108 = at 19 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 18 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 4 (Bx0-1342 ∷ []) (sym (lem-beta-T-at233442 c4)) ▸
       at 19 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸ done

  b109 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ CX34 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ [])
  b109 = at 19 1 (Bx0-1423 ∷ []) (lem-sym34-at2442 c4) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 5 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸ done

  b110 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS24 ∷ CX34 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX34 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b110 = at 7 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (CCZ234 ∷ []) (lw0 c4 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Toff234 ∷ []) (lw0 c4 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (Toff234 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS02⁻ ∷ []) (refl) ▸
       at 6 2 (CS02⁻ ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 5 2 (Sb⁻1-0-2-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 c4) ▸ done

  b111 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (Sb1-0-43-2 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b111 = at 5 1 (CS02⁻ ∷ []) (refl) ▸
       at 4 2 (CS02⁻ ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-43-2 ∷ []) (refl) ▸ done


{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D184 where

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
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym12-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-sym23-at0110243243 ; lem-sym23-at01103443)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym12-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-X1-beta-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-beta-T-at01103443 ; lem-sym34-at0110243243 ; lem-sym34-at01102442)
open import Examples.Groups.Clifford+CS.Five.D.D154 using (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 ; lem-sym12-at01102442 ; lem-sym12-at01142042)
open import Examples.Groups.Clifford+CS.Five.D.D163 using (lem-beta-T-at0114233042 ; lem-sym23-at01142042 ; lem-sym23-at0114233042)
open import Examples.Groups.Clifford+CS.Five.D.D183 using (lem-auto-CCZ012-∣-SBOX⟨1·0·32·4⟩-at233442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·1203⟩-at01102442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·1·3·0⟩-at01102442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·1·3·0⟩-at01102442)
-- F4 CS03^0|CS01^1: 616 steps
lem-F4-CS03ᵖ0∣CS01ᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb1-0-43-2 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS03ᵖ0∣CS01ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (trans (run b62) (trans (run b63) (trans (run b64) (trans (run b65) (trans (run b66) (trans (run b67) (trans (run b68) (trans (run b69) (trans (run b70) (trans (run b71) (trans (run b72) (trans (run b73) (trans (run b74) (trans (run b75) (run b76))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb1-0-43-2 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Sb1-0-43-2 ∷ CCZ013 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 2 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 3 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 2 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 1 2 (Bx2-0413 ∷ Sb1-0-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·1203⟩-at01102442 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Sb1-0-43-2 ∷ CCZ013 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ CCZ013 ∷ CCZ013 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b1 = at 1 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 0 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 0 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 4 2 (X4 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-0-43-2 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨1·0·32·4⟩-at233442 c4) ▸
       at 3 2 (X4 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx2-0413 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ CCZ013 ∷ CCZ013 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b2 = at 4 2 [] (lw4 c4 (CCZ013 ∷ CCZ013 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸ done

  b3 : Chain (Bx2-0413 ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b3 = at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (CS02⁻ ∷ []) (refl) ▸
       at 13 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 10 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Bx2-0413 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b4 = at 8 1 (CS02 ∷ []) (refl) ▸
       at 7 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 4 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx1-0423 ∷ []) (lem-sym34-at01102442 c4) ▸
       at 2 1 (Bx1-0243 ∷ []) (lem-sym23-at0110243243 c4) ▸
       at 2 1 (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) (lem-beta-T-at01103443 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (Bx2-0413 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ X4 ∷ CCZ012 ∷ K1⁻ ∷ X4 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b5 = at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 8 2 (K3 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (K)) ▸
       at 7 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 9 1 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (lw4 c4 (Toff102 ∷ []) (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (Bx2-0413 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ X4 ∷ CCZ012 ∷ K1⁻ ∷ X4 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b6 = at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS34 ∷ X4 ∷ K1⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K1⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ K1⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (Bx2-0413 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ CS34 ∷ X4 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ X4 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b7 = at 20 4 (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CX02 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CX02 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b8 : Chain (Bx2-0413 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ CS34 ∷ X4 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ X4 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b8 = at 13 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (CS34 ∷ X4 ∷ K1 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K1 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ K1 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 3 (Toff102 ∷ []) (lw4 c4 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (Toff102 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 10 2 (K3⁻ ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (K • iI)) ▸
       at 9 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸ done

  b9 : Chain (Bx2-0413 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS34 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b9 = at 4 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 2 2 (K3 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (K)) ▸
       at 1 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 3 1 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (lw4 c4 (Toff102 ∷ []) (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (CS34 ∷ X4 ∷ K1⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K1⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ K1⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (Bx2-0413 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS34 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b10 = at 6 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CX02 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (Bx2-0413 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ X4 ∷ K1 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b11 = at 8 4 (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CX02 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CS34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CS34 ∷ X4 ∷ K1 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K1 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ K1 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ X4 ∷ K1 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff102 ∷ CCZ134 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b12 = at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 3 (Toff102 ∷ []) (lw4 c4 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (Toff102 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 4 2 (K3⁻ ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (K • iI)) ▸
       at 3 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b13 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff102 ∷ CCZ134 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b13 = at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 4 (Bx1-0243 ∷ []) (sym (lem-beta-T-at01103443 c4)) ▸
       at 5 1 (Bx1-0423 ∷ []) (lem-sym23-at01103443 c4) ▸
       at 5 1 (Bx1-0432 ∷ []) (lem-sym34-at0110243243 c4) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b14 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b14 = at 5 5 (Sb1-0-43-2 ∷ []) (refl) ▸
       at 5 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 1 (CS02⁻ ∷ []) (refl) ▸
       at 16 4 (K3 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ K3 ∷ []) (K3 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b15 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b15 = at 18 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 18 1 (CS02⁻ ∷ []) (refl) ▸
       at 17 4 (CX14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 19 1 (CS02⁻ ∷ []) (refl) ▸
       at 18 4 (K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ K3⁻ ∷ []) (K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 20 1 (CS02⁻ ∷ []) (refl) ▸ done

  b16 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b16 = at 19 4 (K3 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ K3 ∷ []) (K3 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 21 1 (CS02⁻ ∷ []) (refl) ▸
       at 20 4 (CS34⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 22 1 (CS02⁻ ∷ []) (refl) ▸
       at 21 4 (K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ K3⁻ ∷ []) (K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸ done

  b17 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b17 = at 23 1 (CS02⁻ ∷ []) (refl) ▸
       at 22 4 (K3 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ K3 ∷ []) (K3 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 24 1 (CS02⁻ ∷ []) (refl) ▸
       at 23 4 (CX14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 25 1 (CS02⁻ ∷ []) (refl) ▸
       at 24 4 (K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ K3⁻ ∷ []) (K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b18 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ CS13 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b18 = at 26 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 26 1 (CS02⁻ ∷ []) (refl) ▸
       at 25 4 (K3 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ K3 ∷ []) (K3 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 28 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 27 1 (CS02⁻ ∷ []) (refl) ▸
       at 27 2 (CS13 ∷ CS02⁻ ∷ []) (lw4 c4 (CS02⁻ ∷ CS13 ∷ []) (CS13 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 28 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸ done

  b19 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ CS13 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b19 = at 26 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 28 1 (CS02⁻ ∷ []) (refl) ▸
       at 27 4 (K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ K3⁻ ∷ []) (K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 29 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 13 15 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ []) (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CS02 ∷ []) (refl) ▸
       at 10 4 (K3 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ K3 ∷ []) (K3 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (Sb1-0-2-3 ∷ []) (refl) ▸ done

  b20 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b20 = at 12 1 (CS02 ∷ []) (refl) ▸
       at 11 4 (CX14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 13 1 (CS02 ∷ []) (refl) ▸
       at 12 4 (K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ []) (K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 14 1 (CS02 ∷ []) (refl) ▸
       at 13 4 (K3 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ K3 ∷ []) (K3 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b21 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b21 = at 15 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 15 1 (CS02 ∷ []) (refl) ▸
       at 14 4 (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 16 1 (CS02 ∷ []) (refl) ▸
       at 15 4 (K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ []) (K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 17 1 (CS02 ∷ []) (refl) ▸ done

  b22 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b22 = at 16 4 (K3 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ K3 ∷ []) (K3 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 18 1 (CS02 ∷ []) (refl) ▸
       at 17 4 (CX14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 19 1 (CS02 ∷ []) (refl) ▸
       at 18 4 (K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ []) (K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 1 (Sb1-0-2-3 ∷ []) (refl) ▸ done

  b23 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b23 = at 20 1 (CS02 ∷ []) (refl) ▸
       at 19 4 (K3 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ K3 ∷ []) (K3 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 22 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 21 1 (CS02 ∷ []) (refl) ▸
       at 21 2 (CS13 ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ CS13 ∷ []) (CS13 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 22 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 20 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸ done

  b24 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b24 = at 22 1 (CS02 ∷ []) (refl) ▸
       at 21 4 (K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ []) (K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 7 15 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ []) (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx1-4032 ∷ []) (lem-sym12-at01102442 c4) ▸
       at 5 1 (Bx1-4302 ∷ []) (lem-sym23-at01142042 c4) ▸
       at 5 1 (Toff134 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ []) (lem-beta-T-at0114233042 c4) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b25 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ X4 ∷ K3⁻ ∷ CCZ012 ∷ X4 ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b25 = at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 14 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 13 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 14 4 (CX14 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CCZ012 ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 16 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸ done

  b26 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ X4 ∷ K3⁻ ∷ CCZ012 ∷ X4 ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX02 ∷ CS01 ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b26 = at 15 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 18 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 17 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 16 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 18 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b27 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX02 ∷ CS01 ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b27 = at 28 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 29 4 (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 4 (CS34⁻ ∷ X4 ∷ CX02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CX02 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CX02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (CS34⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CS34⁻ ∷ X4 ∷ CX02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CX02 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CX02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS34⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b28 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ X4 ∷ K3 ∷ CCZ012 ∷ X4 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b28 = at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 19 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸
       at 18 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 21 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 20 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸ done

  b29 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ X4 ∷ K3 ∷ CCZ012 ∷ X4 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b29 = at 19 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 20 4 (CX14 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CCZ012 ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 22 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸
       at 21 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 24 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 23 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 22 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸ done

  b30 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ K3 ∷ X4 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b30 = at 25 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 24 2 (CS13 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CS13 ∷ []) (CS13 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 26 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 25 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸
       at 24 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 10 15 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ []) (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸ done

  b31 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ K3 ∷ X4 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ X4 ∷ K3 ∷ CCZ012 ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b31 = at 8 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 7 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 8 4 (CX14 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CCZ012 ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 10 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸
       at 9 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 12 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 11 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸ done

  b32 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ X4 ∷ K3 ∷ CCZ012 ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b32 = at 10 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 12 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CS34⁻ ∷ X4 ∷ CX02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CX02 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CX02 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b33 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ CCZ012 ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b33 = at 17 4 (CS34⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS34⁻ ∷ X4 ∷ CX02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CX02 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CX02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS34⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 13 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done

  b34 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ CCZ012 ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ X4 ∷ CCZ012 ∷ K3⁻ ∷ X4 ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b34 = at 14 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 13 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸
       at 12 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 15 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 14 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 13 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 14 4 (CX14 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CCZ012 ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸ done

  b35 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ X4 ∷ CCZ012 ∷ K3⁻ ∷ X4 ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ X4 ∷ CCZ012 ∷ X4 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b35 = at 16 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸
       at 15 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 18 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 17 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 16 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 19 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 18 2 (CS13 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CS13 ∷ []) (CS13 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸ done

  b36 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ X4 ∷ CCZ012 ∷ X4 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Bx1-4302 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b36 = at 20 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 19 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸
       at 18 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 4 15 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ []) (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 4 (Bx1-4302 ∷ []) (sym (lem-beta-T-at0114233042 c4)) ▸ done

  b37 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Bx1-4302 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b37 = at 17 1 (Bx1-4032 ∷ []) (lem-sym23-at0114233042 c4) ▸
       at 17 1 (Bx1-0432 ∷ []) (lem-sym12-at01142042 c4) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 5 (Sb1-0-43-2 ∷ []) (refl) ▸
       at 3 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸ done

  b38 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ Sb1-0-43-2 ∷ Sb2-0-3-1 ∷ X4 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b38 = at 4 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸
       at 2 5 (CCZ134 ∷ []) (lw0 c4 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 4 2 (CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ []) (CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b39 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ Sb1-0-43-2 ∷ Sb2-0-3-1 ∷ X4 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b39 = at 3 2 (Sb2-0-3-1 ∷ Sb1-0-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·1·3·0⟩-at01102442 c4) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 2 2 (CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ []) (CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 6 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸ done

  b40 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b40 = at 14 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (CS02⁻ ∷ []) (refl) ▸ done

  b41 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Bx1-0423 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b41 = at 15 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 12 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (CS02 ∷ []) (refl) ▸
       at 9 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 6 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx1-0423 ∷ []) (lem-sym34-at01102442 c4) ▸ done

  b42 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Bx1-0423 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ K3 ∷ Toff102 ∷ X4 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b42 = at 4 1 (Bx1-0243 ∷ []) (lem-sym23-at0110243243 c4) ▸
       at 4 1 (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) (lem-beta-T-at01103443 c4) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 10 2 (K3 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (K)) ▸ done

  b43 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ K3 ∷ Toff102 ∷ X4 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ X4 ∷ CS34 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b43 = at 9 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 11 1 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (lw4 c4 (Toff102 ∷ []) (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS34 ∷ X4 ∷ K1⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K1⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ K1⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b44 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ X4 ∷ CS34 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ CS34 ∷ X4 ∷ CS12 ∷ CX02 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b44 = at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CX02 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CX02 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b45 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ CS34 ∷ X4 ∷ CS12 ∷ CX02 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ CS34 ∷ X4 ∷ Toff102 ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b45 = at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS34 ∷ X4 ∷ K1 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K1 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ K1 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 3 (Toff102 ∷ []) (lw4 c4 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (Toff102 ∷ []) tt tt Eq.refl) ▸ done

  b46 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ CS34 ∷ X4 ∷ Toff102 ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X4 ∷ K1 ∷ CCZ012 ∷ K1⁻ ∷ X4 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b46 = at 13 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 12 2 (K3⁻ ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (K • iI)) ▸
       at 11 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 6 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 4 2 (K3 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (K)) ▸
       at 3 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 5 1 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (lw4 c4 (Toff102 ∷ []) (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸ done

  b47 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X4 ∷ K1 ∷ CCZ012 ∷ K1⁻ ∷ X4 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b47 = at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS34 ∷ X4 ∷ K1⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K1⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ K1⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b48 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ CS34 ∷ X4 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b48 = at 19 4 (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CX02 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CX02 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (CS34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b49 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ CS34 ∷ X4 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ X4 ∷ K3⁻ ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b49 = at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CS34 ∷ X4 ∷ K1 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K1 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ K1 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 3 (Toff102 ∷ []) (lw4 c4 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (Toff102 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 6 2 (K3⁻ ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (K • iI)) ▸ done

  b50 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ X4 ∷ K3⁻ ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b50 = at 5 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 4 (Bx1-0243 ∷ []) (sym (lem-beta-T-at01103443 c4)) ▸
       at 7 1 (Bx1-0423 ∷ []) (lem-sym23-at01103443 c4) ▸
       at 7 1 (Bx1-0432 ∷ []) (lem-sym34-at0110243243 c4) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b51 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b51 = at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 5 (Sb1-0-43-2 ∷ []) (refl) ▸
       at 7 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b52 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b52 = at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (CS02⁻ ∷ []) (refl) ▸
       at 18 4 (K3 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ K3 ∷ []) (K3 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 20 1 (CS02⁻ ∷ []) (refl) ▸
       at 19 4 (CX14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 21 1 (CS02⁻ ∷ []) (refl) ▸ done

  b53 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b53 = at 20 4 (K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ K3⁻ ∷ []) (K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 22 1 (CS02⁻ ∷ []) (refl) ▸
       at 21 4 (K3 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ K3 ∷ []) (K3 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 23 1 (CS02⁻ ∷ []) (refl) ▸
       at 22 4 (CS34⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸ done

  b54 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b54 = at 24 1 (CS02⁻ ∷ []) (refl) ▸
       at 23 4 (K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ K3⁻ ∷ []) (K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 25 1 (CS02⁻ ∷ []) (refl) ▸
       at 24 4 (K3 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ K3 ∷ []) (K3 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 26 1 (CS02⁻ ∷ []) (refl) ▸
       at 25 4 (CX14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b55 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ CS13 ∷ X4 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b55 = at 27 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 27 1 (CS02⁻ ∷ []) (refl) ▸
       at 26 4 (K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ K3⁻ ∷ []) (K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 28 1 (CS02⁻ ∷ []) (refl) ▸
       at 27 4 (K3 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ K3 ∷ []) (K3 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 29 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 30 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸ done

  b56 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ CS13 ∷ X4 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b56 = at 29 1 (CS02⁻ ∷ []) (refl) ▸
       at 29 2 (CS13 ∷ CS02⁻ ∷ []) (lw4 c4 (CS02⁻ ∷ CS13 ∷ []) (CS13 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 30 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 28 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 30 1 (CS02⁻ ∷ []) (refl) ▸
       at 29 4 (K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ K3⁻ ∷ []) (K3⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 31 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 15 15 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ []) (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b57 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b57 = at 13 1 (CS02 ∷ []) (refl) ▸
       at 12 4 (K3 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ K3 ∷ []) (K3 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 14 1 (CS02 ∷ []) (refl) ▸
       at 13 4 (CX14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 15 1 (CS02 ∷ []) (refl) ▸
       at 14 4 (K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ []) (K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b58 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b58 = at 16 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 16 1 (CS02 ∷ []) (refl) ▸
       at 15 4 (K3 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ K3 ∷ []) (K3 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 17 1 (CS02 ∷ []) (refl) ▸
       at 16 4 (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 18 1 (CS02 ∷ []) (refl) ▸ done

  b59 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b59 = at 17 4 (K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ []) (K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 19 1 (CS02 ∷ []) (refl) ▸
       at 18 4 (K3 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ K3 ∷ []) (K3 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 20 1 (CS02 ∷ []) (refl) ▸
       at 19 4 (CX14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 1 (Sb1-0-2-3 ∷ []) (refl) ▸ done

  b60 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ CS02 ∷ CS13 ∷ X4 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b60 = at 21 1 (CS02 ∷ []) (refl) ▸
       at 20 4 (K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ []) (K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 22 1 (CS02 ∷ []) (refl) ▸
       at 21 4 (K3 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ K3 ∷ []) (K3 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 24 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 23 1 (CS02 ∷ []) (refl) ▸ done

  b61 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ CS02 ∷ CS13 ∷ X4 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-4032 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b61 = at 23 2 (CS13 ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ CS13 ∷ []) (CS13 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 24 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 22 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 24 1 (CS02 ∷ []) (refl) ▸
       at 23 4 (K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ []) (K3⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 9 15 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ []) (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx1-4032 ∷ []) (lem-sym12-at01102442 c4) ▸ done

  b62 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx1-4032 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b62 = at 7 1 (Bx1-4302 ∷ []) (lem-sym23-at01142042 c4) ▸
       at 7 1 (Toff134 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ []) (lem-beta-T-at0114233042 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 16 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 15 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸ done

  b63 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b63 = at 16 4 (CX14 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CCZ012 ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 18 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸
       at 17 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 20 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 19 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 18 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 20 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) tt tt Eq.refl) ▸ done

  b64 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b64 = at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 30 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 31 4 (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 4 (CS34⁻ ∷ X4 ∷ CX02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CX02 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CX02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS34⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS34⁻ ∷ X4 ∷ CX02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CX02 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CX02 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b65 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ K3⁻ ∷ CCZ012 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b65 = at 19 4 (CS34⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 24 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 25 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 21 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸ done

  b66 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ K3⁻ ∷ CCZ012 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ X4 ∷ CCZ012 ∷ X4 ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b66 = at 20 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 23 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 22 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 21 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 22 4 (CX14 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CCZ012 ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 24 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸
       at 23 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸ done

  b67 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ X4 ∷ CCZ012 ∷ X4 ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ X4 ∷ K3⁻ ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b67 = at 26 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 25 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 24 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 27 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 26 2 (CS13 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CS13 ∷ []) (CS13 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 25 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 28 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 27 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸ done

  b68 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ X4 ∷ K3⁻ ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ X4 ∷ K3⁻ ∷ CCZ012 ∷ X4 ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b68 = at 26 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 12 15 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ []) (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 10 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 9 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 10 4 (CX14 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CCZ012 ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 12 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸ done

  b69 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ X4 ∷ K3⁻ ∷ CCZ012 ∷ X4 ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX02 ∷ CS01 ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b69 = at 11 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 14 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 13 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 12 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 14 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b70 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX02 ∷ CS01 ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b70 = at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS34⁻ ∷ X4 ∷ CX02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CX02 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CX02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS34⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS34⁻ ∷ X4 ∷ CX02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CX02 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CX02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS34⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b71 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ X4 ∷ K3 ∷ CCZ012 ∷ X4 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b71 = at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 15 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸
       at 14 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 17 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 16 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸ done

  b72 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ X4 ∷ K3 ∷ CCZ012 ∷ X4 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b72 = at 15 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 16 4 (CX14 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CCZ012 ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 18 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸
       at 17 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 20 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 19 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 18 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸ done

  b73 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b73 = at 21 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 20 2 (CS13 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CS13 ∷ []) (CS13 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 19 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 22 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 21 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸
       at 20 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 6 15 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ []) (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b74 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b74 = at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 4 (Bx1-4302 ∷ []) (sym (lem-beta-T-at0114233042 c4)) ▸
       at 19 1 (Bx1-4032 ∷ []) (lem-sym23-at0114233042 c4) ▸
       at 19 1 (Bx1-0432 ∷ []) (lem-sym12-at01142042 c4) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b75 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b75 = at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 5 (Sb1-0-43-2 ∷ []) (refl) ▸
       at 5 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (CCZ134 ∷ []) (lw0 c4 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸ done

  b76 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ [])
  b76 = at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 6 2 (CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 2 (Sb⁻2-0-3-1 ∷ Sb1-0-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·1·3·0⟩-at01102442 c4) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 2 (CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


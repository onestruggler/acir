{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D164 where

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
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at0214213043 ; lem-sym12-at0214203143 ; lem-sym23-at0214203143 ; lem-sym23-at0214213043 ; lem-sym34-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym12-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210243143 ; lem-sym34-at02142041)
open import Examples.Groups.Clifford+CS.Five.D.D013 using (lem-auto-BOX⟨0·1234⟩-∣-CS40-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-CSd40-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D154 using (lem-sym12-at01102442 ; lem-sym12-at01142042)
open import Examples.Groups.Clifford+CS.Five.D.D159 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D163 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ310-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·0·4⟩-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨3·1·0·4⟩-at0210243143 ; lem-beta-T-at0114233042 ; lem-beta-T-at0214233041 ; lem-sym23-at01142042 ; lem-sym23-at0114233042 ; lem-sym23-at02142041 ; lem-sym23-at0214233041)
-- F4 CS01^0|CS03^1: 772 steps
lem-F4-CS01ᵖ0∣CS03ᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣CS03ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (trans (run b62) (trans (run b63) (trans (run b64) (trans (run b65) (trans (run b66) (trans (run b67) (trans (run b68) (trans (run b69) (trans (run b70) (trans (run b71) (trans (run b72) (trans (run b73) (trans (run b74) (trans (run b75) (trans (run b76) (trans (run b77) (trans (run b78) (trans (run b79) (trans (run b80) (trans (run b81) (trans (run b82) (trans (run b83) (trans (run b84) (trans (run b85) (trans (run b86) (trans (run b87) (trans (run b88) (trans (run b89) (trans (run b90) (trans (run b91) (trans (run b92) (trans (run b93) (trans (run b94) (trans (run b95) (run b96))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb1-0-43-2 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b0 = at 3 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 3 1 (Bx1-4032 ∷ []) (lem-sym12-at01102442 c4) ▸
       at 3 1 (Bx1-4302 ∷ []) (lem-sym23-at01142042 c4) ▸
       at 3 1 (Toff134 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ []) (lem-beta-T-at0114233042 c4) ▸
       at 3 1 (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b1 = at 11 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (CS03⁻ ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (X4 ∷ Bx2-4013 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b2 = at 12 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 9 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 6 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸ done

  b3 : Chain (X4 ∷ Bx2-4013 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ X4 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b3 = at 1 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 1 1 (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-beta-T-at0214213043 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 10 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b4 : Chain (X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ X4 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b4 = at 11 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ K1⁻ ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b5 = at 13 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 5 (CCZ023 ∷ []) (lw4 c4 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b6 : Chain (X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ K1⁻ ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b6 = at 12 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 6 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 4 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 5 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b7 = at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b8 = at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 5 (CCZ023 ∷ []) (lw4 c4 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 6 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b9 : Chain (X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b9 = at 0 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 4 (Bx2-4103 ∷ []) (sym (lem-beta-T-at0214213043 c4)) ▸
       at 4 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸
       at 4 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b10 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b10 = at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 4 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b11 = at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (CS03⁻ ∷ []) (refl) ▸
       at 15 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 12 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (CS03 ∷ []) (refl) ▸
       at 9 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b12 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b12 = at 6 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 4 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 4 1 (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-beta-T-at0214213043 c4) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b13 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b13 = at 13 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 13 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 15 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 17 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 16 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b14 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b14 = at 15 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 17 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b15 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b15 = at 22 4 (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 5 (CCZ023 ∷ []) (lw4 c4 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b16 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ CCZ023 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b16 = at 19 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 18 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 20 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 19 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 19 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b17 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ CCZ023 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b17 = at 21 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 23 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 22 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 21 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 24 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 23 2 (CS13 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ CS13 ∷ []) (CS13 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸ done

  b18 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b18 = at 25 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 24 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 9 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 7 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 7 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b19 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b19 = at 10 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 9 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 11 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 10 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 11 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b20 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b20 = at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b21 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b21 = at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 5 (CCZ023 ∷ []) (lw4 c4 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 12 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b22 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b22 = at 14 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 13 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 13 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 15 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 17 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b23 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b23 = at 16 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 18 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 17 2 (CS13 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ CS13 ∷ []) (CS13 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 19 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 18 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b24 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b24 = at 3 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 4 (Bx2-4103 ∷ []) (sym (lem-beta-T-at0214213043 c4)) ▸
       at 16 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸
       at 16 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b25 : Chain (K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (K1 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b25 = at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 2 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸ done

  b26 : Chain (K1 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b26 = at 1 5 (CCZ134 ∷ []) (lw0 c4 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CCZ012 ∷ []) (CCZ012 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ310-at0210243143 c4) ▸
       at 1 2 (CCZ012 ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CCZ012 ∷ []) (CCZ012 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸ done

  b27 : Chain (Toff134 ∷ CCZ012 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b27 = at 10 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b28 : Chain (Toff134 ∷ CCZ012 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b28 = at 15 1 (CS03⁻ ∷ []) (refl) ▸
       at 14 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 11 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (CS03 ∷ []) (refl) ▸
       at 8 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 5 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b29 : Chain (Toff134 ∷ CCZ012 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b29 = at 3 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 3 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 3 1 (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-beta-T-at0214213043 c4) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 12 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b30 : Chain (Toff134 ∷ CCZ012 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b30 = at 11 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 13 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b31 : Chain (Toff134 ∷ CCZ012 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b31 = at 18 4 (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 4 (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 14 5 (CCZ023 ∷ []) (lw4 c4 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b32 : Chain (Toff134 ∷ CCZ012 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b32 = at 15 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 14 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 8 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 6 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 7 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) tt tt Eq.refl) ▸ done

  b33 : Chain (Toff134 ∷ CCZ012 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ X4 ∷ CS23 ∷ X4 ∷ CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b33 = at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 4 (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b34 : Chain (Toff134 ∷ CCZ012 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ X4 ∷ CS23 ∷ X4 ∷ CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ K1⁻ ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b34 = at 6 4 (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 5 (CCZ023 ∷ []) (lw4 c4 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 8 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b35 : Chain (Toff134 ∷ CCZ012 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ K1⁻ ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b35 = at 7 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 2 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 4 (Bx2-4103 ∷ []) (sym (lem-beta-T-at0214213043 c4)) ▸
       at 6 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸
       at 6 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸ done

  b36 : Chain (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b36 = at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 6 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b37 : Chain (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b37 = at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 1 (CS03⁻ ∷ []) (refl) ▸
       at 17 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 30 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 14 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (CS03 ∷ []) (refl) ▸
       at 11 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b38 : Chain (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b38 = at 24 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 8 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 6 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 6 1 (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-beta-T-at0214213043 c4) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b39 : Chain (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b39 = at 16 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 15 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 15 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 17 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 19 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b40 : Chain (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b40 = at 18 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 19 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 29 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 30 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b41 : Chain (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b41 = at 27 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 4 (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 4 (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 24 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b42 : Chain (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b42 = at 20 5 (CCZ023 ∷ []) (lw4 c4 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 21 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 20 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 19 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 22 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 21 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 21 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b43 : Chain (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS13 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b43 = at 24 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 23 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 25 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 24 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 26 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 25 2 (CS13 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ CS13 ∷ []) (CS13 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b44 : Chain (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS13 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b44 = at 24 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 27 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 26 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 25 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 11 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 9 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b45 : Chain (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b45 = at 9 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 11 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 13 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 12 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 13 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) tt tt Eq.refl) ▸ done

  b46 : Chain (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b46 = at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 4 (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b47 : Chain (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ K1⁻ ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b47 = at 12 4 (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 14 5 (CCZ023 ∷ []) (lw4 c4 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 14 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b48 : Chain (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ K1⁻ ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b48 = at 13 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 16 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 15 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 15 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 17 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b49 : Chain (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ X4 ∷ K1⁻ ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b49 = at 19 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 18 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 20 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 19 2 (CS13 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ CS13 ∷ []) (CS13 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 21 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 20 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b50 : Chain (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ X4 ∷ K1⁻ ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b50 = at 19 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 5 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff214 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 4 (Bx2-4103 ∷ []) (sym (lem-beta-T-at0214213043 c4)) ▸
       at 18 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸
       at 18 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸ done

  b51 : Chain (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b51 = at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 4 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸ done

  b52 : Chain (Toff134 ∷ CCZ012 ∷ K1 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-4032 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b52 = at 7 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 3 5 (CCZ134 ∷ []) (lw0 c4 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CCZ012 ∷ []) (CCZ012 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ310-at0210243143 c4) ▸
       at 3 2 (CCZ012 ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CCZ012 ∷ []) (CCZ012 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx1-4302 ∷ []) (sym (lem-beta-T-at0114233042 c4)) ▸
       at 0 1 (Bx1-4032 ∷ []) (lem-sym23-at0114233042 c4) ▸ done

  b53 : Chain (Bx1-4032 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ234 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b53 = at 0 1 (Bx1-0432 ∷ []) (lem-sym12-at01142042 c4) ▸
       at 4 1 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (lw0 c4 (Toff234 ∷ []) (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K2 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2 ∷ []) (K2 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (K2 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at0210243143 c4) ▸
       at 1 2 (K2 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2 ∷ []) (K2 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b54 : Chain (Bx1-0432 ∷ K2 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CCZ234 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ CCZ234 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b54 = at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 1 (CS03⁻ ∷ []) (refl) ▸
       at 14 4 (CCZ234 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CCZ234 ∷ []) (CCZ234 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 11 4 (CCZ234 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ X4 ∷ CCZ234 ∷ []) (CCZ234 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (CS03 ∷ []) (refl) ▸
       at 8 4 (CCZ234 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CCZ234 ∷ []) (CCZ234 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b55 : Chain (Bx1-0432 ∷ K2 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ CCZ234 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS23 ∷ X4 ∷ Bx2-4013 ∷ X4 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b55 = at 10 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 5 4 (CCZ234 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ X4 ∷ CCZ234 ∷ []) (CCZ234 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ []) (CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS23 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS40-at0210243143 c4) ▸
       at 2 2 (CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ []) (CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (K3 ∷ CZ34 ∷ K3⁻ ∷ []) (lw0 c4 (CX43 ∷ []) (K3 ∷ CZ34 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸ done

  b56 : Chain (Bx1-0432 ∷ K2 ∷ CS23 ∷ X4 ∷ Bx2-4013 ∷ X4 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ K3 ∷ CCZ012 ∷ X4 ∷ CZ34 ∷ K3⁻ ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b56 = at 4 1 (Bx2-4031 ∷ []) (lem-sym34-at0214203143 c4) ▸
       at 4 1 (Bx2-4301 ∷ []) (lem-sym23-at02142041 c4) ▸
       at 4 1 (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-beta-T-at0214233041 c4) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 13 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸ done

  b57 : Chain (Bx1-0432 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ K3 ∷ CCZ012 ∷ X4 ∷ CZ34 ∷ K3⁻ ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b57 = at 12 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 14 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CZ34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CX01 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b58 : Chain (Bx1-0432 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ X4 ∷ CCZ012 ∷ X4 ∷ K3⁻ ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b58 = at 19 4 (CZ34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CX01 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CZ34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done

  b59 : Chain (Bx1-0432 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ X4 ∷ CCZ012 ∷ X4 ∷ K3⁻ ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ X4 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b59 = at 16 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 15 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸
       at 14 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 9 6 (K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ []) (K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 7 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 6 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 8 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸ done

  b60 : Chain (Bx1-0432 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ X4 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b60 = at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CZ34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CX01 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CZ34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CX01 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b61 : Chain (Bx1-0432 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ X4 ∷ K3⁻ ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b61 = at 7 4 (CZ34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 9 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸ done

  b62 : Chain (Bx1-0432 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ X4 ∷ K3⁻ ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS23 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Bx2-4013 ∷ X4 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b62 = at 8 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 3 6 (K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ []) (K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 4 (Bx2-4301 ∷ []) (sym (lem-beta-T-at0214233041 c4)) ▸
       at 7 1 (Bx2-4031 ∷ []) (lem-sym23-at0214233041 c4) ▸
       at 7 1 (Bx2-4013 ∷ []) (lem-sym34-at02142041 c4) ▸ done

  b63 : Chain (Bx1-0432 ∷ K2 ∷ CS23 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Bx2-4013 ∷ X4 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Bx2-4031 ∷ X4 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b63 = at 7 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 3 3 (CX43 ∷ []) (lw0 c4 (K3 ∷ CZ34 ∷ K3⁻ ∷ []) (CX43 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS23⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd40-at0210243143 c4) ▸
       at 4 2 (CS23⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (K3 ∷ CZ34 ∷ K3⁻ ∷ []) (lw0 c4 (CX43 ∷ []) (K3 ∷ CZ34 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 6 1 (Bx2-4031 ∷ []) (lem-sym34-at0214203143 c4) ▸ done

  b64 : Chain (Bx1-0432 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Bx2-4031 ∷ X4 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CZ34 ∷ K3⁻ ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b64 = at 6 1 (Bx2-4301 ∷ []) (lem-sym23-at02142041 c4) ▸
       at 6 1 (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-beta-T-at0214233041 c4) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 15 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 14 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸ done

  b65 : Chain (Bx1-0432 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CZ34 ∷ K3⁻ ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ CZ34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b65 = at 16 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 4 (CZ34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 4 (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CX01 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 4 (CZ34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b66 : Chain (Bx1-0432 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ CZ34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ X4 ∷ CCZ012 ∷ K3⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b66 = at 18 4 (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CX01 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (CZ34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸ done

  b67 : Chain (Bx1-0432 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ X4 ∷ CCZ012 ∷ K3⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ X4 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b67 = at 17 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸
       at 16 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 11 6 (K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ []) (K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 9 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 8 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 10 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b68 : Chain (Bx1-0432 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ X4 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b68 = at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 4 (CZ34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 4 (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CX01 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (CZ34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 4 (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CX01 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 4 (CZ34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b69 : Chain (Bx1-0432 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b69 = at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 11 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸
       at 10 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸ done

  b70 : Chain (Bx1-0432 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b70 = at 5 6 (K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ []) (K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 4 (Bx2-4301 ∷ []) (sym (lem-beta-T-at0214233041 c4)) ▸
       at 9 1 (Bx2-4031 ∷ []) (lem-sym23-at0214233041 c4) ▸
       at 9 1 (Bx2-4013 ∷ []) (lem-sym34-at02142041 c4) ▸
       at 9 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸ done

  b71 : Chain (Bx1-0432 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ X4 ∷ Toff204 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b71 = at 5 3 (CX43 ∷ []) (lw0 c4 (K3 ∷ CZ34 ∷ K3⁻ ∷ []) (CX43 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff204 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b72 : Chain (Bx1-0432 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ X4 ∷ Toff204 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ K2 ∷ CCZ234 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b72 = at 6 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff204 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 2 5 (CCZ234 ∷ []) (lw0 c4 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b73 : Chain (Bx1-0432 ∷ K2 ∷ CCZ234 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS02 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b73 = at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 5 2 (K2⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2⁻ ∷ []) (K2⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (K2⁻ ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at0210243143 c4) ▸
       at 3 2 (K2⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2⁻ ∷ []) (K2⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff234 ∷ []) (lw0 c4 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (Toff234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS02 ∷ []) (refl) ▸ done

  b74 : Chain (Bx1-0432 ∷ Toff234 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS02 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Sb2-0-41-3 ∷ K2 ∷ X4 ∷ CCZ234 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b74 = at 4 2 (CS02 ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02 ∷ []) (CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 3 2 (Sb1-0-2-3 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·0·4⟩-at0210243143 c4) ▸
       at 3 1 (CS02 ∷ []) (refl) ▸
       at 2 2 (CS02 ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02 ∷ []) (CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 6 1 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (lw0 c4 (Toff234 ∷ []) (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K2 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2 ∷ []) (K2 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b75 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ Sb2-0-41-3 ∷ K2 ∷ X4 ∷ CCZ234 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CCZ234 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b75 = at 4 2 (K2 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at0210243143 c4) ▸
       at 3 2 (K2 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2 ∷ []) (K2 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 1 (CS03⁻ ∷ []) (refl) ▸ done

  b76 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CCZ234 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b76 = at 16 4 (CCZ234 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CCZ234 ∷ []) (CCZ234 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 13 4 (CCZ234 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ X4 ∷ CCZ234 ∷ []) (CCZ234 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CS03 ∷ []) (refl) ▸
       at 10 4 (CCZ234 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CCZ234 ∷ []) (CCZ234 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 7 4 (CCZ234 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ X4 ∷ CCZ234 ∷ []) (CCZ234 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) tt tt Eq.refl) ▸ done

  b77 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ X4 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b77 = at 6 2 (CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ []) (CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS23 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS40-at0210243143 c4) ▸
       at 4 2 (CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ []) (CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (K3 ∷ CZ34 ∷ K3⁻ ∷ []) (lw0 c4 (CX43 ∷ []) (K3 ∷ CZ34 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 6 1 (Bx2-4031 ∷ []) (lem-sym34-at0214203143 c4) ▸
       at 6 1 (Bx2-4301 ∷ []) (lem-sym23-at02142041 c4) ▸
       at 6 1 (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-beta-T-at0214233041 c4) ▸ done

  b78 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ X4 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ X4 ∷ CZ34 ∷ K3⁻ ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b78 = at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 15 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 14 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 16 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b79 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ X4 ∷ CZ34 ∷ K3⁻ ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b79 = at 20 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 4 (CZ34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 4 (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CX01 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 4 (CZ34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 4 (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CX01 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (CZ34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b80 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b80 = at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 17 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸
       at 16 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸ done

  b81 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX01 ∷ CS02 ∷ X4 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b81 = at 11 6 (K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ []) (K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 9 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 8 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 10 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b82 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX01 ∷ CS02 ∷ X4 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ X4 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b82 = at 20 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 4 (CZ34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 4 (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CX01 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (CZ34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 4 (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CX01 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 4 (CZ34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b83 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ X4 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b83 = at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 11 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸
       at 10 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 5 6 (K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ []) (K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b84 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ CX43 ∷ X4 ∷ Bx2-0413 ∷ CS23⁻ ∷ X4 ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b84 = at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 4 (Bx2-4301 ∷ []) (sym (lem-beta-T-at0214233041 c4)) ▸
       at 9 1 (Bx2-4031 ∷ []) (lem-sym23-at0214233041 c4) ▸
       at 9 1 (Bx2-4013 ∷ []) (lem-sym34-at02142041 c4) ▸
       at 9 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 5 3 (CX43 ∷ []) (lw0 c4 (K3 ∷ CZ34 ∷ K3⁻ ∷ []) (CX43 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CS23⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b85 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ CX43 ∷ X4 ∷ Bx2-0413 ∷ CS23⁻ ∷ X4 ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ X4 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b85 = at 7 2 (CS23⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd40-at0210243143 c4) ▸
       at 6 2 (CS23⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (K3 ∷ CZ34 ∷ K3⁻ ∷ []) (lw0 c4 (CX43 ∷ []) (K3 ∷ CZ34 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 8 1 (Bx2-4031 ∷ []) (lem-sym34-at0214203143 c4) ▸
       at 8 1 (Bx2-4301 ∷ []) (lem-sym23-at02142041 c4) ▸
       at 8 1 (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-beta-T-at0214233041 c4) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b86 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ X4 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ X4 ∷ CZ34 ∷ K3⁻ ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b86 = at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 17 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 16 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 18 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b87 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ X4 ∷ CZ34 ∷ K3⁻ ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ X4 ∷ CS12 ∷ CX01 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b87 = at 25 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 29 4 (CZ34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 4 (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CX01 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (CZ34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CX01 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CZ34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b88 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ X4 ∷ CS12 ∷ CX01 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b88 = at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 19 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸
       at 18 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 13 6 (K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ []) (K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b89 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b89 = at 12 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 11 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 10 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 12 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b90 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX01 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ X4 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b90 = at 23 4 (CZ34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CX01 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CZ34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CX01 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CX01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CZ34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CZ34 ∷ []) (CZ34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b91 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ X4 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b91 = at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 13 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 13 2 (K3⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (K • iI)) ▸
       at 12 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 7 6 (K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ []) (K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b92 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ K3 ∷ CZ34 ∷ K3⁻ ∷ X4 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b92 = at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 4 (Bx2-4301 ∷ []) (sym (lem-beta-T-at0214233041 c4)) ▸
       at 11 1 (Bx2-4031 ∷ []) (lem-sym23-at0214233041 c4) ▸
       at 11 1 (Bx2-4013 ∷ []) (lem-sym34-at02142041 c4) ▸
       at 11 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 7 3 (CX43 ∷ []) (lw0 c4 (K3 ∷ CZ34 ∷ K3⁻ ∷ []) (CX43 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b93 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b93 = at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff204 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff204 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b94 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CCZ234 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ [])
  b94 = at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 4 5 (CCZ234 ∷ []) (lw0 c4 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

  b95 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ K2 ∷ CCZ234 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ K2⁻ ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b95 = at 7 2 (K2⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2⁻ ∷ []) (K2⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K2⁻ ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at0210243143 c4) ▸
       at 5 2 (K2⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2⁻ ∷ []) (K2⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Toff234 ∷ []) (lw0 c4 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (Toff234 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS02⁻ ∷ []) (refl) ▸
       at 6 2 (CS02⁻ ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 5 2 (Sb⁻1-0-2-3 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨3·1·0·4⟩-at0210243143 c4) ▸ done

  b96 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (Sb1-0-43-2 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b96 = at 5 1 (CS02⁻ ∷ []) (refl) ▸
       at 4 2 (CS02⁻ ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-43-2 ∷ []) (refl) ▸ done


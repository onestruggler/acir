{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D225 where

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
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F0d)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-BOXd-BOX-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210243143 ; lem-beta-T-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-F5-CS01)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-beta-T-at0210233441 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.D081 using (lem-BOXd-BOX-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D157 using (lem-beta-T-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D224 using (lem-AX-SB-at3443 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at0210243143 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0210243143 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0210243143)
-- F2 CS01|CS23: 975 steps
lem-F2-CS01∣CS23 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F2-CS01∣CS23 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (trans (run b62) (trans (run b63) (trans (run b64) (trans (run b65) (trans (run b66) (trans (run b67) (trans (run b68) (trans (run b69) (trans (run b70) (trans (run b71) (trans (run b72) (trans (run b73) (trans (run b74) (trans (run b75) (trans (run b76) (trans (run b77) (trans (run b78) (trans (run b79) (trans (run b80) (trans (run b81) (trans (run b82) (trans (run b83) (trans (run b84) (trans (run b85) (trans (run b86) (trans (run b87) (trans (run b88) (trans (run b89) (trans (run b90) (trans (run b91) (trans (run b92) (trans (run b93) (trans (run b94) (trans (run b95) (trans (run b96) (trans (run b97) (trans (run b98) (trans (run b99) (trans (run b100) (trans (run b101) (trans (run b102) (trans (run b103) (trans (run b104) (trans (run b105) (trans (run b106) (trans (run b107) (trans (run b108) (trans (run b109) (trans (run b110) (trans (run b111) (trans (run b112) (trans (run b113) (trans (run b114) (trans (run b115) (trans (run b116) (trans (run b117) (trans (run b118) (trans (run b119) (trans (run b120) (run b121)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 0 (CS03 ∷ CS03⁻ ∷ []) (lw4 c4 [] (CS03 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 2 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (CS03⁻ ∷ CS03 ∷ []) (lw4 c4 [] (CS03⁻ ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ [])
  b1 = at 4 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (lw4 c4 [] (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 8 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 5 6 (Bx⁻0-213 ∷ []) (refl) ▸
       at 8 1 (Bx2-03 ∷ []) (refl) ▸
       at 11 1 (Bx2-03 ∷ []) (refl) ▸
       at 6 6 (Bx0-213 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ [])
  b2 = at 6 0 (CCZ024 ∷ CCZ024 ∷ []) (pw1 c4 [] (CCZ024 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Toff204 ∷ Toff204 ∷ []) (pw1 c4 [] (Toff204 ∷ Toff204 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (lw4 c4 [] (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 11 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 8 6 (Bx⁻0-213 ∷ []) (refl) ▸
       at 11 1 (Bx2-03 ∷ []) (refl) ▸
       at 14 1 (Bx2-03 ∷ []) (refl) ▸ done

  b3 : Chain (X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ [])
  b3 = at 9 6 (Bx0-213 ∷ []) (refl) ▸
       at 9 0 (Toff204 ∷ Toff204 ∷ []) (pw1 c4 [] (Toff204 ∷ Toff204 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (CCZ024 ∷ CCZ024 ∷ []) (pw1 c4 [] (CCZ024 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 6 (Bx⁻2-0413 ∷ []) (refl) ▸
       at 6 6 (Bx2-0413 ∷ []) (refl) ▸
       at 1 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 2 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b4 = at 3 4 (CS01 ∷ []) (lem-F5-CS01 c4) ▸
       at 3 2 (Sb0-2-43-1 ∷ CS01 ∷ []) (lem-AX-SB-at3443 c4) ▸
       at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 3 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (pw1 c4 (Toff024 ∷ []) (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b5 = at 11 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸ done

  b6 : Chain (X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b6 = at 13 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 22 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 21 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 23 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b7 = at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 30 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 33 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 34 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS12 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 31 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 4 (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ K0⁻ ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b8 = at 22 4 (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS23 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 26 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 27 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 28 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 24 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 25 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 24 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸ done

  b9 : Chain (X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ K0⁻ ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b9 = at 23 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 18 6 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 16 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 15 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 17 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CS23 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b10 = at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS12 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS23 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b11 : Chain (X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CS23 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b11 = at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 19 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 18 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 17 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 12 6 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b12 = at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 16 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸
       at 9 6 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff314 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸ done

  b13 : Chain (X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b13 = at 0 12 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 10 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸ done

  b14 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b14 = at 4 1 (Sb⁻3-0-41-2 ∷ []) (lem-F0d c4) ▸
       at 4 1 (Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ Toff214 ∷ Bx⁻3-0412 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (Bx3-0412 ∷ []) (lem-BOXd-BOX-at0310243142 c4) ▸
       at 16 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-beta-T-at0310243142 c4) ▸ done

  b15 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ X4 ∷ CCZ123 ∷ K0⁻ ∷ X4 ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b15 = at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 25 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 24 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 25 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CX24 ∷ []) (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸ done

  b16 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ X4 ∷ CCZ123 ∷ K0⁻ ∷ X4 ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b16 = at 27 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 26 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 29 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 28 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 27 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 29 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 30 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 33 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b17 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ CS23 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b17 = at 36 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 39 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 40 4 (CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 37 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CX12 ∷ X4 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 34 4 (CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 31 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CX12 ∷ X4 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 4 (CS04⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS23 ∷ X4 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 31 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b18 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ CS23 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ X4 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b18 = at 32 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 33 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 34 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 30 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 31 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 30 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 29 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 32 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸ done

  b19 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ X4 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ X4 ∷ K0 ∷ CCZ123 ∷ X4 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b19 = at 31 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 30 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 31 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CX24 ∷ []) (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 34 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 33 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 32 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 35 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 34 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸ done

  b20 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ X4 ∷ K0 ∷ CCZ123 ∷ X4 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b20 = at 33 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 36 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 35 2 (CS02 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CS02 ∷ []) (CS02 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 34 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 37 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 36 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 35 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 21 15 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ []) (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b21 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ X4 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b21 = at 20 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 19 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 18 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 19 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CX24 ∷ []) (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 21 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 20 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 23 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸ done

  b22 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ X4 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b22 = at 22 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 21 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 23 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 30 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 33 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 34 4 (CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b23 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b23 = at 31 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CX12 ∷ X4 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 4 (CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CX12 ∷ X4 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS04⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS23 ∷ X4 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 26 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 27 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 28 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b24 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b24 = at 24 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 25 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 24 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 23 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 26 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 25 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 24 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 25 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CX24 ∷ []) (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b25 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS02 ∷ CCZ123 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b25 = at 28 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 27 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 26 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 29 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 28 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 27 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 30 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 29 2 (CS02 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CS02 ∷ []) (CS02 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸ done

  b26 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS02 ∷ CCZ123 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b26 = at 28 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 31 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 30 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 29 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 15 15 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ []) (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 29 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 30 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 31 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b27 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Bx⁻3-0412 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b27 = at 28 4 (Bx3-0412 ∷ []) (sym (lem-beta-T-at0310243142 c4)) ▸
       at 28 1 (Bx⁻3-0412 ∷ []) (sym (lem-BOXd-BOX-at0310243142 c4)) ▸
       at 12 15 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ Toff214 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ []) (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS02 ∷ []) (refl) ▸
       at 10 1 (CS02⁻ ∷ []) (refl) ▸
       at 3 21 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ []) (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 22 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸ done

  b28 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Bx⁻3-0412 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (K0 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b28 = at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 5 (Sb⁻3-0-41-2 ∷ []) (refl) ▸
       at 16 1 (Sb⁻2-0-41-3 ∷ []) (sym (lem-F0d c4)) ▸
       at 2 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸ done

  b29 : Chain (K0 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ K0 ∷ CCZ024 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b29 = at 4 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 1 5 (CCZ024 ∷ []) (pw1 c4 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff024 ∷ []) (pw1 c4 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (Toff024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CCZ013 ∷ []) (CCZ013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ013 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at0210243143 c4) ▸
       at 1 2 (CCZ013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CCZ013 ∷ []) (CCZ013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (pw1 c4 (Toff024 ∷ []) (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸ done

  b30 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ K0 ∷ CCZ024 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b30 = at 6 1 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b31 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b31 = at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 15 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸ done

  b32 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b32 = at 24 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 23 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 25 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 26 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 29 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 32 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 35 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 36 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS12 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b33 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b33 = at 33 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 30 4 (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 4 (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS23 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 28 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 29 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 30 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b34 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b34 = at 26 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 27 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 26 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 25 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 20 6 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 18 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 17 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸ done

  b35 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b35 = at 19 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 29 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 30 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS12 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 4 (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b36 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CCZ123 ∷ K0⁻ ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b36 = at 21 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 4 (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS23 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 24 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 21 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸ done

  b37 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CCZ123 ∷ K0⁻ ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b37 = at 20 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 19 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 14 6 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 18 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸ done

  b38 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b38 = at 11 6 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff314 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 9 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 12 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 12 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b39 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ Bx⁻3-0412 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b39 = at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 6 1 (Sb⁻3-0-41-2 ∷ []) (lem-F0d c4) ▸
       at 6 1 (Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ Toff214 ∷ Bx⁻3-0412 ∷ []) (refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b40 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ Bx⁻3-0412 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ K0 ∷ CCZ123 ∷ X4 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b40 = at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 1 (Bx3-0412 ∷ []) (lem-BOXd-BOX-at0310243142 c4) ▸
       at 18 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-beta-T-at0310243142 c4) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 27 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸ done

  b41 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ K0 ∷ CCZ123 ∷ X4 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b41 = at 26 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 27 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CX24 ∷ []) (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 30 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 29 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 28 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 31 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 30 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 29 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸ done

  b42 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b42 = at 31 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 32 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 35 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 38 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 41 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 42 4 (CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 39 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CX12 ∷ X4 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 36 4 (CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b43 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ CCZ123 ∷ K0⁻ ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b43 = at 33 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CX12 ∷ X4 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 30 4 (CS04⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS23 ∷ X4 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 33 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 34 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 35 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 36 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 32 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 33 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸ done

  b44 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ CCZ123 ∷ K0⁻ ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ X4 ∷ K0⁻ ∷ CCZ123 ∷ X4 ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b44 = at 32 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 31 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 34 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 33 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 32 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 33 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CX24 ∷ []) (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 36 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 35 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸ done

  b45 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ X4 ∷ K0⁻ ∷ CCZ123 ∷ X4 ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ X4 ∷ CCZ123 ∷ K0⁻ ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b45 = at 34 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 37 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 36 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 35 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 38 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 37 2 (CS02 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CS02 ∷ []) (CS02 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 36 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 39 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸ done

  b46 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ X4 ∷ CCZ123 ∷ K0⁻ ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ X4 ∷ CCZ123 ∷ K0⁻ ∷ X4 ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b46 = at 38 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 37 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 23 15 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ []) (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 21 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 20 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 21 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CX24 ∷ []) (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸ done

  b47 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ X4 ∷ CCZ123 ∷ K0⁻ ∷ X4 ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b47 = at 23 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 22 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 25 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 24 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 23 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 25 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 26 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 29 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b48 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ CS23 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b48 = at 32 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 35 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 36 4 (CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 33 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CX12 ∷ X4 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 30 4 (CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CX12 ∷ X4 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 4 (CS04⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS23 ∷ X4 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b49 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ CS23 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ X4 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b49 = at 28 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 29 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 30 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 26 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 27 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 26 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 25 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 28 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸ done

  b50 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ X4 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ X4 ∷ K0 ∷ CCZ123 ∷ X4 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b50 = at 27 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 26 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 27 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CX24 ∷ []) (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 30 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 29 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 28 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 31 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 30 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸ done

  b51 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ X4 ∷ K0 ∷ CCZ123 ∷ X4 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b51 = at 29 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 32 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 31 2 (CS02 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CS02 ∷ []) (CS02 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 30 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 33 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 32 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 31 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 17 15 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ []) (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b52 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Bx⁻3-0412 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b52 = at 31 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 32 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 33 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 30 4 (Bx3-0412 ∷ []) (sym (lem-beta-T-at0310243142 c4)) ▸
       at 30 1 (Bx⁻3-0412 ∷ []) (sym (lem-BOXd-BOX-at0310243142 c4)) ▸
       at 14 15 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ Toff214 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ []) (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS02 ∷ []) (refl) ▸
       at 12 1 (CS02⁻ ∷ []) (refl) ▸ done

  b53 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Bx⁻3-0412 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Sb⁻3-0-41-2 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b53 = at 5 21 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ []) (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 24 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 5 (Sb⁻3-0-41-2 ∷ []) (refl) ▸ done

  b54 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Sb⁻3-0-41-2 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ CCZ013 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b54 = at 18 1 (Sb⁻2-0-41-3 ∷ []) (sym (lem-F0d c4)) ▸
       at 4 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 3 5 (CCZ024 ∷ []) (pw1 c4 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Toff024 ∷ []) (pw1 c4 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (Toff024 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CCZ013 ∷ []) (CCZ013 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b55 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ CCZ013 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b55 = at 4 2 (CCZ013 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at0210243143 c4) ▸
       at 3 2 (CCZ013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CCZ013 ∷ []) (CCZ013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 4 1 (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸ done

  b56 : Chain (Bx0-2431 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx2-0431 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b56 = at 15 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 14 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸ done

  b57 : Chain (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx2-0431 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ K1 ∷ Toff203 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b57 = at 14 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 14 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 20 2 (K1 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1 ∷ []) (K1 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸ done

  b58 : Chain (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ K1 ∷ Toff203 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b58 = at 19 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 21 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (lw4 c4 (Toff203 ∷ []) (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 4 (CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 25 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b59 : Chain (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b59 = at 31 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 34 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 35 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 32 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 29 4 (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b60 : Chain (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ Toff203 ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b60 = at 27 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 28 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 29 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 25 5 (CCZ023 ∷ []) (lw4 c4 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 24 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 3 (Toff203 ∷ []) (lw4 c4 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) tt tt Eq.refl) ▸ done

  b61 : Chain (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ Toff203 ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b61 = at 23 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 22 2 (K1⁻ ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 21 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 16 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 14 2 (K1 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1 ∷ []) (K1 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 15 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (lw4 c4 (Toff203 ∷ []) (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸ done

  b62 : Chain (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b62 = at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b63 : Chain (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b63 = at 29 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b64 : Chain (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ K1⁻ ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b64 = at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 5 (CCZ023 ∷ []) (lw4 c4 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 3 (Toff203 ∷ []) (lw4 c4 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 16 2 (K1⁻ ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff203 ∷ []) tt tt Eq.refl) ▸ done

  b65 : Chain (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ K1⁻ ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b65 = at 15 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸
       at 17 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸
       at 17 1 (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4) ▸
       at 17 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸ done

  b66 : Chain (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b66 = at 10 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (CS03⁻ ∷ []) (refl) ▸
       at 7 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS03 ∷ []) (refl) ▸
       at 1 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b67 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b67 = at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 5 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b68 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b68 = at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 17 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸
       at 17 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 17 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b69 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ X4 ∷ K1⁻ ∷ Toff203 ∷ X4 ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b69 = at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 23 2 (K1 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1 ∷ []) (K1 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 23 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff203 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 25 2 (K1⁻ ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff203 ∷ []) tt tt Eq.refl) ▸ done

  b70 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ X4 ∷ K1⁻ ∷ Toff203 ∷ X4 ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b70 = at 24 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 27 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 26 2 (K1 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1 ∷ []) (K1 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 25 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 27 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (lw4 c4 (Toff203 ∷ []) (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 28 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 31 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 32 4 (CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2⁻ ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b71 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b71 = at 30 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 31 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 34 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 37 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 40 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 41 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 38 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 35 4 (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b72 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b72 = at 32 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 29 4 (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 32 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 33 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 34 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 35 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 31 5 (CCZ023 ∷ []) (lw4 c4 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 26 4 (CS14⁻ ∷ X4 ∷ K2 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ K2 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b73 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ K1 ∷ Toff203 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b73 = at 29 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 30 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 28 3 (Toff203 ∷ []) (lw4 c4 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) tt tt Eq.refl) ▸
       at 29 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 28 2 (K1⁻ ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 27 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 30 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 29 2 (K1 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1 ∷ []) (K1 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸ done

  b74 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ K1 ∷ Toff203 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ Toff203 ∷ X4 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b74 = at 28 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 29 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff203 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 32 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 31 2 (K1⁻ ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 30 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 33 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 32 2 (K1 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1 ∷ []) (K1 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 31 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b75 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ Toff203 ∷ X4 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ K1 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b75 = at 34 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 33 2 (CS13 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ CS13 ∷ []) (CS13 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 32 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 35 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 34 2 (K1⁻ ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 33 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 19 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b76 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ K1 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ K1 ∷ Toff203 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b76 = at 17 2 (K1 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1 ∷ []) (K1 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 17 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff203 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 19 2 (K1⁻ ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 21 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 20 2 (K1 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1 ∷ []) (K1 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸ done

  b77 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ K1 ∷ Toff203 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b77 = at 19 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 21 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (lw4 c4 (Toff203 ∷ []) (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 4 (CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2⁻ ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 25 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b78 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS23 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b78 = at 31 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 34 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 35 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 32 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 29 4 (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b79 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS23 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b79 = at 27 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 28 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 29 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 25 5 (CCZ023 ∷ []) (lw4 c4 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CS14⁻ ∷ X4 ∷ K2 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ K2 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 24 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 3 (Toff203 ∷ []) (lw4 c4 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) tt tt Eq.refl) ▸ done

  b80 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b80 = at 23 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 22 2 (K1⁻ ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 21 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 24 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 23 2 (K1 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1 ∷ []) (K1 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 23 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff203 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b81 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ X4 ∷ Toff203 ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b81 = at 25 2 (K1⁻ ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 24 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 27 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 26 2 (K1 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1 ∷ []) (K1 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 25 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 28 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 27 2 (CS13 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ CS13 ∷ []) (CS13 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 26 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸ done

  b82 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ X4 ∷ Toff203 ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Bx2-0431 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b82 = at 29 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 28 2 (K1⁻ ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 27 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 30 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 31 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 32 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 29 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸
       at 29 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸ done

  b83 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Bx2-0431 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b83 = at 29 1 (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4) ▸
       at 29 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸
       at 13 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CS03⁻ ∷ []) (refl) ▸
       at 10 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 7 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸ done

  b84 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b84 = at 4 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 3 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸ done

  b85 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b85 = at 4 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 2 5 (CCZ134 ∷ []) (lw0 c4 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 4 2 (CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ []) (CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b86 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b86 = at 3 2 (Sb0-2-1-3 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0210243143 c4) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 2 2 (CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ []) (CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 6 1 (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸ done

  b87 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b87 = at 14 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸ done

  b88 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ K1 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b88 = at 16 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸
       at 16 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 16 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b89 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ K1 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b89 = at 22 2 (K1 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1 ∷ []) (K1 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 21 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 23 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (lw4 c4 (Toff203 ∷ []) (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 4 (CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b90 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b90 = at 30 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 33 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 36 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 37 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 34 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 31 4 (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b91 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b91 = at 28 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 29 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 30 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 31 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 27 5 (CCZ023 ∷ []) (lw4 c4 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 26 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b92 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ Toff203 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b92 = at 24 3 (Toff203 ∷ []) (lw4 c4 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) tt tt Eq.refl) ▸
       at 25 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 24 2 (K1⁻ ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 18 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 16 2 (K1 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1 ∷ []) (K1 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b93 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ Toff203 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b93 = at 17 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (lw4 c4 (Toff203 ∷ []) (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b94 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b94 = at 30 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 31 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b95 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b95 = at 24 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 25 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 5 (CCZ023 ∷ []) (lw4 c4 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 3 (Toff203 ∷ []) (lw4 c4 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) tt tt Eq.refl) ▸
       at 19 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b96 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b96 = at 18 2 (K1⁻ ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸
       at 19 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸
       at 19 1 (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4) ▸ done

  b97 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b97 = at 19 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸
       at 12 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (CS03⁻ ∷ []) (refl) ▸
       at 9 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 6 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS03 ∷ []) (refl) ▸
       at 3 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b98 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b98 = at 7 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 7 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b99 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b99 = at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 19 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸
       at 19 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 19 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b100 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b100 = at 23 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 25 2 (K1 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1 ∷ []) (K1 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 24 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 25 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff203 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b101 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b101 = at 27 2 (K1⁻ ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 26 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 29 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 28 2 (K1 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1 ∷ []) (K1 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 27 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 29 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (lw4 c4 (Toff203 ∷ []) (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 30 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 33 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b102 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b102 = at 34 4 (CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2⁻ ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 32 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 33 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 36 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 39 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 42 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 43 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 40 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b103 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b103 = at 37 4 (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 34 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 31 4 (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 34 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 35 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 36 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 37 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 33 5 (CCZ023 ∷ []) (lw4 c4 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b104 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ K1 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b104 = at 28 4 (CS14⁻ ∷ X4 ∷ K2 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ K2 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 31 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 32 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 30 3 (Toff203 ∷ []) (lw4 c4 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) tt tt Eq.refl) ▸
       at 31 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 30 2 (K1⁻ ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 29 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 32 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b105 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ K1 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ K1 ∷ Toff203 ∷ X4 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b105 = at 31 2 (K1 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1 ∷ []) (K1 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 30 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 31 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff203 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 34 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 33 2 (K1⁻ ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 32 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 35 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 34 2 (K1 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1 ∷ []) (K1 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸ done

  b106 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ K1 ∷ Toff203 ∷ X4 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b106 = at 33 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 36 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 35 2 (CS13 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ CS13 ∷ []) (CS13 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 34 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 37 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 36 2 (K1⁻ ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 35 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 21 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b107 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ K1 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b107 = at 20 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 19 2 (K1 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1 ∷ []) (K1 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 19 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff203 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 21 2 (K1⁻ ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 23 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b108 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ K1 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b108 = at 22 2 (K1 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1 ∷ []) (K1 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 21 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 23 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (lw4 c4 (Toff203 ∷ []) (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 4 (CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2⁻ ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b109 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b109 = at 30 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 33 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 36 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 37 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 34 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 31 4 (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23⁻ ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b110 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b110 = at 28 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 29 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 30 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 31 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 27 5 (CCZ023 ∷ []) (lw4 c4 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS14⁻ ∷ X4 ∷ K2 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ K2 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 26 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b111 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b111 = at 24 3 (Toff203 ∷ []) (lw4 c4 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) tt tt Eq.refl) ▸
       at 25 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 24 2 (K1⁻ ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 26 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 25 2 (K1 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1 ∷ []) (K1 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 24 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 25 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff203 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b112 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS13 ∷ Toff203 ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b112 = at 28 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 27 2 (K1⁻ ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 26 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 29 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 28 2 (K1 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1 ∷ []) (K1 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 27 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 30 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 29 2 (CS13 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ CS13 ∷ []) (CS13 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸ done

  b113 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS13 ∷ Toff203 ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Bx2-0341 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b113 = at 28 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 31 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 30 2 (K1⁻ ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 29 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 32 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 33 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 34 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 31 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸ done

  b114 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Bx2-0341 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b114 = at 31 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸
       at 31 1 (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4) ▸
       at 31 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸
       at 15 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (CS03⁻ ∷ []) (refl) ▸
       at 12 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 9 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b115 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b115 = at 7 1 (CS03 ∷ []) (refl) ▸
       at 6 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸ done

  b116 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ CS12⁻ ∷ X4 ∷ CS01 ∷ [])
  b116 = at 5 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (CCZ134 ∷ []) (lw0 c4 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 6 2 (CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b117 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ CS12⁻ ∷ X4 ∷ CS01 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b117 = at 6 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 2 (Sb⁻0-2-1-3 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0210243143 c4) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 4 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-CS01 c4)) ▸
       at 3 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b118 : Chain (Sb0-2-43-1 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b118 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 7 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 6 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 11 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (pw1 c4 (Toff204 ∷ Toff204 ∷ []) [] tt tt Eq.refl) ▸
       at 9 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 9 1 (CZ03 ∷ []) (refl) ▸ done

  b119 : Chain (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b119 = at 12 1 (CZ03 ∷ []) (refl) ▸
       at 15 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 17 1 (CZ03 ∷ []) (refl) ▸
       at 20 1 (CZ03 ∷ []) (refl) ▸
       at 9 12 [] (lw4 c4 (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (pw1 c4 (Toff204 ∷ Toff204 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸
       at 6 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸ done

  b120 : Chain (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b120 = at 6 1 (CZ03 ∷ []) (refl) ▸
       at 9 1 (CZ03 ∷ []) (refl) ▸
       at 12 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 14 1 (CZ03 ∷ []) (refl) ▸
       at 17 1 (CZ03 ∷ []) (refl) ▸
       at 6 12 [] (lw4 c4 (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Toff314 ∷ Toff314 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (CS03⁻ ∷ []) (refl) ▸ done

  b121 : Chain (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ [])
  b121 = at 5 1 (CS03 ∷ []) (refl) ▸
       at 4 2 [] (lw4 c4 (CS03⁻ ∷ CS03 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 [] (lw0 c4 (Toff314 ∷ Toff314 ∷ []) [] tt tt Eq.refl) ▸
       at 2 1 (CS03 ∷ []) (refl) ▸
       at 3 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 2 [] (lw4 c4 (CS03 ∷ CS03⁻ ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done


{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D092 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0393 ; wl0433 ; wl0503 ; wl0509 ; wl0515 ; wl0516 ; wl0517 ; wl0518 ; wl0519 ; wl0520 ; wl0521 ; wl0522 ; wl0523 ; wl0524 ; wl0525 ; wl0526 ; wl0527 ; wl0528 ; wl0529 ; wl0530 ; wl0531 ; wp0182 ; wp0193 ; wp0194 ; wp0195 ; wp0196 ; wp0197 ; wp0198 ; wp0199 ; wp0200 ; wp0201 ; wp0202 ; wp0203 ; wp0204 ; wp0205)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 ; lem-beta-T-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-X1-beta-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0210243143 ; lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314213240)
-- F1 CS-K1 [rhs shape] part1: 500 steps
lem-F1-CS-K1-rhs-shape-part1 : Ws → ⟪ (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K1-rhs-shape-part1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (run b62))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b0 = at 21 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 17 4 (X0 ∷ CK01 ∷ X0 ∷ CS04⁻ ∷ []) (wp0193 c4) ▸
       at 16 4 (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) (wl0515 (lit c4)) ▸
       at 24 1 (ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) (wl0516 (lit c4)) ▸
       at 32 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 33 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 36 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 39 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b1 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS01 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b1 = at 42 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 32 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 33 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 36 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 39 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 30 4 (X0 ∷ Toff204 ∷ X0 ∷ CS01 ∷ []) (wp0194 c4) ▸
       at 33 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ []) (wl0517 (lit c4)) ▸
       at 36 4 (X0 ∷ Toff204 ∷ X0 ∷ CS01 ∷ []) (wp0194 c4) ▸ done

  b2 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS01 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ CS01 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b2 = at 39 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ []) (wl0517 (lit c4)) ▸
       at 32 2 [] (wl0509 (lit c4)) ▸
       at 33 2 [] (wl0509 (lit c4)) ▸
       at 34 2 [] (wl0509 (lit c4)) ▸
       at 31 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 33 4 (X0 ∷ Toff314 ∷ X0 ∷ CS01 ∷ []) (wp0195 c4) ▸
       at 38 1 (CS03 ∷ []) (refl) ▸
       at 36 4 (X0 ∷ CS03 ∷ X0 ∷ CS01 ∷ []) (wl0518 (lit c4)) ▸ done

  b3 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ CS01 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b3 = at 37 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 39 4 (X0 ∷ Toff314 ∷ X0 ∷ CS01 ∷ []) (wp0195 c4) ▸
       at 44 1 (CS03⁻ ∷ []) (refl) ▸
       at 42 4 (X0 ∷ CS03⁻ ∷ X0 ∷ CS01 ∷ []) (wl0519 (lit c4)) ▸
       at 43 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 32 2 [] (wl0509 (lit c4)) ▸
       at 33 2 [] (wl0509 (lit c4)) ▸
       at 34 2 [] (wl0509 (lit c4)) ▸ done

  b4 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Bx2-0143 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b4 = at 35 2 [] (wl0509 (lit c4)) ▸
       at 31 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 31 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 32 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 38 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 41 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 31 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸ done

  b5 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Bx2-0143 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ X0 ∷ CCZ234 ∷ X0 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b5 = at 31 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 32 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 38 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 27 6 (X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wl0520 (lit c4)) ▸
       at 32 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸
       at 33 2 (CCZ234 ∷ K1 ∷ []) (c₂ (K ↑) (CCZ)) ▸
       at 34 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸ done

  b6 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ X0 ∷ CCZ234 ∷ X0 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ CS01 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b6 = at 33 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4)) ▸
       at 34 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 37 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 40 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 43 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 31 4 (X0 ∷ CS23 ∷ X0 ∷ CS01 ∷ []) (wl0521 (lit c4)) ▸
       at 34 4 (X0 ∷ CX43 ∷ X0 ∷ CS01 ∷ []) (wl0522 (lit c4)) ▸
       at 37 4 (X0 ∷ CS23⁻ ∷ X0 ∷ CS01 ∷ []) (wl0523 (lit c4)) ▸ done

  b7 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ CS01 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ K1 ∷ CCZ234 ∷ X0 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b7 = at 40 4 (X0 ∷ CX43 ∷ X0 ∷ CS01 ∷ []) (wl0522 (lit c4)) ▸
       at 43 4 (X0 ∷ CS24 ∷ X0 ∷ CS01 ∷ []) (wp0196 c4) ▸
       at 33 2 [] (wl0509 (lit c4)) ▸
       at 34 2 [] (wl0509 (lit c4)) ▸
       at 35 2 [] (wl0509 (lit c4)) ▸
       at 36 2 [] (wl0509 (lit c4)) ▸
       at 32 5 (CCZ234 ∷ []) (sym (wl0393 (lit c4))) ▸
       at 30 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸ done

  b8 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ K1 ∷ CCZ234 ∷ X0 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X0 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b8 = at 31 2 (CCZ234 ∷ K1 ∷ []) (c₂ (K ↑) (CCZ)) ▸
       at 32 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸
       at 33 6 (X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wl0520 (lit c4)) ▸
       at 38 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸
       at 39 2 (CCZ234 ∷ K1 ∷ []) (c₂ (K ↑) (CCZ)) ▸
       at 40 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸
       at 39 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4)) ▸
       at 40 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b9 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X0 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b9 = at 43 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 46 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 49 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 37 4 (X0 ∷ CS23 ∷ X0 ∷ CS01 ∷ []) (wl0521 (lit c4)) ▸
       at 40 4 (X0 ∷ CX43 ∷ X0 ∷ CS01 ∷ []) (wl0522 (lit c4)) ▸
       at 43 4 (X0 ∷ CS23⁻ ∷ X0 ∷ CS01 ∷ []) (wl0523 (lit c4)) ▸
       at 46 4 (X0 ∷ CX43 ∷ X0 ∷ CS01 ∷ []) (wl0522 (lit c4)) ▸
       at 49 4 (X0 ∷ CS24 ∷ X0 ∷ CS01 ∷ []) (wp0196 c4) ▸ done

  b10 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b10 = at 39 2 [] (wl0509 (lit c4)) ▸
       at 40 2 [] (wl0509 (lit c4)) ▸
       at 41 2 [] (wl0509 (lit c4)) ▸
       at 42 2 [] (wl0509 (lit c4)) ▸
       at 38 5 (CCZ234 ∷ []) (sym (wl0393 (lit c4))) ▸
       at 36 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸
       at 37 2 (CCZ234 ∷ K1 ∷ []) (c₂ (K ↑) (CCZ)) ▸
       at 38 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸ done

  b11 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b11 = at 29 2 [] (wl0509 (lit c4)) ▸
       at 30 2 [] (wl0509 (lit c4)) ▸
       at 31 2 [] (wl0509 (lit c4)) ▸
       at 28 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 28 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 37 1 (CS03 ∷ []) (refl) ▸
       at 30 12 (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wp0197 c4) ▸
       at 34 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b12 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b12 = at 43 1 (CS03⁻ ∷ []) (refl) ▸
       at 39 6 (X0 ∷ CS03⁻ ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wl0524 (lit c4)) ▸
       at 40 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 29 2 [] (wl0509 (lit c4)) ▸
       at 30 2 [] (wl0509 (lit c4)) ▸
       at 31 2 [] (wl0509 (lit c4)) ▸
       at 32 2 [] (wl0509 (lit c4)) ▸
       at 28 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

  b13 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b13 = at 28 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 29 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 32 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 38 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 28 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 29 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 32 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b14 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b14 = at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 26 4 (X0 ∷ Toff204 ∷ X0 ∷ CS01 ∷ []) (wp0194 c4) ▸
       at 29 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ []) (wl0517 (lit c4)) ▸
       at 32 4 (X0 ∷ Toff204 ∷ X0 ∷ CS01 ∷ []) (wp0194 c4) ▸
       at 35 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ []) (wl0517 (lit c4)) ▸
       at 28 2 [] (wl0509 (lit c4)) ▸
       at 29 2 [] (wl0509 (lit c4)) ▸
       at 30 2 [] (wl0509 (lit c4)) ▸ done

  b15 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b15 = at 27 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 29 4 (X0 ∷ Toff314 ∷ X0 ∷ CS01 ∷ []) (wp0195 c4) ▸
       at 34 1 (CS03 ∷ []) (refl) ▸
       at 32 4 (X0 ∷ CS03 ∷ X0 ∷ CS01 ∷ []) (wl0518 (lit c4)) ▸
       at 33 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 35 4 (X0 ∷ Toff314 ∷ X0 ∷ CS01 ∷ []) (wp0195 c4) ▸
       at 40 1 (CS03⁻ ∷ []) (refl) ▸
       at 38 4 (X0 ∷ CS03⁻ ∷ X0 ∷ CS01 ∷ []) (wl0519 (lit c4)) ▸ done

  b16 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b16 = at 39 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 28 2 [] (wl0509 (lit c4)) ▸
       at 29 2 [] (wl0509 (lit c4)) ▸
       at 30 2 [] (wl0509 (lit c4)) ▸
       at 31 2 [] (wl0509 (lit c4)) ▸
       at 27 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 27 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 28 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b17 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ X0 ∷ Toff204 ∷ X0 ∷ S0⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b17 = at 31 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 34 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 37 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 27 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 28 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 31 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 34 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 25 4 (X0 ∷ Toff204 ∷ X0 ∷ S0⁻ ∷ []) (wp0198 c4) ▸ done

  b18 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ X0 ∷ Toff204 ∷ X0 ∷ S0⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ S0⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b18 = at 28 4 (X0 ∷ CCZ123 ∷ X0 ∷ S0⁻ ∷ []) (wl0525 (lit c4)) ▸
       at 31 4 (X0 ∷ Toff204 ∷ X0 ∷ S0⁻ ∷ []) (wp0198 c4) ▸
       at 34 4 (X0 ∷ CCZ123 ∷ X0 ∷ S0⁻ ∷ []) (wl0525 (lit c4)) ▸
       at 27 2 [] (wl0509 (lit c4)) ▸
       at 28 2 [] (wl0509 (lit c4)) ▸
       at 29 2 [] (wl0509 (lit c4)) ▸
       at 26 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 28 4 (X0 ∷ Toff314 ∷ X0 ∷ S0⁻ ∷ []) (wp0199 c4) ▸ done

  b19 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ S0⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b19 = at 33 1 (CS03 ∷ []) (refl) ▸
       at 31 4 (X0 ∷ CS03 ∷ X0 ∷ S0⁻ ∷ []) (wl0526 (lit c4)) ▸
       at 32 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 34 4 (X0 ∷ Toff314 ∷ X0 ∷ S0⁻ ∷ []) (wp0199 c4) ▸
       at 39 1 (CS03⁻ ∷ []) (refl) ▸
       at 37 4 (X0 ∷ CS03⁻ ∷ X0 ∷ S0⁻ ∷ []) (wl0527 (lit c4)) ▸
       at 38 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 27 2 [] (wl0509 (lit c4)) ▸ done

  b20 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ ι ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b20 = at 28 2 [] (wl0509 (lit c4)) ▸
       at 29 2 [] (wl0509 (lit c4)) ▸
       at 30 2 [] (wl0509 (lit c4)) ▸
       at 26 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 24 2 (X0 ∷ ι ∷ []) (sym zc) ▸
       at 25 2 (Sb2-0-41-3 ∷ ι ∷ []) (sym zc) ▸
       at 26 2 (X0 ∷ ι ∷ []) (sym zc) ▸
       at 27 7 (CK01 ∷ []) (sym (wl0516 (lit c4))) ▸ done

  b21 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b21 = at 23 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 27 1 (CS03⁻ ∷ []) (refl) ▸
       at 29 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 30 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 33 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 36 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 39 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 29 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸ done

  b22 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b22 = at 30 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 33 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 36 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 27 4 (X0 ∷ Toff204 ∷ X0 ∷ CS03⁻ ∷ []) (wp0200 c4) ▸
       at 30 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ []) (wl0528 (lit c4)) ▸
       at 33 4 (X0 ∷ Toff204 ∷ X0 ∷ CS03⁻ ∷ []) (wp0200 c4) ▸
       at 36 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ []) (wl0528 (lit c4)) ▸
       at 29 2 [] (wl0509 (lit c4)) ▸ done

  b23 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ CS03⁻ ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b23 = at 30 2 [] (wl0509 (lit c4)) ▸
       at 31 2 [] (wl0509 (lit c4)) ▸
       at 28 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 35 1 (CS03 ∷ []) (refl) ▸
       at 30 10 (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ []) (wp0201 c4) ▸
       at 34 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 41 1 (CS03⁻ ∷ []) (refl) ▸
       at 39 4 (X0 ∷ CS03⁻ ∷ X0 ∷ CS03⁻ ∷ []) (wl0529 (lit c4)) ▸ done

  b24 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ CS03⁻ ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b24 = at 40 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 29 2 [] (wl0509 (lit c4)) ▸
       at 30 2 [] (wl0509 (lit c4)) ▸
       at 31 2 [] (wl0509 (lit c4)) ▸
       at 32 2 [] (wl0509 (lit c4)) ▸
       at 28 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 30 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 26 2 (X0 ∷ Toff314 ∷ []) (wp0202 c4) ▸ done

  b25 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b25 = at 27 2 (Sb2-0-41-3 ∷ Toff314 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314213240 c4) ▸
       at 28 2 (X0 ∷ Toff314 ∷ []) (wp0202 c4) ▸
       at 25 1 (CS03 ∷ []) (refl) ▸
       at 27 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 28 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 31 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 34 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 37 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b26 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b26 = at 27 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 28 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 31 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 34 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 25 4 (X0 ∷ Toff204 ∷ X0 ∷ CS03 ∷ []) (wp0203 c4) ▸
       at 28 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ []) (wl0530 (lit c4)) ▸
       at 31 4 (X0 ∷ Toff204 ∷ X0 ∷ CS03 ∷ []) (wp0203 c4) ▸
       at 34 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ []) (wl0530 (lit c4)) ▸ done

  b27 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b27 = at 27 2 [] (wl0509 (lit c4)) ▸
       at 28 2 [] (wl0509 (lit c4)) ▸
       at 29 2 [] (wl0509 (lit c4)) ▸
       at 26 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 33 1 (CS03 ∷ []) (refl) ▸
       at 28 10 (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ []) (wp0204 c4) ▸
       at 32 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 39 1 (CS03⁻ ∷ []) (refl) ▸ done

  b28 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b28 = at 37 4 (X0 ∷ CS03⁻ ∷ X0 ∷ CS03 ∷ []) (wl0531 (lit c4)) ▸
       at 38 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 27 2 [] (wl0509 (lit c4)) ▸
       at 28 2 [] (wl0509 (lit c4)) ▸
       at 29 2 [] (wl0509 (lit c4)) ▸
       at 30 2 [] (wl0509 (lit c4)) ▸
       at 26 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 28 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b29 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ X0 ∷ CCZ134 ∷ Sb2-0-41-3 ∷ X0 ∷ CCZ134 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b29 = at 24 2 (X0 ∷ Toff314 ∷ []) (wp0202 c4) ▸
       at 25 2 (Sb2-0-41-3 ∷ Toff314 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314213240 c4) ▸
       at 26 2 (X0 ∷ Toff314 ∷ []) (wp0202 c4) ▸
       at 23 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 24 3 (CCZ134 ∷ Bx2-0413 ∷ []) (lem-X1-beta-at0210243143 c4) ▸
       at 25 2 (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 c4) ▸
       at 26 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 27 3 (CCZ134 ∷ Bx2-0413 ∷ []) (lem-X1-beta-at0210243143 c4) ▸ done

  b30 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ X0 ∷ CCZ134 ∷ Sb2-0-41-3 ∷ X0 ∷ CCZ134 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b30 = at 23 2 (CCZ134 ∷ X0 ∷ []) (sym (wp0205 c4)) ▸
       at 26 2 (CCZ134 ∷ X0 ∷ []) (sym (wp0205 c4)) ▸
       at 25 2 (CCZ134 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0210243143 c4) ▸
       at 24 2 (CCZ134 ∷ X0 ∷ []) (sym (wp0205 c4)) ▸
       at 23 2 [] (wl0503 (lit c4)) ▸
       at 26 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 22 1 (ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) (wl0516 (lit c4)) ▸
       at 30 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b31 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b31 = at 31 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 34 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 37 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 40 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 30 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 31 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 34 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 37 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b32 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ CS01 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b32 = at 28 4 (X0 ∷ Toff204 ∷ X0 ∷ CS01 ∷ []) (wp0194 c4) ▸
       at 31 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ []) (wl0517 (lit c4)) ▸
       at 34 4 (X0 ∷ Toff204 ∷ X0 ∷ CS01 ∷ []) (wp0194 c4) ▸
       at 37 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ []) (wl0517 (lit c4)) ▸
       at 30 2 [] (wl0509 (lit c4)) ▸
       at 31 2 [] (wl0509 (lit c4)) ▸
       at 32 2 [] (wl0509 (lit c4)) ▸
       at 29 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸ done

  b33 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ CS01 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b33 = at 31 4 (X0 ∷ Toff314 ∷ X0 ∷ CS01 ∷ []) (wp0195 c4) ▸
       at 36 1 (CS03 ∷ []) (refl) ▸
       at 34 4 (X0 ∷ CS03 ∷ X0 ∷ CS01 ∷ []) (wl0518 (lit c4)) ▸
       at 35 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 37 4 (X0 ∷ Toff314 ∷ X0 ∷ CS01 ∷ []) (wp0195 c4) ▸
       at 42 1 (CS03⁻ ∷ []) (refl) ▸
       at 40 4 (X0 ∷ CS03⁻ ∷ X0 ∷ CS01 ∷ []) (wl0519 (lit c4)) ▸
       at 41 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b34 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b34 = at 30 2 [] (wl0509 (lit c4)) ▸
       at 31 2 [] (wl0509 (lit c4)) ▸
       at 32 2 [] (wl0509 (lit c4)) ▸
       at 33 2 [] (wl0509 (lit c4)) ▸
       at 29 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 29 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 30 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 33 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b35 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b35 = at 36 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 39 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 29 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 29 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 30 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 33 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 36 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 25 6 (X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wl0520 (lit c4)) ▸ done

  b36 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b36 = at 30 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸
       at 31 2 (CCZ234 ∷ K1 ∷ []) (c₂ (K ↑) (CCZ)) ▸
       at 32 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸
       at 31 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4)) ▸
       at 32 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 38 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 41 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b37 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ X0 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b37 = at 29 4 (X0 ∷ CS23 ∷ X0 ∷ CS01 ∷ []) (wl0521 (lit c4)) ▸
       at 32 4 (X0 ∷ CX43 ∷ X0 ∷ CS01 ∷ []) (wl0522 (lit c4)) ▸
       at 35 4 (X0 ∷ CS23⁻ ∷ X0 ∷ CS01 ∷ []) (wl0523 (lit c4)) ▸
       at 38 4 (X0 ∷ CX43 ∷ X0 ∷ CS01 ∷ []) (wl0522 (lit c4)) ▸
       at 41 4 (X0 ∷ CS24 ∷ X0 ∷ CS01 ∷ []) (wp0196 c4) ▸
       at 31 2 [] (wl0509 (lit c4)) ▸
       at 32 2 [] (wl0509 (lit c4)) ▸
       at 33 2 [] (wl0509 (lit c4)) ▸ done

  b38 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ X0 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ X0 ∷ CCZ234 ∷ K1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b38 = at 34 2 [] (wl0509 (lit c4)) ▸
       at 30 5 (CCZ234 ∷ []) (sym (wl0393 (lit c4))) ▸
       at 28 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸
       at 29 2 (CCZ234 ∷ K1 ∷ []) (c₂ (K ↑) (CCZ)) ▸
       at 30 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸
       at 31 6 (X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wl0520 (lit c4)) ▸
       at 36 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸
       at 37 2 (CCZ234 ∷ K1 ∷ []) (c₂ (K ↑) (CCZ)) ▸ done

  b39 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ X0 ∷ CCZ234 ∷ K1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ CS01 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b39 = at 38 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸
       at 37 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4)) ▸
       at 38 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 41 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 44 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 47 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 35 4 (X0 ∷ CS23 ∷ X0 ∷ CS01 ∷ []) (wl0521 (lit c4)) ▸
       at 38 4 (X0 ∷ CX43 ∷ X0 ∷ CS01 ∷ []) (wl0522 (lit c4)) ▸ done

  b40 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ CS01 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ X0 ∷ CCZ234 ∷ X0 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b40 = at 41 4 (X0 ∷ CS23⁻ ∷ X0 ∷ CS01 ∷ []) (wl0523 (lit c4)) ▸
       at 44 4 (X0 ∷ CX43 ∷ X0 ∷ CS01 ∷ []) (wl0522 (lit c4)) ▸
       at 47 4 (X0 ∷ CS24 ∷ X0 ∷ CS01 ∷ []) (wp0196 c4) ▸
       at 37 2 [] (wl0509 (lit c4)) ▸
       at 38 2 [] (wl0509 (lit c4)) ▸
       at 39 2 [] (wl0509 (lit c4)) ▸
       at 40 2 [] (wl0509 (lit c4)) ▸
       at 36 5 (CCZ234 ∷ []) (sym (wl0393 (lit c4))) ▸ done

  b41 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ X0 ∷ CCZ234 ∷ X0 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b41 = at 34 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸
       at 35 2 (CCZ234 ∷ K1 ∷ []) (c₂ (K ↑) (CCZ)) ▸
       at 36 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸
       at 27 2 [] (wl0509 (lit c4)) ▸
       at 28 2 [] (wl0509 (lit c4)) ▸
       at 29 2 [] (wl0509 (lit c4)) ▸
       at 26 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 26 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸ done

  b42 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b42 = at 35 1 (CS03 ∷ []) (refl) ▸
       at 28 12 (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wp0197 c4) ▸
       at 32 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 41 1 (CS03⁻ ∷ []) (refl) ▸
       at 37 6 (X0 ∷ CS03⁻ ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wl0524 (lit c4)) ▸
       at 38 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 27 2 [] (wl0509 (lit c4)) ▸
       at 28 2 [] (wl0509 (lit c4)) ▸ done

  b43 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b43 = at 29 2 [] (wl0509 (lit c4)) ▸
       at 30 2 [] (wl0509 (lit c4)) ▸
       at 26 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 26 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 27 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 30 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 33 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 36 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b44 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b44 = at 26 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 27 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 30 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 33 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 24 4 (X0 ∷ Toff204 ∷ X0 ∷ CS01 ∷ []) (wp0194 c4) ▸
       at 27 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ []) (wl0517 (lit c4)) ▸
       at 30 4 (X0 ∷ Toff204 ∷ X0 ∷ CS01 ∷ []) (wp0194 c4) ▸
       at 33 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ []) (wl0517 (lit c4)) ▸ done

  b45 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ CS01 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b45 = at 26 2 [] (wl0509 (lit c4)) ▸
       at 27 2 [] (wl0509 (lit c4)) ▸
       at 28 2 [] (wl0509 (lit c4)) ▸
       at 25 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 27 4 (X0 ∷ Toff314 ∷ X0 ∷ CS01 ∷ []) (wp0195 c4) ▸
       at 32 1 (CS03 ∷ []) (refl) ▸
       at 30 4 (X0 ∷ CS03 ∷ X0 ∷ CS01 ∷ []) (wl0518 (lit c4)) ▸
       at 31 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b46 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ CS01 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b46 = at 33 4 (X0 ∷ Toff314 ∷ X0 ∷ CS01 ∷ []) (wp0195 c4) ▸
       at 38 1 (CS03⁻ ∷ []) (refl) ▸
       at 36 4 (X0 ∷ CS03⁻ ∷ X0 ∷ CS01 ∷ []) (wl0519 (lit c4)) ▸
       at 37 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 26 2 [] (wl0509 (lit c4)) ▸
       at 27 2 [] (wl0509 (lit c4)) ▸
       at 28 2 [] (wl0509 (lit c4)) ▸
       at 29 2 [] (wl0509 (lit c4)) ▸ done

  b47 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b47 = at 25 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 25 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 26 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 29 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 32 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 25 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 26 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b48 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ S0⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b48 = at 29 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 32 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 23 4 (X0 ∷ Toff204 ∷ X0 ∷ S0⁻ ∷ []) (wp0198 c4) ▸
       at 26 4 (X0 ∷ CCZ123 ∷ X0 ∷ S0⁻ ∷ []) (wl0525 (lit c4)) ▸
       at 29 4 (X0 ∷ Toff204 ∷ X0 ∷ S0⁻ ∷ []) (wp0198 c4) ▸
       at 32 4 (X0 ∷ CCZ123 ∷ X0 ∷ S0⁻ ∷ []) (wl0525 (lit c4)) ▸
       at 25 2 [] (wl0509 (lit c4)) ▸
       at 26 2 [] (wl0509 (lit c4)) ▸ done

  b49 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ S0⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ S0⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b49 = at 27 2 [] (wl0509 (lit c4)) ▸
       at 24 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 26 4 (X0 ∷ Toff314 ∷ X0 ∷ S0⁻ ∷ []) (wp0199 c4) ▸
       at 31 1 (CS03 ∷ []) (refl) ▸
       at 29 4 (X0 ∷ CS03 ∷ X0 ∷ S0⁻ ∷ []) (wl0526 (lit c4)) ▸
       at 30 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 32 4 (X0 ∷ Toff314 ∷ X0 ∷ S0⁻ ∷ []) (wp0199 c4) ▸
       at 37 1 (CS03⁻ ∷ []) (refl) ▸ done

  b50 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ S0⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ X0 ∷ ι ∷ Sb2-0-41-3 ∷ X0 ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b50 = at 35 4 (X0 ∷ CS03⁻ ∷ X0 ∷ S0⁻ ∷ []) (wl0527 (lit c4)) ▸
       at 36 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 25 2 [] (wl0509 (lit c4)) ▸
       at 26 2 [] (wl0509 (lit c4)) ▸
       at 27 2 [] (wl0509 (lit c4)) ▸
       at 28 2 [] (wl0509 (lit c4)) ▸
       at 24 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 22 2 (X0 ∷ ι ∷ []) (sym zc) ▸ done

  b51 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ X0 ∷ ι ∷ Sb2-0-41-3 ∷ X0 ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b51 = at 23 2 (Sb2-0-41-3 ∷ ι ∷ []) (sym zc) ▸
       at 24 2 (X0 ∷ ι ∷ []) (sym zc) ▸
       at 25 7 (CK01 ∷ []) (sym (wl0516 (lit c4))) ▸
       at 21 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 25 1 (CS03⁻ ∷ []) (refl) ▸
       at 27 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 28 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 31 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b52 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b52 = at 34 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 37 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 27 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 28 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 31 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 34 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 25 4 (X0 ∷ Toff204 ∷ X0 ∷ CS03⁻ ∷ []) (wp0200 c4) ▸
       at 28 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ []) (wl0528 (lit c4)) ▸ done

  b53 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b53 = at 31 4 (X0 ∷ Toff204 ∷ X0 ∷ CS03⁻ ∷ []) (wp0200 c4) ▸
       at 34 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ []) (wl0528 (lit c4)) ▸
       at 27 2 [] (wl0509 (lit c4)) ▸
       at 28 2 [] (wl0509 (lit c4)) ▸
       at 29 2 [] (wl0509 (lit c4)) ▸
       at 26 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 33 1 (CS03 ∷ []) (refl) ▸
       at 28 10 (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ []) (wp0201 c4) ▸ done

  b54 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS03⁻ ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b54 = at 32 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 39 1 (CS03⁻ ∷ []) (refl) ▸
       at 37 4 (X0 ∷ CS03⁻ ∷ X0 ∷ CS03⁻ ∷ []) (wl0529 (lit c4)) ▸
       at 38 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 27 2 [] (wl0509 (lit c4)) ▸
       at 28 2 [] (wl0509 (lit c4)) ▸
       at 29 2 [] (wl0509 (lit c4)) ▸
       at 30 2 [] (wl0509 (lit c4)) ▸ done

  b55 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS03⁻ ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b55 = at 26 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 28 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 24 2 (X0 ∷ Toff314 ∷ []) (wp0202 c4) ▸
       at 25 2 (Sb2-0-41-3 ∷ Toff314 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314213240 c4) ▸
       at 26 2 (X0 ∷ Toff314 ∷ []) (wp0202 c4) ▸
       at 23 1 (CS03 ∷ []) (refl) ▸
       at 25 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 26 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b56 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS03 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b56 = at 29 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 32 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 25 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 26 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 29 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 32 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 23 4 (X0 ∷ Toff204 ∷ X0 ∷ CS03 ∷ []) (wp0203 c4) ▸ done

  b57 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS03 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b57 = at 26 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ []) (wl0530 (lit c4)) ▸
       at 29 4 (X0 ∷ Toff204 ∷ X0 ∷ CS03 ∷ []) (wp0203 c4) ▸
       at 32 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ []) (wl0530 (lit c4)) ▸
       at 25 2 [] (wl0509 (lit c4)) ▸
       at 26 2 [] (wl0509 (lit c4)) ▸
       at 27 2 [] (wl0509 (lit c4)) ▸
       at 24 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 31 1 (CS03 ∷ []) (refl) ▸ done

  b58 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b58 = at 26 10 (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ []) (wp0204 c4) ▸
       at 30 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 37 1 (CS03⁻ ∷ []) (refl) ▸
       at 35 4 (X0 ∷ CS03⁻ ∷ X0 ∷ CS03 ∷ []) (wl0531 (lit c4)) ▸
       at 36 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 25 2 [] (wl0509 (lit c4)) ▸
       at 26 2 [] (wl0509 (lit c4)) ▸
       at 27 2 [] (wl0509 (lit c4)) ▸ done

  b59 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ CCZ134 ∷ Bx2-0413 ∷ Sb2-0-41-3 ∷ X0 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b59 = at 28 2 [] (wl0509 (lit c4)) ▸
       at 24 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 26 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 22 2 (X0 ∷ Toff314 ∷ []) (wp0202 c4) ▸
       at 23 2 (Sb2-0-41-3 ∷ Toff314 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314213240 c4) ▸
       at 24 2 (X0 ∷ Toff314 ∷ []) (wp0202 c4) ▸
       at 21 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 22 3 (CCZ134 ∷ Bx2-0413 ∷ []) (lem-X1-beta-at0210243143 c4) ▸ done

  b60 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ CCZ134 ∷ Bx2-0413 ∷ Sb2-0-41-3 ∷ X0 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b60 = at 23 2 (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 c4) ▸
       at 24 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 25 3 (CCZ134 ∷ Bx2-0413 ∷ []) (lem-X1-beta-at0210243143 c4) ▸
       at 21 2 (CCZ134 ∷ X0 ∷ []) (sym (wp0205 c4)) ▸
       at 24 2 (CCZ134 ∷ X0 ∷ []) (sym (wp0205 c4)) ▸
       at 23 2 (CCZ134 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0210243143 c4) ▸
       at 22 2 (CCZ134 ∷ X0 ∷ []) (sym (wp0205 c4)) ▸
       at 21 2 [] (wl0503 (lit c4)) ▸ done

  b61 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b61 = at 24 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 22 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 23 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 26 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 29 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 32 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 22 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 23 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b62 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b62 = at 26 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 29 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 20 4 (X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ []) (wp0182 c4) ▸
       at 25 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸ done


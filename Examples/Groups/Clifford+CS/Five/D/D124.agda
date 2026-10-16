{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D124 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0393 ; wl0433 ; wl0503 ; wl0505 ; wl0506 ; wl0507 ; wl0508 ; wl0509 ; wl0510 ; wl0511 ; wl0512 ; wl0513 ; wl0514 ; wl0515 ; wl0516 ; wl0517 ; wl0518 ; wl0519 ; wl0520 ; wl0521 ; wl0522 ; wl0523 ; wl0524 ; wl0525 ; wl0526 ; wl0527 ; wl0528 ; wl0529 ; wl0530 ; wl0531 ; wl0532 ; wp0178 ; wp0179 ; wp0180 ; wp0181 ; wp0182 ; wp0183 ; wp0184 ; wp0185 ; wp0186 ; wp0187 ; wp0188 ; wp0189 ; wp0190 ; wp0191 ; wp0192 ; wp0193 ; wp0194 ; wp0195 ; wp0196 ; wp0197 ; wp0198 ; wp0199 ; wp0200 ; wp0201 ; wp0202 ; wp0203 ; wp0204 ; wp0205)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 ; lem-beta-T-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-F5-CS01-at0440 ; lem-SBtgt-at0440 ; lem-X1-beta-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0210243143 ; lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314213240)
-- F1 CS-K1 part0: 500 steps
lem-F1-CS-K1-part0 : Ws → ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) ⟫ʷ
lem-F1-CS-K1-part0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (run b62))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-4-01-3 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b0 = at 3 0 (CK41⁻ ∷ CK41 ∷ []) (sym (wl0505 (lit c4))) ▸
       at 4 2 (S4⁻ ∷ []) (wl0506 (lit c4)) ▸
       at 1 1 (ι1 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (wp0178 c4) ▸
       at 1 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 1 1 (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) (sym (wl0507 (lit c4))) ▸
       at 5 1 (CS04⁻ ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (sym (wp0179 c4)) ▸
       at 9 1 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F5-CS01-at0440 c4)) ▸
       at 10 1 (Sb2-0-41-3 ∷ []) (lem-SBtgt-at0440 c4) ▸ done

  b1 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-4-01-3 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-4-01-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b1 = at 12 1 (Sb2-0-41-3 ∷ []) (lem-SBtgt-at0440 c4) ▸
       at 13 1 (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (wl0508 (lit c4)) ▸
       at 17 1 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F5-CS01-at0440 c4)) ▸
       at 18 1 (Sb2-0-41-3 ∷ []) (lem-SBtgt-at0440 c4) ▸
       at 20 1 (Sb2-0-41-3 ∷ []) (lem-SBtgt-at0440 c4) ▸
       at 21 1 (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (wl0508 (lit c4)) ▸
       at 25 1 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (sym (lem-F5-CS01-at0440 c4)) ▸
       at 26 1 (Sb2-0-41-3 ∷ []) (lem-SBtgt-at0440 c4) ▸ done

  b2 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-4-01-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b2 = at 28 1 (Sb2-0-41-3 ∷ []) (lem-SBtgt-at0440 c4) ▸
       at 5 4 (X0 ∷ CS04⁻ ∷ X0 ∷ CS04⁻ ∷ []) (wp0180 c4) ▸
       at 4 4 (X0 ∷ CS04⁻ ∷ X0 ∷ S0 ∷ []) (wp0181 c4) ▸
       at 10 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 11 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 14 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 17 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 20 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b3 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b3 = at 10 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 11 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 14 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 17 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 8 4 (X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ []) (wp0182 c4) ▸
       at 13 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸
       at 14 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 17 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b4 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CS23 ∷ CX13 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ X0 ∷ CS12 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b4 = at 20 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 23 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 11 4 (X0 ∷ CS23 ∷ X0 ∷ CS04⁻ ∷ []) (wp0183 c4) ▸
       at 14 4 (X0 ∷ CX13 ∷ X0 ∷ CS04⁻ ∷ []) (wp0184 c4) ▸
       at 17 4 (X0 ∷ CS23⁻ ∷ X0 ∷ CS04⁻ ∷ []) (wp0185 c4) ▸
       at 20 4 (X0 ∷ CX13 ∷ X0 ∷ CS04⁻ ∷ []) (wp0184 c4) ▸
       at 23 4 (X0 ∷ CS12 ∷ X0 ∷ CS04⁻ ∷ []) (wp0186 c4) ▸
       at 13 2 [] (wl0509 (lit c4)) ▸ done

  b5 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CS23 ∷ CX13 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ X0 ∷ CS12 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b5 = at 14 2 [] (wl0509 (lit c4)) ▸
       at 15 2 [] (wl0509 (lit c4)) ▸
       at 16 2 [] (wl0509 (lit c4)) ▸
       at 12 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 14 4 (X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ []) (wp0182 c4) ▸
       at 19 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸
       at 20 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 23 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b6 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CS23 ∷ CX13 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ X0 ∷ CS12 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b6 = at 26 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 29 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 17 4 (X0 ∷ CS23 ∷ X0 ∷ CS04⁻ ∷ []) (wp0183 c4) ▸
       at 20 4 (X0 ∷ CX13 ∷ X0 ∷ CS04⁻ ∷ []) (wp0184 c4) ▸
       at 23 4 (X0 ∷ CS23⁻ ∷ X0 ∷ CS04⁻ ∷ []) (wp0185 c4) ▸
       at 26 4 (X0 ∷ CX13 ∷ X0 ∷ CS04⁻ ∷ []) (wp0184 c4) ▸
       at 29 4 (X0 ∷ CS12 ∷ X0 ∷ CS04⁻ ∷ []) (wp0186 c4) ▸
       at 19 2 [] (wl0509 (lit c4)) ▸ done

  b7 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CS23 ∷ CX13 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ X0 ∷ CS12 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ S0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b7 = at 20 2 [] (wl0509 (lit c4)) ▸
       at 21 2 [] (wl0509 (lit c4)) ▸
       at 22 2 [] (wl0509 (lit c4)) ▸
       at 18 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 10 2 [] (wl0509 (lit c4)) ▸
       at 11 2 [] (wl0509 (lit c4)) ▸
       at 12 2 [] (wl0509 (lit c4)) ▸
       at 9 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸ done

  b8 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ S0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ S0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b8 = at 11 4 (X0 ∷ Toff314 ∷ X0 ∷ CS04⁻ ∷ []) (wp0187 c4) ▸
       at 16 1 (CS03 ∷ []) (refl) ▸
       at 14 4 (X0 ∷ CS03 ∷ X0 ∷ CS04⁻ ∷ []) (wp0188 c4) ▸
       at 15 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 17 4 (X0 ∷ Toff314 ∷ X0 ∷ CS04⁻ ∷ []) (wp0187 c4) ▸
       at 22 1 (CS03⁻ ∷ []) (refl) ▸
       at 20 4 (X0 ∷ CS03⁻ ∷ X0 ∷ CS04⁻ ∷ []) (wp0189 c4) ▸
       at 21 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b9 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ S0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ S0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b9 = at 10 2 [] (wl0509 (lit c4)) ▸
       at 11 2 [] (wl0509 (lit c4)) ▸
       at 12 2 [] (wl0509 (lit c4)) ▸
       at 13 2 [] (wl0509 (lit c4)) ▸
       at 9 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 9 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 10 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 13 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b10 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ S0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b10 = at 16 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 19 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 9 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 10 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 13 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 16 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 7 4 (X0 ∷ Toff204 ∷ X0 ∷ S0 ∷ []) (wp0190 c4) ▸
       at 10 4 (X0 ∷ CCZ123 ∷ X0 ∷ S0 ∷ []) (wl0510 (lit c4)) ▸ done

  b11 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b11 = at 13 4 (X0 ∷ Toff204 ∷ X0 ∷ S0 ∷ []) (wp0190 c4) ▸
       at 16 4 (X0 ∷ CCZ123 ∷ X0 ∷ S0 ∷ []) (wl0510 (lit c4)) ▸
       at 9 2 [] (wl0509 (lit c4)) ▸
       at 10 2 [] (wl0509 (lit c4)) ▸
       at 11 2 [] (wl0509 (lit c4)) ▸
       at 8 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 10 4 (X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ []) (wp0191 c4) ▸
       at 15 1 (CS03 ∷ []) (refl) ▸ done

  b12 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b12 = at 13 4 (X0 ∷ CS03 ∷ X0 ∷ S0 ∷ []) (wl0511 (lit c4)) ▸
       at 14 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 16 4 (X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ []) (wp0191 c4) ▸
       at 21 1 (CS03⁻ ∷ []) (refl) ▸
       at 19 4 (X0 ∷ CS03⁻ ∷ X0 ∷ S0 ∷ []) (wl0512 (lit c4)) ▸
       at 20 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 9 2 [] (wl0509 (lit c4)) ▸
       at 10 2 [] (wl0509 (lit c4)) ▸ done

  b13 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b13 = at 11 2 [] (wl0509 (lit c4)) ▸
       at 12 2 [] (wl0509 (lit c4)) ▸
       at 8 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 12 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 16 1 (CS03⁻ ∷ []) (refl) ▸
       at 16 4 (X0 ∷ CK01 ∷ X0 ∷ CS03⁻ ∷ []) (wl0513 (lit c4)) ▸
       at 19 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 14 1 (CS03 ∷ []) (refl) ▸ done

  b14 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Toff201 ∷ CCZ234 ∷ X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ CCZ234 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b14 = at 13 6 (X0 ∷ CK01 ∷ X0 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ []) (wp0192 c4) ▸
       at 17 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 12 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 12 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 15 2 (X0 ∷ CCZ234 ∷ []) (sym (c₁ (X) (CCZ ↑))) ▸
       at 16 2 (CK01 ∷ CCZ234 ∷ []) (sym (c₂ (CK₀₁) (CCZ))) ▸
       at 17 2 (X0 ∷ CCZ234 ∷ []) (sym (c₁ (X) (CCZ ↑))) ▸
       at 14 4 (X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ []) (wl0514 (lit c4)) ▸ done

  b15 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Toff201 ∷ CCZ234 ∷ X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ CCZ234 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b15 = at 13 2 (X0 ∷ CCZ234 ∷ []) (sym (c₁ (X) (CCZ ↑))) ▸
       at 14 2 (CK01 ∷ CCZ234 ∷ []) (sym (c₂ (CK₀₁) (CCZ))) ▸
       at 15 2 (X0 ∷ CCZ234 ∷ []) (sym (c₁ (X) (CCZ ↑))) ▸
       at 12 4 (X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ []) (wl0514 (lit c4)) ▸
       at 15 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 15 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 15 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 11 4 (X0 ∷ CK01 ∷ X0 ∷ CS04⁻ ∷ []) (wp0193 c4) ▸ done

  b16 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b16 = at 10 4 (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) (wl0515 (lit c4)) ▸
       at 16 1 (ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) (wl0516 (lit c4)) ▸
       at 24 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 25 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 28 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 31 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 34 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 24 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸ done

  b17 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b17 = at 25 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 28 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 31 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 22 4 (X0 ∷ Toff204 ∷ X0 ∷ CS01 ∷ []) (wp0194 c4) ▸
       at 25 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ []) (wl0517 (lit c4)) ▸
       at 28 4 (X0 ∷ Toff204 ∷ X0 ∷ CS01 ∷ []) (wp0194 c4) ▸
       at 31 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ []) (wl0517 (lit c4)) ▸
       at 24 2 [] (wl0509 (lit c4)) ▸ done

  b18 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS01 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b18 = at 25 2 [] (wl0509 (lit c4)) ▸
       at 26 2 [] (wl0509 (lit c4)) ▸
       at 23 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 25 4 (X0 ∷ Toff314 ∷ X0 ∷ CS01 ∷ []) (wp0195 c4) ▸
       at 30 1 (CS03 ∷ []) (refl) ▸
       at 28 4 (X0 ∷ CS03 ∷ X0 ∷ CS01 ∷ []) (wl0518 (lit c4)) ▸
       at 29 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 31 4 (X0 ∷ Toff314 ∷ X0 ∷ CS01 ∷ []) (wp0195 c4) ▸ done

  b19 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS01 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b19 = at 36 1 (CS03⁻ ∷ []) (refl) ▸
       at 34 4 (X0 ∷ CS03⁻ ∷ X0 ∷ CS01 ∷ []) (wl0519 (lit c4)) ▸
       at 35 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 24 2 [] (wl0509 (lit c4)) ▸
       at 25 2 [] (wl0509 (lit c4)) ▸
       at 26 2 [] (wl0509 (lit c4)) ▸
       at 27 2 [] (wl0509 (lit c4)) ▸
       at 23 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

  b20 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b20 = at 23 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 24 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 27 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 30 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 33 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 23 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 23 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 24 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b21 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X0 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b21 = at 27 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 30 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 19 6 (X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wl0520 (lit c4)) ▸
       at 24 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸
       at 25 2 (CCZ234 ∷ K1 ∷ []) (c₂ (K ↑) (CCZ)) ▸
       at 26 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸
       at 25 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4)) ▸
       at 26 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b22 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X0 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b22 = at 29 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 32 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 23 4 (X0 ∷ CS23 ∷ X0 ∷ CS01 ∷ []) (wl0521 (lit c4)) ▸
       at 26 4 (X0 ∷ CX43 ∷ X0 ∷ CS01 ∷ []) (wl0522 (lit c4)) ▸
       at 29 4 (X0 ∷ CS23⁻ ∷ X0 ∷ CS01 ∷ []) (wl0523 (lit c4)) ▸
       at 32 4 (X0 ∷ CX43 ∷ X0 ∷ CS01 ∷ []) (wl0522 (lit c4)) ▸
       at 35 4 (X0 ∷ CS24 ∷ X0 ∷ CS01 ∷ []) (wp0196 c4) ▸ done

  b23 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b23 = at 25 2 [] (wl0509 (lit c4)) ▸
       at 26 2 [] (wl0509 (lit c4)) ▸
       at 27 2 [] (wl0509 (lit c4)) ▸
       at 28 2 [] (wl0509 (lit c4)) ▸
       at 24 5 (CCZ234 ∷ []) (sym (wl0393 (lit c4))) ▸
       at 22 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸
       at 23 2 (CCZ234 ∷ K1 ∷ []) (c₂ (K ↑) (CCZ)) ▸
       at 24 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸ done

  b24 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ CS24 ∷ X0 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b24 = at 25 6 (X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wl0520 (lit c4)) ▸
       at 30 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸
       at 31 2 (CCZ234 ∷ K1 ∷ []) (c₂ (K ↑) (CCZ)) ▸
       at 32 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸
       at 31 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4)) ▸
       at 32 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 38 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b25 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ CS01 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ CS24 ∷ X0 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ X0 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b25 = at 41 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 29 4 (X0 ∷ CS23 ∷ X0 ∷ CS01 ∷ []) (wl0521 (lit c4)) ▸
       at 32 4 (X0 ∷ CX43 ∷ X0 ∷ CS01 ∷ []) (wl0522 (lit c4)) ▸
       at 35 4 (X0 ∷ CS23⁻ ∷ X0 ∷ CS01 ∷ []) (wl0523 (lit c4)) ▸
       at 38 4 (X0 ∷ CX43 ∷ X0 ∷ CS01 ∷ []) (wl0522 (lit c4)) ▸
       at 41 4 (X0 ∷ CS24 ∷ X0 ∷ CS01 ∷ []) (wp0196 c4) ▸
       at 31 2 [] (wl0509 (lit c4)) ▸
       at 32 2 [] (wl0509 (lit c4)) ▸ done

  b26 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1 ∷ X0 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b26 = at 33 2 [] (wl0509 (lit c4)) ▸
       at 34 2 [] (wl0509 (lit c4)) ▸
       at 30 5 (CCZ234 ∷ []) (sym (wl0393 (lit c4))) ▸
       at 28 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸
       at 29 2 (CCZ234 ∷ K1 ∷ []) (c₂ (K ↑) (CCZ)) ▸
       at 30 2 (X0 ∷ K1 ∷ []) (sym (c₁ (X) (K))) ▸
       at 21 2 [] (wl0509 (lit c4)) ▸
       at 22 2 [] (wl0509 (lit c4)) ▸ done

  b27 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b27 = at 23 2 [] (wl0509 (lit c4)) ▸
       at 20 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 20 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 29 1 (CS03 ∷ []) (refl) ▸
       at 22 12 (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wp0197 c4) ▸
       at 26 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 35 1 (CS03⁻ ∷ []) (refl) ▸
       at 31 6 (X0 ∷ CS03⁻ ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) (wl0524 (lit c4)) ▸ done

  b28 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b28 = at 32 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 21 2 [] (wl0509 (lit c4)) ▸
       at 22 2 [] (wl0509 (lit c4)) ▸
       at 23 2 [] (wl0509 (lit c4)) ▸
       at 24 2 [] (wl0509 (lit c4)) ▸
       at 20 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 20 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 21 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b29 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ CS01 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ CS01 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b29 = at 24 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 27 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 30 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 20 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 21 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 24 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 27 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 18 4 (X0 ∷ Toff204 ∷ X0 ∷ CS01 ∷ []) (wp0194 c4) ▸ done

  b30 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ CS01 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS01 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b30 = at 21 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ []) (wl0517 (lit c4)) ▸
       at 24 4 (X0 ∷ Toff204 ∷ X0 ∷ CS01 ∷ []) (wp0194 c4) ▸
       at 27 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS01 ∷ []) (wl0517 (lit c4)) ▸
       at 20 2 [] (wl0509 (lit c4)) ▸
       at 21 2 [] (wl0509 (lit c4)) ▸
       at 22 2 [] (wl0509 (lit c4)) ▸
       at 19 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 21 4 (X0 ∷ Toff314 ∷ X0 ∷ CS01 ∷ []) (wp0195 c4) ▸ done

  b31 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS01 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b31 = at 26 1 (CS03 ∷ []) (refl) ▸
       at 24 4 (X0 ∷ CS03 ∷ X0 ∷ CS01 ∷ []) (wl0518 (lit c4)) ▸
       at 25 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 27 4 (X0 ∷ Toff314 ∷ X0 ∷ CS01 ∷ []) (wp0195 c4) ▸
       at 32 1 (CS03⁻ ∷ []) (refl) ▸
       at 30 4 (X0 ∷ CS03⁻ ∷ X0 ∷ CS01 ∷ []) (wl0519 (lit c4)) ▸
       at 31 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 20 2 [] (wl0509 (lit c4)) ▸ done

  b32 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b32 = at 21 2 [] (wl0509 (lit c4)) ▸
       at 22 2 [] (wl0509 (lit c4)) ▸
       at 23 2 [] (wl0509 (lit c4)) ▸
       at 19 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 19 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 20 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 23 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 26 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b33 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S0⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ S0⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b33 = at 29 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 19 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 20 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 23 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 26 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 17 4 (X0 ∷ Toff204 ∷ X0 ∷ S0⁻ ∷ []) (wp0198 c4) ▸
       at 20 4 (X0 ∷ CCZ123 ∷ X0 ∷ S0⁻ ∷ []) (wl0525 (lit c4)) ▸
       at 23 4 (X0 ∷ Toff204 ∷ X0 ∷ S0⁻ ∷ []) (wp0198 c4) ▸ done

  b34 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ S0⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ S0⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b34 = at 26 4 (X0 ∷ CCZ123 ∷ X0 ∷ S0⁻ ∷ []) (wl0525 (lit c4)) ▸
       at 19 2 [] (wl0509 (lit c4)) ▸
       at 20 2 [] (wl0509 (lit c4)) ▸
       at 21 2 [] (wl0509 (lit c4)) ▸
       at 18 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 20 4 (X0 ∷ Toff314 ∷ X0 ∷ S0⁻ ∷ []) (wp0199 c4) ▸
       at 25 1 (CS03 ∷ []) (refl) ▸
       at 23 4 (X0 ∷ CS03 ∷ X0 ∷ S0⁻ ∷ []) (wl0526 (lit c4)) ▸ done

  b35 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ S0⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b35 = at 24 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 26 4 (X0 ∷ Toff314 ∷ X0 ∷ S0⁻ ∷ []) (wp0199 c4) ▸
       at 31 1 (CS03⁻ ∷ []) (refl) ▸
       at 29 4 (X0 ∷ CS03⁻ ∷ X0 ∷ S0⁻ ∷ []) (wl0527 (lit c4)) ▸
       at 30 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 19 2 [] (wl0509 (lit c4)) ▸
       at 20 2 [] (wl0509 (lit c4)) ▸
       at 21 2 [] (wl0509 (lit c4)) ▸ done

  b36 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ ι ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ S0⁻ ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b36 = at 22 2 [] (wl0509 (lit c4)) ▸
       at 18 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 16 2 (X0 ∷ ι ∷ []) (sym zc) ▸
       at 17 2 (Sb2-0-41-3 ∷ ι ∷ []) (sym zc) ▸
       at 18 2 (X0 ∷ ι ∷ []) (sym zc) ▸
       at 19 7 (CK01 ∷ []) (sym (wl0516 (lit c4))) ▸
       at 15 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 19 1 (CS03⁻ ∷ []) (refl) ▸ done

  b37 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b37 = at 21 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 22 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 25 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 28 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 31 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 21 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 22 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 25 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b38 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b38 = at 28 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 19 4 (X0 ∷ Toff204 ∷ X0 ∷ CS03⁻ ∷ []) (wp0200 c4) ▸
       at 22 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ []) (wl0528 (lit c4)) ▸
       at 25 4 (X0 ∷ Toff204 ∷ X0 ∷ CS03⁻ ∷ []) (wp0200 c4) ▸
       at 28 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ []) (wl0528 (lit c4)) ▸
       at 21 2 [] (wl0509 (lit c4)) ▸
       at 22 2 [] (wl0509 (lit c4)) ▸
       at 23 2 [] (wl0509 (lit c4)) ▸ done

  b39 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS03⁻ ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b39 = at 20 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 27 1 (CS03 ∷ []) (refl) ▸
       at 22 10 (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ []) (wp0201 c4) ▸
       at 26 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 33 1 (CS03⁻ ∷ []) (refl) ▸
       at 31 4 (X0 ∷ CS03⁻ ∷ X0 ∷ CS03⁻ ∷ []) (wl0529 (lit c4)) ▸
       at 32 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 21 2 [] (wl0509 (lit c4)) ▸ done

  b40 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS03⁻ ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b40 = at 22 2 [] (wl0509 (lit c4)) ▸
       at 23 2 [] (wl0509 (lit c4)) ▸
       at 24 2 [] (wl0509 (lit c4)) ▸
       at 20 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 22 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 18 2 (X0 ∷ Toff314 ∷ []) (wp0202 c4) ▸
       at 19 2 (Sb2-0-41-3 ∷ Toff314 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314213240 c4) ▸
       at 20 2 (X0 ∷ Toff314 ∷ []) (wp0202 c4) ▸ done

  b41 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b41 = at 17 1 (CS03 ∷ []) (refl) ▸
       at 19 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 20 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 23 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 26 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 29 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 19 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 20 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b42 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b42 = at 23 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 26 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 17 4 (X0 ∷ Toff204 ∷ X0 ∷ CS03 ∷ []) (wp0203 c4) ▸
       at 20 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ []) (wl0530 (lit c4)) ▸
       at 23 4 (X0 ∷ Toff204 ∷ X0 ∷ CS03 ∷ []) (wp0203 c4) ▸
       at 26 4 (X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ []) (wl0530 (lit c4)) ▸
       at 19 2 [] (wl0509 (lit c4)) ▸
       at 20 2 [] (wl0509 (lit c4)) ▸ done

  b43 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b43 = at 21 2 [] (wl0509 (lit c4)) ▸
       at 18 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 25 1 (CS03 ∷ []) (refl) ▸
       at 20 10 (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ []) (wp0204 c4) ▸
       at 24 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 31 1 (CS03⁻ ∷ []) (refl) ▸
       at 29 4 (X0 ∷ CS03⁻ ∷ X0 ∷ CS03 ∷ []) (wl0531 (lit c4)) ▸
       at 30 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b44 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ X0 ∷ Sb2-0-41-3 ∷ Toff314 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b44 = at 19 2 [] (wl0509 (lit c4)) ▸
       at 20 2 [] (wl0509 (lit c4)) ▸
       at 21 2 [] (wl0509 (lit c4)) ▸
       at 22 2 [] (wl0509 (lit c4)) ▸
       at 18 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 20 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 16 2 (X0 ∷ Toff314 ∷ []) (wp0202 c4) ▸
       at 17 2 (Sb2-0-41-3 ∷ Toff314 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨3·4·12·0⟩-at0314213240 c4) ▸ done

  b45 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ X0 ∷ Sb2-0-41-3 ∷ Toff314 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ CCZ134 ∷ X0 ∷ Sb2-0-41-3 ∷ CCZ134 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b45 = at 18 2 (X0 ∷ Toff314 ∷ []) (wp0202 c4) ▸
       at 15 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 16 3 (CCZ134 ∷ Bx2-0413 ∷ []) (lem-X1-beta-at0210243143 c4) ▸
       at 17 2 (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 c4) ▸
       at 18 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 19 3 (CCZ134 ∷ Bx2-0413 ∷ []) (lem-X1-beta-at0210243143 c4) ▸
       at 15 2 (CCZ134 ∷ X0 ∷ []) (sym (wp0205 c4)) ▸
       at 18 2 (CCZ134 ∷ X0 ∷ []) (sym (wp0205 c4)) ▸ done

  b46 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ CCZ134 ∷ X0 ∷ Sb2-0-41-3 ∷ CCZ134 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b46 = at 17 2 (CCZ134 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ234-at0210243143 c4) ▸
       at 16 2 (CCZ134 ∷ X0 ∷ []) (sym (wp0205 c4)) ▸
       at 15 2 [] (wl0503 (lit c4)) ▸
       at 18 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 16 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 17 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 20 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 23 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b47 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b47 = at 26 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 16 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 17 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 20 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 23 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 14 4 (X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ []) (wp0182 c4) ▸
       at 19 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸
       at 20 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b48 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ X0 ∷ CS12 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b48 = at 23 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 26 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 29 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 17 4 (X0 ∷ CS23 ∷ X0 ∷ CS04⁻ ∷ []) (wp0183 c4) ▸
       at 20 4 (X0 ∷ CX13 ∷ X0 ∷ CS04⁻ ∷ []) (wp0184 c4) ▸
       at 23 4 (X0 ∷ CS23⁻ ∷ X0 ∷ CS04⁻ ∷ []) (wp0185 c4) ▸
       at 26 4 (X0 ∷ CX13 ∷ X0 ∷ CS04⁻ ∷ []) (wp0184 c4) ▸
       at 29 4 (X0 ∷ CS12 ∷ X0 ∷ CS04⁻ ∷ []) (wp0186 c4) ▸ done

  b49 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ X0 ∷ CS12 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b49 = at 19 2 [] (wl0509 (lit c4)) ▸
       at 20 2 [] (wl0509 (lit c4)) ▸
       at 21 2 [] (wl0509 (lit c4)) ▸
       at 22 2 [] (wl0509 (lit c4)) ▸
       at 18 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 20 4 (X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ []) (wp0182 c4) ▸
       at 25 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸
       at 26 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b50 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ X0 ∷ CS12 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b50 = at 29 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 32 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 23 4 (X0 ∷ CS23 ∷ X0 ∷ CS04⁻ ∷ []) (wp0183 c4) ▸
       at 26 4 (X0 ∷ CX13 ∷ X0 ∷ CS04⁻ ∷ []) (wp0184 c4) ▸
       at 29 4 (X0 ∷ CS23⁻ ∷ X0 ∷ CS04⁻ ∷ []) (wp0185 c4) ▸
       at 32 4 (X0 ∷ CX13 ∷ X0 ∷ CS04⁻ ∷ []) (wp0184 c4) ▸
       at 35 4 (X0 ∷ CS12 ∷ X0 ∷ CS04⁻ ∷ []) (wp0186 c4) ▸ done

  b51 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ X0 ∷ CS12 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b51 = at 25 2 [] (wl0509 (lit c4)) ▸
       at 26 2 [] (wl0509 (lit c4)) ▸
       at 27 2 [] (wl0509 (lit c4)) ▸
       at 28 2 [] (wl0509 (lit c4)) ▸
       at 24 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 16 2 [] (wl0509 (lit c4)) ▸
       at 17 2 [] (wl0509 (lit c4)) ▸
       at 18 2 [] (wl0509 (lit c4)) ▸ done

  b52 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b52 = at 15 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 17 4 (X0 ∷ Toff314 ∷ X0 ∷ CS04⁻ ∷ []) (wp0187 c4) ▸
       at 22 1 (CS03 ∷ []) (refl) ▸
       at 20 4 (X0 ∷ CS03 ∷ X0 ∷ CS04⁻ ∷ []) (wp0188 c4) ▸
       at 21 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 23 4 (X0 ∷ Toff314 ∷ X0 ∷ CS04⁻ ∷ []) (wp0187 c4) ▸
       at 28 1 (CS03⁻ ∷ []) (refl) ▸
       at 26 4 (X0 ∷ CS03⁻ ∷ X0 ∷ CS04⁻ ∷ []) (wp0189 c4) ▸ done

  b53 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b53 = at 27 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 16 2 [] (wl0509 (lit c4)) ▸
       at 17 2 [] (wl0509 (lit c4)) ▸
       at 18 2 [] (wl0509 (lit c4)) ▸
       at 19 2 [] (wl0509 (lit c4)) ▸
       at 15 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 15 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 16 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b54 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ S0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b54 = at 19 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 22 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 25 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 15 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 16 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 19 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 22 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 13 4 (X0 ∷ Toff204 ∷ X0 ∷ S0 ∷ []) (wp0190 c4) ▸ done

  b55 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ S0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b55 = at 16 4 (X0 ∷ CCZ123 ∷ X0 ∷ S0 ∷ []) (wl0510 (lit c4)) ▸
       at 19 4 (X0 ∷ Toff204 ∷ X0 ∷ S0 ∷ []) (wp0190 c4) ▸
       at 22 4 (X0 ∷ CCZ123 ∷ X0 ∷ S0 ∷ []) (wl0510 (lit c4)) ▸
       at 15 2 [] (wl0509 (lit c4)) ▸
       at 16 2 [] (wl0509 (lit c4)) ▸
       at 17 2 [] (wl0509 (lit c4)) ▸
       at 14 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 16 4 (X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ []) (wp0191 c4) ▸ done

  b56 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b56 = at 21 1 (CS03 ∷ []) (refl) ▸
       at 19 4 (X0 ∷ CS03 ∷ X0 ∷ S0 ∷ []) (wl0511 (lit c4)) ▸
       at 20 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 22 4 (X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ []) (wp0191 c4) ▸
       at 27 1 (CS03⁻ ∷ []) (refl) ▸
       at 25 4 (X0 ∷ CS03⁻ ∷ X0 ∷ S0 ∷ []) (wl0512 (lit c4)) ▸
       at 26 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 15 2 [] (wl0509 (lit c4)) ▸ done

  b57 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b57 = at 16 2 [] (wl0509 (lit c4)) ▸
       at 17 2 [] (wl0509 (lit c4)) ▸
       at 18 2 [] (wl0509 (lit c4)) ▸
       at 14 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 20 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 24 1 (CS03⁻ ∷ []) (refl) ▸
       at 24 4 (X0 ∷ CK01 ∷ X0 ∷ CS03⁻ ∷ []) (wl0513 (lit c4)) ▸
       at 27 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b58 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ X0 ∷ CK01 ∷ X0 ∷ CCZ234 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b58 = at 22 1 (CS03 ∷ []) (refl) ▸
       at 21 6 (X0 ∷ CK01 ∷ X0 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ []) (wp0192 c4) ▸
       at 25 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 20 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 20 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 23 2 (X0 ∷ CCZ234 ∷ []) (sym (c₁ (X) (CCZ ↑))) ▸
       at 24 2 (CK01 ∷ CCZ234 ∷ []) (sym (c₂ (CK₀₁) (CCZ))) ▸
       at 25 2 (X0 ∷ CCZ234 ∷ []) (sym (c₁ (X) (CCZ ↑))) ▸ done

  b59 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ X0 ∷ CK01 ∷ X0 ∷ CCZ234 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b59 = at 22 4 (X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ []) (wl0514 (lit c4)) ▸
       at 21 2 (X0 ∷ CCZ234 ∷ []) (sym (c₁ (X) (CCZ ↑))) ▸
       at 22 2 (CK01 ∷ CCZ234 ∷ []) (sym (c₂ (CK₀₁) (CCZ))) ▸
       at 23 2 (X0 ∷ CCZ234 ∷ []) (sym (c₁ (X) (CCZ ↑))) ▸
       at 20 4 (X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ []) (wl0514 (lit c4)) ▸
       at 23 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 23 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 23 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

  b60 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ X0 ∷ CK01 ∷ X0 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b60 = at 19 4 (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (wl0532 (lit c4)) ▸
       at 18 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 22 1 (CS03⁻ ∷ []) (refl) ▸
       at 22 4 (X0 ∷ CK01 ∷ X0 ∷ CS03⁻ ∷ []) (wl0513 (lit c4)) ▸
       at 25 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 20 1 (CS03 ∷ []) (refl) ▸
       at 19 6 (X0 ∷ CK01 ∷ X0 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ []) (wp0192 c4) ▸
       at 23 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b61 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Bx2-0413 ∷ X0 ∷ CK01 ∷ X0 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Toff201 ∷ X0 ∷ CK01 ∷ CCZ234 ∷ X0 ∷ Toff201 ∷ CCZ234 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b61 = at 18 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 18 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 21 2 (X0 ∷ CCZ234 ∷ []) (sym (c₁ (X) (CCZ ↑))) ▸
       at 22 2 (CK01 ∷ CCZ234 ∷ []) (sym (c₂ (CK₀₁) (CCZ))) ▸
       at 23 2 (X0 ∷ CCZ234 ∷ []) (sym (c₁ (X) (CCZ ↑))) ▸
       at 20 4 (X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ []) (wl0514 (lit c4)) ▸
       at 19 2 (X0 ∷ CCZ234 ∷ []) (sym (c₁ (X) (CCZ ↑))) ▸
       at 20 2 (CK01 ∷ CCZ234 ∷ []) (sym (c₂ (CK₀₁) (CCZ))) ▸ done

  b62 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Toff201 ∷ X0 ∷ CK01 ∷ CCZ234 ∷ X0 ∷ Toff201 ∷ CCZ234 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b62 = at 21 2 (X0 ∷ CCZ234 ∷ []) (sym (c₁ (X) (CCZ ↑))) ▸
       at 18 4 (X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ []) (wl0514 (lit c4)) ▸
       at 21 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 21 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸ done


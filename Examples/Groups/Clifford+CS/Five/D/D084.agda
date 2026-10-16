{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D084 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0379 ; wl0382 ; wl0383 ; wl0384 ; wl0385 ; wl0393 ; wl0402 ; wl0403 ; wl0404 ; wl0405 ; wl0406 ; wl0415 ; wl0416 ; wl0417 ; wl0418 ; wl0419 ; wl0424 ; wl0425 ; wl0426 ; wl0427 ; wl0428 ; wl0429 ; wl0430 ; wl0431 ; wl0433 ; wl0434 ; wl0440 ; wl0441 ; wl0442 ; wl0443 ; wl0444 ; wl0445 ; wl0461 ; wl0462 ; wl0463 ; wl0464 ; wp0130 ; wp0143 ; wp0146 ; wp0147 ; wp0148 ; wp0149 ; wp0150 ; wp0155 ; wp0168)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym34-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-sym12-at021021 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym23-at0220 ; lem-sym23-at022330)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 ; lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 ; lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0312203441 ; lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 ; lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-beta-T-at022330 ; lem-sym12-at02203443 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at0220)
open import Examples.Groups.Clifford+CS.Five.D.D044 using (lem-auto-CS01-∣-BOX⟨1·2340⟩-at0312203441 ; lem-auto-CSd01-∣-BOX⟨1·2340⟩-at0312203441 ; lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-CX41-TOFF203)
-- F1 CS-K0 part39: 500 steps
lem-F1-CS-K0-part39 : Ws → ⟪ (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Bx⁻2-0413 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K0-part39 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (run b62))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b0 = at 17 2 [] (wl0379 (lit c4)) ▸
       at 18 2 [] (wl0379 (lit c4)) ▸
       at 19 2 [] (wl0379 (lit c4)) ▸
       at 16 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 16 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 18 4 (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (wl0415 (lit c4)) ▸
       at 23 1 (CS03 ∷ []) (refl) ▸
       at 21 4 (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) (wl0416 (lit c4)) ▸ done

  b1 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b1 = at 22 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 24 4 (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (wl0415 (lit c4)) ▸
       at 29 1 (CS03⁻ ∷ []) (refl) ▸
       at 27 4 (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) (wl0417 (lit c4)) ▸
       at 28 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 17 2 [] (wl0379 (lit c4)) ▸
       at 18 2 [] (wl0379 (lit c4)) ▸
       at 19 2 [] (wl0379 (lit c4)) ▸ done

  b2 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ CS03 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b2 = at 20 2 [] (wl0379 (lit c4)) ▸
       at 16 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 18 5 (CCZ134 ∷ []) (sym (wl0404 (lit c4))) ▸
       at 14 2 (X1 ∷ K3 ∷ []) (wl0418 (lit c4)) ▸
       at 15 2 (Sb2-0-41-3 ∷ K3 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4) ▸
       at 16 2 (X1 ∷ K3 ∷ []) (wl0418 (lit c4)) ▸
       at 17 3 (Toff314 ∷ []) (wl0402 (lit c4)) ▸
       at 13 1 (CS03 ∷ []) (refl) ▸ done

  b3 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ CS03 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b3 = at 13 2 (X1 ∷ CS03 ∷ []) (wl0419 (lit c4)) ▸
       at 14 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 14 2 (Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 c4) ▸
       at 15 1 (CS03 ∷ []) (refl) ▸
       at 15 2 (X1 ∷ CS03 ∷ []) (wl0419 (lit c4)) ▸
       at 16 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 16 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 12 1 (CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ []) (wl0424 (lit c4)) ▸ done

  b4 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b4 = at 18 2 (X1 ∷ ι⁻ ∷ []) (sym zc⁻) ▸
       at 19 2 (Sb2-0-41-3 ∷ ι⁻ ∷ []) (sym zc⁻) ▸
       at 20 2 (X1 ∷ ι⁻ ∷ []) (sym zc⁻) ▸
       at 19 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 20 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 23 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 26 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 29 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b5 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b5 = at 19 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 20 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 23 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 26 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 17 4 (X1 ∷ Toff204 ∷ X1 ∷ S1 ∷ []) (wp0130 c4) ▸
       at 20 4 (X1 ∷ CCZ123 ∷ X1 ∷ S1 ∷ []) (wl0382 (lit c4)) ▸
       at 23 4 (X1 ∷ Toff204 ∷ X1 ∷ S1 ∷ []) (wp0130 c4) ▸
       at 26 4 (X1 ∷ CCZ123 ∷ X1 ∷ S1 ∷ []) (wl0382 (lit c4)) ▸ done

  b6 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b6 = at 19 2 [] (wl0379 (lit c4)) ▸
       at 20 2 [] (wl0379 (lit c4)) ▸
       at 21 2 [] (wl0379 (lit c4)) ▸
       at 18 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 20 4 (X1 ∷ Toff314 ∷ X1 ∷ S1 ∷ []) (wl0383 (lit c4)) ▸
       at 25 1 (CS03 ∷ []) (refl) ▸
       at 23 4 (X1 ∷ CS03 ∷ X1 ∷ S1 ∷ []) (wl0384 (lit c4)) ▸
       at 24 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b7 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b7 = at 26 4 (X1 ∷ Toff314 ∷ X1 ∷ S1 ∷ []) (wl0383 (lit c4)) ▸
       at 31 1 (CS03⁻ ∷ []) (refl) ▸
       at 29 4 (X1 ∷ CS03⁻ ∷ X1 ∷ S1 ∷ []) (wl0385 (lit c4)) ▸
       at 30 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 19 2 [] (wl0379 (lit c4)) ▸
       at 20 2 [] (wl0379 (lit c4)) ▸
       at 21 2 [] (wl0379 (lit c4)) ▸
       at 22 2 [] (wl0379 (lit c4)) ▸ done

  b8 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b8 = at 18 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 18 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 19 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 22 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 25 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 28 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 18 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 19 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b9 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b9 = at 22 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 25 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 16 4 (X1 ∷ Toff204 ∷ X1 ∷ CS01⁻ ∷ []) (wp0146 c4) ▸
       at 19 4 (X1 ∷ CCZ123 ∷ X1 ∷ CS01⁻ ∷ []) (wl0425 (lit c4)) ▸
       at 22 4 (X1 ∷ Toff204 ∷ X1 ∷ CS01⁻ ∷ []) (wp0146 c4) ▸
       at 25 4 (X1 ∷ CCZ123 ∷ X1 ∷ CS01⁻ ∷ []) (wl0425 (lit c4)) ▸
       at 18 2 [] (wl0379 (lit c4)) ▸
       at 19 2 [] (wl0379 (lit c4)) ▸ done

  b10 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b10 = at 20 2 [] (wl0379 (lit c4)) ▸
       at 17 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 19 4 (X1 ∷ Toff314 ∷ X1 ∷ CS01⁻ ∷ []) (wp0147 c4) ▸
       at 24 1 (CS03 ∷ []) (refl) ▸
       at 22 4 (X1 ∷ CS03 ∷ X1 ∷ CS01⁻ ∷ []) (wl0427 (lit c4)) ▸
       at 23 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 25 4 (X1 ∷ Toff314 ∷ X1 ∷ CS01⁻ ∷ []) (wp0147 c4) ▸
       at 30 1 (CS03⁻ ∷ []) (refl) ▸ done

  b11 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b11 = at 28 4 (X1 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ []) (wl0426 (lit c4)) ▸
       at 29 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 18 2 [] (wl0379 (lit c4)) ▸
       at 19 2 [] (wl0379 (lit c4)) ▸
       at 20 2 [] (wl0379 (lit c4)) ▸
       at 21 2 [] (wl0379 (lit c4)) ▸
       at 17 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 17 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b12 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b12 = at 18 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 21 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 24 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 27 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 17 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 17 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 18 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 21 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b13 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ X1 ∷ CS23 ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X1 ∷ K0⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b13 = at 24 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 13 6 (X1 ∷ Toff201 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wl0431 (lit c4)) ▸
       at 18 2 (X1 ∷ K0⁻ ∷ []) (c₁ (K • iI) (X)) ▸
       at 19 2 (CCZ234 ∷ K0⁻ ∷ []) (c₁ (K • iI) (CCZ ↑)) ▸
       at 20 2 (X1 ∷ K0⁻ ∷ []) (c₁ (K • iI) (X)) ▸
       at 19 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4)) ▸
       at 20 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 23 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b14 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ X1 ∷ CS23 ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X1 ∷ K0⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ K0⁻ ∷ X1 ∷ CS23 ∷ CX43 ∷ X1 ∷ X1 ∷ CS23⁻ ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b14 = at 26 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 29 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 17 4 (X1 ∷ CS23 ∷ X1 ∷ CS01⁻ ∷ []) (wl0430 (lit c4)) ▸
       at 20 4 (X1 ∷ CX43 ∷ X1 ∷ CS01⁻ ∷ []) (wl0428 (lit c4)) ▸
       at 23 4 (X1 ∷ CS23⁻ ∷ X1 ∷ CS01⁻ ∷ []) (wl0429 (lit c4)) ▸
       at 26 4 (X1 ∷ CX43 ∷ X1 ∷ CS01⁻ ∷ []) (wl0428 (lit c4)) ▸
       at 29 4 (X1 ∷ CS24 ∷ X1 ∷ CS01⁻ ∷ []) (wp0148 c4) ▸
       at 19 2 [] (wl0379 (lit c4)) ▸ done

  b15 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ K0⁻ ∷ X1 ∷ CS23 ∷ CX43 ∷ X1 ∷ X1 ∷ CS23⁻ ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b15 = at 20 2 [] (wl0379 (lit c4)) ▸
       at 21 2 [] (wl0379 (lit c4)) ▸
       at 22 2 [] (wl0379 (lit c4)) ▸
       at 18 5 (CCZ234 ∷ []) (sym (wl0393 (lit c4))) ▸
       at 16 2 (X1 ∷ K0⁻ ∷ []) (c₁ (K • iI) (X)) ▸
       at 17 2 (CCZ234 ∷ K0⁻ ∷ []) (c₁ (K • iI) (CCZ ↑)) ▸
       at 18 2 (X1 ∷ K0⁻ ∷ []) (c₁ (K • iI) (X)) ▸
       at 19 6 (X1 ∷ Toff201 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wl0431 (lit c4)) ▸ done

  b16 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ X1 ∷ CS23 ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS23⁻ ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ K0⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b16 = at 24 2 (X1 ∷ K0⁻ ∷ []) (c₁ (K • iI) (X)) ▸
       at 25 2 (CCZ234 ∷ K0⁻ ∷ []) (c₁ (K • iI) (CCZ ↑)) ▸
       at 26 2 (X1 ∷ K0⁻ ∷ []) (c₁ (K • iI) (X)) ▸
       at 25 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4)) ▸
       at 26 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 29 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 32 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 35 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b17 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ X1 ∷ CS23 ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS23⁻ ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ K0⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0⁻ ∷ X1 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b17 = at 23 4 (X1 ∷ CS23 ∷ X1 ∷ CS01⁻ ∷ []) (wl0430 (lit c4)) ▸
       at 26 4 (X1 ∷ CX43 ∷ X1 ∷ CS01⁻ ∷ []) (wl0428 (lit c4)) ▸
       at 29 4 (X1 ∷ CS23⁻ ∷ X1 ∷ CS01⁻ ∷ []) (wl0429 (lit c4)) ▸
       at 32 4 (X1 ∷ CX43 ∷ X1 ∷ CS01⁻ ∷ []) (wl0428 (lit c4)) ▸
       at 35 4 (X1 ∷ CS24 ∷ X1 ∷ CS01⁻ ∷ []) (wp0148 c4) ▸
       at 25 2 [] (wl0379 (lit c4)) ▸
       at 26 2 [] (wl0379 (lit c4)) ▸
       at 27 2 [] (wl0379 (lit c4)) ▸ done

  b18 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0⁻ ∷ X1 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b18 = at 28 2 [] (wl0379 (lit c4)) ▸
       at 24 5 (CCZ234 ∷ []) (sym (wl0393 (lit c4))) ▸
       at 22 2 (X1 ∷ K0⁻ ∷ []) (c₁ (K • iI) (X)) ▸
       at 23 2 (CCZ234 ∷ K0⁻ ∷ []) (c₁ (K • iI) (CCZ ↑)) ▸
       at 24 2 (X1 ∷ K0⁻ ∷ []) (c₁ (K • iI) (X)) ▸
       at 15 2 [] (wl0379 (lit c4)) ▸
       at 16 2 [] (wl0379 (lit c4)) ▸
       at 17 2 [] (wl0379 (lit c4)) ▸ done

  b19 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b19 = at 14 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 14 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 16 6 (X1 ∷ Toff314 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wp0149 c4) ▸
       at 23 1 (CS03 ∷ []) (refl) ▸
       at 29 1 (CS03⁻ ∷ []) (refl) ▸
       at 19 12 (X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wp0150 c4) ▸
       at 20 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 26 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b20 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b20 = at 15 2 [] (wl0379 (lit c4)) ▸
       at 16 2 [] (wl0379 (lit c4)) ▸
       at 17 2 [] (wl0379 (lit c4)) ▸
       at 18 2 [] (wl0379 (lit c4)) ▸
       at 14 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 14 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 15 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 18 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b21 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b21 = at 21 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 24 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 14 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 15 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 18 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 21 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 12 4 (X1 ∷ Toff204 ∷ X1 ∷ CS01⁻ ∷ []) (wp0146 c4) ▸
       at 15 4 (X1 ∷ CCZ123 ∷ X1 ∷ CS01⁻ ∷ []) (wl0425 (lit c4)) ▸ done

  b22 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b22 = at 18 4 (X1 ∷ Toff204 ∷ X1 ∷ CS01⁻ ∷ []) (wp0146 c4) ▸
       at 21 4 (X1 ∷ CCZ123 ∷ X1 ∷ CS01⁻ ∷ []) (wl0425 (lit c4)) ▸
       at 14 2 [] (wl0379 (lit c4)) ▸
       at 15 2 [] (wl0379 (lit c4)) ▸
       at 16 2 [] (wl0379 (lit c4)) ▸
       at 13 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 15 4 (X1 ∷ Toff314 ∷ X1 ∷ CS01⁻ ∷ []) (wp0147 c4) ▸
       at 20 1 (CS03 ∷ []) (refl) ▸ done

  b23 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b23 = at 18 4 (X1 ∷ CS03 ∷ X1 ∷ CS01⁻ ∷ []) (wl0427 (lit c4)) ▸
       at 19 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 21 4 (X1 ∷ Toff314 ∷ X1 ∷ CS01⁻ ∷ []) (wp0147 c4) ▸
       at 26 1 (CS03⁻ ∷ []) (refl) ▸
       at 24 4 (X1 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ []) (wl0426 (lit c4)) ▸
       at 25 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 14 2 [] (wl0379 (lit c4)) ▸
       at 15 2 [] (wl0379 (lit c4)) ▸ done

  b24 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b24 = at 16 2 [] (wl0379 (lit c4)) ▸
       at 17 2 [] (wl0379 (lit c4)) ▸
       at 13 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 15 7 (CK10⁻ ∷ []) (sym (wl0424 (lit c4))) ▸
       at 11 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 15 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 15 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 20 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b25 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b25 = at 21 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 24 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 27 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 30 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 18 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸
       at 24 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 24 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 25 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b26 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b26 = at 28 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 31 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 22 4 (X1 ∷ Toff201 ∷ X1 ∷ CS12 ∷ []) (wl0442 (lit c4)) ▸
       at 25 4 (X1 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ []) (wl0441 (lit c4)) ▸
       at 28 4 (X1 ∷ Toff201 ∷ X1 ∷ CS12 ∷ []) (wl0442 (lit c4)) ▸
       at 31 4 (X1 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ []) (wl0441 (lit c4)) ▸
       at 24 2 [] (wl0379 (lit c4)) ▸
       at 25 2 [] (wl0379 (lit c4)) ▸ done

  b27 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X1 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b27 = at 26 2 [] (wl0379 (lit c4)) ▸
       at 23 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 23 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 23 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 23 1 (Bx2-0134 ∷ []) (lem-sym34-at0210213443 c4) ▸
       at 23 1 (Bx2-1034 ∷ []) (lem-sym12-at021021 c4) ▸
       at 23 1 (Bx2-1304 ∷ []) (lem-sym23-at0220 c4) ▸
       at 23 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-beta-T-at022330 c4) ▸ done

  b28 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X1 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ CS02 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b28 = at 24 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 27 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 30 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 21 4 (X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ []) (wl0464 (lit c4)) ▸
       at 26 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4) ▸
       at 27 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 30 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 33 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b29 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ CS02 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CX13 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b29 = at 36 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 24 4 (X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ []) (wl0463 (lit c4)) ▸
       at 27 4 (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) (wp0168 c4) ▸
       at 30 4 (X1 ∷ CS24⁻ ∷ X1 ∷ CX13 ∷ []) (wl0462 (lit c4)) ▸
       at 33 4 (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) (wp0168 c4) ▸
       at 36 4 (X1 ∷ CS02 ∷ X1 ∷ CX13 ∷ []) (wl0461 (lit c4)) ▸
       at 26 2 [] (wl0379 (lit c4)) ▸
       at 27 2 [] (wl0379 (lit c4)) ▸ done

  b30 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CX13 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ CS02 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b30 = at 28 2 [] (wl0379 (lit c4)) ▸
       at 29 2 [] (wl0379 (lit c4)) ▸
       at 25 5 (CCZ024 ∷ []) (sym (wp0143 c4)) ▸
       at 27 4 (X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ []) (wl0464 (lit c4)) ▸
       at 32 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4) ▸
       at 33 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 36 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 39 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b31 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ CS02 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b31 = at 42 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 30 4 (X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ []) (wl0463 (lit c4)) ▸
       at 33 4 (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) (wp0168 c4) ▸
       at 36 4 (X1 ∷ CS24⁻ ∷ X1 ∷ CX13 ∷ []) (wl0462 (lit c4)) ▸
       at 39 4 (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) (wp0168 c4) ▸
       at 42 4 (X1 ∷ CS02 ∷ X1 ∷ CX13 ∷ []) (wl0461 (lit c4)) ▸
       at 32 2 [] (wl0379 (lit c4)) ▸
       at 33 2 [] (wl0379 (lit c4)) ▸ done

  b32 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Bx2-1034 ∷ X1 ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b32 = at 34 2 [] (wl0379 (lit c4)) ▸
       at 35 2 [] (wl0379 (lit c4)) ▸
       at 31 5 (CCZ024 ∷ []) (sym (wp0143 c4)) ▸
       at 23 2 [] (wl0379 (lit c4)) ▸
       at 24 2 [] (wl0379 (lit c4)) ▸
       at 25 2 [] (wl0379 (lit c4)) ▸
       at 22 4 (Bx2-1304 ∷ []) (sym (lem-beta-T-at022330 c4)) ▸
       at 22 1 (Bx2-1034 ∷ []) (lem-sym23-at022330 c4) ▸ done

  b33 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Bx2-1034 ∷ X1 ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ X1 ∷ Bx2-0134 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b33 = at 22 1 (Bx2-1043 ∷ []) (lem-sym34-at0220 c4) ▸
       at 22 1 (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4) ▸
       at 22 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 20 2 (X1 ∷ CS23⁻ ∷ []) (wl0440 (lit c4)) ▸
       at 21 2 (Bx2-0413 ∷ CS23⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2340⟩-at0312203441 c4) ▸
       at 22 2 (X1 ∷ CS23⁻ ∷ []) (wl0440 (lit c4)) ▸
       at 21 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 21 1 (Bx2-0134 ∷ []) (lem-sym34-at0210213443 c4) ▸ done

  b34 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ X1 ∷ Bx2-0134 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b34 = at 21 1 (Bx2-1034 ∷ []) (lem-sym12-at021021 c4) ▸
       at 21 1 (Bx2-1304 ∷ []) (lem-sym23-at0220 c4) ▸
       at 21 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-beta-T-at022330 c4) ▸
       at 22 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 25 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 28 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 19 4 (X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ []) (wl0464 (lit c4)) ▸
       at 24 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4) ▸ done

  b35 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ X1 ∷ CS02 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b35 = at 25 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 28 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 31 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 34 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 22 4 (X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ []) (wl0463 (lit c4)) ▸
       at 25 4 (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) (wp0168 c4) ▸
       at 28 4 (X1 ∷ CS24⁻ ∷ X1 ∷ CX13 ∷ []) (wl0462 (lit c4)) ▸
       at 31 4 (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) (wp0168 c4) ▸ done

  b36 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ X1 ∷ CS02 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b36 = at 34 4 (X1 ∷ CS02 ∷ X1 ∷ CX13 ∷ []) (wl0461 (lit c4)) ▸
       at 24 2 [] (wl0379 (lit c4)) ▸
       at 25 2 [] (wl0379 (lit c4)) ▸
       at 26 2 [] (wl0379 (lit c4)) ▸
       at 27 2 [] (wl0379 (lit c4)) ▸
       at 23 5 (CCZ024 ∷ []) (sym (wp0143 c4)) ▸
       at 25 4 (X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ []) (wl0464 (lit c4)) ▸
       at 30 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4) ▸ done

  b37 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ X1 ∷ CS02 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b37 = at 31 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 34 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 37 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 40 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 28 4 (X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ []) (wl0463 (lit c4)) ▸
       at 31 4 (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) (wp0168 c4) ▸
       at 34 4 (X1 ∷ CS24⁻ ∷ X1 ∷ CX13 ∷ []) (wl0462 (lit c4)) ▸
       at 37 4 (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) (wp0168 c4) ▸ done

  b38 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ X1 ∷ CS02 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b38 = at 40 4 (X1 ∷ CS02 ∷ X1 ∷ CX13 ∷ []) (wl0461 (lit c4)) ▸
       at 30 2 [] (wl0379 (lit c4)) ▸
       at 31 2 [] (wl0379 (lit c4)) ▸
       at 32 2 [] (wl0379 (lit c4)) ▸
       at 33 2 [] (wl0379 (lit c4)) ▸
       at 29 5 (CCZ024 ∷ []) (sym (wp0143 c4)) ▸
       at 21 2 [] (wl0379 (lit c4)) ▸
       at 22 2 [] (wl0379 (lit c4)) ▸ done

  b39 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ X1 ∷ Bx2-0413 ∷ CS23 ∷ X1 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b39 = at 23 2 [] (wl0379 (lit c4)) ▸
       at 20 4 (Bx2-1304 ∷ []) (sym (lem-beta-T-at022330 c4)) ▸
       at 20 1 (Bx2-1034 ∷ []) (lem-sym23-at022330 c4) ▸
       at 20 1 (Bx2-1043 ∷ []) (lem-sym34-at0220 c4) ▸
       at 20 1 (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4) ▸
       at 20 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 18 2 (X1 ∷ CS23 ∷ []) (wl0434 (lit c4)) ▸
       at 19 2 (Bx2-0413 ∷ CS23 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2340⟩-at0312203441 c4) ▸ done

  b40 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ X1 ∷ Bx2-0413 ∷ CS23 ∷ X1 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b40 = at 20 2 (X1 ∷ CS23 ∷ []) (wl0434 (lit c4)) ▸
       at 21 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 21 4 (X1 ∷ Toff314 ∷ X1 ∷ CCZ123 ∷ []) (wl0443 (lit c4)) ▸
       at 26 1 (CS03 ∷ []) (refl) ▸
       at 24 4 (X1 ∷ CS03 ∷ X1 ∷ CCZ123 ∷ []) (wl0445 (lit c4)) ▸
       at 25 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 27 4 (X1 ∷ Toff314 ∷ X1 ∷ CCZ123 ∷ []) (wl0443 (lit c4)) ▸
       at 32 1 (CS03⁻ ∷ []) (refl) ▸ done

  b41 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ Toff204 ∷ Sb2-0-41-3 ∷ X1 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b41 = at 30 4 (X1 ∷ CS03⁻ ∷ X1 ∷ CCZ123 ∷ []) (wl0444 (lit c4)) ▸
       at 31 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 20 2 [] (wl0379 (lit c4)) ▸
       at 21 2 [] (wl0379 (lit c4)) ▸
       at 22 2 [] (wl0379 (lit c4)) ▸
       at 23 2 [] (wl0379 (lit c4)) ▸
       at 19 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 17 2 (X1 ∷ Toff204 ∷ []) (wp0155 c4) ▸ done

  b42 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ Toff204 ∷ Sb2-0-41-3 ∷ X1 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b42 = at 18 2 (Sb2-0-41-3 ∷ Toff204 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩-at0210243143 c4) ▸
       at 19 2 (X1 ∷ Toff204 ∷ []) (wp0155 c4) ▸
       at 18 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 19 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 22 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 25 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 28 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 16 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸ done

  b43 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ CS12 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b43 = at 22 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 22 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 23 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 26 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 29 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 20 4 (X1 ∷ Toff201 ∷ X1 ∷ CS12 ∷ []) (wl0442 (lit c4)) ▸
       at 23 4 (X1 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ []) (wl0441 (lit c4)) ▸
       at 26 4 (X1 ∷ Toff201 ∷ X1 ∷ CS12 ∷ []) (wl0442 (lit c4)) ▸ done

  b44 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ CS12 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X1 ∷ Bx2-0134 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b44 = at 29 4 (X1 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ []) (wl0441 (lit c4)) ▸
       at 22 2 [] (wl0379 (lit c4)) ▸
       at 23 2 [] (wl0379 (lit c4)) ▸
       at 24 2 [] (wl0379 (lit c4)) ▸
       at 21 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 21 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 21 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 21 1 (Bx2-0134 ∷ []) (lem-sym34-at0210213443 c4) ▸ done

  b45 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X1 ∷ Bx2-0134 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b45 = at 21 1 (Bx2-1034 ∷ []) (lem-sym12-at021021 c4) ▸
       at 21 1 (Bx2-1304 ∷ []) (lem-sym23-at0220 c4) ▸
       at 21 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-beta-T-at022330 c4) ▸
       at 22 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 25 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 28 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 19 4 (X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ []) (wl0464 (lit c4)) ▸
       at 24 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4) ▸ done

  b46 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ X1 ∷ CS02 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b46 = at 25 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 28 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 31 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 34 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 22 4 (X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ []) (wl0463 (lit c4)) ▸
       at 25 4 (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) (wp0168 c4) ▸
       at 28 4 (X1 ∷ CS24⁻ ∷ X1 ∷ CX13 ∷ []) (wl0462 (lit c4)) ▸
       at 31 4 (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) (wp0168 c4) ▸ done

  b47 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ X1 ∷ CS02 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b47 = at 34 4 (X1 ∷ CS02 ∷ X1 ∷ CX13 ∷ []) (wl0461 (lit c4)) ▸
       at 24 2 [] (wl0379 (lit c4)) ▸
       at 25 2 [] (wl0379 (lit c4)) ▸
       at 26 2 [] (wl0379 (lit c4)) ▸
       at 27 2 [] (wl0379 (lit c4)) ▸
       at 23 5 (CCZ024 ∷ []) (sym (wp0143 c4)) ▸
       at 25 4 (X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ []) (wl0464 (lit c4)) ▸
       at 30 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4) ▸ done

  b48 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ X1 ∷ CS02 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b48 = at 31 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 34 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 37 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 40 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 28 4 (X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ []) (wl0463 (lit c4)) ▸
       at 31 4 (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) (wp0168 c4) ▸
       at 34 4 (X1 ∷ CS24⁻ ∷ X1 ∷ CX13 ∷ []) (wl0462 (lit c4)) ▸
       at 37 4 (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) (wp0168 c4) ▸ done

  b49 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ X1 ∷ CS02 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b49 = at 40 4 (X1 ∷ CS02 ∷ X1 ∷ CX13 ∷ []) (wl0461 (lit c4)) ▸
       at 30 2 [] (wl0379 (lit c4)) ▸
       at 31 2 [] (wl0379 (lit c4)) ▸
       at 32 2 [] (wl0379 (lit c4)) ▸
       at 33 2 [] (wl0379 (lit c4)) ▸
       at 29 5 (CCZ024 ∷ []) (sym (wp0143 c4)) ▸
       at 21 2 [] (wl0379 (lit c4)) ▸
       at 22 2 [] (wl0379 (lit c4)) ▸ done

  b50 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ X1 ∷ Bx2-0413 ∷ CS23⁻ ∷ X1 ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b50 = at 23 2 [] (wl0379 (lit c4)) ▸
       at 20 4 (Bx2-1304 ∷ []) (sym (lem-beta-T-at022330 c4)) ▸
       at 20 1 (Bx2-1034 ∷ []) (lem-sym23-at022330 c4) ▸
       at 20 1 (Bx2-1043 ∷ []) (lem-sym34-at0220 c4) ▸
       at 20 1 (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4) ▸
       at 20 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 18 2 (X1 ∷ CS23⁻ ∷ []) (wl0440 (lit c4)) ▸
       at 19 2 (Bx2-0413 ∷ CS23⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2340⟩-at0312203441 c4) ▸ done

  b51 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ X1 ∷ Bx2-0413 ∷ CS23⁻ ∷ X1 ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ CCZ024 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b51 = at 20 2 (X1 ∷ CS23⁻ ∷ []) (wl0440 (lit c4)) ▸
       at 19 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 19 1 (Bx2-0134 ∷ []) (lem-sym34-at0210213443 c4) ▸
       at 19 1 (Bx2-1034 ∷ []) (lem-sym12-at021021 c4) ▸
       at 19 1 (Bx2-1304 ∷ []) (lem-sym23-at0220 c4) ▸
       at 19 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-beta-T-at022330 c4) ▸
       at 20 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 23 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b52 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ CCZ024 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b52 = at 26 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 17 4 (X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ []) (wl0464 (lit c4)) ▸
       at 22 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4) ▸
       at 23 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 26 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 29 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 32 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 20 4 (X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ []) (wl0463 (lit c4)) ▸ done

  b53 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ X1 ∷ CX13 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b53 = at 23 4 (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) (wp0168 c4) ▸
       at 26 4 (X1 ∷ CS24⁻ ∷ X1 ∷ CX13 ∷ []) (wl0462 (lit c4)) ▸
       at 29 4 (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) (wp0168 c4) ▸
       at 32 4 (X1 ∷ CS02 ∷ X1 ∷ CX13 ∷ []) (wl0461 (lit c4)) ▸
       at 22 2 [] (wl0379 (lit c4)) ▸
       at 23 2 [] (wl0379 (lit c4)) ▸
       at 24 2 [] (wl0379 (lit c4)) ▸
       at 25 2 [] (wl0379 (lit c4)) ▸ done

  b54 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ X1 ∷ CX13 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b54 = at 21 5 (CCZ024 ∷ []) (sym (wp0143 c4)) ▸
       at 23 4 (X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ []) (wl0464 (lit c4)) ▸
       at 28 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4) ▸
       at 29 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 32 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 35 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 38 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 26 4 (X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ []) (wl0463 (lit c4)) ▸ done

  b55 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ X1 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b55 = at 29 4 (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) (wp0168 c4) ▸
       at 32 4 (X1 ∷ CS24⁻ ∷ X1 ∷ CX13 ∷ []) (wl0462 (lit c4)) ▸
       at 35 4 (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) (wp0168 c4) ▸
       at 38 4 (X1 ∷ CS02 ∷ X1 ∷ CX13 ∷ []) (wl0461 (lit c4)) ▸
       at 28 2 [] (wl0379 (lit c4)) ▸
       at 29 2 [] (wl0379 (lit c4)) ▸
       at 30 2 [] (wl0379 (lit c4)) ▸
       at 31 2 [] (wl0379 (lit c4)) ▸ done

  b56 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ X1 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Bx2-0143 ∷ X1 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b56 = at 27 5 (CCZ024 ∷ []) (sym (wp0143 c4)) ▸
       at 19 2 [] (wl0379 (lit c4)) ▸
       at 20 2 [] (wl0379 (lit c4)) ▸
       at 21 2 [] (wl0379 (lit c4)) ▸
       at 18 4 (Bx2-1304 ∷ []) (sym (lem-beta-T-at022330 c4)) ▸
       at 18 1 (Bx2-1034 ∷ []) (lem-sym23-at022330 c4) ▸
       at 18 1 (Bx2-1043 ∷ []) (lem-sym34-at0220 c4) ▸
       at 18 1 (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4) ▸ done

  b57 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Bx2-0143 ∷ X1 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ CCZ123 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b57 = at 18 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 16 2 (X1 ∷ CS23 ∷ []) (wl0434 (lit c4)) ▸
       at 17 2 (Bx2-0413 ∷ CS23 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2340⟩-at0312203441 c4) ▸
       at 18 2 (X1 ∷ CS23 ∷ []) (wl0434 (lit c4)) ▸
       at 19 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 19 4 (X1 ∷ Toff314 ∷ X1 ∷ CCZ123 ∷ []) (wl0443 (lit c4)) ▸
       at 24 1 (CS03 ∷ []) (refl) ▸
       at 22 4 (X1 ∷ CS03 ∷ X1 ∷ CCZ123 ∷ []) (wl0445 (lit c4)) ▸ done

  b58 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ CCZ123 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b58 = at 23 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 25 4 (X1 ∷ Toff314 ∷ X1 ∷ CCZ123 ∷ []) (wl0443 (lit c4)) ▸
       at 30 1 (CS03⁻ ∷ []) (refl) ▸
       at 28 4 (X1 ∷ CS03⁻ ∷ X1 ∷ CCZ123 ∷ []) (wl0444 (lit c4)) ▸
       at 29 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 18 2 [] (wl0379 (lit c4)) ▸
       at 19 2 [] (wl0379 (lit c4)) ▸
       at 20 2 [] (wl0379 (lit c4)) ▸ done

  b59 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ K3 ∷ CCZ134 ∷ K3⁻ ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Bx⁻2-0413 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b59 = at 21 2 [] (wl0379 (lit c4)) ▸
       at 17 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 15 2 (X1 ∷ Toff204 ∷ []) (wp0155 c4) ▸
       at 16 2 (Sb2-0-41-3 ∷ Toff204 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩-at0210243143 c4) ▸
       at 17 2 (X1 ∷ Toff204 ∷ []) (wp0155 c4) ▸
       at 18 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 18 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸
       at 14 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (sym (wl0402 (lit c4))) ▸ done

  b60 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ K3 ∷ CCZ134 ∷ K3⁻ ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Bx⁻2-0413 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Bx⁻2-0413 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b60 = at 16 2 (X1 ∷ K3⁻ ∷ []) (wl0403 (lit c4)) ▸
       at 17 2 (Sb2-0-41-3 ∷ K3⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4) ▸
       at 18 2 (X1 ∷ K3⁻ ∷ []) (wl0403 (lit c4)) ▸
       at 15 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4)) ▸
       at 19 2 (X1 ∷ CS34 ∷ []) (wl0405 (lit c4)) ▸
       at 20 2 (Sb2-0-41-3 ∷ CS34 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 c4) ▸
       at 21 2 (X1 ∷ CS34 ∷ []) (wl0405 (lit c4)) ▸
       at 20 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b61 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Bx⁻2-0413 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Bx⁻2-0413 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b61 = at 21 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 24 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 27 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 30 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 20 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸
       at 20 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 20 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 21 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b62 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Bx⁻2-0413 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Bx⁻2-0413 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b62 = at 24 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 27 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 18 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸
       at 19 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸ done


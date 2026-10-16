{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D008 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0379 ; wl0388 ; wl0389 ; wl0390 ; wl0391 ; wl0392 ; wl0393 ; wl0394 ; wl0395 ; wl0396 ; wl0397 ; wl0398 ; wl0399 ; wl0400 ; wl0401 ; wl0402 ; wl0403 ; wl0404 ; wl0405 ; wl0406 ; wl0407 ; wl0408 ; wl0409 ; wl0410 ; wl0411 ; wl0412 ; wl0413 ; wl0414 ; wl0415 ; wl0416 ; wl0417 ; wl0418 ; wl0419 ; wp0024 ; wp0060 ; wp0134 ; wp0135 ; wp0136 ; wp0137 ; wp0138 ; wp0139 ; wp0140 ; wp0141 ; wp0142 ; wp0143 ; wp0144)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-X1-beta-at02203443 ; lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 ; lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 ; lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 ; lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0312203441 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0210243143 ; lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 ; lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 ; lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-sym12-at0210213443 ; lem-sym12-at02203443 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-CX41-TOFF203)
-- F1 CS-K0 [rhs shape] part2: 500 steps
lem-F1-CS-K0-rhs-shape-part2 : Ws → ⟪ (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K0-rhs-shape-part2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (run b62))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b0 = at 27 4 (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) (wl0407 (lit c4)) ▸
       at 26 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸
       at 27 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸
       at 28 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸
       at 29 6 (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wl0408 (lit c4)) ▸
       at 34 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸
       at 35 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸
       at 36 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸ done

  b1 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b1 = at 33 4 (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) (wl0407 (lit c4)) ▸
       at 32 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸
       at 33 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸
       at 34 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸
       at 35 6 (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wl0408 (lit c4)) ▸
       at 28 2 [] (wl0379 (lit c4)) ▸
       at 29 2 [] (wl0379 (lit c4)) ▸
       at 30 2 [] (wl0379 (lit c4)) ▸ done

  b2 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b2 = at 27 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸
       at 27 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸
       at 27 1 (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4) ▸
       at 36 1 (CS03 ∷ []) (refl) ▸
       at 29 12 (X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0140 c4) ▸
       at 33 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 42 1 (CS03⁻ ∷ []) (refl) ▸
       at 38 6 (X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0141 c4) ▸ done

  b3 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b3 = at 39 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 28 2 [] (wl0379 (lit c4)) ▸
       at 29 2 [] (wl0379 (lit c4)) ▸
       at 30 2 [] (wl0379 (lit c4)) ▸
       at 31 2 [] (wl0379 (lit c4)) ▸
       at 27 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 27 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 28 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b4 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ K2 ∷ CCZ024 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b4 = at 31 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 34 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 37 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 27 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 28 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 31 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 34 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 27 1 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (sym (wp0142 c4)) ▸ done

  b5 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ K2 ∷ CCZ024 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ K2 ∷ X1 ∷ CS13 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ X1 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b5 = at 28 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 31 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 25 4 (X1 ∷ K2 ∷ X1 ∷ CS13 ∷ []) (wl0409 (lit c4)) ▸
       at 30 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4) ▸
       at 31 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 34 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 37 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 40 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b6 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ K2 ∷ X1 ∷ CS13 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ X1 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ K2 ∷ X1 ∷ X1 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CS13 ∷ X1 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b6 = at 28 4 (X1 ∷ CS24 ∷ X1 ∷ CS13 ∷ []) (wl0410 (lit c4)) ▸
       at 31 4 (X1 ∷ CX04 ∷ X1 ∷ CS13 ∷ []) (wp0144 c4) ▸
       at 34 4 (X1 ∷ CS24⁻ ∷ X1 ∷ CS13 ∷ []) (wl0411 (lit c4)) ▸
       at 37 4 (X1 ∷ CX04 ∷ X1 ∷ CS13 ∷ []) (wp0144 c4) ▸
       at 40 4 (X1 ∷ CS02 ∷ X1 ∷ CS13 ∷ []) (wl0412 (lit c4)) ▸
       at 30 2 [] (wl0379 (lit c4)) ▸
       at 31 2 [] (wl0379 (lit c4)) ▸
       at 32 2 [] (wl0379 (lit c4)) ▸ done

  b7 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ K2 ∷ X1 ∷ X1 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CS13 ∷ X1 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS13 ∷ X1 ∷ K2 ∷ CCZ024 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b7 = at 33 2 [] (wl0379 (lit c4)) ▸
       at 29 5 (CCZ024 ∷ []) (sym (wp0143 c4)) ▸
       at 31 4 (X1 ∷ K2⁻ ∷ X1 ∷ CS13 ∷ []) (wl0413 (lit c4)) ▸
       at 27 2 [] (wl0379 (lit c4)) ▸
       at 28 2 [] (wl0379 (lit c4)) ▸
       at 26 3 (Toff204 ∷ []) (wp0142 c4) ▸
       at 28 4 (X1 ∷ CCZ123 ∷ X1 ∷ CS13 ∷ []) (wl0414 (lit c4)) ▸
       at 33 1 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (sym (wp0142 c4)) ▸ done

  b8 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS13 ∷ X1 ∷ K2 ∷ CCZ024 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ K2 ∷ X1 ∷ CS13 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ X1 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b8 = at 34 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 37 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 31 4 (X1 ∷ K2 ∷ X1 ∷ CS13 ∷ []) (wl0409 (lit c4)) ▸
       at 36 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4) ▸
       at 37 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 40 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 43 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 46 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b9 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ K2 ∷ X1 ∷ CS13 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ X1 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ K2 ∷ X1 ∷ X1 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CS13 ∷ X1 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b9 = at 34 4 (X1 ∷ CS24 ∷ X1 ∷ CS13 ∷ []) (wl0410 (lit c4)) ▸
       at 37 4 (X1 ∷ CX04 ∷ X1 ∷ CS13 ∷ []) (wp0144 c4) ▸
       at 40 4 (X1 ∷ CS24⁻ ∷ X1 ∷ CS13 ∷ []) (wl0411 (lit c4)) ▸
       at 43 4 (X1 ∷ CX04 ∷ X1 ∷ CS13 ∷ []) (wp0144 c4) ▸
       at 46 4 (X1 ∷ CS02 ∷ X1 ∷ CS13 ∷ []) (wl0412 (lit c4)) ▸
       at 36 2 [] (wl0379 (lit c4)) ▸
       at 37 2 [] (wl0379 (lit c4)) ▸
       at 38 2 [] (wl0379 (lit c4)) ▸ done

  b10 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ K2 ∷ X1 ∷ X1 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CS13 ∷ X1 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b10 = at 39 2 [] (wl0379 (lit c4)) ▸
       at 35 5 (CCZ024 ∷ []) (sym (wp0143 c4)) ▸
       at 37 4 (X1 ∷ K2⁻ ∷ X1 ∷ CS13 ∷ []) (wl0413 (lit c4)) ▸
       at 33 2 [] (wl0379 (lit c4)) ▸
       at 34 2 [] (wl0379 (lit c4)) ▸
       at 32 3 (Toff204 ∷ []) (wp0142 c4) ▸
       at 34 4 (X1 ∷ CCZ123 ∷ X1 ∷ CS13 ∷ []) (wl0414 (lit c4)) ▸
       at 27 2 [] (wl0379 (lit c4)) ▸ done

  b11 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b11 = at 28 2 [] (wl0379 (lit c4)) ▸
       at 29 2 [] (wl0379 (lit c4)) ▸
       at 26 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 28 4 (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (wl0415 (lit c4)) ▸
       at 33 1 (CS03 ∷ []) (refl) ▸
       at 31 4 (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) (wl0416 (lit c4)) ▸
       at 32 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 34 4 (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (wl0415 (lit c4)) ▸ done

  b12 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b12 = at 39 1 (CS03⁻ ∷ []) (refl) ▸
       at 37 4 (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) (wl0417 (lit c4)) ▸
       at 38 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 27 2 [] (wl0379 (lit c4)) ▸
       at 28 2 [] (wl0379 (lit c4)) ▸
       at 29 2 [] (wl0379 (lit c4)) ▸
       at 30 2 [] (wl0379 (lit c4)) ▸
       at 26 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

  b13 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ X1 ∷ Bx2-1043 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b13 = at 28 5 (CCZ134 ∷ []) (sym (wl0404 (lit c4))) ▸
       at 24 2 (X1 ∷ K3 ∷ []) (wl0418 (lit c4)) ▸
       at 25 2 (Sb2-0-41-3 ∷ K3 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4) ▸
       at 26 2 (X1 ∷ K3 ∷ []) (wl0418 (lit c4)) ▸
       at 27 3 (Toff314 ∷ []) (wl0402 (lit c4)) ▸
       at 23 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 25 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 25 1 (Bx2-1043 ∷ []) (lem-sym12-at0210213443 c4) ▸ done

  b14 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ X1 ∷ Bx2-1043 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ CCZ034 ∷ Sb2-0-41-3 ∷ X1 ∷ CCZ034 ∷ Bx2-1043 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b14 = at 24 3 (CCZ034 ∷ Bx2-1043 ∷ []) (lem-X1-beta-at02203443 c4) ▸
       at 25 1 (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4) ▸
       at 25 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 25 2 (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 c4) ▸
       at 26 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 28 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 28 1 (Bx2-1043 ∷ []) (lem-sym12-at0210213443 c4) ▸
       at 27 3 (CCZ034 ∷ Bx2-1043 ∷ []) (lem-X1-beta-at02203443 c4) ▸ done

  b15 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ CCZ034 ∷ Sb2-0-41-3 ∷ X1 ∷ CCZ034 ∷ Bx2-1043 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b15 = at 28 1 (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4) ▸
       at 28 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 23 2 (CCZ034 ∷ X1 ∷ []) (sym (wp0060 c4)) ▸
       at 26 2 (CCZ034 ∷ X1 ∷ []) (sym (wp0060 c4)) ▸
       at 25 2 (CCZ034 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0210243143 c4) ▸
       at 24 2 (CCZ034 ∷ X1 ∷ []) (sym (wp0060 c4)) ▸
       at 23 2 [] (wp0024 c4) ▸
       at 26 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

  b16 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b16 = at 22 1 (ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ []) (wl0388 (lit c4)) ▸
       at 30 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 31 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 34 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 37 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 40 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 30 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 31 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b17 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b17 = at 34 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 37 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 28 4 (X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ []) (wp0134 c4) ▸
       at 31 4 (X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ []) (wl0389 (lit c4)) ▸
       at 34 4 (X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ []) (wp0134 c4) ▸
       at 37 4 (X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ []) (wl0389 (lit c4)) ▸
       at 30 2 [] (wl0379 (lit c4)) ▸
       at 31 2 [] (wl0379 (lit c4)) ▸ done

  b18 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b18 = at 32 2 [] (wl0379 (lit c4)) ▸
       at 29 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 31 4 (X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ []) (wp0135 c4) ▸
       at 36 1 (CS03 ∷ []) (refl) ▸
       at 34 4 (X1 ∷ CS03 ∷ X1 ∷ CS01 ∷ []) (wl0390 (lit c4)) ▸
       at 35 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 37 4 (X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ []) (wp0135 c4) ▸
       at 42 1 (CS03⁻ ∷ []) (refl) ▸ done

  b19 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b19 = at 40 4 (X1 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 41 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 30 2 [] (wl0379 (lit c4)) ▸
       at 31 2 [] (wl0379 (lit c4)) ▸
       at 32 2 [] (wl0379 (lit c4)) ▸
       at 33 2 [] (wl0379 (lit c4)) ▸
       at 29 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 29 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b20 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b20 = at 30 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 33 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 36 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 39 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 29 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 29 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 30 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 33 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b21 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ X1 ∷ CS23 ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X1 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b21 = at 36 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 25 6 (X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) (wl0392 (lit c4)) ▸
       at 30 2 (X1 ∷ K0 ∷ []) (c₁ (K) (X)) ▸
       at 31 2 (CCZ234 ∷ K0 ∷ []) (c₁ (K) (CCZ ↑)) ▸
       at 32 2 (X1 ∷ K0 ∷ []) (c₁ (K) (X)) ▸
       at 31 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4)) ▸
       at 32 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 35 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b22 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ X1 ∷ CS23 ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X1 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ X1 ∷ CS23 ∷ CX43 ∷ X1 ∷ X1 ∷ CS23⁻ ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b22 = at 38 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 41 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 29 4 (X1 ∷ CS23 ∷ X1 ∷ CS01 ∷ []) (wl0394 (lit c4)) ▸
       at 32 4 (X1 ∷ CX43 ∷ X1 ∷ CS01 ∷ []) (wl0395 (lit c4)) ▸
       at 35 4 (X1 ∷ CS23⁻ ∷ X1 ∷ CS01 ∷ []) (wl0396 (lit c4)) ▸
       at 38 4 (X1 ∷ CX43 ∷ X1 ∷ CS01 ∷ []) (wl0395 (lit c4)) ▸
       at 41 4 (X1 ∷ CS24 ∷ X1 ∷ CS01 ∷ []) (wp0136 c4) ▸
       at 31 2 [] (wl0379 (lit c4)) ▸ done

  b23 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ X1 ∷ CS23 ∷ CX43 ∷ X1 ∷ X1 ∷ CS23⁻ ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b23 = at 32 2 [] (wl0379 (lit c4)) ▸
       at 33 2 [] (wl0379 (lit c4)) ▸
       at 34 2 [] (wl0379 (lit c4)) ▸
       at 30 5 (CCZ234 ∷ []) (sym (wl0393 (lit c4))) ▸
       at 28 2 (X1 ∷ K0 ∷ []) (c₁ (K) (X)) ▸
       at 29 2 (CCZ234 ∷ K0 ∷ []) (c₁ (K) (CCZ ↑)) ▸
       at 30 2 (X1 ∷ K0 ∷ []) (c₁ (K) (X)) ▸
       at 31 6 (X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) (wl0392 (lit c4)) ▸ done

  b24 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ X1 ∷ CS23 ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS23⁻ ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ K0 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b24 = at 36 2 (X1 ∷ K0 ∷ []) (c₁ (K) (X)) ▸
       at 37 2 (CCZ234 ∷ K0 ∷ []) (c₁ (K) (CCZ ↑)) ▸
       at 38 2 (X1 ∷ K0 ∷ []) (c₁ (K) (X)) ▸
       at 37 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4)) ▸
       at 38 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 41 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 44 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 47 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b25 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ CS01 ∷ X1 ∷ CS23 ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS23⁻ ∷ X1 ∷ X1 ∷ CX43 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ K0 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ X1 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b25 = at 35 4 (X1 ∷ CS23 ∷ X1 ∷ CS01 ∷ []) (wl0394 (lit c4)) ▸
       at 38 4 (X1 ∷ CX43 ∷ X1 ∷ CS01 ∷ []) (wl0395 (lit c4)) ▸
       at 41 4 (X1 ∷ CS23⁻ ∷ X1 ∷ CS01 ∷ []) (wl0396 (lit c4)) ▸
       at 44 4 (X1 ∷ CX43 ∷ X1 ∷ CS01 ∷ []) (wl0395 (lit c4)) ▸
       at 47 4 (X1 ∷ CS24 ∷ X1 ∷ CS01 ∷ []) (wp0136 c4) ▸
       at 37 2 [] (wl0379 (lit c4)) ▸
       at 38 2 [] (wl0379 (lit c4)) ▸
       at 39 2 [] (wl0379 (lit c4)) ▸ done

  b26 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ K0 ∷ X1 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b26 = at 40 2 [] (wl0379 (lit c4)) ▸
       at 36 5 (CCZ234 ∷ []) (sym (wl0393 (lit c4))) ▸
       at 34 2 (X1 ∷ K0 ∷ []) (c₁ (K) (X)) ▸
       at 35 2 (CCZ234 ∷ K0 ∷ []) (c₁ (K) (CCZ ↑)) ▸
       at 36 2 (X1 ∷ K0 ∷ []) (c₁ (K) (X)) ▸
       at 27 2 [] (wl0379 (lit c4)) ▸
       at 28 2 [] (wl0379 (lit c4)) ▸
       at 29 2 [] (wl0379 (lit c4)) ▸ done

  b27 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b27 = at 26 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 26 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 28 6 (X1 ∷ Toff314 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) (wp0137 c4) ▸
       at 35 1 (CS03 ∷ []) (refl) ▸
       at 41 1 (CS03⁻ ∷ []) (refl) ▸
       at 31 12 (X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) (wp0138 c4) ▸
       at 32 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 38 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b28 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b28 = at 27 2 [] (wl0379 (lit c4)) ▸
       at 28 2 [] (wl0379 (lit c4)) ▸
       at 29 2 [] (wl0379 (lit c4)) ▸
       at 30 2 [] (wl0379 (lit c4)) ▸
       at 26 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 26 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 27 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 30 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b29 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b29 = at 33 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 36 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 26 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 27 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 30 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 33 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 24 4 (X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ []) (wp0134 c4) ▸
       at 27 4 (X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ []) (wl0389 (lit c4)) ▸ done

  b30 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b30 = at 30 4 (X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ []) (wp0134 c4) ▸
       at 33 4 (X1 ∷ CCZ123 ∷ X1 ∷ CS01 ∷ []) (wl0389 (lit c4)) ▸
       at 26 2 [] (wl0379 (lit c4)) ▸
       at 27 2 [] (wl0379 (lit c4)) ▸
       at 28 2 [] (wl0379 (lit c4)) ▸
       at 25 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 27 4 (X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ []) (wp0135 c4) ▸
       at 32 1 (CS03 ∷ []) (refl) ▸ done

  b31 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b31 = at 30 4 (X1 ∷ CS03 ∷ X1 ∷ CS01 ∷ []) (wl0390 (lit c4)) ▸
       at 31 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 33 4 (X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ []) (wp0135 c4) ▸
       at 38 1 (CS03⁻ ∷ []) (refl) ▸
       at 36 4 (X1 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 37 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 26 2 [] (wl0379 (lit c4)) ▸
       at 27 2 [] (wl0379 (lit c4)) ▸ done

  b32 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b32 = at 28 2 [] (wl0379 (lit c4)) ▸
       at 29 2 [] (wl0379 (lit c4)) ▸
       at 25 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 25 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 26 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 29 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 32 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 35 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b33 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ S1⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ S1⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b33 = at 25 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 26 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 29 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 32 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 23 4 (X1 ∷ Toff204 ∷ X1 ∷ S1⁻ ∷ []) (wp0139 c4) ▸
       at 26 4 (X1 ∷ CCZ123 ∷ X1 ∷ S1⁻ ∷ []) (wl0397 (lit c4)) ▸
       at 29 4 (X1 ∷ Toff204 ∷ X1 ∷ S1⁻ ∷ []) (wp0139 c4) ▸
       at 32 4 (X1 ∷ CCZ123 ∷ X1 ∷ S1⁻ ∷ []) (wl0397 (lit c4)) ▸ done

  b34 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ S1⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b34 = at 25 2 [] (wl0379 (lit c4)) ▸
       at 26 2 [] (wl0379 (lit c4)) ▸
       at 27 2 [] (wl0379 (lit c4)) ▸
       at 24 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 26 4 (X1 ∷ Toff314 ∷ X1 ∷ S1⁻ ∷ []) (wl0398 (lit c4)) ▸
       at 31 1 (CS03 ∷ []) (refl) ▸
       at 29 4 (X1 ∷ CS03 ∷ X1 ∷ S1⁻ ∷ []) (wl0399 (lit c4)) ▸
       at 30 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b35 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b35 = at 32 4 (X1 ∷ Toff314 ∷ X1 ∷ S1⁻ ∷ []) (wl0398 (lit c4)) ▸
       at 37 1 (CS03⁻ ∷ []) (refl) ▸
       at 35 4 (X1 ∷ CS03⁻ ∷ X1 ∷ S1⁻ ∷ []) (wl0400 (lit c4)) ▸
       at 36 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 25 2 [] (wl0379 (lit c4)) ▸
       at 26 2 [] (wl0379 (lit c4)) ▸
       at 27 2 [] (wl0379 (lit c4)) ▸
       at 28 2 [] (wl0379 (lit c4)) ▸ done

  b36 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ ι ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X1 ∷ CS03⁻ ∷ Sb2-0-41-3 ∷ X1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b36 = at 24 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 22 2 (X1 ∷ ι ∷ []) (sym zc) ▸
       at 23 2 (Sb2-0-41-3 ∷ ι ∷ []) (sym zc) ▸
       at 24 2 (X1 ∷ ι ∷ []) (sym zc) ▸
       at 25 7 (CK10 ∷ []) (sym (wl0388 (lit c4))) ▸
       at 21 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 25 1 (CS03⁻ ∷ []) (refl) ▸
       at 25 2 (X1 ∷ CS03⁻ ∷ []) (wl0401 (lit c4)) ▸ done

  b37 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X1 ∷ CS03⁻ ∷ Sb2-0-41-3 ∷ X1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CCZ134 ∷ X1 ∷ Sb2-0-41-3 ∷ K3⁻ ∷ X1 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b37 = at 26 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 26 2 (Sb2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 c4) ▸
       at 27 1 (CS03⁻ ∷ []) (refl) ▸
       at 27 2 (X1 ∷ CS03⁻ ∷ []) (wl0401 (lit c4)) ▸
       at 28 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 24 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (sym (wl0402 (lit c4))) ▸
       at 26 2 (X1 ∷ K3⁻ ∷ []) (wl0403 (lit c4)) ▸
       at 27 2 (Sb2-0-41-3 ∷ K3⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4) ▸ done

  b38 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CCZ134 ∷ X1 ∷ Sb2-0-41-3 ∷ K3⁻ ∷ X1 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b38 = at 28 2 (X1 ∷ K3⁻ ∷ []) (wl0403 (lit c4)) ▸
       at 25 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4)) ▸
       at 29 2 (X1 ∷ CS34 ∷ []) (wl0405 (lit c4)) ▸
       at 30 2 (Sb2-0-41-3 ∷ CS34 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 c4) ▸
       at 31 2 (X1 ∷ CS34 ∷ []) (wl0405 (lit c4)) ▸
       at 30 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 31 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 34 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b39 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b39 = at 37 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 40 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 30 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸
       at 30 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 30 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 31 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 34 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 37 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b40 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b40 = at 28 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸
       at 29 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸
       at 30 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸
       at 27 4 (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) (wl0407 (lit c4)) ▸
       at 26 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸
       at 27 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸
       at 28 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸
       at 29 6 (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wl0408 (lit c4)) ▸ done

  b41 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b41 = at 34 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸
       at 35 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸
       at 36 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸
       at 33 4 (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) (wl0407 (lit c4)) ▸
       at 32 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸
       at 33 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸
       at 34 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸
       at 35 6 (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wl0408 (lit c4)) ▸ done

  b42 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b42 = at 28 2 [] (wl0379 (lit c4)) ▸
       at 29 2 [] (wl0379 (lit c4)) ▸
       at 30 2 [] (wl0379 (lit c4)) ▸
       at 27 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸
       at 27 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸
       at 27 1 (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4) ▸
       at 36 1 (CS03 ∷ []) (refl) ▸
       at 29 12 (X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0140 c4) ▸ done

  b43 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b43 = at 33 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 42 1 (CS03⁻ ∷ []) (refl) ▸
       at 38 6 (X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0141 c4) ▸
       at 39 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 28 2 [] (wl0379 (lit c4)) ▸
       at 29 2 [] (wl0379 (lit c4)) ▸
       at 30 2 [] (wl0379 (lit c4)) ▸
       at 31 2 [] (wl0379 (lit c4)) ▸ done

  b44 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b44 = at 27 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 27 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 28 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 31 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 34 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 37 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 27 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 28 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b45 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ K2 ∷ X1 ∷ CS13 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ X1 ∷ X1 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b45 = at 31 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 34 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 27 1 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (sym (wp0142 c4)) ▸
       at 28 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 31 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 25 4 (X1 ∷ K2 ∷ X1 ∷ CS13 ∷ []) (wl0409 (lit c4)) ▸
       at 30 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4) ▸
       at 31 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b46 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ K2 ∷ X1 ∷ CS13 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ X1 ∷ X1 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ K2 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CS13 ∷ X1 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b46 = at 34 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 37 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 40 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 28 4 (X1 ∷ CS24 ∷ X1 ∷ CS13 ∷ []) (wl0410 (lit c4)) ▸
       at 31 4 (X1 ∷ CX04 ∷ X1 ∷ CS13 ∷ []) (wp0144 c4) ▸
       at 34 4 (X1 ∷ CS24⁻ ∷ X1 ∷ CS13 ∷ []) (wl0411 (lit c4)) ▸
       at 37 4 (X1 ∷ CX04 ∷ X1 ∷ CS13 ∷ []) (wp0144 c4) ▸
       at 40 4 (X1 ∷ CS02 ∷ X1 ∷ CS13 ∷ []) (wl0412 (lit c4)) ▸ done

  b47 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ K2 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CS13 ∷ X1 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ K2 ∷ CCZ024 ∷ K2⁻ ∷ X1 ∷ CS13 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b47 = at 30 2 [] (wl0379 (lit c4)) ▸
       at 31 2 [] (wl0379 (lit c4)) ▸
       at 32 2 [] (wl0379 (lit c4)) ▸
       at 33 2 [] (wl0379 (lit c4)) ▸
       at 29 5 (CCZ024 ∷ []) (sym (wp0143 c4)) ▸
       at 31 4 (X1 ∷ K2⁻ ∷ X1 ∷ CS13 ∷ []) (wl0413 (lit c4)) ▸
       at 27 2 [] (wl0379 (lit c4)) ▸
       at 28 2 [] (wl0379 (lit c4)) ▸ done

  b48 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ K2 ∷ CCZ024 ∷ K2⁻ ∷ X1 ∷ CS13 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ K2 ∷ X1 ∷ CS13 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ X1 ∷ X1 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b48 = at 26 3 (Toff204 ∷ []) (wp0142 c4) ▸
       at 28 4 (X1 ∷ CCZ123 ∷ X1 ∷ CS13 ∷ []) (wl0414 (lit c4)) ▸
       at 33 1 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (sym (wp0142 c4)) ▸
       at 34 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 37 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 31 4 (X1 ∷ K2 ∷ X1 ∷ CS13 ∷ []) (wl0409 (lit c4)) ▸
       at 36 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4) ▸
       at 37 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b49 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ K2 ∷ X1 ∷ CS13 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ X1 ∷ X1 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ K2 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CS13 ∷ X1 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b49 = at 40 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 43 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 46 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 34 4 (X1 ∷ CS24 ∷ X1 ∷ CS13 ∷ []) (wl0410 (lit c4)) ▸
       at 37 4 (X1 ∷ CX04 ∷ X1 ∷ CS13 ∷ []) (wp0144 c4) ▸
       at 40 4 (X1 ∷ CS24⁻ ∷ X1 ∷ CS13 ∷ []) (wl0411 (lit c4)) ▸
       at 43 4 (X1 ∷ CX04 ∷ X1 ∷ CS13 ∷ []) (wp0144 c4) ▸
       at 46 4 (X1 ∷ CS02 ∷ X1 ∷ CS13 ∷ []) (wl0412 (lit c4)) ▸ done

  b50 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ K2 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CS13 ∷ X1 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ K2 ∷ CCZ024 ∷ K2⁻ ∷ X1 ∷ CS13 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b50 = at 36 2 [] (wl0379 (lit c4)) ▸
       at 37 2 [] (wl0379 (lit c4)) ▸
       at 38 2 [] (wl0379 (lit c4)) ▸
       at 39 2 [] (wl0379 (lit c4)) ▸
       at 35 5 (CCZ024 ∷ []) (sym (wp0143 c4)) ▸
       at 37 4 (X1 ∷ K2⁻ ∷ X1 ∷ CS13 ∷ []) (wl0413 (lit c4)) ▸
       at 33 2 [] (wl0379 (lit c4)) ▸
       at 34 2 [] (wl0379 (lit c4)) ▸ done

  b51 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ K2 ∷ CCZ024 ∷ K2⁻ ∷ X1 ∷ CS13 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b51 = at 32 3 (Toff204 ∷ []) (wp0142 c4) ▸
       at 34 4 (X1 ∷ CCZ123 ∷ X1 ∷ CS13 ∷ []) (wl0414 (lit c4)) ▸
       at 27 2 [] (wl0379 (lit c4)) ▸
       at 28 2 [] (wl0379 (lit c4)) ▸
       at 29 2 [] (wl0379 (lit c4)) ▸
       at 26 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 28 4 (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (wl0415 (lit c4)) ▸
       at 33 1 (CS03 ∷ []) (refl) ▸ done

  b52 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b52 = at 31 4 (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) (wl0416 (lit c4)) ▸
       at 32 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 34 4 (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (wl0415 (lit c4)) ▸
       at 39 1 (CS03⁻ ∷ []) (refl) ▸
       at 37 4 (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) (wl0417 (lit c4)) ▸
       at 38 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 27 2 [] (wl0379 (lit c4)) ▸
       at 28 2 [] (wl0379 (lit c4)) ▸ done

  b53 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b53 = at 29 2 [] (wl0379 (lit c4)) ▸
       at 30 2 [] (wl0379 (lit c4)) ▸
       at 26 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 28 5 (CCZ134 ∷ []) (sym (wl0404 (lit c4))) ▸
       at 24 2 (X1 ∷ K3 ∷ []) (wl0418 (lit c4)) ▸
       at 25 2 (Sb2-0-41-3 ∷ K3 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4) ▸
       at 26 2 (X1 ∷ K3 ∷ []) (wl0418 (lit c4)) ▸
       at 27 3 (Toff314 ∷ []) (wl0402 (lit c4)) ▸ done

  b54 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CCZ134 ∷ K3⁻ ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b54 = at 23 1 (CS03 ∷ []) (refl) ▸
       at 23 2 (X1 ∷ CS03 ∷ []) (wl0419 (lit c4)) ▸
       at 24 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 24 2 (Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 c4) ▸
       at 25 1 (CS03 ∷ []) (refl) ▸
       at 25 2 (X1 ∷ CS03 ∷ []) (wl0419 (lit c4)) ▸
       at 26 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 22 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (sym (wl0402 (lit c4))) ▸ done

  b55 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CCZ134 ∷ K3⁻ ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b55 = at 24 2 (X1 ∷ K3⁻ ∷ []) (wl0403 (lit c4)) ▸
       at 25 2 (Sb2-0-41-3 ∷ K3⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4) ▸
       at 26 2 (X1 ∷ K3⁻ ∷ []) (wl0403 (lit c4)) ▸
       at 23 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4)) ▸
       at 27 2 (X1 ∷ CS34 ∷ []) (wl0405 (lit c4)) ▸
       at 28 2 (Sb2-0-41-3 ∷ CS34 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 c4) ▸
       at 29 2 (X1 ∷ CS34 ∷ []) (wl0405 (lit c4)) ▸
       at 28 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b56 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b56 = at 29 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 32 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 35 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 38 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 28 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸
       at 28 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 28 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 29 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b57 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b57 = at 32 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 35 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 26 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸
       at 27 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸
       at 28 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸
       at 25 4 (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) (wl0407 (lit c4)) ▸
       at 24 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸
       at 25 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸ done

  b58 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b58 = at 26 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸
       at 27 6 (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wl0408 (lit c4)) ▸
       at 32 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸
       at 33 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸
       at 34 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸
       at 31 4 (X1 ∷ Toff203 ∷ X1 ∷ CS13⁻ ∷ []) (wl0407 (lit c4)) ▸
       at 30 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸
       at 31 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸ done

  b59 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b59 = at 32 2 (X1 ∷ CX41 ∷ []) (wl0406 (lit c4)) ▸
       at 33 6 (X1 ∷ CCZ124 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wl0408 (lit c4)) ▸
       at 26 2 [] (wl0379 (lit c4)) ▸
       at 27 2 [] (wl0379 (lit c4)) ▸
       at 28 2 [] (wl0379 (lit c4)) ▸
       at 25 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸
       at 25 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸
       at 25 1 (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4) ▸ done

  b60 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b60 = at 34 1 (CS03 ∷ []) (refl) ▸
       at 27 12 (X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0140 c4) ▸
       at 31 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 40 1 (CS03⁻ ∷ []) (refl) ▸
       at 36 6 (X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (wp0141 c4) ▸
       at 37 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 26 2 [] (wl0379 (lit c4)) ▸
       at 27 2 [] (wl0379 (lit c4)) ▸ done

  b61 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b61 = at 28 2 [] (wl0379 (lit c4)) ▸
       at 29 2 [] (wl0379 (lit c4)) ▸
       at 25 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 25 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 26 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 29 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 32 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 35 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b62 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b62 = at 25 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 26 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 29 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 32 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done


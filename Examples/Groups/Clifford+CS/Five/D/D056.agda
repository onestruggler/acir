{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D056 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0377 ; wl0378 ; wl0379 ; wl0380 ; wl0381 ; wl0382 ; wl0383 ; wl0384 ; wl0385 ; wl0387 ; wl0398 ; wl0399 ; wl0400 ; wl0402 ; wl0403 ; wl0404 ; wl0405 ; wl0406 ; wl0407 ; wl0408 ; wl0415 ; wl0416 ; wl0417 ; wl0418 ; wl0419 ; wl0452 ; wl0453 ; wl0454 ; wl0455 ; wp0024 ; wp0060 ; wp0127 ; wp0128 ; wp0129 ; wp0130 ; wp0133 ; wp0140 ; wp0141)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-X1-beta-at02203443 ; lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14233241 ; lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14233241 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 ; lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-sym12-at0210213443 ; lem-sym12-at02203443 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-TOFF203-CX41)
-- F1 CS-K0 part11: 395 steps
lem-F1-CS-K0-part11 : Ws → ⟪ (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ S1⁻ ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Bx2-0431 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) ⟫ʷ
lem-F1-CS-K0-part11 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (run b49)))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ S1⁻ ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ X1 ∷ CS03 ∷ X1 ∷ S1⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Bx⁻2-0413 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b0 = at 50 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 50 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸
       at 45 4 (S1⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (sym (wl0398 (lit c4))) ▸
       at 43 1 (CS03⁻ ∷ []) (refl) ▸
       at 42 4 (S1⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (sym (wl0400 (lit c4))) ▸
       at 44 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 39 4 (S1⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (sym (wl0398 (lit c4))) ▸
       at 37 1 (CS03 ∷ []) (refl) ▸ done

  b1 : Chain (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ X1 ∷ CS03 ∷ X1 ∷ S1⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Bx⁻2-0413 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b1 = at 36 4 (S1⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (sym (wl0399 (lit c4))) ▸
       at 38 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 39 2 [] (wl0379 (lit c4)) ▸
       at 40 2 [] (wl0379 (lit c4)) ▸
       at 41 2 [] (wl0379 (lit c4)) ▸
       at 42 2 [] (wl0379 (lit c4)) ▸
       at 38 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 20 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b2 : Chain (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b2 = at 21 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 24 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 27 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 30 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 32 1 (CS03⁻ ∷ []) (refl) ▸
       at 31 4 (S1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (sym (wl0385 (lit c4))) ▸
       at 33 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 28 4 (S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (sym (wl0383 (lit c4))) ▸ done

  b3 : Chain (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b3 = at 26 1 (CS03 ∷ []) (refl) ▸
       at 25 4 (S1 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (sym (wl0384 (lit c4))) ▸
       at 27 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 22 4 (S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (sym (wl0383 (lit c4))) ▸
       at 20 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 21 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 24 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 27 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b4 : Chain (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b4 = at 28 4 (S1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (sym (wl0382 (lit c4))) ▸
       at 25 4 (S1 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (sym (wp0130 c4)) ▸
       at 22 4 (S1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (sym (wl0382 (lit c4))) ▸
       at 19 4 (S1 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (sym (wp0130 c4)) ▸
       at 22 2 [] (wl0379 (lit c4)) ▸
       at 23 2 [] (wl0379 (lit c4)) ▸
       at 24 2 [] (wl0379 (lit c4)) ▸
       at 21 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸ done

  b5 : Chain (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ S1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b5 = at 22 2 [] (wl0379 (lit c4)) ▸
       at 23 2 [] (wl0379 (lit c4)) ▸
       at 24 2 [] (wl0379 (lit c4)) ▸
       at 25 2 [] (wl0379 (lit c4)) ▸
       at 21 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 16 4 (S1 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (sym (wl0387 (lit c4))) ▸
       at 14 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 15 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b6 : Chain (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ S1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b6 = at 18 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 21 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 24 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 26 1 (CS03⁻ ∷ []) (refl) ▸
       at 25 4 (S1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (sym (wl0385 (lit c4))) ▸
       at 27 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 22 4 (S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (sym (wl0383 (lit c4))) ▸
       at 20 1 (CS03 ∷ []) (refl) ▸ done

  b7 : Chain (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ S1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b7 = at 19 4 (S1 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (sym (wl0384 (lit c4))) ▸
       at 21 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 16 4 (S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (sym (wl0383 (lit c4))) ▸
       at 14 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 15 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 18 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 21 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 22 4 (S1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (sym (wl0382 (lit c4))) ▸ done

  b8 : Chain (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ S1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b8 = at 19 4 (S1 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (sym (wp0130 c4)) ▸
       at 16 4 (S1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (sym (wl0382 (lit c4))) ▸
       at 13 4 (S1 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (sym (wp0130 c4)) ▸
       at 16 2 [] (wl0379 (lit c4)) ▸
       at 17 2 [] (wl0379 (lit c4)) ▸
       at 18 2 [] (wl0379 (lit c4)) ▸
       at 15 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 16 2 [] (wl0379 (lit c4)) ▸ done

  b9 : Chain (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ S1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b9 = at 17 2 [] (wl0379 (lit c4)) ▸
       at 18 2 [] (wl0379 (lit c4)) ▸
       at 19 2 [] (wl0379 (lit c4)) ▸
       at 15 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 10 4 (S1 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (sym (wl0387 (lit c4))) ▸
       at 8 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 9 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 12 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b10 : Chain (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ S1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ S1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b10 = at 15 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 18 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 20 1 (CS03⁻ ∷ []) (refl) ▸
       at 19 4 (S1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (sym (wl0385 (lit c4))) ▸
       at 21 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 16 4 (S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (sym (wl0383 (lit c4))) ▸
       at 14 1 (CS03 ∷ []) (refl) ▸
       at 13 4 (S1 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (sym (wl0384 (lit c4))) ▸ done

  b11 : Chain (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ S1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ S1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b11 = at 15 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 10 4 (S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (sym (wl0383 (lit c4))) ▸
       at 8 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 9 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 12 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 15 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 16 4 (S1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (sym (wl0382 (lit c4))) ▸
       at 13 4 (S1 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (sym (wp0130 c4)) ▸ done

  b12 : Chain (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ S1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b12 = at 10 4 (S1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (sym (wl0382 (lit c4))) ▸
       at 7 4 (S1 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (sym (wp0130 c4)) ▸
       at 10 2 [] (wl0379 (lit c4)) ▸
       at 11 2 [] (wl0379 (lit c4)) ▸
       at 12 2 [] (wl0379 (lit c4)) ▸
       at 9 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 10 2 [] (wl0379 (lit c4)) ▸
       at 11 2 [] (wl0379 (lit c4)) ▸ done

  b13 : Chain (Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b13 = at 12 2 [] (wl0379 (lit c4)) ▸
       at 13 2 [] (wl0379 (lit c4)) ▸
       at 9 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 4 4 (S1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (sym (wl0378 (lit c4))) ▸
       at 1 4 (S1 ∷ X1 ∷ S1 ∷ X1 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 21 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 22 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 25 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b14 : Chain (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b14 = at 28 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 31 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 33 1 (CS03⁻ ∷ []) (refl) ▸
       at 32 4 (CS14⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (sym (wp0129 c4)) ▸
       at 34 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 29 4 (CS14⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (sym (wl0381 (lit c4))) ▸
       at 27 1 (CS03 ∷ []) (refl) ▸
       at 26 4 (CS14⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (sym (wp0128 c4)) ▸ done

  b15 : Chain (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b15 = at 28 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 23 4 (CS14⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (sym (wl0381 (lit c4))) ▸
       at 21 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 22 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 25 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 28 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 29 4 (CS14⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (sym (wl0380 (lit c4))) ▸
       at 26 4 (CS14⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (sym (wp0127 c4)) ▸ done

  b16 : Chain (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b16 = at 23 4 (CS14⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (sym (wl0380 (lit c4))) ▸
       at 20 4 (CS14⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (sym (wp0127 c4)) ▸
       at 23 2 [] (wl0379 (lit c4)) ▸
       at 24 2 [] (wl0379 (lit c4)) ▸
       at 25 2 [] (wl0379 (lit c4)) ▸
       at 22 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 23 2 [] (wl0379 (lit c4)) ▸
       at 24 2 [] (wl0379 (lit c4)) ▸ done

  b17 : Chain (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b17 = at 25 2 [] (wl0379 (lit c4)) ▸
       at 26 2 [] (wl0379 (lit c4)) ▸
       at 22 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 17 4 (CS14⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (sym (wp0133 c4)) ▸
       at 15 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 16 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 19 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 22 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b18 : Chain (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b18 = at 25 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 27 1 (CS03⁻ ∷ []) (refl) ▸
       at 26 4 (CS14⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (sym (wp0129 c4)) ▸
       at 28 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 23 4 (CS14⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (sym (wl0381 (lit c4))) ▸
       at 21 1 (CS03 ∷ []) (refl) ▸
       at 20 4 (CS14⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (sym (wp0128 c4)) ▸
       at 22 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b19 : Chain (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b19 = at 17 4 (CS14⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (sym (wl0381 (lit c4))) ▸
       at 15 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 16 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 19 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 22 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 23 4 (CS14⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (sym (wl0380 (lit c4))) ▸
       at 20 4 (CS14⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (sym (wp0127 c4)) ▸
       at 17 4 (CS14⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (sym (wl0380 (lit c4))) ▸ done

  b20 : Chain (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b20 = at 14 4 (CS14⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (sym (wp0127 c4)) ▸
       at 17 2 [] (wl0379 (lit c4)) ▸
       at 18 2 [] (wl0379 (lit c4)) ▸
       at 19 2 [] (wl0379 (lit c4)) ▸
       at 16 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 17 2 [] (wl0379 (lit c4)) ▸
       at 18 2 [] (wl0379 (lit c4)) ▸
       at 19 2 [] (wl0379 (lit c4)) ▸ done

  b21 : Chain (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b21 = at 20 2 [] (wl0379 (lit c4)) ▸
       at 16 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 11 4 (CS14⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (sym (wp0133 c4)) ▸
       at 9 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 10 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 13 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 16 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 19 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b22 : Chain (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b22 = at 21 1 (CS03⁻ ∷ []) (refl) ▸
       at 20 4 (CS14⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (sym (wp0129 c4)) ▸
       at 22 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 17 4 (CS14⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (sym (wl0381 (lit c4))) ▸
       at 15 1 (CS03 ∷ []) (refl) ▸
       at 14 4 (CS14⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (sym (wp0128 c4)) ▸
       at 16 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 11 4 (CS14⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (sym (wl0381 (lit c4))) ▸ done

  b23 : Chain (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b23 = at 9 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 10 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 13 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 16 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 17 4 (CS14⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (sym (wl0380 (lit c4))) ▸
       at 14 4 (CS14⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (sym (wp0127 c4)) ▸
       at 11 4 (CS14⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (sym (wl0380 (lit c4))) ▸
       at 8 4 (CS14⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (sym (wp0127 c4)) ▸ done

  b24 : Chain (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b24 = at 11 2 [] (wl0379 (lit c4)) ▸
       at 12 2 [] (wl0379 (lit c4)) ▸
       at 13 2 [] (wl0379 (lit c4)) ▸
       at 10 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 11 2 [] (wl0379 (lit c4)) ▸
       at 12 2 [] (wl0379 (lit c4)) ▸
       at 13 2 [] (wl0379 (lit c4)) ▸
       at 14 2 [] (wl0379 (lit c4)) ▸ done

  b25 : Chain (Sb2-0-41-3 ∷ S1 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ CCZ034 ∷ Bx2-1043 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b25 = at 10 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 5 4 (CS14⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (sym (wl0377 (lit c4))) ▸
       at 2 4 (CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ []) (sym (wl0453 (lit c4))) ▸
       at 24 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 25 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 24 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 24 1 (Bx2-1043 ∷ []) (lem-sym12-at0210213443 c4) ▸
       at 23 3 (CCZ034 ∷ Bx2-1043 ∷ []) (lem-X1-beta-at02203443 c4) ▸ done

  b26 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ CCZ034 ∷ Bx2-1043 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ CCZ034 ∷ Bx2-1043 ∷ X1 ∷ Sb2-0-41-3 ∷ CCZ034 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b26 = at 24 1 (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4) ▸
       at 24 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 23 2 (Bx2-0413 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14233241 c4) ▸
       at 22 2 (Bx2-0413 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0210243143 c4) ▸
       at 23 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 22 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 22 1 (Bx2-1043 ∷ []) (lem-sym12-at0210213443 c4) ▸
       at 21 3 (CCZ034 ∷ Bx2-1043 ∷ []) (lem-X1-beta-at02203443 c4) ▸ done

  b27 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ CCZ034 ∷ Bx2-1043 ∷ X1 ∷ Sb2-0-41-3 ∷ CCZ034 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b27 = at 22 1 (Bx2-0143 ∷ []) (lem-sym12-at02203443 c4) ▸
       at 22 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 21 2 (Bx2-0413 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14233241 c4) ▸
       at 25 2 (X1 ∷ CCZ034 ∷ []) (wp0060 c4) ▸
       at 22 2 (X1 ∷ CCZ034 ∷ []) (wp0060 c4) ▸
       at 23 2 (Sb2-0-41-3 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14233241 c4) ▸
       at 24 2 (X1 ∷ CCZ034 ∷ []) (wp0060 c4) ▸
       at 25 2 [] (wp0024 c4) ▸ done

  b28 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b28 = at 25 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (sym (wl0402 (lit c4))) ▸
       at 24 2 (K3 ∷ X1 ∷ []) (sym (wl0418 (lit c4))) ▸
       at 23 2 (K3 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 c4) ▸
       at 22 2 (K3 ∷ X1 ∷ []) (sym (wl0418 (lit c4))) ▸
       at 26 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4)) ▸
       at 24 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 25 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 28 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b29 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b29 = at 31 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 34 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 36 1 (CS03⁻ ∷ []) (refl) ▸
       at 35 4 (CS13 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (sym (wl0417 (lit c4))) ▸
       at 37 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 32 4 (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (sym (wl0415 (lit c4))) ▸
       at 30 1 (CS03 ∷ []) (refl) ▸
       at 29 4 (CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (sym (wl0416 (lit c4))) ▸ done

  b30 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b30 = at 31 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 26 4 (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (sym (wl0415 (lit c4))) ▸
       at 24 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 24 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 25 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 28 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 31 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 32 4 (CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (sym (wl0454 (lit c4))) ▸ done

  b31 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b31 = at 29 4 (CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (sym (wl0455 (lit c4))) ▸
       at 26 4 (CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 23 4 (CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (sym (wl0455 (lit c4))) ▸
       at 26 2 [] (wl0379 (lit c4)) ▸
       at 27 2 [] (wl0379 (lit c4)) ▸
       at 28 2 [] (wl0379 (lit c4)) ▸
       at 25 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 25 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸ done

  b32 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b32 = at 26 2 [] (wl0379 (lit c4)) ▸
       at 27 2 [] (wl0379 (lit c4)) ▸
       at 28 2 [] (wl0379 (lit c4)) ▸
       at 29 2 [] (wl0379 (lit c4)) ▸
       at 25 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 25 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 26 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 29 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b33 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b33 = at 32 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 35 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 37 1 (CS03⁻ ∷ []) (refl) ▸
       at 36 6 (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (sym (wp0141 c4)) ▸
       at 40 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 31 1 (CS03 ∷ []) (refl) ▸
       at 27 12 (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (sym (wp0140 c4)) ▸
       at 34 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b34 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b34 = at 25 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸
       at 25 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 25 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 26 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 29 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 32 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 33 6 (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ []) (sym (wl0408 (lit c4))) ▸
       at 32 2 (CX41 ∷ X1 ∷ []) (sym (wl0406 (lit c4))) ▸ done

  b35 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b35 = at 31 2 (CX41 ∷ Toff203 ∷ []) (lem-comm-TOFF203-CX41 (lit c4)) ▸
       at 30 2 (CX41 ∷ X1 ∷ []) (sym (wl0406 (lit c4))) ▸
       at 31 4 (CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ []) (sym (wl0407 (lit c4))) ▸
       at 34 2 (CX41 ∷ X1 ∷ []) (sym (wl0406 (lit c4))) ▸
       at 33 2 (CX41 ∷ Toff203 ∷ []) (lem-comm-TOFF203-CX41 (lit c4)) ▸
       at 32 2 (CX41 ∷ X1 ∷ []) (sym (wl0406 (lit c4))) ▸
       at 27 6 (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ []) (sym (wl0408 (lit c4))) ▸
       at 26 2 (CX41 ∷ X1 ∷ []) (sym (wl0406 (lit c4))) ▸ done

  b36 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b36 = at 25 2 (CX41 ∷ Toff203 ∷ []) (lem-comm-TOFF203-CX41 (lit c4)) ▸
       at 24 2 (CX41 ∷ X1 ∷ []) (sym (wl0406 (lit c4))) ▸
       at 25 4 (CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ []) (sym (wl0407 (lit c4))) ▸
       at 28 2 (CX41 ∷ X1 ∷ []) (sym (wl0406 (lit c4))) ▸
       at 27 2 (CX41 ∷ Toff203 ∷ []) (lem-comm-TOFF203-CX41 (lit c4)) ▸
       at 26 2 (CX41 ∷ X1 ∷ []) (sym (wl0406 (lit c4))) ▸
       at 29 2 [] (wl0379 (lit c4)) ▸
       at 30 2 [] (wl0379 (lit c4)) ▸ done

  b37 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b37 = at 31 2 [] (wl0379 (lit c4)) ▸
       at 28 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸
       at 28 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸
       at 28 1 (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4) ▸
       at 29 2 [] (wl0379 (lit c4)) ▸
       at 30 2 [] (wl0379 (lit c4)) ▸
       at 31 2 [] (wl0379 (lit c4)) ▸
       at 32 2 [] (wl0379 (lit c4)) ▸ done

  b38 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ CCZ134 ∷ K3⁻ ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b38 = at 28 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 29 2 (CS34 ∷ X1 ∷ []) (sym (wl0405 (lit c4))) ▸
       at 28 2 (CS34 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at0210243143 c4) ▸
       at 27 2 (CS34 ∷ X1 ∷ []) (sym (wl0405 (lit c4))) ▸
       at 23 5 (CCZ134 ∷ []) (sym (wl0404 (lit c4))) ▸
       at 26 2 (K3⁻ ∷ X1 ∷ []) (sym (wl0403 (lit c4))) ▸
       at 25 2 (K3⁻ ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0210243143 c4) ▸
       at 24 2 (K3⁻ ∷ X1 ∷ []) (sym (wl0403 (lit c4))) ▸ done

  b39 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ CCZ134 ∷ K3⁻ ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b39 = at 22 3 (Toff314 ∷ []) (wl0402 (lit c4)) ▸
       at 26 1 (CS03 ∷ []) (refl) ▸
       at 25 2 (CS03 ∷ X1 ∷ []) (sym (wl0419 (lit c4))) ▸
       at 25 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 24 2 (Sb2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 c4) ▸
       at 24 1 (CS03 ∷ []) (refl) ▸
       at 23 2 (CS03 ∷ X1 ∷ []) (sym (wl0419 (lit c4))) ▸
       at 23 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b40 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b40 = at 27 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (sym (wl0402 (lit c4))) ▸
       at 26 2 (K3 ∷ X1 ∷ []) (sym (wl0418 (lit c4))) ▸
       at 25 2 (K3 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 c4) ▸
       at 24 2 (K3 ∷ X1 ∷ []) (sym (wl0418 (lit c4))) ▸
       at 28 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4)) ▸
       at 26 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 27 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 30 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b41 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b41 = at 33 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 36 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 38 1 (CS03⁻ ∷ []) (refl) ▸
       at 37 4 (CS13 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (sym (wl0417 (lit c4))) ▸
       at 39 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 34 4 (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (sym (wl0415 (lit c4))) ▸
       at 32 1 (CS03 ∷ []) (refl) ▸
       at 31 4 (CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (sym (wl0416 (lit c4))) ▸ done

  b42 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b42 = at 33 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 28 4 (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (sym (wl0415 (lit c4))) ▸
       at 26 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 26 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 27 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 30 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 33 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 34 4 (CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (sym (wl0454 (lit c4))) ▸ done

  b43 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff201 ∷ X1 ∷ CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b43 = at 31 4 (CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (sym (wl0455 (lit c4))) ▸
       at 28 4 (CS13 ∷ X1 ∷ CCZ234 ∷ X1 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 25 4 (CS13 ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (sym (wl0455 (lit c4))) ▸
       at 28 2 [] (wl0379 (lit c4)) ▸
       at 29 2 [] (wl0379 (lit c4)) ▸
       at 30 2 [] (wl0379 (lit c4)) ▸
       at 27 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 27 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸ done

  b44 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b44 = at 28 2 [] (wl0379 (lit c4)) ▸
       at 29 2 [] (wl0379 (lit c4)) ▸
       at 30 2 [] (wl0379 (lit c4)) ▸
       at 31 2 [] (wl0379 (lit c4)) ▸
       at 27 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 27 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 28 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 31 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸ done

  b45 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b45 = at 34 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 37 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 39 1 (CS03⁻ ∷ []) (refl) ▸
       at 38 6 (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (sym (wp0141 c4)) ▸
       at 42 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 33 1 (CS03 ∷ []) (refl) ▸
       at 29 12 (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (sym (wp0140 c4)) ▸
       at 36 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b46 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b46 = at 27 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸
       at 27 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 27 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 28 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 31 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 34 0 (X1 ∷ X1 ∷ []) (sym (wl0379 (lit c4))) ▸
       at 35 6 (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ []) (sym (wl0408 (lit c4))) ▸
       at 34 2 (CX41 ∷ X1 ∷ []) (sym (wl0406 (lit c4))) ▸ done

  b47 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b47 = at 33 2 (CX41 ∷ Toff203 ∷ []) (lem-comm-TOFF203-CX41 (lit c4)) ▸
       at 32 2 (CX41 ∷ X1 ∷ []) (sym (wl0406 (lit c4))) ▸
       at 33 4 (CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ []) (sym (wl0407 (lit c4))) ▸
       at 36 2 (CX41 ∷ X1 ∷ []) (sym (wl0406 (lit c4))) ▸
       at 35 2 (CX41 ∷ Toff203 ∷ []) (lem-comm-TOFF203-CX41 (lit c4)) ▸
       at 34 2 (CX41 ∷ X1 ∷ []) (sym (wl0406 (lit c4))) ▸
       at 29 6 (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ []) (sym (wl0408 (lit c4))) ▸
       at 28 2 (CX41 ∷ X1 ∷ []) (sym (wl0406 (lit c4))) ▸ done

  b48 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b48 = at 27 2 (CX41 ∷ Toff203 ∷ []) (lem-comm-TOFF203-CX41 (lit c4)) ▸
       at 26 2 (CX41 ∷ X1 ∷ []) (sym (wl0406 (lit c4))) ▸
       at 27 4 (CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ []) (sym (wl0407 (lit c4))) ▸
       at 30 2 (CX41 ∷ X1 ∷ []) (sym (wl0406 (lit c4))) ▸
       at 29 2 (CX41 ∷ Toff203 ∷ []) (lem-comm-TOFF203-CX41 (lit c4)) ▸
       at 28 2 (CX41 ∷ X1 ∷ []) (sym (wl0406 (lit c4))) ▸
       at 31 2 [] (wl0379 (lit c4)) ▸
       at 32 2 [] (wl0379 (lit c4)) ▸ done

  b49 : Chain (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ []) (Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Bx2-0431 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ CS04 ∷ [])
  b49 = at 33 2 [] (wl0379 (lit c4)) ▸
       at 30 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸
       at 30 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸ done


{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D175 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0103 ; wl0189 ; wl0211 ; wl0283 ; wl0305 ; wl0364 ; wl0433 ; wl0600 ; wl0717 ; wl0719 ; wl0730 ; wl0732 ; wl0733 ; wl0734 ; wl0735 ; wl0736 ; wl0737 ; wl0738 ; wl0739 ; wl0740 ; wl0741 ; wl0742 ; wp0296 ; wp0343 ; wp0344 ; wp0345 ; wp0346 ; wp0353 ; wp0356 ; wp0373 ; wp0374 ; wp0375 ; wp0376 ; wp0377 ; wp0378 ; wp0379 ; wp0380 ; wp0381 ; wp0382 ; wp0383 ; wp0384 ; wp0385 ; wp0386)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0 ; lem-sym12-at14213243 ; lem-sym23-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at0210243143 ; lem-beta-T-at0310243142 ; lem-sym12-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-SBsym-at0113203442)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D160 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS02-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D166 using (lem-sym23-at143143)
open import Examples.Groups.Clifford+CS.Five.D.D171 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-beta-T-at12213443)
open import Examples.Groups.Clifford+CS.Five.D.D174 using (lem-auto-BOX⟨0·1234⟩-∣-CS04-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-CSd04-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-K0-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at0210243143 ; lem-beta-T-at143143)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ013 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-1-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-2-BOX⟨0·3142⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩ ; lem-nat-3-SBOX⟨1·0·2·4⟩ ; lem-nat-3-SBOXd⟨1·0·2·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-SBOX⟨0·1·2·3⟩ ; lem-nat-1-SBOX⟨0·2·1·3⟩ ; lem-nat-1-SBOXd⟨0·1·2·3⟩ ; lem-nat-1-SBOXd⟨0·2·1·3⟩ ; lem-nat-2-SBOX⟨1·0·3·4⟩ ; lem-nat-2-SBOXd⟨1·0·3·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-SBOX⟨1·0·2·4⟩ ; lem-nat-2-SBOXd⟨1·0·2·4⟩ ; lem-nat-3-SBOX⟨1·0·2·3⟩ ; lem-nat-3-SBOXd⟨1·0·2·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-BOX⟨0·3241⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-SBOX⟨0·1·2·3⟩ ; lem-nat-0-SBOXd⟨0·1·2·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-SBOX⟨1·0·2·3⟩ ; lem-nat-0-SBOXd⟨1·0·2·3⟩)
-- F4 CS01^0|CS12^1: 648 steps
lem-F4-CS01ᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣CS12ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (trans (run b62) (trans (run b63) (trans (run b64) (trans (run b65) (trans (run b66) (trans (run b67) (trans (run b68) (trans (run b69) (trans (run b70) (trans (run b71) (trans (run b72) (trans (run b73) (trans (run b74) (trans (run b75) (trans (run b76) (trans (run b77) (trans (run b78) (trans (run b79) (run b80))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 3 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸
       at 3 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at143143 c4) ▸
       at 3 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (sym (wp0373 c4)) ▸
       at 4 1 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (wp0374 c4) ▸
       at 5 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0189 (lit c4))) ▸
       at 8 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0189 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b1 = at 11 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0189 (lit c4))) ▸
       at 14 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0189 (lit c4))) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b2 = at 13 1 (CS03⁻ ∷ []) (refl) ▸
       at 6 12 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0375 c4)) ▸
       at 10 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 16 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 6 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wp0376 c4)) ▸
       at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b3 : Chain (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ CS12 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b3 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 10 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 9 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 11 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ CS12 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b4 = at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wp0343 c4)) ▸
       at 19 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 16 4 (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0345 c4)) ▸
       at 13 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 10 4 (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0346 c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸ done

  b5 : Chain (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b5 = at 15 2 [] (wl0283 (lit c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 12 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 13 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 12 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 11 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 6 6 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0377 c4)) ▸
       at 5 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸ done

  b6 : Chain (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b6 = at 4 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 3 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 5 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wp0343 c4)) ▸ done

  b7 : Chain (X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b7 = at 13 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 10 4 (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0345 c4)) ▸
       at 7 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 4 4 (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0346 c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸ done

  b8 : Chain (X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b8 = at 6 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 7 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 6 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 5 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 0 6 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0377 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸ done

  b9 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b9 = at 4 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 4 1 (Sb3-0-41-2 ∷ []) (lem-F0 c4) ▸
       at 4 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸ done

  b10 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Bx3-0412 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b10 = at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 1 (CS02 ∷ []) (refl) ▸
       at 16 1 (CS02⁻ ∷ []) (refl) ▸
       at 9 21 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (sym (wp0378 c4)) ▸
       at 22 1 (Sb3-0-2-1 ∷ []) (refl) ▸ done

  b11 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Bx3-0412 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ K0 ∷ CCZ123 ∷ X4 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b11 = at 28 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 6 15 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) (sym (wp0379 c4)) ▸
       at 4 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-beta-T-at0310243142 c4) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 13 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸ done

  b12 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ K0 ∷ CCZ123 ∷ X4 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b12 = at 12 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 13 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0733 (lit c4))) ▸
       at 16 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 15 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 14 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 17 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 16 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 15 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸ done

  b13 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b13 = at 17 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0211 (lit c4)) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 28 4 (CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wp0380 c4)) ▸
       at 25 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (sym (wp0381 c4)) ▸
       at 22 4 (CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0382 c4)) ▸ done

  b14 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ CCZ123 ∷ K0⁻ ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b14 = at 19 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (sym (wp0381 c4)) ▸
       at 16 4 (CS04⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0383 c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 18 5 (CCZ123 ∷ []) (sym (wl0211 (lit c4))) ▸
       at 19 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸ done

  b15 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ CCZ123 ∷ K0⁻ ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ X4 ∷ K0⁻ ∷ CCZ123 ∷ X4 ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b15 = at 18 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 17 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 20 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 19 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 18 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 19 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0733 (lit c4))) ▸
       at 22 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 21 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸ done

  b16 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ X4 ∷ K0⁻ ∷ CCZ123 ∷ X4 ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ X4 ∷ CCZ123 ∷ K0⁻ ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b16 = at 20 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 23 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 22 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 21 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 24 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 23 2 (CS02 ∷ CCZ123 ∷ []) (wl0734 (lit c4)) ▸
       at 22 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 25 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸ done

  b17 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ X4 ∷ CCZ123 ∷ K0⁻ ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ X4 ∷ CCZ123 ∷ K0⁻ ∷ X4 ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b17 = at 24 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 23 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 9 15 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ []) (sym (wp0384 c4)) ▸
       at 8 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 7 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 6 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 7 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0733 (lit c4))) ▸
       at 10 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸ done

  b18 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ X4 ∷ CCZ123 ∷ K0⁻ ∷ X4 ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b18 = at 9 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 8 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 11 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 10 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 9 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 11 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0211 (lit c4)) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b19 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ CS23 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b19 = at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 4 (CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wp0380 c4)) ▸
       at 19 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (sym (wp0381 c4)) ▸
       at 16 4 (CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0382 c4)) ▸
       at 13 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (sym (wp0381 c4)) ▸
       at 10 4 (CS04⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0383 c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸ done

  b20 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ CS23 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ X4 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b20 = at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 12 5 (CCZ123 ∷ []) (sym (wl0211 (lit c4))) ▸
       at 13 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 12 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 11 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 14 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸ done

  b21 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ X4 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ X4 ∷ K0 ∷ CCZ123 ∷ X4 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b21 = at 13 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 12 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 13 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0733 (lit c4))) ▸
       at 16 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 15 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 14 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 17 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 16 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸ done

  b22 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ X4 ∷ K0 ∷ CCZ123 ∷ X4 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b22 = at 15 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 18 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 17 2 (CS02 ∷ CCZ123 ∷ []) (wl0734 (lit c4)) ▸
       at 16 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 19 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 18 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 17 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 3 15 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ []) (sym (wp0384 c4)) ▸ done

  b23 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b23 = at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 16 4 (Bx3-0412 ∷ []) (sym (lem-beta-T-at0310243142 c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸ done

  b24 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b24 = at 16 5 (Sb3-0-41-2 ∷ []) (refl) ▸
       at 16 1 (Sb2-0-41-3 ∷ []) (sym (lem-F0 c4)) ▸
       at 2 2 [] (wl0189 (lit c4)) ▸
       at 3 2 [] (wl0189 (lit c4)) ▸
       at 4 2 [] (wl0189 (lit c4)) ▸
       at 5 2 [] (wl0189 (lit c4)) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0374 c4)) ▸
       at 0 3 (Toff024 ∷ []) (wp0373 c4) ▸ done

  b25 : Chain (Toff024 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b25 = at 3 2 (CCZ013 ∷ X4 ∷ []) (sym (wp0296 c4)) ▸
       at 2 2 (CCZ013 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at0210243143 c4) ▸
       at 1 2 (CCZ013 ∷ X4 ∷ []) (sym (wp0296 c4)) ▸
       at 5 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (sym (wp0373 c4)) ▸
       at 6 1 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (wp0374 c4) ▸
       at 7 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0189 (lit c4))) ▸
       at 10 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0189 (lit c4))) ▸
       at 13 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0189 (lit c4))) ▸ done

  b26 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b26 = at 16 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0189 (lit c4))) ▸
       at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 1 (CS03 ∷ []) (refl) ▸
       at 15 1 (CS03⁻ ∷ []) (refl) ▸ done

  b27 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b27 = at 8 12 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0375 c4)) ▸
       at 12 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 18 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 6 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wp0376 c4)) ▸
       at 3 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b28 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b28 = at 13 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 12 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 11 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 13 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b29 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b29 = at 24 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wp0343 c4)) ▸
       at 21 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 18 4 (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0345 c4)) ▸
       at 15 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 12 4 (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0346 c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸ done

  b30 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ K0 ∷ CCZ123 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b30 = at 18 2 [] (wl0283 (lit c4)) ▸
       at 14 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 15 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 14 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 13 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 8 6 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0377 c4)) ▸
       at 7 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 6 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸ done

  b31 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ K0 ∷ CCZ123 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b31 = at 5 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 7 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wp0343 c4)) ▸
       at 15 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸ done

  b32 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b32 = at 12 4 (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0345 c4)) ▸
       at 9 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 6 4 (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0346 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 8 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸ done

  b33 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b33 = at 9 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 8 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 7 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 2 6 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0377 c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 6 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸ done

  b34 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Bx3-0412 ∷ X4 ∷ X4 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b34 = at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 6 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 6 1 (Sb3-0-41-2 ∷ []) (lem-F0 c4) ▸
       at 6 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b35 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Bx3-0412 ∷ X4 ∷ X4 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Bx3-0412 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b35 = at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 1 (CS02 ∷ []) (refl) ▸
       at 18 1 (CS02⁻ ∷ []) (refl) ▸
       at 11 21 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (sym (wp0378 c4)) ▸
       at 24 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 30 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸ done

  b36 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Bx3-0412 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b36 = at 8 15 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) (sym (wp0379 c4)) ▸
       at 6 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-beta-T-at0310243142 c4) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 15 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 14 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸ done

  b37 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b37 = at 15 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0733 (lit c4))) ▸
       at 18 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 17 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 16 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 19 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 18 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 17 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 19 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0211 (lit c4)) ▸ done

  b38 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b38 = at 20 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 26 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 29 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 30 4 (CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wp0380 c4)) ▸
       at 27 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (sym (wp0381 c4)) ▸
       at 24 4 (CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0382 c4)) ▸
       at 21 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (sym (wp0381 c4)) ▸ done

  b39 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ K0⁻ ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b39 = at 18 4 (CS04⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0383 c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 23 2 [] (wl0283 (lit c4)) ▸
       at 24 2 [] (wl0283 (lit c4)) ▸
       at 20 5 (CCZ123 ∷ []) (sym (wl0211 (lit c4))) ▸
       at 21 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 20 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸ done

  b40 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ K0⁻ ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b40 = at 19 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 22 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 21 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 20 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 21 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0733 (lit c4))) ▸
       at 24 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 23 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 22 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸ done

  b41 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ X4 ∷ K0⁻ ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b41 = at 25 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 24 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 23 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 26 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 25 2 (CS02 ∷ CCZ123 ∷ []) (wl0734 (lit c4)) ▸
       at 24 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 27 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 26 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸ done

  b42 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ X4 ∷ K0⁻ ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ X4 ∷ K0⁻ ∷ CCZ123 ∷ X4 ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b42 = at 25 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 11 15 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ []) (sym (wp0384 c4)) ▸
       at 10 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 9 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 8 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 9 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0733 (lit c4))) ▸
       at 12 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 11 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸ done

  b43 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ X4 ∷ K0⁻ ∷ CCZ123 ∷ X4 ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b43 = at 10 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 13 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 12 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 11 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 13 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0211 (lit c4)) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b44 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b44 = at 23 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 4 (CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wp0380 c4)) ▸
       at 21 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (sym (wp0381 c4)) ▸
       at 18 4 (CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0382 c4)) ▸
       at 15 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (sym (wp0381 c4)) ▸
       at 12 4 (CS04⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0383 c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸ done

  b45 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ X4 ∷ K0 ∷ CCZ123 ∷ X4 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b45 = at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 14 5 (CCZ123 ∷ []) (sym (wl0211 (lit c4))) ▸
       at 15 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 14 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 13 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 16 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 15 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸ done

  b46 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ X4 ∷ K0 ∷ CCZ123 ∷ X4 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b46 = at 14 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 15 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0733 (lit c4))) ▸
       at 18 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 17 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 16 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 19 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 18 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 17 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸ done

  b47 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b47 = at 20 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 19 2 (CS02 ∷ CCZ123 ∷ []) (wl0734 (lit c4)) ▸
       at 18 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 21 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 20 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 19 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 5 15 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ []) (sym (wp0384 c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸ done

  b48 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Sb3-0-41-2 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b48 = at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 18 4 (Bx3-0412 ∷ []) (sym (lem-beta-T-at0310243142 c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 18 5 (Sb3-0-41-2 ∷ []) (refl) ▸ done

  b49 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Sb3-0-41-2 ∷ X4 ∷ CCZ013 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ X4 ∷ Sb2-0-41-3 ∷ CCZ013 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b49 = at 18 1 (Sb2-0-41-3 ∷ []) (sym (lem-F0 c4)) ▸
       at 4 2 [] (wl0189 (lit c4)) ▸
       at 5 2 [] (wl0189 (lit c4)) ▸
       at 6 2 [] (wl0189 (lit c4)) ▸
       at 7 2 [] (wl0189 (lit c4)) ▸
       at 3 5 (CCZ024 ∷ []) (sym (wp0374 c4)) ▸
       at 2 3 (Toff024 ∷ []) (wp0373 c4) ▸
       at 5 2 (CCZ013 ∷ X4 ∷ []) (sym (wp0296 c4)) ▸ done

  b50 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ X4 ∷ Sb2-0-41-3 ∷ CCZ013 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ X4 ∷ K3 ∷ Sb2-0-41-3 ∷ X4 ∷ CCZ234 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b50 = at 4 2 (CCZ013 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at0210243143 c4) ▸
       at 3 2 (CCZ013 ∷ X4 ∷ []) (sym (wp0296 c4)) ▸
       at 0 4 (Bx0-4213 ∷ []) (sym (lem-beta-T-at143143 c4)) ▸
       at 0 1 (Bx0-4123 ∷ []) (lem-sym23-at143143 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 4 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (sym (wl0364 (lit c4))) ▸
       at 3 2 (K3 ∷ X4 ∷ []) (sym (wl0732 (lit c4))) ▸
       at 2 2 (K3 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 c4) ▸ done

  b51 : Chain (Bx0-1423 ∷ X4 ∷ K3 ∷ Sb2-0-41-3 ∷ X4 ∷ CCZ234 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ CCZ234 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b51 = at 1 2 (K3 ∷ X4 ∷ []) (sym (wl0732 (lit c4))) ▸
       at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 1 (CS03⁻ ∷ []) (refl) ▸
       at 14 4 (CCZ234 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0385 c4)) ▸ done

  b52 : Chain (Bx0-1423 ∷ K3 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ CCZ234 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ X4 ∷ Bx2-0413 ∷ CS23 ∷ X4 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b52 = at 16 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 11 4 (CCZ234 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 9 1 (CS03 ∷ []) (refl) ▸
       at 8 4 (CCZ234 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0386 c4)) ▸
       at 10 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 5 4 (CCZ234 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 5 1 (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (wl0600 (lit c4)) ▸
       at 4 2 (CS23 ∷ X4 ∷ []) (sym (wl0736 (lit c4))) ▸ done

  b53 : Chain (Bx0-1423 ∷ K3 ∷ X4 ∷ Bx2-0413 ∷ CS23 ∷ X4 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS23 ∷ K2 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ CS24 ∷ K2⁻ ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b53 = at 3 2 (CS23 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS04-at0210243143 c4) ▸
       at 2 2 (CS23 ∷ X4 ∷ []) (sym (wl0736 (lit c4))) ▸
       at 6 1 (K2 ∷ CZ24 ∷ K2⁻ ∷ []) (wl0737 (lit c4)) ▸
       at 5 2 (K2 ∷ X4 ∷ []) (sym (wl0730 (lit c4))) ▸
       at 4 2 (K2 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at0210243143 c4) ▸
       at 3 2 (K2 ∷ X4 ∷ []) (sym (wl0730 (lit c4))) ▸
       at 7 1 (CS24 ∷ CS24 ∷ []) (sym (wl0305 (lit c4))) ▸
       at 5 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸ done

  b54 : Chain (Bx0-1423 ∷ K3 ∷ CS23 ∷ K2 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ CS24 ∷ K2⁻ ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS23 ∷ K2 ∷ CS24 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b54 = at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 10 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸
       at 7 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 4 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸ done

  b55 : Chain (Bx0-1423 ∷ K3 ∷ CS23 ∷ K2 ∷ CS24 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS23 ∷ K2 ∷ CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K2⁻ ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b55 = at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 6 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 6 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸ done

  b56 : Chain (Bx0-1423 ∷ K3 ∷ CS23 ∷ K2 ∷ CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K2⁻ ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS23 ∷ K2 ∷ CZ24 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ K2⁻ ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b56 = at 11 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸
       at 8 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 5 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 7 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 4 2 (CZ24 ∷ []) (wl0305 (lit c4)) ▸ done

  b57 : Chain (Bx0-1423 ∷ K3 ∷ CS23 ∷ K2 ∷ CZ24 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ K2⁻ ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ K2 ∷ CZ24 ∷ K2⁻ ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b57 = at 7 2 (K2⁻ ∷ X4 ∷ []) (sym (wl0738 (lit c4))) ▸
       at 6 2 (K2⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0210243143 c4) ▸
       at 5 2 (K2⁻ ∷ X4 ∷ []) (sym (wl0738 (lit c4))) ▸
       at 3 3 (CX42 ∷ []) (sym (wl0737 (lit c4))) ▸
       at 6 2 (CS23⁻ ∷ X4 ∷ []) (sym (wl0739 (lit c4))) ▸
       at 5 2 (CS23⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd04-at0210243143 c4) ▸
       at 4 2 (CS23⁻ ∷ X4 ∷ []) (sym (wl0739 (lit c4))) ▸
       at 8 1 (K2 ∷ CZ24 ∷ K2⁻ ∷ []) (wl0737 (lit c4)) ▸ done

  b58 : Chain (Bx0-1423 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ K2 ∷ CZ24 ∷ K2⁻ ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ K2 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ CS24 ∷ K2⁻ ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b58 = at 7 2 (K2 ∷ X4 ∷ []) (sym (wl0730 (lit c4))) ▸
       at 6 2 (K2 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at0210243143 c4) ▸
       at 5 2 (K2 ∷ X4 ∷ []) (sym (wl0730 (lit c4))) ▸
       at 9 1 (CS24 ∷ CS24 ∷ []) (sym (wl0305 (lit c4))) ▸
       at 7 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b59 : Chain (Bx0-1423 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ K2 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ CS24 ∷ K2⁻ ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ K2 ∷ CS24 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b59 = at 15 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 12 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸
       at 9 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 6 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 8 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸ done

  b60 : Chain (Bx0-1423 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ K2 ∷ CS24 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ K2 ∷ CS24 ∷ CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K2⁻ ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b60 = at 8 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 13 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸
       at 10 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 7 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸ done

  b61 : Chain (Bx0-1423 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ K2 ∷ CS24 ∷ CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K2⁻ ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ K2 ∷ CZ24 ∷ K2⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b61 = at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 9 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 6 2 (CZ24 ∷ []) (wl0305 (lit c4)) ▸
       at 9 2 (K2⁻ ∷ X4 ∷ []) (sym (wl0738 (lit c4))) ▸
       at 8 2 (K2⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0210243143 c4) ▸
       at 7 2 (K2⁻ ∷ X4 ∷ []) (sym (wl0738 (lit c4))) ▸ done

  b62 : Chain (Bx0-1423 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ K2 ∷ CZ24 ∷ K2⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ X4 ∷ Toff204 ∷ X4 ∷ CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b62 = at 5 3 (CX42 ∷ []) (sym (wl0737 (lit c4))) ▸
       at 7 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 4 (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0719 (lit c4))) ▸
       at 12 4 (CS34 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0356 c4)) ▸
       at 9 4 (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0719 (lit c4))) ▸ done

  b63 : Chain (Bx0-1423 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ X4 ∷ Toff204 ∷ X4 ∷ CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CCZ234 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b63 = at 6 4 (CS34 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0356 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 8 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 2 5 (CCZ234 ∷ []) (sym (wl0600 (lit c4))) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸ done

  b64 : Chain (Bx0-1423 ∷ K3 ∷ CCZ234 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b64 = at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 5 2 (K3⁻ ∷ X4 ∷ []) (sym (wl0740 (lit c4))) ▸
       at 4 2 (K3⁻ ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0210243143 c4) ▸
       at 3 2 (K3⁻ ∷ X4 ∷ []) (sym (wl0740 (lit c4))) ▸
       at 1 3 (Toff324 ∷ []) (wl0364 (lit c4)) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸ done

  b65 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ Sb2-0-41-3 ∷ K3 ∷ X4 ∷ CCZ234 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b65 = at 4 2 (CS13 ∷ X4 ∷ []) (sym (wl0741 (lit c4))) ▸
       at 4 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 3 2 (Sb0-1-3-2 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at0210243143 c4) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 2 2 (CS13 ∷ X4 ∷ []) (sym (wl0741 (lit c4))) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 6 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (sym (wl0364 (lit c4))) ▸
       at 5 2 (K3 ∷ X4 ∷ []) (sym (wl0732 (lit c4))) ▸ done

  b66 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ Sb2-0-41-3 ∷ K3 ∷ X4 ∷ CCZ234 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CCZ234 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b66 = at 4 2 (K3 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 c4) ▸
       at 3 2 (K3 ∷ X4 ∷ []) (sym (wl0732 (lit c4))) ▸
       at 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 1 (CS03⁻ ∷ []) (refl) ▸ done

  b67 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CCZ234 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b67 = at 16 4 (CCZ234 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0385 c4)) ▸
       at 18 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 13 4 (CCZ234 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 11 1 (CS03 ∷ []) (refl) ▸
       at 10 4 (CCZ234 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0386 c4)) ▸
       at 12 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 7 4 (CCZ234 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 7 1 (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (wl0600 (lit c4)) ▸ done

  b68 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS23 ∷ K2 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ CS24 ∷ CS24 ∷ K2⁻ ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b68 = at 6 2 (CS23 ∷ X4 ∷ []) (sym (wl0736 (lit c4))) ▸
       at 5 2 (CS23 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS04-at0210243143 c4) ▸
       at 4 2 (CS23 ∷ X4 ∷ []) (sym (wl0736 (lit c4))) ▸
       at 8 1 (K2 ∷ CZ24 ∷ K2⁻ ∷ []) (wl0737 (lit c4)) ▸
       at 7 2 (K2 ∷ X4 ∷ []) (sym (wl0730 (lit c4))) ▸
       at 6 2 (K2 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at0210243143 c4) ▸
       at 5 2 (K2 ∷ X4 ∷ []) (sym (wl0730 (lit c4))) ▸
       at 9 1 (CS24 ∷ CS24 ∷ []) (sym (wl0305 (lit c4))) ▸ done

  b69 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS23 ∷ K2 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ CS24 ∷ CS24 ∷ K2⁻ ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS23 ∷ K2 ∷ CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b69 = at 7 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 12 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸
       at 9 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 6 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸ done

  b70 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS23 ∷ K2 ∷ CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS23 ∷ K2 ∷ CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b70 = at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 8 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 8 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b71 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS23 ∷ K2 ∷ CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS23 ∷ K2 ∷ CS24 ∷ CS24 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ K2⁻ ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b71 = at 16 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 13 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸
       at 10 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 7 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 9 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸ done

  b72 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS23 ∷ K2 ∷ CS24 ∷ CS24 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ K2⁻ ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ CX42 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b72 = at 6 2 (CZ24 ∷ []) (wl0305 (lit c4)) ▸
       at 9 2 (K2⁻ ∷ X4 ∷ []) (sym (wl0738 (lit c4))) ▸
       at 8 2 (K2⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0210243143 c4) ▸
       at 7 2 (K2⁻ ∷ X4 ∷ []) (sym (wl0738 (lit c4))) ▸
       at 5 3 (CX42 ∷ []) (sym (wl0737 (lit c4))) ▸
       at 8 2 (CS23⁻ ∷ X4 ∷ []) (sym (wl0739 (lit c4))) ▸
       at 7 2 (CS23⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd04-at0210243143 c4) ▸
       at 6 2 (CS23⁻ ∷ X4 ∷ []) (sym (wl0739 (lit c4))) ▸ done

  b73 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ CX42 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ K2 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ CS24 ∷ K2⁻ ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b73 = at 10 1 (K2 ∷ CZ24 ∷ K2⁻ ∷ []) (wl0737 (lit c4)) ▸
       at 9 2 (K2 ∷ X4 ∷ []) (sym (wl0730 (lit c4))) ▸
       at 8 2 (K2 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at0210243143 c4) ▸
       at 7 2 (K2 ∷ X4 ∷ []) (sym (wl0730 (lit c4))) ▸
       at 11 1 (CS24 ∷ CS24 ∷ []) (sym (wl0305 (lit c4))) ▸
       at 9 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b74 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ K2 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ CS24 ∷ K2⁻ ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ K2 ∷ CS24 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b74 = at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 14 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸
       at 11 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 8 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸ done

  b75 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ K2 ∷ CS24 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ K2 ∷ CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K2⁻ ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b75 = at 10 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 10 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 15 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸
       at 12 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸ done

  b76 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ K2 ∷ CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K2⁻ ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ K2 ∷ CZ24 ∷ X4 ∷ K2⁻ ∷ Bx2-0413 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b76 = at 9 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 11 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 8 2 (CZ24 ∷ []) (wl0305 (lit c4)) ▸
       at 11 2 (K2⁻ ∷ X4 ∷ []) (sym (wl0738 (lit c4))) ▸
       at 10 2 (K2⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0210243143 c4) ▸ done

  b77 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ K2 ∷ CZ24 ∷ X4 ∷ K2⁻ ∷ Bx2-0413 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b77 = at 9 2 (K2⁻ ∷ X4 ∷ []) (sym (wl0738 (lit c4))) ▸
       at 7 3 (CX42 ∷ []) (sym (wl0737 (lit c4))) ▸
       at 9 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 4 (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0719 (lit c4))) ▸
       at 14 4 (CS34 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0356 c4)) ▸ done

  b78 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CCZ234 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b78 = at 11 4 (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0719 (lit c4))) ▸
       at 8 4 (CS34 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0356 c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 10 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 4 5 (CCZ234 ∷ []) (sym (wl0600 (lit c4))) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸ done

  b79 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CCZ234 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ [])
  b79 = at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 6 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 7 2 (K3⁻ ∷ X4 ∷ []) (sym (wl0740 (lit c4))) ▸
       at 6 2 (K3⁻ ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0210243143 c4) ▸
       at 5 2 (K3⁻ ∷ X4 ∷ []) (sym (wl0740 (lit c4))) ▸
       at 3 3 (Toff324 ∷ []) (wl0364 (lit c4)) ▸ done

  b80 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b80 = at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 2 (CS13⁻ ∷ X4 ∷ []) (sym (wl0742 (lit c4))) ▸
       at 6 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 2 (Sb⁻0-1-3-2 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at0210243143 c4) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 2 (CS13⁻ ∷ X4 ∷ []) (sym (wl0742 (lit c4))) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- beta-T @13213442: 8 steps
lem-beta-T-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-beta-T-at13213442 c4 = run b0
  where
  b0 : Chain (Bx0-3142 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-2143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3142⟩ (lit c4)) ▸
       at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at12213443 c4) ▸
       at 0 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 2 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 4 2 [] (wl0006 (lit c4)) ▸ done


-- beta-T @133441: 8 steps
lem-beta-T-at133441 : Ws → ⟪ (Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-beta-T-at133441 c4 = run b0
  where
  b0 : Chain (Bx0-3241 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-3142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3241⟩ (lit c4)) ▸
       at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at13213442 c4) ▸
       at 0 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 2 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(1;0;3;4): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb1-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-4 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb1-0-3-4 ∷ []) (Sb1-0-3-4 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS03 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS02-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb1-0-3-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(1;0;3;4): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb⁻1-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-4 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb⁻1-0-3-4 ∷ []) (Sb⁻1-0-3-4 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS03⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb⁻1-0-3-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ143 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ143 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at2332 c4) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ143 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at243243 c4) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ143 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at0110243243 c4) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4)) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(1;0;3;4) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb1-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-4 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb1-0-2-4 ∷ []) (Sb1-0-2-4 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Sb1-0-3-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·2·4⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-3-4 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩ c4) ▸
       at 0 2 (Sb1-0-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·3·4⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(1;0;3;4) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-2-3 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb1-0-2-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·2·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-2-4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2332 c4) ▸
       at 0 2 (Sb1-0-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·2·4⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(1;0;3;4) @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-3 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-2-3 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb1-0-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·2·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-2-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 c4) ▸
       at 0 2 (Sb0-1-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·2·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(1;0;3;4) @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb0-2-1-3 ∷ []) (Sb0-2-1-3 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (Sb0-1-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·1·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0110243243 c4) ▸
       at 0 2 (Sb0-2-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·2·3⟩ (lit c4)) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(1;0;3;4) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb⁻1-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-4 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb⁻1-0-2-4 ∷ []) (Sb⁻1-0-2-4 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Sb⁻1-0-3-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·2·4⟩ (lit c4)) ▸
       at 1 2 (Sb⁻1-0-3-4 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩ c4) ▸
       at 0 2 (Sb⁻1-0-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·3·4⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(1;0;3;4) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb⁻1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-2-3 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb⁻1-0-2-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·2·3⟩ (lit c4)) ▸
       at 1 2 (Sb⁻1-0-2-4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2332 c4) ▸
       at 0 2 (Sb⁻1-0-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·2·4⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(1;0;3;4) @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-3 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb⁻1-0-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·2·3⟩ (lit c4)) ▸
       at 1 2 (Sb⁻1-0-2-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 c4) ▸
       at 0 2 (Sb⁻0-1-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·2·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(1;0;3;4) @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-2-1-3 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (Sb⁻0-1-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·1·3⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0110243243 c4) ▸
       at 0 2 (Sb⁻0-2-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·1·2·3⟩ (lit c4)) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


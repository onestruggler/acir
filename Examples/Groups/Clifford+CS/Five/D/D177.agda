{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D177 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0037 ; wl0044 ; wl0047 ; wl0057 ; wl0058 ; wl0085 ; wl0091 ; wl0096 ; wl0097 ; wl0099 ; wl0113 ; wl0119 ; wl0120 ; wl0190 ; wl0260 ; wl0283 ; wl0353 ; wl0548 ; wl0560 ; wl0724 ; wl0725 ; wl0726 ; wl0727 ; wl0728 ; wl0743 ; wl0744 ; wl0745 ; wl0746 ; wl0747 ; wl0748 ; wl0749 ; wl0750 ; wl0751 ; wl0752 ; wl0753 ; wl0754 ; wl0755 ; wl0756 ; wl0757 ; wl0758 ; wl0759 ; wl0760 ; wl0761 ; wl0762 ; wl0763 ; wl0764 ; wl0765 ; wl0766 ; wl0767 ; wl0768 ; wp0348 ; wp0349 ; wp0365 ; wp0366 ; wp0387 ; wp0388 ; wp0389 ; wp0390 ; wp0391 ; wp0392 ; wp0393 ; wp0394 ; wp0395 ; wp0396 ; wp0397 ; wp0398 ; wp0399 ; wp0400 ; wp0401 ; wp0402 ; wp0403 ; wp0404 ; wp0405 ; wp0406)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-T-beta ; lem-beta-T-at243243 ; lem-c124-beta-at0310213442 ; lem-sym12 ; lem-sym12-at1221 ; lem-sym23 ; lem-sym34-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym12-at233442 ; lem-sym23-at12213443 ; lem-sym23-at12243143 ; lem-sym23-at2332 ; lem-sym34-at12213443 ; lem-sym34-at2332 ; lem-sym34-at233442)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F0-at132132 ; lem-X1-beta-at0214203143 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CS13-at243243 ; lem-sym12-at13213442)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at243243 ; lem-beta-T-at0210233441 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.D161 using (lem-auto-CCZ012-∣-CCZ342-at04103143)
open import Examples.Groups.Clifford+CS.Five.D.D164 using (lem-T-beta-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D170 using (lem-auto-CCZ012-∣-TOFF342)
open import Examples.Groups.Clifford+CS.Five.D.D173 using (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at3443 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D175 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D176 using (lem-F4-CS01ᵖ0∣CS23ᵖ1-part0)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-2-TOFF201)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-TOFF403 ; lem-nat-2-BOX⟨3·4012⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-TOFF413 ; lem-nat-2-BOX⟨2·4013⟩ ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-1-TOFF401 ; lem-nat-2-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-CS01 ; lem-nat-1-CS02 ; lem-nat-2-CS12 ; lem-nat-2-CS13)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-2-BOX⟨0·1432⟩ ; lem-nat-2-CS02 ; lem-nat-2-SBOX⟨1·0·2·3⟩ ; lem-nat-2-SBOX⟨1·0·43·2⟩ ; lem-nat-2-SBOXd⟨1·0·2·3⟩ ; lem-nat-2-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨0·3142⟩ ; lem-nat-0-BOX⟨1·3042⟩ ; lem-nat-1-BOX⟨1·3042⟩ ; lem-nat-1-BOX⟨2·3041⟩ ; lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-1-TOFF402 ; lem-nat-2-BOX⟨0·1423⟩ ; lem-nat-2-CS03)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-SBOX⟨0·2·43·1⟩ ; lem-nat-2-SBOX⟨0·1·42·3⟩ ; lem-nat-2-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-BOX⟨3·0142⟩ ; lem-nat-1-BOX⟨3·0241⟩ ; lem-nat-2-SBOX⟨1·0·3·2⟩ ; lem-nat-2-SBOX⟨1·0·42·3⟩ ; lem-nat-2-SBOXd⟨1·0·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-BOX⟨4·0123⟩ ; lem-nat-0-BOX⟨4·1023⟩ ; lem-nat-1-BOX⟨4·0123⟩ ; lem-nat-1-BOX⟨4·0213⟩ ; lem-nat-1-BOX⟨4·1032⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨3·0142⟩ ; lem-nat-0-BOX⟨3·1042⟩ ; lem-nat-0-SBOX⟨0·1·43·2⟩ ; lem-nat-1-BOX⟨3·1042⟩ ; lem-nat-1-BOX⟨3·2041⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-0-SBOX⟨2·0·43·1⟩ ; lem-nat-1-BOX⟨4·2031⟩ ; lem-nat-1-SBOX⟨2·1·43·0⟩ ; lem-nat-2-BOX⟨2·3041⟩ ; lem-nat-2-BOX⟨3·2041⟩ ; lem-nat-2-BOX⟨4·1023⟩ ; lem-nat-2-BOX⟨4·1032⟩ ; lem-nat-3-BOX⟨3·2041⟩ ; lem-nat-3-BOX⟨4·2031⟩)
-- F4 CS01^0|CS23^1 part1: 392 steps
lem-F4-CS01ᵖ0∣CS23ᵖ1-part1 : Ws → ⟪ (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣CS23ᵖ1-part1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (run b48))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 1 (CS03⁻ ∷ []) (refl) ▸
       at 16 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0389 c4)) ▸
       at 29 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 13 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0747 (lit c4))) ▸
       at 11 1 (CS03 ∷ []) (refl) ▸
       at 10 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0390 c4)) ▸ done

  b1 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b1 = at 23 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 7 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0747 (lit c4))) ▸
       at 5 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸
       at 5 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 5 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b2 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b2 = at 13 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (sym (wl0748 (lit c4))) ▸
       at 12 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 11 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 10 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 11 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (sym (wp0391 c4)) ▸
       at 14 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 13 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 12 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b3 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b3 = at 15 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 14 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 13 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 15 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 20 4 (CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (sym (wl0749 (lit c4))) ▸
       at 18 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4)) ▸ done

  b4 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b4 = at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 25 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 28 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 29 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0392 c4)) ▸
       at 26 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0393 c4)) ▸
       at 23 4 (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wl0750 (lit c4))) ▸
       at 20 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0393 c4)) ▸ done

  b5 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ K2 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b5 = at 17 4 (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wl0751 (lit c4))) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 23 2 [] (wl0283 (lit c4)) ▸
       at 19 5 (CCZ023 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 14 4 (CS14⁻ ∷ X4 ∷ K2 ∷ X4 ∷ []) (sym (wl0752 (lit c4))) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸ done

  b6 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ K2 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ X4 ∷ Toff203 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b6 = at 18 2 [] (wl0283 (lit c4)) ▸
       at 16 3 (Toff203 ∷ []) (wl0548 (lit c4)) ▸
       at 17 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 16 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 15 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 18 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 17 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 16 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b7 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ X4 ∷ Toff203 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ Toff203 ∷ CS13 ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b7 = at 17 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (sym (wp0391 c4)) ▸
       at 20 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 19 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 18 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 21 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 20 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 19 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 22 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸ done

  b8 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ Toff203 ∷ CS13 ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ K1 ∷ Toff203 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b8 = at 21 2 (CS13 ∷ Toff203 ∷ []) (sym (wl0753 (lit c4))) ▸
       at 20 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 23 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 22 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 21 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 7 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (sym (wl0748 (lit c4))) ▸
       at 6 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 5 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸ done

  b9 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ K1 ∷ Toff203 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ Toff203 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b9 = at 4 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 5 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (sym (wp0391 c4)) ▸
       at 8 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 7 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 6 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 9 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 8 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 7 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b10 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ Toff203 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b10 = at 9 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 4 (CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (sym (wl0749 (lit c4))) ▸
       at 12 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4)) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b11 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b11 = at 22 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0392 c4)) ▸
       at 20 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0393 c4)) ▸
       at 17 4 (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wl0750 (lit c4))) ▸
       at 14 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0393 c4)) ▸
       at 11 4 (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wl0751 (lit c4))) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸ done

  b12 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b12 = at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 13 5 (CCZ023 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 8 4 (CS14⁻ ∷ X4 ∷ K2 ∷ X4 ∷ []) (sym (wl0752 (lit c4))) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 10 3 (Toff203 ∷ []) (wl0548 (lit c4)) ▸
       at 11 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b13 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ K1⁻ ∷ Toff203 ∷ X4 ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b13 = at 10 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 9 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 12 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 11 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 10 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 11 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (sym (wp0391 c4)) ▸
       at 14 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 13 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸ done

  b14 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ K1⁻ ∷ Toff203 ∷ X4 ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b14 = at 12 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 15 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 14 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 13 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 16 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 15 2 (CS13 ∷ Toff203 ∷ []) (sym (wl0753 (lit c4))) ▸
       at 14 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 17 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b15 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b15 = at 16 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 15 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 17 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸
       at 17 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸
       at 17 1 (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4) ▸ done

  b16 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b16 = at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 17 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 3 2 [] (wl0260 (lit c4)) ▸
       at 4 2 [] (wl0260 (lit c4)) ▸
       at 5 2 [] (wl0260 (lit c4)) ▸ done

  b17 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Sb2-0-41-3 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b17 = at 6 2 [] (wl0260 (lit c4)) ▸
       at 2 5 (CCZ134 ∷ []) (sym (wl0190 (lit c4))) ▸
       at 1 3 (Toff134 ∷ []) (wl0743 (lit c4)) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 4 2 (CS12 ∷ X4 ∷ []) (sym (wl0754 (lit c4))) ▸
       at 4 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 3 2 (Sb0-2-1-3 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0210243143 c4) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸ done

  b18 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Sb2-0-41-3 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b18 = at 2 2 (CS12 ∷ X4 ∷ []) (sym (wl0754 (lit c4))) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 6 1 (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (sym (wl0743 (lit c4))) ▸
       at 7 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl0190 (lit c4)) ▸
       at 8 0 (K1⁻ ∷ K1 ∷ []) (sym (wl0260 (lit c4))) ▸
       at 11 0 (K1⁻ ∷ K1 ∷ []) (sym (wl0260 (lit c4))) ▸
       at 14 0 (K1⁻ ∷ K1 ∷ []) (sym (wl0260 (lit c4))) ▸
       at 17 0 (K1⁻ ∷ K1 ∷ []) (sym (wl0260 (lit c4))) ▸ done

  b19 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b19 = at 4 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 1 (CS03⁻ ∷ []) (refl) ▸
       at 15 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0387 c4)) ▸
       at 19 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b20 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b20 = at 12 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0744 (lit c4))) ▸
       at 10 1 (CS03 ∷ []) (refl) ▸
       at 9 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0388 c4)) ▸
       at 13 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 6 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0744 (lit c4))) ▸
       at 4 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸
       at 4 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 4 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸ done

  b21 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b21 = at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (sym (wl0745 (lit c4))) ▸
       at 11 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 10 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 9 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 11 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸ done

  b22 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b22 = at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 4 (CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (sym (wl0725 (lit c4))) ▸
       at 14 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4)) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b23 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b23 = at 25 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0365 c4)) ▸
       at 22 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0366 c4)) ▸
       at 19 4 (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wl0726 (lit c4))) ▸
       at 16 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0366 c4)) ▸
       at 13 4 (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wl0727 (lit c4))) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸ done

  b24 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ K1⁻ ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b24 = at 19 2 [] (wl0283 (lit c4)) ▸
       at 15 5 (CCZ023 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 10 4 (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) (sym (wl0728 (lit c4))) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 12 3 (Toff203 ∷ []) (wl0548 (lit c4)) ▸
       at 13 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 12 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸ done

  b25 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ K1⁻ ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b25 = at 11 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 6 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (sym (wl0745 (lit c4))) ▸
       at 5 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 4 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 3 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 5 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b26 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b26 = at 10 4 (CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (sym (wl0725 (lit c4))) ▸
       at 8 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4)) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0365 c4)) ▸
       at 16 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0366 c4)) ▸ done

  b27 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b27 = at 13 4 (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wl0726 (lit c4))) ▸
       at 10 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0366 c4)) ▸
       at 7 4 (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wl0727 (lit c4))) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 9 5 (CCZ023 ∷ []) (sym (wl0560 (lit c4))) ▸ done

  b28 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b28 = at 4 4 (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) (sym (wl0728 (lit c4))) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 6 3 (Toff203 ∷ []) (wl0548 (lit c4)) ▸
       at 7 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 6 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 5 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸ done

  b29 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b29 = at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 7 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸
       at 7 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸
       at 7 1 (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸ done

  b30 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ [])
  b30 = at 11 2 [] (wl0283 (lit c4)) ▸
       at 7 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 7 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 1 (CS03⁻ ∷ []) (refl) ▸ done

  b31 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0431 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b31 = at 18 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0389 c4)) ▸
       at 31 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 15 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0747 (lit c4))) ▸
       at 13 1 (CS03 ∷ []) (refl) ▸
       at 12 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0390 c4)) ▸
       at 25 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 9 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0747 (lit c4))) ▸
       at 7 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸ done

  b32 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0431 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ K1 ∷ Toff203 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b32 = at 7 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 7 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (sym (wl0748 (lit c4))) ▸
       at 14 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 13 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸ done

  b33 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ K1 ∷ Toff203 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ Toff203 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b33 = at 12 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 13 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (sym (wp0391 c4)) ▸
       at 16 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 15 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 14 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 17 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 16 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 15 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b34 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ Toff203 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b34 = at 17 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 4 (CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (sym (wl0749 (lit c4))) ▸
       at 20 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4)) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b35 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b35 = at 30 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 31 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0392 c4)) ▸
       at 28 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0393 c4)) ▸
       at 25 4 (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wl0750 (lit c4))) ▸
       at 22 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0393 c4)) ▸
       at 19 4 (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wl0751 (lit c4))) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 23 2 [] (wl0283 (lit c4)) ▸ done

  b36 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b36 = at 24 2 [] (wl0283 (lit c4)) ▸
       at 25 2 [] (wl0283 (lit c4)) ▸
       at 21 5 (CCZ023 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 16 4 (CS14⁻ ∷ X4 ∷ K2 ∷ X4 ∷ []) (sym (wl0752 (lit c4))) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 18 3 (Toff203 ∷ []) (wl0548 (lit c4)) ▸
       at 19 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b37 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ K1⁻ ∷ Toff203 ∷ X4 ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b37 = at 18 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 17 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 20 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 19 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 18 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 19 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (sym (wp0391 c4)) ▸
       at 22 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 21 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸ done

  b38 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ K1⁻ ∷ Toff203 ∷ X4 ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b38 = at 20 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 23 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 22 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 21 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 24 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 23 2 (CS13 ∷ Toff203 ∷ []) (sym (wl0753 (lit c4))) ▸
       at 22 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 25 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b39 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b39 = at 24 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 23 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 9 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (sym (wl0748 (lit c4))) ▸
       at 8 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 7 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 6 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 7 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (sym (wp0391 c4)) ▸
       at 10 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b40 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b40 = at 9 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 8 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 11 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 10 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 9 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 11 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b41 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b41 = at 16 4 (CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (sym (wl0749 (lit c4))) ▸
       at 14 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4)) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 25 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0392 c4)) ▸
       at 22 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0393 c4)) ▸ done

  b42 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b42 = at 19 4 (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wl0750 (lit c4))) ▸
       at 16 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0393 c4)) ▸
       at 13 4 (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wl0751 (lit c4))) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 15 5 (CCZ023 ∷ []) (sym (wl0560 (lit c4))) ▸ done

  b43 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ K1 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b43 = at 10 4 (CS14⁻ ∷ X4 ∷ K2 ∷ X4 ∷ []) (sym (wl0752 (lit c4))) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 12 3 (Toff203 ∷ []) (wl0548 (lit c4)) ▸
       at 13 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 12 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 11 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 14 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b44 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ K1 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ K1 ∷ Toff203 ∷ X4 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b44 = at 13 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 12 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 13 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (sym (wp0391 c4)) ▸
       at 16 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 15 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 14 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 17 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 16 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸ done

  b45 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ K1 ∷ Toff203 ∷ X4 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b45 = at 15 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 18 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 17 2 (CS13 ∷ Toff203 ∷ []) (sym (wl0753 (lit c4))) ▸
       at 16 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 19 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 18 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 17 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸ done

  b46 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b46 = at 21 2 [] (wl0283 (lit c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 19 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸
       at 19 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸
       at 19 1 (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸ done

  b47 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ [])
  b47 = at 23 2 [] (wl0283 (lit c4)) ▸
       at 19 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 5 2 [] (wl0260 (lit c4)) ▸
       at 6 2 [] (wl0260 (lit c4)) ▸
       at 7 2 [] (wl0260 (lit c4)) ▸
       at 8 2 [] (wl0260 (lit c4)) ▸
       at 4 5 (CCZ134 ∷ []) (sym (wl0190 (lit c4))) ▸
       at 3 3 (Toff134 ∷ []) (wl0743 (lit c4)) ▸ done

  b48 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b48 = at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 6 2 (CS12⁻ ∷ X4 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 6 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 2 (Sb⁻0-2-1-3 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0210243143 c4) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ X4 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F4 CS01^0|CS23^1: 2 steps
lem-F4-CS01ᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣CS23ᵖ1 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (lem-F4-CS01ᵖ0∣CS23ᵖ1-part0 c4) ▸
       at 0 30 (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣CS23ᵖ1-part1 c4) ▸ done


-- auto CS01 | SBOX(2;0;31;4) @12213443: 7 steps
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at12213443 : Ws → ⟪ (CS02 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at12213443 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4)) ▸
       at 2 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb2-0-41-3 ∷ CS01 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at3443 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- c124-beta @03103441: 7 steps
lem-c124-beta-at03103441 : Ws → ⟪ (CCZ012 ∷ Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ CCZ012 ∷ []) ⟫ʷ
lem-c124-beta-at03103441 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-0241 ∷ []) (Bx3-0241 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 2 2 (Bx3-0142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0241⟩ (lit c4)) ▸
       at 1 2 (Bx3-0142 ∷ CCZ012 ∷ []) (lem-c124-beta-at0310213442 c4) ▸
       at 0 2 (Bx3-0241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0142⟩ (lit c4)) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- X1-beta @0314203142: 8 steps
lem-X1-beta-at0314203142 : Ws → ⟪ (X4 ∷ Bx3-4012 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx3-4012 ∷ []) ⟫ʷ
lem-X1-beta-at0314203142 c4 = run b0
  where
  b0 : Chain (X4 ∷ Bx3-4012 ∷ X4 ∷ []) (CCZ012 ∷ Bx3-4012 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 2 2 (Bx2-4013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4012⟩ (lit c4)) ▸
       at 3 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 1 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 1 2 (Bx3-4012 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4013⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | K0 @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2442 : Ws → ⟪ (Sb0-1-43-2 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ K0 ∷ []) (K0 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 1 2 (K0 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at243243 c4) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | K4 @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2442 : Ws → ⟪ (Sb0-1-43-2 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ K2 ∷ []) (K2 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 (lit c4))) ▸
       at 1 2 (K3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at243243 c4) ▸
       at 0 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 (lit c4))) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto TOFF012 | BOX(0;3142): 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩ : Ws → ⟪ (Toff012 ∷ Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩ c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Bx0-3142 ∷ []) (Bx0-3142 ∷ Toff012 ∷ [])
  b0 = at 1 1 (Bx0-1342 ∷ []) (lem-sym12-at13213442 c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym34-at233442 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 2 (Bx0-1234 ∷ Toff012 ∷ []) (lem-T-beta c4) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym12-at233442 c4) ▸ done


-- auto CCZ012 | CCZ342 @0410233142: 7 steps
lem-auto-CCZ012-∣-CCZ342-at0410233142 : Ws → ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at0410233142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at04103143 c4) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 (lit c4))) ▸
       at 1 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto TOFF012 | BOX(0;3142) @0110: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0110 : Ws → ⟪ (Toff102 ∷ Bx1-3042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3042 ∷ Toff102 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0110 c4 = run b0
  where
  b0 : Chain (Toff102 ∷ Bx1-3042 ∷ []) (Bx1-3042 ∷ Toff102 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 (lit c4)) ▸
       at 2 2 (Bx0-3142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3042⟩ (lit c4)) ▸
       at 1 2 (Bx0-3142 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩ c4) ▸
       at 0 2 (Bx1-3042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3142⟩ (lit c4)) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto TOFF012 | BOX(0;3142) @021021: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at021021 : Ws → ⟪ (Toff201 ∷ Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ Toff201 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at021021 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Bx2-3041 ∷ []) (Bx2-3041 ∷ Toff201 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 (lit c4)) ▸
       at 2 2 (Bx1-3042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3041⟩ (lit c4)) ▸
       at 1 2 (Bx1-3042 ∷ Toff102 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0110 c4) ▸
       at 0 2 (Bx2-3041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3042⟩ (lit c4)) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto TOFF012 | BOX(0;3142) @03102132: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at03102132 : Ws → ⟪ (Toff301 ∷ Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ Toff301 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at03102132 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Bx3-2041 ∷ []) (Bx3-2041 ∷ Toff301 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 (lit c4)) ▸
       at 2 2 (Bx2-3041 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·2041⟩ (lit c4)) ▸
       at 1 2 (Bx2-3041 ∷ Toff201 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at021021 c4) ▸
       at 0 2 (Bx3-2041 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·3041⟩ (lit c4)) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto TOFF012 | BOX(0;3142) @0410213243: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0410213243 : Ws → ⟪ (Toff401 ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ Toff401 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (Toff401 ∷ Bx4-2031 ∷ []) (Bx4-2031 ∷ Toff401 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 (lit c4)) ▸
       at 2 2 (Bx3-2041 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·2031⟩ (lit c4)) ▸
       at 1 2 (Bx3-2041 ∷ Toff301 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at03102132 c4) ▸
       at 0 2 (Bx4-2031 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·2041⟩ (lit c4)) ▸
       at 1 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto TOFF012 | BOX(0;3142) @04103143: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at04103143 : Ws → ⟪ (Toff402 ∷ Bx4-1032 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1032 ∷ Toff402 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at04103143 c4 = run b0
  where
  b0 : Chain (Toff402 ∷ Bx4-1032 ∷ []) (Bx4-1032 ∷ Toff402 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 (lit c4)) ▸
       at 2 2 (Bx4-2031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·1032⟩ (lit c4)) ▸
       at 1 2 (Bx4-2031 ∷ Toff401 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0410213243 c4) ▸
       at 0 2 (Bx4-1032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·2031⟩ (lit c4)) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto TOFF012 | BOX(0;3142) @0410233142: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0410233142 : Ws → ⟪ (Toff403 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ Toff403 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0410233142 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ Bx4-1023 ∷ []) (Bx4-1023 ∷ Toff403 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 (lit c4)) ▸
       at 2 2 (Bx4-1032 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·1023⟩ (lit c4)) ▸
       at 1 2 (Bx4-1032 ∷ Toff402 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at04103143 c4) ▸
       at 0 2 (Bx4-1023 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·1032⟩ (lit c4)) ▸
       at 1 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto TOFF012 | BOX(0;3142) @04233042: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at04233042 : Ws → ⟪ (Toff413 ∷ Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ Toff413 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at04233042 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ Bx4-0123 ∷ []) (Bx4-0123 ∷ Toff413 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 (lit c4)) ▸
       at 2 2 (Bx4-1023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0123⟩ (lit c4)) ▸
       at 1 2 (Bx4-1023 ∷ Toff403 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0410233142 c4) ▸
       at 0 2 (Bx4-0123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1023⟩ (lit c4)) ▸
       at 1 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto TOFF012 | BOX(0;3142) @0412233041: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0412233041 : Ws → ⟪ (Toff423 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Toff423 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0412233041 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Toff423 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (wl0091 (lit c4)) ▸
       at 2 2 (Bx4-0123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0213⟩ (lit c4)) ▸
       at 1 2 (Bx4-0123 ∷ Toff413 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at04233042 c4) ▸
       at 0 2 (Bx4-0213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0123⟩ (lit c4)) ▸
       at 1 2 (Toff423 ∷ Sw12 ∷ []) (wl0085 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | TOFF342 @3443: 7 steps
lem-auto-CCZ012-∣-TOFF342-at3443 : Ws → ⟪ (CCZ012 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at3443 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (Toff324 ∷ Sw34 ∷ []) (wl0120 (lit c4)) ▸
       at 1 2 (Toff324 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF342 c4) ▸
       at 0 2 (Toff423 ∷ Sw34 ∷ []) (wl0119 (lit c4)) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS13 @2442: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS13-at2442 : Ws → ⟪ (Bx0-1432 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx0-1432 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS13-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ CS13 ∷ []) (CS13 ∷ Bx0-1432 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4)) ▸
       at 2 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 (lit c4)) ▸
       at 1 2 (CS12 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at243243 c4) ▸
       at 0 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 (lit c4)) ▸
       at 1 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ134 @2442: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2442 : Ws → ⟪ (Bx0-1432 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1432 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1432 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4)) ▸
       at 2 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at243243 c4) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 (lit c4))) ▸
       at 1 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CS01 | SBOX(2;0;31;4) @13213442: 7 steps
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at13213442 : Ws → ⟪ (CS03 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ CS03 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at13213442 c4 = run b0
  where
  b0 : Chain (CS03 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ CS03 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 (lit c4)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ CS02 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at12213443 c4) ▸
       at 0 2 (Sb1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ143 @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at2442 : Ws → ⟪ (Sb0-1-43-2 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at243243 c4) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 (lit c4))) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(1;0;3;4) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2442 : Ws → ⟪ (Sb0-1-43-2 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Sb1-0-3-2 ∷ []) (Sb1-0-3-2 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 (Sb1-0-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-2-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 c4) ▸
       at 0 2 (Sb1-0-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·2·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(1;0;3;4) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2442 : Ws → ⟪ (Sb0-1-43-2 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻1-0-3-2 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 (Sb⁻1-0-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 1 2 (Sb⁻1-0-2-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 c4) ▸
       at 0 2 (Sb⁻1-0-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·2·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- F0 @01132032: 5 steps
lem-F0-at01132032 : Ws → ⟪ (Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-43-0 ∷ []) ⟫ʷ
lem-F0-at01132032 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ []) (Sb2-1-43-0 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 1 (Sb2-0-43-1 ∷ []) (lem-F0-at132132 c4) ▸
       at 0 2 (Sb2-1-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·43·1⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | TOFF042: 9 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF042 : Ws → ⟪ (Bx0-1234 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ Toff024 ∷ []) (Toff024 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (Toff024 ∷ []) (wp0394 c4) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 0 2 (Toff024 ∷ Bx0-2413 ∷ []) (sym (lem-T-beta-at12243143 c4)) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done

  b1 : Chain (Toff024 ∷ Bx0-1234 ∷ []) (Toff024 ∷ Bx0-1234 ∷ [])
  b1 = at 0 1 (Toff024 ∷ []) (wp0394 c4) ▸ done


-- c124-beta @03203442: 7 steps
lem-c124-beta-at03203442 : Ws → ⟪ (CCZ012 ∷ Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ CCZ012 ∷ []) ⟫ʷ
lem-c124-beta-at03203442 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-1042 ∷ []) (Bx3-1042 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 (lit c4))) ▸
       at 2 2 (Bx3-0142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1042⟩ (lit c4)) ▸
       at 1 2 (Bx3-0142 ∷ CCZ012 ∷ []) (lem-c124-beta-at0310213442 c4) ▸
       at 0 2 (Bx3-1042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0142⟩ (lit c4)) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- c124-beta @0312203441: 7 steps
lem-c124-beta-at0312203441 : Ws → ⟪ (CCZ012 ∷ Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ CCZ012 ∷ []) ⟫ʷ
lem-c124-beta-at0312203441 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-2041 ∷ []) (Bx3-2041 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 2 2 (Bx3-1042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2041⟩ (lit c4)) ▸
       at 1 2 (Bx3-1042 ∷ CCZ012 ∷ []) (lem-c124-beta-at03203442 c4) ▸
       at 0 2 (Bx3-2041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1042⟩ (lit c4)) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F0 @02132031: 5 steps
lem-F0-at02132031 : Ws → ⟪ (Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ []) ⟫ʷ
lem-F0-at02132031 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 1 1 (Sb2-1-43-0 ∷ []) (lem-F0-at01132032 c4) ▸
       at 0 2 (Sb1-2-43-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·43·0⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- F4 CS12^0|iI^1: 30 steps
lem-F4-CS12ᵖ0∣iIᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣iIᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ S4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 1 (CS13⁻ ∷ []) (refl) ▸
       at 12 4 (S4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0756 (lit c4))) ▸
       at 14 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ S4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ S4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b1 = at 9 4 (S4 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0757 (lit c4))) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸
       at 6 4 (S4 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0758 (lit c4))) ▸
       at 8 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 3 4 (S4 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0757 (lit c4))) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ S4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (S4 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b2 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 4 (S4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0395 c4)) ▸
       at 6 4 (S4 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0396 c4)) ▸
       at 3 4 (S4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0395 c4)) ▸
       at 0 4 (S4 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0396 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b3 : Chain (S4 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b3 = at 2 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 2 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- F4 CS12^0|S0^1: 30 steps
lem-F4-CS12ᵖ0∣S0ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣S0ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ []) (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 1 (CS13⁻ ∷ []) (refl) ▸
       at 12 4 (CS04 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wp0397 c4)) ▸
       at 14 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b1 = at 9 4 (CS04 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wp0398 c4)) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸
       at 6 4 (CS04 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wp0399 c4)) ▸
       at 8 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 3 4 (CS04 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wp0398 c4)) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (CS04 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b2 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 4 (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0400 c4)) ▸
       at 6 4 (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0401 c4)) ▸
       at 3 4 (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0400 c4)) ▸
       at 0 4 (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0401 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b3 : Chain (CS04 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b3 = at 2 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 2 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- F4 CS12^0|S1^1: 58 steps
lem-F4-CS12ᵖ0∣S1ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣S1ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 1 (CS13⁻ ∷ []) (refl) ▸
       at 12 4 (CS14 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0759 (lit c4))) ▸
       at 14 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b1 = at 9 4 (CS14 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0760 (lit c4))) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸
       at 6 4 (CS14 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0761 (lit c4))) ▸
       at 8 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 3 4 (CS14 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0760 (lit c4))) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b2 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0353 (lit c4)) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0365 c4)) ▸
       at 18 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸ done

  b3 : Chain (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b3 = at 15 4 (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0348 c4)) ▸
       at 12 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸
       at 9 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0349 c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 11 5 (CCZ023 ∷ []) (sym (wl0353 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b4 = at 6 4 (CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0402 c4)) ▸
       at 4 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0353 (lit c4)) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0365 c4)) ▸
       at 12 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸ done

  b5 : Chain (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b5 = at 9 4 (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0348 c4)) ▸
       at 6 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸
       at 3 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0349 c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 5 5 (CCZ023 ∷ []) (sym (wl0353 (lit c4))) ▸ done

  b6 : Chain (X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (CS14 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b6 = at 0 4 (CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0402 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b7 : Chain (CS14 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b7 = at 6 2 [] (wl0283 (lit c4)) ▸
       at 2 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- F4 CS12^0|S2^1: 30 steps
lem-F4-CS12ᵖ0∣S2ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣S2ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 1 (CS13⁻ ∷ []) (refl) ▸
       at 12 4 (CS24 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 14 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b1 = at 9 4 (CS24 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0764 (lit c4))) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸
       at 6 4 (CS24 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 8 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 3 4 (CS24 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0764 (lit c4))) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (CS24 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b2 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 4 (CS24 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0403 c4)) ▸
       at 6 4 (CS24 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0404 c4)) ▸
       at 3 4 (CS24 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0403 c4)) ▸
       at 0 4 (CS24 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0404 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b3 : Chain (CS24 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b3 = at 2 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 2 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- F4 CS12^0|S3^1: 30 steps
lem-F4-CS12ᵖ0∣S3ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣S3ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ []) (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 1 (CS13⁻ ∷ []) (refl) ▸
       at 12 4 (CS34 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0766 (lit c4))) ▸
       at 14 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b1 = at 9 4 (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0767 (lit c4))) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸
       at 6 4 (CS34 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0768 (lit c4))) ▸
       at 8 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 3 4 (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0767 (lit c4))) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (CS34 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b2 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 4 (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0405 c4)) ▸
       at 6 4 (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0406 c4)) ▸
       at 3 4 (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0405 c4)) ▸
       at 0 4 (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0406 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b3 : Chain (CS34 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b3 = at 2 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 2 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


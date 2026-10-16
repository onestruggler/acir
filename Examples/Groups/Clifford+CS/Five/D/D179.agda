{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D179 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0035 ; wl0037 ; wl0100 ; wl0103 ; wl0138 ; wl0183 ; wl0212 ; wl0283 ; wl0296 ; wl0333 ; wl0351 ; wl0357 ; wl0358 ; wl0550 ; wl0563 ; wl0616 ; wl0779 ; wl0780 ; wl0781 ; wl0782 ; wl0783 ; wl0787 ; wl0788 ; wl0789 ; wl0790 ; wl0791 ; wl0792 ; wl0793 ; wl0794 ; wl0795 ; wl0796 ; wl0797 ; wl0798 ; wl0799 ; wl0800 ; wl0801 ; wl0802 ; wl0803 ; wl0804 ; wl0805 ; wl0806 ; wl0807 ; wl0808 ; wl0809 ; wl0810 ; wl0811 ; wl0812 ; wl0813 ; wl0814 ; wl0815 ; wl0816 ; wp0055 ; wp0269 ; wp0285 ; wp0351 ; wp0352 ; wp0411 ; wp0412 ; wp0413 ; wp0414 ; wp0415 ; wp0416 ; wp0417 ; wp0418)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0 ; lem-beta-T-at13243142 ; lem-beta-inv-at243243 ; lem-sym12 ; lem-sym12-at0314203142 ; lem-sym12-at1221 ; lem-sym12-at14213243 ; lem-sym23-at1221 ; lem-sym23-at14213243 ; lem-sym34 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-Cz-beta-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 ; lem-sym12-at243243 ; lem-sym23-at122331 ; lem-sym23-at243243 ; lem-sym23-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-SBsym-at0113203442 ; lem-X1-beta-at14213243 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CS13-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at233442 ; lem-sym23-at233442 ; lem-sym23-at2442 ; lem-sym34-at243243 ; lem-sym34-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D089 using (lem-sym12-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D164 using (lem-T-beta-at2332 ; lem-sym23-at0312203441 ; lem-sym23-at0312243041)
open import Examples.Groups.Clifford+CS.Five.D.D166 using (lem-T312-beta-at1441 ; lem-sym23-at143143 ; lem-sym34-at143143 ; lem-sym34-at1441)
open import Examples.Groups.Clifford+CS.Five.D.D171 using (lem-T312-beta-at133441 ; lem-auto-BOX⟨0·1234⟩-∣-CSd21 ; lem-auto-CCZ012-∣-BOX⟨3·0412⟩)
open import Examples.Groups.Clifford+CS.Five.D.D175 using (lem-beta-T-at133441)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-X1-beta-at0314203142 ; lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at12213443 ; lem-c124-beta-at0312203441)
open import Examples.Groups.Clifford+CS.Five.D.D178 using (lem-auto-CCZ012-∣-SBOX⟨0·1·32·4⟩-at3443 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩-at243243)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-1-BOX⟨0·1324⟩ ; lem-nat-1-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-1-TOFF023)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-BOX⟨0·2314⟩ ; lem-nat-2-CSd12 ; lem-nat-2-CSd13)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-1-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-SBOX⟨2·1·40·3⟩ ; lem-nat-1-SBOX⟨3·1·40·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-0-SBOX⟨2·0·41·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-1-BOX⟨0·3421⟩ ; lem-nat-2-BOX⟨0·2431⟩ ; lem-nat-2-BOX⟨0·3241⟩ ; lem-nat-3-BOX⟨0·2341⟩ ; lem-nat-3-BOX⟨0·2431⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-comm-SBOX⟨0·1·2·3⟩-TOFF034 ; lem-comm-SBOXd⟨0·1·2·3⟩-TOFF034 ; lem-nat-1-SBOX⟨3·2·40·1⟩ ; lem-nat-2-BOX⟨0·2341⟩ ; lem-nat-2-BOX⟨0·3421⟩ ; lem-nat-2-SBOX⟨2·1·40·3⟩ ; lem-nat-2-SBOX⟨3·1·40·2⟩)
-- F4 CS12^0|CS01^1: 510 steps
lem-F4-CS12ᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣CS01ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (trans (run b62) (run b63)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Bx3-0412 ∷ Sb0-1-42-3 ∷ CCZ012 ∷ X4 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b0 = at 3 1 (Sb3-0-41-2 ∷ []) (lem-F0 c4) ▸
       at 3 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 2 3 (CCZ012 ∷ Bx3-4012 ∷ []) (lem-X1-beta-at0314203142 c4) ▸
       at 3 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 2 2 (Bx3-0412 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩ c4) ▸
       at 1 2 (Bx3-0412 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩-at243243 c4) ▸ done

  b1 : Chain (X4 ∷ Bx3-0412 ∷ Sb0-1-42-3 ∷ CCZ012 ∷ X4 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ X4 ∷ Sb0-1-42-3 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b1 = at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 1 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 0 3 (CCZ012 ∷ Bx3-4012 ∷ []) (lem-X1-beta-at0314203142 c4) ▸
       at 1 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 0 2 (Bx3-0412 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩ c4) ▸
       at 4 2 (X4 ∷ CCZ012 ∷ []) (wl0787 (lit c4)) ▸
       at 1 2 (X4 ∷ CCZ012 ∷ []) (wl0787 (lit c4)) ▸
       at 2 2 (Sb0-1-42-3 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨0·1·32·4⟩-at3443 c4) ▸ done

  b2 : Chain (Bx3-0412 ∷ X4 ∷ Sb0-1-42-3 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b2 = at 3 2 (X4 ∷ CCZ012 ∷ []) (wl0787 (lit c4)) ▸
       at 4 2 [] (wl0183 (lit c4)) ▸
       at 4 1 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (sym (wl0563 (lit c4))) ▸
       at 5 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0788 (lit c4)) ▸
       at 6 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 9 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 12 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 15 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸ done

  b3 : Chain (Bx3-0412 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b3 = at 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 1 (CS13⁻ ∷ []) (refl) ▸
       at 13 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0789 (lit c4))) ▸
       at 17 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b4 : Chain (Bx3-0412 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b4 = at 10 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0790 (lit c4))) ▸
       at 8 1 (CS13 ∷ []) (refl) ▸
       at 7 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0791 (lit c4))) ▸
       at 11 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0790 (lit c4))) ▸
       at 2 1 (Bx0-1432 ∷ []) (lem-sym34-at243243 c4) ▸
       at 2 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 2 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4) ▸ done

  b5 : Chain (Bx3-0412 ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ CCZ013 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b5 = at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (sym (wp0412 c4)) ▸
       at 9 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 8 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 7 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 9 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (sym (wl0780 (lit c4))) ▸ done

  b6 : Chain (Bx3-0412 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ CCZ013 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b6 = at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 4 (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0781 (lit c4))) ▸
       at 12 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0333 (lit c4)) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b7 : Chain (Bx3-0412 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b7 = at 23 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0411 c4)) ▸
       at 20 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wl0782 (lit c4))) ▸
       at 17 4 (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0351 c4)) ▸
       at 14 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wl0782 (lit c4))) ▸
       at 11 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0352 c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸ done

  b8 : Chain (Bx3-0412 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ K2⁻ ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b8 = at 17 2 [] (wl0283 (lit c4)) ▸
       at 13 5 (CCZ013 ∷ []) (sym (wl0333 (lit c4))) ▸
       at 8 4 (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0783 (lit c4))) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 10 3 (Toff013 ∷ []) (wl0780 (lit c4)) ▸
       at 11 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 10 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl0792 (lit c4))) ▸ done

  b9 : Chain (Bx3-0412 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ K2⁻ ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b9 = at 9 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 4 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (sym (wp0412 c4)) ▸
       at 3 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 2 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 1 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 3 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (sym (wl0780 (lit c4))) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b10 : Chain (Bx3-0412 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b10 = at 8 4 (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0781 (lit c4))) ▸
       at 6 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0333 (lit c4)) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0411 c4)) ▸
       at 14 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wl0782 (lit c4))) ▸ done

  b11 : Chain (Bx3-0412 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b11 = at 11 4 (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0351 c4)) ▸
       at 8 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wl0782 (lit c4))) ▸
       at 5 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0352 c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 7 5 (CCZ013 ∷ []) (sym (wl0333 (lit c4))) ▸ done

  b12 : Chain (Bx3-0412 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b12 = at 2 4 (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0783 (lit c4))) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 4 3 (Toff013 ∷ []) (wl0780 (lit c4)) ▸
       at 5 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 4 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl0792 (lit c4))) ▸
       at 3 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸ done

  b13 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b13 = at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 5 4 (Bx0-1342 ∷ []) (sym (lem-beta-T-at233442 c4)) ▸
       at 5 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 5 1 (Bx0-1423 ∷ []) (lem-sym34-at2442 c4) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸ done

  b14 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b14 = at 9 2 [] (wl0283 (lit c4)) ▸
       at 5 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 1 (CS13⁻ ∷ []) (refl) ▸ done

  b15 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b15 = at 16 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0793 (lit c4))) ▸
       at 29 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 13 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0794 (lit c4))) ▸
       at 11 1 (CS13 ∷ []) (refl) ▸
       at 10 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0795 (lit c4))) ▸
       at 23 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0794 (lit c4))) ▸
       at 5 1 (Bx0-1432 ∷ []) (lem-sym34-at243243 c4) ▸ done

  b16 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ K2 ∷ Toff013 ∷ X4 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b16 = at 5 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 5 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (sym (wp0413 c4)) ▸
       at 12 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 11 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸ done

  b17 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ K2 ∷ Toff013 ∷ X4 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ Toff013 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b17 = at 10 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 11 4 (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (sym (wp0414 c4)) ▸
       at 14 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 13 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl0792 (lit c4))) ▸
       at 12 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 15 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 14 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 13 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b18 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ Toff013 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b18 = at 15 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (sym (wl0780 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 20 4 (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0796 (lit c4))) ▸
       at 18 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0333 (lit c4)) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 25 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b19 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b19 = at 28 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 29 4 (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0415 c4)) ▸
       at 26 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wl0797 (lit c4))) ▸
       at 23 4 (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0416 c4)) ▸
       at 20 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wl0797 (lit c4))) ▸
       at 17 4 (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0417 c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸ done

  b20 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ Toff013 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b20 = at 22 2 [] (wl0283 (lit c4)) ▸
       at 23 2 [] (wl0283 (lit c4)) ▸
       at 19 5 (CCZ013 ∷ []) (sym (wl0333 (lit c4))) ▸
       at 14 4 (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0798 (lit c4))) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 16 3 (Toff013 ∷ []) (wl0780 (lit c4)) ▸
       at 17 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸ done

  b21 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ Toff013 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ X4 ∷ K2⁻ ∷ Toff013 ∷ X4 ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b21 = at 16 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl0792 (lit c4))) ▸
       at 15 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 18 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 17 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 16 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 17 4 (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (sym (wp0414 c4)) ▸
       at 20 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 19 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl0792 (lit c4))) ▸ done

  b22 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ X4 ∷ K2⁻ ∷ Toff013 ∷ X4 ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ X4 ∷ Toff013 ∷ K2⁻ ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b22 = at 18 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 21 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 20 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 19 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 22 2 (CS12 ∷ X4 ∷ []) (sym (c₃ (CS ↑) (X ↑))) ▸
       at 21 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0799 (lit c4))) ▸
       at 20 2 (CS12 ∷ X4 ∷ []) (sym (c₃ (CS ↑) (X ↑))) ▸
       at 23 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸ done

  b23 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ X4 ∷ Toff013 ∷ K2⁻ ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ X4 ∷ Toff013 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b23 = at 22 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl0792 (lit c4))) ▸
       at 21 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 7 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (sym (wp0413 c4)) ▸
       at 6 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 5 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 4 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 5 4 (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (sym (wp0414 c4)) ▸
       at 8 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸ done

  b24 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ X4 ∷ Toff013 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b24 = at 7 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl0792 (lit c4))) ▸
       at 6 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 9 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 8 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 7 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 9 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (sym (wl0780 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b25 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b25 = at 14 4 (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0796 (lit c4))) ▸
       at 12 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0333 (lit c4)) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 4 (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0415 c4)) ▸
       at 20 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wl0797 (lit c4))) ▸ done

  b26 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b26 = at 17 4 (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0416 c4)) ▸
       at 14 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wl0797 (lit c4))) ▸
       at 11 4 (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0417 c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 13 5 (CCZ013 ∷ []) (sym (wl0333 (lit c4))) ▸ done

  b27 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ K2 ∷ X4 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b27 = at 8 4 (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0798 (lit c4))) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 10 3 (Toff013 ∷ []) (wl0780 (lit c4)) ▸
       at 11 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 10 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl0792 (lit c4))) ▸
       at 9 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 12 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b28 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ K2 ∷ X4 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ X4 ∷ K2 ∷ Toff013 ∷ X4 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b28 = at 11 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 10 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 11 4 (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (sym (wp0414 c4)) ▸
       at 14 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 13 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl0792 (lit c4))) ▸
       at 12 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 15 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 14 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸ done

  b29 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ X4 ∷ K2 ∷ Toff013 ∷ X4 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b29 = at 13 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 16 2 (CS12 ∷ X4 ∷ []) (sym (c₃ (CS ↑) (X ↑))) ▸
       at 15 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0799 (lit c4))) ▸
       at 14 2 (CS12 ∷ X4 ∷ []) (sym (c₃ (CS ↑) (X ↑))) ▸
       at 17 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 16 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl0792 (lit c4))) ▸
       at 15 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸ done

  b30 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b30 = at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 17 4 (Bx0-1342 ∷ []) (sym (lem-beta-T-at233442 c4)) ▸
       at 17 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 17 1 (Bx0-1423 ∷ []) (lem-sym34-at2442 c4) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸ done

  b31 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b31 = at 21 2 [] (wl0283 (lit c4)) ▸
       at 17 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 2 [] (wl0550 (lit c4)) ▸
       at 4 2 [] (wl0550 (lit c4)) ▸
       at 5 2 [] (wl0550 (lit c4)) ▸
       at 6 2 [] (wl0550 (lit c4)) ▸
       at 2 5 (CCZ124 ∷ []) (sym (wl0788 (lit c4))) ▸
       at 1 3 (Toff214 ∷ []) (wl0563 (lit c4)) ▸ done

  b32 : Chain (Bx3-0412 ∷ Toff214 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ K2 ∷ CCZ124 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b32 = at 5 1 (CS02 ∷ []) (refl) ▸
       at 4 2 (CS02 ∷ X4 ∷ []) (sym (wl0800 (lit c4))) ▸
       at 4 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 3 2 (Sb3-0-2-1 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩-at243243 c4) ▸
       at 3 1 (CS02 ∷ []) (refl) ▸
       at 2 2 (CS02 ∷ X4 ∷ []) (sym (wl0800 (lit c4))) ▸
       at 2 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 6 1 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (sym (wl0563 (lit c4))) ▸ done

  b33 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ K2 ∷ CCZ124 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b33 = at 7 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0788 (lit c4)) ▸
       at 8 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 11 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 14 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 17 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b34 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b34 = at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 1 (CS13⁻ ∷ []) (refl) ▸
       at 15 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0789 (lit c4))) ▸
       at 19 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 12 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0790 (lit c4))) ▸
       at 10 1 (CS13 ∷ []) (refl) ▸
       at 9 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0791 (lit c4))) ▸ done

  b35 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b35 = at 13 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 6 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0790 (lit c4))) ▸
       at 4 1 (Bx0-1432 ∷ []) (lem-sym34-at243243 c4) ▸
       at 4 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 4 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b36 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b36 = at 12 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (sym (wp0412 c4)) ▸
       at 11 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 10 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 9 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 11 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (sym (wl0780 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 4 (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0781 (lit c4))) ▸ done

  b37 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b37 = at 14 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0333 (lit c4)) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 25 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0411 c4)) ▸
       at 22 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wl0782 (lit c4))) ▸
       at 19 4 (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0351 c4)) ▸ done

  b38 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b38 = at 16 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wl0782 (lit c4))) ▸
       at 13 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0352 c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 15 5 (CCZ013 ∷ []) (sym (wl0333 (lit c4))) ▸
       at 10 4 (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0783 (lit c4))) ▸ done

  b39 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Toff013 ∷ K2 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b39 = at 13 2 [] (wl0283 (lit c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 12 3 (Toff013 ∷ []) (wl0780 (lit c4)) ▸
       at 13 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 12 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl0792 (lit c4))) ▸
       at 11 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 6 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (sym (wp0412 c4)) ▸
       at 5 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b40 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Toff013 ∷ K2 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ X4 ∷ CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b40 = at 4 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 3 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 5 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (sym (wl0780 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 4 (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0781 (lit c4))) ▸
       at 8 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0333 (lit c4)) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b41 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ X4 ∷ CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b41 = at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0411 c4)) ▸
       at 16 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wl0782 (lit c4))) ▸
       at 13 4 (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0351 c4)) ▸
       at 10 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wl0782 (lit c4))) ▸
       at 7 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0352 c4)) ▸ done

  b42 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ X4 ∷ K0 ∷ CCZ013 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b42 = at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 9 5 (CCZ013 ∷ []) (sym (wl0333 (lit c4))) ▸
       at 4 4 (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0783 (lit c4))) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸ done

  b43 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ X4 ∷ K0 ∷ CCZ013 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1342 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b43 = at 6 3 (Toff013 ∷ []) (wl0780 (lit c4)) ▸
       at 7 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 6 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl0792 (lit c4))) ▸
       at 5 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 7 4 (Bx0-1342 ∷ []) (sym (lem-beta-T-at233442 c4)) ▸ done

  b44 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1342 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b44 = at 7 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 7 1 (Bx0-1423 ∷ []) (lem-sym34-at2442 c4) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 7 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 7 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b45 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b45 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 1 (CS13⁻ ∷ []) (refl) ▸
       at 18 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0793 (lit c4))) ▸
       at 31 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 15 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0794 (lit c4))) ▸ done

  b46 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b46 = at 13 1 (CS13 ∷ []) (refl) ▸
       at 12 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0795 (lit c4))) ▸
       at 25 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 9 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0794 (lit c4))) ▸
       at 7 1 (Bx0-1432 ∷ []) (lem-sym34-at243243 c4) ▸
       at 7 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 7 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b47 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ X4 ∷ Toff013 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b47 = at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (sym (wp0413 c4)) ▸
       at 14 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 13 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 12 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 13 4 (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (sym (wp0414 c4)) ▸
       at 16 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸ done

  b48 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ X4 ∷ Toff013 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b48 = at 15 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl0792 (lit c4))) ▸
       at 14 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 17 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 16 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 15 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 17 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (sym (wl0780 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b49 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b49 = at 22 4 (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0796 (lit c4))) ▸
       at 20 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0333 (lit c4)) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 30 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 31 4 (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0415 c4)) ▸
       at 28 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wl0797 (lit c4))) ▸ done

  b50 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b50 = at 25 4 (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0416 c4)) ▸
       at 22 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wl0797 (lit c4))) ▸
       at 19 4 (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0417 c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 23 2 [] (wl0283 (lit c4)) ▸
       at 24 2 [] (wl0283 (lit c4)) ▸
       at 25 2 [] (wl0283 (lit c4)) ▸
       at 21 5 (CCZ013 ∷ []) (sym (wl0333 (lit c4))) ▸ done

  b51 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ K2 ∷ X4 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b51 = at 16 4 (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0798 (lit c4))) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 18 3 (Toff013 ∷ []) (wl0780 (lit c4)) ▸
       at 19 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 18 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl0792 (lit c4))) ▸
       at 17 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 20 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b52 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ K2 ∷ X4 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ X4 ∷ K2 ∷ Toff013 ∷ X4 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b52 = at 19 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 18 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 19 4 (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (sym (wp0414 c4)) ▸
       at 22 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 21 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl0792 (lit c4))) ▸
       at 20 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 23 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 22 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸ done

  b53 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ X4 ∷ K2 ∷ Toff013 ∷ X4 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b53 = at 21 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 24 2 (CS12 ∷ X4 ∷ []) (sym (c₃ (CS ↑) (X ↑))) ▸
       at 23 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0799 (lit c4))) ▸
       at 22 2 (CS12 ∷ X4 ∷ []) (sym (c₃ (CS ↑) (X ↑))) ▸
       at 25 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 24 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl0792 (lit c4))) ▸
       at 23 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 9 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (sym (wp0413 c4)) ▸ done

  b54 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ K2 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b54 = at 8 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 7 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 6 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 7 4 (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (sym (wp0414 c4)) ▸
       at 10 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 9 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl0792 (lit c4))) ▸
       at 8 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 11 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b55 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ K2 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b55 = at 10 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 9 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 11 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (sym (wl0780 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 4 (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0796 (lit c4))) ▸
       at 14 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0333 (lit c4)) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b56 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b56 = at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 25 4 (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0415 c4)) ▸
       at 22 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wl0797 (lit c4))) ▸
       at 19 4 (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0416 c4)) ▸
       at 16 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wl0797 (lit c4))) ▸
       at 13 4 (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0417 c4)) ▸ done

  b57 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ K0 ∷ CCZ013 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b57 = at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 15 5 (CCZ013 ∷ []) (sym (wl0333 (lit c4))) ▸
       at 10 4 (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0798 (lit c4))) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸ done

  b58 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ K0 ∷ CCZ013 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b58 = at 12 3 (Toff013 ∷ []) (wl0780 (lit c4)) ▸
       at 13 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 12 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl0792 (lit c4))) ▸
       at 11 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 14 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 13 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 12 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 13 4 (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (sym (wp0414 c4)) ▸ done

  b59 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS12 ∷ Toff013 ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b59 = at 16 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 15 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl0792 (lit c4))) ▸
       at 14 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 17 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 16 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 15 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 18 2 (CS12 ∷ X4 ∷ []) (sym (c₃ (CS ↑) (X ↑))) ▸
       at 17 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0799 (lit c4))) ▸ done

  b60 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS12 ∷ Toff013 ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Bx0-1342 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b60 = at 16 2 (CS12 ∷ X4 ∷ []) (sym (c₃ (CS ↑) (X ↑))) ▸
       at 19 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 18 2 (K2⁻ ∷ Toff013 ∷ []) (sym (wl0792 (lit c4))) ▸
       at 17 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 19 4 (Bx0-1342 ∷ []) (sym (lem-beta-T-at233442 c4)) ▸ done

  b61 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Bx0-1342 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b61 = at 19 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 19 1 (Bx0-1423 ∷ []) (lem-sym34-at2442 c4) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 23 2 [] (wl0283 (lit c4)) ▸
       at 19 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 5 2 [] (wl0550 (lit c4)) ▸ done

  b62 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ [])
  b62 = at 6 2 [] (wl0550 (lit c4)) ▸
       at 7 2 [] (wl0550 (lit c4)) ▸
       at 8 2 [] (wl0550 (lit c4)) ▸
       at 4 5 (CCZ124 ∷ []) (sym (wl0788 (lit c4))) ▸
       at 3 3 (Toff214 ∷ []) (wl0563 (lit c4)) ▸
       at 7 1 (CS02⁻ ∷ []) (refl) ▸
       at 6 2 (CS02⁻ ∷ X4 ∷ []) (sym (wl0801 (lit c4))) ▸
       at 6 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸ done

  b63 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b63 = at 5 2 (Sb⁻3-0-2-1 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩-at243243 c4) ▸
       at 5 1 (CS02⁻ ∷ []) (refl) ▸
       at 4 2 (CS02⁻ ∷ X4 ∷ []) (sym (wl0801 (lit c4))) ▸
       at 4 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 0 5 (Sb3-0-41-2 ∷ []) (refl) ▸
       at 0 1 (Sb2-0-41-3 ∷ []) (sym (lem-F0 c4)) ▸ done


-- F5 CS12: 38 steps
lem-F5-CS12 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
lem-F5-CS12 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CCZ123 ∷ Bx0-1423 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 1 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 8 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Bx0-1423 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ Toff324 ∷ Bx0-4123 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 10 1 (CS13 ∷ []) (refl) ▸
       at 12 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 6 (CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ []) (sym (wl0802 (lit c4))) ▸
       at 1 2 (CS12 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at243243 c4) ▸
       at 2 2 (CCZ123 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at243243 c4) ▸
       at 3 2 (CS13 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at243243 c4) ▸
       at 4 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 6 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸ done

  b2 : Chain (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ Toff324 ∷ Bx0-4123 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Bx0-1423 ∷ Toff324 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b2 = at 6 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸
       at 6 1 (Bx0-4231 ∷ []) (lem-sym34-at143143 c4) ▸
       at 5 3 (Bx0-4231 ∷ CCZ124 ∷ []) (lem-T312-beta-at1441 c4) ▸
       at 5 1 (Bx0-4213 ∷ []) (lem-sym34-at1441 c4) ▸
       at 5 1 (Bx0-4123 ∷ []) (lem-sym23-at143143 c4) ▸
       at 5 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 5 2 (CCZ124 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 c4) ▸
       at 6 2 (CS13⁻ ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at243243 c4) ▸ done

  b3 : Chain (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Bx0-1423 ∷ Toff324 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Bx0-1423 ∷ CCZ124 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b3 = at 7 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 9 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 9 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸
       at 9 1 (Bx0-4231 ∷ []) (lem-sym34-at143143 c4) ▸
       at 8 3 (Bx0-4231 ∷ CCZ124 ∷ []) (lem-T312-beta-at1441 c4) ▸
       at 8 1 (Bx0-4213 ∷ []) (lem-sym34-at1441 c4) ▸
       at 8 1 (Bx0-4123 ∷ []) (lem-sym23-at143143 c4) ▸
       at 8 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸ done

  b4 : Chain (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Bx0-1423 ∷ CCZ124 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS12 ∷ [])
  b4 = at 8 2 (CCZ124 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 c4) ▸
       at 1 5 (CCZ124 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ []) (sym (wl0803 (lit c4))) ▸
       at 2 7 (CCZ124 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ []) (sym (wl0804 (lit c4))) ▸
       at 1 2 [] (wl0351 (lit c4)) ▸
       at 7 2 [] (lem-beta-inv-at243243 c4) ▸
       at 0 11 (CS12 ∷ []) (wl0805 (lit c4)) ▸ done


-- auto CS01 | SBOX(2;0;31;4) @0112203443: 7 steps
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0112203443 : Ws → ⟪ (CS12 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS12 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0112203443 c4 = run b0
  where
  b0 : Chain (CS12 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS12 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (sym (wl0035 (lit c4))) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ CS02 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at12213443 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (CS12 ∷ Sw01 ∷ []) (sym (wl0138 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- F4 CS12^0|CS12^1: 63 steps
lem-F4-CS12ᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣CS12ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CS12 ∷ CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Bx⁻0-13 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ Toff014 ∷ CCZ014 ∷ [])
  b0 = at 0 4 (CS12 ∷ []) (lem-F5-CS12 c4) ▸
       at 1 0 (CCZ014 ∷ CCZ014 ∷ []) (sym (wp0055 c4)) ▸
       at 2 0 (Toff014 ∷ Toff014 ∷ []) (sym (wp0269 c4)) ▸
       at 3 0 (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ CZ13 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ []) (sym (wl0806 (lit c4))) ▸
       at 5 1 (Bx0-13 ∷ []) (refl) ▸
       at 8 1 (Bx0-13 ∷ []) (refl) ▸
       at 3 6 (Bx1-023 ∷ []) (refl) ▸
       at 4 1 (Bx⁻0-13 ∷ []) (refl) ▸ done

  b1 : Chain (CS12 ∷ CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Bx⁻0-13 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ Toff014 ∷ CCZ014 ∷ []) (CS12 ∷ CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ CZ13 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-023 ∷ Toff014 ∷ CCZ014 ∷ [])
  b1 = at 7 1 (Bx⁻0-13 ∷ []) (refl) ▸
       at 4 6 (Bx⁻1-023 ∷ []) (refl) ▸
       at 4 0 (Toff014 ∷ Toff014 ∷ []) (sym (wp0269 c4)) ▸
       at 5 0 (CCZ014 ∷ CCZ014 ∷ []) (sym (wp0055 c4)) ▸
       at 6 0 (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ CZ13 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ []) (sym (wl0806 (lit c4))) ▸
       at 8 1 (Bx0-13 ∷ []) (refl) ▸
       at 11 1 (Bx0-13 ∷ []) (refl) ▸
       at 6 6 (Bx1-023 ∷ []) (refl) ▸ done

  b2 : Chain (CS12 ∷ CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ CZ13 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-023 ∷ Toff014 ∷ CCZ014 ∷ []) (CS12 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CS13⁻ ∷ Toff324 ∷ Bx⁻0-1423 ∷ [])
  b2 = at 7 1 (Bx⁻0-13 ∷ []) (refl) ▸
       at 10 1 (Bx⁻0-13 ∷ []) (refl) ▸
       at 7 6 (Bx⁻1-023 ∷ []) (refl) ▸
       at 1 6 (Bx0-1423 ∷ []) (refl) ▸
       at 2 6 (Bx⁻0-1423 ∷ []) (refl) ▸
       at 2 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 3 0 (CS13 ∷ CS13⁻ ∷ []) (sym (wl0807 (lit c4))) ▸
       at 3 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b3 : Chain (CS12 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CS13⁻ ∷ Toff324 ∷ Bx⁻0-1423 ∷ []) (Sb0-1-42-3 ∷ CS12 ∷ Sb⁻0-1-42-3 ∷ [])
  b3 = at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 5 0 (CS13⁻ ∷ CS13 ∷ []) (sym (wl0808 (lit c4))) ▸
       at 5 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 1 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 2 5 (Sb⁻0-1-42-3 ∷ []) (refl) ▸
       at 0 2 (Sb0-1-42-3 ∷ CS12 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0112203443 c4) ▸ done

  b4 : Chain (Sb0-1-42-3 ∷ CS12 ∷ Sb⁻0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Sb⁻0-1-3-2 ∷ Toff324 ∷ Bx⁻0-1423 ∷ [])
  b4 = at 1 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸
       at 5 1 (Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Toff324 ∷ Bx⁻0-1423 ∷ []) (refl) ▸
       at 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (CS13⁻ ∷ []) (refl) ▸
       at 9 1 (CS13 ∷ []) (refl) ▸
       at 8 2 [] (wl0808 (lit c4)) ▸
       at 7 2 [] (wl0616 (lit c4)) ▸
       at 6 1 (CS13 ∷ []) (refl) ▸ done

  b5 : Chain (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Sb⁻0-1-3-2 ∷ Toff324 ∷ Bx⁻0-1423 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ Bx⁻1-023 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-023 ∷ Toff014 ∷ CCZ014 ∷ [])
  b5 = at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 2 [] (wl0807 (lit c4)) ▸
       at 5 2 [] (wl0616 (lit c4)) ▸
       at 5 1 (Bx⁻1-023 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-023 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 4 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 9 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 11 1 (CZ13 ∷ []) (refl) ▸
       at 14 1 (CZ13 ∷ []) (refl) ▸ done

  b6 : Chain (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ Bx⁻1-023 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-023 ∷ Toff014 ∷ CCZ014 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CCZ014 ∷ Toff014 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Bx⁻1-023 ∷ Toff014 ∷ CCZ014 ∷ [])
  b6 = at 15 1 (Bx⁻0-13 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-13 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 15 1 (CZ13 ∷ []) (refl) ▸
       at 18 1 (CZ13 ∷ []) (refl) ▸
       at 9 12 [] (wl0806 (lit c4)) ▸
       at 8 2 [] (wp0055 c4) ▸
       at 7 2 [] (wp0269 c4) ▸
       at 6 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 8 1 (CZ13 ∷ []) (refl) ▸ done

  b7 : Chain (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CCZ014 ∷ Toff014 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Bx⁻1-023 ∷ Toff014 ∷ CCZ014 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b7 = at 11 1 (CZ13 ∷ []) (refl) ▸
       at 12 1 (Bx⁻0-13 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-13 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 12 1 (CZ13 ∷ []) (refl) ▸
       at 15 1 (CZ13 ∷ []) (refl) ▸
       at 6 12 [] (wl0806 (lit c4)) ▸
       at 5 2 [] (wp0269 c4) ▸
       at 4 2 [] (wp0055 c4) ▸ done


-- beta-T @13243241: 8 steps
lem-beta-T-at13243241 : Ws → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-beta-T-at13243241 c4 = run b0
  where
  b0 : Chain (Bx0-3421 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-3412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3421⟩ (lit c4)) ▸
       at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-beta-T-at13243142 c4) ▸
       at 0 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 (lit c4)) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 2 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 (lit c4)) ▸
       at 3 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;3421): 10 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩ : Ws → ⟪ (Sb⁻0-1-2-3 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx0-3421 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CS12⁻ ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-beta-T-at13243241 c4) ▸
       at 0 2 (Toff034 ∷ Sb⁻0-1-2-3 ∷ []) (lem-comm-SBOXd⟨0·1·2·3⟩-TOFF034 (lit c4)) ▸
       at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 2 (CCZ012 ∷ CS12⁻ ∷ []) (sym (wl0809 (lit c4))) ▸
       at 2 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 2 2 (Toff034 ∷ Sb⁻0-1-2-3 ∷ []) (lem-comm-SBOXd⟨0·1·2·3⟩-TOFF034 (lit c4)) ▸
       at 3 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 2 (CCZ012 ∷ CS12⁻ ∷ []) (sym (wl0809 (lit c4))) ▸ done

  b1 : Chain (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CS12⁻ ∷ []) (Bx0-3421 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx0-3421 ∷ []) (sym (lem-beta-T-at13243241 c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;3421): 10 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩ : Ws → ⟪ (Sb0-1-2-3 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-2-3 ∷ Bx0-3421 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CS12 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-beta-T-at13243241 c4) ▸
       at 0 2 (Toff034 ∷ Sb0-1-2-3 ∷ []) (lem-comm-SBOX⟨0·1·2·3⟩-TOFF034 (lit c4)) ▸
       at 1 1 (CS12 ∷ []) (refl) ▸
       at 1 2 (CCZ012 ∷ CS12 ∷ []) (sym (wl0810 (lit c4))) ▸
       at 2 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 2 2 (Toff034 ∷ Sb0-1-2-3 ∷ []) (lem-comm-SBOX⟨0·1·2·3⟩-TOFF034 (lit c4)) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 3 2 (CCZ012 ∷ CS12 ∷ []) (sym (wl0810 (lit c4))) ▸ done

  b1 : Chain (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CS12 ∷ []) (Bx0-3421 ∷ Sb0-1-2-3 ∷ [])
  b1 = at 4 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx0-3421 ∷ []) (sym (lem-beta-T-at13243241 c4)) ▸ done


-- T-beta @122331: 7 steps
lem-T-beta-at122331 : Ws → ⟪ (Toff023 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ Toff023 ∷ []) ⟫ʷ
lem-T-beta-at122331 c4 = run b0
  where
  b0 : Chain (Toff023 ∷ Bx0-2314 ∷ []) (Bx0-2314 ∷ Toff023 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 (lit c4)) ▸
       at 2 2 (Bx0-1324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2314⟩ (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ Toff013 ∷ []) (lem-T-beta-at2332 c4) ▸
       at 0 2 (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | TOFF032: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF032 : Ws → ⟪ (Bx0-1234 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF032 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Toff023 ∷ []) (Toff023 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (Toff023 ∷ []) (wl0811 (lit c4)) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 2 (Toff023 ∷ Bx0-2314 ∷ []) (sym (lem-T-beta-at122331 c4)) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 0 1 (Toff023 ∷ []) (wl0811 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ041: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ041 : Ws → ⟪ (Bx0-1234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ041 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ []) (wp0285 c4) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CCZ014 ∷ Bx0-1423 ∷ []) (sym (lem-Cz-beta-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CCZ014 ∷ []) (wp0285 c4) ▸ done


-- auto BOX(0;1234) | BOX(0;3241): 6 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·3241⟩ : Ws → ⟪ (Bx0-1234 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·3241⟩ c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Bx0-3241 ∷ []) (Bx0-3241 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-beta-T-at133441 c4) ▸
       at 0 2 (Toff023 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF032 c4) ▸
       at 1 2 (CCZ014 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ041 c4) ▸
       at 2 2 (Toff023 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF032 c4) ▸
       at 3 2 (CCZ014 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ041 c4) ▸
       at 0 4 (Bx0-3241 ∷ []) (sym (lem-beta-T-at133441 c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;3421) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2332 : Ws → ⟪ (Sb⁻0-1-3-2 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-3-2 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 (Bx0-3421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2431⟩ (lit c4)) ▸
       at 1 2 (Bx0-3421 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩ c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3421⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;3421) @243243: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at243243 : Ws → ⟪ (Sb⁻0-1-4-2 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-2 ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ Sb⁻0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ (lit c4)) ▸
       at 2 2 (Bx0-2431 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2341⟩ (lit c4)) ▸
       at 1 2 (Bx0-2431 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2332 c4) ▸
       at 0 2 (Bx0-2341 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2431⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;3421) @2442: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2442 : Ws → ⟪ (Sb⁻0-1-4-3 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-3 ∷ Bx0-3241 ∷ []) (Bx0-3241 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ (lit c4)) ▸
       at 2 2 (Bx0-2341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3241⟩ (lit c4)) ▸
       at 1 2 (Bx0-2341 ∷ Sb⁻0-1-4-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at243243 c4) ▸
       at 0 2 (Bx0-3241 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2341⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;3421) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2332 : Ws → ⟪ (Sb0-1-3-2 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-3-2 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ Sb0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 (Bx0-3421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2431⟩ (lit c4)) ▸
       at 1 2 (Bx0-3421 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩ c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3421⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;3421) @243243: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at243243 : Ws → ⟪ (Sb0-1-4-2 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-2 ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ Sb0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ (lit c4)) ▸
       at 2 2 (Bx0-2431 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2341⟩ (lit c4)) ▸
       at 1 2 (Bx0-2431 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2332 c4) ▸
       at 0 2 (Bx0-2341 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2431⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;3421) @2442: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2442 : Ws → ⟪ (Sb0-1-4-3 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-3 ∷ Bx0-3241 ∷ []) (Bx0-3241 ∷ Sb0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ (lit c4)) ▸
       at 2 2 (Bx0-2341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3241⟩ (lit c4)) ▸
       at 1 2 (Bx0-2341 ∷ Sb0-1-4-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at243243 c4) ▸
       at 0 2 (Bx0-3241 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2341⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;3241): 22 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩ c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sb0-1-23-4 ∷ Bx0-3241 ∷ []) (Bx0-1234 ∷ Toff423 ∷ Bx0-3241 ∷ Toff423 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 2 (Bx0-3241 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2442 c4) ▸
       at 5 0 (Toff423 ∷ Toff423 ∷ []) (sym (wl0296 (lit c4))) ▸
       at 3 1 (Toff423 ∷ []) (wl0812 (lit c4)) ▸
       at 5 1 (Toff423 ∷ []) (wl0812 (lit c4)) ▸
       at 3 3 (Bx0-3241 ∷ CCZ123 ∷ []) (lem-T312-beta-at133441 c4) ▸
       at 2 2 (Bx0-3241 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·3421⟩-at2442 c4) ▸
       at 3 0 (Toff423 ∷ Toff423 ∷ []) (sym (wl0296 (lit c4))) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ Bx0-3241 ∷ Toff423 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx0-3241 ∷ Bx0-1234 ∷ CCZ123 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ123 ∷ [])
  b1 = at 1 1 (Toff423 ∷ []) (wl0812 (lit c4)) ▸
       at 3 1 (Toff423 ∷ []) (wl0812 (lit c4)) ▸
       at 1 3 (Bx0-3241 ∷ CCZ123 ∷ []) (lem-T312-beta-at133441 c4) ▸
       at 0 2 (Bx0-3241 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·3241⟩ c4) ▸
       at 7 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 3 (Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) (wl0357 (lit c4)) ▸
       at 6 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14 ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-3241 ∷ Bx0-1234 ∷ CCZ123 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ123 ∷ []) (Bx0-3241 ∷ Sb0-1-23-4 ∷ [])
  b2 = at 6 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 5 (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) (wl0358 (lit c4)) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 6 2 [] (wl0212 (lit c4)) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto CCZ012 | BOX(3;2401): 5 steps
lem-auto-CCZ012-∣-BOX⟨3·2401⟩ : Ws → ⟪ (CCZ012 ∷ Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·2401⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-2401 ∷ []) (Bx3-2401 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ []) (wl0813 (lit c4)) ▸
       at 1 1 (Bx3-2041 ∷ []) (lem-sym23-at0312243041 c4) ▸
       at 0 2 (Bx3-2041 ∷ CCZ012 ∷ []) (lem-c124-beta-at0312203441 c4) ▸
       at 0 1 (Bx3-2401 ∷ []) (lem-sym23-at0312203441 c4) ▸
       at 1 1 (CCZ012 ∷ []) (wl0813 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;2;40;1): 9 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩ : Ws → ⟪ (CCZ012 ∷ Sb3-2-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-2-40-1 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Sb3-2-40-1 ∷ []) (Bx3-2401 ∷ Toff104 ∷ Sb3-2-1-0 ∷ Toff104 ∷ Sb⁻3-2-1-0 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx3-2401 ∷ Toff104 ∷ Sb3-2-1-0 ∷ Toff104 ∷ Sb⁻3-2-1-0 ∷ []) (refl) ▸
       at 0 2 (Bx3-2401 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·2401⟩ c4) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 1 4 (Toff104 ∷ CS12 ∷ Toff104 ∷ CCZ012 ∷ []) (wp0418 c4) ▸
       at 2 1 (Sb3-2-1-0 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ CCZ012 ∷ []) (wl0809 (lit c4)) ▸
       at 4 1 (Sb⁻3-2-1-0 ∷ []) (refl) ▸ done

  b1 : Chain (Bx3-2401 ∷ Toff104 ∷ Sb3-2-1-0 ∷ Toff104 ∷ Sb⁻3-2-1-0 ∷ CCZ012 ∷ []) (Sb3-2-40-1 ∷ CCZ012 ∷ [])
  b1 = at 0 5 (Sb3-2-40-1 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;3;1;4): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb0-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-1-4 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·3·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb0-3-1-4 ∷ []) (Sb0-3-1-4 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS13 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb0-3-1-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd21: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd21 : Ws → ⟪ (Sb0-1-23-4 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd21 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS12⁻ ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS12⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ CS14⁻ ∷ []) (sym (wl0814 (lit c4))) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS12⁻ ∷ Toff423 ∷ []) (sym (wl0815 (lit c4))) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS12⁻ ∷ CS14 ∷ []) (sym (wl0816 (lit c4))) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS12⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS12⁻ ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS12⁻ ∷ Toff423 ∷ []) (sym (wl0815 (lit c4))) ▸
       at 0 2 (CS12⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd21 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd21 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd21-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd21-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 (lit c4)) ▸
       at 1 2 (CS12⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd21 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;3;1;4): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb⁻0-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-1-4 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·3·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb⁻0-3-1-4 ∷ []) (Sb⁻0-3-1-4 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS13⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd21-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb⁻0-3-1-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;3241) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Bx0-3241 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2341⟩ (lit c4)) ▸
       at 1 2 (Bx0-3241 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩ c4) ▸
       at 0 2 (Bx0-2341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3241⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;3241) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Bx0-2341 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2431⟩ (lit c4)) ▸
       at 1 2 (Bx0-2341 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·3241⟩-at2332 c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2341⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;2;40;1) @1221: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at1221 : Ws → ⟪ (CCZ012 ∷ Sb3-1-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-40-2 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at1221 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Sb3-1-40-2 ∷ []) (Sb3-1-40-2 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 2 2 (Sb3-2-40-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·1·40·2⟩ (lit c4)) ▸
       at 1 2 (Sb3-2-40-1 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩ c4) ▸
       at 0 2 (Sb3-1-40-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·2·40·1⟩ (lit c4)) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;2;40;1) @132132: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at132132 : Ws → ⟪ (CCZ013 ∷ Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-40-3 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at132132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Sb2-1-40-3 ∷ []) (Sb2-1-40-3 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 2 2 (Sb3-1-40-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·1·40·3⟩ (lit c4)) ▸
       at 1 2 (Sb3-1-40-2 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at1221 c4) ▸
       at 0 2 (Sb2-1-40-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·1·40·2⟩ (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;2;40;1) @01132032: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at01132032 : Ws → ⟪ (CCZ013 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at01132032 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 (lit c4))) ▸
       at 2 2 (Sb2-1-40-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (Sb2-1-40-3 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at132132 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·40·3⟩ (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;2;40;1) @02132031: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at02132031 : Ws → ⟪ (CCZ023 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at02132031 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4)) ▸
       at 2 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb2-0-41-3 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at01132032 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;2;40;1) @02132130: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at02132130 : Ws → ⟪ (CCZ123 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at02132130 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·2·40·1⟩-at02132031 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D183 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0096 ; wl0103 ; wl0212 ; wl0214 ; wl0227 ; wl0283 ; wl0296 ; wl0341 ; wl0357 ; wl0358 ; wl0402 ; wl0602 ; wl0813 ; wl0848 ; wl0849 ; wl0850 ; wl0851 ; wl0852 ; wl0859 ; wl0860 ; wl0861 ; wl0862 ; wl0863 ; wl0864 ; wl0865 ; wl0866 ; wl0867 ; wl0868 ; wl0869 ; wl0870 ; wl0871 ; wl0872 ; wl0873 ; wp0440 ; wp0448 ; wp0449 ; wp0450 ; wp0451 ; wp0452 ; wp0453 ; wp0454 ; wp0455 ; wp0456)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-beta-T-at12243143 ; lem-sym12-at14213243 ; lem-sym23)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-Cz-beta-at2332 ; lem-sym12-at243243 ; lem-sym23-at12213443 ; lem-sym23-at12243143 ; lem-sym23-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-SBsym-at0113203442 ; lem-T312-beta-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-sym23-at0310243241 ; lem-sym23-at03103441)
open import Examples.Groups.Clifford+CS.Five.D.D161 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D171 using (lem-sym34-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-beta-T-at12213443 ; lem-sym23-at12233441 ; lem-sym23-at122441 ; lem-sym34-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D174 using (lem-beta-T-at143143)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-auto-BOX⟨0·1234⟩-∣-TOFF042 ; lem-c124-beta-at03103441)
open import Examples.Groups.Clifford+CS.Five.D.D181 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at122441 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D182 using (lem-F4-CS23ᵖ0∣CS01ᵖ1-part0)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-1-CCZ023 ; lem-nat-2-BOX⟨0·3412⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·1423⟩ ; lem-nat-1-CCZ013 ; lem-nat-2-BOX⟨0·2413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-SBOX⟨0·2·43·1⟩ ; lem-nat-0-SBOX⟨1·2·43·0⟩ ; lem-nat-1-SBOX⟨0·1·43·2⟩ ; lem-nat-1-SBOX⟨0·2·43·1⟩ ; lem-nat-2-SBOX⟨0·1·42·3⟩ ; lem-nat-2-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-BOX⟨0·4213⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨3·0421⟩ ; lem-nat-0-BOX⟨3·1420⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-1-BOX⟨0·4123⟩ ; lem-nat-2-BOX⟨0·4213⟩ ; lem-nat-2-BOX⟨0·4312⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-0-BOX⟨3·0241⟩ ; lem-nat-0-BOX⟨3·1240⟩ ; lem-nat-1-SBOX⟨0·1·3·2⟩ ; lem-nat-1-SBOX⟨0·2·3·1⟩ ; lem-nat-1-SBOX⟨2·1·43·0⟩ ; lem-nat-1-SBOXd⟨0·1·3·2⟩ ; lem-nat-1-SBOXd⟨0·2·3·1⟩ ; lem-nat-2-SBOX⟨2·1·43·0⟩ ; lem-nat-2-SBOX⟨3·1·42·0⟩ ; lem-nat-3-BOX⟨0·3412⟩ ; lem-nat-3-BOX⟨0·4312⟩)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-nat-1-SBOX⟨1·2·43·0⟩ ; lem-nat-2-SBOX⟨0·2·3·1⟩ ; lem-nat-2-SBOX⟨0·3·2·1⟩ ; lem-nat-2-SBOX⟨0·4·2·1⟩ ; lem-nat-2-SBOX⟨0·4·3·1⟩ ; lem-nat-2-SBOXd⟨0·2·3·1⟩ ; lem-nat-2-SBOXd⟨0·3·2·1⟩ ; lem-nat-2-SBOXd⟨0·4·2·1⟩ ; lem-nat-2-SBOXd⟨0·4·3·1⟩ ; lem-nat-3-SBOX⟨0·3·2·1⟩ ; lem-nat-3-SBOX⟨0·4·2·1⟩ ; lem-nat-3-SBOXd⟨0·3·2·1⟩ ; lem-nat-3-SBOXd⟨0·4·2·1⟩)
-- F4 CS23^0|CS01^1 part1: 392 steps
lem-F4-CS23ᵖ0∣CS01ᵖ1-part1 : Ws → ⟪ (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣CS01ᵖ1-part1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (run b48))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 1 (CS12⁻ ∷ []) (refl) ▸
       at 16 15 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0863 (lit c4))) ▸
       at 29 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 13 15 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0864 (lit c4))) ▸
       at 11 1 (CS12 ∷ []) (refl) ▸
       at 10 15 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0865 (lit c4))) ▸ done

  b1 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b1 = at 23 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 7 15 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0864 (lit c4))) ▸
       at 5 1 (Bx0-2413 ∷ []) (lem-sym34-at122441 c4) ▸
       at 5 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 5 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at12213443 c4) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b2 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b2 = at 13 15 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (sym (wp0449 c4)) ▸
       at 12 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 11 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 10 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 11 4 (CX14 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (sym (wp0450 c4)) ▸
       at 14 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 13 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 12 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸ done

  b3 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b3 = at 15 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 14 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 13 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 15 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0341 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 20 4 (CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0866 (lit c4))) ▸
       at 18 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4)) ▸ done

  b4 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b4 = at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 25 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 28 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 29 4 (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0451 c4)) ▸
       at 26 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0867 (lit c4))) ▸
       at 23 4 (CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wl0868 (lit c4))) ▸
       at 20 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0867 (lit c4))) ▸ done

  b5 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ K0 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b5 = at 17 4 (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wl0869 (lit c4))) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 23 2 [] (wl0283 (lit c4)) ▸
       at 19 5 (CCZ012 ∷ []) (sym (wl0602 (lit c4))) ▸
       at 14 4 (CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0870 (lit c4))) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸ done

  b6 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ K0 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ X4 ∷ Toff012 ∷ X4 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b6 = at 18 2 [] (wl0283 (lit c4)) ▸
       at 16 3 (Toff012 ∷ []) (wl0341 (lit c4)) ▸
       at 17 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 16 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 15 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 18 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 17 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 16 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸ done

  b7 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ X4 ∷ Toff012 ∷ X4 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ Toff012 ∷ CS13 ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b7 = at 17 4 (CX14 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (sym (wp0450 c4)) ▸
       at 20 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 19 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 18 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 21 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 20 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 19 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 22 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸ done

  b8 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ Toff012 ∷ CS13 ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b8 = at 21 2 (CS13 ∷ Toff012 ∷ []) (sym (wl0214 (lit c4))) ▸
       at 20 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 23 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 22 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 21 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 7 15 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (sym (wp0449 c4)) ▸
       at 6 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 5 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸ done

  b9 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ Toff012 ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b9 = at 4 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 5 4 (CX14 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (sym (wp0450 c4)) ▸
       at 8 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 7 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 6 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 9 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 8 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 7 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸ done

  b10 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ Toff012 ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b10 = at 9 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0341 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 4 (CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0866 (lit c4))) ▸
       at 12 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4)) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b11 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b11 = at 22 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 4 (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0451 c4)) ▸
       at 20 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0867 (lit c4))) ▸
       at 17 4 (CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wl0868 (lit c4))) ▸
       at 14 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0867 (lit c4))) ▸
       at 11 4 (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wl0869 (lit c4))) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸ done

  b12 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ Toff012 ∷ K3⁻ ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b12 = at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 13 5 (CCZ012 ∷ []) (sym (wl0602 (lit c4))) ▸
       at 8 4 (CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0870 (lit c4))) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 10 3 (Toff012 ∷ []) (wl0341 (lit c4)) ▸
       at 11 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸ done

  b13 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ Toff012 ∷ K3⁻ ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ X4 ∷ K3⁻ ∷ Toff012 ∷ X4 ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b13 = at 10 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 9 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 12 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 11 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 10 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 11 4 (CX14 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (sym (wp0450 c4)) ▸
       at 14 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 13 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸ done

  b14 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ X4 ∷ K3⁻ ∷ Toff012 ∷ X4 ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ X4 ∷ Toff012 ∷ K3⁻ ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b14 = at 12 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 15 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 14 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 13 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 16 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 15 2 (CS13 ∷ Toff012 ∷ []) (sym (wl0214 (lit c4))) ▸
       at 14 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 17 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸ done

  b15 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ X4 ∷ Toff012 ∷ K3⁻ ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b15 = at 16 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 15 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 17 4 (Bx0-2143 ∷ []) (sym (lem-beta-T-at12213443 c4)) ▸
       at 17 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 17 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸ done

  b16 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b16 = at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 17 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 3 2 [] (wl0859 (lit c4)) ▸
       at 4 2 [] (wl0859 (lit c4)) ▸
       at 5 2 [] (wl0859 (lit c4)) ▸ done

  b17 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CS03 ∷ Sb0-2-43-1 ∷ X4 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b17 = at 6 2 [] (wl0859 (lit c4)) ▸
       at 2 5 (CCZ134 ∷ []) (sym (wl0227 (lit c4))) ▸
       at 1 3 (Toff314 ∷ []) (wl0402 (lit c4)) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 4 2 (CS03 ∷ X4 ∷ []) (sym (wp0452 c4)) ▸
       at 4 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 2 (Sb2-0-3-1 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at122441 c4) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸ done

  b18 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CS03 ∷ Sb0-2-43-1 ∷ X4 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b18 = at 2 2 (CS03 ∷ X4 ∷ []) (sym (wp0452 c4)) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 6 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (sym (wl0402 (lit c4))) ▸
       at 7 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0227 (lit c4)) ▸
       at 8 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0859 (lit c4))) ▸
       at 11 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0859 (lit c4))) ▸
       at 14 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0859 (lit c4))) ▸
       at 17 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0859 (lit c4))) ▸ done

  b19 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b19 = at 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 1 (CS12⁻ ∷ []) (refl) ▸
       at 15 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0860 (lit c4))) ▸
       at 19 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b20 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b20 = at 12 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 10 1 (CS12 ∷ []) (refl) ▸
       at 9 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0862 (lit c4))) ▸
       at 13 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 6 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 4 1 (Bx0-2413 ∷ []) (lem-sym34-at122441 c4) ▸
       at 4 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 4 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at12213443 c4) ▸ done

  b21 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b21 = at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (sym (wp0448 c4)) ▸
       at 11 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 10 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 9 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 11 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0341 (lit c4))) ▸ done

  b22 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b22 = at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 4 (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0848 (lit c4))) ▸
       at 14 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4)) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b23 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34 ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b23 = at 25 4 (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0440 c4)) ▸
       at 22 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0849 (lit c4))) ▸
       at 19 4 (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wl0850 (lit c4))) ▸
       at 16 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0849 (lit c4))) ▸
       at 13 4 (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wl0851 (lit c4))) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸ done

  b24 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34 ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ X4 ∷ K3⁻ ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b24 = at 19 2 [] (wl0283 (lit c4)) ▸
       at 15 5 (CCZ012 ∷ []) (sym (wl0602 (lit c4))) ▸
       at 10 4 (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0852 (lit c4))) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 12 3 (Toff012 ∷ []) (wl0341 (lit c4)) ▸
       at 13 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 12 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸ done

  b25 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ X4 ∷ K3⁻ ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b25 = at 11 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 6 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (sym (wp0448 c4)) ▸
       at 5 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 4 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 3 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 5 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0341 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b26 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b26 = at 10 4 (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0848 (lit c4))) ▸
       at 8 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4)) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 4 (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0440 c4)) ▸
       at 16 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0849 (lit c4))) ▸ done

  b27 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b27 = at 13 4 (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wl0850 (lit c4))) ▸
       at 10 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0849 (lit c4))) ▸
       at 7 4 (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wl0851 (lit c4))) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 9 5 (CCZ012 ∷ []) (sym (wl0602 (lit c4))) ▸ done

  b28 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b28 = at 4 4 (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0852 (lit c4))) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 6 3 (Toff012 ∷ []) (wl0341 (lit c4)) ▸
       at 7 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 6 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 5 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸ done

  b29 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b29 = at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 7 4 (Bx0-2143 ∷ []) (sym (lem-beta-T-at12213443 c4)) ▸
       at 7 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 7 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸ done

  b30 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ [])
  b30 = at 11 2 [] (wl0283 (lit c4)) ▸
       at 7 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 7 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 1 (CS12⁻ ∷ []) (refl) ▸ done

  b31 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2413 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b31 = at 18 15 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0863 (lit c4))) ▸
       at 31 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 15 15 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0864 (lit c4))) ▸
       at 13 1 (CS12 ∷ []) (refl) ▸
       at 12 15 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0865 (lit c4))) ▸
       at 25 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 9 15 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0864 (lit c4))) ▸
       at 7 1 (Bx0-2413 ∷ []) (lem-sym34-at122441 c4) ▸ done

  b32 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2413 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b32 = at 7 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 7 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at12213443 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 15 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (sym (wp0449 c4)) ▸
       at 14 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 13 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸ done

  b33 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ Toff012 ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b33 = at 12 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 13 4 (CX14 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (sym (wp0450 c4)) ▸
       at 16 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 15 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 14 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 17 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 16 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 15 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸ done

  b34 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ Toff012 ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b34 = at 17 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0341 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 4 (CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0866 (lit c4))) ▸
       at 20 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4)) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b35 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b35 = at 30 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 31 4 (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0451 c4)) ▸
       at 28 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0867 (lit c4))) ▸
       at 25 4 (CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wl0868 (lit c4))) ▸
       at 22 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0867 (lit c4))) ▸
       at 19 4 (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wl0869 (lit c4))) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 23 2 [] (wl0283 (lit c4)) ▸ done

  b36 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ Toff012 ∷ K3⁻ ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b36 = at 24 2 [] (wl0283 (lit c4)) ▸
       at 25 2 [] (wl0283 (lit c4)) ▸
       at 21 5 (CCZ012 ∷ []) (sym (wl0602 (lit c4))) ▸
       at 16 4 (CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0870 (lit c4))) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 18 3 (Toff012 ∷ []) (wl0341 (lit c4)) ▸
       at 19 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸ done

  b37 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ Toff012 ∷ K3⁻ ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ X4 ∷ K3⁻ ∷ Toff012 ∷ X4 ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b37 = at 18 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 17 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 20 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 19 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 18 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 19 4 (CX14 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (sym (wp0450 c4)) ▸
       at 22 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 21 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸ done

  b38 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ X4 ∷ K3⁻ ∷ Toff012 ∷ X4 ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ X4 ∷ Toff012 ∷ K3⁻ ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b38 = at 20 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 23 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 22 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 21 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 24 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 23 2 (CS13 ∷ Toff012 ∷ []) (sym (wl0214 (lit c4))) ▸
       at 22 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 25 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸ done

  b39 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ X4 ∷ Toff012 ∷ K3⁻ ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ X4 ∷ Toff012 ∷ K3⁻ ∷ X4 ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b39 = at 24 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 23 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 9 15 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (sym (wp0449 c4)) ▸
       at 8 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 7 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 6 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 7 4 (CX14 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (sym (wp0450 c4)) ▸
       at 10 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸ done

  b40 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ X4 ∷ Toff012 ∷ K3⁻ ∷ X4 ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b40 = at 9 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 8 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 11 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 10 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 9 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 11 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0341 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b41 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b41 = at 16 4 (CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0866 (lit c4))) ▸
       at 14 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4)) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 25 4 (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0451 c4)) ▸
       at 22 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0867 (lit c4))) ▸ done

  b42 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b42 = at 19 4 (CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wl0868 (lit c4))) ▸
       at 16 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0867 (lit c4))) ▸
       at 13 4 (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wl0869 (lit c4))) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 15 5 (CCZ012 ∷ []) (sym (wl0602 (lit c4))) ▸ done

  b43 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ K3 ∷ X4 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b43 = at 10 4 (CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0870 (lit c4))) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 12 3 (Toff012 ∷ []) (wl0341 (lit c4)) ▸
       at 13 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 12 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 11 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 14 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸ done

  b44 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ K3 ∷ X4 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b44 = at 13 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 12 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 13 4 (CX14 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (sym (wp0450 c4)) ▸
       at 16 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 15 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 14 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 17 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 16 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸ done

  b45 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b45 = at 15 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 18 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 17 2 (CS13 ∷ Toff012 ∷ []) (sym (wl0214 (lit c4))) ▸
       at 16 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 19 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 18 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 17 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸ done

  b46 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b46 = at 21 2 [] (wl0283 (lit c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 19 4 (Bx0-2143 ∷ []) (sym (lem-beta-T-at12213443 c4)) ▸
       at 19 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 19 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸ done

  b47 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ [])
  b47 = at 23 2 [] (wl0283 (lit c4)) ▸
       at 19 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 5 2 [] (wl0859 (lit c4)) ▸
       at 6 2 [] (wl0859 (lit c4)) ▸
       at 7 2 [] (wl0859 (lit c4)) ▸
       at 8 2 [] (wl0859 (lit c4)) ▸
       at 4 5 (CCZ134 ∷ []) (sym (wl0227 (lit c4))) ▸
       at 3 3 (Toff314 ∷ []) (wl0402 (lit c4)) ▸ done

  b48 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b48 = at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 6 2 (CS03⁻ ∷ X4 ∷ []) (sym (wp0453 c4)) ▸
       at 6 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 2 (Sb⁻2-0-3-1 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at122441 c4) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 2 (CS03⁻ ∷ X4 ∷ []) (sym (wp0453 c4)) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- F4 CS23^0|CS01^1: 2 steps
lem-F4-CS23ᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣CS01ᵖ1 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (lem-F4-CS23ᵖ0∣CS01ᵖ1-part0 c4) ▸
       at 0 30 (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣CS01ᵖ1-part1 c4) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;2413): 14 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩ : Ws → ⟪ (Sb⁻0-1-2-3 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx0-2413 ∷ []) (Toff024 ∷ CCZ013 ∷ CS12⁻ ∷ Toff024 ∷ CCZ013 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at12243143 c4) ▸
       at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Toff024 ∷ CS12⁻ ∷ []) (wp0454 c4) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 2 (CCZ013 ∷ CS12⁻ ∷ []) (sym (wl0871 (lit c4))) ▸
       at 2 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 2 1 (CS12⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ CS12⁻ ∷ Toff024 ∷ CCZ013 ∷ []) (Bx0-2413 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 2 2 (Toff024 ∷ CS12⁻ ∷ []) (wp0454 c4) ▸
       at 3 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 3 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 2 (CCZ013 ∷ CS12⁻ ∷ []) (sym (wl0871 (lit c4))) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx0-2413 ∷ []) (sym (lem-beta-T-at12243143 c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;2413): 14 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩ : Ws → ⟪ (Sb0-1-2-3 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-2-3 ∷ Bx0-2413 ∷ []) (Toff024 ∷ CCZ013 ∷ CS12 ∷ Toff024 ∷ CCZ013 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at12243143 c4) ▸
       at 0 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (Toff024 ∷ CS12 ∷ []) (wp0455 c4) ▸
       at 1 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 1 1 (CS12 ∷ []) (refl) ▸
       at 1 2 (CCZ013 ∷ CS12 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 2 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 2 1 (CS12 ∷ []) (refl) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ CS12 ∷ Toff024 ∷ CCZ013 ∷ []) (Bx0-2413 ∷ Sb0-1-2-3 ∷ [])
  b1 = at 2 2 (Toff024 ∷ CS12 ∷ []) (wp0455 c4) ▸
       at 3 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 3 2 (CCZ013 ∷ CS12 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 4 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx0-2413 ∷ []) (sym (lem-beta-T-at12243143 c4)) ▸ done


-- auto BOX(0;1234) | CCZ013: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ013 : Ws → ⟪ (Bx0-1234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ013 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ013 ∷ []) (CCZ013 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CCZ013 ∷ Bx0-1324 ∷ []) (sym (lem-Cz-beta-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸ done


-- auto BOX(0;1234) | BOX(0;4213): 6 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·4213⟩ : Ws → ⟪ (Bx0-1234 ∷ Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·4213⟩ c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Bx0-4213 ∷ []) (Bx0-4213 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at143143 c4) ▸
       at 0 2 (Toff024 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF042 c4) ▸
       at 1 2 (CCZ013 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ013 c4) ▸
       at 2 2 (Toff024 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF042 c4) ▸
       at 3 2 (CCZ013 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ013 c4) ▸
       at 0 4 (Bx0-4213 ∷ []) (sym (lem-beta-T-at143143 c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;2413) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2332 : Ws → ⟪ (Sb⁻0-1-3-2 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-3-2 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4)) ▸
       at 1 2 (Bx0-2413 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩ c4) ▸
       at 0 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;2413) @243243: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at243243 : Ws → ⟪ (Sb⁻0-1-4-2 ∷ Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-2 ∷ Bx0-4312 ∷ []) (Bx0-4312 ∷ Sb⁻0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ (lit c4)) ▸
       at 2 2 (Bx0-3412 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4312⟩ (lit c4)) ▸
       at 1 2 (Bx0-3412 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2332 c4) ▸
       at 0 2 (Bx0-4312 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3412⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;2413) @2442: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2442 : Ws → ⟪ (Sb⁻0-1-4-3 ∷ Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-3 ∷ Bx0-4213 ∷ []) (Bx0-4213 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ (lit c4)) ▸
       at 2 2 (Bx0-4312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4213⟩ (lit c4)) ▸
       at 1 2 (Bx0-4312 ∷ Sb⁻0-1-4-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at243243 c4) ▸
       at 0 2 (Bx0-4213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4312⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- sym12 @143143: 5 steps
lem-sym12-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-sym12-at143143 c4 = run b0
  where
  b0 : Chain (Bx0-4213 ∷ []) (Bx0-2413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-4123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·4213⟩ (lit c4)) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 0 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym12 @12243143: 5 steps
lem-sym12-at12243143 : Ws → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-sym12-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ []) (Bx0-4213 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4)) ▸
       at 1 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 0 2 (Bx0-4213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·4123⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;2413) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2332 : Ws → ⟪ (Sb0-1-3-2 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-3-2 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ Sb0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4)) ▸
       at 1 2 (Bx0-2413 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩ c4) ▸
       at 0 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;2413) @243243: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at243243 : Ws → ⟪ (Sb0-1-4-2 ∷ Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-2 ∷ Bx0-4312 ∷ []) (Bx0-4312 ∷ Sb0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ (lit c4)) ▸
       at 2 2 (Bx0-3412 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4312⟩ (lit c4)) ▸
       at 1 2 (Bx0-3412 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2332 c4) ▸
       at 0 2 (Bx0-4312 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3412⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;2413) @2442: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2442 : Ws → ⟪ (Sb0-1-4-3 ∷ Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-3 ∷ Bx0-4213 ∷ []) (Bx0-4213 ∷ Sb0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ (lit c4)) ▸
       at 2 2 (Bx0-4312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4213⟩ (lit c4)) ▸
       at 1 2 (Bx0-4312 ∷ Sb0-1-4-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at243243 c4) ▸
       at 0 2 (Bx0-4213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4312⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;4213): 30 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb0-1-23-4 ∷ Bx0-4213 ∷ []) (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Bx0-2431 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 2 (Bx0-4213 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2442 c4) ▸
       at 5 0 (Toff423 ∷ Toff423 ∷ []) (sym (wl0296 (lit c4))) ▸
       at 4 1 (Bx0-2413 ∷ []) (lem-sym12-at143143 c4) ▸
       at 4 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸
       at 4 1 (Bx0-2341 ∷ []) (lem-sym23-at122441 c4) ▸
       at 3 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-T312-beta-at12233441 c4) ▸
       at 3 1 (Bx0-2431 ∷ []) (lem-sym23-at12233441 c4) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Bx0-2431 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx0-1234 ∷ Bx0-2341 ∷ CCZ123 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b1 = at 3 1 (Bx0-2413 ∷ []) (lem-sym34-at122441 c4) ▸
       at 3 1 (Bx0-4213 ∷ []) (lem-sym12-at12243143 c4) ▸
       at 2 2 (Bx0-4213 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·2413⟩-at2442 c4) ▸
       at 3 0 (Toff423 ∷ Toff423 ∷ []) (sym (wl0296 (lit c4))) ▸
       at 2 1 (Bx0-2413 ∷ []) (lem-sym12-at143143 c4) ▸
       at 2 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸
       at 2 1 (Bx0-2341 ∷ []) (lem-sym23-at122441 c4) ▸
       at 1 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-T312-beta-at12233441 c4) ▸ done

  b2 : Chain (Bx0-1234 ∷ Bx0-2341 ∷ CCZ123 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx0-4213 ∷ Bx0-1234 ∷ CCZ123 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ123 ∷ [])
  b2 = at 1 1 (Bx0-2431 ∷ []) (lem-sym23-at12233441 c4) ▸
       at 1 1 (Bx0-2413 ∷ []) (lem-sym34-at122441 c4) ▸
       at 1 1 (Bx0-4213 ∷ []) (lem-sym12-at12243143 c4) ▸
       at 0 2 (Bx0-4213 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·4213⟩ c4) ▸
       at 7 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 3 (Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) (wl0357 (lit c4)) ▸
       at 6 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14 ∷ []) (refl) ▸ done

  b3 : Chain (Bx0-4213 ∷ Bx0-1234 ∷ CCZ123 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ123 ∷ []) (Bx0-4213 ∷ Sb0-1-23-4 ∷ [])
  b3 = at 6 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 5 (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) (wl0358 (lit c4)) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 6 2 [] (wl0212 (lit c4)) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- sym23 @03243240: 5 steps
lem-sym23-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-sym23-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ []) (Bx3-1240 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ (lit c4)) ▸
       at 1 1 (Bx3-0241 ∷ []) (lem-sym23-at0310243241 c4) ▸
       at 0 2 (Bx3-1240 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0241⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- c124-beta @033440: 7 steps
lem-c124-beta-at033440 : Ws → ⟪ (CCZ012 ∷ Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ CCZ012 ∷ []) ⟫ʷ
lem-c124-beta-at033440 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-1240 ∷ []) (Bx3-1240 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 (lit c4))) ▸
       at 2 2 (Bx3-0241 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1240⟩ (lit c4)) ▸
       at 1 2 (Bx3-0241 ∷ CCZ012 ∷ []) (lem-c124-beta-at03103441 c4) ▸
       at 0 2 (Bx3-1240 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0241⟩ (lit c4)) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- sym23 @033440: 5 steps
lem-sym23-at033440 : Ws → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-sym23-at033440 c4 = run b0
  where
  b0 : Chain (Bx3-1240 ∷ []) (Bx3-1420 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0241 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1240⟩ (lit c4)) ▸
       at 1 1 (Bx3-0421 ∷ []) (lem-sym23-at03103441 c4) ▸
       at 0 2 (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;1420): 5 steps
lem-auto-CCZ012-∣-BOX⟨3·1420⟩ : Ws → ⟪ (CCZ012 ∷ Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·1420⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-1420 ∷ []) (Bx3-1420 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ []) (wl0813 (lit c4)) ▸
       at 1 1 (Bx3-1240 ∷ []) (lem-sym23-at03243240 c4) ▸
       at 0 2 (Bx3-1240 ∷ CCZ012 ∷ []) (lem-c124-beta-at033440 c4) ▸
       at 0 1 (Bx3-1420 ∷ []) (lem-sym23-at033440 c4) ▸
       at 1 1 (CCZ012 ∷ []) (wl0813 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;1;42;0): 9 steps
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩ : Ws → ⟪ (CCZ012 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Sb3-1-42-0 ∷ []) (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 0 2 (Bx3-1420 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·1420⟩ c4) ▸
       at 3 1 (CS01 ∷ []) (refl) ▸
       at 1 4 (Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ012 ∷ []) (wp0456 c4) ▸
       at 2 1 (Sb3-1-0-2 ∷ []) (refl) ▸
       at 5 1 (CS01⁻ ∷ []) (refl) ▸
       at 4 2 (CS01⁻ ∷ CCZ012 ∷ []) (wl0873 (lit c4)) ▸
       at 4 1 (Sb⁻3-1-0-2 ∷ []) (refl) ▸ done

  b1 : Chain (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ CCZ012 ∷ []) (Sb3-1-42-0 ∷ CCZ012 ∷ [])
  b1 = at 0 5 (Sb3-1-42-0 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;4;3;1): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb0-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-3-1 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb0-4-3-1 ∷ []) (Sb0-4-3-1 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS34 ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb0-4-3-1 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;4;3;1): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb⁻0-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-3-1 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb⁻0-4-3-1 ∷ []) (Sb⁻0-4-3-1 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS34⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb⁻0-4-3-1 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;4213) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Bx0-4312 ∷ []) (Bx0-4312 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Bx0-4213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4312⟩ (lit c4)) ▸
       at 1 2 (Bx0-4213 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩ c4) ▸
       at 0 2 (Bx0-4312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4213⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;4213) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Bx0-4312 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3412⟩ (lit c4)) ▸
       at 1 2 (Bx0-4312 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at2332 c4) ▸
       at 0 2 (Bx0-3412 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4312⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;4213) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at2442 : Ws → ⟪ (Sb0-1-43-2 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ (lit c4)) ▸
       at 1 2 (Bx0-3412 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at243243 c4) ▸
       at 0 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;4213) @122441: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at122441 : Ws → ⟪ (Sb0-2-43-1 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at122441 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 2 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx0-2413 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at2442 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4)) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;1;42;0) @2332: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at2332 : Ws → ⟪ (CCZ013 ∷ Sb2-1-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-43-0 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at2332 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Sb2-1-43-0 ∷ []) (Sb2-1-43-0 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 2 2 (Sb3-1-42-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·1·43·0⟩ (lit c4)) ▸
       at 1 2 (Sb3-1-42-0 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩ c4) ▸
       at 0 2 (Sb2-1-43-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·1·42·0⟩ (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;1;42;0) @122331: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at122331 : Ws → ⟪ (CCZ023 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at122331 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Sb1-2-43-0 ∷ []) (Sb1-2-43-0 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4)) ▸
       at 2 2 (Sb2-1-43-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 1 2 (Sb2-1-43-0 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at2332 c4) ▸
       at 0 2 (Sb1-2-43-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·43·0⟩ (lit c4)) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;1;42;0) @01122330: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at01122330 : Ws → ⟪ (CCZ123 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CCZ123 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at01122330 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 2 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 1 2 (Sb1-2-43-0 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at122331 c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;4;3;1) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-2-1 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb0-4-2-1 ∷ []) (Sb0-4-2-1 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Sb0-4-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·4·2·1⟩ (lit c4)) ▸
       at 1 2 (Sb0-4-3-1 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩ c4) ▸
       at 0 2 (Sb0-4-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·4·3·1⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;4;3;1) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb0-3-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-2-1 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb0-3-2-1 ∷ []) (Sb0-3-2-1 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb0-4-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·3·2·1⟩ (lit c4)) ▸
       at 1 2 (Sb0-4-2-1 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at2332 c4) ▸
       at 0 2 (Sb0-3-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·4·2·1⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;4;3;1) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at2442 : Ws → ⟪ (Sb0-1-43-2 ∷ Sb0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-3-1 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Sb0-2-3-1 ∷ []) (Sb0-2-3-1 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 (Sb0-3-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·2·3·1⟩ (lit c4)) ▸
       at 1 2 (Sb0-3-2-1 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at243243 c4) ▸
       at 0 2 (Sb0-2-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·3·2·1⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;4;3;1) @122441: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at122441 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at122441 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-3-2 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 2 2 (Sb0-2-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·3·2⟩ (lit c4)) ▸
       at 1 2 (Sb0-2-3-1 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at2442 c4) ▸
       at 0 2 (Sb0-1-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·3·1⟩ (lit c4)) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;4;3;1) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb⁻0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-2-1 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb⁻0-4-2-1 ∷ []) (Sb⁻0-4-2-1 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Sb⁻0-4-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·4·2·1⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-4-3-1 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩ c4) ▸
       at 0 2 (Sb⁻0-4-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·4·3·1⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;4;3;1) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb⁻0-3-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-2-1 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb⁻0-3-2-1 ∷ []) (Sb⁻0-3-2-1 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb⁻0-4-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·3·2·1⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-4-2-1 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at2332 c4) ▸
       at 0 2 (Sb⁻0-3-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·4·2·1⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;4;3;1) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at2442 : Ws → ⟪ (Sb0-1-43-2 ∷ Sb⁻0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-3-1 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻0-2-3-1 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 (Sb⁻0-3-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·2·3·1⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-3-2-1 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at243243 c4) ▸
       at 0 2 (Sb⁻0-2-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·3·2·1⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;4;3;1) @122441: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at122441 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at122441 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 2 2 (Sb⁻0-2-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·1·3·2⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-2-3-1 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at2442 c4) ▸
       at 0 2 (Sb⁻0-1-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·3·1⟩ (lit c4)) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D184 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0021 ; wl0024 ; wl0025 ; wl0103 ; wl0111 ; wl0187 ; wl0212 ; wl0225 ; wl0226 ; wl0265 ; wl0270 ; wl0271 ; wl0272 ; wl0273 ; wl0283 ; wl0298 ; wl0325 ; wl0326 ; wl0341 ; wl0364 ; wl0602 ; wl0627 ; wl0653 ; wl0661 ; wl0741 ; wl0742 ; wl0848 ; wl0849 ; wl0850 ; wl0851 ; wl0852 ; wl0859 ; wl0860 ; wl0861 ; wl0862 ; wl0866 ; wl0867 ; wl0868 ; wl0869 ; wl0870 ; wl0874 ; wl0875 ; wl0876 ; wl0877 ; wl0878 ; wl0879 ; wl0880 ; wl0881 ; wl0882 ; wl0883 ; wl0884 ; wp0034 ; wp0268 ; wp0370 ; wp0371 ; wp0372 ; wp0440 ; wp0448 ; wp0451 ; wp0457 ; wp0458 ; wp0459 ; wp0460)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-BOXd-BOX ; lem-CS12-beta ; lem-CS20-beta-ci ; lem-beta-T-at2332 ; lem-sym12-at14213243 ; lem-sym34 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-AX-SB ; lem-BOXd-BOX-at2332 ; lem-CS12-beta-at243243 ; lem-sym12-at243243 ; lem-sym23-at12213443 ; lem-sym23-at12243143 ; lem-sym23-at243243 ; lem-sym23-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-X1-beta-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-SBsymd-at0113203442)
open import Examples.Groups.Clifford+CS.Five.D.D089 using (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS02)
open import Examples.Groups.Clifford+CS.Five.D.D166 using (lem-T312-beta-at14233142 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at122441 ; lem-beta-inv-at122441 ; lem-sym12-at122441 ; lem-sym12-at1441 ; lem-sym23-at14233241 ; lem-sym23-at1441 ; lem-sym34-at14233142 ; lem-sym34-at14233241)
open import Examples.Groups.Clifford+CS.Five.D.D171 using (lem-sym34-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-X1-beta-at1441 ; lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 ; lem-beta-T-at12213443 ; lem-sym34-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2442 ; lem-auto-BOX⟨0·1234⟩-∣-CS13-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D180 using (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0113203442)
open import Examples.Groups.Clifford+CS.Five.D.D183 using (lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at01122330 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at122441 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at122441 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at122441)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ013 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-2-CS12 ; lem-nat-2-CS13)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-2-CS02 ; lem-nat-2-CSd02 ; lem-nat-3-SBOX⟨1·0·2·4⟩ ; lem-nat-3-SBOXd⟨1·0·2·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-2-CS03 ; lem-nat-2-CSd03 ; lem-nat-2-SBOXd⟨0·1·23·4⟩ ; lem-nat-2-SBOXd⟨0·1·32·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-BOX⟨0·1432⟩ ; lem-nat-1-BOX⟨0·2431⟩ ; lem-nat-1-SBOX⟨0·1·2·3⟩ ; lem-nat-1-SBOX⟨0·1·43·2⟩ ; lem-nat-1-SBOX⟨0·2·1·3⟩ ; lem-nat-1-SBOX⟨0·2·43·1⟩ ; lem-nat-1-SBOXd⟨0·1·2·3⟩ ; lem-nat-1-SBOXd⟨0·2·1·3⟩ ; lem-nat-2-SBOX⟨1·0·3·4⟩ ; lem-nat-2-SBOXd⟨1·0·3·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-0-SBOXd⟨0·1·42·3⟩ ; lem-nat-0-SBOXd⟨1·0·42·3⟩ ; lem-nat-1-SBOXd⟨1·0·42·3⟩ ; lem-nat-1-SBOXd⟨2·0·41·3⟩ ; lem-nat-2-SBOX⟨1·0·2·4⟩ ; lem-nat-2-SBOXd⟨1·0·2·4⟩ ; lem-nat-3-SBOX⟨1·0·2·3⟩ ; lem-nat-3-SBOXd⟨0·1·32·4⟩ ; lem-nat-3-SBOXd⟨0·1·42·3⟩ ; lem-nat-3-SBOXd⟨1·0·2·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-SBOX⟨0·1·2·3⟩ ; lem-nat-0-SBOXd⟨0·1·2·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-SBOX⟨1·0·2·3⟩ ; lem-nat-0-SBOXd⟨1·0·2·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-comm-CCZ024-CSd13 ; lem-nat-3-SBOX⟨0·2·34·1⟩ ; lem-nat-3-SBOX⟨0·2·43·1⟩)
-- F4 CS23^0|CS12^1: 508 steps
lem-F4-CS23ᵖ0∣CS12ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣CS12ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (trans (run b62) (run b63)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 3 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 2 2 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4) ▸
       at 1 2 (Bx0-1423 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·4213⟩-at122441 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CCZ123 ∷ CCZ123 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b1 = at 1 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 0 2 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (wl0661 (lit c4)) ▸
       at 1 2 (X4 ∷ CCZ123 ∷ []) (wl0661 (lit c4)) ▸
       at 2 2 (Sb0-2-43-1 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·1·42·0⟩-at01122330 c4) ▸
       at 3 2 (X4 ∷ CCZ123 ∷ []) (wl0661 (lit c4)) ▸ done

  b2 : Chain (Bx0-1423 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CCZ123 ∷ CCZ123 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b2 = at 4 2 [] (wl0212 (lit c4)) ▸
       at 4 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (sym (wl0364 (lit c4))) ▸
       at 5 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0225 (lit c4)) ▸
       at 6 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0859 (lit c4))) ▸
       at 9 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0859 (lit c4))) ▸
       at 12 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0859 (lit c4))) ▸
       at 15 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0859 (lit c4))) ▸
       at 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b3 : Chain (Bx0-1423 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b3 = at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 1 (CS12⁻ ∷ []) (refl) ▸
       at 13 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0860 (lit c4))) ▸
       at 17 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 10 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0861 (lit c4))) ▸ done

  b4 : Chain (Bx0-1423 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b4 = at 8 1 (CS12 ∷ []) (refl) ▸
       at 7 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0862 (lit c4))) ▸
       at 11 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 2 1 (Bx0-2413 ∷ []) (lem-sym34-at122441 c4) ▸
       at 2 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 2 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at12213443 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b5 : Chain (Bx0-1423 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b5 = at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (sym (wp0448 c4)) ▸
       at 9 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 8 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 7 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 9 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0341 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b6 : Chain (Bx0-1423 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b6 = at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 4 (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0848 (lit c4))) ▸
       at 12 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4)) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 4 (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0440 c4)) ▸ done

  b7 : Chain (Bx0-1423 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34 ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b7 = at 20 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0849 (lit c4))) ▸
       at 17 4 (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wl0850 (lit c4))) ▸
       at 14 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0849 (lit c4))) ▸
       at 11 4 (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wl0851 (lit c4))) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸ done

  b8 : Chain (Bx0-1423 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34 ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b8 = at 13 5 (CCZ012 ∷ []) (sym (wl0602 (lit c4))) ▸
       at 8 4 (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0852 (lit c4))) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 10 3 (Toff012 ∷ []) (wl0341 (lit c4)) ▸
       at 11 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 10 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 9 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸ done

  b9 : Chain (Bx0-1423 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b9 = at 4 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (sym (wp0448 c4)) ▸
       at 3 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 2 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 1 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 3 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0341 (lit c4))) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 4 (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0848 (lit c4))) ▸ done

  b10 : Chain (Bx0-1423 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b10 = at 6 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4)) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 4 (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0440 c4)) ▸
       at 14 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0849 (lit c4))) ▸
       at 11 4 (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wl0850 (lit c4))) ▸ done

  b11 : Chain (Bx0-1423 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS34 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b11 = at 8 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0849 (lit c4))) ▸
       at 5 4 (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wl0851 (lit c4))) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 7 5 (CCZ012 ∷ []) (sym (wl0602 (lit c4))) ▸
       at 2 4 (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0852 (lit c4))) ▸ done

  b12 : Chain (Bx0-1423 ∷ K3 ∷ CS34 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b12 = at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 4 3 (Toff012 ∷ []) (wl0341 (lit c4)) ▸
       at 5 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 4 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 3 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸ done

  b13 : Chain (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b13 = at 8 2 [] (wl0283 (lit c4)) ▸
       at 5 4 (Bx0-2143 ∷ []) (sym (lem-beta-T-at12213443 c4)) ▸
       at 5 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 5 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸ done

  b14 : Chain (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b14 = at 5 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 1 (CS12⁻ ∷ []) (refl) ▸
       at 16 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0874 (lit c4))) ▸ done

  b15 : Chain (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2143 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b15 = at 29 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 13 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0875 (lit c4))) ▸
       at 11 1 (CS12 ∷ []) (refl) ▸
       at 10 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0876 (lit c4))) ▸
       at 23 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 7 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0875 (lit c4))) ▸
       at 5 1 (Bx0-2413 ∷ []) (lem-sym34-at122441 c4) ▸
       at 5 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸ done

  b16 : Chain (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2143 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ Toff012 ∷ X4 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b16 = at 5 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at12213443 c4) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (sym (wp0457 c4)) ▸
       at 12 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 11 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 10 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸ done

  b17 : Chain (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ Toff012 ∷ X4 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b17 = at 11 4 (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (sym (wp0458 c4)) ▸
       at 14 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 13 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 12 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 15 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 14 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 13 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 15 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0341 (lit c4))) ▸ done

  b18 : Chain (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b18 = at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 20 4 (CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0866 (lit c4))) ▸
       at 18 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4)) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 25 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 28 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b19 : Chain (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b19 = at 29 4 (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0451 c4)) ▸
       at 26 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0867 (lit c4))) ▸
       at 23 4 (CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wl0868 (lit c4))) ▸
       at 20 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0867 (lit c4))) ▸
       at 17 4 (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wl0869 (lit c4))) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸ done

  b20 : Chain (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ K3⁻ ∷ Toff012 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b20 = at 23 2 [] (wl0283 (lit c4)) ▸
       at 19 5 (CCZ012 ∷ []) (sym (wl0602 (lit c4))) ▸
       at 14 4 (CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0870 (lit c4))) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 16 3 (Toff012 ∷ []) (wl0341 (lit c4)) ▸
       at 17 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 16 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸ done

  b21 : Chain (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ K3⁻ ∷ Toff012 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b21 = at 15 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 18 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 17 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 16 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 17 4 (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (sym (wp0458 c4)) ▸
       at 20 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 19 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 18 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸ done

  b22 : Chain (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ X4 ∷ K3⁻ ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b22 = at 21 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 20 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 19 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 22 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 21 2 (CS23 ∷ Toff012 ∷ []) (sym (wl0226 (lit c4))) ▸
       at 20 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 23 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 22 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸ done

  b23 : Chain (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ X4 ∷ K3⁻ ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ X4 ∷ K3⁻ ∷ Toff012 ∷ X4 ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b23 = at 21 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 7 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (sym (wp0457 c4)) ▸
       at 6 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 5 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 4 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 5 4 (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (sym (wp0458 c4)) ▸
       at 8 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 7 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸ done

  b24 : Chain (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ X4 ∷ K3⁻ ∷ Toff012 ∷ X4 ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b24 = at 6 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 9 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 8 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 7 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 9 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0341 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 4 (CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0866 (lit c4))) ▸ done

  b25 : Chain (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b25 = at 12 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4)) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 4 (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0451 c4)) ▸
       at 20 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0867 (lit c4))) ▸
       at 17 4 (CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wl0868 (lit c4))) ▸ done

  b26 : Chain (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b26 = at 14 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0867 (lit c4))) ▸
       at 11 4 (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wl0869 (lit c4))) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 13 5 (CCZ012 ∷ []) (sym (wl0602 (lit c4))) ▸
       at 8 4 (CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0870 (lit c4))) ▸ done

  b27 : Chain (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b27 = at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 10 3 (Toff012 ∷ []) (wl0341 (lit c4)) ▸
       at 11 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 10 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 9 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 12 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 11 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸ done

  b28 : Chain (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ Toff012 ∷ X4 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b28 = at 10 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 11 4 (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (sym (wp0458 c4)) ▸
       at 14 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 13 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 12 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 15 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 14 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 13 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸ done

  b29 : Chain (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ Toff012 ∷ X4 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b29 = at 16 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 15 2 (CS23 ∷ Toff012 ∷ []) (sym (wl0226 (lit c4))) ▸
       at 14 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 17 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 16 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 15 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸ done

  b30 : Chain (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b30 = at 20 2 [] (wl0283 (lit c4)) ▸
       at 17 4 (Bx0-2143 ∷ []) (sym (lem-beta-T-at12213443 c4)) ▸
       at 17 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 17 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸ done

  b31 : Chain (Bx0-1423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b31 = at 17 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 3 2 [] (wl0859 (lit c4)) ▸
       at 4 2 [] (wl0859 (lit c4)) ▸
       at 5 2 [] (wl0859 (lit c4)) ▸
       at 6 2 [] (wl0859 (lit c4)) ▸
       at 2 5 (CCZ234 ∷ []) (sym (wl0225 (lit c4))) ▸
       at 1 3 (Toff324 ∷ []) (wl0364 (lit c4)) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸ done

  b32 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ K3 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b32 = at 4 2 (CS13 ∷ X4 ∷ []) (sym (wl0741 (lit c4))) ▸
       at 4 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 3 2 (Sb0-1-3-2 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·4·3·1⟩-at122441 c4) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 2 2 (CS13 ∷ X4 ∷ []) (sym (wl0741 (lit c4))) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 6 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (sym (wl0364 (lit c4))) ▸
       at 7 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0225 (lit c4)) ▸ done

  b33 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ K3 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b33 = at 8 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0859 (lit c4))) ▸
       at 11 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0859 (lit c4))) ▸
       at 14 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0859 (lit c4))) ▸
       at 17 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0859 (lit c4))) ▸
       at 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b34 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b34 = at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 1 (CS12⁻ ∷ []) (refl) ▸
       at 15 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0860 (lit c4))) ▸
       at 19 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 12 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 10 1 (CS12 ∷ []) (refl) ▸
       at 9 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0862 (lit c4))) ▸
       at 13 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b35 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b35 = at 6 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 4 1 (Bx0-2413 ∷ []) (lem-sym34-at122441 c4) ▸
       at 4 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 4 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at12213443 c4) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (sym (wp0448 c4)) ▸ done

  b36 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ X4 ∷ CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b36 = at 11 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 10 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 9 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 11 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0341 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 4 (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0848 (lit c4))) ▸
       at 14 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4)) ▸ done

  b37 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ X4 ∷ CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b37 = at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 25 4 (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0440 c4)) ▸
       at 22 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0849 (lit c4))) ▸
       at 19 4 (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wl0850 (lit c4))) ▸
       at 16 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0849 (lit c4))) ▸ done

  b38 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ X4 ∷ K0 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b38 = at 13 4 (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wl0851 (lit c4))) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 15 5 (CCZ012 ∷ []) (sym (wl0602 (lit c4))) ▸
       at 10 4 (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0852 (lit c4))) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸ done

  b39 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ X4 ∷ K0 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b39 = at 14 2 [] (wl0283 (lit c4)) ▸
       at 12 3 (Toff012 ∷ []) (wl0341 (lit c4)) ▸
       at 13 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 12 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 11 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 6 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (sym (wp0448 c4)) ▸
       at 5 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 4 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸ done

  b40 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ X4 ∷ CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b40 = at 3 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 5 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0341 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 4 (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0848 (lit c4))) ▸
       at 8 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4)) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b41 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ X4 ∷ CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34 ∷ X4 ∷ CS01 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b41 = at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 4 (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0440 c4)) ▸
       at 16 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0849 (lit c4))) ▸
       at 13 4 (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wl0850 (lit c4))) ▸
       at 10 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0849 (lit c4))) ▸
       at 7 4 (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wl0851 (lit c4))) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸ done

  b42 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34 ∷ X4 ∷ CS01 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ X4 ∷ Toff012 ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b42 = at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 9 5 (CCZ012 ∷ []) (sym (wl0602 (lit c4))) ▸
       at 4 4 (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0852 (lit c4))) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 6 3 (Toff012 ∷ []) (wl0341 (lit c4)) ▸ done

  b43 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ X4 ∷ Toff012 ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2413 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b43 = at 7 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 6 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 5 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 7 4 (Bx0-2143 ∷ []) (sym (lem-beta-T-at12213443 c4)) ▸
       at 7 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸ done

  b44 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2413 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ [])
  b44 = at 7 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 7 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 7 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b45 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ [])
  b45 = at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 1 (CS12⁻ ∷ []) (refl) ▸
       at 18 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0874 (lit c4))) ▸
       at 31 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 15 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0875 (lit c4))) ▸
       at 13 1 (CS12 ∷ []) (refl) ▸ done

  b46 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ [])
  b46 = at 12 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0876 (lit c4))) ▸
       at 25 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 9 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0875 (lit c4))) ▸
       at 7 1 (Bx0-2413 ∷ []) (lem-sym34-at122441 c4) ▸
       at 7 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 7 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at12213443 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b47 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ X4 ∷ K3⁻ ∷ Toff012 ∷ X4 ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ [])
  b47 = at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (sym (wp0457 c4)) ▸
       at 14 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 13 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 12 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 13 4 (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (sym (wp0458 c4)) ▸
       at 16 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 15 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸ done

  b48 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ X4 ∷ K3⁻ ∷ Toff012 ∷ X4 ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ [])
  b48 = at 14 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 17 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 16 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 15 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 17 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0341 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 4 (CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0866 (lit c4))) ▸ done

  b49 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ [])
  b49 = at 20 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4)) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 30 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 31 4 (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0451 c4)) ▸
       at 28 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0867 (lit c4))) ▸
       at 25 4 (CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wl0868 (lit c4))) ▸ done

  b50 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ [])
  b50 = at 22 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0867 (lit c4))) ▸
       at 19 4 (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wl0869 (lit c4))) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 23 2 [] (wl0283 (lit c4)) ▸
       at 24 2 [] (wl0283 (lit c4)) ▸
       at 25 2 [] (wl0283 (lit c4)) ▸
       at 21 5 (CCZ012 ∷ []) (sym (wl0602 (lit c4))) ▸
       at 16 4 (CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0870 (lit c4))) ▸ done

  b51 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ [])
  b51 = at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 18 3 (Toff012 ∷ []) (wl0341 (lit c4)) ▸
       at 19 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 18 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 17 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 20 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 19 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸ done

  b52 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ Toff012 ∷ X4 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ [])
  b52 = at 18 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 19 4 (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (sym (wp0458 c4)) ▸
       at 22 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 21 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 20 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 23 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 22 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 21 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸ done

  b53 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ Toff012 ∷ X4 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ K3 ∷ X4 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ [])
  b53 = at 24 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 23 2 (CS23 ∷ Toff012 ∷ []) (sym (wl0226 (lit c4))) ▸
       at 22 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 25 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 24 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 23 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 9 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (sym (wp0457 c4)) ▸
       at 8 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸ done

  b54 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ K3 ∷ X4 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ [])
  b54 = at 7 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 6 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 7 4 (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (sym (wp0458 c4)) ▸
       at 10 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 9 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 8 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 11 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 10 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸ done

  b55 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ [])
  b55 = at 9 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 11 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0341 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 4 (CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0866 (lit c4))) ▸
       at 14 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4)) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b56 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CS01 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ [])
  b56 = at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 25 4 (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0451 c4)) ▸
       at 22 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0867 (lit c4))) ▸
       at 19 4 (CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wl0868 (lit c4))) ▸
       at 16 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0867 (lit c4))) ▸
       at 13 4 (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wl0869 (lit c4))) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸ done

  b57 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CS01 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ [])
  b57 = at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 15 5 (CCZ012 ∷ []) (sym (wl0602 (lit c4))) ▸
       at 10 4 (CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0870 (lit c4))) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 12 3 (Toff012 ∷ []) (wl0341 (lit c4)) ▸ done

  b58 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ X4 ∷ Toff012 ∷ K3⁻ ∷ X4 ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ [])
  b58 = at 13 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 12 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 11 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 14 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 13 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 12 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 13 4 (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (sym (wp0458 c4)) ▸
       at 16 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸ done

  b59 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ X4 ∷ Toff012 ∷ K3⁻ ∷ X4 ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ X4 ∷ Toff012 ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ [])
  b59 = at 15 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 14 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 17 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 16 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 15 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 18 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 17 2 (CS23 ∷ Toff012 ∷ []) (sym (wl0226 (lit c4))) ▸
       at 16 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸ done

  b60 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ X4 ∷ Toff012 ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Bx0-2413 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ [])
  b60 = at 19 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 18 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 17 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 19 4 (Bx0-2143 ∷ []) (sym (lem-beta-T-at12213443 c4)) ▸
       at 19 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸ done

  b61 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Bx0-2413 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ [])
  b61 = at 19 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 23 2 [] (wl0283 (lit c4)) ▸
       at 19 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 5 2 [] (wl0859 (lit c4)) ▸
       at 6 2 [] (wl0859 (lit c4)) ▸ done

  b62 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b62 = at 7 2 [] (wl0859 (lit c4)) ▸
       at 8 2 [] (wl0859 (lit c4)) ▸
       at 4 5 (CCZ234 ∷ []) (sym (wl0225 (lit c4))) ▸
       at 3 3 (Toff324 ∷ []) (wl0364 (lit c4)) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 2 (CS13⁻ ∷ X4 ∷ []) (sym (wl0742 (lit c4))) ▸
       at 6 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 2 (Sb⁻0-1-3-2 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·4·3·1⟩-at122441 c4) ▸ done

  b63 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b63 = at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 2 (CS13⁻ ∷ X4 ∷ []) (sym (wl0742 (lit c4))) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CS13 @122441: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS13-at122441 : Ws → ⟪ (Bx0-2431 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS13-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ CS23 ∷ []) (CS23 ∷ Bx0-2431 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ (lit c4)) ▸
       at 2 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0024 (lit c4))) ▸
       at 1 2 (CS13 ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at2442 c4) ▸
       at 0 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0025 (lit c4))) ▸
       at 1 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ134 @122441: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at122441 : Ws → ⟪ (Bx0-2431 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-2431 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ (lit c4)) ▸
       at 2 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2442 c4) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 (lit c4))) ▸
       at 1 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F5 CS23: 38 steps
lem-F5-CS23 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ []) ⟫ʷ
lem-F5-CS23 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CCZ123 ∷ Bx0-2431 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 1 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 8 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Bx0-2431 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (CCZ123 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ Toff134 ∷ Bx0-4231 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 10 1 (CS12 ∷ []) (refl) ▸
       at 12 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 6 (CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ []) (sym (wl0877 (lit c4))) ▸
       at 1 2 (CS23 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at122441 c4) ▸
       at 2 2 (CCZ123 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at122441 c4) ▸
       at 3 2 (CS12 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at122441 c4) ▸
       at 4 0 (Toff134 ∷ Toff134 ∷ []) (sym (wl0627 (lit c4))) ▸
       at 6 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸ done

  b2 : Chain (CCZ123 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ Toff134 ∷ Bx0-4231 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CCZ123 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Bx0-2431 ∷ Toff134 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b2 = at 6 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 6 1 (Bx0-4312 ∷ []) (lem-sym34-at14233241 c4) ▸
       at 5 3 (Bx0-4312 ∷ CCZ234 ∷ []) (lem-T312-beta-at14233142 c4) ▸
       at 5 1 (Bx0-4321 ∷ []) (lem-sym34-at14233142 c4) ▸
       at 5 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 5 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 5 2 (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 c4) ▸
       at 6 2 (CS12⁻ ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at122441 c4) ▸ done

  b3 : Chain (CCZ123 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Bx0-2431 ∷ Toff134 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CCZ123 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff134 ∷ Bx0-2431 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b3 = at 7 0 (Toff134 ∷ Toff134 ∷ []) (sym (wl0627 (lit c4))) ▸
       at 9 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 9 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 9 1 (Bx0-4312 ∷ []) (lem-sym34-at14233241 c4) ▸
       at 8 3 (Bx0-4312 ∷ CCZ234 ∷ []) (lem-T312-beta-at14233142 c4) ▸
       at 8 1 (Bx0-4321 ∷ []) (lem-sym34-at14233142 c4) ▸
       at 8 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 8 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸ done

  b4 : Chain (CCZ123 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff134 ∷ Bx0-2431 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS23 ∷ [])
  b4 = at 8 2 (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 c4) ▸
       at 1 5 (CCZ234 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ []) (sym (wl0878 (lit c4))) ▸
       at 2 7 (CCZ234 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ []) (sym (wl0879 (lit c4))) ▸
       at 1 2 [] (wl0265 (lit c4)) ▸
       at 7 2 [] (lem-beta-inv-at122441 c4) ▸
       at 0 11 (CS23 ∷ []) (wl0880 (lit c4)) ▸ done


-- auto CS01 | SBOX(2;0;31;4) @0213203441: 7 steps
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0213203441 : Ws → ⟪ (CS23 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS23 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0213203441 c4 = run b0
  where
  b0 : Chain (CS23 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS23 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0024 (lit c4))) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-43-2 ∷ CS13 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0113203442 c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0025 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F4 CS23^0|CS23^1: 63 steps
lem-F4-CS23ᵖ0∣CS23ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣CS23ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CS23 ∷ CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Bx⁻0-21 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ Toff024 ∷ CCZ024 ∷ [])
  b0 = at 0 4 (CS23 ∷ []) (lem-F5-CS23 c4) ▸
       at 1 0 (CCZ024 ∷ CCZ024 ∷ []) (sym (wp0034 c4)) ▸
       at 2 0 (Toff024 ∷ Toff024 ∷ []) (sym (wp0268 c4)) ▸
       at 3 0 (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ CZ12 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ []) (sym (wl0881 (lit c4))) ▸
       at 5 1 (Bx0-21 ∷ []) (refl) ▸
       at 8 1 (Bx0-21 ∷ []) (refl) ▸
       at 3 6 (Bx2-031 ∷ []) (refl) ▸
       at 4 1 (Bx⁻0-21 ∷ []) (refl) ▸ done

  b1 : Chain (CS23 ∷ CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Bx⁻0-21 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ Toff024 ∷ CCZ024 ∷ []) (CS23 ∷ CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ CZ12 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-031 ∷ Toff024 ∷ CCZ024 ∷ [])
  b1 = at 7 1 (Bx⁻0-21 ∷ []) (refl) ▸
       at 4 6 (Bx⁻2-031 ∷ []) (refl) ▸
       at 4 0 (Toff024 ∷ Toff024 ∷ []) (sym (wp0268 c4)) ▸
       at 5 0 (CCZ024 ∷ CCZ024 ∷ []) (sym (wp0034 c4)) ▸
       at 6 0 (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ CZ12 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ []) (sym (wl0881 (lit c4))) ▸
       at 8 1 (Bx0-21 ∷ []) (refl) ▸
       at 11 1 (Bx0-21 ∷ []) (refl) ▸
       at 6 6 (Bx2-031 ∷ []) (refl) ▸ done

  b2 : Chain (CS23 ∷ CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ CZ12 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-031 ∷ Toff024 ∷ CCZ024 ∷ []) (CS23 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CS12⁻ ∷ Toff134 ∷ Bx⁻0-2431 ∷ [])
  b2 = at 7 1 (Bx⁻0-21 ∷ []) (refl) ▸
       at 10 1 (Bx⁻0-21 ∷ []) (refl) ▸
       at 7 6 (Bx⁻2-031 ∷ []) (refl) ▸
       at 1 6 (Bx0-2431 ∷ []) (refl) ▸
       at 2 6 (Bx⁻0-2431 ∷ []) (refl) ▸
       at 2 0 (Toff134 ∷ Toff134 ∷ []) (sym (wl0627 (lit c4))) ▸
       at 3 0 (CS12 ∷ CS12⁻ ∷ []) (sym (wl0882 (lit c4))) ▸
       at 3 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b3 : Chain (CS23 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CS12⁻ ∷ Toff134 ∷ Bx⁻0-2431 ∷ []) (Sb0-2-43-1 ∷ CS23 ∷ Sb⁻0-2-43-1 ∷ [])
  b3 = at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 0 (Toff134 ∷ Toff134 ∷ []) (sym (wl0627 (lit c4))) ▸
       at 5 0 (CS12⁻ ∷ CS12 ∷ []) (sym (wl0187 (lit c4))) ▸
       at 5 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 1 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 2 5 (Sb⁻0-2-43-1 ∷ []) (refl) ▸
       at 0 2 (Sb0-2-43-1 ∷ CS23 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0213203441 c4) ▸ done

  b4 : Chain (Sb0-2-43-1 ∷ CS23 ∷ Sb⁻0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Sb⁻0-2-1-3 ∷ Toff134 ∷ Bx⁻0-2431 ∷ [])
  b4 = at 1 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-CS23 c4)) ▸
       at 5 1 (Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ Toff134 ∷ Bx⁻0-2431 ∷ []) (refl) ▸
       at 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (CS12⁻ ∷ []) (refl) ▸
       at 9 1 (CS12 ∷ []) (refl) ▸
       at 8 2 [] (wl0187 (lit c4)) ▸
       at 7 2 [] (wl0627 (lit c4)) ▸
       at 6 1 (CS12 ∷ []) (refl) ▸ done

  b5 : Chain (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Sb⁻0-2-1-3 ∷ Toff134 ∷ Bx⁻0-2431 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ Bx⁻2-031 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-031 ∷ Toff024 ∷ CCZ024 ∷ [])
  b5 = at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 6 2 [] (wl0882 (lit c4)) ▸
       at 5 2 [] (wl0627 (lit c4)) ▸
       at 5 1 (Bx⁻2-031 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-031 ∷ Toff024 ∷ CCZ024 ∷ []) (refl) ▸
       at 4 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 9 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 11 1 (CZ12 ∷ []) (refl) ▸
       at 14 1 (CZ12 ∷ []) (refl) ▸ done

  b6 : Chain (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ Bx⁻2-031 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-031 ∷ Toff024 ∷ CCZ024 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CCZ024 ∷ Toff024 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ Bx⁻2-031 ∷ Toff024 ∷ CCZ024 ∷ [])
  b6 = at 15 1 (Bx⁻0-21 ∷ CCZ023 ∷ Toff203 ∷ Bx⁻0-21 ∷ Toff203 ∷ CCZ023 ∷ []) (refl) ▸
       at 15 1 (CZ12 ∷ []) (refl) ▸
       at 18 1 (CZ12 ∷ []) (refl) ▸
       at 9 12 [] (wl0881 (lit c4)) ▸
       at 8 2 [] (wp0034 c4) ▸
       at 7 2 [] (wp0268 c4) ▸
       at 6 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 8 1 (CZ12 ∷ []) (refl) ▸ done

  b7 : Chain (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CCZ024 ∷ Toff024 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ Bx⁻2-031 ∷ Toff024 ∷ CCZ024 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b7 = at 11 1 (CZ12 ∷ []) (refl) ▸
       at 12 1 (Bx⁻0-21 ∷ CCZ023 ∷ Toff203 ∷ Bx⁻0-21 ∷ Toff203 ∷ CCZ023 ∷ []) (refl) ▸
       at 12 1 (CZ12 ∷ []) (refl) ▸
       at 15 1 (CZ12 ∷ []) (refl) ▸
       at 6 12 [] (wl0881 (lit c4)) ▸
       at 5 2 [] (wp0268 c4) ▸
       at 4 2 [] (wp0034 c4) ▸ done


-- auto BOXd(0;1234) | CS21: 5 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS21 : Ws → ⟪ (Bx⁻0-1234 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS21 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS12 ∷ []) (CS12 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 1 1 (CS12 ∷ []) (wl0270 (lit c4)) ▸
       at 0 2 (CS12 ∷ Bx0-1234 ∷ []) (sym (lem-CS12-beta c4)) ▸
       at 0 1 (CS12 ∷ []) (wl0270 (lit c4)) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CS21: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CS12 ∷ []) (CS14 ∷ CS12 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (CS12 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS21 c4) ▸
       at 3 2 (CS12 ∷ Toff423 ∷ []) (sym (wl0272 (lit c4))) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 2 (CS12 ∷ CS14⁻ ∷ []) (sym (wl0271 (lit c4))) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 1 2 (CS12 ∷ Toff423 ∷ []) (sym (wl0272 (lit c4))) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS14 ∷ CS12 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (CS12 ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 0 2 (CS12 ∷ CS14 ∷ []) (sym (wl0273 (lit c4))) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOXd(0;1;23;4) | CS21 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS13 ∷ []) (CS13 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 (lit c4)) ▸
       at 1 2 (CS12 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21 c4) ▸
       at 0 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 (lit c4)) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOXd(0;1234) | CS41: 9 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS41 : Ws → ⟪ (Bx⁻0-1234 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS41 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 1 1 (CS14 ∷ []) (wl0298 (lit c4)) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS14 ∷ Bx0-1423 ∷ []) (sym (lem-CS12-beta-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CS14 ∷ []) (wl0298 (lit c4)) ▸ done

  b1 : Chain (CS14 ∷ Bx0-1234 ∷ []) (CS14 ∷ Bx⁻0-1234 ∷ [])
  b1 = at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CS41: 9 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS41 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS41 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (CS14 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS41 c4) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 1 4 (CS14 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (sym (wl0325 (lit c4))) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ CS14 ∷ []) (wl0326 (lit c4)) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (CS14 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (CS14 ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOXd(0;1;23;4) | CS41 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS41-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS41-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS14 ∷ []) (CS14 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 (lit c4))) ▸
       at 1 2 (CS14 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS41 c4) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ143: 26 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CCZ134 ∷ []) (CS13 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX43 ∷ CS13⁻ ∷ CCZ024 ∷ CX43 ∷ CS14 ∷ [])
  b0 = at 1 1 (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (wl0653 (lit c4)) ▸
       at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 2 (CS13 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21-at2332 c4) ▸
       at 1 1 (Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ []) (refl) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-BOXd-BOX-at2332 c4) ▸
       at 5 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at2332 c4) ▸
       at 8 2 (CX43 ∷ CCZ024 ∷ []) (wp0459 c4) ▸
       at 9 2 (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 (lit c4)) ▸ done

  b1 : Chain (CS13 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX43 ∷ CS13⁻ ∷ CCZ024 ∷ CX43 ∷ CS14 ∷ []) (CS13 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ Bx⁻0-1324 ∷ CS14 ∷ [])
  b1 = at 10 2 (CX43 ∷ CCZ024 ∷ []) (wp0459 c4) ▸
       at 7 4 (CX43 ∷ CS13⁻ ∷ CX43 ∷ Toff013 ∷ []) (sym (wp0460 c4)) ▸
       at 6 2 (CX43 ∷ CCZ024 ∷ []) (wp0459 c4) ▸
       at 7 2 (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 (lit c4)) ▸
       at 8 2 (CX43 ∷ CCZ024 ∷ []) (wp0459 c4) ▸
       at 5 4 (CX43 ∷ CS13⁻ ∷ CX43 ∷ Toff013 ∷ []) (sym (wp0460 c4)) ▸
       at 8 4 (Bx0-1324 ∷ []) (sym (lem-beta-T-at2332 c4)) ▸
       at 8 1 (Bx⁻0-1324 ∷ []) (sym (lem-BOXd-BOX-at2332 c4)) ▸ done

  b2 : Chain (CS13 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ Bx⁻0-1324 ∷ CS14 ∷ []) (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ Sb⁻0-1-32-4 ∷ [])
  b2 = at 3 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 6 (CX43 ∷ CS13⁻ ∷ CX43 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (sym (wl0883 (lit c4))) ▸
       at 6 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 1 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (wl0884 (lit c4)) ▸
       at 4 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 4 5 (Sb⁻0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS14 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS41-at2332 c4) ▸ done

  b3 : Chain (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ Sb⁻0-1-32-4 ∷ []) (CCZ134 ∷ Sb⁻0-1-23-4 ∷ [])
  b3 = at 5 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸
       at 0 5 (CCZ134 ∷ []) (sym (wl0653 (lit c4))) ▸ done


-- auto SBOXd(0;1;23;4) | CS02 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS02-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS02-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS03 ∷ []) (CS03 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 (lit c4)) ▸
       at 1 2 (CS02 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS02 c4) ▸
       at 0 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4)) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | SBOX(1;0;3;4): 5 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩ : Ws → ⟪ (Sb⁻0-1-23-4 ∷ Sb1-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-4 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ Sb1-0-3-4 ∷ []) (Sb1-0-3-4 ∷ Sb⁻0-1-23-4 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 2 (CS03 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS02-at2332 c4) ▸
       at 1 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸
       at 0 1 (Sb1-0-3-4 ∷ []) (refl) ▸ done


-- auto BOXd(0;1234) | CSd02: 3 steps
lem-auto-BOXd⟨0·1234⟩-∣-CSd02 : Ws → ⟪ (Bx⁻0-1234 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CSd02 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 2 (CS02⁻ ∷ Bx0-1234 ∷ []) (sym (lem-CS20-beta-ci c4)) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CSd02: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd02 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd02 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CS02⁻ ∷ []) (CS14 ∷ CS02⁻ ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (CS02⁻ ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CSd02 c4) ▸
       at 3 2 (CS02⁻ ∷ Toff423 ∷ []) (sym (wp0371 c4)) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 2 (CS02⁻ ∷ CS14⁻ ∷ []) (sym (wp0370 c4)) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 1 2 (CS02⁻ ∷ Toff423 ∷ []) (sym (wp0371 c4)) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS14 ∷ CS02⁻ ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (CS02⁻ ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 0 2 (CS02⁻ ∷ CS14 ∷ []) (sym (wp0372 c4)) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOXd(0;1;23;4) | CSd02 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd02-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd02-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 (lit c4)) ▸
       at 1 2 (CS02⁻ ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd02 c4) ▸
       at 0 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 (lit c4)) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | SBOXd(1;0;3;4): 5 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩ : Ws → ⟪ (Sb⁻0-1-23-4 ∷ Sb⁻1-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-4 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ Sb⁻1-0-3-4 ∷ []) (Sb⁻1-0-3-4 ∷ Sb⁻0-1-23-4 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 2 (CS03⁻ ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd02-at2332 c4) ▸
       at 1 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸
       at 0 1 (Sb⁻1-0-3-4 ∷ []) (refl) ▸ done


-- AX-SB @3443: 7 steps
lem-AX-SB-at3443 : Ws → ⟪ (CS01 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS01 ∷ []) ⟫ʷ
lem-AX-SB-at3443 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 2 2 (Sb0-2-34-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 1 2 (Sb0-2-34-1 ∷ CS01 ∷ []) (lem-AX-SB c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·34·1⟩ (lit c4)) ▸
       at 1 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ143 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ143 @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at243243 : Ws → ⟪ (Sb⁻0-1-42-3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-42-3 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sb⁻0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at2332 c4) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 (lit c4)) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ143 @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at0110243243 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at243243 c4) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ143 @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at0210243143 : Ws → ⟪ (Sb⁻2-0-41-3 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at0110243243 c4) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4)) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | SBOX(1;0;3;4) @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ Sb1-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-4 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ Sb1-0-2-4 ∷ []) (Sb1-0-2-4 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Sb1-0-3-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·2·4⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-3-4 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩ c4) ▸
       at 0 2 (Sb1-0-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·3·4⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | SBOX(1;0;3;4) @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 : Ws → ⟪ (Sb⁻0-1-42-3 ∷ Sb1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-3 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-42-3 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-2-3 ∷ Sb⁻0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb1-0-2-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·2·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-2-4 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2332 c4) ▸
       at 0 2 (Sb1-0-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·2·4⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | SBOX(1;0;3;4) @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0110243243 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-3 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-2-3 ∷ Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb1-0-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·2·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-2-3 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 c4) ▸
       at 0 2 (Sb0-1-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·2·3⟩ (lit c4)) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | SBOX(1;0;3;4) @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0210243143 : Ws → ⟪ (Sb⁻2-0-41-3 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-3 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ Sb0-2-1-3 ∷ []) (Sb0-2-1-3 ∷ Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (Sb0-1-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·1·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0110243243 c4) ▸
       at 0 2 (Sb0-2-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·2·3⟩ (lit c4)) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | SBOXd(1;0;3;4) @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ Sb⁻1-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-4 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ Sb⁻1-0-2-4 ∷ []) (Sb⁻1-0-2-4 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Sb⁻1-0-3-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·2·4⟩ (lit c4)) ▸
       at 1 2 (Sb⁻1-0-3-4 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩ c4) ▸
       at 0 2 (Sb⁻1-0-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·3·4⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | SBOXd(1;0;3;4) @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 : Ws → ⟪ (Sb⁻0-1-42-3 ∷ Sb⁻1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-3 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-42-3 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-2-3 ∷ Sb⁻0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb⁻1-0-2-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·2·3⟩ (lit c4)) ▸
       at 1 2 (Sb⁻1-0-2-4 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2332 c4) ▸
       at 0 2 (Sb⁻1-0-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·2·4⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | SBOXd(1;0;3;4) @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0110243243 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-3 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb⁻1-0-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·2·3⟩ (lit c4)) ▸
       at 1 2 (Sb⁻1-0-2-3 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 c4) ▸
       at 0 2 (Sb⁻0-1-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·2·3⟩ (lit c4)) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | SBOXd(1;0;3;4) @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0210243143 : Ws → ⟪ (Sb⁻2-0-41-3 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-3 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-2-1-3 ∷ Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (Sb⁻0-1-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·1·3⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0110243243 c4) ▸
       at 0 2 (Sb⁻0-2-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·1·2·3⟩ (lit c4)) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D161 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0011 ; wl0012 ; wl0015 ; wl0016 ; wl0034 ; wl0035 ; wl0036 ; wl0037 ; wl0038 ; wl0039 ; wl0044 ; wl0047 ; wl0078 ; wl0084 ; wl0085 ; wl0086 ; wl0091 ; wl0096 ; wl0097 ; wl0099 ; wl0110 ; wl0111 ; wl0113 ; wl0116 ; wl0132 ; wl0133 ; wl0138 ; wl0139 ; wl0154 ; wl0155 ; wl0183 ; wl0212 ; wl0230 ; wl0244 ; wl0269 ; wl0332 ; wl0360 ; wl0596 ; wl0597 ; wl0598 ; wl0599 ; wl0600 ; wl0601 ; wl0602 ; wl0603 ; wl0604 ; wl0605 ; wl0606 ; wl0607 ; wl0608 ; wl0609 ; wl0610 ; wl0611 ; wl0612 ; wl0613 ; wl0614 ; wp0025 ; wp0118 ; wp0120 ; wp0260 ; wp0261 ; wp0262 ; wp0263 ; wp0264 ; wp0265)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0 ; lem-T-beta ; lem-T312-beta ; lem-T312-beta-at0314203142 ; lem-T312-beta-at0314213240 ; lem-c124-beta-at3443 ; lem-sym12 ; lem-sym12-at0314203142 ; lem-sym12-at1221 ; lem-sym12-at132132 ; lem-sym23 ; lem-sym23-at0314203142 ; lem-sym23-at0314213042 ; lem-sym23-at1221 ; lem-sym34 ; lem-sym34-at0314213042 ; lem-sym34-at0314213240 ; lem-sym34-at1221 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-Cz-beta-at12243143 ; lem-Cz-beta-at13243142 ; lem-SB2 ; lem-T312-beta-at2332 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 ; lem-beta-T-at03102132 ; lem-sym12-at233442 ; lem-sym23-at011220 ; lem-sym23-at01122330 ; lem-sym23-at12213443 ; lem-sym23-at122331 ; lem-sym23-at12243143 ; lem-sym23-at13213442 ; lem-sym23-at13243142 ; lem-sym23-at2332 ; lem-sym34-at12213443 ; lem-sym34-at122331 ; lem-sym34-at12233441 ; lem-sym34-at13213442 ; lem-sym34-at2332 ; lem-sym34-at233442)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F0-at1221 ; lem-F0-at3443 ; lem-SBsym-at0113203442 ; lem-T312-beta-at233442 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ134 ; lem-sym12-at13213442)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-CS20-beta-ci-at2332 ; lem-auto-BOX⟨0·1234⟩-∣-CS42 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-CS20-beta-c-at011220 ; lem-CS20-beta-ci-at011220)
open import Examples.Groups.Clifford+CS.Five.D.D089 using (lem-CSd12-beta-at12243143 ; lem-sym12-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-sym34-at0310243142 ; lem-sym34-at0310243241)
open import Examples.Groups.Clifford+CS.Five.D.D160 using (lem-F0-at0112203443 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ241 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ243 ; lem-sym12-at0410233142 ; lem-sym12-at0413203142 ; lem-sym23-at0413203142 ; lem-sym23-at0413213042 ; lem-sym23-at04233240 ; lem-sym23-at0440)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF024 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF301 ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF201 ; lem-nat-3-BOX⟨0·1324⟩ ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-BOX⟨3·4102⟩ ; lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF403 ; lem-nat-1-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-BOX⟨3·4012⟩ ; lem-nat-0-BOX⟨3·4021⟩ ; lem-nat-0-BOX⟨3·4120⟩ ; lem-nat-0-TOFF204 ; lem-nat-0-TOFF413 ; lem-nat-1-BOX⟨0·1234⟩ ; lem-nat-1-BOX⟨0·1324⟩ ; lem-nat-1-BOX⟨3·4012⟩ ; lem-nat-1-BOX⟨3·4021⟩ ; lem-nat-2-TOFF104 ; lem-nat-3-TOFF214 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-0-TOFF401 ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-1-TOFF401 ; lem-nat-2-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨2·0314⟩ ; lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0124⟩ ; lem-nat-2-BOX⟨3·0214⟩ ; lem-nat-2-BOX⟨3·0412⟩ ; lem-nat-2-CCZ014 ; lem-nat-2-TOFF402 ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-BOX⟨0·1342⟩ ; lem-nat-1-BOX⟨0·2341⟩ ; lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-1-BOX⟨3·0412⟩ ; lem-nat-1-CSd02 ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-2-CS02 ; lem-nat-2-CSd02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-2-TOFF403 ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨4·0231⟩ ; lem-nat-1-BOX⟨4·0312⟩ ; lem-nat-1-CSd01 ; lem-nat-3-BOX⟨3·0124⟩ ; lem-nat-3-BOX⟨4·0123⟩ ; lem-nat-3-SBOX⟨2·0·31·4⟩ ; lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨2·0314⟩ ; lem-nat-0-BOX⟨2·1304⟩ ; lem-nat-0-BOX⟨4·1230⟩ ; lem-nat-1-BOX⟨4·0132⟩ ; lem-nat-1-BOX⟨4·0231⟩ ; lem-nat-1-TOFF402 ; lem-nat-2-BOX⟨4·0123⟩ ; lem-nat-2-BOX⟨4·0132⟩ ; lem-nat-2-CS03 ; lem-nat-2-CSd03 ; lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-TOFF124 ; lem-nat-1-BOX⟨1·3240⟩ ; lem-nat-1-BOX⟨2·3140⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-BOX⟨3·0412⟩ ; lem-nat-0-BOX⟨3·4210⟩ ; lem-nat-1-BOX⟨0·3214⟩ ; lem-nat-1-BOX⟨3·4120⟩ ; lem-nat-1-SBOX⟨2·4·1·0⟩ ; lem-nat-2-SBOX⟨3·4·1·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-BOX⟨4·0321⟩ ; lem-nat-0-BOX⟨4·1023⟩ ; lem-nat-0-BOX⟨4·1320⟩ ; lem-nat-0-BOX⟨4·3102⟩ ; lem-nat-1-BOX⟨0·3241⟩ ; lem-nat-1-BOX⟨1·2304⟩ ; lem-nat-1-BOX⟨2·1304⟩ ; lem-nat-1-BOX⟨3·0421⟩ ; lem-nat-1-BOX⟨3·4102⟩ ; lem-nat-1-BOX⟨3·4201⟩ ; lem-nat-1-BOX⟨4·0123⟩ ; lem-nat-1-BOX⟨4·0213⟩ ; lem-nat-1-BOX⟨4·0321⟩ ; lem-nat-1-BOX⟨4·2013⟩ ; lem-nat-2-BOX⟨4·0213⟩ ; lem-nat-2-BOX⟨4·0312⟩ ; lem-nat-2-BOX⟨4·3012⟩ ; lem-nat-2-SBOX⟨2·4·1·0⟩ ; lem-nat-3-BOX⟨3·0214⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨0·3241⟩ ; lem-nat-0-BOX⟨1·3240⟩ ; lem-nat-0-BOX⟨3·0421⟩ ; lem-nat-0-BOX⟨3·1402⟩ ; lem-nat-0-BOX⟨3·1420⟩ ; lem-nat-0-BOX⟨3·4201⟩ ; lem-nat-0-SBOX⟨0·4·2·1⟩ ; lem-nat-0-SBOX⟨1·4·2·0⟩ ; lem-nat-0-SBOX⟨3·0·42·1⟩ ; lem-nat-0-SBOX⟨4·0·3·1⟩ ; lem-nat-0-SBOX⟨4·1·3·0⟩ ; lem-nat-1-BOX⟨0·3142⟩ ; lem-nat-1-BOX⟨4·1230⟩ ; lem-nat-1-BOX⟨4·2130⟩ ; lem-nat-1-SBOX⟨1·4·2·0⟩ ; lem-nat-1-SBOX⟨4·1·3·0⟩ ; lem-nat-1-SBOX⟨4·2·3·0⟩ ; lem-nat-1-SBOX⟨4·3·1·0⟩ ; lem-nat-1-SBOX⟨4·3·2·0⟩ ; lem-nat-2-BOX⟨2·3140⟩ ; lem-nat-2-BOX⟨3·2140⟩ ; lem-nat-2-BOX⟨4·1230⟩ ; lem-nat-2-BOX⟨4·1320⟩ ; lem-nat-2-SBOX⟨2·0·31·4⟩ ; lem-nat-2-SBOX⟨3·0·21·4⟩ ; lem-nat-2-SBOX⟨4·0·31·2⟩ ; lem-nat-2-SBOX⟨4·2·3·0⟩ ; lem-nat-2-SBOX⟨4·3·2·0⟩ ; lem-nat-2-SBOXd⟨4·0·2·1⟩ ; lem-nat-2-SBOXd⟨4·0·3·1⟩ ; lem-nat-3-BOX⟨3·2140⟩ ; lem-nat-3-BOX⟨4·0213⟩ ; lem-nat-3-BOX⟨4·2130⟩ ; lem-nat-3-SBOX⟨2·0·41·3⟩ ; lem-nat-3-SBOX⟨3·4·1·0⟩ ; lem-nat-3-SBOX⟨4·3·1·0⟩)
-- auto BOX(0;1234) | CSd42: 9 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd42 : Ws → ⟪ (Bx0-1234 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd42 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (wl0596 (lit c4)) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 0 2 (CS24⁻ ∷ Bx0-2413 ∷ []) (sym (lem-CSd12-beta-at12243143 c4)) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done

  b1 : Chain (CS24⁻ ∷ Bx0-1234 ∷ []) (CS24⁻ ∷ Bx0-1234 ∷ [])
  b1 = at 0 1 (CS24⁻ ∷ []) (wl0596 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CSd42: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42 : Ws → ⟪ (Sb0-1-23-4 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS24⁻ ∷ CS14⁻ ∷ []) (wl0597 (lit c4)) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CS24⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (sym (wl0598 (lit c4))) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd42 c4) ▸ done

  b1 : Chain (CS24⁻ ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS24⁻ ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CS42 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS34 ∷ []) (CS34 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 (lit c4))) ▸
       at 1 2 (CS24 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42 c4) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CSd42 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 (lit c4))) ▸
       at 1 2 (CS24⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd42 c4) ▸
       at 0 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- beta-T @0410213243: 8 steps
lem-beta-T-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) ⟫ʷ
lem-beta-T-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0123⟩ (lit c4)) ▸
       at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-beta-T-at03102132 c4) ▸
       at 0 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 2 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 (lit c4)) ▸
       at 3 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 4 2 [] (wl0007 (lit c4)) ▸ done


-- sym12 @1331: 5 steps
lem-sym12-at1331 : Ws → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-sym12-at1331 c4 = run b0
  where
  b0 : Chain (Bx0-3214 ∷ []) (Bx0-2314 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-3124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3214⟩ (lit c4)) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 0 2 (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CSd24: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd24 : Ws → ⟪ (Bx0-1234 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd24 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 0 2 (CS24⁻ ∷ Bx0-2413 ∷ []) (sym (lem-CSd12-beta-at12243143 c4)) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done


-- auto CSd01 | BOX(1;2304): 5 steps
lem-auto-CSd01-∣-BOX⟨1·2304⟩ : Ws → ⟪ (CS01⁻ ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2304⟩ c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx1-2304 ∷ []) (Bx1-2304 ∷ CS01⁻ ∷ [])
  b0 = at 0 1 (CS01⁻ ∷ []) (wl0360 (lit c4)) ▸
       at 1 1 (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4) ▸
       at 0 2 (Bx1-2034 ∷ CS01⁻ ∷ []) (lem-CS20-beta-ci-at011220 c4) ▸
       at 0 1 (Bx1-2304 ∷ []) (lem-sym23-at011220 c4) ▸
       at 1 1 (CS01⁻ ∷ []) (wl0360 (lit c4)) ▸ done


-- auto CSd01 | BOX(1;2304) @1221: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at1221 : Ws → ⟪ (CS02⁻ ∷ Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at1221 c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ Bx2-1304 ∷ []) (Bx2-1304 ∷ CS02⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 (lit c4)) ▸
       at 2 2 (Bx1-2304 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1304⟩ (lit c4)) ▸
       at 1 2 (Bx1-2304 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2304⟩ c4) ▸
       at 0 2 (Bx2-1304 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2304⟩ (lit c4)) ▸
       at 1 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CSd01 | BOX(1;2304) @011220: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at011220 : Ws → ⟪ (CS12⁻ ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at011220 c4 = run b0
  where
  b0 : Chain (CS12⁻ ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ CS12⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) (sym (wl0036 (lit c4))) ▸
       at 2 2 (Bx2-1304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0314⟩ (lit c4)) ▸
       at 1 2 (Bx2-1304 ∷ CS02⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2304⟩-at1221 c4) ▸
       at 0 2 (Bx2-0314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1304⟩ (lit c4)) ▸
       at 1 2 (CS12⁻ ∷ Sw01 ∷ []) (sym (wl0139 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(2;0314): 3 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩ : Ws → ⟪ (Sb⁻0-1-2-3 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩ c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Bx2-0314 ∷ CS12⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2304⟩-at011220 c4) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


-- sym12 @133441: 5 steps
lem-sym12-at133441 : Ws → ⟪ (Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-sym12-at133441 c4 = run b0
  where
  b0 : Chain (Bx0-3241 ∷ []) (Bx0-2341 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-3142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3241⟩ (lit c4)) ▸
       at 1 1 (Bx0-1342 ∷ []) (lem-sym12-at13213442 c4) ▸
       at 0 2 (Bx0-2341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1342⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- T-beta @1221: 7 steps
lem-T-beta-at1221 : Ws → ⟪ (Toff012 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ Toff012 ∷ []) ⟫ʷ
lem-T-beta-at1221 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ Toff012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ Toff012 ∷ []) (lem-T-beta c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- sym12 @12233441: 5 steps
lem-sym12-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-sym12-at12233441 c4 = run b0
  where
  b0 : Chain (Bx0-2341 ∷ []) (Bx0-3241 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2341⟩ (lit c4)) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-sym12-at233442 c4) ▸
       at 0 2 (Bx0-3241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3142⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- auto TOFF012 | BOX(0;3241): 9 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩ : Ws → ⟪ (Toff012 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff012 ∷ Bx0-3241 ∷ []) (Bx0-3241 ∷ Toff012 ∷ [])
  b0 = at 0 1 (Toff012 ∷ []) (wl0599 (lit c4)) ▸
       at 1 1 (Bx0-2341 ∷ []) (lem-sym12-at133441 c4) ▸
       at 1 1 (Bx0-2314 ∷ []) (lem-sym34-at12233441 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 0 2 (Bx0-2134 ∷ Toff012 ∷ []) (lem-T-beta-at1221 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 1 (Bx0-2341 ∷ []) (lem-sym34-at122331 c4) ▸
       at 0 1 (Bx0-3241 ∷ []) (lem-sym12-at12233441 c4) ▸ done

  b1 : Chain (Bx0-3241 ∷ Toff012 ∷ []) (Bx0-3241 ∷ Toff012 ∷ [])
  b1 = at 1 1 (Toff012 ∷ []) (wl0599 (lit c4)) ▸ done


-- auto CS01 | BOX(1;2304): 5 steps
lem-auto-CS01-∣-BOX⟨1·2304⟩ : Ws → ⟪ (CS01 ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2304⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx1-2304 ∷ []) (Bx1-2304 ∷ CS01 ∷ [])
  b0 = at 0 1 (CS01 ∷ []) (wl0332 (lit c4)) ▸
       at 1 1 (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4) ▸
       at 0 2 (Bx1-2034 ∷ CS01 ∷ []) (lem-CS20-beta-c-at011220 c4) ▸
       at 0 1 (Bx1-2304 ∷ []) (lem-sym23-at011220 c4) ▸
       at 1 1 (CS01 ∷ []) (wl0332 (lit c4)) ▸ done


-- auto CS01 | BOX(1;2304) @1221: 7 steps
lem-auto-CS01-∣-BOX⟨1·2304⟩-at1221 : Ws → ⟪ (CS02 ∷ Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2304⟩-at1221 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Bx2-1304 ∷ []) (Bx2-1304 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4)) ▸
       at 2 2 (Bx1-2304 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1304⟩ (lit c4)) ▸
       at 1 2 (Bx1-2304 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2304⟩ c4) ▸
       at 0 2 (Bx2-1304 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2304⟩ (lit c4)) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CS01 | BOX(1;2304) @011220: 7 steps
lem-auto-CS01-∣-BOX⟨1·2304⟩-at011220 : Ws → ⟪ (CS12 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ CS12 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2304⟩-at011220 c4 = run b0
  where
  b0 : Chain (CS12 ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ CS12 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (sym (wl0035 (lit c4))) ▸
       at 2 2 (Bx2-1304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0314⟩ (lit c4)) ▸
       at 1 2 (Bx2-1304 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2304⟩-at1221 c4) ▸
       at 0 2 (Bx2-0314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1304⟩ (lit c4)) ▸
       at 1 2 (CS12 ∷ Sw01 ∷ []) (sym (wl0138 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(2;0314): 3 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩ : Ws → ⟪ (Sb0-1-2-3 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-2-3 ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ Sb0-1-2-3 ∷ [])
  b0 = at 0 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (Bx2-0314 ∷ CS12 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2304⟩-at011220 c4) ▸
       at 1 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done


-- auto CCZ012 | CS34: 1 steps
lem-auto-CCZ012-∣-CS34 : Ws → ⟪ (CCZ012 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CS34 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CS34 ∷ []) (CS34 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸ done


-- auto CCZ012 | CS34 @3443: 7 steps
lem-auto-CCZ012-∣-CS34-at3443 : Ws → ⟪ (CCZ012 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CS34-at3443 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CS34 ∷ []) (CS34 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0039 (lit c4))) ▸
       at 1 2 (CS34 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CS34 c4) ▸
       at 0 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0039 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ403: 11 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ403 : Ws → ⟪ (Bx0-1234 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ403 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx0-3124 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ []) (wp0025 c4) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym12-at233442 c4) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4) ▸
       at 0 2 (CCZ034 ∷ Bx0-3412 ∷ []) (sym (lem-Cz-beta-at13243142 c4)) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4) ▸ done

  b1 : Chain (CCZ034 ∷ Bx0-3124 ∷ []) (CCZ034 ∷ Bx0-1234 ∷ [])
  b1 = at 1 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (CCZ034 ∷ []) (wp0025 c4) ▸ done


-- auto CCZ012 | CCZ342: 15 steps
lem-auto-CCZ012-∣-CCZ342 : Ws → ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ CCZ234 ∷ []) (CS23 ∷ CS01 ∷ CX21 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ CS34 ∷ [])
  b0 = at 1 1 (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (wl0600 (lit c4)) ▸
       at 0 2 (CS23 ∷ CCZ012 ∷ []) (wl0601 (lit c4)) ▸
       at 1 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4)) ▸
       at 5 4 (CX42 ∷ CS23⁻ ∷ CX42 ∷ CS02 ∷ []) (wp0260 c4) ▸
       at 4 4 (CX42 ∷ CS23⁻ ∷ CX42 ∷ CX21 ∷ []) (wl0603 (lit c4)) ▸
       at 3 2 (CX42 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑ • CX₁₀ • Swap ↑)) ▸
       at 4 2 (CS23⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CS • CS • CS)) ▸
       at 5 2 (CX42 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑ • CX₁₀ • Swap ↑)) ▸ done

  b1 : Chain (CS23 ∷ CS01 ∷ CX21 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ CS34 ∷ []) (CCZ234 ∷ CCZ012 ∷ [])
  b1 = at 2 4 (CX42 ∷ CS23⁻ ∷ CX42 ∷ CX21 ∷ []) (wl0603 (lit c4)) ▸
       at 1 2 (CX42 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑ • CX₁₀ • Swap ↑)) ▸
       at 2 2 (CS23⁻ ∷ CS01 ∷ []) (c₂ (CS) (CS • CS • CS)) ▸
       at 3 2 (CX42 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑ • CX₁₀ • Swap ↑)) ▸
       at 4 5 (CCZ012 ∷ []) (sym (wl0602 (lit c4))) ▸
       at 4 2 (CS34 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CS34-at3443 c4) ▸
       at 0 5 (CCZ234 ∷ []) (sym (wl0600 (lit c4))) ▸ done


-- auto BOX(0;1234) | CCZ402: 9 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ402 : Ws → ⟪ (Bx0-1234 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ402 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ []) (wp0261 c4) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 0 2 (CCZ024 ∷ Bx0-2413 ∷ []) (sym (lem-Cz-beta-at12243143 c4)) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Bx0-1234 ∷ []) (CCZ024 ∷ Bx0-1234 ∷ [])
  b1 = at 0 1 (CCZ024 ∷ []) (wp0261 c4) ▸ done


-- auto BOX(0;1234) | CCZ132: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ132 : Ws → ⟪ (Bx0-1234 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ132 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ []) (wl0269 (lit c4)) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 2 (CCZ123 ∷ Bx0-1243 ∷ []) (sym (lem-c124-beta-at3443 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CCZ123 ∷ []) (wl0269 (lit c4)) ▸ done


-- beta-T @04203243: 8 steps
lem-beta-T-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) ⟫ʷ
lem-beta-T-at04203243 c4 = run b0
  where
  b0 : Chain (Bx4-1023 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx4-0123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1023⟩ (lit c4)) ▸
       at 1 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-beta-T-at0410213243 c4) ▸
       at 0 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 2 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 (lit c4)) ▸
       at 3 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 4 2 [] (wl0002 (lit c4)) ▸ done


-- beta-T @0412203143: 8 steps
lem-beta-T-at0412203143 : Ws → ⟪ (Bx4-2013 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) ⟫ʷ
lem-beta-T-at0412203143 c4 = run b0
  where
  b0 : Chain (Bx4-2013 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx4-1023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·2013⟩ (lit c4)) ▸
       at 1 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-beta-T-at04203243 c4) ▸
       at 0 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 2 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 (lit c4)) ▸
       at 3 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- beta-T @0413203142: 8 steps
lem-beta-T-at0413203142 : Ws → ⟪ (Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) ⟫ʷ
lem-beta-T-at0413203142 c4 = run b0
  where
  b0 : Chain (Bx4-3012 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx4-2013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·3012⟩ (lit c4)) ▸
       at 1 1 (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-beta-T-at0412203143 c4) ▸
       at 0 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 2 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 (lit c4)) ▸
       at 3 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 4 2 [] (wl0006 (lit c4)) ▸ done


-- beta-T @0413213042: 8 steps
lem-beta-T-at0413213042 : Ws → ⟪ (Bx4-3102 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) ⟫ʷ
lem-beta-T-at0413213042 c4 = run b0
  where
  b0 : Chain (Bx4-3102 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx4-3012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·3102⟩ (lit c4)) ▸
       at 1 1 (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) (lem-beta-T-at0413203142 c4) ▸
       at 0 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4)) ▸
       at 2 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4)) ▸
       at 4 2 [] (wl0002 (lit c4)) ▸ done


-- auto CCZ012 | CCZ342 @0110: 7 steps
lem-auto-CCZ012-∣-CCZ342-at0110 : Ws → ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at0110 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 (lit c4))) ▸
       at 2 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ342 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CCZ012 | CCZ342 @021021: 7 steps
lem-auto-CCZ012-∣-CCZ342-at021021 : Ws → ⟪ (CCZ012 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at021021 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0110 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | CCZ342 @03102132: 7 steps
lem-auto-CCZ012-∣-CCZ342-at03102132 : Ws → ⟪ (CCZ013 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at03102132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at021021 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CCZ012 | CCZ342 @0410213243: 7 steps
lem-auto-CCZ012-∣-CCZ342-at0410213243 : Ws → ⟪ (CCZ014 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at0410213243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at03102132 c4) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CCZ012 | CCZ342 @04103143: 7 steps
lem-auto-CCZ012-∣-CCZ342-at04103143 : Ws → ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at04103143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0410213243 c4) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 (lit c4))) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(4;0312): 31 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·0312⟩ : Ws → ⟪ (Bx0-1234 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·0312⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Bx0-1234 ∷ Bx4-0312 ∷ []) (Toff413 ∷ Toff413 ∷ Bx0-1342 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ [])
  b0 = at 1 1 (Bx4-3012 ∷ []) (lem-sym12-at0410233142 c4) ▸
       at 1 1 (Bx4-3102 ∷ []) (lem-sym23-at0413203142 c4) ▸
       at 1 1 (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-beta-T-at0413213042 c4) ▸
       at 0 0 (Toff413 ∷ Toff413 ∷ []) (sym (wl0604 (lit c4))) ▸
       at 1 1 (Toff413 ∷ []) (wl0605 (lit c4)) ▸
       at 3 1 (Toff413 ∷ []) (wl0605 (lit c4)) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 2 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸ done

  b1 : Chain (Toff413 ∷ Toff413 ∷ Bx0-1342 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (Toff413 ∷ CCZ123 ∷ CCZ024 ∷ Toff413 ∷ Toff413 ∷ Bx0-1234 ∷ Toff413 ∷ CCZ024 ∷ [])
  b1 = at 1 3 (Bx0-1342 ∷ CCZ123 ∷ []) (lem-T312-beta-at233442 c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym34-at233442 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 1 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ132 c4) ▸
       at 2 2 (CCZ024 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ402 c4) ▸
       at 3 0 (Toff413 ∷ Toff413 ∷ []) (sym (wl0604 (lit c4))) ▸
       at 4 1 (Toff413 ∷ []) (wl0605 (lit c4)) ▸
       at 6 1 (Toff413 ∷ []) (wl0605 (lit c4)) ▸ done

  b2 : Chain (Toff413 ∷ CCZ123 ∷ CCZ024 ∷ Toff413 ∷ Toff413 ∷ Bx0-1234 ∷ Toff413 ∷ CCZ024 ∷ []) (CCZ123 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ123 ∷ CCZ024 ∷ Bx0-1234 ∷ [])
  b2 = at 5 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 5 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 4 3 (Bx0-1342 ∷ CCZ123 ∷ []) (lem-T312-beta-at233442 c4) ▸
       at 4 1 (Bx0-1324 ∷ []) (lem-sym34-at233442 c4) ▸
       at 4 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 4 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ132 c4) ▸
       at 5 2 (CCZ024 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ402 c4) ▸
       at 0 2 (CCZ123 ∷ Toff413 ∷ []) (sym (wl0606 (lit c4))) ▸ done

  b3 : Chain (CCZ123 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ123 ∷ CCZ024 ∷ Bx0-1234 ∷ []) (Bx4-0312 ∷ Bx0-1234 ∷ [])
  b3 = at 3 2 (CCZ123 ∷ Toff413 ∷ []) (sym (wl0606 (lit c4))) ▸
       at 2 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at04103143 c4) ▸
       at 1 2 (CCZ123 ∷ Toff413 ∷ []) (sym (wl0606 (lit c4))) ▸
       at 0 2 [] (wl0212 (lit c4)) ▸
       at 0 4 (Bx4-3102 ∷ []) (sym (lem-beta-T-at0413213042 c4)) ▸
       at 0 1 (Bx4-3012 ∷ []) (lem-sym23-at0413213042 c4) ▸
       at 0 1 (Bx4-0312 ∷ []) (lem-sym12-at0413203142 c4) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(2;0314) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2332 : Ws → ⟪ (Sb⁻0-1-3-2 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-3-2 ∷ Bx3-0214 ∷ []) (Bx3-0214 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 (Bx2-0314 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0214⟩ (lit c4)) ▸
       at 1 2 (Bx2-0314 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩ c4) ▸
       at 0 2 (Bx3-0214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0314⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(2;0314) @243243: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at243243 : Ws → ⟪ (Sb⁻0-1-4-2 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-2 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Sb⁻0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ (lit c4)) ▸
       at 2 2 (Bx3-0214 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0213⟩ (lit c4)) ▸
       at 1 2 (Bx3-0214 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2332 c4) ▸
       at 0 2 (Bx4-0213 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0214⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(2;0314) @2442: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2442 : Ws → ⟪ (Sb⁻0-1-4-3 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-3 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ (lit c4)) ▸
       at 2 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ (lit c4)) ▸
       at 1 2 (Bx4-0213 ∷ Sb⁻0-1-4-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at243243 c4) ▸
       at 0 2 (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto TOFF012 | BOX(0;3241) @0110: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0110 : Ws → ⟪ (Toff102 ∷ Bx1-3240 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3240 ∷ Toff102 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0110 c4 = run b0
  where
  b0 : Chain (Toff102 ∷ Bx1-3240 ∷ []) (Bx1-3240 ∷ Toff102 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 (lit c4)) ▸
       at 2 2 (Bx0-3241 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3240⟩ (lit c4)) ▸
       at 1 2 (Bx0-3241 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩ c4) ▸
       at 0 2 (Bx1-3240 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3241⟩ (lit c4)) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto TOFF012 | BOX(0;3241) @021021: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at021021 : Ws → ⟪ (Toff201 ∷ Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ Toff201 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at021021 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Bx2-3140 ∷ []) (Bx2-3140 ∷ Toff201 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 (lit c4)) ▸
       at 2 2 (Bx1-3240 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3140⟩ (lit c4)) ▸
       at 1 2 (Bx1-3240 ∷ Toff102 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0110 c4) ▸
       at 0 2 (Bx2-3140 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3240⟩ (lit c4)) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto TOFF012 | BOX(0;3241) @03102132: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at03102132 : Ws → ⟪ (Toff301 ∷ Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ Toff301 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at03102132 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Bx3-2140 ∷ []) (Bx3-2140 ∷ Toff301 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 (lit c4)) ▸
       at 2 2 (Bx2-3140 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·2140⟩ (lit c4)) ▸
       at 1 2 (Bx2-3140 ∷ Toff201 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at021021 c4) ▸
       at 0 2 (Bx3-2140 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·3140⟩ (lit c4)) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto TOFF012 | BOX(0;3241) @0410213243: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0410213243 : Ws → ⟪ (Toff401 ∷ Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ Toff401 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (Toff401 ∷ Bx4-2130 ∷ []) (Bx4-2130 ∷ Toff401 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 (lit c4)) ▸
       at 2 2 (Bx3-2140 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·2130⟩ (lit c4)) ▸
       at 1 2 (Bx3-2140 ∷ Toff301 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at03102132 c4) ▸
       at 0 2 (Bx4-2130 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·2140⟩ (lit c4)) ▸
       at 1 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto TOFF012 | BOX(0;3241) @04103143: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at04103143 : Ws → ⟪ (Toff402 ∷ Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ Toff402 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at04103143 c4 = run b0
  where
  b0 : Chain (Toff402 ∷ Bx4-1230 ∷ []) (Bx4-1230 ∷ Toff402 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 (lit c4)) ▸
       at 2 2 (Bx4-2130 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·1230⟩ (lit c4)) ▸
       at 1 2 (Bx4-2130 ∷ Toff401 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0410213243 c4) ▸
       at 0 2 (Bx4-1230 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·2130⟩ (lit c4)) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto TOFF012 | BOX(0;3241) @0410233142: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0410233142 : Ws → ⟪ (Toff403 ∷ Bx4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ Toff403 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0410233142 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ Bx4-1320 ∷ []) (Bx4-1320 ∷ Toff403 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 (lit c4)) ▸
       at 2 2 (Bx4-1230 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·1320⟩ (lit c4)) ▸
       at 1 2 (Bx4-1230 ∷ Toff402 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at04103143 c4) ▸
       at 0 2 (Bx4-1320 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·1230⟩ (lit c4)) ▸
       at 1 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto TOFF012 | BOX(0;3241) @04233042: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at04233042 : Ws → ⟪ (Toff413 ∷ Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ Toff413 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at04233042 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ Bx4-0321 ∷ []) (Bx4-0321 ∷ Toff413 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 (lit c4)) ▸
       at 2 2 (Bx4-1320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0321⟩ (lit c4)) ▸
       at 1 2 (Bx4-1320 ∷ Toff403 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0410233142 c4) ▸
       at 0 2 (Bx4-0321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1320⟩ (lit c4)) ▸
       at 1 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto TOFF012 | BOX(0;3241) @0412233041: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0412233041 : Ws → ⟪ (Toff423 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Toff423 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0412233041 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Toff423 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (wl0091 (lit c4)) ▸
       at 2 2 (Bx4-0321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0312⟩ (lit c4)) ▸
       at 1 2 (Bx4-0321 ∷ Toff413 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at04233042 c4) ▸
       at 0 2 (Bx4-0312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0321⟩ (lit c4)) ▸
       at 1 2 (Toff423 ∷ Sw12 ∷ []) (wl0085 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(2;0314) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2332 : Ws → ⟪ (Sb0-1-3-2 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-3-2 ∷ Bx3-0214 ∷ []) (Bx3-0214 ∷ Sb0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 (Bx2-0314 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0214⟩ (lit c4)) ▸
       at 1 2 (Bx2-0314 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩ c4) ▸
       at 0 2 (Bx3-0214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0314⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(2;0314) @243243: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at243243 : Ws → ⟪ (Sb0-1-4-2 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-2 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Sb0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ (lit c4)) ▸
       at 2 2 (Bx3-0214 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0213⟩ (lit c4)) ▸
       at 1 2 (Bx3-0214 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2332 c4) ▸
       at 0 2 (Bx4-0213 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0214⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(2;0314) @2442: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2442 : Ws → ⟪ (Sb0-1-4-3 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-3 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Sb0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ (lit c4)) ▸
       at 2 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ (lit c4)) ▸
       at 1 2 (Bx4-0213 ∷ Sb0-1-4-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at243243 c4) ▸
       at 0 2 (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | BOX(4;0312): 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0312⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0312⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 2 (Bx4-0312 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2442 c4) ▸
       at 3 2 (Bx4-0312 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0412233041 c4) ▸
       at 2 2 (Bx4-0312 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2442 c4) ▸
       at 1 2 (Bx4-0312 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0412233041 c4) ▸
       at 0 2 (Bx4-0312 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·0312⟩ c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | SBOX(0;4;2;1): 3 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩ : Ws → ⟪ (Bx0-1234 ∷ Sb0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-2-1 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩ c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Sb0-4-2-1 ∷ []) (Sb0-4-2-1 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS42 c4) ▸
       at 0 1 (Sb0-4-2-1 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CSd03: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd03 : Ws → ⟪ (Bx0-1234 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd03 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CS03⁻ ∷ Bx0-1324 ∷ []) (sym (lem-CS20-beta-ci-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸ done


-- auto SBOX(0;1;23;4) | CSd03: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd03 : Ws → ⟪ (Sb0-1-23-4 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd03 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS03⁻ ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS03⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS03⁻ ∷ CS14⁻ ∷ []) (sym (wp0118 c4)) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS03⁻ ∷ Toff423 ∷ []) (sym (wp0262 c4)) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS03⁻ ∷ CS14 ∷ []) (sym (wp0120 c4)) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS03⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS03⁻ ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS03⁻ ∷ Toff423 ∷ []) (sym (wp0262 c4)) ▸
       at 0 2 (CS03⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd03 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd03 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd03-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd03-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 (lit c4)) ▸
       at 1 2 (CS03⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd03 c4) ▸
       at 0 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(4;0;2;1): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·2·1⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb⁻4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-2-1 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻4-0-2-1 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS02⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd03-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb⁻4-0-2-1 ∷ []) (refl) ▸ done


-- F0 @233442: 5 steps
lem-F0-at233442 : Ws → ⟪ (Sb3-0-21-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-21-3 ∷ []) ⟫ʷ
lem-F0-at233442 c4 = run b0
  where
  b0 : Chain (Sb3-0-21-4 ∷ []) (Sb4-0-21-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb2-0-31-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·21·4⟩ (lit c4)) ▸
       at 1 1 (Sb4-0-31-2 ∷ []) (lem-F0-at3443 c4) ▸
       at 0 2 (Sb4-0-21-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·0·31·2⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | BOX(4;0312) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0312⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0312⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ (lit c4)) ▸
       at 1 2 (Bx4-0312 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0312⟩ c4) ▸
       at 0 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- T312-beta @0110: 8 steps
lem-T312-beta-at0110 : Ws → ⟪ (Toff302 ∷ Bx1-0234 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CCZ024 ∷ []) ⟫ʷ
lem-T312-beta-at0110 c4 = run b0
  where
  b0 : Chain (Toff302 ∷ Bx1-0234 ∷ Toff302 ∷ []) (Bx1-0234 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4)) ▸
       at 3 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 (lit c4)) ▸
       at 1 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-T312-beta c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- T312-beta @021021: 8 steps
lem-T312-beta-at021021 : Ws → ⟪ (Toff301 ∷ Bx2-0134 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ CCZ014 ∷ []) ⟫ʷ
lem-T312-beta-at021021 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Bx2-0134 ∷ Toff301 ∷ []) (Bx2-0134 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 (lit c4)) ▸
       at 2 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4)) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 (lit c4)) ▸
       at 1 3 (Bx1-0234 ∷ CCZ024 ∷ []) (lem-T312-beta-at0110 c4) ▸
       at 0 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- T312-beta @03102132: 8 steps
lem-T312-beta-at03102132 : Ws → ⟪ (Toff201 ∷ Bx3-0124 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ CCZ014 ∷ []) ⟫ʷ
lem-T312-beta-at03102132 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Bx3-0124 ∷ Toff201 ∷ []) (Bx3-0124 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 (lit c4)) ▸
       at 2 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ (lit c4)) ▸
       at 3 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 (lit c4)) ▸
       at 1 3 (Bx2-0134 ∷ CCZ014 ∷ []) (lem-T312-beta-at021021 c4) ▸
       at 0 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- T312-beta @0410213243: 8 steps
lem-T312-beta-at0410213243 : Ws → ⟪ (Toff201 ∷ Bx4-0123 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ CCZ013 ∷ []) ⟫ʷ
lem-T312-beta-at0410213243 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Bx4-0123 ∷ Toff201 ∷ []) (Bx4-0123 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 2 2 (Bx3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0123⟩ (lit c4)) ▸
       at 3 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 1 3 (Bx3-0124 ∷ CCZ014 ∷ []) (lem-T312-beta-at03102132 c4) ▸
       at 0 2 (Bx4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0124⟩ (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- T312-beta @04102142: 8 steps
lem-T312-beta-at04102142 : Ws → ⟪ (Toff301 ∷ Bx4-0132 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0132 ∷ CCZ012 ∷ []) ⟫ʷ
lem-T312-beta-at04102142 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Bx4-0132 ∷ Toff301 ∷ []) (Bx4-0132 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 (lit c4)) ▸
       at 2 2 (Bx4-0123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0132⟩ (lit c4)) ▸
       at 3 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 (lit c4)) ▸
       at 1 3 (Bx4-0123 ∷ CCZ013 ∷ []) (lem-T312-beta-at0410213243 c4) ▸
       at 0 2 (Bx4-0132 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0123⟩ (lit c4)) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- T312-beta @041041: 8 steps
lem-T312-beta-at041041 : Ws → ⟪ (Toff302 ∷ Bx4-0231 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ CCZ012 ∷ []) ⟫ʷ
lem-T312-beta-at041041 c4 = run b0
  where
  b0 : Chain (Toff302 ∷ Bx4-0231 ∷ Toff302 ∷ []) (Bx4-0231 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 (lit c4)) ▸
       at 2 2 (Bx4-0132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0231⟩ (lit c4)) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 (lit c4)) ▸
       at 1 3 (Bx4-0132 ∷ CCZ012 ∷ []) (lem-T312-beta-at04102142 c4) ▸
       at 0 2 (Bx4-0231 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0132⟩ (lit c4)) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- T312-beta @0440: 8 steps
lem-T312-beta-at0440 : Ws → ⟪ (Toff312 ∷ Bx4-1230 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ CCZ012 ∷ []) ⟫ʷ
lem-T312-beta-at0440 c4 = run b0
  where
  b0 : Chain (Toff312 ∷ Bx4-1230 ∷ Toff312 ∷ []) (Bx4-1230 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (wl0110 (lit c4)) ▸
       at 2 2 (Bx4-0231 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1230⟩ (lit c4)) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (wl0110 (lit c4)) ▸
       at 1 3 (Bx4-0231 ∷ CCZ012 ∷ []) (lem-T312-beta-at041041 c4) ▸
       at 0 2 (Bx4-1230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0231⟩ (lit c4)) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ134 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0110 : Ws → ⟪ (Bx1-0234 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134 c4) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4)) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ134 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at021021 : Ws → ⟪ (Bx2-0134 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4)) ▸
       at 2 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0110 c4) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ134 @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at03102132 : Ws → ⟪ (Bx3-0124 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ (lit c4)) ▸
       at 2 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at021021 c4) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ134 @0410213243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Bx4-0123 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ CCZ023 ∷ []) (CCZ023 ∷ Bx4-0123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0123⟩ (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at03102132 c4) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 (lit c4)) ▸
       at 1 2 (Bx4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0124⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ134 @04103143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at04103143 : Ws → ⟪ (Bx4-0213 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Bx4-0213 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at04103143 c4 = run b0
  where
  b0 : Chain (Bx4-0213 ∷ CCZ013 ∷ []) (CCZ013 ∷ Bx4-0213 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx4-0123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0213⟩ (lit c4)) ▸
       at 2 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ Bx4-0123 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410213243 c4) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4)) ▸
       at 1 2 (Bx4-0213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0123⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ134 @0410233142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410233142 : Ws → ⟪ (Bx4-0312 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx4-0312 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410233142 c4 = run b0
  where
  b0 : Chain (Bx4-0312 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx4-0312 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ (lit c4)) ▸
       at 2 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Bx4-0213 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at04103143 c4) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 1 2 (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ134 @0410233241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410233241 : Ws → ⟪ (Bx4-0321 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx4-0321 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410233241 c4 = run b0
  where
  b0 : Chain (Bx4-0321 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx4-0321 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx4-0312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0321⟩ (lit c4)) ▸
       at 2 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Bx4-0312 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410233142 c4) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 1 2 (Bx4-0321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0312⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ134 @04233240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at04233240 : Ws → ⟪ (Bx4-1320 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx4-1320 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at04233240 c4 = run b0
  where
  b0 : Chain (Bx4-1320 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx4-1320 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx4-0321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1320⟩ (lit c4)) ▸
       at 2 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Bx4-0321 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0410233241 c4) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 (lit c4))) ▸
       at 1 2 (Bx4-1320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0321⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | SBOX(0;4;2;1) @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0110 : Ws → ⟪ (Bx1-0234 ∷ Sb1-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-2-0 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ Sb1-4-2-0 ∷ []) (Sb1-4-2-0 ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 (Sb0-4-2-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·4·2·0⟩ (lit c4)) ▸
       at 1 2 (Sb0-4-2-1 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩ c4) ▸
       at 0 2 (Sb1-4-2-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·4·2·1⟩ (lit c4)) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | SBOX(0;4;2;1) @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at021021 : Ws → ⟪ (Bx2-0134 ∷ Sb2-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-1-0 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ Sb2-4-1-0 ∷ []) (Sb2-4-1-0 ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4)) ▸
       at 2 2 (Sb1-4-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·4·1·0⟩ (lit c4)) ▸
       at 1 2 (Sb1-4-2-0 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0110 c4) ▸
       at 0 2 (Sb2-4-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·4·2·0⟩ (lit c4)) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | SBOX(0;4;2;1) @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at03102132 : Ws → ⟪ (Bx3-0124 ∷ Sb3-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-1-0 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ Sb3-4-1-0 ∷ []) (Sb3-4-1-0 ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ (lit c4)) ▸
       at 2 2 (Sb2-4-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·4·1·0⟩ (lit c4)) ▸
       at 1 2 (Sb2-4-1-0 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at021021 c4) ▸
       at 0 2 (Sb3-4-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·4·1·0⟩ (lit c4)) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | SBOX(0;4;2;1) @0410213243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ Sb4-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-3-1-0 ∷ Bx4-0123 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ Sb4-3-1-0 ∷ []) (Sb4-3-1-0 ∷ Bx4-0123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0123⟩ (lit c4)) ▸
       at 2 2 (Sb3-4-1-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨4·3·1·0⟩ (lit c4)) ▸
       at 1 2 (Sb3-4-1-0 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at03102132 c4) ▸
       at 0 2 (Sb4-3-1-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨3·4·1·0⟩ (lit c4)) ▸
       at 1 2 (Bx4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0124⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | SBOX(0;4;2;1) @04103143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at04103143 : Ws → ⟪ (Bx4-0213 ∷ Sb4-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-3-2-0 ∷ Bx4-0213 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at04103143 c4 = run b0
  where
  b0 : Chain (Bx4-0213 ∷ Sb4-3-2-0 ∷ []) (Sb4-3-2-0 ∷ Bx4-0213 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx4-0123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0213⟩ (lit c4)) ▸
       at 2 2 (Sb4-3-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨4·3·2·0⟩ (lit c4)) ▸
       at 1 2 (Sb4-3-1-0 ∷ Bx4-0123 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410213243 c4) ▸
       at 0 2 (Sb4-3-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨4·3·1·0⟩ (lit c4)) ▸
       at 1 2 (Bx4-0213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0123⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | SBOX(0;4;2;1) @0410233142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410233142 : Ws → ⟪ (Bx4-0312 ∷ Sb4-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-3-0 ∷ Bx4-0312 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410233142 c4 = run b0
  where
  b0 : Chain (Bx4-0312 ∷ Sb4-2-3-0 ∷ []) (Sb4-2-3-0 ∷ Bx4-0312 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ (lit c4)) ▸
       at 2 2 (Sb4-3-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·2·3·0⟩ (lit c4)) ▸
       at 1 2 (Sb4-3-2-0 ∷ Bx4-0213 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at04103143 c4) ▸
       at 0 2 (Sb4-2-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·3·2·0⟩ (lit c4)) ▸
       at 1 2 (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | SBOX(0;4;2;1) @0410233241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410233241 : Ws → ⟪ (Bx4-0321 ∷ Sb4-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-3-0 ∷ Bx4-0321 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410233241 c4 = run b0
  where
  b0 : Chain (Bx4-0321 ∷ Sb4-1-3-0 ∷ []) (Sb4-1-3-0 ∷ Bx4-0321 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx4-0312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0321⟩ (lit c4)) ▸
       at 2 2 (Sb4-2-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨4·1·3·0⟩ (lit c4)) ▸
       at 1 2 (Sb4-2-3-0 ∷ Bx4-0312 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410233142 c4) ▸
       at 0 2 (Sb4-1-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨4·2·3·0⟩ (lit c4)) ▸
       at 1 2 (Bx4-0321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0312⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | SBOX(0;4;2;1) @04233240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at04233240 : Ws → ⟪ (Bx4-1320 ∷ Sb4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-3-1 ∷ Bx4-1320 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at04233240 c4 = run b0
  where
  b0 : Chain (Bx4-1320 ∷ Sb4-0-3-1 ∷ []) (Sb4-0-3-1 ∷ Bx4-1320 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx4-0321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1320⟩ (lit c4)) ▸
       at 2 2 (Sb4-1-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨4·0·3·1⟩ (lit c4)) ▸
       at 1 2 (Sb4-1-3-0 ∷ Bx4-0321 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at0410233241 c4) ▸
       at 0 2 (Sb4-0-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨4·1·3·0⟩ (lit c4)) ▸
       at 1 2 (Bx4-1320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0321⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(4;0;2;1) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·2·1⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb⁻4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-3-1 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·2·1⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb⁻4-0-3-1 ∷ []) (Sb⁻4-0-3-1 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Sb⁻4-0-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·0·3·1⟩ (lit c4)) ▸
       at 1 2 (Sb⁻4-0-2-1 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·2·1⟩ c4) ▸
       at 0 2 (Sb⁻4-0-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·0·2·1⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(3;0;21;4): 42 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb3-0-21-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-21-4 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb3-0-21-4 ∷ []) (Bx4-0213 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ CS01⁻ ∷ Toff312 ∷ CS03 ∷ Toff312 ∷ Sb⁻4-0-3-1 ∷ [])
  b0 = at 1 1 (Sb4-0-21-3 ∷ []) (lem-F0-at233442 c4) ▸
       at 1 1 (Bx4-0213 ∷ Toff312 ∷ Sb4-0-3-1 ∷ Toff312 ∷ Sb⁻4-0-3-1 ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (Bx4-0213 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0312⟩-at2332 c4) ▸
       at 1 1 (Sb4-1-32-0 ∷ []) (lem-F0-at0112203443 c4) ▸
       at 1 1 (Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ []) (refl) ▸
       at 5 1 (CS01⁻ ∷ []) (refl) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸ done

  b1 : Chain (Bx4-0213 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ CS01⁻ ∷ Toff312 ∷ CS03 ∷ Toff312 ∷ Sb⁻4-0-3-1 ∷ []) (Bx4-0213 ∷ Bx4-1320 ∷ Toff312 ∷ Sb4-0-3-1 ∷ Toff312 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ Sb⁻4-0-3-1 ∷ [])
  b1 = at 5 4 (Toff312 ∷ CS03 ∷ Toff312 ∷ CS01⁻ ∷ []) (wl0607 (lit c4)) ▸
       at 6 1 (Sb4-0-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-1-0-2 ∷ []) (refl) ▸
       at 3 1 (CS01 ∷ []) (refl) ▸
       at 6 1 (CS03 ∷ []) (refl) ▸
       at 2 6 (Toff312 ∷ CS03 ∷ Toff312 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ []) (wl0608 (lit c4)) ▸
       at 3 1 (Sb4-0-3-1 ∷ []) (refl) ▸
       at 6 1 (Sb4-1-0-2 ∷ []) (refl) ▸ done

  b2 : Chain (Bx4-0213 ∷ Bx4-1320 ∷ Toff312 ∷ Sb4-0-3-1 ∷ Toff312 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ Sb⁻4-0-3-1 ∷ []) (Bx4-0213 ∷ Toff312 ∷ CCZ012 ∷ Sb4-0-3-1 ∷ Bx4-1320 ∷ Toff312 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ Sb⁻4-0-3-1 ∷ [])
  b2 = at 1 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0230 (lit c4))) ▸
       at 2 1 (Toff312 ∷ []) (wl0609 (lit c4)) ▸
       at 4 1 (Toff312 ∷ []) (wl0609 (lit c4)) ▸
       at 3 1 (Bx4-1230 ∷ []) (lem-sym23-at04233240 c4) ▸
       at 2 3 (Bx4-1230 ∷ CCZ012 ∷ []) (lem-T312-beta-at0440 c4) ▸
       at 2 1 (Bx4-1320 ∷ []) (lem-sym23-at0440 c4) ▸
       at 2 2 (CCZ012 ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at04233240 c4) ▸
       at 3 2 (Sb4-0-3-1 ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·4·2·1⟩-at04233240 c4) ▸ done

  b3 : Chain (Bx4-0213 ∷ Toff312 ∷ CCZ012 ∷ Sb4-0-3-1 ∷ Bx4-1320 ∷ Toff312 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ Sb⁻4-0-3-1 ∷ []) (Bx4-0213 ∷ CCZ012 ∷ Toff312 ∷ Sb4-0-3-1 ∷ Toff312 ∷ CCZ012 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ Sb⁻4-0-3-1 ∷ [])
  b3 = at 4 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0230 (lit c4))) ▸
       at 5 1 (Toff312 ∷ []) (wl0609 (lit c4)) ▸
       at 7 1 (Toff312 ∷ []) (wl0609 (lit c4)) ▸
       at 6 1 (Bx4-1230 ∷ []) (lem-sym23-at04233240 c4) ▸
       at 5 3 (Bx4-1230 ∷ CCZ012 ∷ []) (lem-T312-beta-at0440 c4) ▸
       at 5 1 (Bx4-1320 ∷ []) (lem-sym23-at0440 c4) ▸
       at 5 2 (CCZ012 ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at04233240 c4) ▸
       at 1 2 (CCZ012 ∷ Toff312 ∷ []) (sym (wl0610 (lit c4))) ▸ done

  b4 : Chain (Bx4-0213 ∷ CCZ012 ∷ Toff312 ∷ Sb4-0-3-1 ∷ Toff312 ∷ CCZ012 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ Sb⁻4-0-3-1 ∷ []) (Bx4-0213 ∷ Toff312 ∷ Sb4-0-3-1 ∷ Toff312 ∷ Sb⁻4-0-3-1 ∷ Sb0-1-23-4 ∷ [])
  b4 = at 3 1 (CS03 ∷ []) (refl) ▸
       at 2 4 (CCZ012 ∷ Toff312 ∷ CS03 ∷ Toff312 ∷ []) (sym (wl0611 (lit c4))) ▸
       at 4 1 (Sb4-0-3-1 ∷ []) (refl) ▸
       at 1 2 [] (wl0183 (lit c4)) ▸
       at 4 5 (Sb4-1-32-0 ∷ []) (refl) ▸
       at 4 1 (Sb0-1-32-4 ∷ []) (sym (lem-F0-at0112203443 c4)) ▸
       at 4 2 (Sb⁻4-0-3-1 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·2·1⟩-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸ done

  b5 : Chain (Bx4-0213 ∷ Toff312 ∷ Sb4-0-3-1 ∷ Toff312 ∷ Sb⁻4-0-3-1 ∷ Sb0-1-23-4 ∷ []) (Sb3-0-21-4 ∷ Sb0-1-23-4 ∷ [])
  b5 = at 0 5 (Sb4-0-21-3 ∷ []) (refl) ▸
       at 0 1 (Sb3-0-21-4 ∷ []) (sym (lem-F0-at233442 c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(3;0;21;4) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-31-4 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb2-0-31-4 ∷ []) (Sb2-0-31-4 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Sb3-0-21-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·31·4⟩ (lit c4)) ▸
       at 1 2 (Sb3-0-21-4 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩ c4) ▸
       at 0 2 (Sb2-0-31-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·21·4⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(3;0;21;4) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb2-0-31-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (Sb2-0-31-4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩-at2332 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·31·4⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- F1 comm-CS-CS: 1 steps
lem-F1-comm-CS-CS : Ws → ⟪ (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-CS c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·0·21·4⟩-at243243 c4) ▸ done


-- auto BOX(0;1234) | CCZ123: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123 : Ws → ⟪ (Bx0-1234 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 2 (CCZ123 ∷ Bx0-1243 ∷ []) (sym (lem-c124-beta-at3443 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸ done


-- SB2 @1221: 6 steps
lem-SB2-at1221 : Ws → ⟪ (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ []) ⟫ʷ
lem-SB2-at1221 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ []) (CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- SB2 @011220: 6 steps
lem-SB2-at011220 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
lem-SB2-at011220 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (CCZ124 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (CCZ024 ∷ []) (lem-SB2-at1221 c4) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ231 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4)) ▸
       at 2 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 (lit c4)) ▸
       at 1 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS14 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ CS02 ∷ []) (CS02 ∷ Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4)) ▸
       at 2 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4)) ▸
       at 1 2 (CS03 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 c4) ▸
       at 0 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 (lit c4)) ▸
       at 1 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CSd14 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4)) ▸
       at 2 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 (lit c4)) ▸
       at 1 2 (CS03⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 c4) ▸
       at 0 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 (lit c4)) ▸
       at 1 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- sym23 @0314203241: 5 steps
lem-sym23-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-sym23-at0314203241 c4 = run b0
  where
  b0 : Chain (Bx3-4021 ∷ []) (Bx3-4201 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-4012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4021⟩ (lit c4)) ▸
       at 1 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 0 2 (Bx3-4201 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4102⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym23 @0314213240: 5 steps
lem-sym23-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ []) ⟫ʷ
lem-sym23-at0314213240 c4 = run b0
  where
  b0 : Chain (Bx3-4120 ∷ []) (Bx3-4210 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-4021 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4120⟩ (lit c4)) ▸
       at 1 1 (Bx3-4201 ∷ []) (lem-sym23-at0314203241 c4) ▸
       at 0 2 (Bx3-4210 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4201⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- T312-beta @0314213042: 8 steps
lem-T312-beta-at0314213042 : Ws → ⟪ (Toff014 ∷ Bx3-4102 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ CCZ124 ∷ []) ⟫ʷ
lem-T312-beta-at0314213042 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Bx3-4102 ∷ Toff014 ∷ []) (Bx3-4102 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 (lit c4)) ▸
       at 2 2 (Bx3-4012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4102⟩ (lit c4)) ▸
       at 3 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 (lit c4)) ▸
       at 1 3 (Bx3-4012 ∷ CCZ024 ∷ []) (lem-T312-beta-at0314203142 c4) ▸
       at 0 2 (Bx3-4102 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4012⟩ (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- T312-beta @03143041: 8 steps
lem-T312-beta-at03143041 : Ws → ⟪ (Toff024 ∷ Bx3-4201 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ CCZ124 ∷ []) ⟫ʷ
lem-T312-beta-at03143041 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ Bx3-4201 ∷ Toff024 ∷ []) (Bx3-4201 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 (lit c4)) ▸
       at 2 2 (Bx3-4102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4201⟩ (lit c4)) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 (lit c4)) ▸
       at 1 3 (Bx3-4102 ∷ CCZ124 ∷ []) (lem-T312-beta-at0314213042 c4) ▸
       at 0 2 (Bx3-4201 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4102⟩ (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- T312-beta @03143140: 8 steps
lem-T312-beta-at03143140 : Ws → ⟪ (Toff124 ∷ Bx3-4210 ∷ Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ CCZ024 ∷ []) ⟫ʷ
lem-T312-beta-at03143140 c4 = run b0
  where
  b0 : Chain (Toff124 ∷ Bx3-4210 ∷ Toff124 ∷ []) (Bx3-4210 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 (lit c4)) ▸
       at 2 2 (Bx3-4201 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4210⟩ (lit c4)) ▸
       at 3 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 (lit c4)) ▸
       at 1 3 (Bx3-4201 ∷ CCZ124 ∷ []) (lem-T312-beta-at03143041 c4) ▸
       at 0 2 (Bx3-4210 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4201⟩ (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- sym23 @03143041: 5 steps
lem-sym23-at03143041 : Ws → ⟪ (Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-sym23-at03143041 c4 = run b0
  where
  b0 : Chain (Bx3-4201 ∷ []) (Bx3-4021 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-4102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4201⟩ (lit c4)) ▸
       at 1 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 0 2 (Bx3-4021 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4012⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym23 @03143140: 5 steps
lem-sym23-at03143140 : Ws → ⟪ (Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-sym23-at03143140 c4 = run b0
  where
  b0 : Chain (Bx3-4210 ∷ []) (Bx3-4120 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-4201 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4210⟩ (lit c4)) ▸
       at 1 1 (Bx3-4021 ∷ []) (lem-sym23-at03143041 c4) ▸
       at 0 2 (Bx3-4120 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4021⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ241 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241 c4) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ241 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at243243 : Ws → ⟪ (Bx0-1423 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Sw34 ∷ []) (sym (wl0154 (lit c4))) ▸
       at 1 2 (CCZ134 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at2332 c4) ▸
       at 0 2 (CCZ134 ∷ Sw34 ∷ []) (sym (wl0154 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ241 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at243243 c4) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ241 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0110243243 c4) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ241 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4)) ▸
       at 2 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 1 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- F1 rel-266 [nf of rhs]: 55 steps
lem-F1-rel-266-nf-of-rhs : Ws → ⟪ (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-F1-rel-266-nf-of-rhs c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Sb2-0-41-3 ∷ Toff124 ∷ Toff214 ∷ [])
  b0 = at 1 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 5 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 10 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 14 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 0 4 (Toff214 ∷ []) (wl0612 (lit c4)) ▸
       at 1 4 (Toff124 ∷ []) (wl0613 (lit c4)) ▸
       at 3 4 (Toff124 ∷ []) (wl0613 (lit c4)) ▸
       at 4 4 (Toff214 ∷ []) (wl0612 (lit c4)) ▸ done

  b1 : Chain (Toff214 ∷ Toff124 ∷ Sb2-0-41-3 ∷ Toff124 ∷ Toff214 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ Bx3-4120 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ Toff214 ∷ [])
  b1 = at 2 1 (Sb3-0-41-2 ∷ []) (lem-F0 c4) ▸
       at 2 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 4 1 (CS02 ∷ []) (refl) ▸
       at 6 1 (CS02⁻ ∷ []) (refl) ▸
       at 2 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 4 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 4 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 4 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸ done

  b2 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ Bx3-4120 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ Toff214 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff214 ∷ Bx3-4012 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ Toff214 ∷ [])
  b2 = at 3 3 (Bx3-4120 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314213240 c4) ▸
       at 3 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 3 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 3 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 3 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4) ▸
       at 4 2 (CS02 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 c4) ▸
       at 5 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 7 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸ done

  b3 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff214 ∷ Bx3-4012 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ Toff214 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ Toff124 ∷ Toff214 ∷ [])
  b3 = at 7 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 7 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸
       at 6 3 (Bx3-4120 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314213240 c4) ▸
       at 6 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 6 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 6 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 6 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4) ▸
       at 7 2 (CS02⁻ ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 c4) ▸ done

  b4 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ Toff124 ∷ Toff214 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ Bx3-4102 ∷ CCZ024 ∷ Toff214 ∷ [])
  b4 = at 8 0 (Toff124 ∷ Toff124 ∷ []) (sym (wl0614 (lit c4))) ▸
       at 10 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 10 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 10 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸
       at 10 1 (Bx3-4210 ∷ []) (lem-sym23-at0314213240 c4) ▸
       at 9 3 (Bx3-4210 ∷ CCZ024 ∷ []) (lem-T312-beta-at03143140 c4) ▸
       at 9 1 (Bx3-4120 ∷ []) (lem-sym23-at03143140 c4) ▸
       at 9 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸ done

  b5 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ Bx3-4102 ∷ CCZ024 ∷ Toff214 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ Bx3-4120 ∷ CCZ014 ∷ [])
  b5 = at 9 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 9 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 9 2 (CCZ024 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 c4) ▸
       at 10 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 12 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 12 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 12 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸
       at 11 3 (Bx3-4120 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314213240 c4) ▸ done

  b6 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ Bx3-4120 ∷ CCZ014 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b6 = at 11 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 11 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 11 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 11 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4) ▸
       at 9 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0263 c4) ▸
       at 7 2 (Toff124 ∷ CS02⁻ ∷ []) (wp0264 c4) ▸
       at 6 2 (Toff124 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0265 c4) ▸ done


-- F0 @011220: 5 steps
lem-F0-at011220 : Ws → ⟪ (Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ []) ⟫ʷ
lem-F0-at011220 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ []) (Sb3-1-42-0 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 1 (Sb3-0-42-1 ∷ []) (lem-F0-at1221 c4) ▸
       at 0 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym12 @0310243241: 5 steps
lem-sym12-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-sym12-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ []) (Bx3-4021 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ (lit c4)) ▸
       at 1 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 0 2 (Bx3-4021 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4012⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym12 @03243240: 5 steps
lem-sym12-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-sym12-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ []) (Bx3-4120 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ (lit c4)) ▸
       at 1 1 (Bx3-4021 ∷ []) (lem-sym12-at0310243241 c4) ▸
       at 0 2 (Bx3-4120 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4021⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym34 @03143041: 5 steps
lem-sym34-at03143041 : Ws → ⟪ (Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ []) ⟫ʷ
lem-sym34-at03143041 c4 = run b0
  where
  b0 : Chain (Bx3-4201 ∷ []) (Bx3-4210 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-4102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4201⟩ (lit c4)) ▸
       at 1 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸
       at 0 2 (Bx3-4210 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4120⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym34 @03143140: 5 steps
lem-sym34-at03143140 : Ws → ⟪ (Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-sym34-at03143140 c4 = run b0
  where
  b0 : Chain (Bx3-4210 ∷ []) (Bx3-4201 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-4201 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4210⟩ (lit c4)) ▸
       at 1 1 (Bx3-4210 ∷ []) (lem-sym34-at03143041 c4) ▸
       at 0 2 (Bx3-4201 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4210⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym12 @0314203241: 5 steps
lem-sym12-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-sym12-at0314203241 c4 = run b0
  where
  b0 : Chain (Bx3-4021 ∷ []) (Bx3-0421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-4012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4021⟩ (lit c4)) ▸
       at 1 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 0 2 (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym12 @0314213240: 5 steps
lem-sym12-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-sym12-at0314213240 c4 = run b0
  where
  b0 : Chain (Bx3-4120 ∷ []) (Bx3-1420 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-4021 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4120⟩ (lit c4)) ▸
       at 1 1 (Bx3-0421 ∷ []) (lem-sym12-at0314203241 c4) ▸
       at 0 2 (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ231 @0310243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx3-0421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ (lit c4)) ▸
       at 2 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4)) ▸
       at 1 2 (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ231 @03243240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 : Ws → ⟪ (Bx3-1420 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-1420 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Bx3-0421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243241 c4) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4)) ▸
       at 1 2 (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS14 @0310243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Bx3-0421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ CS01 ∷ []) (CS01 ∷ Bx3-0421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ (lit c4)) ▸
       at 2 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4)) ▸
       at 1 2 (CS02 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 c4) ▸
       at 0 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4)) ▸
       at 1 2 (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS14 @03243240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14-at03243240 : Ws → ⟪ (Bx3-1420 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ CS01 ∷ []) (CS01 ∷ Bx3-1420 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ (lit c4)) ▸
       at 2 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 1 2 (CS01 ∷ Bx3-0421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243241 c4) ▸
       at 0 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 1 2 (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CSd14 @0310243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Bx3-0421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Bx3-0421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ (lit c4)) ▸
       at 2 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 (lit c4)) ▸
       at 1 2 (CS02⁻ ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 c4) ▸
       at 0 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 (lit c4)) ▸
       at 1 2 (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CSd14 @03243240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at03243240 : Ws → ⟪ (Bx3-1420 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Bx3-1420 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ (lit c4)) ▸
       at 2 2 (CS01⁻ ∷ Sw01 ∷ []) (sym (wl0133 (lit c4))) ▸
       at 1 2 (CS01⁻ ∷ Bx3-0421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243241 c4) ▸
       at 0 2 (CS01⁻ ∷ Sw01 ∷ []) (sym (wl0133 (lit c4))) ▸
       at 1 2 (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ243 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243 c4) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ243 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at243243 : Ws → ⟪ (Bx0-1423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at2332 c4) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ243 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at243243 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ243 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0110243243 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ243 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0210243143 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 1 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ243 @0310243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx3-0421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-0421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0310243142 c4) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 1 2 (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ243 @03243240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at03243240 : Ws → ⟪ (Bx3-1420 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-1420 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Bx3-0421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0310243241 c4) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4)) ▸
       at 1 2 (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- sym34 @03243240: 5 steps
lem-sym34-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ []) ⟫ʷ
lem-sym34-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ []) (Bx3-1402 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ (lit c4)) ▸
       at 1 1 (Bx3-0412 ∷ []) (lem-sym34-at0310243241 c4) ▸
       at 0 2 (Bx3-1402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0412⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- T312-beta @243243: 8 steps
lem-T312-beta-at243243 : Ws → ⟪ (Toff214 ∷ Bx0-1423 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ134 ∷ []) ⟫ʷ
lem-T312-beta-at243243 c4 = run b0
  where
  b0 : Chain (Toff214 ∷ Bx0-1423 ∷ Toff214 ∷ []) (Bx0-1423 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 (lit c4)) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 3 2 (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 (lit c4)) ▸
       at 1 3 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-T312-beta-at2332 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Sw34 ∷ []) (sym (wl0154 (lit c4))) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- T312-beta @0110243243: 8 steps
lem-T312-beta-at0110243243 : Ws → ⟪ (Toff204 ∷ Bx1-0423 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CCZ034 ∷ []) ⟫ʷ
lem-T312-beta-at0110243243 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Bx1-0423 ∷ Toff204 ∷ []) (Bx1-0423 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 (lit c4)) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 3 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 (lit c4)) ▸
       at 1 3 (Bx0-1423 ∷ CCZ134 ∷ []) (lem-T312-beta-at243243 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- T312-beta @0210243143: 8 steps
lem-T312-beta-at0210243143 : Ws → ⟪ (Toff104 ∷ Bx2-0413 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ034 ∷ []) ⟫ʷ
lem-T312-beta-at0210243143 c4 = run b0
  where
  b0 : Chain (Toff104 ∷ Bx2-0413 ∷ Toff104 ∷ []) (Bx2-0413 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 (lit c4)) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 3 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 (lit c4)) ▸
       at 1 3 (Bx1-0423 ∷ CCZ034 ∷ []) (lem-T312-beta-at0110243243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- T312-beta @0310243142: 8 steps
lem-T312-beta-at0310243142 : Ws → ⟪ (Toff104 ∷ Bx3-0412 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CCZ024 ∷ []) ⟫ʷ
lem-T312-beta-at0310243142 c4 = run b0
  where
  b0 : Chain (Toff104 ∷ Bx3-0412 ∷ Toff104 ∷ []) (Bx3-0412 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 (lit c4)) ▸
       at 2 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4)) ▸
       at 3 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 (lit c4)) ▸
       at 1 3 (Bx2-0413 ∷ CCZ034 ∷ []) (lem-T312-beta-at0210243143 c4) ▸
       at 0 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- T312-beta @03243042: 8 steps
lem-T312-beta-at03243042 : Ws → ⟪ (Toff014 ∷ Bx3-1402 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ CCZ124 ∷ []) ⟫ʷ
lem-T312-beta-at03243042 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Bx3-1402 ∷ Toff014 ∷ []) (Bx3-1402 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 (lit c4)) ▸
       at 2 2 (Bx3-0412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1402⟩ (lit c4)) ▸
       at 3 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 (lit c4)) ▸
       at 1 3 (Bx3-0412 ∷ CCZ024 ∷ []) (lem-T312-beta-at0310243142 c4) ▸
       at 0 2 (Bx3-1402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0412⟩ (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- sym34 @03243042: 5 steps
lem-sym34-at03243042 : Ws → ⟪ (Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-sym34-at03243042 c4 = run b0
  where
  b0 : Chain (Bx3-1402 ∷ []) (Bx3-1420 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1402⟩ (lit c4)) ▸
       at 1 1 (Bx3-0421 ∷ []) (lem-sym34-at0310243142 c4) ▸
       at 0 2 (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ123 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123 c4) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ123 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at243243 : Ws → ⟪ (Bx0-1423 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at2332 c4) ▸
       at 0 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ123 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at243243 c4) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ123 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0110243243 c4) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ123 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4)) ▸
       at 2 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0210243143 c4) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 (lit c4)) ▸
       at 1 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ123 @0310243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx3-0421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ (lit c4)) ▸
       at 2 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0310243142 c4) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4)) ▸
       at 1 2 (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ123 @03243240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at03243240 : Ws → ⟪ (Bx3-1420 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-1420 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Bx3-0421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0310243241 c4) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4)) ▸
       at 1 2 (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done

